package soot.jbco.bafTransformations;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 1999 Raja Vallee-Rai
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 2.1 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser Public License for more details.
 * 
 * You should have received a copy of the GNU General Lesser Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/lgpl-2.1.html>.
 * #L%
 */

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import soot.Body;
import soot.BodyTransformer;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.PatchingChain;
import soot.PrimType;
import soot.PrimTypeCollector;
import soot.RefType;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.UnitBox;
import soot.baf.Baf;
import soot.baf.DupInst;
import soot.baf.FieldArgInst;
import soot.baf.IdentityInst;
import soot.baf.IncInst;
import soot.baf.InstanceCastInst;
import soot.baf.InstanceOfInst;
import soot.baf.LoadInst;
import soot.baf.MethodArgInst;
import soot.baf.NewArrayInst;
import soot.baf.NewInst;
import soot.baf.NewMultiArrayInst;
import soot.baf.NoArgInst;
import soot.baf.OpTypeArgInst;
import soot.baf.PopInst;
import soot.baf.PrimitiveCastInst;
import soot.baf.PushInst;
import soot.baf.ReturnInst;
import soot.baf.SpecialInvokeInst;
import soot.baf.StoreInst;
import soot.baf.SwapInst;
import soot.baf.TargetArgInst;
import soot.jbco.IJbcoTransform;
import soot.jimple.Constant;
import soot.jimple.ConstantFactory;
import soot.jimple.DoubleConstant;
import soot.jimple.FloatConstant;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NullConstant;
import soot.jimple.StringConstant;
import soot.toolkits.graph.BriefUnitGraph;
import soot.util.Chain;
import soot.util.PhaseDumper;

/**
 * @author Michael Batchelder
 *
 *         Created on 12-May-2006
 */
public class FindDuplicateSequences extends BodyTransformer implements IJbcoTransform {

  int totalcounts[] = new int[512];

  public static String dependancies[] = new String[] { "bb.jbco_j2bl", "bb.jbco_rds", "bb.jbco_ful", "bb.lp" };
  private PhaseDumper myPhaseDumper;
  private Baf myBaf;
  private Jimple myJimple;
  private ConstantFactory constantFactory;
  private PrimTypeCollector primTypeCollector;

  public FindDuplicateSequences(PhaseDumper myPhaseDumper, Baf myBaf, Jimple myJimple, ConstantFactory constantFactory, PrimTypeCollector primTypeCollector) {
    this.myPhaseDumper = myPhaseDumper;
    this.myBaf = myBaf;
    this.myJimple = myJimple;
    this.constantFactory = constantFactory;
    this.primTypeCollector = primTypeCollector;
  }

  public String[] getDependencies() {
    return dependancies;
  }

  public static String name = "bb.jbco_rds";

  public String getName() {
    return name;
  }

  public void outputSummary() {
//    out.println("Duplicate Sequences:");
    for (int count = totalcounts.length - 1; count >= 0; count--) {
      if (totalcounts[count] > 0) {
//        out.println("\t" + count + " total: " + totalcounts[count]);
      }
    }
  }

  protected void internalTransform(Body b, String phaseName, Map<String, String> options) {

    int weight = soot.jbco.Main.getWeight(phaseName, b.getMethod().getSignature());
    if (weight == 0) {
      return;
    }
//FIXME
//    if (output) {
//      out.println("Checking " + b.getMethod().getName() + " for duplicate sequences..");
//    }

    List<Unit> illegalUnits = new ArrayList<Unit>();
    List<Unit> seenUnits = new ArrayList<Unit>();
    List<Unit> workList = new ArrayList<Unit>();
    PatchingChain<Unit> units = b.getUnits();
    BriefUnitGraph bug = new BriefUnitGraph(b, myPhaseDumper);
    workList.addAll(bug.getHeads());
    while (workList.size() > 0) {
      Unit u = workList.remove(0);
      if (seenUnits.contains(u)) {
        continue;
      }

      if (u instanceof NewInst) {
        RefType t = ((NewInst) u).getBaseType();
        List<Unit> tmpWorkList = new ArrayList<Unit>();
        tmpWorkList.add(u);
        while (tmpWorkList.size() > 0) {
          Unit v = tmpWorkList.remove(0);

          // horrible approximatin about which init call belongs to which new
          if (v instanceof SpecialInvokeInst) {
            SpecialInvokeInst si = (SpecialInvokeInst) v;
            if (si.getMethodRef().getSignature().indexOf("void <init>") < 0
                || si.getMethodRef().declaringClass() != t.getSootClass()) {
              tmpWorkList.addAll(bug.getSuccsOf(v));
            }
          } else {
            tmpWorkList.addAll(bug.getSuccsOf(v));
          }
          illegalUnits.add(v);
        }
      }

      seenUnits.add(u);
      workList.addAll(bug.getSuccsOf(u));
    }
    seenUnits = null;

    int controlLocalIndex = 0;
    int longestSeq = (units.size() / 2) - 1;
    if (longestSeq > 20) {
      longestSeq = 20;
    }

    Local controlLocal = null;
    Collection<Local> bLocals = b.getLocals();
    int counts[] = new int[longestSeq + 1];
    // ArrayList protectedUnits = new ArrayList();
    Map<Local, Local> bafToJLocals = soot.jbco.Main.methods2Baf2JLocals.get(b.getMethod());
    boolean changed = true;
    Map<Unit, Stack<Type>> stackHeightsBefore = null;
    for (int count = longestSeq; count > 2; count--) {
      Unit uArry[] = units.toArray(new Unit[units.size()]);
      if (uArry.length <= 0) {
        return;
      }

      // int count = uArry.length > 100 ? 4 : uArry.length > 50 ? 3 : 2;

      List<List<Unit>> candidates = new ArrayList<List<Unit>>();
      List<Unit> unitIDs = new ArrayList<Unit>();

      if (changed) {
        stackHeightsBefore = StackTypeHeightCalculator.calculateStackHeights(b, bafToJLocals);
        bug = StackTypeHeightCalculator.bug;
        changed = false;
      }

      LOOP: for (int i = 0; i < uArry.length; i++) {
        unitIDs.add(uArry[i]);

        if (i + count > uArry.length) {
          continue;
        }

        List<Unit> seq = new ArrayList<Unit>();
        for (int j = 0; j < count; j++) {
          Unit u = uArry[i + j];
          if (u instanceof IdentityInst || u instanceof ReturnInst || illegalUnits.contains(u)) {
            break;
          }

          // don't allow units within the sequence that have more than one
          // predecessor that is not _within_ the sequence
          if (j > 0) {
            List<Unit> preds = bug.getPredsOf(u);
            if (preds.size() > 0) {
              int found = 0;
              Iterator<Unit> pit = preds.iterator();
              while (pit.hasNext()) {
                Unit p = pit.next();
                for (int jj = 0; jj < count; jj++) {
                  if (p == uArry[i + jj]) {
                    found++;
                    break;
                  }
                }
              }
              if (found < preds.size()) {
                continue LOOP;
              }
            }
          }

          seq.add(u);
        }
        if (seq.size() == count) {
          if (seq.get(seq.size() - 1).fallsThrough()) {
            candidates.add(seq);
          }
        }
      }

      Map<List<Unit>, List<List<Unit>>> selected = new HashMap<List<Unit>, List<List<Unit>>>();
      for (int i = 0; i < candidates.size(); i++) {
        List<Unit> seq = candidates.get(i);
        List<List<Unit>> matches = new ArrayList<List<Unit>>();
        for (int j = 0; j < (uArry.length - count); j++) {
          if (overlap(uArry, seq, j, count)) {
            continue;
          }

          boolean found = false;
          for (int k = 0; k < count; k++) {
            Unit u = seq.get(k);

            found = false;

            Unit v = uArry[j + k];
            if (!equalUnits(u, v, b) || illegalUnits.contains(v)) {
              break;
            }

            if (k > 0) {
              List<Unit> preds = bug.getPredsOf(v);
              if (preds.size() > 0) {
                int fcount = 0;
                Iterator<Unit> pit = preds.iterator();
                while (pit.hasNext()) {
                  Unit p = pit.next();
                  for (int jj = 0; jj < count; jj++) {
                    if (p == uArry[j + jj]) {
                      fcount++;
                      break;
                    }
                  }
                }
                if (fcount < preds.size()) {
                  break;
                }
              }
            }

            // No need to calc AFTER stack, since they are equal units
            if (!stackHeightsBefore.get(u).equals(stackHeightsBefore.get(v))) {
              break;
            }

            found = true;
          }

          if (found) {
            List<Unit> foundSeq = new ArrayList<Unit>();
            for (int m = 0; m < count; m++) {
              foundSeq.add(uArry[j + m]);
            }
            matches.add(foundSeq);
          }
        }

        if (matches.size() > 0) {
          boolean done = false;
          for (int x = 0; x < seq.size(); x++) {
            if (!unitIDs.contains(seq.get(x))) {
              done = true;
            } else {
              unitIDs.remove(seq.get(x));
            }
          }

          if (!done) {
            matches = cullOverlaps(b, unitIDs, matches);
            if (matches.size() > 0) {
              selected.put(seq, matches);
            }
          }
        }
      }

      if (selected.size() <= 0) {
        continue;
      }

      Iterator<List<Unit>> keys = selected.keySet().iterator();
      while (keys.hasNext()) {
        List<Unit> key = keys.next();
        List<List<Unit>> avalues = selected.get(key);
        if (avalues.size() < 1 || soot.jbco.util.Rand.getInt(10) <= weight) {
          continue;
        }

        changed = true;

        controlLocal = myBaf.newLocal("controlLocalfordups" + controlLocalIndex, primTypeCollector.getIntType());
        bLocals.add(controlLocal);
        bafToJLocals.put(controlLocal, myJimple.newLocal("controlLocalfordups" + controlLocalIndex++, primTypeCollector.getIntType()));

        counts[key.size()] += avalues.size();

        List<Unit> jumps = new ArrayList<Unit>();

        Unit first = key.get(0);
        // protectedUnits.addAll(key);

        Unit store = myBaf.newStoreInst(primTypeCollector.getIntType(), controlLocal);
        // protectedUnits.add(store);

        units.insertBefore(store, first);

        Unit pushUnit = myBaf.newPushInst(constantFactory.createIntConstant(0));
        // protectedUnits.add(pushUnit);

        units.insertBefore(pushUnit, store);

        int index = 1;
        Iterator<List<Unit>> values = avalues.iterator();
        while (values.hasNext()) {
          List<Unit> next = values.next();

          Unit jump = units.getSuccOf(next.get(next.size() - 1));
          // protectedUnits.add(jump);

          Unit firstt = next.get(0);
          Unit storet = (Unit) store.clone();
          // protectedUnits.add(storet);

          units.insertBefore(storet, firstt);

          pushUnit = myBaf.newPushInst(constantFactory.createIntConstant(index++));
          // protectedUnits.add(pushUnit);

          units.insertBefore(pushUnit, storet);

          Unit goUnit = myBaf.newGotoInst(first);
          // protectedUnits.add(goUnit);

          units.insertAfter(goUnit, storet);
          jumps.add(jump);
        }

        Unit insertAfter = key.get(key.size() - 1);
        // protectedUnits.add(insertAfter);

        Unit swUnit = myBaf.newTableSwitchInst(units.getSuccOf(insertAfter), 1, jumps.size(), jumps);
        // protectedUnits.add(swUnit);

        units.insertAfter(swUnit, insertAfter);

        Unit loadUnit = myBaf.newLoadInst(primTypeCollector.getIntType(), controlLocal);
        // protectedUnits.add(loadUnit);

        units.insertAfter(loadUnit, insertAfter);

        values = avalues.iterator();
        while (values.hasNext()) {
          List<Unit> next = values.next();
          units.removeAll(next);
          // protectedUnits.removeAll(next);
        }
      }
    } // end of for loop for duplicate seq of various length

    boolean dupsExist = false;
//    if (output) {
//      System.out.println("Duplicate Sequences for " + b.getMethod().getName());
//    }

    for (int count = longestSeq; count >= 0; count--) {
      if (counts[count] > 0) {
//        if (output) {
//          out.println(count + " total: " + counts[count]);
//        }
        dupsExist = true;
        totalcounts[count] += counts[count];
      }
    }
//FIXME
//    if (!dupsExist) {
//      if (output) {
//        out.println("\tnone");
//      }
//    } else if (debug) {
//      StackTypeHeightCalculator.calculateStackHeights(b);
//    }
  }

  private boolean equalUnits(Object o1, Object o2, Body b) {
    if (o1.getClass() != o2.getClass()) {
      return false;
    }

    // this is actually handled by the predecessor checks

    // if units are targets of different jumps then not equal
    // if (!((Unit)o1).getBoxesPointingToThis().equals(
    // ((Unit)o2).getBoxesPointingToThis()))
    // return false;

    List<Trap> l1 = getTrapsForUnit(o1, b);
    List<Trap> l2 = getTrapsForUnit(o2, b);
    if (l1.size() != l2.size()) {
      return false;
    } else {
      for (int i = 0; i < l1.size(); i++) {
        if (l1.get(i) != l2.get(i)) {
          return false;
        }
      }
    }

    if (o1 instanceof NoArgInst) {
      return true;
    }

    /*
     * if (o1 instanceof IncInst) { IncInst ii = (IncInst)o1; if (ii.getLocal() != ((IncInst)o2).getLocal() ||
     * ii.getConstant() != ((IncInst)o2).getConstant()) return false; return true; }
     */

    if (o1 instanceof TargetArgInst) {
      // return false;
      // Maybe shouldn't allow duplicate target units?
      if (o1 instanceof OpTypeArgInst) {
        return ((TargetArgInst) o1).getTarget() == ((TargetArgInst) o2).getTarget()
            && ((OpTypeArgInst) o1).getOpType() == ((OpTypeArgInst) o2).getOpType();
      } else {
        return ((TargetArgInst) o1).getTarget() == ((TargetArgInst) o2).getTarget();
      }
    }

    if (o1 instanceof OpTypeArgInst) {
      return ((OpTypeArgInst) o1).getOpType() == ((OpTypeArgInst) o2).getOpType();
    }

    if (o1 instanceof MethodArgInst) {
      return ((MethodArgInst) o1).getMethod() == ((MethodArgInst) o2).getMethod();
    }

    if (o1 instanceof FieldArgInst) {
      return ((FieldArgInst) o1).getField() == ((FieldArgInst) o2).getField();
    }

    if (o1 instanceof PrimitiveCastInst) {
      return ((PrimitiveCastInst) o1).getFromType() == ((PrimitiveCastInst) o2).getFromType()
          && ((PrimitiveCastInst) o1).getToType() == ((PrimitiveCastInst) o2).getToType();
    }

    if (o1 instanceof DupInst) {
      return compareDups(o1, o2);
    }

    if (o1 instanceof LoadInst) {
      return ((LoadInst) o1).getLocal() == ((LoadInst) o2).getLocal();
    }

    if (o1 instanceof StoreInst) {
      return ((StoreInst) o1).getLocal() == ((StoreInst) o2).getLocal();
    }

    if (o1 instanceof PushInst) {
      return equalConstants(((PushInst) o1).getConstant(), ((PushInst) o2).getConstant());
    }

    if (o1 instanceof IncInst) {
      if (equalConstants(((IncInst) o1).getConstant(), ((IncInst) o2).getConstant())) {
        return (((IncInst) o1).getLocal() == ((IncInst) o2).getLocal());
      }
    }

    if (o1 instanceof InstanceCastInst) {
      return equalTypes(((InstanceCastInst) o1).getCastType(), ((InstanceCastInst) o2).getCastType());
    }

    if (o1 instanceof InstanceOfInst) {
      return equalTypes(((InstanceOfInst) o1).getCheckType(), ((InstanceOfInst) o2).getCheckType());
    }

    if (o1 instanceof NewArrayInst) {
      return equalTypes(((NewArrayInst) o1).getBaseType(), ((NewArrayInst) o2).getBaseType());
    }

    if (o1 instanceof NewInst) {
      return equalTypes(((NewInst) o1).getBaseType(), ((NewInst) o2).getBaseType());
    }

    if (o1 instanceof NewMultiArrayInst) {
      return equalTypes(((NewMultiArrayInst) o1).getBaseType(), ((NewMultiArrayInst) o2).getBaseType())
          && ((NewMultiArrayInst) o1).getDimensionCount() == ((NewMultiArrayInst) o2).getDimensionCount();
    }

    if (o1 instanceof PopInst) {
      return ((PopInst) o1).getWordCount() == ((PopInst) o2).getWordCount();
    }

    if (o1 instanceof SwapInst) {
      return ((SwapInst) o1).getFromType() == ((SwapInst) o2).getFromType()
          && ((SwapInst) o1).getToType() == ((SwapInst) o2).getToType();
    }

    return false;
  }

  private List<Trap> getTrapsForUnit(Object o, Body b) {
    ArrayList<Trap> list = new ArrayList<Trap>();
    Chain<Trap> traps = b.getTraps();
    if (traps.size() != 0) {
      PatchingChain<Unit> units = b.getUnits();
      Iterator<Trap> it = traps.iterator();
      while (it.hasNext()) {
        Trap t = it.next();
        Iterator<Unit> tit = units.iterator(t.getBeginUnit(), t.getEndUnit());
        while (tit.hasNext()) {
          if (tit.next() == o) {
            list.add(t);
            break;
          }
        }
      }
    }
    return list;
  }

  private boolean overlap(Object units[], List<?> list, int idx, int count) {
    if (idx < 0 || list == null || list.size() == 0) {
      return false;
    }

    Object first = list.get(0);
    Object last = list.get(list.size() - 1);
    for (int i = idx; i < idx + count; i++) {
      if (i < units.length && (first == units[i] || last == units[i])) {
        return true;
      }
    }

    return false;
  }

  private boolean equalConstants(Constant c1, Constant c2) {
    Type t = c1.getType(myScene);
    if (t != c2.getType(myScene)) {
      return false;
    }

    if (t instanceof IntType) {
      return ((IntConstant) c1).value == ((IntConstant) c2).value;
    }

    if (t instanceof FloatType) {
      return ((FloatConstant) c1).value == ((FloatConstant) c2).value;
    }

    if (t instanceof LongType) {
      return ((LongConstant) c1).value == ((LongConstant) c2).value;
    }

    if (t instanceof DoubleType) {
      return ((DoubleConstant) c1).value == ((DoubleConstant) c2).value;
    }

    if (c1 instanceof StringConstant && c2 instanceof StringConstant) {
      return ((StringConstant) c1).value == ((StringConstant) c2).value;
    }

    return c1 instanceof NullConstant && c2 instanceof NullConstant;
  }

  private boolean compareDups(Object o1, Object o2) {
    DupInst d1 = (DupInst) o1;
    DupInst d2 = (DupInst) o2;

    List<Type> l1 = d1.getOpTypes();
    List<Type> l2 = d2.getOpTypes();
    for (int k = 0; k < 2; k++) {
      if (k == 1) {
        l1 = d1.getUnderTypes();
        l2 = d2.getUnderTypes();
      }
      if (l1.size() != l2.size()) {
        return false;
      }

      for (int i = 0; i < l1.size(); i++) {
        if (l1.get(i) != l2.get(i)) {
          return false;
        }
      }
    }

    return true;
  }

  private boolean equalTypes(Type t1, Type t2) {
    if (t1 instanceof RefType) {
      if (t2 instanceof RefType) {
        // TODO: more discerning comparison here?
        RefType rt1 = (RefType) t1;
        RefType rt2 = (RefType) t2;
        return rt1.compareTo(rt2) == 0;
      }
      return false;
    }

    if (t1 instanceof PrimType && t2 instanceof PrimType) {
      return t1.getClass() == t2.getClass();
    }

    return false;
  }

  private static List<List<Unit>> cullOverlaps(Body b, List<Unit> ids, List<List<Unit>> matches) {
    List<List<Unit>> newMatches = new ArrayList<List<Unit>>();
    for (int i = 0; i < matches.size(); i++) {
      List<Unit> match = matches.get(i);
      Iterator<Unit> it = match.iterator();
      boolean clean = true;
      while (it.hasNext()) {
        if (!ids.contains(it.next())) {
          clean = false;
          break;
        }
      }
      if (clean) {
        List<UnitBox> targs = b.getUnitBoxes(true);
        for (int j = 0; j < targs.size() && clean; j++) {
          Unit u = targs.get(j).getUnit();
          it = match.iterator();
          while (it.hasNext()) {
            if (u == it.next()) {
              clean = false;
              break;
            }
          }
        }
      }

      if (clean) {
        it = match.iterator();
        while (it.hasNext()) {
          ids.remove(it.next());
        }
        newMatches.add(match);
      }
    }
    return newMatches;
  }
}
