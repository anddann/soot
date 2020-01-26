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
import java.util.Iterator;
import java.util.Map;
import java.util.Stack;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.BodyTransformer;
import soot.IntegerType;
import soot.Local;
import soot.PatchingChain;
import soot.PrimTypeCollector;
import soot.RefType;
import soot.SootField;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.baf.Baf;
import soot.baf.GotoInst;
import soot.baf.IdentityInst;
import soot.baf.JSRInst;
import soot.baf.TargetArgInst;
import soot.baf.ThrowInst;
import soot.jbco.IJbcoTransform;
import soot.jbco.jimpleTransformations.FieldRenamer;
import soot.jbco.util.BodyBuilder;
import soot.jbco.util.Rand;
import soot.jbco.util.ThrowSet;
import soot.jimple.ConstantFactory;
import soot.util.Chain;

/**
 * @author Michael Batchelder
 *
 *         Created on 2-May-2006
 *
 *         This transformer takes a portion of gotos/ifs and moves them into a TRY/CATCH block
 */
public class IndirectIfJumpsToCaughtGotos extends BodyTransformer implements IJbcoTransform {

  private static final Logger logger = LoggerFactory.getLogger(IndirectIfJumpsToCaughtGotos.class);
  int count = 0;

  public static String dependancies[] = new String[] { "bb.jbco_iii", "bb.jbco_ful", "bb.lp" };

  private FieldRenamer myFieldRenamer;
  private ConstantFactory constantFactory;
  private PrimTypeCollector primTypeCollector;

  public IndirectIfJumpsToCaughtGotos( FieldRenamer myFieldRenamer, ConstantFactory constantFactory, PrimTypeCollector primTypeCollector) {

    this.myFieldRenamer = myFieldRenamer;
    this.constantFactory = constantFactory;
    this.primTypeCollector = primTypeCollector;
  }

  public String[] getDependencies() {
    return dependancies;
  }

  public static String name = "bb.jbco_iii";

  public String getName() {
    return name;
  }

  public void outputSummary() {
    logger.info("Indirected Ifs through Traps: " + count);
  }

  protected void internalTransform(Body b, String phaseName, Map<String, String> options) {

    int weight = soot.jbco.Main.getWeight(phaseName, b.getMethod().getSignature());
    if (weight == 0) {
      return;
    }

    PatchingChain<Unit> units = b.getUnits();
    Unit nonTrap = findNonTrappedUnit(units, b.getTraps());
    if (nonTrap == null) {
      Unit last = null;
      nonTrap = Baf.newNopInst();
      for (Iterator<Unit> it = units.iterator(); it.hasNext();) {
        Unit u = (Unit) it.next();
        if (u instanceof IdentityInst && ((IdentityInst) u).getLeftOp() instanceof Local) {
          last = u;
          continue;
        } else {
          if (last != null) {
            units.insertAfter(nonTrap, last);
          } else {
            units.addFirst(nonTrap);
          }
          break;
        }
      }
    }

    Stack<Type> stack = StackTypeHeightCalculator.getAfterStack(b, nonTrap);

    ArrayList<Unit> addedUnits = new ArrayList<Unit>();
    Iterator<Unit> it = units.snapshotIterator();
    while (it.hasNext()) {
      Unit u = (Unit) it.next();
      if (isIf(u) && Rand.getInt(10) <= weight) {
        TargetArgInst ifu = (TargetArgInst) u;
        Unit newTarg = Baf.newGotoInst(ifu.getTarget());
        units.add(newTarg);
        ifu.setTarget(newTarg);
        addedUnits.add(newTarg);
      }
    }

    if (addedUnits.size() <= 0) {
      return;
    }

    Unit nop = Baf.newNopInst();
    units.add(nop);

    ArrayList<Unit> toinsert = new ArrayList<Unit>();
    SootField field = null;
    try {
      field = myFieldRenamer.getRandomOpaques()[Rand.getInt(2)];
    } catch (NullPointerException npe) {
      logger.debug(npe.getMessage(), npe);
    }

    if (field != null && Rand.getInt(3) > 0) {
      toinsert.add(Baf.newStaticGetInst(field.makeRef()));
      if (field.getType() instanceof IntegerType) {
        toinsert.add(Baf.newIfGeInst((Unit) units.getSuccOf(nonTrap)));
      } else {
        SootMethod boolInit = ((RefType) field.getType()).getSootClass().getMethod("boolean booleanValue()");
        toinsert.add(Baf.newVirtualInvokeInst(boolInit.makeRef()));
        toinsert.add(Baf.newIfGeInst((Unit) units.getSuccOf(nonTrap)));
      }
    } else {
      toinsert.add(Baf.newPushInst(constantFactory.createIntConstant(BodyBuilder.getIntegerNine())));
      toinsert.add(Baf.newPrimitiveCastInst(primTypeCollector.getIntType(), primTypeCollector.getByteType()));
      toinsert.add(Baf.newPushInst(constantFactory.createIntConstant(Rand.getInt() % 2 == 0 ? 9 : 3)));
      toinsert.add(Baf.newRemInst(primTypeCollector.getByteType()));

      /*
       * toinsert.add(Baf.newDup1Inst(primTypeCollector.getByteType()));
       * toinsert.add(Baf.newPrimitiveCastInst(primTypeCollector.getByteType(),primTypeCollector.getIntType()));
       * toinsert.add(Baf.newStaticGetInst(sys.getFieldByName("out").makeRef()));
       * toinsert.add(Baf.newSwapInst(primTypeCollector.getIntType(),primTypeCollector.getRefType())); ArrayList parms = new ArrayList();
       * parms.add(primTypeCollector.getIntType()); toinsert.add(Baf.newVirtualInvokeInst(out.getMethod("println",parms).makeRef()));
       */
      toinsert.add(Baf.newIfEqInst((Unit) units.getSuccOf(nonTrap)));
    }

    ArrayList<Unit> toinserttry = new ArrayList<Unit>();
    while (stack.size() > 0) {
      toinserttry.add(Baf.newPopInst(stack.pop()));
    }
    toinserttry.add(Baf.newPushInst(constantFactory.getNullConstant()));

    Unit handler = Baf.newThrowInst();
    int rand = Rand.getInt(toinserttry.size());
    while (rand++ < toinserttry.size()) {
      toinsert.add(toinserttry.get(0));
      toinserttry.remove(0);
    }
    if (toinserttry.size() > 0) {
      toinserttry.add(Baf.newGotoInst(handler));
      toinsert.add(Baf.newGotoInst(toinserttry.get(0)));
      units.insertBefore(toinserttry, nop);
    }

    toinsert.add(handler);
    units.insertAfter(toinsert, nonTrap);

    b.getTraps().add(Baf.newTrap(ThrowSet.getRandomThrowable(), addedUnits.get(0), nop, handler));

    count += addedUnits.size();
    // fixme debug??
    if (addedUnits.size() > 0 && true) {
      StackTypeHeightCalculator.calculateStackHeights(b);
      // StackTypeHeightCalculator.printStack(units, StackTypeHeightCalculator.calculateStackHeights(b), false);
    }
  }

  private Unit findNonTrappedUnit(PatchingChain<Unit> units, Chain<Trap> traps) {
    int intrap = 0;
    ArrayList<Unit> untrapped = new ArrayList<Unit>();
    Iterator<Unit> it = units.snapshotIterator();
    while (it.hasNext()) {
      Unit u = it.next();
      Iterator<Trap> tit = traps.iterator();
      while (tit.hasNext()) {
        Trap t = tit.next();
        if (u == t.getBeginUnit()) {
          intrap++;
        }
        if (u == t.getEndUnit()) {
          intrap--;
        }
      }

      if (intrap == 0) {
        untrapped.add(u);
      }
    }

    Unit result = null;
    if (untrapped.size() > 0) {
      int count = 0;
      while (result == null && count < 10) {
        count++;
        result = untrapped.get(Rand.getInt(999999) % untrapped.size());
        if (!result.fallsThrough() || units.getSuccOf(result) == null || units.getSuccOf(result) instanceof ThrowInst) {
          result = null;
        }
      }
    }

    return result;
  }

  private boolean isIf(Unit u) {
    // TODO: will a RET statement be a TargetArgInst?
    return (u instanceof TargetArgInst) && !(u instanceof GotoInst) && !(u instanceof JSRInst);
  }
}
