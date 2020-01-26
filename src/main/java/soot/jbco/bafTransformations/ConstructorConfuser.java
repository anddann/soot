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

import java.util.Iterator;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PatchingChain;
import soot.PrimTypeCollector;
import soot.RefType;
import soot.SootClass;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.baf.Baf;
import soot.baf.LoadInst;
import soot.baf.SpecialInvokeInst;
import soot.jbco.IJbcoTransform;
import soot.jbco.util.BodyBuilder;
import soot.jbco.util.Rand;
import soot.jbco.util.ThrowSet;
import soot.jimple.ConstantFactory;

public class ConstructorConfuser extends BodyTransformer implements IJbcoTransform {

  static int count = 0;

  static int instances[] = new int[4];

  public static String dependancies[] = new String[] { "bb.jbco_dcc", "bb.jbco_ful", "bb.lp" };
  private Baf myBaf;
  private PrimTypeCollector primTypeCollector;
  private ConstantFactory constantFactory;

  public ConstructorConfuser(Baf myBaf, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory) {
    this.myBaf = myBaf;
    this.primTypeCollector = primTypeCollector;
    this.constantFactory = constantFactory;
  }

  public String[] getDependencies() {
    return dependancies;
  }

  public static String name = "bb.jbco_dcc";

  public String getName() {
    return name;
  }

  public void outputSummary() {
  //FIXME

    //out.println("Constructor methods have been jumbled: " + count);
  }

  @SuppressWarnings("fallthrough")
  protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
    if (!b.getMethod().getSubSignature().equals("void <init>()")) {
      return;
    }
    int weight = soot.jbco.Main.getWeight(phaseName, b.getMethod().getSignature());
    if (weight == 0) {
      return;
    }

    SootClass origClass = b.getMethod().getDeclaringClass();
    SootClass c = origClass;
    if (c.hasSuperclass()) {
      c = c.getSuperclass();
    } else {
      c = null;
    }

    PatchingChain<Unit> units = b.getUnits();
    Iterator<Unit> it = units.snapshotIterator();
    Unit prev = null;
    SpecialInvokeInst sii = null;
    while (it.hasNext()) {
      Unit u = (Unit) it.next();
      if (u instanceof SpecialInvokeInst) {
        sii = (SpecialInvokeInst) u;
        SootMethodRef smr = sii.getMethodRef();
        if (c == null || !smr.declaringClass().getName().equals(c.getName()) || !smr.name().equals("<init>")) {
          sii = null;
        } else {
          break;
        }
      }
      prev = u;
    }

    if (sii == null) {
      return;
    }

    int lowi = -1, lowest = 99999999, rand = Rand.getInt(4);
    for (int i = 0; i < instances.length; i++) {
      if (lowest > instances[i]) {
        lowest = instances[i];
        lowi = i;
      }
    }
    if (instances[rand] > instances[lowi]) {
      rand = lowi;
    }

    boolean done = false;
    switch (rand) {
      case 0:
        if (prev != null && prev instanceof LoadInst && sii.getMethodRef().parameterTypes().size() == 0
            && !BodyBuilder.isExceptionCaughtAt(units, sii, b.getTraps().iterator())) {

          Local bl = ((LoadInst) prev).getLocal();
          Map<Local, Local> locals = soot.jbco.Main.methods2Baf2JLocals.get(b.getMethod());
          if (locals != null && locals.containsKey(bl)) {
            Type t = ((Local) locals.get(bl)).getType();
            if (t instanceof RefType && ((RefType) t).getSootClass().getName().equals(origClass.getName())) {
              units.insertBefore(myBaf.newDup1Inst(primTypeCollector.getRefType()), sii);
              Unit ifinst = myBaf.newIfNullInst(sii);
              units.insertBeforeNoRedirect(ifinst, sii);
              units.insertAfter(myBaf.newThrowInst(), ifinst);
              units.insertAfter(myBaf.newPushInst(constantFactory.getNullConstant()), ifinst);

              Unit pop = myBaf.newPopInst(primTypeCollector.getRefType());
              units.add(pop);
              units.add((Unit) prev.clone());
              b.getTraps().add(myBaf.newTrap(ThrowSet.getRandomThrowable(), ifinst, sii, pop));
              if (Rand.getInt() % 2 == 0) {
                pop = (Unit) pop.clone();
                units.insertBefore(pop, sii);
                units.insertBefore(myBaf.newGotoInst(sii), pop);
                units.add(myBaf.newJSRInst(pop));
              } else {
                units.add(myBaf.newGotoInst(sii));
              }
              done = true;
              break;
            }
          }
        }
      case 1:
        if (!BodyBuilder.isExceptionCaughtAt(units, sii, b.getTraps().iterator())) {
          Unit handler = myBaf.newThrowInst();
          units.add(handler);
          b.getTraps().add(myBaf.newTrap(ThrowSet.getRandomThrowable(), sii, (Unit) units.getSuccOf(sii), handler));
          done = true;
          break;
        }
      case 2:
        if (sii.getMethodRef().parameterTypes().size() == 0
            && !BodyBuilder.isExceptionCaughtAt(units, sii, b.getTraps().iterator())) {
          while (c != null) {
            if (c.getName().equals("java.lang.Throwable")) {
              Unit throwThis = myBaf.newThrowInst();
              units.insertBefore(throwThis, sii);
              b.getTraps().add(myBaf.newTrap(origClass, throwThis, sii, sii));
              done = true;
              break;
            }

            if (c.hasSuperclass()) {
              c = c.getSuperclass();
            } else {
              c = null;
            }
          }
        }
        if (done) {
          break;
        }
      case 3:
        Unit pop = myBaf.newPopInst(primTypeCollector.getRefType());
        units.insertBefore(pop, sii);
        units.insertBeforeNoRedirect(myBaf.newJSRInst(pop), pop);
        done = true;
        break;
    }

    if (done) {
      instances[rand]++;
      count++;
    }
// FIXME
//    if (debug) {
//      StackTypeHeightCalculator.calculateStackHeights(b);
//    }
  }
}
