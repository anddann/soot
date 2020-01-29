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
import soot.BooleanType;
import soot.G;
import soot.PatchingChain;
import soot.RefType;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.baf.Baf;
import soot.baf.IfNonNullInst;
import soot.baf.IfNullInst;
import soot.jbco.IJbcoTransform;
import soot.jbco.util.BodyBuilder;
import soot.jbco.util.Rand;
import soot.jimple.NullConstant;

/**
 * @author Michael Batchelder
 * 
 *         Created on 20-Jun-2006
 */
public class IfNullToTryCatch extends BodyTransformer implements IJbcoTransform {

  int count = 0;
  int totalifs = 0;

  public static String dependancies[] = new String[] { "bb.jbco_riitcb", "bb.jbco_ful", "bb.lp" };

  public String[] getDependencies() {
    return dependancies;
  }

  public static String name = "bb.jbco_riitcb";

  public String getName() {
    return name;
  }

  public void outputSummary() {
    out.println("If(Non)Nulls changed to traps: " + count);
    out.println("Total ifs found: " + totalifs);
  }

  protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
    int weight = soot.jbco.Main.getWeight(phaseName, b.getMethod().getSignature());
    if (weight == 0) {
      return;
    }

    SootClass exc = G.v().soot_Scene().getSootClass("java.lang.NullPointerException");
    SootClass obj = G.v().soot_Scene().getSootClass("java.lang.Object");
    SootMethod toStrg = obj.getMethodByName("toString");
    SootMethod eq = obj.getMethodByName("equals");
    boolean change = false;
    PatchingChain<Unit> units = b.getUnits();
    Iterator<Unit> uit = units.snapshotIterator();
    while (uit.hasNext()) {
      Unit u = uit.next();
      if (BodyBuilder.isBafIf(u)) {
        totalifs++;
      }

      if (u instanceof IfNullInst && Rand.getInt(10) <= weight) {
        Unit targ = ((IfNullInst) u).getTarget();
        Unit succ = units.getSuccOf(u);
        Unit pop = Baf.newPopInst(primTypeCollector.getRefType());
        Unit popClone = (Unit) pop.clone();
        units.insertBefore(pop, targ);

        Unit gotoTarg = Baf.newGotoInst(targ);
        units.insertBefore(gotoTarg, pop);

        if (Rand.getInt(2) == 0) {
          Unit methCall = Baf.newVirtualInvokeInst(toStrg.makeRef());
          units.insertBefore(methCall, u);

          if (Rand.getInt(2) == 0) {
            units.remove(u);
            units.insertAfter(popClone, methCall);
          }

          b.getTraps().add(Baf.newTrap(exc, methCall, succ, pop));
        } else {
          Unit throwu = Baf.newThrowInst();
          units.insertBefore(throwu, u);
          units.remove(u);

          units.insertBefore(Baf.newPushInst(constantFactory.getNullConstant()), throwu);
          Unit ifunit = Baf.newIfCmpNeInst(primTypeCollector.getRefType(), succ);
          units.insertBefore(ifunit, throwu);
          units.insertBefore(Baf.newPushInst(constantFactory.getNullConstant()), throwu);

          b.getTraps().add(Baf.newTrap(exc, throwu, succ, pop));
        }
        count++;
        change = true;
      } else if (u instanceof IfNonNullInst && Rand.getInt(10) <= weight) {
        Unit targ = ((IfNonNullInst) u).getTarget();

        Unit methCall = Baf.newVirtualInvokeInst(eq.makeRef());
        units.insertBefore(methCall, u);
        units.insertBefore(Baf.newPushInst(constantFactory.getNullConstant()), methCall);
        if (Rand.getInt(2) == 0) {
          Unit pop = Baf.newPopInst(primTypeCollector.getBooleanType());
          units.insertBefore(pop, u);
          Unit gotoTarg = Baf.newGotoInst(targ);
          units.insertBefore(gotoTarg, u);

          pop = Baf.newPopInst(primTypeCollector.getRefType());
          units.insertAfter(pop, u);
          units.remove(u);

          // add first, so it is always checked first in the exception table
          b.getTraps().addFirst(Baf.newTrap(exc, methCall, gotoTarg, pop));
        } else {
          Unit iffalse = Baf.newIfEqInst(targ);
          units.insertBefore(iffalse, u);
          units.insertBefore(Baf.newPushInst(constantFactory.getNullConstant()), u);
          Unit pop = Baf.newPopInst(primTypeCollector.getRefType());
          units.insertAfter(pop, u);
          units.remove(u);

          // add first, so it is always checked first in the exception table
          b.getTraps().addFirst(Baf.newTrap(exc, methCall, iffalse, pop));
        }
        count++;
        change = true;
      }
    }

    if (change && debug) {
      StackTypeHeightCalculator.calculateStackHeights(b);
      // StackTypeHeightCalculator.printStack(units, StackTypeHeightCalculator.calculateStackHeights(b), true)
    }
  }
}
