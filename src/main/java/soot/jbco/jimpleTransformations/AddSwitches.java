package soot.jbco.jimpleTransformations;

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
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PatchingChain;
import soot.PrimType;
import soot.PrimTypeCollector;
import soot.RefType;
import soot.SootField;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jbco.IJbcoTransform;
import soot.jbco.util.Rand;
import soot.jimple.ConstantFactory;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.Jimple;
import soot.options.Options;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.interaction.InteractionHandler;
import soot.util.PhaseDumper;

/**
 * @author Michael Batchelder
 *
 *         Created on 10-Jul-2006
 */
public class AddSwitches extends BodyTransformer implements IJbcoTransform {

  int switchesadded = 0;
  private InteractionHandler myInteractionHandler;
  private PhaseDumper myPhaseDumper;
  private Options myOptions;
  private FieldRenamer myFieldRenamer;
  private PrimTypeCollector primTypeCollector;
  private ConstantFactory constantFactory;

  public AddSwitches(InteractionHandler myInteractionHandler, PhaseDumper myPhaseDumper, Options myOptions,
                     FieldRenamer myFieldRenamer, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory) {
    this.myInteractionHandler = myInteractionHandler;
    this.myPhaseDumper = myPhaseDumper;
    this.myOptions = myOptions;
    this.myFieldRenamer = myFieldRenamer;
    this.primTypeCollector = primTypeCollector;
    this.constantFactory = constantFactory;
  }

  public void outputSummary() {

    // out.println("Switches added: " + switchesadded);
  }

  public static String dependancies[] = new String[] { "wjtp.jbco_fr", "jtp.jbco_adss", "bb.jbco_ful" };

  public String[] getDependencies() {
    return dependancies;
  }

  public static String name = "jtp.jbco_adss";

  public String getName() {
    return name;
  }

  public boolean checkTraps(Unit u, Body b) {
    Iterator<Trap> it = b.getTraps().iterator();
    while (it.hasNext()) {
      Trap t = it.next();
      if (t.getBeginUnit() == u || t.getEndUnit() == u || t.getHandlerUnit() == u) {
        return true;
      }
    }

    return false;
  }

  protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
    if (b.getMethod().getSignature().indexOf("<clinit>") >= 0) {
      return;
    }
    int weight = soot.jbco.Main.getWeight(phaseName, b.getMethod().getSignature());
    if (weight == 0) {
      return;
    }

    New2InitFlowAnalysis fa
        = new New2InitFlowAnalysis(new BriefUnitGraph(b, myPhaseDumper), myOptions.interactive_mode(), myInteractionHandler);

    Vector<Unit> zeroheight = new Vector<Unit>();
    PatchingChain<Unit> units = b.getUnits();

    Unit first = null;
    for (Unit unit : units) {
      if (unit instanceof IdentityStmt) {
        continue;
      }

      first = unit;
      break;
    }

    Iterator<Unit> it = units.snapshotIterator();
    while (it.hasNext()) {
      Unit unit = (Unit) it.next();
      if (unit instanceof IdentityStmt || checkTraps(unit, b)) {
        continue;
      }
      // very conservative estimate about where new-<init> ranges are
      if (fa.getFlowAfter(unit).isEmpty() && fa.getFlowBefore(unit).isEmpty()) {
        zeroheight.add(unit);
      }
    }

    if (zeroheight.size() < 3) {
      return;
    }

    int idx = 0;
    Unit u = null;
    for (int i = 0; i < zeroheight.size(); i++) {
      idx = Rand.getInt(zeroheight.size() - 1) + 1;
      u = (Unit) zeroheight.get(idx);
      if (u.fallsThrough()) {
        break;
      }
      u = null;
    }
    // couldn't find a unit that fell through
    if (u == null || Rand.getInt(10) > weight) {
      return;
    }

    zeroheight.remove(idx);
    while (zeroheight.size() > (weight > 3 ? weight : 3)) {
      zeroheight.remove(Rand.getInt(zeroheight.size()));
    }

    Collection<Local> locals = b.getLocals();
    List<Unit> targs = new ArrayList<Unit>();
    targs.addAll(zeroheight);

    SootField ops[] = myFieldRenamer.getRandomOpaques();

    Local b1 = Jimple.newLocal("addswitchesbool1", primTypeCollector.getBooleanType());
    locals.add(b1);
    Local b2 = Jimple.newLocal("addswitchesbool2", primTypeCollector.getBooleanType());
    locals.add(b2);

    if (ops[0].getType() instanceof PrimType) {
      units.insertBefore(Jimple.newAssignStmt(b1, Jimple.newStaticFieldRef(ops[0].makeRef())), u);
    } else {
      RefType rt = (RefType) ops[0].getType();
      SootMethod m = rt.getSootClass().getMethodByName("booleanValue");
      Local B = Jimple.newLocal("addswitchesBOOL1", rt);
      locals.add(B);
      units.insertBefore(Jimple.newAssignStmt(B, Jimple.newStaticFieldRef(ops[0].makeRef())), u);
      units.insertBefore(
          Jimple.newAssignStmt(b1, Jimple.newVirtualInvokeExpr(B, m.makeRef(), Collections.<Value>emptyList(), myOptions)), u);
    }
    if (ops[1].getType() instanceof PrimType) {
      units.insertBefore(Jimple.newAssignStmt(b2, Jimple.newStaticFieldRef(ops[1].makeRef())), u);
    } else {
      RefType rt = (RefType) ops[1].getType();
      SootMethod m = rt.getSootClass().getMethodByName("booleanValue");
      Local B = Jimple.newLocal("addswitchesBOOL2", rt);
      locals.add(B);
      units.insertBefore(Jimple.newAssignStmt(B, Jimple.newStaticFieldRef(ops[1].makeRef())), u);
      units.insertBefore(
          Jimple.newAssignStmt(b2, Jimple.newVirtualInvokeExpr(B, m.makeRef(), Collections.<Value>emptyList(), myOptions)), u);
    }

    IfStmt ifstmt = Jimple.newIfStmt(Jimple.newNeExpr(b1, b2), u);
    units.insertBefore(ifstmt, u);

    Local l = Jimple.newLocal("addswitchlocal", primTypeCollector.getIntType());
    locals.add(l);
    units.insertBeforeNoRedirect(Jimple.newAssignStmt(l, constantFactory.createIntConstant(0)), first);
    units.insertAfter(Jimple.newTableSwitchStmt(l, 1, zeroheight.size(), targs, u), ifstmt);

    switchesadded += zeroheight.size() + 1;

    Iterator<Unit> tit = targs.iterator();
    while (tit.hasNext()) {
      Unit nxt = (Unit) tit.next();
      if (Rand.getInt(5) < 4) {
        units.insertBefore(
            Jimple.newAssignStmt(l, Jimple.newAddExpr(l, constantFactory.createIntConstant(Rand.getInt(3) + 1))), nxt);
      }
    }

    ifstmt.setTarget(u);
  }
}
