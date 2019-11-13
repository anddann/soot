package soot.javaToJimple;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2004 Jennifer Lhotak
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
import java.util.HashMap;
import java.util.List;

import polyglot.ast.Block;
import polyglot.ast.FieldDecl;

import soot.MethodSource;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootField;

public class PolyglotMethodSource implements MethodSource {

  private polyglot.ast.Block block;
  private List formals;
  private ArrayList<FieldDecl> fieldInits;
  private ArrayList<FieldDecl> staticFieldInits;
  private ArrayList<Block> initializerBlocks;
  private ArrayList<Block> staticInitializerBlocks;
  private soot.Local outerClassThisInit;
  private boolean hasAssert = false;
  private ArrayList<SootField> finalsList;
  private HashMap newToOuterMap;
  private AbstractJimpleBodyBuilder ajbb;

  public PolyglotMethodSource() {
    this.block = null;
    this.formals = null;
  }

  public PolyglotMethodSource(polyglot.ast.Block block, List formals) {
    this.block = block;
    this.formals = formals;
  }

  public soot.Body getBody(soot.SootMethod sm, String phaseName) {
    // JimpleBodyBuilder jbb = new JimpleBodyBuilder();
    soot.jimple.JimpleBody jb = ajbb.createJimpleBody(block, formals, sm);

    PackmyManager.getPack("jj").apply(jb);
    return jb;
  }

  public void setJBB(AbstractJimpleBodyBuilder ajbb) {
    this.ajbb = ajbb;
  }

  public void setFieldInits(ArrayList<FieldDecl> fieldInits) {
    this.fieldInits = fieldInits;
  }

  public void setStaticFieldInits(ArrayList<FieldDecl> staticFieldInits) {
    this.staticFieldInits = staticFieldInits;
  }

  public ArrayList<FieldDecl> getFieldInits() {
    return fieldInits;
  }

  public ArrayList<FieldDecl> getStaticFieldInits() {
    return staticFieldInits;
  }

  public void setStaticInitializerBlocks(ArrayList<Block> staticInits) {
    staticInitializerBlocks = staticInits;
  }

  public void setInitializerBlocks(ArrayList<Block> inits) {
    initializerBlocks = inits;
  }

  public ArrayList<Block> getStaticInitializerBlocks() {
    return staticInitializerBlocks;
  }

  public ArrayList<Block> getInitializerBlocks() {
    return initializerBlocks;
  }

  public void setOuterClassThisInit(soot.Local l) {
    outerClassThisInit = l;
  }

  public soot.Local getOuterClassThisInit() {
    return outerClassThisInit;
  }

  public boolean hasAssert() {
    return hasAssert;
  }

  public void hasAssert(boolean val) {
    hasAssert = val;
  }

  public void addAssertInits(soot.Body body) {
    // if class is inner get desired assertion status from outer most class
    soot.SootClass assertStatusClass = body.getMethod().getDeclaringClass();
    HashMap<SootClass, InnerClassInfo> innerMap = soot.javaToJimple.myInitialResolver.getInnerClassInfoMap();
    while ((innerMap != null) && (innerMap.containsKey(assertStatusClass))) {
      assertStatusClass = innerMap.get(assertStatusClass).getOuterClass();
    }

    String paramName = assertStatusClass.getName();
    String fieldName = "class$" + assertStatusClass.getName().replaceAll(".", "$");

    if (assertStatusClass.isInterface()) {
      assertStatusClass = myInitialResolver.specialAnonMap().get(assertStatusClass);
    }

    // field ref
    soot.SootFieldRef field
        = soot.myScene.makeFieldRef(assertStatusClass, fieldName, soot.RefType.v("java.lang.Class"), true);

    soot.Local fieldLocal = soot.jimple.myJimple.newLocal("$r0", soot.RefType.v("java.lang.Class"));

    body.getLocals().add(fieldLocal);

    soot.jimple.FieldRef fieldRef = soot.jimple.myJimple.newStaticFieldRef(field);

    soot.jimple.AssignStmt fieldAssignStmt = soot.jimple.myJimple.newAssignStmt(fieldLocal, fieldRef);

    body.getUnits().add(fieldAssignStmt);

    // if field not null
    soot.jimple.ConditionExpr cond = soot.jimple.myJimple.newNeExpr(fieldLocal, soot.jimple.myNullConstant);

    soot.jimple.NopStmt nop1 = soot.jimple.myJimple.newNopStmt();

    soot.jimple.IfStmt ifStmt = soot.jimple.myJimple.newIfStmt(cond, nop1);
    body.getUnits().add(ifStmt);

    // if alternative
    soot.Local invokeLocal = soot.jimple.myJimple.newLocal("$r1", soot.RefType.v("java.lang.Class"));

    body.getLocals().add(invokeLocal);

    ArrayList paramTypes = new ArrayList();
    paramTypes.add(soot.RefType.v("java.lang.String"));

    soot.SootMethodRef methodToInvoke
        = soot.myScene.makeMethodRef(assertStatusClass, "class$", paramTypes, soot.RefType.v("java.lang.Class"), true);

    ArrayList params = new ArrayList();
    params.add(soot.jimple.StringConstant.v(paramName));
    soot.jimple.StaticInvokeExpr invoke = soot.jimple.myJimple.newStaticInvokeExpr(methodToInvoke, params);
    soot.jimple.AssignStmt invokeAssign = soot.jimple.myJimple.newAssignStmt(invokeLocal, invoke);

    body.getUnits().add(invokeAssign);

    // field ref assign
    soot.jimple.AssignStmt fieldRefAssign = soot.jimple.myJimple.newAssignStmt(fieldRef, invokeLocal);

    body.getUnits().add(fieldRefAssign);

    soot.jimple.NopStmt nop2 = soot.jimple.myJimple.newNopStmt();

    soot.jimple.GotoStmt goto1 = soot.jimple.myJimple.newGotoStmt(nop2);

    body.getUnits().add(goto1);
    // add nop1 - and if consequence
    body.getUnits().add(nop1);

    soot.jimple.AssignStmt fieldRefAssign2 = soot.jimple.myJimple.newAssignStmt(invokeLocal, fieldRef);

    body.getUnits().add(fieldRefAssign2);

    body.getUnits().add(nop2);

    // boolean tests
    soot.Local boolLocal1 = soot.jimple.myJimple.newLocal("$z0", soot.BooleanType.v());
    body.getLocals().add(boolLocal1);
    soot.Local boolLocal2 = soot.jimple.myJimple.newLocal("$z1", soot.BooleanType.v());
    body.getLocals().add(boolLocal2);

    // virtual invoke
    soot.SootMethodRef vMethodToInvoke = myScene.makeMethodRef(soot.myScene.getSootClass("java.lang.Class"),
        "desiredAssertionStatus", new ArrayList(), soot.BooleanType.v(), false);
    soot.jimple.VirtualInvokeExpr vInvoke
        = soot.jimple.myJimple.newVirtualInvokeExpr(invokeLocal, vMethodToInvoke, new ArrayList());

    soot.jimple.AssignStmt testAssign = soot.jimple.myJimple.newAssignStmt(boolLocal1, vInvoke);

    body.getUnits().add(testAssign);

    // if
    soot.jimple.ConditionExpr cond2 = soot.jimple.myJimple.newNeExpr(boolLocal1, soot.jimple.IntConstant.v(0));

    soot.jimple.NopStmt nop3 = soot.jimple.myJimple.newNopStmt();

    soot.jimple.IfStmt ifStmt2 = soot.jimple.myJimple.newIfStmt(cond2, nop3);
    body.getUnits().add(ifStmt2);

    // alternative
    soot.jimple.AssignStmt altAssign = soot.jimple.myJimple.newAssignStmt(boolLocal2, soot.jimple.IntConstant.v(1));

    body.getUnits().add(altAssign);

    soot.jimple.NopStmt nop4 = soot.jimple.myJimple.newNopStmt();

    soot.jimple.GotoStmt goto2 = soot.jimple.myJimple.newGotoStmt(nop4);

    body.getUnits().add(goto2);

    body.getUnits().add(nop3);

    soot.jimple.AssignStmt conAssign = soot.jimple.myJimple.newAssignStmt(boolLocal2, soot.jimple.IntConstant.v(0));

    body.getUnits().add(conAssign);

    body.getUnits().add(nop4);

    // field assign
    soot.SootFieldRef fieldD
        = myScene.makeFieldRef(body.getMethod().getDeclaringClass(), "$assertionsDisabled", soot.BooleanType.v(), true);

    soot.jimple.FieldRef fieldRefD = soot.jimple.myJimple.newStaticFieldRef(fieldD);
    soot.jimple.AssignStmt fAssign = soot.jimple.myJimple.newAssignStmt(fieldRefD, boolLocal2);
    body.getUnits().add(fAssign);

  }

  public void setFinalsList(ArrayList<SootField> list) {
    finalsList = list;
  }

  public ArrayList<SootField> getFinalsList() {
    return finalsList;
  }

  public void setNewToOuterMap(HashMap map) {
    newToOuterMap = map;
  }

  public HashMap getNewToOuterMap() {
    return newToOuterMap;
  }
}
