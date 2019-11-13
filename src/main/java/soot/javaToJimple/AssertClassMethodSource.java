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

public class AssertClassMethodSource implements soot.MethodSource {

  public soot.Body getBody(soot.SootMethod sootMethod, String phaseName) {

    soot.Body classBody = soot.jimple.myJimple.newBody(sootMethod);

    // static invoke of forName
    soot.jimple.ParameterRef paramRef = soot.jimple.myJimple.newParameterRef(soot.RefType.v("java.lang.String"), 0);

    soot.Local paramLocal = soot.jimple.myJimple.newLocal("$r0", soot.RefType.v("java.lang.String"));
    classBody.getLocals().add(paramLocal);
    soot.jimple.Stmt stmt = soot.jimple.myJimple.newIdentityStmt(paramLocal, paramRef);
    classBody.getUnits().add(stmt);

    ArrayList paramTypes = new ArrayList();
    paramTypes.add(soot.RefType.v("java.lang.String"));
    soot.SootMethodRef methodToInvoke = soot.myScene.makeMethodRef(soot.myScene.getSootClass("java.lang.Class"),
        "forName", paramTypes, soot.RefType.v("java.lang.Class"), true);
    soot.Local invokeLocal = soot.jimple.myJimple.newLocal("$r1", soot.RefType.v("java.lang.Class"));
    classBody.getLocals().add(invokeLocal);
    ArrayList params = new ArrayList();
    params.add(paramLocal);
    soot.jimple.Expr invokeExpr = soot.jimple.myJimple.newStaticInvokeExpr(methodToInvoke, params);
    soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(invokeLocal, invokeExpr);
    classBody.getUnits().add(assign);

    // return
    soot.jimple.Stmt retStmt = soot.jimple.myJimple.newReturnStmt(invokeLocal);
    classBody.getUnits().add(retStmt);

    // catch
    soot.Local catchRefLocal = soot.jimple.myJimple.newLocal("$r2", soot.RefType.v("java.lang.ClassNotFoundException"));
    classBody.getLocals().add(catchRefLocal);
    soot.jimple.CaughtExceptionRef caughtRef = soot.jimple.myJimple.newCaughtExceptionRef();
    soot.jimple.Stmt caughtIdentity = soot.jimple.myJimple.newIdentityStmt(catchRefLocal, caughtRef);
    classBody.getUnits().add(caughtIdentity);

    // new no class def found error
    soot.Local noClassDefLocal = soot.jimple.myJimple.newLocal("$r3", soot.RefType.v("java.lang.NoClassDefFoundError"));
    classBody.getLocals().add(noClassDefLocal);
    soot.jimple.Expr newExpr = soot.jimple.myJimple.newNewExpr(soot.RefType.v("java.lang.NoClassDefFoundError"));
    soot.jimple.Stmt noClassDefAssign = soot.jimple.myJimple.newAssignStmt(noClassDefLocal, newExpr);
    classBody.getUnits().add(noClassDefAssign);

    // no class def found invoke
    paramTypes = new ArrayList();
    soot.SootMethodRef initMethToInvoke = soot.myScene.makeMethodRef(
        soot.myScene.getSootClass("java.lang.NoClassDefFoundError"), "<init>", paramTypes, soot.VoidType.v(), false);
    params = new ArrayList();
    soot.jimple.Expr initInvoke = soot.jimple.myJimple.newSpecialInvokeExpr(noClassDefLocal, initMethToInvoke, params);
    soot.jimple.Stmt initStmt = soot.jimple.myJimple.newInvokeStmt(initInvoke);
    classBody.getUnits().add(initStmt);

    // get exception message
    soot.Local throwLocal = soot.jimple.myJimple.newLocal("$r4", soot.RefType.v("java.lang.Throwable"));
    classBody.getLocals().add(throwLocal);
    paramTypes = new ArrayList();
    paramTypes.add(soot.RefType.v("java.lang.Throwable"));
    params = new ArrayList();
    params.add(catchRefLocal);
    soot.SootMethodRef messageMethToInvoke = soot.myScene.makeMethodRef(soot.myScene.getSootClass("java.lang.Throwable"),
        "initCause", paramTypes, soot.RefType.v("java.lang.Throwable"), false);

    soot.jimple.Expr messageInvoke
        = soot.jimple.myJimple.newVirtualInvokeExpr(noClassDefLocal, messageMethToInvoke, params);
    soot.jimple.Stmt messageAssign = soot.jimple.myJimple.newAssignStmt(throwLocal, messageInvoke);
    classBody.getUnits().add(messageAssign);

    // throw
    soot.jimple.Stmt throwStmt = soot.jimple.myJimple.newThrowStmt(throwLocal);
    throwStmt.addTag(new soot.tagkit.ThrowCreatedByCompilerTag());
    classBody.getUnits().add(throwStmt);

    // trap
    soot.Trap trap = soot.jimple.myJimple.newTrap(soot.myScene.getSootClass("java.lang.ClassNotFoundException"), assign,
        retStmt, caughtIdentity);
    classBody.getTraps().add(trap);

    return classBody;

  }
}
