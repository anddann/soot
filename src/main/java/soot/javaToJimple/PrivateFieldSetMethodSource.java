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

import java.util.Iterator;

import soot.Scene;
import soot.Type;
import soot.jimple.Jimple;

public class PrivateFieldSetMethodSource implements soot.MethodSource {

  private final soot.Type fieldType;
  private final String fieldName;
  private final boolean isStatic;
  private Jimple myJimple;
  private Scene myScene;

  public PrivateFieldSetMethodSource(Type fieldType, String fieldName, boolean isStatic, Jimple myJimple, Scene myScene) {
    this.fieldType = fieldType;
    this.fieldName = fieldName;
    this.isStatic = isStatic;
    this.myJimple = myJimple;
    this.myScene = myScene;
  }

  public soot.Body getBody(soot.SootMethod sootMethod, String phaseName) {

    soot.Body body = myJimple.newBody(sootMethod);
    LocalGenerator lg = new LocalGenerator(body);

    soot.Local fieldBase = null;
    soot.Local assignLocal = null;
    // create parameters
    int paramCounter = 0;
    Iterator paramIt = sootMethod.getParameterTypes().iterator();
    while (paramIt.hasNext()) {
      soot.Type sootType = (soot.Type) paramIt.next();
      soot.Local paramLocal = lg.generateLocal(sootType);

      soot.jimple.ParameterRef paramRef = myJimple.newParameterRef(sootType, paramCounter);
      soot.jimple.Stmt stmt = myJimple.newIdentityStmt(paramLocal, paramRef);
      body.getUnits().add(stmt);

      if (paramCounter == 0) {
        fieldBase = paramLocal;
      }
      assignLocal = paramLocal;
      paramCounter++;
    }

    // create field type local
    // soot.Local fieldLocal = lg.generateLocal(fieldType);
    // assign local to fieldRef
    soot.SootFieldRef field = myScene.makeFieldRef(sootMethod.getDeclaringClass(), fieldName, fieldType, isStatic);

    soot.jimple.FieldRef fieldRef = null;
    if (isStatic) {
      fieldRef = myJimple.newStaticFieldRef(field);
    } else {
      fieldRef = myJimple.newInstanceFieldRef(fieldBase, field);
    }
    soot.jimple.AssignStmt assign = myJimple.newAssignStmt(fieldRef, assignLocal);
    body.getUnits().add(assign);

    // return local
    soot.jimple.Stmt retStmt = myJimple.newReturnStmt(assignLocal);
    body.getUnits().add(retStmt);

    return body;

  }
}
