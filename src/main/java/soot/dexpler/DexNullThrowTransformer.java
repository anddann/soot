package soot.dexpler;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 2018 Raja Vallée-Rai and others
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

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;

import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.scalar.LocalCreation;

/**
 * Some Android applications throw null references, e.g.,
 *
 * a = null; throw a;
 *
 * This will make unit graph construction fail as no targets of the throw statement can be found. We therefore replace such
 * statements with direct NullPointerExceptions which would happen at runtime anyway.
 *
 * @author Steven Arzt
 *
 */
public class DexNullThrowTransformer extends BodyTransformer {

  private ConstantFactory constantFactory;
  private Scene myScene;

  public DexNullThrowTransformer(ConstantFactory constantFactory, Scene myScene) {
    this.constantFactory = constantFactory;
    this.myScene = myScene;
  }

  public static DexNullThrowTransformer v(ConstantFactory constantFactory, Scene myScene) {
    return new DexNullThrowTransformer(constantFactory, myScene);
  }

  @Override
  protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
    LocalCreation lc = new LocalCreation(b.getLocals(), "ex");

    for (Iterator<Unit> unitIt = b.getUnits().snapshotIterator(); unitIt.hasNext();) {
      Unit u = unitIt.next();

      // Check for a null exception
      if (u instanceof ThrowStmt) {
        ThrowStmt throwStmt = (ThrowStmt) u;
        if (throwStmt.getOp() == constantFactory.getNullConstant() || throwStmt.getOp().equals(constantFactory.createIntConstant(0))
            || throwStmt.getOp().equals(constantFactory.createLongConstant(0))) {
          createThrowStmt(b, throwStmt, lc);
        }
      }
    }
  }

  /**
   * Creates a new statement that throws a NullPointerException
   *
   * @param body
   *          The body in which to create the statement
   * @param oldStmt
   *          The old faulty statement that shall be replaced with the exception
   * @param lc
   *          The object for creating new locals
   */
  private void createThrowStmt(Body body, Unit oldStmt, LocalCreation lc) {
    RefType tp = RefType.v("java.lang.NullPointerException",myScene);
    Local lcEx = lc.newLocal(tp);

    SootMethodRef constructorRef
        = myScene.makeConstructorRef(tp.getSootClass(), Collections.singletonList((Type) RefType.v("java.lang.String",myScene)));

    // Create the exception instance
    Stmt newExStmt = Jimple.newAssignStmt(lcEx, Jimple.newNewExpr(tp));
    body.getUnits().insertBefore(newExStmt, oldStmt);
    Stmt invConsStmt = Jimple.newInvokeStmt(Jimple.newSpecialInvokeExpr(lcEx, constructorRef,
        Collections.singletonList(constantFactory.createStringConstant("Null throw statement replaced by Soot"))));
    body.getUnits().insertBefore(invConsStmt, oldStmt);

    // Throw the exception
    body.getUnits().swapWith(oldStmt, Jimple.newThrowStmt(lcEx));
  }

}
