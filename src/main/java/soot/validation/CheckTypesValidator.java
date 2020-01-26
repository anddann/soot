package soot.validation;

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

import com.google.inject.Inject;

import java.util.List;

import soot.ArrayType;
import soot.Body;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.LongType;
import soot.NullType;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;

public class CheckTypesValidator implements BodyValidator {

  private Scene myScene;

  @Inject
  public CheckTypesValidator(Scene myScene) {

    this.myScene = myScene;
  }

  @Override
  public void validate(Body body, List<ValidationException> exception) {
    for (Unit u : body.getUnits()) {
      String errorSuffix = " at " + u + " in " + body.getMethod();

      if (u instanceof DefinitionStmt) {
        DefinitionStmt astmt = (DefinitionStmt) u;
        if (!(astmt.getRightOp() instanceof CaughtExceptionRef)) {
          Type leftType = astmt.getLeftOp().getType().toMachineType();
          Type rightType = astmt.getRightOp().getType().toMachineType();

          checkCopy(astmt, body, exception, leftType, rightType, errorSuffix, myScene);
        }
      }

      if (u instanceof Stmt) {
        Stmt stmt = (Stmt) u;
        if (stmt.containsInvokeExpr()) {
          SootMethodRef called = stmt.getInvokeExpr().getMethodRef();
          InvokeExpr iexpr = stmt.getInvokeExpr();

          if (iexpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr iiexpr = (InstanceInvokeExpr) iexpr;
            checkCopy(stmt, body, exception, called.declaringClass().getType(), iiexpr.getBase().getType(),
                " in receiver of call" + errorSuffix, myScene);
          }

          if (called.parameterTypes().size() != iexpr.getArgCount()) {
            exception.add(new ValidationException(stmt, "Argument count does not match the signature of the called function",
                "Warning: Argument count doesn't match up with signature in call" + errorSuffix + " in "
                    + body.getMethod()));
          } else {
            for (int i = 0; i < iexpr.getArgCount(); i++) {
              checkCopy(stmt, body, exception, called.parameterType(i).toMachineType(),
                  iexpr.getArg(i).getType().toMachineType(),
                  " in argument " + i + " of call" + errorSuffix + " (Note: Parameters are zero-indexed)", myScene);
            }
          }
        }
      }
    }
  }

  private void checkCopy(Unit stmt, Body body, List<ValidationException> exception, Type leftType, Type rightType,
      String errorSuffix, Scene myScene) {
    if (leftType instanceof PrimType || rightType instanceof PrimType) {
      if (leftType instanceof IntType && rightType instanceof IntType) {
        return;
      }
      if (leftType instanceof LongType && rightType instanceof LongType) {
        return;
      }
      if (leftType instanceof FloatType && rightType instanceof FloatType) {
        return;
      }
      if (leftType instanceof DoubleType && rightType instanceof DoubleType) {
        return;
      }
      exception.add(
          new ValidationException(stmt, "", "Warning: Bad use of primitive type" + errorSuffix + " in " + body.getMethod()));
    }

    if (rightType instanceof NullType) {
      return;
    }
    if (leftType instanceof RefType && ((RefType) leftType).getClassName().equals("java.lang.Object")) {
      return;
    }

    if (leftType instanceof ArrayType || rightType instanceof ArrayType) {
      if (leftType instanceof ArrayType && rightType instanceof ArrayType) {
        return;
      }
      // it is legal to assign arrays to variables of type Serializable,
      // Cloneable or Object
      if (rightType instanceof ArrayType) {
        if (leftType.equals(RefType.v("java.io.Serializable", myScene))
            || leftType.equals(RefType.v("java.lang.Cloneable", myScene))
            || leftType.equals(RefType.v("java.lang.Object", myScene))) {
          return;
        }
      }

      exception
          .add(new ValidationException(stmt, "Warning: Bad use of array type" + errorSuffix + " in " + body.getMethod()));
    }

    if (leftType instanceof RefType && rightType instanceof RefType) {
      SootClass leftClass = ((RefType) leftType).getSootClass();
      SootClass rightClass = ((RefType) rightType).getSootClass();
      if (leftClass.isPhantom() || rightClass.isPhantom()) {
        return;
      }

      if (leftClass.isInterface()) {
        if (rightClass.isInterface()) {
          if (!(leftClass.getName().equals(rightClass.getName())
              || myScene.getActiveHierarchy().isInterfaceSubinterfaceOf(rightClass, leftClass))) {
            exception.add(new ValidationException(stmt,
                "Warning: Bad use of interface type" + errorSuffix + " in " + body.getMethod()));
          }
        } else {
          // No quick way to check this for now.
        }
      } else {
        if (rightClass.isInterface()) {
          exception.add(new ValidationException(stmt, "Warning: trying to use interface type where non-Object class expected"
              + errorSuffix + " in " + body.getMethod()));
        } else {
          if (!myScene.getActiveHierarchy().isClassSubclassOfIncluding(rightClass, leftClass)) {
            exception.add(
                new ValidationException(stmt, "Warning: Bad use of class type" + errorSuffix + " in " + body.getMethod()));
          }
        }
      }
      return;
    }
    exception.add(new ValidationException(stmt, "Warning: Bad types" + errorSuffix + " in " + body.getMethod()));
  }

  @Override
  public boolean isBasicValidator() {
    return false;
  }
}
