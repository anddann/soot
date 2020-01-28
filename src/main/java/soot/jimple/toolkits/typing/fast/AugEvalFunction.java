package soot.jimple.toolkits.typing.fast;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2008 Ben Bellamy
 *
 * All rights reserved.
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

import java.util.Collection;
import java.util.Collections;

import soot.*;
import soot.jimple.AddExpr;
import soot.jimple.AndExpr;
import soot.jimple.ArrayRef;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.ClassConstant;
import soot.jimple.CmpExpr;
import soot.jimple.CmpgExpr;
import soot.jimple.CmplExpr;
import soot.jimple.DivExpr;
import soot.jimple.DoubleConstant;
import soot.jimple.EqExpr;
import soot.jimple.FieldRef;
import soot.jimple.FloatConstant;
import soot.jimple.GeExpr;
import soot.jimple.GtExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.JimpleBody;
import soot.jimple.LeExpr;
import soot.jimple.LengthExpr;
import soot.jimple.LongConstant;
import soot.jimple.LtExpr;
import soot.jimple.MethodHandle;
import soot.jimple.MethodType;
import soot.jimple.MulExpr;
import soot.jimple.NeExpr;
import soot.jimple.NegExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.OrExpr;
import soot.jimple.ParameterRef;
import soot.jimple.RemExpr;
import soot.jimple.ShlExpr;
import soot.jimple.ShrExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.SubExpr;
import soot.jimple.ThisRef;
import soot.jimple.UshrExpr;
import soot.jimple.XorExpr;

/**
 * @author Ben Bellamy
 */
public class AugEvalFunction implements IEvalFunction {
  private JimpleBody jb;

  public AugEvalFunction(JimpleBody jb) {
    this.jb = jb;
  }

  public static Type eval_(Typing tg, Value expr, Stmt stmt, JimpleBody jb, PrimTypeCollector primTypeCollector, Scene myScene) {
    if (expr instanceof ThisRef) {
      return ((ThisRef) expr).getType();
    } else if (expr instanceof ParameterRef) {
      return ((ParameterRef) expr).getType();
    } else if (expr instanceof Local) {
      Local ex = (Local) expr;
      // changed to prevent null pointer exception in case of phantom classes where a null typing is encountered
      // syed
      if (tg == null) {
        return null;
      } else {
        return tg.get(ex);
      }
    } else if (expr instanceof BinopExpr) {
      BinopExpr be = (BinopExpr) expr;

      Value opl = be.getOp1(), opr = be.getOp2();
      Type tl = eval_(tg, opl, stmt, jb, primTypeCollector, myScene), tr = eval_(tg, opr, stmt, jb, primTypeCollector, myScene);

      if (expr instanceof CmpExpr || expr instanceof CmpgExpr || expr instanceof CmplExpr) {
        return primTypeCollector.getByteType();
      } else if (expr instanceof GeExpr || expr instanceof GtExpr || expr instanceof LeExpr || expr instanceof LtExpr
          || expr instanceof EqExpr || expr instanceof NeExpr) {
        return primTypeCollector.getBooleanType();
      } else if (expr instanceof ShlExpr) {
        if (tl instanceof IntegerType) {
          return primTypeCollector.getIntType();
        } else {
          return tl;
        }
      } else if (expr instanceof ShrExpr || expr instanceof UshrExpr) {
        return tl;
      } else if (expr instanceof AddExpr || expr instanceof SubExpr || expr instanceof MulExpr || expr instanceof DivExpr
          || expr instanceof RemExpr) {
        if (tl instanceof IntegerType) {
          return primTypeCollector.getIntType();
        } else {
          return tl;
        }
      } else if (expr instanceof AndExpr || expr instanceof OrExpr || expr instanceof XorExpr) {
        if (tl instanceof IntegerType && tr instanceof IntegerType) {
          if (tl instanceof BooleanType) {
            if (tr instanceof BooleanType) {
              return primTypeCollector.getBooleanType();
            } else {
              return tr;
            }
          } else if (tr instanceof BooleanType) {
            return tl;
          } else {
            Collection<Type> rs = AugHierarchy.lcas_(tl, tr, myScene);
            // AugHierarchy.lcas_ is single-valued
            for (Type r : rs) {
              return r;
            }
            throw new RuntimeException();
          }
        } else {
          return tl;
        }
      } else {
        throw new RuntimeException("Unhandled binary expression: " + expr);
      }
    } else if (expr instanceof NegExpr) {
      Type t = eval_(tg, ((NegExpr) expr).getOp(), stmt, jb, primTypeCollector, myScene);
      if (t instanceof IntegerType) {
        /*
         * Here I repeat the behaviour of the original type assigner, but is it right? For example, -128 is a byte, but
         * -(-128) is not! --BRB
         */
        if (t instanceof Integer1Type || t instanceof BooleanType || t instanceof Integer127Type || t instanceof ByteType) {
          return primTypeCollector.getByteType();
        } else if (t instanceof ShortType || t instanceof Integer32767Type) {
          return primTypeCollector.getShortType();
        } else {
          return primTypeCollector.getIntType();
        }
      } else {
        return t;
      }
    } else if (expr instanceof CaughtExceptionRef) {
      RefType r = null;
      RefType throwableType = RefType.v("java.lang.Throwable", myScene);

      for (RefType t : TrapManager.getExceptionTypesOf(stmt, jb)) {
        if (r == null) {
          if (t.getSootClass().isPhantom()) {
            r = throwableType;
          } else {
            r = t;
          }
        } else {
          if (t.getSootClass().isPhantom()) {
            r = throwableType;
          } else {
            /*
             * In theory, we could have multiple exception types pointing here. The JLS requires the exception parameter be a
             * *subclass* of Throwable, so we do not need to worry about multiple inheritance.
             */
            r = BytecodeHierarchy.lcsc(r, t, throwableType);
          }
        }
      }

      if (r == null) {
        throw new RuntimeException(
            "Exception reference used other than as the first " + "statement of an exception handler.");
      }

      return r;
    } else if (expr instanceof ArrayRef) {
      Local av = (Local) ((ArrayRef) expr).getBase();
      Type at = tg.get(av);

      if (at instanceof ArrayType) {
        return ((ArrayType) at).getElementType();
      } else if (at instanceof RefType) {
        RefType ref = (RefType) at;
        if (ref.getSootClass().getName().equals("java.lang.Object")
            || ref.getSootClass().getName().equals("java.io.Serializable")
            || ref.getSootClass().getName().equals("java.lang.Cloneable")) {
          return ref;
        } else {
          return primTypeCollector.getBottomType();
        }
      } else {
        return primTypeCollector.getBottomType();
      }
    } else if (expr instanceof NewArrayExpr) {
      return ((NewArrayExpr) expr).getBaseType().makeArrayType();
    } else if (expr instanceof NewMultiArrayExpr) {
      return ((NewMultiArrayExpr) expr).getBaseType();
    } else if (expr instanceof CastExpr) {
      return ((CastExpr) expr).getCastType();
    } else if (expr instanceof InstanceOfExpr) {
      return primTypeCollector.getBooleanType();
    } else if (expr instanceof LengthExpr) {
      return primTypeCollector.getIntType();
    } else if (expr instanceof InvokeExpr) {
      return ((InvokeExpr) expr).getMethodRef().returnType();
    } else if (expr instanceof NewExpr) {
      return ((NewExpr) expr).getBaseType();
    } else if (expr instanceof FieldRef) {
      return ((FieldRef) expr).getType();
    } else if (expr instanceof DoubleConstant) {
      return primTypeCollector.getDoubleType();
    } else if (expr instanceof FloatConstant) {
      return primTypeCollector.getFloatType();
    } else if (expr instanceof IntConstant) {
      int value = ((IntConstant) expr).value;

      if (value >= 0 && value < 2) {
        return primTypeCollector.getInteger1Type();
      } else if (value >= 2 && value < 128) {
        return primTypeCollector.getInteger127Type();
      } else if (value >= -128 && value < 0) {
        return primTypeCollector.getByteType();
      } else if (value >= 128 && value < 32768) {
        return primTypeCollector.getInteger32767Type();
      } else if (value >= -32768 && value < -128) {
        return primTypeCollector.getShortType();
      } else if (value >= 32768 && value < 65536) {
        return primTypeCollector.getCharType();
      } else {
        return primTypeCollector.getIntType();
      }
    } else if (expr instanceof LongConstant) {
      return primTypeCollector.getLongType();
    } else if (expr instanceof NullConstant) {
      return primTypeCollector.getNullType();
    } else if (expr instanceof StringConstant) {
      return RefType.v("java.lang.String", myScene);
    } else if (expr instanceof ClassConstant) {
      return RefType.v("java.lang.Class", myScene);
    } else if (expr instanceof MethodHandle) {
      return RefType.v("java.lang.invoke.MethodHandle",myScene);
    } else if (expr instanceof MethodType) {
      return RefType.v("java.lang.invoke.MethodType",myScene);
    } else {
      throw new RuntimeException("Unhandled expression: " + expr);
    }
  }

  public Collection<Type> eval(Typing tg, Value expr, Stmt stmt, PrimTypeCollector primTypeCollector, Scene myScene) {
    return Collections.<Type>singletonList(eval_(tg, expr, stmt, this.jb, primTypeCollector, myScene));
  }
}
