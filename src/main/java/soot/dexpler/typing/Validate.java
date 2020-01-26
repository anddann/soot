package soot.dexpler.typing;

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

import java.util.ArrayList;
import java.util.List;

import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethodRef;
import soot.SootResolver;
import soot.Type;
import soot.VoidType;

public class Validate {

  //FIXME:

//  public static void validateArrays(Body b, ThrowAnalysis myThrowAnalysis, Options myOptions, ThrowableSet.Manager myManager, PhaseDumper phaseDumper, InteractionHandler myInteractionHandlerr) {
//
//    Set<DefinitionStmt> definitions = new HashSet<DefinitionStmt>();
//    Set<Unit> unitWithArrayRef = new HashSet<Unit>();
//
//    for (Unit u : b.getUnits()) {
//      if (u instanceof DefinitionStmt) {
//        DefinitionStmt s = (DefinitionStmt) u;
//        definitions.add(s);
//      }
//      List<ValueBox> uses = u.getUseBoxes();
//      for (ValueBox vb : uses) {
//        Value v = vb.getValue();
//        if (v instanceof ArrayRef) {
//          unitWithArrayRef.add(u);
//        }
//      }
//    }
//
//    final LocalDefs localDefs = LocalDefs.Factory.newLocalDefs(b, true, myThrowAnalysis, myOptions, myManager, phaseDumper, myInteractionHandlerr);
//
//    Set<Unit> toReplace = new HashSet<Unit>();
//
//    for (Unit u : unitWithArrayRef) {
//      boolean ok = false;
//      List<ValueBox> uses = u.getUseBoxes();
//      for (ValueBox vb : uses) {
//        Value v = vb.getValue();
//        if (v instanceof ArrayRef) {
//          ArrayRef ar = (ArrayRef) v;
//          Local base = (Local) ar.getBase();
//          List<Unit> defs = localDefs.getDefsOfAt(base, u);
//
//          // add aliases
//          Set<Unit> alreadyHandled = new HashSet<Unit>();
//          while (true) {
//            boolean isMore = false;
//            for (Unit d : defs) {
//              if (alreadyHandled.contains(d)) {
//                continue;
//              }
//              if (d instanceof AssignStmt) {
//                AssignStmt ass = (AssignStmt) d;
//                Value r = ass.getRightOp();
//                if (r instanceof Local) {
//                  defs.addAll(localDefs.getDefsOfAt((Local) r, d));
//                  alreadyHandled.add(d);
//                  isMore = true;
//                  break;
//                } else if (r instanceof ArrayRef) {
//                  ArrayRef arrayRef = (ArrayRef) r;
//                  Local l = (Local) arrayRef.getBase();
//                  defs.addAll(localDefs.getDefsOfAt(l, d));
//                  alreadyHandled.add(d);
//                  isMore = true;
//                  break;
//                }
//              }
//            }
//            if (!isMore) {
//              break;
//            }
//          }
//
//          // System.out.println("def size "+ defs.size());
//          for (Unit def : defs) {
//            // System.out.println("def u "+ def);
//            Value r = null;
//            if (def instanceof IdentityStmt) {
//              IdentityStmt idstmt = (IdentityStmt) def;
//              r = idstmt.getRightOp();
//            } else if (def instanceof AssignStmt) {
//              AssignStmt assStmt = (AssignStmt) def;
//              r = assStmt.getRightOp();
//            } else {
//              throw new RuntimeException("error: definition statement not an IdentityStmt nor an AssignStmt! " + def);
//            }
//
//            Type t = null;
//            if (r instanceof InvokeExpr) {
//              InvokeExpr ie = (InvokeExpr) r;
//              t = ie.getType();
//              // System.out.println("ie type: "+ t +" "+ t.getClass());
//              if (t instanceof ArrayType) {
//                ok = true;
//              }
//            } else if (r instanceof FieldRef) {
//              FieldRef ref = (FieldRef) r;
//              t = ref.getType();
//              // System.out.println("fr type: "+ t +" "+ t.getClass());
//              if (t instanceof ArrayType) {
//                ok = true;
//              }
//            } else if (r instanceof IdentityRef) {
//              IdentityRef ir = (IdentityRef) r;
//              t = ir.getType();
//              if (t instanceof ArrayType) {
//                ok = true;
//              }
//            } else if (r instanceof CastExpr) {
//              CastExpr c = (CastExpr) r;
//              t = c.getType();
//              if (t instanceof ArrayType) {
//                ok = true;
//              }
//            } else if (r instanceof ArrayRef) {
//              // we also check that this arrayref is correctly defined
//            } else if (r instanceof NewArrayExpr) {
//              ok = true;
//            } else if (r instanceof Local) {
//
//            } else if (r instanceof Constant) {
//
//            } else {
//              throw new RuntimeException("error: unknown right hand side of definition stmt " + def);
//            }
//
//            if (ok) {
//              break;
//            }
//
//          }
//
//          if (ok) {
//            break;
//          }
//        }
//      }
//
//      if (!ok) {
//        toReplace.add(u);
//      }
//    }
//
//    int i = 0;
//    for (Unit u : toReplace) {
//      System.out.println("warning: incorrect array def, replacing unit " + u);
//      // new object
//      RefType throwableType = RefType.v("java.lang.Throwable",myScene);
//      Local ttt = Jimple.newLocal("ttt_" + ++i, throwableType);
//      b.getLocals().add(ttt);
//      Value r = Jimple.newNewExpr(throwableType);
//      Unit initLocalUnit = Jimple.newAssignStmt(ttt, r);
//
//      // call <init> method with a string parameter for message
//      List<String> pTypes = new ArrayList<String>();
//      pTypes.add("java.lang.String");
//      boolean isStatic = false;
//      SootMethodRef mRef = Validate.makeMethodRef("java.lang.Throwable", "<init>", "", pTypes, isStatic);
//      List<Value> parameters = new ArrayList<Value>();
//      parameters.add(constantFactory.createStringConstant("Soot updated this instruction"));
//      InvokeExpr ie = Jimple.newSpecialInvokeExpr(ttt, mRef, parameters);
//      Unit initMethod = Jimple.newInvokeStmt(ie);
//
//      // throw exception
//      Unit newUnit = Jimple.newThrowStmt(ttt);
//
//      // change instruction in body
//      b.getUnits().swapWith(u, newUnit);
//      b.getUnits().insertBefore(initMethod, newUnit);
//      b.getUnits().insertBefore(initLocalUnit, initMethod);
//      // Exception a = throw new Exception();
//    }
//
//    myDeadAssignmentEliminator.transform(b);
//    myUnusedLocalEliminator.transform(b);
//    myNopEliminator.transform(b);
//    myUnreachableCodeEliminator.transform(b);
//
//  }

  public static SootMethodRef makeMethodRef(String cName, String mName, String rType, List<String> pTypes,
                                            boolean isStatic, SootResolver mySootResolver, Scene myScene) {
    SootClass sc = mySootResolver.makeClassRef(cName);
    Type returnType = null;
    if (rType == "") {
      returnType = myScene.getPrimTypeCollector().getVoidType();
    } else {
      returnType = RefType.v(rType,myScene);
    }
    List<Type> parameterTypes = new ArrayList<Type>();
    for (String p : pTypes) {
      parameterTypes.add(RefType.v(p,myScene));
    }
    return myScene.makeMethodRef(sc, mName, parameterTypes, returnType, isStatic);
  }
}
