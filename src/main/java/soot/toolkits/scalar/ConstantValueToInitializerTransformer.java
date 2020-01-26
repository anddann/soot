package soot.toolkits.scalar;

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

import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import soot.*;
import soot.jimple.*;
import soot.tagkit.DoubleConstantValueTag;
import soot.tagkit.FloatConstantValueTag;
import soot.tagkit.IntegerConstantValueTag;
import soot.tagkit.LongConstantValueTag;
import soot.tagkit.StringConstantValueTag;
import soot.tagkit.Tag;
import soot.util.Chain;

/**
 * Transformer that creates a static initializer which sets constant values into final static fields to emulate the
 * initializations that are done through the constant table in CLASS and DEX code, but that are not supported by Jimple.
 *
 * @author Steven Arzt
 */
public class ConstantValueToInitializerTransformer extends SceneTransformer {

  private Scene myScene;
  private ConstantFactory constantFactory;
  private PrimTypeCollector primTypeCollector;

  public ConstantValueToInitializerTransformer(Scene myScene, ConstantFactory constantFactory, PrimTypeCollector primTypeCollector) {
    this.myScene = myScene;
    this.constantFactory = constantFactory;
    this.primTypeCollector = primTypeCollector;
  }

  //FIXME: make singleton
  public static ConstantValueToInitializerTransformer v() {
    return new ConstantValueToInitializerTransformer(myScene, constantFactory, primTypeCollector);
  }

  @Override
  protected void internalTransform(String phaseName, Map<String, String> options) {
    for (SootClass sc : myScene.getClasses()) {
      transformClass(sc);
    }
  }

  public void transformClass(SootClass sc) {
    SootMethod smInit = null;
    Set<SootField> alreadyInitialized = new HashSet<SootField>();

    for (SootField sf : sc.getFields()) {
      // We can only create an initializer for all fields that have the
      // constant value tag. In case of non-static fields, this provides
      // a default value
      // If there is already an initializer for this field, we do not
      // generate a second one (this does not concern overwriting in
      // user code)
      if (alreadyInitialized.contains(sf)) {
        continue;
      }

      // Look for constant values
      for (Tag t : sf.getTags()) {
        Constant constant = null;
        if (t instanceof DoubleConstantValueTag) {
          double value = ((DoubleConstantValueTag) t).getDoubleValue();
          constant = constantFactory.createDoubleConstant(value);
        } else if (t instanceof FloatConstantValueTag) {
          float value = ((FloatConstantValueTag) t).getFloatValue();
          constant = constantFactory.createFloatConstant(value);
        } else if (t instanceof IntegerConstantValueTag) {
          int value = ((IntegerConstantValueTag) t).getIntValue();
          constant = constantFactory.createIntConstant(value);
        } else if (t instanceof LongConstantValueTag) {
          long value = ((LongConstantValueTag) t).getLongValue();
          constant = constantFactory.createLongConstant(value);
        } else if (t instanceof StringConstantValueTag) {
          String value = ((StringConstantValueTag) t).getStringValue();
          constant = constantFactory.createStringConstant(value);
        }

        if (constant != null) {
          if (sf.isStatic()) {
            Stmt initStmt = Jimple.newAssignStmt(Jimple.newStaticFieldRef(sf.makeRef()), constant);
            if (smInit == null) {
              smInit = getOrCreateInitializer(sc, alreadyInitialized);
            }
            if (smInit != null) {
              smInit.getActiveBody().getUnits().addFirst(initStmt);
            }
          } else {
            // We have a default value for a non-static field
            // So we have to get it into all <init>s, which
            // do not call other constructors of the same class.
            // It has to be after the constructor call to the super class
            // so that it can be potentially overwritten within the method,
            // without the default value taking precedence.
            for (SootMethod m : sc.getMethods()) {
              if (m.isConstructor()) {
                final Body body = m.retrieveActiveBody();
                for (Unit u : body.getUnits()) {
                  if (u instanceof Stmt) {
                    final Stmt s = (Stmt) u;
                    if (s.containsInvokeExpr()) {
                      final InvokeExpr expr = s.getInvokeExpr();
                      if (expr instanceof SpecialInvokeExpr) {
                        if (expr.getMethod().getDeclaringClass() == sc) {
                          // Calling another constructor in the same class
                          break;
                        }
                        Stmt initStmt = Jimple
                            .newAssignStmt(Jimple.newInstanceFieldRef(body.getThisLocal(), sf.makeRef()), constant);

                        body.getUnits().insertAfter(initStmt, s);
                        break;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    if (smInit != null) {
      Chain<Unit> units = smInit.getActiveBody().getUnits();
      if (units.isEmpty() || !(units.getLast() instanceof ReturnVoidStmt)) {
        units.add(Jimple.newReturnVoidStmt());
      }
    }
  }

  private SootMethod getOrCreateInitializer(SootClass sc, Set<SootField> alreadyInitialized) {
    SootMethod smInit;
    // Create a static initializer if we don't already have one
    smInit = sc.getMethodByNameUnsafe(SootMethod.staticInitializerName);
    if (smInit == null) {
      smInit = myScene.makeSootMethod(SootMethod.staticInitializerName, Collections.<Type>emptyList(), primTypeCollector.getVoidType());
      smInit.setActiveBody(Jimple.newBody(smInit));
      sc.addMethod(smInit);
      smInit.setModifiers(Modifier.PUBLIC | Modifier.STATIC);
    } else if (smInit.isPhantom()) {
      return null;
    } else {
      smInit.retrieveActiveBody();

      // We need to collect those variables that are already initialized
      // somewhere
      for (Unit u : smInit.getActiveBody().getUnits()) {
        Stmt s = (Stmt) u;
        for (ValueBox vb : s.getDefBoxes()) {
          if (vb.getValue() instanceof FieldRef) {
            alreadyInitialized.add(((FieldRef) vb.getValue()).getField());
          }
        }
      }
    }
    return smInit;
  }

}
