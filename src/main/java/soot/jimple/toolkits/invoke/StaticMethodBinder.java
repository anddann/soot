package soot.jimple.toolkits.invoke;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1999 Patrick Lam, Raja Vallee-Rai
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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import com.google.inject.Inject;
import soot.Body;
import soot.Hierarchy;
import soot.Local;
import soot.Modifier;
import soot.PhaseOptions;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.TrapManager;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ConstantFactory;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.ParameterRef;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.Filter;
import soot.jimple.toolkits.callgraph.InstanceInvokeEdgesPred;
import soot.jimple.toolkits.callgraph.Targets;
import soot.jimple.toolkits.scalar.LocalNameStandardizer;
import soot.options.SMBOptions;
import soot.util.Chain;

/**
 * Uses the Scene's currently-active InvokeGraph to statically bind monomorphic call sites.
 */
public class StaticMethodBinder extends SceneTransformer {

  private Scene myScene;

  private SynchronizerManager mySynchronizerManager;
  private LocalNameStandardizer myLocalNameStandardizer;
  private ConstantFactory myConstantfactory;

  @Inject
  public StaticMethodBinder(Scene myScene,  SynchronizerManager mySynchronizerManager, LocalNameStandardizer myLocalNameStandardizer, ConstantFactory myConstantfactory) {
    this.myScene = myScene;
    ;
    this.mySynchronizerManager = mySynchronizerManager;
    this.myLocalNameStandardizer = myLocalNameStandardizer;
    this.myConstantfactory = myConstantfactory;
  }


  protected void internalTransform(String phaseName, Map opts) {
    Filter instanceInvokesFilter = new Filter(new InstanceInvokeEdgesPred());
    SMBOptions options = new SMBOptions(opts);
    String modifierOptions = PhaseOptions.getString(opts, "allowed-modifier-changes");
    HashMap instanceToStaticMap = new HashMap();

    CallGraph cg = myScene.getCallGraph();
    Hierarchy hierarchy = myScene.getActiveHierarchy();

    Iterator classesIt = myScene.getApplicationClasses().iterator();
    while (classesIt.hasNext()) {
      SootClass c = (SootClass) classesIt.next();

      LinkedList methodsList = new LinkedList();
      for (Iterator it = c.methodIterator(); it.hasNext();) {
        methodsList.add(it.next());
      }

      while (!methodsList.isEmpty()) {
        SootMethod container = (SootMethod) methodsList.removeFirst();

        if (!container.isConcrete()) {
          continue;
        }

        if (!instanceInvokesFilter.wrap(cg.edgesOutOf(container)).hasNext()) {
          continue;
        }

        JimpleBody b = (JimpleBody) container.getActiveBody();

        List<Unit> unitList = new ArrayList<Unit>();
        unitList.addAll(b.getUnits());
        Iterator<Unit> unitIt = unitList.iterator();

        while (unitIt.hasNext()) {
          Stmt s = (Stmt) unitIt.next();
          if (!s.containsInvokeExpr()) {
            continue;
          }

          InvokeExpr ie = s.getInvokeExpr();

          if (ie instanceof StaticInvokeExpr || ie instanceof SpecialInvokeExpr) {
            continue;
          }

          Iterator targets = new Targets(instanceInvokesFilter.wrap(cg.edgesOutOf(s)));
          if (!targets.hasNext()) {
            continue;
          }
          SootMethod target = (SootMethod) targets.next();
          if (targets.hasNext()) {
            continue;
          }

          // Ok, we have an Interface or VirtualInvoke going to 1.

          if (!AccessManager.ensureAccess(container, target, modifierOptions)) {
            continue;
          }

          if (!target.getDeclaringClass().isApplicationClass() || !target.isConcrete()) {
            continue;
          }

          // Don't modify java.lang.Object
          if (target.getDeclaringClass() == myScene.getSootClass("java.lang.Object")) {
            continue;
          }

          if (!instanceToStaticMap.containsKey(target)) {
            List newParameterTypes = new ArrayList();
            newParameterTypes.add(RefType.v(target.getDeclaringClass().getName(),myScene));

            newParameterTypes.addAll(target.getParameterTypes());

            // Check for signature conflicts.
            String newName = target.getName() + "_static";
            while (target.getDeclaringClass().declaresMethod(newName, newParameterTypes, target.getReturnType())) {
              newName = newName + "_static";
            }

            SootMethod ct = myScene.makeSootMethod(newName, newParameterTypes, target.getReturnType(),
                target.getModifiers() | Modifier.STATIC, target.getExceptions());
            target.getDeclaringClass().addMethod(ct);

            methodsList.addLast(ct);

            ct.setActiveBody((Body) target.getActiveBody().clone());

            // Make the invoke graph take into account the
            // newly-cloned body.
            {
              Iterator oldUnits = target.getActiveBody().getUnits().iterator();
              Iterator newUnits = ct.getActiveBody().getUnits().iterator();

              while (newUnits.hasNext()) {
                Stmt oldStmt, newStmt;
                oldStmt = (Stmt) oldUnits.next();
                newStmt = (Stmt) newUnits.next();

                Iterator edges = cg.edgesOutOf(oldStmt);
                while (edges.hasNext()) {
                  Edge e = (Edge) edges.next();
                  cg.addEdge(new Edge(ct, newStmt, e.tgt(), e.kind()));
                  cg.removeEdge(e);
                }
              }
            }

            // Shift the parameter list to apply to the new this
            // parameter.
            // If the method uses this, then we replace
            // the r0 := @this with r0 := @parameter0 & shift.
            // Otherwise, just zap the r0 := @this.
            {
              Body newBody = ct.getActiveBody();

              Chain units = newBody.getUnits();

              Iterator unitsIt = newBody.getUnits().snapshotIterator();
              while (unitsIt.hasNext()) {
                Stmt st = (Stmt) unitsIt.next();
                if (st instanceof IdentityStmt) {
                  IdentityStmt is = (IdentityStmt) st;
                  if (is.getRightOp() instanceof ThisRef) {
                    units.swapWith(st, Jimple.newIdentityStmt(is.getLeftOp(),
                        Jimple.newParameterRef(is.getRightOp().getType(), 0)));
                  } else {
                    if (is.getRightOp() instanceof ParameterRef) {
                      ParameterRef ro = (ParameterRef) is.getRightOp();
                      ro.setIndex(ro.getIndex() + 1);
                    }
                  }
                }
              }

            }

            instanceToStaticMap.put(target, ct);
          }

          SootMethod clonedTarget = (SootMethod) instanceToStaticMap.get(target);
          Value thisToAdd = ((InstanceInvokeExpr) ie).getBase();

          // Insert casts to please the verifier.
          if (options.insert_redundant_casts()) {
            // The verifier will complain if targetUsesThis, and:
            // the argument passed to the method is not the same
            // type.
            // For instance, Bottle.price_static takes a cost.
            // Cost is an interface implemented by Bottle.
            SootClass localType, parameterType;
            localType = ((RefType) ((InstanceInvokeExpr) ie).getBase().getType()).getSootClass();
            parameterType = target.getDeclaringClass();

            if (localType.isInterface() || hierarchy.isClassSuperclassOf(localType, parameterType)) {
              Local castee = Jimple.newLocal("__castee", parameterType.getType());
              b.getLocals().add(castee);
              b.getUnits().insertBefore(Jimple.newAssignStmt(castee,
                  Jimple.newCastExpr(((InstanceInvokeExpr) ie).getBase(), parameterType.getType())), s);
              thisToAdd = castee;
            }
          }

          // Now rebind the method call & fix the invoke graph.
          {
            List newArgs = new ArrayList();
            newArgs.add(thisToAdd);
            newArgs.addAll(ie.getArgs());

            StaticInvokeExpr sie = Jimple.newStaticInvokeExpr(clonedTarget.makeRef(), newArgs);

            ValueBox ieBox = s.getInvokeExprBox();
            ieBox.setValue(sie);

            cg.addEdge(new Edge(container, s, clonedTarget));
          }

          // (If enabled), add a null pointer check.
          if (options.insert_null_checks()) {
            boolean caught = TrapManager.isExceptionCaughtAt(myScene.getSootClass("java.lang.NullPointerException"), s, b);

            /* Ah ha. Caught again! */
            if (caught) {
              /*
               * In this case, we don't use throwPoint; instead, put the code right there.
               */
              Stmt insertee
                  = Jimple.newIfStmt(Jimple.newNeExpr(((InstanceInvokeExpr) ie).getBase(), myConstantfactory.getNullConstant()), s);

              b.getUnits().insertBefore(insertee, s);

              // This sucks (but less than before).
              ((IfStmt) insertee).setTarget(s);

              ThrowManager.addThrowAfter(b, insertee);
            } else {
              Stmt throwPoint = ThrowManager.getNullPointerExceptionThrower(b);
              b.getUnits().insertBefore(Jimple
                  .newIfStmt(Jimple.newEqExpr(((InstanceInvokeExpr) ie).getBase(), myConstantfactory.getNullConstant()), throwPoint), s);
            }
          }

          // Add synchronizing stuff.
          {
            if (target.isSynchronized()) {
              clonedTarget.setModifiers(clonedTarget.getModifiers() & ~Modifier.SYNCHRONIZED);
              mySynchronizerManager.synchronizeStmtOn(s, b, (Local) ((InstanceInvokeExpr) ie).getBase());
            }
          }

          // Resolve name collisions.
          myLocalNameStandardizer.transform(b, phaseName + ".lns");
        }
      }
    }
  }
}
