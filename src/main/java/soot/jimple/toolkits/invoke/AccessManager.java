package soot.jimple.toolkits.invoke;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1999 Patrick Lam
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
import java.util.Iterator;
import java.util.LinkedList;

import soot.*;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.*;
import soot.options.Options;

/** Methods for checking Java scope and visibiliity requirements. */
public class AccessManager {
  /**
   * Returns true iff target is legally accessible from container. Illegal access occurs when any of the following cases
   * holds: 1. target is private, but container.declaringClass() != target.declaringClass(); or, 2. target is
   * package-visible, and its package differs from that of container; or, 3. target is protected, and either: a. container
   * doesn't belong to target.declaringClass, or any subclass of ;
   */
  public static boolean isAccessLegal(SootMethod container, ClassMember target, Scene myScene) {
    SootClass targetClass = target.getDeclaringClass();
    SootClass containerClass = container.getDeclaringClass();

    if (!isAccessLegal(container, targetClass)) {
      return false;
    }

    // Condition 1 above.
    if (target.isPrivate() && !targetClass.getName().equals(containerClass.getName())) {
      return false;
    }

    // Condition 2. Check the package names.
    if (!target.isPrivate() && !target.isProtected() && !target.isPublic()) {
      if (!targetClass.getPackageName().equals(containerClass.getPackageName())) {
        return false;
      }
    }

    // Condition 3.
    if (target.isProtected()) {
      Hierarchy h = myScene.getActiveHierarchy();

      // protected means that you can be accessed by your children.
      // i.e. container must be in a child of target.
      if (h.isClassSuperclassOfIncluding(targetClass, containerClass)) {
        return true;
      }

      return false;
    }

    return true;
  }

  /**
   * Returns true if an access to <code>target</code> is legal from code in <code>container</code>.
   */
  public static boolean isAccessLegal(SootMethod container, SootClass target) {
    return target.isPublic() || container.getDeclaringClass().getPackageName().equals(target.getPackageName());
  }

  /**
   * Returns true if the statement <code>stmt</code> contains an illegal access to a field or method, assuming the statement
   * is in method <code>container</code>
   *
   * @param container
   * @param stmt
   * @param myScene
   * @return
   */
  public static boolean isAccessLegal(SootMethod container, Stmt stmt, Scene myScene) {
    if (stmt.containsInvokeExpr()) {
      return AccessManager.isAccessLegal(container, stmt.getInvokeExpr().getMethod(), myScene);
    } else if (stmt instanceof AssignStmt) {
      AssignStmt as = (AssignStmt) stmt;
      if (as.getRightOp() instanceof FieldRef) {
        FieldRef r = (FieldRef) as.getRightOp();
        return AccessManager.isAccessLegal(container, r.getField(), myScene);
      }
      if (as.getLeftOp() instanceof FieldRef) {
        FieldRef r = (FieldRef) as.getLeftOp();
        return AccessManager.isAccessLegal(container, r.getField(), myScene);
      }
    }
    return true;
  }

  /**
   * Resolves illegal accesses in the interval ]before,after[ by creating accessor methods. <code>before</code> and
   * <code>after</code> can be null to indicate beginning/end respectively.
   *
   * @param body
   * @param before
   * @param after
   * @param myScene
   * @param primTypeCollector
   * @param myPrinter
   * @param myOptions
   */
  public static void createAccessorMethods(Body body, Stmt before, Stmt after, Scene myScene, PrimTypeCollector primTypeCollector, Printer myPrinter, Options myOptions) {
    soot.util.Chain units = body.getUnits();

    if (before != null && !units.contains(before)) {
      throw new RuntimeException();
    }
    if (after != null && !units.contains(after)) {
      throw new RuntimeException();
    }

    ArrayList<Unit> unitList = new ArrayList<Unit>();
    unitList.addAll(units);

    boolean bInside = before == null;
    for (Unit unit : unitList) {
      Stmt s = (Stmt) unit;

      if (bInside) {
        if (s == after) {
          return;
        }

        if (!isAccessLegal(body.getMethod(), s, myScene)) {
          createAccessorMethod(body.getMethod(), s, primTypeCollector, myScene, myPrinter, myOptions);
        }

      } else {
        if (s == before) {
          bInside = true;
        }
      }
    }

  }

  /**
   * Creates a name for an accessor method.
   *
   * @param member
   * @param setter
   * @return
   */
  public static String createAccessorName(ClassMember member, boolean setter) {
    SootClass target = member.getDeclaringClass();

    String name = "access$";
    if (member instanceof SootField) {
      SootField f = (SootField) member;
      if (setter) {
        name += "set$";
      } else {
        name += "get$";
      }
      name += f.getName();
    } else {
      SootMethod m = (SootMethod) member;
      name += m.getName() + "$";

      for (Iterator it = m.getParameterTypes().iterator(); it.hasNext();) {
        Type type = (Type) it.next();
        name += type.toString().replaceAll("\\.", "\\$\\$") + "$";
      }
    }
    return name;
  }

  /**
   * Turns a field access or method call into a call to an accessor method. Reuses existing accessors based on name mangling
   * (see createAccessorName)
   *
   * @param container
   * @param stmt
   * @param primTypeCollector
   * @param myScene
   * @param myPrinter
   * @param myOptions
   */
  public static void createAccessorMethod(SootMethod container, Stmt stmt, PrimTypeCollector primTypeCollector, Scene myScene, Printer myPrinter, Options myOptions) {
    // System.out.println("Creating accessor method: \n" +
    // " method: " + container + " \n" +
    // " stmt: " + stmt);

    Body containerBody = container.getActiveBody();
    soot.util.Chain containerStmts = containerBody.getUnits();
    if (!containerStmts.contains(stmt)) {
      throw new RuntimeException();
    }

    if (stmt.containsInvokeExpr()) {
      createInvokeAccessor(container, stmt, primTypeCollector, myPrinter, myOptions, myScene);
    } else if (stmt instanceof AssignStmt) {
      AssignStmt as = (AssignStmt) stmt;
      FieldRef ref;
      if (as.getLeftOp() instanceof FieldRef) {
        // set
        ref = (FieldRef) as.getLeftOp();
        createSetAccessor(container, as, ref, primTypeCollector, myScene, myPrinter, myOptions);

      } else if (as.getRightOp() instanceof FieldRef) {
        // get
        ref = (FieldRef) as.getRightOp();
        createGetAccessor(container, as, ref, primTypeCollector, myPrinter, myOptions,myScene );
      } else {
        throw new RuntimeException("Expected class member access");
      }
    } else {
      throw new RuntimeException("Expected class member access");
    }
  }

  private static void createGetAccessor(SootMethod container, AssignStmt as, FieldRef ref, PrimTypeCollector primTypeCollector, Printer myPrinter, Options myOptions, Scene myScene) {
    java.util.List parameterTypes = new LinkedList();
    java.util.List<SootClass> thrownExceptions = new LinkedList<SootClass>();

    Body accessorBody = Jimple.newBody(myPrinter, myOptions);
    soot.util.Chain accStmts = accessorBody.getUnits();
    LocalGenerator lg = new LocalGenerator(accessorBody, primTypeCollector);

    Body containerBody = container.getActiveBody();
    soot.util.Chain containerStmts = containerBody.getUnits();

    SootClass target = ref.getField().getDeclaringClass();

    SootMethod accessor;

    String name = createAccessorName(ref.getField(), false);
    accessor = target.getMethodByNameUnsafe(name);
    if (accessor == null) {
      Type returnType = ref.getField().getType();
      Local thisLocal = lg.generateLocal(target.getType());
      if (ref instanceof InstanceFieldRef) {
        parameterTypes.add(target.getType());
        accStmts.addFirst(Jimple.newIdentityStmt(thisLocal, Jimple.newParameterRef(target.getType(), 0)));
      }
      Local l = lg.generateLocal(ref.getField().getType());
      Value v;
      if (ref instanceof InstanceFieldRef) {
        v = Jimple.newInstanceFieldRef(thisLocal, ref.getFieldRef());
      } else {
        v = Jimple.newStaticFieldRef(ref.getFieldRef());
      }
      accStmts.add(Jimple.newAssignStmt(l, v));
      accStmts.add(Jimple.newReturnStmt(l));

      accessor
          = myScene.makeSootMethod(name, parameterTypes, returnType, Modifier.PUBLIC | Modifier.STATIC, thrownExceptions);
      accessorBody.setMethod(accessor);
      accessor.setActiveBody(accessorBody);
      target.addMethod(accessor);
    }
    java.util.List args = new LinkedList();
    if (ref instanceof InstanceFieldRef) {
      args.add(((InstanceFieldRef) ref).getBase());
    }
    InvokeExpr newExpr = Jimple.newStaticInvokeExpr(accessor.makeRef(), args);

    as.setRightOp(newExpr);
  }

  private static void createSetAccessor(SootMethod container, AssignStmt as, FieldRef ref, PrimTypeCollector primTypeCollector, Scene myScene, Printer myPrinter, Options myOptions) {
    java.util.List parameterTypes = new LinkedList();
    java.util.List<SootClass> thrownExceptions = new LinkedList<SootClass>();

    Body accessorBody = Jimple.newBody(myPrinter, myOptions);
    soot.util.Chain accStmts = accessorBody.getUnits();
    LocalGenerator lg = new LocalGenerator(accessorBody, primTypeCollector);

    Body containerBody = container.getActiveBody();
    soot.util.Chain containerStmts = containerBody.getUnits();

    SootClass target = ref.getField().getDeclaringClass();
    SootMethod accessor;

    String name = createAccessorName(ref.getField(), true);
    accessor = target.getMethodByNameUnsafe(name);
    if (accessor == null) {
      Local thisLocal = lg.generateLocal(target.getType());
      int paramID = 0;
      if (ref instanceof InstanceFieldRef) {
        accStmts.add(Jimple.newIdentityStmt(thisLocal, Jimple.newParameterRef(target.getType(), paramID)));
        parameterTypes.add(target.getType());
        paramID++;
      }
      parameterTypes.add(ref.getField().getType());
      Local l = lg.generateLocal(ref.getField().getType());
      accStmts.add(Jimple.newIdentityStmt(l, Jimple.newParameterRef(ref.getField().getType(), paramID)));
      paramID++;
      if (ref instanceof InstanceFieldRef) {
        accStmts.add(Jimple.newAssignStmt(Jimple.newInstanceFieldRef(thisLocal, ref.getFieldRef()), l));
      } else {
        accStmts.add(Jimple.newAssignStmt(Jimple.newStaticFieldRef(ref.getFieldRef()), l));
      }
      accStmts.addLast(Jimple.newReturnVoidStmt());
      Type returnType = primTypeCollector.getVoidType();

      accessor
          = myScene.makeSootMethod(name, parameterTypes, returnType, Modifier.PUBLIC | Modifier.STATIC, thrownExceptions);
      accessorBody.setMethod(accessor);
      accessor.setActiveBody(accessorBody);
      target.addMethod(accessor);
    }

    java.util.List args = new LinkedList();
    if (ref instanceof InstanceFieldRef) {
      args.add(((InstanceFieldRef) ref).getBase());
    }
    args.add(as.getRightOp());
    InvokeExpr newExpr = Jimple.newStaticInvokeExpr(accessor.makeRef(), args);

    Stmt newStmt = Jimple.newInvokeStmt(newExpr);

    containerStmts.insertAfter(newStmt, as);
    containerStmts.remove(as);
  }

  private static void createInvokeAccessor(SootMethod container, Stmt stmt, PrimTypeCollector primTypeCollector, Printer myPrinter, Options myOptions, Scene myScene) {
    java.util.List parameterTypes = new LinkedList();
    java.util.List<SootClass> thrownExceptions = new LinkedList<SootClass>();
    Type returnType;

    Body accessorBody = Jimple.newBody(myPrinter, myOptions);
    soot.util.Chain accStmts = accessorBody.getUnits();
    LocalGenerator lg = new LocalGenerator(accessorBody, primTypeCollector);

    Body containerBody = container.getActiveBody();
    soot.util.Chain containerStmts = containerBody.getUnits();

    InvokeExpr expr = stmt.getInvokeExpr();
    SootMethod method = expr.getMethod();
    // System.out.println("method: " + method);

    SootClass target = method.getDeclaringClass();
    // System.out.println("target: " + target);

    // System.out.println("method ref: " + expr.getMethodRef());

    SootMethod accessor;

    String name = createAccessorName(method, true);
    accessor = target.getMethodByNameUnsafe(name);
    if (accessor == null) {
      java.util.List arguments = new LinkedList();

      if (expr instanceof InstanceInvokeExpr) {
        parameterTypes.add(target.getType());
      }

      parameterTypes.addAll(method.getParameterTypes());
      returnType = method.getReturnType();
      thrownExceptions.addAll(method.getExceptions());

      int paramID = 0;
      for (java.util.Iterator it = parameterTypes.iterator(); it.hasNext();) {
        Type type = (Type) it.next();
        Local l = lg.generateLocal(type);
        // System.out.println("local type: " + type);
        accStmts.add(Jimple.newIdentityStmt(l, Jimple.newParameterRef(type, paramID)));
        arguments.add(l);
        paramID++;
      }

      InvokeExpr accExpr;

      if (expr instanceof StaticInvokeExpr) {
        accExpr = Jimple.newStaticInvokeExpr(method.makeRef(), arguments);
      } else if (expr instanceof VirtualInvokeExpr) {
        Local thisLocal = (Local) arguments.get(0);
        arguments.remove(0);
        accExpr = Jimple.newVirtualInvokeExpr(thisLocal, method.makeRef(), arguments,myOptions);
      } else if (expr instanceof SpecialInvokeExpr) {
        Local thisLocal = (Local) arguments.get(0);
        arguments.remove(0);
        accExpr = Jimple.newSpecialInvokeExpr(thisLocal, method.makeRef(), arguments);
      } else {
        throw new RuntimeException("");
      }

      Stmt s;
      if (returnType instanceof VoidType) {
        s = Jimple.newInvokeStmt(accExpr);
        accStmts.add(s);
        accStmts.add(Jimple.newReturnVoidStmt());
      } else {
        Local resultLocal = lg.generateLocal(returnType);
        s = Jimple.newAssignStmt(resultLocal, accExpr);
        accStmts.add(s);
        accStmts.add(Jimple.newReturnStmt(resultLocal));
      }

      accessor
          = myScene.makeSootMethod(name, parameterTypes, returnType, Modifier.PUBLIC | Modifier.STATIC, thrownExceptions);
      accessorBody.setMethod(accessor);
      accessor.setActiveBody(accessorBody);
      target.addMethod(accessor);
    }

    java.util.List args = new LinkedList();
    if (expr instanceof InstanceInvokeExpr) {
      args.add(((InstanceInvokeExpr) expr).getBase());
    }
    args.addAll(expr.getArgs());
    InvokeExpr newExpr = Jimple.newStaticInvokeExpr(accessor.makeRef(), args);

    stmt.getInvokeExprBox().setValue(newExpr);
  }

  /**
   * Modifies code so that an access to <code>target</code> is legal from code in <code>container</code>.
   *
   * The "accessors" option assumes suitable accessor methods will be created after checking.
   *
   */
  public static boolean ensureAccess(SootMethod container, ClassMember target, String options, Scene myScene) {
    boolean accessors = options.equals("accessors");
    boolean allowChanges = !(options.equals("none"));
    boolean safeChangesOnly = !(options.equals("unsafe"));

    SootClass targetClass = target.getDeclaringClass();
    if (!ensureAccess(container, targetClass, options)) {
      return false;
    }

    if (isAccessLegal(container, target, myScene)) {
      return true;
    }

    if (!allowChanges && !accessors) {
      return false;
    }

    // throw new RuntimeException("Not implemented yet!");

    if (target.getDeclaringClass().isApplicationClass()) {
      if (accessors) {
        return true;
      }

      if (safeChangesOnly) {
        throw new RuntimeException("Not implemented yet!");
      }

      target.setModifiers(target.getModifiers() | Modifier.PUBLIC);
      return true;
    } else {
      return false;
    }
  }

  /**
   * Modifies code so that an access to <code>target</code> is legal from code in <code>container</code>.
   */
  public static boolean ensureAccess(SootMethod container, SootClass target, String options) {
    boolean accessors = options.equals("accessors");
    boolean allowChanges = !(options.equals("none"));
    boolean safeChangesOnly = !(options.equals("unsafe"));

    if (isAccessLegal(container, target)) {
      return true;
    }

    if (!allowChanges && !accessors) {
      return false;
    }

    if (safeChangesOnly && !accessors) {
      throw new RuntimeException("Not implemented yet!");
    }

    if (accessors) {
      return false;
    }

    if (target.isApplicationClass()) {

      target.setModifiers(target.getModifiers() | Modifier.PUBLIC);
      return true;
    } else {
      return false;
    }
  }

}
