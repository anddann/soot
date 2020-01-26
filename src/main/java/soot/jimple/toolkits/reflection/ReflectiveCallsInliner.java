package soot.jimple.toolkits.reflection;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2010 Eric Bodden
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

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.ArrayType;
import soot.Body;
import soot.Local;
import soot.Modifier;
import soot.PatchingChain;
import soot.PrimType;
import soot.RefLikeType;
import soot.RefType;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.*;
import soot.jimple.toolkits.reflection.ReflectionTraceInfo.Kind;
import soot.options.CGOptions;
import soot.rtlib.tamiflex.DefaultHandler;
import soot.rtlib.tamiflex.IUnexpectedReflectiveCallHandler;
import soot.rtlib.tamiflex.OpaquePredicate;
import soot.rtlib.tamiflex.ReflectiveCalls;
import soot.rtlib.tamiflex.SootSig;
import soot.rtlib.tamiflex.UnexpectedReflectiveCall;
import soot.util.Chain;
import soot.util.HashChain;

public class ReflectiveCallsInliner extends SceneTransformer {
  // caching currently does not work because it adds fields to Class, Method
  // and Constructor,
  // but such fields cannot currently be added using the Instrumentation API
  private final boolean useCaching = false;

  private static final String ALREADY_CHECKED_FIELDNAME = "SOOT$Reflection$alreadyChecked";
  private ReflectionTraceInfo RTI;
  private SootMethodRef UNINTERPRETED_METHOD;

  private boolean initialized = false;

  private int callSiteId;

  private int callNum;

  private SootClass reflectiveCallsClass;

  private static final List<String> fieldSets
      = Arrays.asList("set", "setBoolean", "setByte", "setChar", "setInt", "setLong", "setFloat", "setDouble", "setShort");

  private static final List<String> fieldGets
      = Arrays.asList("get", "getBoolean", "getByte", "getChar", "getInt", "getLong", "getFloat", "getDouble", "getShort");

  @Override
  protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
    if (!initialized) {
      CGOptions cgOptions = new CGOptions(myPhaseOptions().getPhaseOptions("cg"));
      String logFilePath = cgOptions.reflection_log();
      RTI = new ReflectionTraceInfo(logFilePath, myScene);

      myScene.getSootClass(SootSig.class.getName()).setApplicationClass();
      myScene.getSootClass(UnexpectedReflectiveCall.class.getName()).setApplicationClass();
      myScene.getSootClass(IUnexpectedReflectiveCallHandler.class.getName()).setApplicationClass();
      myScene.getSootClass(DefaultHandler.class.getName()).setApplicationClass();
      myScene.getSootClass(OpaquePredicate.class.getName()).setApplicationClass();
      myScene.getSootClass(ReflectiveCalls.class.getName()).setApplicationClass();

      reflectiveCallsClass = new SootClass("soot.rtlib.tamiflex.ReflectiveCallsWrapper", myOptions, Modifier.PUBLIC, myScene, myPackageNamer);
      myScene.addClass(reflectiveCallsClass);
      reflectiveCallsClass.setApplicationClass();

      UNINTERPRETED_METHOD = myScene.makeMethodRef(myScene.getSootClass("soot.rtlib.tamiflex.OpaquePredicate"),
          "getFalse", Collections.<Type>emptyList(), primTypeCollector.getBooleanType(), true);

      if (useCaching) {
        addCaching();
      }

      initializeReflectiveCallsTable();

      callSiteId = 0;
      callNum = 0;

      initialized = true;
    }

    for (SootMethod m : RTI.methodsContainingReflectiveCalls()) {
      m.retrieveActiveBody();
      Body b = m.getActiveBody();
      {
        Set<String> classForNameClassNames = RTI.classForNameClassNames(m);
        if (!classForNameClassNames.isEmpty()) {
          inlineRelectiveCalls(m, classForNameClassNames, ReflectionTraceInfo.Kind.ClassForName);
          if (myOptions.validate()) {
            b.validate();
          }
        }
      }
      {
        Set<String> classNewInstanceClassNames = RTI.classNewInstanceClassNames(m);
        if (!classNewInstanceClassNames.isEmpty()) {
          inlineRelectiveCalls(m, classNewInstanceClassNames, ReflectionTraceInfo.Kind.ClassNewInstance);
          if (myOptions.validate()) {
            b.validate();
          }
        }
      }
      {
        Set<String> constructorNewInstanceSignatures = RTI.constructorNewInstanceSignatures(m);
        if (!constructorNewInstanceSignatures.isEmpty()) {
          inlineRelectiveCalls(m, constructorNewInstanceSignatures, ReflectionTraceInfo.Kind.ConstructorNewInstance);
          if (myOptions.validate()) {
            b.validate();
          }
        }
      }
      {
        Set<String> methodInvokeSignatures = RTI.methodInvokeSignatures(m);
        if (!methodInvokeSignatures.isEmpty()) {
          inlineRelectiveCalls(m, methodInvokeSignatures, ReflectionTraceInfo.Kind.MethodInvoke);
          if (myOptions.validate()) {
            b.validate();
          }
        }
      }
      {
        Set<String> fieldSetSignatures = RTI.fieldSetSignatures(m);
        if (!fieldSetSignatures.isEmpty()) {
          inlineRelectiveCalls(m, fieldSetSignatures, ReflectionTraceInfo.Kind.FieldSet);
          if (myOptions.validate()) {
            b.validate();
          }
        }
      }
      {
        Set<String> fieldGetSignatures = RTI.fieldGetSignatures(m);
        if (!fieldGetSignatures.isEmpty()) {
          inlineRelectiveCalls(m, fieldGetSignatures, ReflectionTraceInfo.Kind.FieldGet);
          if (myOptions.validate()) {
            b.validate();
          }
        }
      }
      // clean up after us
      cleanup(b);
    }
  }

  private void cleanup(Body b) {
    myCopyPropagator.transform(b);
    myDeadAssignmentEliminator.transform(b);
    myUnusedLocalEliminator.transform(b);
    myNopEliminator.transform(b);
  }

  private void initializeReflectiveCallsTable() {
    int callSiteId = 0;

    SootClass reflCallsClass = myScene.getSootClass("soot.rtlib.tamiflex.ReflectiveCalls");
    SootMethod clinit = reflCallsClass.getMethodByName(SootMethod.staticInitializerName);
    Body body = clinit.retrieveActiveBody();
    PatchingChain<Unit> units = body.getUnits();
    LocalGenerator localGen = new LocalGenerator(body, primTypeCollector);
    Chain<Unit> newUnits = new HashChain<Unit>();
    SootClass setClass = myScene.getSootClass("java.util.Set");
    SootMethodRef addMethodRef = setClass.getMethodByName("add").makeRef();
    for (SootMethod m : RTI.methodsContainingReflectiveCalls()) {
      {
        if (!RTI.classForNameClassNames(m).isEmpty()) {
          SootFieldRef fieldRef = myScene.makeFieldRef(reflCallsClass, "classForName", RefType.v("java.util.Set"), true);
          Local setLocal = localGen.generateLocal(RefType.v("java.util.Set"));
          newUnits.add(Jimple.newAssignStmt(setLocal, Jimple.newStaticFieldRef(fieldRef)));
          for (String className : RTI.classForNameClassNames(m)) {
            InterfaceInvokeExpr invokeExpr
                = Jimple.newInterfaceInvokeExpr(setLocal, addMethodRef, constantFactory.createStringConstant(callSiteId + className));
            newUnits.add(Jimple.newInvokeStmt(invokeExpr));
          }
          callSiteId++;
        }
      }
      {
        if (!RTI.classNewInstanceClassNames(m).isEmpty()) {
          SootFieldRef fieldRef
              = myScene.makeFieldRef(reflCallsClass, "classNewInstance", RefType.v("java.util.Set"), true);
          Local setLocal = localGen.generateLocal(RefType.v("java.util.Set"));
          newUnits.add(Jimple.newAssignStmt(setLocal, Jimple.newStaticFieldRef(fieldRef)));
          for (String className : RTI.classNewInstanceClassNames(m)) {
            InterfaceInvokeExpr invokeExpr
                = Jimple.newInterfaceInvokeExpr(setLocal, addMethodRef, constantFactory.createStringConstant(callSiteId + className));
            newUnits.add(Jimple.newInvokeStmt(invokeExpr));
          }
          callSiteId++;
        }
      }
      {
        if (!RTI.constructorNewInstanceSignatures(m).isEmpty()) {
          SootFieldRef fieldRef
              = myScene.makeFieldRef(reflCallsClass, "constructorNewInstance", RefType.v("java.util.Set"), true);
          Local setLocal = localGen.generateLocal(RefType.v("java.util.Set"));
          newUnits.add(Jimple.newAssignStmt(setLocal, Jimple.newStaticFieldRef(fieldRef)));
          for (String constrSig : RTI.constructorNewInstanceSignatures(m)) {
            InterfaceInvokeExpr invokeExpr
                = Jimple.newInterfaceInvokeExpr(setLocal, addMethodRef, constantFactory.createStringConstant(callSiteId + constrSig));
            newUnits.add(Jimple.newInvokeStmt(invokeExpr));
          }
          callSiteId++;
        }
      }
      {
        if (!RTI.methodInvokeSignatures(m).isEmpty()) {
          SootFieldRef fieldRef = myScene.makeFieldRef(reflCallsClass, "methodInvoke", RefType.v("java.util.Set"), true);
          Local setLocal = localGen.generateLocal(RefType.v("java.util.Set"));
          newUnits.add(Jimple.newAssignStmt(setLocal, Jimple.newStaticFieldRef(fieldRef)));
          for (String methodSig : RTI.methodInvokeSignatures(m)) {
            InterfaceInvokeExpr invokeExpr
                = Jimple.newInterfaceInvokeExpr(setLocal, addMethodRef, constantFactory.createStringConstant(callSiteId + methodSig));
            newUnits.add(Jimple.newInvokeStmt(invokeExpr));
          }
          callSiteId++;
        }
      }
    }

    Unit secondLastStmt = units.getPredOf(units.getLast());
    units.insertAfter(newUnits, secondLastStmt);

    if (myOptions.validate()) {
      body.validate();
    }
  }

  private void addCaching() {
    SootClass method = myScene.getSootClass("java.lang.reflect.Method");
    method.addField(myScene.makeSootField(ALREADY_CHECKED_FIELDNAME, primTypeCollector.getBooleanType()));
    SootClass constructor = myScene.getSootClass("java.lang.reflect.Constructor");
    constructor.addField(myScene.makeSootField(ALREADY_CHECKED_FIELDNAME, primTypeCollector.getBooleanType()));
    SootClass clazz = myScene.getSootClass("java.lang.Class");
    clazz.addField(myScene.makeSootField(ALREADY_CHECKED_FIELDNAME, primTypeCollector.getBooleanType()));

    for (Kind k : Kind.values()) {
      addCaching(k);
    }
  }

  private void addCaching(Kind kind) {

    SootClass c;
    String methodName;
    switch (kind) {
      case ClassNewInstance:
        c = myScene.getSootClass("java.lang.Class");
        methodName = "knownClassNewInstance";
        break;
      case ConstructorNewInstance:
        c = myScene.getSootClass("java.lang.reflect.Constructor");
        methodName = "knownConstructorNewInstance";
        break;
      case MethodInvoke:
        c = myScene.getSootClass("java.lang.reflect.Method");
        methodName = "knownMethodInvoke";
        break;
      case ClassForName:
        // Cannot implement caching in this case because we can add no field
        // to the String argument
        return;
      default:
        throw new IllegalStateException("unknown kind: " + kind);
    }

    SootClass reflCallsClass = myScene.getSootClass("soot.rtlib.tamiflex.ReflectiveCalls");

    SootMethod m = reflCallsClass.getMethodByName(methodName);
    JimpleBody body = (JimpleBody) m.retrieveActiveBody();
    LocalGenerator localGen = new LocalGenerator(body, primTypeCollector);
    Unit firstStmt = body.getFirstNonIdentityStmt();
    firstStmt = body.getUnits().getPredOf(firstStmt);

    Stmt jumpTarget = Jimple.newNopStmt();

    Chain<Unit> newUnits = new HashChain<Unit>();

    // alreadyCheckedLocal = m.alreadyChecked
    InstanceFieldRef fieldRef = Jimple.newInstanceFieldRef(body.getParameterLocal(m.getParameterCount() - 1),
        myScene.makeFieldRef(c, ALREADY_CHECKED_FIELDNAME, primTypeCollector.getBooleanType(), false));
    Local alreadyCheckedLocal = localGen.generateLocal(primTypeCollector.getBooleanType());
    newUnits.add(Jimple.newAssignStmt(alreadyCheckedLocal, fieldRef));

    // if(!alreadyChecked) goto jumpTarget
    newUnits.add(Jimple.newIfStmt(Jimple.newEqExpr(alreadyCheckedLocal, constantFactory.createIntConstant(0)), jumpTarget));

    // return
    newUnits.add(Jimple.newReturnVoidStmt());

    // jumpTarget: nop
    newUnits.add(jumpTarget);

    // m.alreadyChecked = true
    InstanceFieldRef fieldRef2 = Jimple.newInstanceFieldRef(body.getParameterLocal(m.getParameterCount() - 1),
        myScene.makeFieldRef(c, ALREADY_CHECKED_FIELDNAME, primTypeCollector.getBooleanType(), false));
    newUnits.add(Jimple.newAssignStmt(fieldRef2, constantFactory.createIntConstant(1)));

    body.getUnits().insertAfter(newUnits, firstStmt);

    if (myOptions.validate()) {
      body.validate();
    }
  }

  private void inlineRelectiveCalls(SootMethod m, Set<String> targets, Kind callKind) {
    if (!m.hasActiveBody()) {
      m.retrieveActiveBody();
    }
    Body b = m.getActiveBody();
    PatchingChain<Unit> units = b.getUnits();
    Iterator<Unit> iter = units.snapshotIterator();
    LocalGenerator localGen = new LocalGenerator(b, primTypeCollector);

    // for all units
    while (iter.hasNext()) {
      Chain<Unit> newUnits = new HashChain<Unit>();
      Stmt s = (Stmt) iter.next();

      // if we have an invoke expression, test to see if it is a
      // reflective invoke expression
      if (s.containsInvokeExpr()) {
        InvokeExpr ie = s.getInvokeExpr();
        boolean found = false;
        Type fieldSetGetType = null;

        if (callKind == Kind.ClassForName
            && (ie.getMethodRef().getSignature().equals("<java.lang.Class: java.lang.Class forName(java.lang.String)>")
                || ie.getMethodRef().getSignature()
                    .equals("<java.lang.Class: java.lang.Class forName(java.lang.String,boolean,java.lang.ClassLoader)>"))) {
          found = true;
          Value classNameValue = ie.getArg(0);
          newUnits.add(Jimple
              .newInvokeStmt(Jimple
                  .newStaticInvokeExpr(myScene
                      .getMethod("<soot.rtlib.tamiflex.ReflectiveCalls: void knownClassForName(int,java.lang.String)>")
                      .makeRef(), constantFactory.createIntConstant(callSiteId), classNameValue)));
        } else if (callKind == Kind.ClassNewInstance
            && ie.getMethodRef().getSignature().equals("<java.lang.Class: java.lang.Object newInstance()>")) {
          found = true;
          Local classLocal = (Local) ((InstanceInvokeExpr) ie).getBase();
          newUnits.add(Jimple
              .newInvokeStmt(Jimple
                  .newStaticInvokeExpr(myScene
                      .getMethod("<soot.rtlib.tamiflex.ReflectiveCalls: void knownClassNewInstance(int,java.lang.Class)>")
                      .makeRef(), constantFactory.createIntConstant(callSiteId), classLocal)));
        } else if (callKind == Kind.ConstructorNewInstance && ie.getMethodRef().getSignature()
            .equals("<java.lang.reflect.Constructor: java.lang.Object newInstance(java.lang.Object[])>")) {
          found = true;
          Local constrLocal = (Local) ((InstanceInvokeExpr) ie).getBase();
          newUnits.add(Jimple.newInvokeStmt(Jimple.newStaticInvokeExpr(myScene.getMethod(
              "<soot.rtlib.tamiflex.ReflectiveCalls: void knownConstructorNewInstance(int,java.lang.reflect.Constructor)>")
              .makeRef(), constantFactory.createIntConstant(callSiteId), constrLocal)));
        } else if (callKind == Kind.MethodInvoke && ie.getMethodRef().getSignature()
            .equals("<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>")) {
          found = true;
          Local methodLocal = (Local) ((InstanceInvokeExpr) ie).getBase();
          Value recv = ie.getArg(0);
          newUnits.add(Jimple.newInvokeStmt(Jimple.newStaticInvokeExpr(myScene.getMethod(
              "<soot.rtlib.tamiflex.ReflectiveCalls: void knownMethodInvoke(int,java.lang.Object,java.lang.reflect.Method)>")
              .makeRef(), constantFactory.createIntConstant(callSiteId), recv, methodLocal)));
        } else if (callKind == Kind.FieldSet) {
          SootMethod sootMethod = ie.getMethodRef().resolve();
          if (sootMethod.getDeclaringClass().getName().equals("java.lang.reflect.Field")
              && fieldSets.contains(sootMethod.getName())) {
            found = true;
            fieldSetGetType = sootMethod.getParameterType(1); // assign
            // type
            // of
            // 2nd
            // parameter
            // (1st
            // is
            // receiver
            // object)
            Value recv = ie.getArg(0);
            Value field = ((InstanceInvokeExpr) ie).getBase();
            newUnits.add(Jimple.newInvokeStmt(Jimple.newStaticInvokeExpr(myScene.getMethod(
                "<soot.rtlib.tamiflex.ReflectiveCalls: void knownFieldSet(int,java.lang.Object,java.lang.reflect.Field)>")
                .makeRef(), constantFactory.createIntConstant(callSiteId), recv, field)));
          }
        } else if (callKind == Kind.FieldGet) {
          SootMethod sootMethod = ie.getMethodRef().resolve();
          if (sootMethod.getDeclaringClass().getName().equals("java.lang.reflect.Field")
              && fieldGets.contains(sootMethod.getName())) {
            found = true;
            fieldSetGetType = sootMethod.getReturnType(); // assign
            // return
            // type
            // of
            // get
            Value recv = ie.getArg(0);
            Value field = ((InstanceInvokeExpr) ie).getBase();
            newUnits.add(Jimple.newInvokeStmt(Jimple.newStaticInvokeExpr(myScene.getMethod(
                "<soot.rtlib.tamiflex.ReflectiveCalls: void knownFieldSet(int,java.lang.Object,java.lang.reflect.Field)>")
                .makeRef(), constantFactory.createIntConstant(callSiteId), recv, field)));
          }
        }

        if (!found) {
          continue;
        }

        NopStmt endLabel = Jimple.newNopStmt();

        // for all recorded targets
        for (String target : targets) {

          NopStmt jumpTarget = Jimple.newNopStmt();

          // boolean predLocal = Opaque.getFalse();
          Local predLocal = localGen.generateLocal(primTypeCollector.getBooleanType());
          StaticInvokeExpr staticInvokeExpr = Jimple.newStaticInvokeExpr(UNINTERPRETED_METHOD);
          newUnits.add(Jimple.newAssignStmt(predLocal, staticInvokeExpr));
          // if predLocal == 0 goto <original reflective call>
          newUnits.add(Jimple.newIfStmt(Jimple.newEqExpr(constantFactory.createIntConstant(0), predLocal), jumpTarget));

          SootMethod newMethod = createNewMethod(callKind, target, fieldSetGetType);

          List<Value> args = new LinkedList<Value>();
          switch (callKind) {
            case ClassForName:
            case ClassNewInstance:
              // no arguments
              break;
            case ConstructorNewInstance:
              // add Object[] argument
              args.add((Value) ie.getArgs().get(0));
              break;
            case MethodInvoke:
              // add Object argument
              args.add((Value) ie.getArgs().get(0));
              // add Object[] argument
              args.add((Value) ie.getArgs().get(1));
              break;
            case FieldSet:
              // add Object argument
              args.add((Value) ie.getArgs().get(0));
              // add value argument
              args.add((Value) ie.getArgs().get(1));
              break;
            case FieldGet:
              // add Object argument
              args.add((Value) ie.getArgs().get(0));
              break;
            default:
              throw new IllegalStateException();
          }

          StaticInvokeExpr methodInvokeExpr = Jimple.newStaticInvokeExpr(newMethod.makeRef(), args);
          Local retLocal = localGen.generateLocal(newMethod.getReturnType());
          newUnits.add(Jimple.newAssignStmt(retLocal, methodInvokeExpr));

          if (s instanceof AssignStmt) {
            AssignStmt assignStmt = (AssignStmt) s;
            Value leftOp = assignStmt.getLeftOp();
            AssignStmt newAssignStmt = Jimple.newAssignStmt(leftOp, retLocal);
            newUnits.add(newAssignStmt);
          }

          GotoStmt gotoStmt = Jimple.newGotoStmt(endLabel);
          newUnits.add(gotoStmt);

          newUnits.add(jumpTarget);
        }

        Unit end = newUnits.getLast();
        units.insertAfter(newUnits, s);
        units.remove(s);
        units.insertAfter(s, end);
        units.insertAfter(endLabel, s);

      }
    }
    callSiteId++;
  }

  @SuppressWarnings("unchecked")
  private SootMethod createNewMethod(Kind callKind, String target, Type fieldSetGetType) {
    List<Type> parameterTypes = new LinkedList<Type>();
    Type returnType = null;
    switch (callKind) {
      case ClassForName:
        returnType = RefType.v("java.lang.Class",myScene);
        break;
      case ClassNewInstance:
        returnType = RefType.v("java.lang.Object",myScene);
        break;
      case ConstructorNewInstance:
        parameterTypes.add(ArrayType.v(RefType.v("java.lang.Object",myScene), 1));
        returnType = RefType.v("java.lang.Object",myScene);
        break;
      case MethodInvoke:
        parameterTypes.add(RefType.v("java.lang.Object",myScene));
        parameterTypes.add(ArrayType.v(RefType.v("java.lang.Object",myScene), 1));
        returnType = RefType.v("java.lang.Object",myScene);
        break;
      case FieldSet:
        parameterTypes.add(RefType.v("java.lang.Object",myScene));
        parameterTypes.add(fieldSetGetType);
        returnType = primTypeCollector.getVoidType();
        break;
      case FieldGet:
        parameterTypes.add(RefType.v("java.lang.Object",myScene));
        returnType = fieldSetGetType;
        break;
      default:
        throw new IllegalStateException();
    }

    SootMethod newMethod = myScene.makeSootMethod("reflectiveCall" + (callNum++), parameterTypes, returnType,
        Modifier.PUBLIC | Modifier.STATIC);
    Body newBody = Jimple.newBody(newMethod);
    newMethod.setActiveBody(newBody);
    reflectiveCallsClass.addMethod(newMethod);

    PatchingChain<Unit> newUnits = newBody.getUnits();

    LocalGenerator localGen = new LocalGenerator(newBody, primTypeCollector);

    Local freshLocal;
    Value replacement = null;
    Local[] paramLocals = null;
    switch (callKind) {
      case ClassForName: {
        // replace by: <Class constant for <target>>
        freshLocal = localGen.generateLocal(RefType.v("java.lang.Class",myScene));
        replacement = constantFactory.createClassConstant(target.replace('.', '/'));
        break;
      }
      case ClassNewInstance: {
        // replace by: new <target>
        RefType targetType = RefType.v(target);
        freshLocal = localGen.generateLocal(targetType);
        replacement = Jimple.newNewExpr(targetType);
        break;
      }
      case ConstructorNewInstance: {
        /*
         * replace r=constr.newInstance(args) by: Object p0 = args[0]; ... Object pn = args[n]; T0 a0 = (T0)p0; ... Tn an =
         * (Tn)pn;
         */

        SootMethod constructor = myScene.getMethod(target);
        paramLocals = new Local[constructor.getParameterCount()];
        if (constructor.getParameterCount() > 0) {
          // argArrayLocal = @parameter-0
          ArrayType arrayType = ArrayType.v(RefType.v("java.lang.Object",myScene), 1);
          Local argArrayLocal = localGen.generateLocal(arrayType);
          newUnits.add(Jimple.newIdentityStmt(argArrayLocal, Jimple.newParameterRef(arrayType, 0)));
          int i = 0;
          for (Type paramType : ((Collection<Type>) constructor.getParameterTypes())) {
            paramLocals[i] = localGen.generateLocal(paramType);
            unboxParameter(argArrayLocal, i, paramLocals, paramType, newUnits, localGen);
            i++;
          }
        }
        RefType targetType = constructor.getDeclaringClass().getType();
        freshLocal = localGen.generateLocal(targetType);
        replacement = Jimple.newNewExpr(targetType);

        break;
      }
      case MethodInvoke: {
        /*
         * replace r=m.invoke(obj,args) by: T recv = (T)obj; Object p0 = args[0]; ... Object pn = args[n]; T0 a0 = (T0)p0;
         * ... Tn an = (Tn)pn;
         */
        SootMethod method = myScene.getMethod(target);
        // recvObject = @parameter-0
        RefType objectType = RefType.v("java.lang.Object",myScene);
        Local recvObject = localGen.generateLocal(objectType);
        newUnits.add(Jimple.newIdentityStmt(recvObject, Jimple.newParameterRef(objectType, 0)));
        paramLocals = new Local[method.getParameterCount()];
        if (method.getParameterCount() > 0) {
          // argArrayLocal = @parameter-1
          ArrayType arrayType = ArrayType.v(RefType.v("java.lang.Object",myScene), 1);
          Local argArrayLocal = localGen.generateLocal(arrayType);
          newUnits.add(Jimple.newIdentityStmt(argArrayLocal, Jimple.newParameterRef(arrayType, 1)));
          int i = 0;
          for (Type paramType : ((Collection<Type>) method.getParameterTypes())) {
            paramLocals[i] = localGen.generateLocal(paramType);
            unboxParameter(argArrayLocal, i, paramLocals, paramType, newUnits, localGen);
            i++;
          }
        }
        RefType targetType = method.getDeclaringClass().getType();
        freshLocal = localGen.generateLocal(targetType);
        replacement = Jimple.newCastExpr(recvObject, method.getDeclaringClass().getType());

        break;
      }
      case FieldSet:
      case FieldGet: {
        /*
         * replace f.set(o,v) by: Object obj = @parameter-0; T freshLocal = (T)obj;
         */
        RefType objectType = RefType.v("java.lang.Object",myScene);
        Local recvObject = localGen.generateLocal(objectType);
        newUnits.add(Jimple.newIdentityStmt(recvObject, Jimple.newParameterRef(objectType, 0)));

        SootField field = myScene.getField(target);
        freshLocal = localGen.generateLocal(field.getDeclaringClass().getType());
        replacement = Jimple.newCastExpr(recvObject, field.getDeclaringClass().getType());

        break;
      }
      default:
        throw new InternalError("Unknown kind of reflective call " + callKind);
    }

    AssignStmt replStmt = Jimple.newAssignStmt(freshLocal, replacement);
    newUnits.add(replStmt);

    Local retLocal = localGen.generateLocal(returnType);

    switch (callKind) {
      case ClassForName: {
        // add: retLocal = freshLocal;
        newUnits.add(Jimple.newAssignStmt(retLocal, freshLocal));
        break;
      }
      case ClassNewInstance: {
        // add: freshLocal.<init>()
        SootClass targetClass = myScene.getSootClass(target);
        SpecialInvokeExpr constrCallExpr = Jimple.newSpecialInvokeExpr(freshLocal, myScene.makeMethodRef(targetClass,
            SootMethod.constructorName, Collections.<Type>emptyList(), primTypeCollector.getVoidType(), false));
        InvokeStmt constrCallStmt2 = Jimple.newInvokeStmt(constrCallExpr);
        newUnits.add(constrCallStmt2);
        // add: retLocal = freshLocal
        newUnits.add(Jimple.newAssignStmt(retLocal, freshLocal));
        break;
      }
      case ConstructorNewInstance: {
        // add: freshLocal.<target>(a0,...,an);
        SootMethod constructor = myScene.getMethod(target);
        SpecialInvokeExpr constrCallExpr
            = Jimple.newSpecialInvokeExpr(freshLocal, constructor.makeRef(), Arrays.asList(paramLocals));
        InvokeStmt constrCallStmt2 = Jimple.newInvokeStmt(constrCallExpr);
        newUnits.add(constrCallStmt2);
        // add: retLocal = freshLocal
        newUnits.add(Jimple.newAssignStmt(retLocal, freshLocal));
        break;
      }
      case MethodInvoke: {
        // add: freshLocal=recv.<target>(a0,...,an);
        SootMethod method = myScene.getMethod(target);
        InvokeExpr invokeExpr;
        if (method.isStatic()) {
          invokeExpr = Jimple.newStaticInvokeExpr(method.makeRef(), Arrays.asList(paramLocals));
        } else {
          invokeExpr = Jimple.newVirtualInvokeExpr(freshLocal, method.makeRef(), Arrays.<Value>asList(paramLocals));
        }
        if (method.getReturnType().equals(primTypeCollector.getVoidType())) {
          // method returns null; simply invoke it and return null
          InvokeStmt invokeStmt = Jimple.newInvokeStmt(invokeExpr);
          newUnits.add(invokeStmt);
          AssignStmt assignStmt = Jimple.newAssignStmt(retLocal, myNullConstant);
          newUnits.add(assignStmt);
        } else {
          AssignStmt assignStmt = Jimple.newAssignStmt(retLocal, invokeExpr);
          newUnits.add(assignStmt);
        }
        break;
      }
      case FieldSet: {
        // add freshLocal.<f> = v;
        Local value = localGen.generateLocal(fieldSetGetType);
        newUnits.insertBeforeNoRedirect(Jimple.newIdentityStmt(value, Jimple.newParameterRef(fieldSetGetType, 1)),
            replStmt);

        SootField field = myScene.getField(target);

        Local boxedOrCasted = localGen.generateLocal(field.getType());

        insertCastOrUnboxingCode(boxedOrCasted, value, newUnits);

        FieldRef fieldRef;
        if (field.isStatic()) {
          fieldRef = Jimple.newStaticFieldRef(field.makeRef());
        } else {
          fieldRef = Jimple.newInstanceFieldRef(freshLocal, field.makeRef());
        }
        newUnits.add(Jimple.newAssignStmt(fieldRef, boxedOrCasted));
        break;
      }
      case FieldGet: {
        /*
         * add: T2 temp = recv.<f>; return temp;
         */
        SootField field = myScene.getField(target);

        Local value = localGen.generateLocal(field.getType());

        FieldRef fieldRef;
        if (field.isStatic()) {
          fieldRef = Jimple.newStaticFieldRef(field.makeRef());
        } else {
          fieldRef = Jimple.newInstanceFieldRef(freshLocal, field.makeRef());
        }
        newUnits.add(Jimple.newAssignStmt(value, fieldRef));

        insertCastOrBoxingCode(retLocal, value, newUnits);

        break;
      }
    }

    if (!returnType.equals(primTypeCollector.getVoidType())) {
      newUnits.add(Jimple.newReturnStmt(retLocal));
    }

    if (myOptions.validate()) {
      newBody.validate();
    }

    cleanup(newBody);

    return newMethod;
  }

  private void insertCastOrUnboxingCode(Local lhs, Local rhs, Chain<Unit> newUnits) {
    // if assigning to a reference type then there's nothing to do
    if (lhs.getType() instanceof PrimType) {
      if ((rhs.getType() instanceof PrimType)) {
        // insert cast
        newUnits.add(Jimple.newAssignStmt(lhs, Jimple.newCastExpr(rhs, lhs.getType())));
      } else {
        // reference type in rhs; insert unboxing code
        RefType boxedType = (RefType) rhs.getType();
        SootMethodRef ref = myScene.makeMethodRef(boxedType.getSootClass(), lhs.getType().toString() + "Value",
            Collections.<Type>emptyList(), lhs.getType(), false);
        newUnits.add(Jimple.newAssignStmt(lhs, Jimple.newVirtualInvokeExpr(rhs, ref)));
      }
    }
  }

  private void insertCastOrBoxingCode(Local lhs, Local rhs, Chain<Unit> newUnits) {
    // if assigning to a primitive type then there's nothing to do
    if (lhs.getType() instanceof RefLikeType) {
      if ((rhs.getType() instanceof RefLikeType)) {
        // insert cast
        newUnits.add(Jimple.newAssignStmt(lhs, Jimple.newCastExpr(rhs, lhs.getType())));
      } else {
        // primitive type in rhs; insert boxing code
        RefType boxedType = ((PrimType) rhs.getType()).boxedType();
        SootMethodRef ref = myScene.makeMethodRef(boxedType.getSootClass(), "valueOf",
            Collections.<Type>singletonList(rhs.getType()), boxedType, true);
        newUnits.add(Jimple.newAssignStmt(lhs, Jimple.newStaticInvokeExpr(ref, rhs)));
      }
    }
  }

  /**
   * Auto-unboxes an argument array.
   *
   * @param argsArrayLocal
   *          a local holding the argument Object[] array
   * @param paramIndex
   *          the index of the parameter to unbox
   * @param paramType
   *          the (target) type of the parameter
   * @param newUnits
   *          the Unit chain to which the unboxing code will be appended
   * @param localGen
   *          a {@link LocalGenerator} for the body holding the units
   */
  private void unboxParameter(Local argsArrayLocal, int paramIndex, Local[] paramLocals, Type paramType,
      Chain<Unit> newUnits, LocalGenerator localGen) {
    ArrayRef arrayRef = Jimple.newArrayRef(argsArrayLocal, constantFactory.createIntConstant(paramIndex));
    AssignStmt assignStmt;
    if (paramType instanceof PrimType) {
      PrimType primType = (PrimType) paramType;
      // Unbox the value if needed
      RefType boxedType = primType.boxedType();
      SootMethodRef ref = myScene.makeMethodRef(boxedType.getSootClass(), paramType + "Value",
          Collections.<Type>emptyList(), paramType, false);
      Local boxedLocal = localGen.generateLocal(RefType.v("java.lang.Object",myScene));
      AssignStmt arrayLoad = Jimple.newAssignStmt(boxedLocal, arrayRef);
      newUnits.add(arrayLoad);
      Local castedLocal = localGen.generateLocal(boxedType);
      AssignStmt cast = Jimple.newAssignStmt(castedLocal, Jimple.newCastExpr(boxedLocal, boxedType));
      newUnits.add(cast);
      VirtualInvokeExpr unboxInvokeExpr = Jimple.newVirtualInvokeExpr(castedLocal, ref);
      assignStmt = Jimple.newAssignStmt(paramLocals[paramIndex], unboxInvokeExpr);
    } else {
      Local boxedLocal = localGen.generateLocal(RefType.v("java.lang.Object",myScene));
      AssignStmt arrayLoad = Jimple.newAssignStmt(boxedLocal, arrayRef);
      newUnits.add(arrayLoad);
      Local castedLocal = localGen.generateLocal(paramType);
      AssignStmt cast = Jimple.newAssignStmt(castedLocal, Jimple.newCastExpr(boxedLocal, paramType));
      newUnits.add(cast);
      assignStmt = Jimple.newAssignStmt(paramLocals[paramIndex], castedLocal);
    }
    newUnits.add(assignStmt);
  }

}
