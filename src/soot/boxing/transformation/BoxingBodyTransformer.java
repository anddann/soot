package soot.boxing.transformation;

import soot.*;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.*;
import soot.util.Chain;
import soot.util.Cons;

import java.util.*;

/**
 * Created by adann on 11.05.17.
 * Jimple Body Transformer for Boxing Primitive Type
 */

//FIXME: adapat to normal soot scene
//currently only adapated to ModuleScene


public class BoxingBodyTransformer extends BodyTransformer {

    public BoxingBodyTransformer(Singletons.Global g) {

    }

    public static BoxingBodyTransformer v() {
        return G.v().soot_boxing_transformation_BoxingBodyTransformer();
    }


    //!!!warning using a private field "body" fucks up parallel execution!!!

    //!!! in generel private fields fuck up the execution


    //FIXME: use AbstractStmtSwitch
    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {

        Value intCounter = null;
        SootMethod methodAlreadyExists = null;

        if (BoxingTransformerUtility.isMethodIgnored(body.getMethod()))
            return;

        HashMap<Value, Type> originalLocalTypes = new HashMap<>();


        //store the original types
        for (Local l : body.getLocals()) {
            if (l.getType() instanceof ArrayType) {
                originalLocalTypes.put(l, ((ArrayType) l.getType()).baseType);

            } else {
                originalLocalTypes.put(l, l.getType());
            }
        }

        //adapt method signature
        methodAlreadyExists = BoxingTransformerUtility.adaptMethodSignature(body);
        //the method already exits


        LocalGenerator localGenerator = new LocalGenerator(body);
        int conditionCounter = 0;


        //units.snapshotIterator()
        for (Iterator<Unit> it = body.getUnits().snapshotIterator(); it.hasNext(); ) {
            Unit unit = it.next();


            handleUnit(unit, body, originalLocalTypes, intCounter, conditionCounter, localGenerator);


        }
        //adapt the parameter identity statements
        for (Iterator<Unit> it = body.getUnits().snapshotIterator(); it.hasNext(); ) {
            Unit unit = it.next();
            if (!(unit instanceof IdentityStmt))
                continue;
            Value value = null;
            boolean isCompatibe = BoxingTransformerUtility.isCompatible(((IdentityStmt) unit).getLeftOp().getType(), ((IdentityStmt) unit).getRightOp().getType());
            if (!isCompatibe)
                value = ((IdentityStmt) unit).getRightOp();
            if (value instanceof ParameterRef)
                ((ParameterRef) value).setType(BoxingTransformerUtility.getBoxedType(value.getType()));
            isCompatibe = BoxingTransformerUtility.isCompatible(((IdentityStmt) unit).getLeftOp().getType(), ((IdentityStmt) unit).getRightOp().getType());
            if (!isCompatibe)
                System.out.println("hihi");


        }


    }


    private void handleUnit(Unit unit, Body body, HashMap<Value, Type> originalLocalTypes, Value intCounter, int conditionCounter, LocalGenerator localGenerator) {

        if (unit instanceof IdentityUnit &&
                ((IdentityUnit) unit).getLeftOp() instanceof Local) {
            handleIdentityStmt((IdentityStmt) unit, body);
        }

        if (unit instanceof DefinitionStmt) {
            handleDefinitionStmt((DefinitionStmt) unit, body, originalLocalTypes, intCounter, conditionCounter, localGenerator);
        }

        if (unit instanceof IfStmt) {
            handleIfStmt((IfStmt) unit, body, originalLocalTypes, localGenerator);
        }

        if (unit instanceof SwitchStmt) {
            handleSwitchStmt((SwitchStmt) unit, body, originalLocalTypes, localGenerator);
        }

        // normal invoke expression
        if (unit instanceof InvokeStmt) {
            handleInvokeExpr(((InvokeStmt) unit).getInvokeExpr(), unit, body, originalLocalTypes, localGenerator);
        }

    }


    private void handleDefinitionStmt(DefinitionStmt definitionStmt, Body body, HashMap<Value, Type> originalLocalTypes, Value intCounter, int conditionCounter, LocalGenerator localGenerator) {
        Type originalType = null;
        Value leftValue = definitionStmt.getLeftOp();
        Value rightValue = definitionStmt.getRightOp();

        //process the leftSide first
        if (leftValue instanceof Local) {
            originalType = originalLocalTypes.get(leftValue);
            if (BoxingTransformerUtility.isTypeToModify(originalType)) {
                ((Local) leftValue).setType(BoxingTransformerUtility.getBoxedType(leftValue.getType()));

            }


        }
        // is this possible?
        if (leftValue instanceof InvokeExpr) {
            handleInvokeExpr((InvokeExpr) leftValue, definitionStmt, body, originalLocalTypes, localGenerator);
        }
        if (leftValue instanceof FieldRef) {
            originalType = handleFieldRef((FieldRef) leftValue, definitionStmt, body, originalLocalTypes, localGenerator);


        }
        if (leftValue instanceof ArrayRef) {
            originalType = handleArrayRef((ArrayRef) leftValue, definitionStmt, body, originalLocalTypes, localGenerator);

        }

       /* if (leftValue instanceof InvokeExpr) {
            handleInvokeExpr((InvokeExpr) leftValue, definitionStmt, body, originalLocalTypes, localGenerator);
        }*/


        /*
         *   now, process the right side
         */

        // extend to Constant for char //changed from NumericConstant
        if (rightValue instanceof NumericConstant) {
            List<Unit> newAssignStmt = this.assignTo(leftValue, originalType, rightValue, originalLocalTypes, localGenerator);
            body.getUnits().insertAfter(newAssignStmt, definitionStmt);
            body.getUnits().remove(definitionStmt);
            //it.remove();
            return;
        }


        // if right value references another local
        //NO aliasing for primitive types!!!
        // then simply assignment
        if (rightValue instanceof Local) {
            Unit newAssignStmt = this.assignLocalTo(leftValue, (Local) rightValue, originalLocalTypes);
            body.getUnits().insertAfter(newAssignStmt, definitionStmt);
            body.getUnits().remove(definitionStmt);
            //it.remove();
            return;
        }

        if (rightValue instanceof FieldRef) {
            handleFieldRef((FieldRef) rightValue, definitionStmt, body, originalLocalTypes, localGenerator);
        }


        //if right value is array ref
        if (rightValue instanceof ArrayRef) {
            handleArrayRef((ArrayRef) rightValue, definitionStmt, body, originalLocalTypes, localGenerator);

        }

        if (rightValue instanceof InvokeExpr) {
            handleInvokeExpr((InvokeExpr) rightValue, definitionStmt, body, originalLocalTypes, localGenerator);
        }


        //right value is BinaryOpr
        if (rightValue instanceof BinopExpr) {
            handleBinOperationExpression((BinopExpr) rightValue, definitionStmt, leftValue, originalType, body, originalLocalTypes, intCounter, conditionCounter, localGenerator);
            //remove the original unit
            body.getUnits().remove(definitionStmt);
            //it.remove();

        }
        if (rightValue instanceof NewArrayExpr) {
            handleNewArrayExpr(leftValue, (NewArrayExpr) rightValue, definitionStmt, body, originalLocalTypes, localGenerator);
        }

        if (rightValue instanceof NewMultiArrayExpr) {
            handleNewMultiArrayExpr(leftValue, (NewMultiArrayExpr) rightValue, definitionStmt, body, originalLocalTypes, localGenerator);
        }

        if (rightValue instanceof CastExpr) {
            handleCastExpr(leftValue, (CastExpr) rightValue, definitionStmt, body, localGenerator);
        }


        if (rightValue instanceof InstanceOfExpr) {
            handleInstanceOfExpr(leftValue, (InstanceOfExpr) rightValue, definitionStmt, body, localGenerator);
        }

        if (rightValue instanceof UnopExpr) {
            handleUnopExpr(leftValue, rightValue, definitionStmt, body, localGenerator);
        }


    }

    private void handleUnopExpr(Value leftValue, Value rightValue, DefinitionStmt definitionStmt, Body body, LocalGenerator localGenerator) {
        if (rightValue instanceof NegExpr) {
            handleNegExpr(leftValue, (NegExpr) rightValue, definitionStmt, body, localGenerator);
        }
        if (rightValue instanceof LengthExpr) {
            handleLengthExpr(leftValue, (LengthExpr) rightValue, definitionStmt, body, localGenerator);
        }

    }

    // since we do not maintain semantics for assignments, we just transform it to an assignment
    private void handleNegExpr(Value leftValue, NegExpr negExpr, DefinitionStmt definitionStmt, Body body, LocalGenerator localGenerator) {
        //we have
        //Integer j
        // Integer i
        // Integer i = -j;

        // Integer i = j;
        Value rightValue = negExpr.getOp();
        if (rightValue instanceof Constant) {
            List<Unit> assignment = assignConstantTo(leftValue, BoxingTransformerUtility.getUnBoxedType(leftValue.getType()), (Constant) rightValue, localGenerator);
            body.getUnits().insertBefore(assignment, definitionStmt);
            body.getUnits().remove(definitionStmt);
        } else {
            //do a simple assignment
            Stmt assignment = Jimple.v().newAssignStmt(leftValue, rightValue);
            body.getUnits().insertBefore(assignment, definitionStmt);
            body.getUnits().remove(definitionStmt);
        }

    }

    private void handleInstanceOfExpr(Value leftValue, InstanceOfExpr instanceOfExpr, DefinitionStmt definitionStmt, Body body, LocalGenerator localGenerator) {

        //we have after lifting
        // Boolean  $z0 = (bool) r15 instanceof jdk.internal.ref.Cleaner
        // we have to transform it to
        // bool newLocal = (bool) r15 instanceof jdk.internal.ref.Cleaner
        // Boolean z0 = new Boolean(newLocal)
        if (leftValue.getType() instanceof BooleanType) {
            return;
        }

        //create local int newLocal
        Local newLocal = localGenerator.generateLocal(BooleanType.v());
        Stmt newLocalAssign = Jimple.v().newAssignStmt(newLocal, instanceOfExpr);
        body.getUnits().insertBefore(newLocalAssign, definitionStmt);

        SootClass sootClassForConstructor = ((RefType) leftValue.getType()).getSootClass();
        Type typeForConstructor = BoxingTransformerUtility.getUnBoxedType(leftValue.getType());
        //create Integer i0 = new Integer(newLocal)
        List<Unit> createdStmt = createNewStmtForBoxedType(sootClassForConstructor, typeForConstructor, leftValue, newLocal);
      /*
        SootMethod constructorToCall = sootClassForConstructor.getMethod("void <init>(" + typeForConstructor.getEscapedName() + ")");

        List<Value> args = new LinkedList<Value>();
        if (constructorToCall.getParameterCount() > 0) {
            for (Type tp : constructorToCall.getParameterTypes()) {
                args.add(newLocal);
            }
        }
        //new Expression
        Expr newExpr = Jimple.v().newNewExpr(RefType.v(sootClassForConstructor));
        Stmt assignment = Jimple.v().newAssignStmt(leftValue, newExpr);
        body.getUnits().insertBefore(assignment,definitionStmt);

        InvokeExpr invokeExpr = Jimple.v().newSpecialInvokeExpr((Local) leftValue, constructorToCall.makeRef(), args);
        Stmt invokeStmt = Jimple.v().newInvokeStmt(invokeExpr);
       // Stmt constructor = Jimple.v().newAssignStmt(leftValue, invokeExpr);*/
        body.getUnits().insertBefore(createdStmt, definitionStmt);
        body.getUnits().remove(definitionStmt);
    }

    private List<Unit> createNewStmtForBoxedType(SootClass sootClassForConstructor, Type typeForConstructor, Value baseValue, Value arg) {
        ArrayList<Unit> newCreatedStatements = new ArrayList<>();
        //SootMethod constructorToCall = sootClassForConstructor.getMethod("void <init>(" + typeForConstructor.getEscapedName() + ")");
        ArrayList<Type> parameter = new ArrayList<>();
        parameter.add(typeForConstructor);
        SootMethod constructorToCall = getMethodOnSnapshot(sootClassForConstructor, "<init>", parameter, VoidType.v());

        List<Value> args = new LinkedList<>();
        if (constructorToCall.getParameterCount() > 0) {
            for (Type tp : constructorToCall.getParameterTypes()) {
                args.add(arg);
            }
        }
        //new Expression
        Expr newExpr = Jimple.v().newNewExpr(RefType.v(sootClassForConstructor));
        Stmt assignment = Jimple.v().newAssignStmt(baseValue, newExpr);
        //body.getUnits().insertBefore(assignment,definitionStmt);
        newCreatedStatements.add(assignment);


        InvokeExpr invokeExpr = Jimple.v().newSpecialInvokeExpr((Local) baseValue, constructorToCall.makeRef(), args);
        Stmt invokeStmt = Jimple.v().newInvokeStmt(invokeExpr);
        newCreatedStatements.add(invokeStmt);
        return newCreatedStatements;
    }

    private void handleLengthExpr(Value leftValue, LengthExpr lengthExpr, DefinitionStmt definitionStmt, Body body, LocalGenerator localGenerator) {
        //we have after lifting
        // Integer i0 = (int) lengthof r0
        // we have to transform it to
        // int newLocal = lengthof r0;
        // Integer i0 = new Integer(newLocal)
        if (leftValue.getType() instanceof IntType) {
            return;
        }

        //create local int newLocal
        Local newLocal = localGenerator.generateLocal(IntType.v());
        Stmt newLocalAssign = Jimple.v().newAssignStmt(newLocal, lengthExpr);
        body.getUnits().insertBefore(newLocalAssign, definitionStmt);


        SootClass sootClassForConstructor = ((RefType) leftValue.getType()).getSootClass();
        Type typeForConstructor = BoxingTransformerUtility.getUnBoxedType(leftValue.getType());
        List<Unit> createdStmt = createNewStmtForBoxedType(sootClassForConstructor, typeForConstructor, leftValue, newLocal);


        body.getUnits().insertBefore(createdStmt, definitionStmt);
        body.getUnits().remove(definitionStmt);

    }

    private void handleCastExpr(Value leftValue, CastExpr castExpr, DefinitionStmt definitionStmt, Body body, LocalGenerator localGenerator) {
        if ((leftValue instanceof FieldRef) && (BoxingTransformerUtility.isFieldIgnored(((FieldRef) leftValue).getField()))) {
            return;
        }

        //if the cast is of non-primitive type, we can ignore it, since we only lift primitive types
        if (!BoxingTransformerUtility.isTypeToModify(castExpr.getCastType())) {
            return;
        }

        if (castExpr.getCastType() instanceof PrimType) {

            // we have to convert the value properly,
            //e.g., Long l = (long) Integer i;
            // is transformed to
            // l= new Long(Integer.toString())
            // in Jimple
            // String newLocal = i.toString();
            // l = new Long(newLocal);


            //first part:
            // String newLocal = new String
            // String newLocal = i.toString();
            SootClass sootClassForNewLocal = ModuleScene.v().getSootClass("java.lang.String", com.google.common.base.Optional.of("java.base"));
            RefType stringType = RefType.v(sootClassForNewLocal);


            Local newStringLocal = localGenerator.generateLocal(stringType);

            Expr newExpr = Jimple.v().newNewExpr(stringType);
            Stmt assignment = Jimple.v().newAssignStmt(newStringLocal, newExpr);
            body.getUnits().insertBefore(assignment, definitionStmt);


            //FIXME: case if right type is Constant

            List<Unit> createdStatements = null;
            if (castExpr.getOp() instanceof Constant) {

                //if its a constant a new Integer expression should be sufficnent
                createdStatements = assignConstantTo((Local) leftValue, (castExpr.getOp().getType()), (Constant) castExpr.getOp(), localGenerator);


            }
            if (castExpr.getOp().getType() instanceof RefType) {
                SootClass sootClassOfRightSide = ((RefType) castExpr.getOp().getType()).getSootClass();

//            SootMethod methodToCall = sootClassOfRightSide.getMethod(stringType.getClassName() + " toString()");
                SootMethod methodToCall = getMethodOnSnapshot(sootClassOfRightSide, "toString", new ArrayList<>(), stringType);
                InvokeExpr toStringInvokeExpr = Jimple.v().newVirtualInvokeExpr((Local) castExpr.getOp(), methodToCall.makeRef());
                Stmt stringAssignment = Jimple.v().newAssignStmt(newStringLocal, toStringInvokeExpr);
                body.getUnits().insertBefore(stringAssignment, definitionStmt);


                // second part:
                // l = new Long(newLocal);
                Type typeForConstructor = stringType;
                SootClass sootClassForConstructor = ((RefType) leftValue.getType()).getSootClass();
                Value argForConstructor = newStringLocal;

                //special case if casted to char
                if (castExpr.getCastType() instanceof CharType) {
                    //e.g., Character c = (char) Integer i;
                    //we have to transform it to
                    // String newStringLocal = new String()
                    // String newStringLocal = i.toString()
                    // char c1 = i.charAt(0);
                    // Character c  = new Character(c1)

                    //create char c1 = i.charAt(0);
                    ArrayList<Type> parameterTypes = new ArrayList<>();
                    parameterTypes.add(IntType.v());
                    SootMethod methodCharAt = getMethodOnSnapshot(stringType.getSootClass(), "charAt", parameterTypes, CharType.v());

                    // SootMethod methodCharAt = stringType.getSootClass().getMethod("charAt", parameterTypes, CharType.v());
                    //   SootMethod methodCharAt = stringType.getSootClass().getMethod(CharType.v().getEscapedName() + " charAt(" + IntType.v().getEscapedName() + ")");
                    Local charLocal = localGenerator.generateLocal(CharType.v());
                    List<Value> args = new LinkedList<>();
                    if (methodCharAt.getParameterCount() > 0) {
                        for (Type tp : methodToCall.getParameterTypes()) {
                            args.add(IntConstant.v(0));
                        }
                    }

                    InvokeExpr invokeCharAt = Jimple.v().newVirtualInvokeExpr(newStringLocal, methodCharAt.makeRef(), args);
                    Stmt charAssignment = Jimple.v().newAssignStmt(charLocal, invokeCharAt);

                    body.getUnits().insertBefore(charAssignment, definitionStmt);

                    typeForConstructor = CharType.v();
                    argForConstructor = charLocal;


                }
                createdStatements = createNewStmtForBoxedType(sootClassForConstructor, typeForConstructor, leftValue, argForConstructor);
            }

            body.getUnits().insertBefore(createdStatements, definitionStmt);
            body.getUnits().remove(definitionStmt);
            return;
        }


        if (castExpr.getCastType() instanceof ArrayType) {
            Value rightValue = castExpr.getOp();
            //if right instance of object simply lift the cast
            Type objectType = RefType.v("java.lang.Object");
            if (rightValue.getType() == objectType || rightValue.getType() == NullType.v()) {
                castExpr.setCastType(BoxingTransformerUtility.getBoxedType(castExpr.getCastType()));

            } else {
                //cast to a primitive[]
                //cannot cast anything to prim[] except Object in java
                //thus this case can never occur
                if (rightValue.getType() instanceof ArrayType && ((((ArrayType) rightValue.getType()).baseType == objectType))) {
                    castExpr.setCastType(BoxingTransformerUtility.getBoxedType(castExpr.getCastType()));
                } else {

                    throw new RuntimeException("Found cast Stmt, I cannot deal with: " + castExpr.toString());
                }


            }

        }


    }


    private void handleNewMultiArrayExpr(Value leftValue, NewMultiArrayExpr newMultiArrayExpr, DefinitionStmt definitionStmt, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        if ((leftValue instanceof FieldRef) && (BoxingTransformerUtility.isFieldIgnored(((FieldRef) leftValue).getField()))) {
            return;
        }

        newMultiArrayExpr.setBaseType((ArrayType) BoxingTransformerUtility.getBoxedType(newMultiArrayExpr.getBaseType()));


        for (int i = 0; i < newMultiArrayExpr.getSizeCount(); i++) {
            Value size = newMultiArrayExpr.getSize(i);
            //if it is a constant everything is fine
            if (size instanceof Constant) {
                //nothing to do
                continue;
            }

            //if its a local, we have
            // array[$local]
            // and in the previous steps we lifted $local to the boxing type
            // for arrays we have to getUnBoxedType it and generate
            // int dummyIndex = $local.intValue()
            // array[dummyIndex]
            if (size instanceof Local) {
                Value unboxedSize = unboxValue(size, definitionStmt, body, originalLocalTypes, localGenerator);
                if (unboxedSize != null)
                    newMultiArrayExpr.setSize(i, unboxedSize);
            }


        }

    }

    private void handleNewArrayExpr(Value leftSide, NewArrayExpr newArrayExpr, Unit unit, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        if ((leftSide instanceof FieldRef) && (BoxingTransformerUtility.isFieldIgnored(((FieldRef) leftSide).getField()))) {
            return;
        }

        newArrayExpr.setBaseType(BoxingTransformerUtility.getBoxedType(newArrayExpr.getBaseType()));

        //check the size argument
        Value size = newArrayExpr.getSize();
        //if it is a constant everything is fine
        if (size instanceof Constant) {
            //nothing to do
            return;
        }

        //if its a local, we have
        // array[$local]
        // and in the previous steps we lifted $local to the boxing type
        // for arrays we have to getUnBoxedType it and generate
        // int dummyIndex = $local.intValue()
        // array[dummyIndex]
        if (size instanceof Local) {
            Value unboxedSize = unboxValue(size, unit, body, originalLocalTypes, localGenerator);
            if (unboxedSize != null)
                newArrayExpr.setSize(unboxedSize);
        }

    }

    private void handleBinOperationExpression(BinopExpr binopExpr, DefinitionStmt definitionStmt, Value leftValue, Type originalType, Body body, HashMap<Value, Type> originalLocalTypes, Value intCounter, int conditionCounter, LocalGenerator localGenerator) {
        //for our transformation, we can make if expressions
        // e.g. a = b + c ---> if(Cond1) a = b; if(cond2) a = c
        //take care of the fact, that a might be an int, whereas a, c might be byte or float
        // then we hate to generate Integer.valueOf(b.intValue())
        if (intCounter == null) {
            intCounter = localGenerator.generateLocal(IntType.v());
            //add this as an already boxed typed to avoid the transformation of it ;)
            originalLocalTypes.put(intCounter, ((PrimType) intCounter.getType()).boxedType());
        }
        Value first = binopExpr.getOp1();

        EqExpr cond = Jimple.v().newEqExpr(intCounter, IntConstant.v(conditionCounter));
        conditionCounter++;

        //the thenStmt must be the statement after the new inserted code
        Unit thenStmt = body.getUnits().getSuccOf(definitionStmt);
        IfStmt ifStmt = Jimple.v().newIfStmt(cond, thenStmt);
        body.getUnits().insertAfter(ifStmt, definitionStmt);

        //if target type (left local) and type of right local do not math
        // since now everything is numerable no problem... (hopefully)
        //List<Unit> creatededStmts = handleUnboxingReboxing(leftValue, first, generator, originalLocaTypes, originalType);
        // creatededStmts.add(thenStmt);
        // b.getUnits().insertAfter(creatededStmts, ifStmt);


        //create a = b
        //  List<Unit> firstAssignment = this.createAssignmentToBoxedType(leftValue, originalType, first);
        List<Unit> firstAssignment = this.assignTo(leftValue, originalType, first, originalLocalTypes, localGenerator);

        body.getUnits().insertAfter(firstAssignment, ifStmt);

        //create a=c
        //then the same again for second ...
        Value second = binopExpr.getOp2();

        EqExpr secondCond = Jimple.v().newEqExpr(intCounter, IntConstant.v(conditionCounter));
        conditionCounter++;

        //the thenStmt must be the statement after the new inserted code
        Unit secondThenStmt = body.getUnits().getSuccOf(definitionStmt);
        IfStmt secondIfStmt = Jimple.v().newIfStmt(secondCond, secondThenStmt);
        body.getUnits().insertAfter(secondIfStmt, firstAssignment.get(firstAssignment.size() - 1));


        //create a = b
        List<Unit> secondAssignment = this.assignTo(leftValue, originalType, second, originalLocalTypes, localGenerator);
        body.getUnits().insertAfter(secondAssignment, secondIfStmt);

    }


    private Type handleFieldRef(FieldRef fieldRef, Unit unit, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        Type originalType = fieldRef.getFieldRef().type();
        SootField sootField = fieldRef.getField();

        Type currentFieldType = sootField.getType();


        if (!BoxingTransformerUtility.isTypeToModify(currentFieldType))
            return originalType;


        if (BoxingTransformerUtility.isFieldIgnored(sootField)) {
            handleFieldRefForIgnoredField(fieldRef, unit, body, originalLocalTypes, localGenerator);
            return originalType;
        }


        sootField.setType(BoxingTransformerUtility.getBoxedType(currentFieldType));
        ((BoxingSootFieldRefImpl) fieldRef.getFieldRef()).liftTheReference();

        if (originalType != currentFieldType)
            System.out.println("FIELD REF Prob");

        return originalType;
    }


    private void handleFieldRefForIgnoredField(FieldRef fieldRef, Unit unit, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        //definition to something on the left side ..
        if (unit instanceof DefinitionStmt) {
            DefinitionStmt definitionStmt = (DefinitionStmt) unit;
            Value leftSide = definitionStmt.getLeftOp();
            Value rightSide = definitionStmt.getRightOp();


            //handle fieldRef = something
            if (leftSide instanceof FieldRef) {
                //getUnBoxedType the value and make the assignment, since we don't lift ignored fields
                Local unboxedLocal = unboxValue(rightSide, unit, body, originalLocalTypes, localGenerator);

                //make assignment
                Stmt assignment = Jimple.v().newAssignStmt(leftSide, unboxedLocal);
                body.getUnits().insertBefore(assignment, unit);
                body.getUnits().remove(definitionStmt);
                return;
            }


            //  handles value = fieldRef
            if (rightSide instanceof FieldRef) {
                Type typeOfLeftSide = leftSide.getType();

                Type typeOfRightSide = ((FieldRef) rightSide).getField().getType();
                //weak criteria
                boolean mustBeAdapted = (typeOfLeftSide != typeOfRightSide);
                if (typeOfLeftSide instanceof RefType && typeOfRightSide instanceof RefType)
                    mustBeAdapted = !BoxingTransformerUtility.isCompatible(typeOfRightSide, typeOfLeftSide);
                boolean isArrayType = typeOfLeftSide instanceof ArrayType;
                if (mustBeAdapted) {

                    if (!isArrayType) {
                        //we have, e.g.,
                        // Integer leftValue = int Integer.field
                        //we have to transform it to
                        // int fieldLocal = field
                        // Integer leftValue = new Integer(fieldLocal)

                        //Class Local
                        //get Boxing Method
                        SootClass valueBoxedClass = ((RefType) BoxingTransformerUtility.getBoxedType(typeOfRightSide)).getSootClass();
                        Local sootClassForLocal = localGenerator.generateLocal(typeOfLeftSide);
                        Local fieldLocal = localGenerator.generateLocal(typeOfRightSide);

                        Stmt assignment = Jimple.v().newAssignStmt(fieldLocal, fieldRef);
                        body.getUnits().insertBefore(assignment, definitionStmt);

                        List<Unit> createdStmts = createNewStmtForBoxedType(valueBoxedClass, typeOfRightSide, sootClassForLocal, fieldLocal);
                        body.getUnits().insertBefore(createdStmts, definitionStmt);
                        body.getUnits().remove(definitionStmt);
                    } else {
                        //we have, e.g.,
                        // Integer[] leftValue = int[] Integer.field
                        //we have to transform it to
                        // int[] fieldLocal = field
                        // Integer[] leftValue = boxingArray(fieldLoca)

                        //FIXME: test this new code
                        Local fieldLocal = localGenerator.generateLocal(typeOfRightSide);

                        Stmt assignment = Jimple.v().newAssignStmt(fieldLocal, fieldRef);
                        body.getUnits().insertBefore(assignment, definitionStmt);

                        Local boxedArray = boxArray(fieldLocal, definitionStmt, body, localGenerator);
                        Stmt assignBoxedArrayToOriginalLocal = Jimple.v().newAssignStmt(definitionStmt.getLeftOp(), boxedArray);
                        body.getUnits().insertBefore(assignBoxedArrayToOriginalLocal, definitionStmt);

                        body.getUnits().remove(definitionStmt);

                    }

                }
            }
        }
    }

    private Type handleArrayRef(ArrayRef arrayRef, DefinitionStmt definitionStmt, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        Value array = arrayRef.getBase();

        Type originalType = originalLocalTypes.get(array);
        if (!BoxingTransformerUtility.isTypeToModify(originalType)) {
            return originalType;
        }


        // this is the original code;
        ArrayType arrayType = (ArrayType) arrayRef.getBase().getType();
        //arrayType.baseType = BoxingTransformerUtility.getBoxedType(arrayType.baseType);

        //migrate
        // TODO: check if this migration actually works
        ArrayType liftedArrayType = ArrayType.v(BoxingTransformerUtility.getBoxedType(arrayType.baseType), arrayType.numDimensions);
        ((Local) arrayRef.getBase()).setType(liftedArrayType);


        //now we have to look for the index of the array
        Value index = arrayRef.getIndex();

        //if it is a constant everything is fine
        if (index instanceof Constant) {
            //nothing to do
            return originalType;
        }

        //if its a local, we have
        // array[$local]
        // and in the previous steps we lifted $local to the boxing type
        // for arrays we have to getUnBoxedType it and generate
        // int dummyIndex = $local.intValue()
        // array[dummyIndex]
        if (index instanceof Local) {
            Value unboxedIndex = unboxValue(index, definitionStmt, body, originalLocalTypes, localGenerator);
            if (unboxedIndex != null)
                arrayRef.setIndex(unboxedIndex);
        }

        return originalType;
    }

    private void handleIfStmt(IfStmt ifStmt, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        Value value = ifStmt.getCondition();
        if (value instanceof ConditionExpr) {
            ConditionExpr conditionExpr = (ConditionExpr) value;
            handleUnboxingForBinaryExpression(ifStmt, conditionExpr, body, originalLocalTypes, localGenerator);
        }
    }

    private void handleSwitchStmt(SwitchStmt switchStmt, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        Value value = switchStmt.getKey();
        Value unboxedValue = unboxValue(value, switchStmt, body, originalLocalTypes, localGenerator);
        if (unboxedValue != null) {
            switchStmt.setKey(unboxedValue);
        }
    }

    private void handleIdentityStmt(IdentityStmt identityStmt, Body body) {
        Local l = (Local) identityStmt.getLeftOp();
        if (!BoxingTransformerUtility.isCompatible(identityStmt.getLeftOp().getType(), identityStmt.getRightOp().getType())) {
            System.out.print("Types do not match");
        }
        if (!BoxingTransformerUtility.isTypeToModify(l.getType()))
            return;
        // l.setType(((PrimType) l).boxedType());
        Value value = identityStmt.getRightOp();
    }


    /**
     * Adapts a method reference
     * changes the return type and parameter types to the boxed type for a method reference
     *
     * @param invokeExpr the Expr to handle
     * @param unit       the unit in which the invokeExpr is used
     */
    private void handleInvokeExpr(InvokeExpr invokeExpr, Unit unit, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {

        SootMethodRef methodRef = invokeExpr.getMethodRef();
        if (BoxingTransformerUtility.isMethodIgnored(methodRef)) {
            if(methodRef.declaringClass().getName().equals(SootClass.INVOKEDYNAMIC_DUMMY_CLASS_NAME))
                return;
            handleInvokeExprForIgnoredMethod(invokeExpr, unit, body, originalLocalTypes, localGenerator);
            return;
        }

        ((BoxingSootMethodRefImpl) methodRef).liftTheReference();

        //adapt args...
        // since we lift the methods' signatures to boxed type, const arguments must also be boxed
        for (int i = 0; i < invokeExpr.getArgCount(); i++) {
            Value arg = invokeExpr.getArg(i);
            if (arg instanceof NumericConstant) {
                NumericConstant numericConstant = (NumericConstant) arg;
                Local newLocal = localGenerator.generateLocal(BoxingTransformerUtility.getBoxedType(methodRef.parameterType(i)));
                List<Unit> assignments = assignTo(newLocal, BoxingTransformerUtility.getUnBoxedType(methodRef.parameterType(i)), numericConstant, originalLocalTypes, localGenerator);
                //add assignment to body before this invoke expression
                body.getUnits().insertBefore(assignments, unit);
                invokeExpr.setArg(i, newLocal);
            }
        }

    }

    /**
     * We do not modify the invoke expressions for
     *
     * @param invokeExpr the expr to handle
     * @param unit       the unit in which the invokeExpr is defined
     * @param body
     * @see BoxingTransformerUtility ignored Classes
     * thus we need to take care of this methods specifically
     */
    private void handleInvokeExprForIgnoredMethod(InvokeExpr invokeExpr, Unit unit, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        Unit insertBefore = unit;

        //du to auto boxing, we might result in
        // Integer $r2 = staticinvoke <java.lang.Integer: java.lang.Integer valueOf(int)>( Integer $i0);
        //after lifting this does not make any sense
        // if $r2 and $i0 are already integer, we can transform it into an simple assignmeint
        if (unit instanceof DefinitionStmt && invokeExpr.getMethodRef().name().contains("valueOf")) {
            Value leftSide = ((DefinitionStmt) unit).getLeftOp();
            Value rightSide = invokeExpr.getArg(0);
            if (leftSide.getType() == rightSide.getType()) {
                //make it a simple assignment
                Stmt assignment = Jimple.v().newAssignStmt(leftSide, rightSide);
                body.getUnits().insertBefore(assignment, unit);
                body.getUnits().remove(unit);
                return;
            }

        }

        if (unit instanceof DefinitionStmt) {
            DefinitionStmt definitionStmt = (DefinitionStmt) unit;
            Type typeOfLeftSide = definitionStmt.getLeftOp().getType();

            Type typeOfRightSide = invokeExpr.getMethodRef().returnType();

            boolean mustBeAdapted = !BoxingTransformerUtility.isCompatible(typeOfRightSide, typeOfLeftSide);
            boolean isArrayType = typeOfLeftSide instanceof ArrayType;


            if (mustBeAdapted) {
                if (!isArrayType) {
                    //we have a definition and the return type does not match
                    // e.g., Integer l1 = Integer: int method();
                    // l1 != return type method()
                    //thus, we need to add new local
                    // int newLocal = invokeExpr()
                    // l1 = Integer.valueOf(newLocal)

                    //new local
                    Local newLocal = localGenerator.generateLocal(typeOfRightSide);
                    AssignStmt stmt = Jimple.v().newAssignStmt(newLocal, invokeExpr);
                    body.getUnits().insertBefore(stmt, insertBefore);

                    insertBefore = stmt;
                    //do Boxing of new Local
                    SootClass valueBoxedClass = ((RefType) BoxingTransformerUtility.getBoxedType(typeOfRightSide)).getSootClass();
                    List<Unit> createdStmts = createNewStmtForBoxedType(valueBoxedClass, typeOfRightSide, definitionStmt.getLeftOp(), newLocal);

                    body.getUnits().insertAfter(createdStmts, stmt);
                    //remove the original definitionStmt
                    body.getUnits().remove(unit);
                } else {
                    //we have a definition and the return type does not match
                    // e.g., Integer[] l1 = Integer: int[] method();
                    // l1 != return type method()
                    //thus, we need to add new local
                    // int[] newLocal = invokeExpr()
                    // l1 = boxingOfArray(newLocal)
                    //FIXME: test this new code
                    Local newLocal = localGenerator.generateLocal(typeOfRightSide);
                    AssignStmt stmt = Jimple.v().newAssignStmt(newLocal, invokeExpr);
                    body.getUnits().insertBefore(stmt, insertBefore);

                    insertBefore = stmt;
                    //do Boxing of new (Array)Local
                    Local boxedArray = boxArray(newLocal, stmt, body, localGenerator);
                    AssignStmt assignBoxedArrayToOrgReferen = Jimple.v().newAssignStmt(definitionStmt.getLeftOp(), boxedArray);


                    body.getUnits().insertAfter(assignBoxedArrayToOrgReferen, stmt);
                    //remove the original definitionStmt
                    body.getUnits().remove(unit);
                }
            }
        }


        //unit has been removed (probably here)

        /* now check the arguments of the invoke expression, they may need to be unboxed ..
         * since we don't lift the ignored methods
         * they never need to be boxed
         */
        List<Type> methodParameterTypes = invokeExpr.getMethod().getParameterTypes();
        for (int i = 0; i < methodParameterTypes.size(); i++) {
            Type argType = invokeExpr.getArg(i).getType();
            Type parameterType = methodParameterTypes.get(i);
            boolean mustBeUnboxed = !BoxingTransformerUtility.isCompatible(argType, parameterType);

            if ((mustBeUnboxed) && !(invokeExpr.getArg(i) instanceof Constant)) {
                //we have to getUnBoxedType the argument
                //FIXME: this is new code, unbox of arrays is also handeld by unboxValue
                if (argType instanceof ArrayType || parameterType instanceof ArrayType) {
                    System.out.printf("here");
                }
                Local unboxedLocal = unboxValue(invokeExpr.getArg(i), insertBefore, body, originalLocalTypes, localGenerator);
                invokeExpr.setArg(i, unboxedLocal);
            }
        }


    }


    private List<Unit> assignConstantTo(Value l, Type originalTypeOfLocal, Constant constant, LocalGenerator localGenerator) {
        throw new RuntimeException("The more appropriate functions should have been called");
    }


    private List<Unit> assignTo(Value leftSide, final Type typeToUse1, Value value, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        Type typeToUse = typeToUse1;
        if (typeToUse == null || !(typeToUse instanceof PrimType)) {
            typeToUse = value.getType();
        }


        if (value instanceof NumericConstant) {
            if (leftSide instanceof Local)
                return assignConstantTo((Local) leftSide, typeToUse, (Constant) value, localGenerator);
            if (leftSide instanceof FieldRef)
                return assignConstantTo((FieldRef) leftSide, typeToUse, (Constant) value, localGenerator);

            if (leftSide instanceof ArrayRef)
                return assignConstantTo((ArrayRef) leftSide, typeToUse, (Constant) value, localGenerator);
        }
        if (value instanceof Local) {
            List<Unit> newAssign = new ArrayList<>();
            newAssign.add(assignLocalTo(leftSide, (Local) value, originalLocalTypes));
            return newAssign;
        }
        throw new RuntimeException("The more appropriate functions should have been called");
    }

    private List<Unit> assignConstantTo(Local leftSide, Type originalTypeOfLocal, Constant constant, LocalGenerator localGenerator) {
        List<Unit> newAssignmentStmt = new ArrayList<>();

        SootClass valuesBoxedClass = ((RefType) BoxingTransformerUtility.getBoxedType(originalTypeOfLocal)).getSootClass();

        List<Unit> createdStmts = createNewStmtForBoxedType(valuesBoxedClass, originalTypeOfLocal, leftSide, constant);

        //do not call value of, since in this method caching and arrays are involved for easier pts I use the constructor
        // SootMethod methodToCall = valuesBoxedClass.getMethod(valuesBoxedClass.getName() + " valueOf(" + originalType.getEscapedName() + ")");
      /*  SootMethod methodToCall = valuesBoxedClass.getMethod("void <init>(" + originalTypeOfLocal.getEscapedName() + ")");

        List<Value> args = new LinkedList<Value>();
        if (methodToCall.getParameterCount() > 0) {
            for (Type tp : methodToCall.getParameterTypes()) {
                args.add(constant);
            }
        }


        Expr newExpr = Jimple.v().newNewExpr(RefType.v(valuesBoxedClass));
        Stmt assignStmt = Jimple.v().newAssignStmt((Local) leftSide, newExpr);
        newAssignmentStmt.add(assignStmt);

        InvokeExpr newSpecialInvokeExpr = Jimple.v().newSpecialInvokeExpr((Local) leftSide, methodToCall.makeRef(), args);
        Stmt invokeStmt = Jimple.v().newInvokeStmt(newSpecialInvokeExpr);
        newAssignmentStmt.add(invokeStmt);*/

        newAssignmentStmt.addAll(createdStmts);
        //InvokeExpr invokeExpr = Jimple.v().newSpecialInvokeExpr((Local) leftSide, methodToCall.makeRef(), args);
        //newAssignmentStmt.add((Jimple.v().newAssignStmt(leftSide, invokeExpr)));
        return newAssignmentStmt;

    }

    private List<Unit> assignConstantTo(FieldRef leftSide, Type originalTypeOfField, Constant constant, LocalGenerator localGenerator) {
        List<Unit> newAssignmentStmt = new ArrayList<>();

        SootClass valuesBoxedClass = ((RefType) BoxingTransformerUtility.getBoxedType(originalTypeOfField)).getSootClass();


        // field a = 42
        // transform to
        // Integer i = Interger(42);
        // field a = i;
        // for this to work
        Local base = localGenerator.generateLocal(BoxingTransformerUtility.getBoxedType(originalTypeOfField));

        List<Unit> createdStmts = createNewStmtForBoxedType(valuesBoxedClass, originalTypeOfField, base, constant);

        //do not call value of, since in this method caching and arrays are involved for easier pts I use the constructor
        // SootMethod methodToCall = valuesBoxedClass.getMethod(valuesBoxedClass.getName() + " valueOf(" + originalType.getEscapedName() + ")");
       /* SootMethod methodToCall = valuesBoxedClass.getMethod("void <init>(" + originalTypeOfField.getEscapedName() + ")");

        List<Value> args = new LinkedList<Value>();
        if (methodToCall.getParameterCount() > 0) {
            for (Type tp : methodToCall.getParameterTypes()) {
                args.add(constant);
            }
        }
        Expr newExpr = Jimple.v().newNewExpr(RefType.v(valuesBoxedClass));
        Stmt assignStmt = Jimple.v().newAssignStmt(base, newExpr);
        newAssignmentStmt.add(assignStmt);

        InvokeExpr newSpecialInvokeExpr = Jimple.v().newSpecialInvokeExpr(base, methodToCall.makeRef(), args);
        Stmt invokeStmt = Jimple.v().newInvokeStmt(newSpecialInvokeExpr);
        newAssignmentStmt.add(invokeStmt);*/


        newAssignmentStmt.addAll(createdStmts);
        // InvokeExpr invokeExpr = Jimple.v().newSpecialInvokeExpr(base, methodToCall.makeRef(), args);
        // newAssignmentStmt.add(Jimple.v().newAssignStmt(base, invokeExpr));
        newAssignmentStmt.add(Jimple.v().newAssignStmt(leftSide, base));
        return newAssignmentStmt;

    }

    private List<Unit> assignConstantTo(ArrayRef leftSide, final Type originalTypeOfField, Constant constant, LocalGenerator localGenerator) {
        List<Unit> newAssignmentStmt = new ArrayList<>();


        // array[i]= 42
        // transform to
        // Integer i2 = Interger(42);
        // array[i] = i2;
        // for this to work
        Local base = localGenerator.generateLocal(BoxingTransformerUtility.getBoxedType(originalTypeOfField));

        SootClass valuesBoxedClass = ((RefType) BoxingTransformerUtility.getBoxedType(originalTypeOfField)).getSootClass();
        List<Unit> createdStmts = createNewStmtForBoxedType(valuesBoxedClass, originalTypeOfField, base, constant);

        newAssignmentStmt.addAll(createdStmts);
        newAssignmentStmt.add(Jimple.v().newAssignStmt(leftSide, base));
        return newAssignmentStmt;

    }


    private Unit assignLocalTo(Value leftSide, Local rightSide, HashMap<Value, Type> originalLocalTypes) {
        return Jimple.v().newAssignStmt(leftSide, rightSide);
    }


    private void handleUnboxingForBinaryExpression(Unit unit, BinopExpr binopExpr, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {
        Value leftValue = binopExpr.getOp1();
        Value righValue = binopExpr.getOp2();

        //we work on  object references, thus no unboxing
        if (leftValue instanceof NullConstant || righValue instanceof NullConstant) {
            return;
        }

        //if both types are not primitive originally then we work on object reference comparision
        boolean leftValueNeedsUnboxing = originalLocalTypes.get(leftValue) instanceof PrimType | leftValue instanceof Constant;
        boolean rightValueNeedsUnboxing = originalLocalTypes.get(righValue) instanceof PrimType | righValue instanceof Constant;
        if (!leftValueNeedsUnboxing && !rightValueNeedsUnboxing) {
            return;
        }


        //We work on object references
        if ((leftValue.getType() instanceof ArrayType) && (righValue.getType() instanceof ArrayType)) {
            return;
        }

        Local leftLocal = unboxValue(leftValue, unit, body, originalLocalTypes, localGenerator);
        if (leftLocal != null)
            binopExpr.setOp1(leftLocal);

        Local rightLocal = unboxValue(righValue, unit, body, originalLocalTypes, localGenerator);
        if (rightLocal != null)
            binopExpr.setOp2(rightLocal);


    }


    private Local unboxValue(Value value, Unit unitToInsertBefore, Body body, HashMap<Value, Type> originalLocalTypes, LocalGenerator localGenerator) {

        return unboxValue(value, originalLocalTypes.get(value), unitToInsertBefore, body, localGenerator);

    }


    private Local unboxValue(Value value, Type targetType, Unit unitToInsertBefore, Body body, LocalGenerator localGenerator) {
        Local createdLocal;
        List<Unit> appendList = new ArrayList<>();
        if (value instanceof Constant) {
            return null;
        }
        if (targetType == null) {
            return null;
        }

        if (value.getType() instanceof ArrayType) {
            createdLocal = unboxArray(value, appendList, localGenerator);
        } else {
            createdLocal = unboxSimpleLocal(value, targetType, appendList, localGenerator);
        }
        if (createdLocal != null) {
            body.getUnits().insertBefore(appendList, unitToInsertBefore);
        }
        return createdLocal;
    }


    private Local unboxSimpleLocal(Value value, Type targetType, List<Unit> appendToList, LocalGenerator localGenerator) {
        Local createdLocal = null;
        if (value instanceof Constant) {
            return null;
        }

        if ((value instanceof Local) && (BoxingTransformerUtility.isTypeToModify(targetType))) {
            Local l = (Local) value;
            Type primTypeForUnboxing = targetType;
            //create new Local with primtive Type
            createdLocal = localGenerator.generateLocal(primTypeForUnboxing);
            //getUnBoxedType the value
            SootClass valuesBoxedClass = ((RefType) l.getType()).getSootClass();

            ArrayList<Type> parameterTypes = new ArrayList<>();
            SootMethod methodToCall = getMethodOnSnapshot(valuesBoxedClass, primTypeForUnboxing.getEscapedName() + "Value", parameterTypes, primTypeForUnboxing);
            //   SootMethod methodToCall = valuesBoxedClass.getMethod(primTypeForUnboxing.getEscapedName() + " " + primTypeForUnboxing.getEscapedName() + "Value()");

            InvokeExpr unBoxinginvokeExpr = Jimple.v().newVirtualInvokeExpr((Local) value, methodToCall.makeRef());
            Stmt unboxingAssignmentStmt = Jimple.v().newAssignStmt(createdLocal, unBoxinginvokeExpr);
            appendToList.add(unboxingAssignmentStmt);

        }
        return createdLocal;
    }


    /*
        public int[] unboxArray(Integer[] orgarray){
        int[] ar = new int[orgarray.length];
        for(int i = 0; i<orgarray.length;i++){
            ar[i] = orgarray[i].intValue();
        }
        return ar;

        // in jimple
         $i0 = lengthof r1;

        r2 = newarray (int)[$i0];

        i3 = 0;

     label1:
        $i1 = lengthof r1;

        if i3 >= $i1 goto label2;

        $r3 = r1[i3];

        $i2 = virtualinvoke $r3.<java.lang.Integer: int intValue()>();

        r2[i3] = $i2;

        i3 = i3 + 1;

        goto label1;

     label2:
        return r2;

    }
     */
    // para is Boxed array, e.g. Integer[]
    private Local unboxArray(Value orgArray, List<Unit> listToAppend, LocalGenerator localGenerator) {
        Local targetUnboxedArray;
        if (!(orgArray.getType() instanceof ArrayType)) {
            return null;
        }

        List<Unit> newCreateStmts = new ArrayList<>();
        //new primitve array local
        ArrayType orgArrayType = (ArrayType) orgArray.getType();
        ArrayType unboxedArrayType = (ArrayType) BoxingTransformerUtility.getUnBoxedType(orgArrayType);

        //create local for length
        Local lengthLocal = localGenerator.generateLocal(IntType.v());
        Expr length = Jimple.v().newLengthExpr(orgArray);
        Stmt assignLength = Jimple.v().newAssignStmt(lengthLocal, length);

        newCreateStmts.add(assignLength);

        //create Local for primitive array
        targetUnboxedArray = localGenerator.generateLocal(unboxedArrayType);
        Expr newArrayExpr = Jimple.v().newNewArrayExpr(unboxedArrayType, lengthLocal);
        Stmt arrayAssign = Jimple.v().newAssignStmt(targetUnboxedArray, newArrayExpr);
        newCreateStmts.add(arrayAssign);

        //create the loop counter
        Local counter = localGenerator.generateLocal(IntType.v());
        Constant zero = IntConstant.v(0);
        Stmt initCounter = Jimple.v().newAssignStmt(counter, zero);
        newCreateStmts.add(initCounter);

        //create the loop

        //loop end
        Stmt endStmt = Jimple.v().newNopStmt();

        Expr condition = Jimple.v().newGeExpr(counter, lengthLocal);
        Stmt ifStmt = Jimple.v().newIfStmt(condition, endStmt);
        newCreateStmts.add(ifStmt);

        //array assignment
        Local r3 = localGenerator.generateLocal(orgArrayType.baseType);
        ArrayRef refOrgArray = Jimple.v().newArrayRef(orgArray, counter);
        Stmt assingOrgArry = Jimple.v().newAssignStmt(r3, refOrgArray);
        newCreateStmts.add(assingOrgArry);

        //local for getUnBoxedType arrayElement
        Local unboxedArrayElement = unboxSimpleLocal(r3, unboxedArrayType.baseType, newCreateStmts, localGenerator);

        //assign the unboxed value to the new unboxed array
        Stmt assignUnboxedToTargetArray = Jimple.v().newAssignStmt(targetUnboxedArray, unboxedArrayElement);
        newCreateStmts.add(assignUnboxedToTargetArray);

        //increase counter
        Expr incCounterExpr = Jimple.v().newAddExpr(counter, IntConstant.v(1));
        Stmt incCounter = Jimple.v().newAssignStmt(counter, incCounterExpr);
        newCreateStmts.add(incCounter);
        //goto start of loop
        Stmt gotoStmt = Jimple.v().newGotoStmt(ifStmt);
        newCreateStmts.add(gotoStmt);

        newCreateStmts.add(endStmt);

        listToAppend.addAll(newCreateStmts);

        return targetUnboxedArray;

    }


    /*
        public Integer[] boxArray(int[] orgarray){
        Integer[] ar = new Integer[orgarray.length];
        for(int i=0;i<orgarray.length;i++){
            ar[i] = new Integer(orgarray[i]);
        }
        return ar;


        //in jimple
         $i0 = lengthof r1;

        r2 = newarray (java.lang.Integer)[$i0];

        i3 = 0;

     label1:
        $i1 = lengthof r1;

        if i3 >= $i1 goto label2;

        $r3 = new java.lang.Integer;

        $i2 = r1[i3];

        specialinvoke $r3.<java.lang.Integer: void <init>(int)>($i2);

        r2[i3] = $r3;

        i3 = i3 + 1;

        goto label1;

     label2:
        return r2;
    }
     */
    private Local boxArray(Value orgArray, Unit unitToInsertBefore, Body body, LocalGenerator localGenerator) {

        Local targetBoxedArray;
        if (!(orgArray.getType() instanceof ArrayType)) {
            return null;
        }

        List<Unit> newCreateStmts = new ArrayList<>();
        //new lifted array local
        ArrayType orgArrayType = (ArrayType) orgArray.getType();
        ArrayType liftedArrayType = (ArrayType) BoxingTransformerUtility.getBoxedType(orgArrayType);

        //create local for length
        Local lengthLocal = localGenerator.generateLocal(IntType.v());
        Expr length = Jimple.v().newLengthExpr(orgArray);
        Stmt assignLength = Jimple.v().newAssignStmt(lengthLocal, length);

        newCreateStmts.add(assignLength);

        //create Local for lifted array
        targetBoxedArray = localGenerator.generateLocal(liftedArrayType);
        Expr newArrayExpr = Jimple.v().newNewArrayExpr(liftedArrayType, lengthLocal);
        Stmt arrayAssign = Jimple.v().newAssignStmt(targetBoxedArray, newArrayExpr);
        newCreateStmts.add(arrayAssign);

        //create the loop counter
        Local counter = localGenerator.generateLocal(IntType.v());
        Constant zero = IntConstant.v(0);
        Stmt initCounter = Jimple.v().newAssignStmt(counter, zero);
        newCreateStmts.add(initCounter);

        //create the loop

        //loop end
        Stmt endStmt = Jimple.v().newNopStmt();

        Expr condition = Jimple.v().newGeExpr(counter, lengthLocal);
        Stmt ifStmt = Jimple.v().newIfStmt(condition, endStmt);
        newCreateStmts.add(ifStmt);

        //array assignment
        Local r3 = localGenerator.generateLocal(liftedArrayType);
        ArrayRef refOrgArray = Jimple.v().newArrayRef(orgArray, counter);
        Local i2 = localGenerator.generateLocal(orgArrayType.baseType);
        Stmt assignArrayElementToi2 = Jimple.v().newAssignStmt(i2, refOrgArray);
        newCreateStmts.add(assignArrayElementToi2);
        //and the new expression
        List<Unit> newUnits = createNewStmtForBoxedType(((RefType) liftedArrayType.baseType).getSootClass(), orgArrayType.baseType, r3, i2);

        newCreateStmts.addAll(newUnits);


        //increase counter
        Expr incCounterExpr = Jimple.v().newAddExpr(counter, IntConstant.v(1));
        Stmt incCounter = Jimple.v().newAssignStmt(counter, incCounterExpr);
        newCreateStmts.add(incCounter);
        //goto start of loop
        Stmt gotoStmt = Jimple.v().newGotoStmt(ifStmt);
        newCreateStmts.add(gotoStmt);

        newCreateStmts.add(endStmt);

        body.getUnits().insertBefore(newCreateStmts, unitToInsertBefore);

        return targetBoxedArray;

    }



    /*
      lifts the given type to an appropriate boxedType if a primitive type is given
      otherwise the original type is returned

      @param
     * @return the boxedType or the original type
     *//*
    private Type getBoxedType(Type type) {
        Type liftedType = type;
        if (type instanceof PrimType) {
            SootPrimitivesEnum typeEnum = SootPrimitivesEnum.valueOf(type.getClass().getSimpleName());
            switch (typeEnum) {
                case CharType:
                    liftedType = RefType.v("java.lang.Character", Optional.of("java.base"));
                    break;
                case BooleanType:
                    liftedType = RefType.v("java.lang.Boolean", Optional.of("java.base"));
                    break;
                case ShortType:
                case IntType:
                case FloatType:
                case LongType:
                case DoubleType:
                case ByteType:
                    liftedType = RefType.v("java.lang.Number", Optional.of("java.base"));
                    break;
                default:
                    throw new RuntimeException("Unexpected Primitive Type");

            }


        }

        return liftedType;
    }*/


    private SootMethod getMethodOnSnapshot(SootClass sootClass, String name, List<Type> parameterTypes, Type returnType) {
        for (SootMethod method : sootClass.getMethodsSnapshot()) {
            if (method.getName().equals(name) && parameterTypes.equals(method.getParameterTypes())
                    && returnType.equals(method.getReturnType())) {
                return method;
            }
        }


        throw new RuntimeException("Class " + sootClass.getName() + " doesn't have method " + name + "(" + parameterTypes + ")"
                + " : " + returnType);
    }


}
