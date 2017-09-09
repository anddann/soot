package soot.boxing.transformation;

import com.google.common.base.Optional;
import soot.*;
import soot.options.Options;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;

/**
 * Created by adann on 18.05.17.
 */
//FIXME: adapt to Scene, currently only ModuleScene
public class BoxingTransformerUtility {
    private BoxingTransformerUtility() {

    }


    /**
     * Changes the primitive types of the method and its body to BoxedTypes
     * Changes the method's parameter, the return type, the locals
     *
     * @param method the method whose signature should be adaapted
     * @return returns true if method is already defined
     */
    //FIXME: also adapt the locals for parameters here
    public synchronized static SootMethod adaptMethodSignature(Body body) {
        SootMethod method = body.getMethod();

        boolean methodHasBeenAdapted = false;
        //check if class is ignored
        if (BoxingTransformerUtility.isMethodIgnored(method))
            return method;


        //change the method's signature to  boxedType

        //parameter type
        List<Type> parameterTypes = method.getParameterTypes();
        List<Type> boxedParameterTypes = new ArrayList<>();
        boxedParameterTypes.addAll(parameterTypes);
        for (int i = 0; i < boxedParameterTypes.size(); i++) {
            Type t = getBoxedType(boxedParameterTypes.get(i));
            methodHasBeenAdapted = methodHasBeenAdapted | !(t.equals(boxedParameterTypes.get(i)));
            boxedParameterTypes.set(i, t);
        }




        //return type
        Type returnType = getBoxedType(method.getReturnType());

        methodHasBeenAdapted = methodHasBeenAdapted | !(returnType.equals(method.getReturnType()));

        // check if methodsignature already exists before adapting it
        try {
            SootMethod checkMethod = method.getDeclaringClass().getMethod(method.getName(), boxedParameterTypes, returnType);
            if (checkMethod != null) {

                if (Options.v().allow_phantom_refs() && methodHasBeenAdapted) {
                    //remove the method
                    //  checkMethod.getDeclaringClass().removeMethod(checkMethod);
                    //  checkMethod.setActiveBody(method.getActiveBody());

                    //anderes rum remove this and set this bod
                    checkMethod.releaseActiveBody();
                    checkMethod.setActiveBody(body);
                    //method.getDeclaringClass().removeMethod(method);
                    //delete the old method
                    body.setMethod(checkMethod);
                    // method.getDeclaringClass().removeMethod(method);
                    return checkMethod;
                }
                return null;
            }
        } catch (RuntimeException ex) {
            //the method is not yet definied, thus we can continue
        }
        method.setSignature(boxedParameterTypes, returnType);

        //  method.setParameterTypes(boxedParameterTypes);


        // box return type
        // method.setReturnType(returnType);


        return method;
    }


    /**
     * lifts the given type to an appropriate boxedType if a primitive type is given
     * otherwise the original type is returned
     *
     * @param type the type to lift
     * @return the boxedType or the original type
     */
    public static Type getBoxedType(Type type) {
        Type liftedType = type;
        Type typeToCheck = type;
        if (typeToCheck instanceof ArrayType) {
            typeToCheck = ((ArrayType) type).baseType;
        }
        if (typeToCheck instanceof PrimType) {
            liftedType = ((PrimType) typeToCheck).boxedType();
           /* BoxingTransformerUtility.SootPrimitivesEnum typeEnum = BoxingTransformerUtility.SootPrimitivesEnum.valueOf(typeToCheck.getClass().getSimpleName());
            switch (typeEnum) {
                case CharType:
                    liftedType = RefType.v("java.lang.Character", Optional.of("java.base"));
                    break;
                case BooleanType:
                    liftedType = RefType.v("java.lang.Boolean", Optional.of("java.base"));
                    break;
                case ShortType:
                    liftedType = RefType.v("java.lang.Short", Optional.of("java.base"));
                    break;
                case IntType:
                    liftedType = RefType.v("java.lang.Integer", Optional.of("java.base"));
                    break;
                case FloatType:
                    liftedType = RefType.v("java.lang.Float", Optional.of("java.base"));
                    break;
                case LongType:
                    liftedType = RefType.v("java.lang.Long", Optional.of("java.base"));
                    break;
                case DoubleType:
                    liftedType = RefType.v("java.lang.Double", Optional.of("java.base"));
                    break;
                case ByteType:
                    liftedType = RefType.v("java.lang.Byte", Optional.of("java.base"));
                    break;
                default:
                    throw new RuntimeException("Unexpected Primitive Type");

            }
            */
        }
        if (type instanceof ArrayType && typeToCheck instanceof PrimType) {

            return ArrayType.v(liftedType, ((ArrayType) type).numDimensions);
        }

        return liftedType;
    }

    public static Type getUnBoxedType(final Type type) {
        Type liftedType = type;
        Type typeToCheck = type;
        if (typeToCheck instanceof ArrayType) {
            typeToCheck = ((ArrayType) type).baseType;
        }
        if (typeToCheck == ModuleRefType.v("java.lang.Character", Optional.of("java.base"))) {
            liftedType = CharType.v();
        }
        if (typeToCheck == ModuleRefType.v("java.lang.Boolean", Optional.of("java.base"))) {
            liftedType = BooleanType.v();
        }
        if (typeToCheck == ModuleRefType.v("java.lang.Short", Optional.of("java.base"))) {
            liftedType = ShortType.v();
        }
        if (typeToCheck == ModuleRefType.v("java.lang.Integer", Optional.of("java.base"))) {
            liftedType = IntType.v();
        }

        if (typeToCheck == ModuleRefType.v("java.lang.Float", Optional.of("java.base"))) {
            liftedType = FloatType.v();
        }

        if (typeToCheck == ModuleRefType.v("java.lang.Long", Optional.of("java.base"))) {
            liftedType = LongType.v();
        }


        if (typeToCheck == ModuleRefType.v("java.lang.Double", Optional.of("java.base"))) {
            liftedType = DoubleType.v();
        }


        if (typeToCheck == ModuleRefType.v("java.lang.Byte", Optional.of("java.base"))) {
            liftedType = ByteType.v();
        }
        if (type instanceof ArrayType && liftedType instanceof PrimType) {
            ArrayType newArray = ArrayType.v(liftedType, ((ArrayType) type).numDimensions);
            //   IMHO: this is already covered by the previous constructor call
            // newArray.baseType = liftedType;
            return newArray;

        }

        return liftedType;

    }


    public static boolean SootClassIsIgnored(SootClass declaringClass) {
        String klassName = declaringClass.getName();

        if (klassName.contains("$")) {
            klassName = klassName.substring(0, klassName.indexOf('$'));
        }

        if (!ignoredClasses.contains(klassName))
            return false;
        else if ((declaringClass.isInnerClass()) && (!ignoredClasses.contains(declaringClass.getOuterClass().getName()))) {
            return false;
        }


        return true;
    }


    public static boolean isMethodIgnored(SootMethod method) {

        if (method.getDeclaringClass().getName().equalsIgnoreCase("java.lang.String") && method.getName().equalsIgnoreCase("charAt"))
            return true;

        if (!BoxingTransformerUtility.SootClassIsIgnored(method.getDeclaringClass())) {
            return false;
        }

        return (method.isConstructor() || !method.isStatic() || method.isStaticInitializer() || method.getName().equals("valueOf") || method.getName().contains("parse"));


    }

    public static boolean isMethodIgnored(SootClass klass, String methodName, boolean isStatic) {

        if (!BoxingTransformerUtility.SootClassIsIgnored(klass)) {
            return false;
        }

        return (methodName.contains("<init>") || methodName.contains("<cinit>") || !isStatic || methodName.equals("valueOf") || methodName.contains("parse"));

    }

    public static boolean isMethodIgnored(SootMethodRef methodRef) {
        if (!BoxingTransformerUtility.SootClassIsIgnored(methodRef.declaringClass())) {
            return false;
        }
        if (methodRef.declaringClass().equals("java.lang.String") && methodRef.name().equalsIgnoreCase("charAt"))
            return true;

        return isMethodIgnored(methodRef.declaringClass(), methodRef.name(), methodRef.isStatic());


    }


    public static boolean isFieldIgnored(SootField field) {
        return BoxingTransformerUtility.SootClassIsIgnored(field.getDeclaringClass());
    }


    public static boolean isCompatible(SootClass actual, SootClass expected) {
        SootClass act = actual;

        while (true) {
            // Do we have a direct match?
            if (act.getName().equals(expected.getName()))
                return true;

            // If we expect an interface, the current class might implement it
            if (expected.isInterface())
                for (SootClass intf : act.getInterfaces())
                    if (intf.getName().equals(expected.getName())) {
                        return true;
                    }
            // If we cannot continue our search further up the hierarchy, the
            // two types are incompatible
            if (!act.hasSuperclass())
                return false;
            act = act.getSuperclass();
        }
    }

    public static boolean isCompatible(Type actual, Type expected) {

        if (actual == expected)
            return true;

        if (actual == NullType.v())
            return true;

        //FIXME: currently we check only for primitive types
        if ((actual instanceof PrimType) && (expected instanceof PrimType)) {
            //return  getBoxedType(actual) == getBoxedType(expected);
            boolean comp = (actual instanceof IntegerType) && (expected instanceof IntegerType);
            return comp;
            //boolean comp = AugHierarchy.ancestor_(expected, actual) || AugHierarchy.ancestor_(actual, expected);
            //return comp;
        }
        if ((actual instanceof RefType) && (expected instanceof RefType))
            return BoxingTransformerUtility.isCompatible(((RefType) actual).getSootClass(), ((RefType) expected).getSootClass());

        return false;
    }

    public static boolean isTypeToModify(final Type type) {
        Type typeToCheck = type;
        if (typeToCheck instanceof ArrayType) {
            typeToCheck = ((ArrayType) typeToCheck).baseType;
        }
        return (typeToCheck instanceof PrimType);
    }


    private static final HashSet<String> ignoredClasses = new HashSet<>(Arrays.asList("java.lang.Number", "java.lang.Boolean", "java.lang.Character", "java.lang.Integer", "java.lang.Double", "java.lang.Long", "java.lang.Float", "java.lang.Byte", "java.lang.Short"));

    public enum SootPrimitivesEnum {
        CharType, BooleanType, ShortType, IntType, FloatType, LongType, DoubleType, ByteType
    }
}
