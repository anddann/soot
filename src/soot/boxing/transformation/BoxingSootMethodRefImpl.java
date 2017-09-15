package soot.boxing.transformation;

import soot.*;
import soot.options.Options;
import soot.util.NumberedString;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by adann on 22.05.17.
 */
public class BoxingSootMethodRefImpl extends SootMethodRefImpl {
    private NumberedString originalSubSig = null;


    private BoxingSootMethodRefImpl(SootClass declaringClass, String name, List<Type> parameterTypes, Type returnType, boolean isStatic, List<Type> liftedParameter, Type liftedReturnType, NumberedString originalSubSig) {
        super(declaringClass, name, parameterTypes, returnType, isStatic);
        this.originalSubSig = originalSubSig;

        if (BoxingTransformerUtility.isMethodIgnored(this)) {
            this.liftedParameter = parameterTypes;
            this.liftedReturnType = returnType;
        } else {
            this.liftedReturnType = liftedReturnType;
            this.liftedParameter = liftedParameter;

        }

        super.setSubsig(Scene.v().getSubSigNumberer().findOrAdd(SootMethod.getSubSignature(name, this.liftedParameter, this.liftedReturnType)));
    }

    private final Type liftedReturnType;
    private final List<Type> liftedParameter;

    /**
     * this is the constructor to use, since we want to call functions before calling super .... :)
     *
     * @param declaringClass
     * @param name
     * @param parameterTypes
     * @param returnType
     * @param isStatic
     * @return
     */
    public static BoxingSootMethodRefImpl v(SootClass declaringClass, String name, List<Type> parameterTypes, Type returnType, boolean isStatic) {
        //create original subsig and store it
        NumberedString originalSubSignature = Scene.v().getSubSigNumberer().findOrAdd(
                SootMethod.getSubSignature(name, parameterTypes, returnType));
        // lift the types
        Type liftedReturnType = returnType;
        List<Type> liftedParameterTypes;

        liftedParameterTypes = new ArrayList<>(parameterTypes);

        liftedReturnType = BoxingTransformerUtility.getBoxedType(returnType);
        for (int i = 0; i < liftedParameterTypes.size(); i++) {
            liftedParameterTypes.set(i, BoxingTransformerUtility.getBoxedType(liftedParameterTypes.get(i)));

        }


        //call constructor with the lifted types
        return new BoxingSootMethodRefImpl(declaringClass, name, parameterTypes, returnType, isStatic, liftedParameterTypes, liftedReturnType, originalSubSignature);
    }

  /*  @Override
    public SootMethod resolve() {

        // for testing purpose (eigentlich sollte in BoxingBodyTransformation, die reference durch custom
        // referenz ausgetausch werden, die dies hier überschreibt
        SootMethod methodToReturn = null;
        try {
            methodToReturn = super.resolve(null);
            // a reference which has not been lifted up
        } catch (RuntimeException ex) {

            try {
                // add cases for dangling referencens
                this.returnType = BoxingTransformerUtility.getBoxedType(this.returnType);
                List<Type> orgParameter = this.parameterTypes;
                List<Type> boxedParam = new ArrayList<>(orgParameter);
                for (int i = 0; i < boxedParam.size(); i++) {

                    boxedParam.set(i, BoxingTransformerUtility.getBoxedType(boxedParam.get(i)));
                }
                this.parameterTypes = boxedParam;
                this.subsig = null;
                methodToReturn = resolve(null);

            } catch (RuntimeException e) {


                //has already been boxed, now look for the org method
                NumberedString orgSubSig = this.getSubSignature();
                Type orgReturn = this.returnType;
                List<Type> orgParameter = this.parameterTypes;

                Type unboxedReturnType = BoxingTransformerUtility.getUnBoxedType(orgReturn);
                List<Type> unboxedPrimPara = new ArrayList<>(orgParameter);
                for (int i = 0; i < unboxedPrimPara.size(); i++) {

                    unboxedPrimPara.set(i, BoxingTransformerUtility.getUnBoxedType(unboxedPrimPara.get(i)));
                }

                //anstatt diese hin zurück gehambel ändere einfach die subsignature
                // for array return or primitve the original value is not properly reset...
                NumberedString newSubSignature = Scene.v().getSubSigNumberer().findOrAdd(
                        SootMethod.getSubSignature(name, unboxedPrimPara, unboxedReturnType));
                this.subsig = newSubSignature;

                methodToReturn = resolve(null);
                this.subsig = orgSubSig;
 *//*           this.returnType = orgReturn;
            for (int i = 0; i < orgParameter.size(); i++) {
                if(orgParameter.get(i) instanceof ArrayType){
                    orgParameter.set(i,getBoxedType(orgParameter.get(i)));
                }
            }
            this.parameterTypes = orgParameter;
            this.subsig = null;*//*
            }
        }

        return methodToReturn;
    }*/


    public void liftTheReference() {
        super.setReturnType(this.liftedReturnType);
        super.setParameterTypes(this.liftedParameter);
        setSubsig(null);
    }

    @Override
    public SootMethod resolve() {
        SootMethod methodToReturn = null;
        try {

            //resolve with current (lifted) subSignature
            //FIXME: here use try resolve
            methodToReturn = super.tryResolve();
            if (methodToReturn == null)
                throw new RuntimeException("no method");
            //if phantom refs are allowed a method is created , we don't want it?


        } catch (RuntimeException ex) {
            //if it fails, the method has not been transformed/lifted
            //thus resolve with old Subsignature
            NumberedString current = super.getSubSignature();
            super.setSubsig(this.originalSubSig);


            methodToReturn = super.resolve();


            //reset to the current/lifted subsignature
            super.setSubsig(current);


        }

        // added here abstract and interface methods, also lift them
        if (declaringClass().isPhantom()
                || (Options.v().no_bodies_for_excluded()
                && Scene.v().isExcluded(declaringClass()) && !Scene.v()
                .getBasicClasses().contains(declaringClass().getName())) || !methodToReturn.isConcrete()) {
            //lift the method' signature
            //  methodToReturn.setParameterTypes(this.liftedParameter);
            //    methodToReturn.setReturnType(liftedReturnType);
            methodToReturn.setSignature(this.liftedParameter, this.liftedReturnType);
            /* this causes a crash
            * when transform public sun.text.normalizer.NormalizerImpl load
            * all primitive types are inferent to java.io.Serializable ??
             witout this the lifting of all types is correct
             *the reference is changed in the boxing transfomration anyway
             */
            // this.returnType = this.liftedReturnType;
            //  this.parameterTypes = this.liftedParameter;
            //the references are changed in the boxing transformation correctly
            //setze hier dann auch die SubSignature
            originalSubSig = Scene.v().getSubSigNumberer().findOrAdd(SootMethod.getSubSignature(super.name(), liftedParameter, liftedReturnType));
        }


        return methodToReturn;
    }
}
