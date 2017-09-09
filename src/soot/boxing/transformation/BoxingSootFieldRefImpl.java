package soot.boxing.transformation;

import soot.*;

/**
 * Created by adann on 22.05.17.
 */

//FIXME; I don't see anaother options instead of code duplication of AbstractSootFieldRef
public class BoxingSootFieldRefImpl extends AbstractSootFieldRef {


    public Type getLiftedType() {
        return liftedType;
    }

    private Type liftedType = null;


    private BoxingSootFieldRefImpl(SootClass declaringClass, String name, Type type, boolean isStatic, Type liftedType) {
        super(declaringClass, name, type, isStatic);
        this.liftedType = liftedType;
    }

    public void liftTheReference() {
        super.setType(this.liftedType);
    }

    /**
     * this is the constructor to use, since we want to call functions before calling super .... :)
     *
     * @param declaringClass
     * @param name
     * @param type
     * @param isStatic
     * @return
     */
    public static BoxingSootFieldRefImpl v(SootClass declaringClass, String name, Type type, boolean isStatic) {
        //create original subsig and store it
        Type originalType = type;
        // lift the types
        Type liftedType = type;
        if (!BoxingTransformerUtility.SootClassIsIgnored(declaringClass)) {
            liftedType = BoxingTransformerUtility.getBoxedType(type);

        }
        //call constructor with the lifted types
        return new BoxingSootFieldRefImpl(declaringClass, name, originalType, isStatic, liftedType);
    }

    /**
     * The order here is the opposite to
     * {@link BoxingSootMethodRefImpl} because the field is used to derive type information
     * if we lift it before the previous Jimple Phases fail
     *
     * @return
     */
    @Override
    public SootField resolve() {
        SootField fieldToReturn;
        try {
            //resolve with old type
            fieldToReturn = super.resolve();
            if (fieldToReturn == null)
                throw new RuntimeException("no field");
        } catch (RuntimeException ex) {
            //if it fails, the method has  been transformed/lifted
            //thus resolve with new lifted type
            super.setType(this.liftedType);
            fieldToReturn = super.resolve();


        }
        return fieldToReturn;
    }
}
