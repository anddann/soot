package soot.dexpler.instructions;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2012 Michael Markert, Frank Hartmann
 *
 * (c) 2012 University of Luxembourg - Interdisciplinary Centre for
 * Security Reliability and Trust (SnT) - All rights reserved
 * Alexandre Bartel
 *
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

import static soot.dexpler.Util.dottedClassName;
import static soot.dexpler.Util.isFloatLike;

import java.util.HashSet;
import java.util.Set;

import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction21c;
import org.jf.dexlib2.iface.instruction.formats.Instruction22c;
import org.jf.dexlib2.iface.instruction.formats.Instruction23x;
import org.jf.dexlib2.iface.reference.FieldReference;

import soot.*;
import soot.dexpler.DexBody;
import soot.dexpler.DexType;
import soot.jimple.AssignStmt;
import soot.jimple.ConcreteRef;
import soot.jimple.Jimple;
import soot.options.Options;

public abstract class FieldInstruction extends DexlibAbstractInstruction {

    private Scene myScene;
    private SootResolver mySootResolver;

    public FieldInstruction(Instruction instruction, int codeAdress, Options myOptions, Scene myScene, SootResolver mySootResolver) {
        super(instruction, codeAdress, myOptions);
        this.myScene = myScene;
        this.mySootResolver = mySootResolver;
    }

    /**
     * Return a static SootFieldRef for a dexlib FieldReference.
     *
     * @param item the dexlib FieldReference.
     */
    protected SootFieldRef getStaticSootFieldRef(FieldReference fref) {
        return getSootFieldRef(fref, true);
    }

    /**
     * Return a SootFieldRef for a dexlib FieldReference.
     *
     * @param item the dexlib FieldReference.
     */
    protected SootFieldRef getSootFieldRef(FieldReference fref) {
        return getSootFieldRef(fref, false);
    }

    /**
     * Return a SootFieldRef for a dexlib FieldReference.
     *
     * @param item     the dexlib FieldReference.
     * @param isStatic if the FieldRef should be static
     */
    private SootFieldRef getSootFieldRef(FieldReference fref, boolean isStatic) {
        String className = dottedClassName(fref.getDefiningClass(), myScene);
        SootClass sc = mySootResolver.makeClassRef(className);
        return myScene.makeFieldRef(sc, fref.getName(), DexType.toSoot(fref.getType()), isStatic);
    }

    /**
     * Check if the field type equals the type of the value that will be stored in the field. A cast expression has to be
     * introduced for the unequal case.
     *
     * @return assignment statement which hold a cast or not depending on the types of the operation
     */
    protected AssignStmt getAssignStmt(DexBody body, Local sourceValue, ConcreteRef instanceField) {
        AssignStmt assign;
        // Type targetType = getTargetType(body);
        // if(targetType != UnknownType.v() && targetType != sourceValue.getType() && ! (targetType instanceof RefType)) {
        // CastExpr castExpr = Jimple.newCastExpr(sourceValue, targetType);
        // Local local = body.generateLocal(targetType);
        // assign = Jimple.newAssignStmt(local, castExpr);
        // body.add(assign);
        // beginUnit = assign;
        // assign = Jimple.newAssignStmt(instanceField, local);
        // }
        // else {
        assign = Jimple.newAssignStmt(instanceField, sourceValue);
        // }
        return assign;
    }

    @Override
    boolean isUsedAsFloatingPoint(DexBody body, int register) {
        return sourceRegister() == register && isFloatLike(getTargetType(body), myScene);
    }

    /**
     * Return the source register for this instruction.
     */
    private int sourceRegister() {
        // I hate smali's API ..
        if (instruction instanceof Instruction23x) {
            return ((Instruction23x) instruction).getRegisterA();
        } else if (instruction instanceof Instruction22c) {
            return ((Instruction22c) instruction).getRegisterA();
        } else if (instruction instanceof Instruction21c) {
            return ((Instruction21c) instruction).getRegisterA();
        } else {
            throw new RuntimeException("Instruction is not a instance, array or static op");
        }
    }

    /**
     * Return the target type for put instructions.
     * <p>
     * Putters should override this.
     *
     * @param body the body containing this instruction
     */
    protected Type getTargetType(DexBody body) {
        return myScene.getPrimTypeCollector().getUnknownType();
    }

    @Override
    public Set<Type> introducedTypes() {
        Set<Type> types = new HashSet<Type>();
        // Aput instructions don't have references
        if (!(instruction instanceof ReferenceInstruction)) {
            return types;
        }

        ReferenceInstruction i = (ReferenceInstruction) instruction;

        FieldReference field = (FieldReference) i.getReference();

        types.add(DexType.toSoot(field.getType()));
        types.add(DexType.toSoot(field.getDefiningClass()));
        return types;
    }
}
