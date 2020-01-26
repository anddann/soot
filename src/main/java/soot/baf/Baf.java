package soot.baf;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1999 Patrick Lam, Patrick Pominville and Raja Vallee-Rai
 * Copyright (C) 2004 Ondrej Lhotak
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

import com.google.inject.Inject;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import soot.*;
import soot.baf.internal.BAddInst;
import soot.baf.internal.BAndInst;
import soot.baf.internal.BArrayLengthInst;
import soot.baf.internal.BArrayReadInst;
import soot.baf.internal.BArrayWriteInst;
import soot.baf.internal.BCmpInst;
import soot.baf.internal.BCmpgInst;
import soot.baf.internal.BCmplInst;
import soot.baf.internal.BDivInst;
import soot.baf.internal.BDup1Inst;
import soot.baf.internal.BDup1_x1Inst;
import soot.baf.internal.BDup1_x2Inst;
import soot.baf.internal.BDup2Inst;
import soot.baf.internal.BDup2_x1Inst;
import soot.baf.internal.BDup2_x2Inst;
import soot.baf.internal.BDynamicInvokeInst;
import soot.baf.internal.BEnterMonitorInst;
import soot.baf.internal.BExitMonitorInst;
import soot.baf.internal.BFieldGetInst;
import soot.baf.internal.BFieldPutInst;
import soot.baf.internal.BGotoInst;
import soot.baf.internal.BIdentityInst;
import soot.baf.internal.BIfCmpEqInst;
import soot.baf.internal.BIfCmpGeInst;
import soot.baf.internal.BIfCmpGtInst;
import soot.baf.internal.BIfCmpLeInst;
import soot.baf.internal.BIfCmpLtInst;
import soot.baf.internal.BIfCmpNeInst;
import soot.baf.internal.BIfEqInst;
import soot.baf.internal.BIfGeInst;
import soot.baf.internal.BIfGtInst;
import soot.baf.internal.BIfLeInst;
import soot.baf.internal.BIfLtInst;
import soot.baf.internal.BIfNeInst;
import soot.baf.internal.BIfNonNullInst;
import soot.baf.internal.BIfNullInst;
import soot.baf.internal.BIncInst;
import soot.baf.internal.BInstanceCastInst;
import soot.baf.internal.BInstanceOfInst;
import soot.baf.internal.BInterfaceInvokeInst;
import soot.baf.internal.BJSRInst;
import soot.baf.internal.BLoadInst;
import soot.baf.internal.BLookupSwitchInst;
import soot.baf.internal.BMulInst;
import soot.baf.internal.BNegInst;
import soot.baf.internal.BNewArrayInst;
import soot.baf.internal.BNewInst;
import soot.baf.internal.BNewMultiArrayInst;
import soot.baf.internal.BNopInst;
import soot.baf.internal.BOrInst;
import soot.baf.internal.BPopInst;
import soot.baf.internal.BPrimitiveCastInst;
import soot.baf.internal.BPushInst;
import soot.baf.internal.BRemInst;
import soot.baf.internal.BReturnInst;
import soot.baf.internal.BReturnVoidInst;
import soot.baf.internal.BShlInst;
import soot.baf.internal.BShrInst;
import soot.baf.internal.BSpecialInvokeInst;
import soot.baf.internal.BStaticGetInst;
import soot.baf.internal.BStaticInvokeInst;
import soot.baf.internal.BStaticPutInst;
import soot.baf.internal.BStoreInst;
import soot.baf.internal.BSubInst;
import soot.baf.internal.BSwapInst;
import soot.baf.internal.BTableSwitchInst;
import soot.baf.internal.BThrowInst;
import soot.baf.internal.BTrap;
import soot.baf.internal.BUshrInst;
import soot.baf.internal.BVirtualInvokeInst;
import soot.baf.internal.BXorInst;
import soot.baf.internal.BafLocal;
import soot.baf.internal.BafLocalBox;
import soot.jimple.*;
import soot.jimple.internal.IdentityRefBox;
import soot.options.Options;

public class Baf {


    @Inject
    public Baf() {

    }

    public static Type getDescriptorTypeOf(Type opType) {
        if (opType instanceof NullType || opType instanceof ArrayType || opType instanceof RefType) {
            opType = opType.getMyScene().getPrimTypeCollector().getRefType();
        }

        return opType;
    }

    /**
     * Constructs a Local with the given name and type.
     */

    public static Local newLocal(String name, Type t) {
        return new BafLocal(name, t);
    }

    /**
     * Constructs a new BTrap for the given exception on the given Unit range with the given Unit handler.
     */

    public static Trap newTrap(SootClass exception, Unit beginUnit, Unit endUnit, Unit handlerUnit) {
        return new BTrap(exception, beginUnit, endUnit, handlerUnit);
    }

    /**
     * Constructs a ExitMonitorInst() grammar chunk
     */

    public static ExitMonitorInst newExitMonitorInst() {
        return new BExitMonitorInst();
    }

    /**
     * Constructs a EnterMonitorInst() grammar chunk.
     */

    public static EnterMonitorInst newEnterMonitorInst() {
        return new BEnterMonitorInst();
    }

    public static ReturnVoidInst newReturnVoidInst() {
        return new BReturnVoidInst();
    }

    public static NopInst newNopInst() {
        return new BNopInst();
    }

    public static GotoInst newGotoInst(Unit unit) {
        return new BGotoInst(unit);
    }

    public static JSRInst newJSRInst(Unit unit) {
        return new BJSRInst(unit);
    }

    public static PlaceholderInst newPlaceholderInst(Unit source) {
        return new PlaceholderInst(source);
    }

    public static UnitBox newInstBox(Unit unit) {
        return new InstBox((Inst) unit);
    }

    public static PushInst newPushInst(Constant c) {
        return new BPushInst(c);
    }

    public static IdentityInst newIdentityInst(Value local, Value identityRef) {
        return new BIdentityInst(local, identityRef);
    }

    public static ValueBox newLocalBox(Value value) {
        return new BafLocalBox(value);
    }

    public static ValueBox newIdentityRefBox(Value value) {
        return new IdentityRefBox(value);
    }

    /**
     * Constructs a ThisRef(RefType) grammar chunk.
     */

    public static ThisRef newThisRef(RefType t) {
        return new ThisRef(t);
    }

    /**
     * Constructs a ParameterRef(SootMethod, int) grammar chunk.
     */

    public static ParameterRef newParameterRef(Type paramType, int number) {
        return new ParameterRef(paramType, number);
    }

    public static StoreInst newStoreInst(Type opType, Local l) {
        return new BStoreInst(opType, l);
    }

    public static LoadInst newLoadInst(Type opType, Local l) {
        return new BLoadInst(opType, l);
    }

    public static ArrayWriteInst newArrayWriteInst(Type opType) {
        return new BArrayWriteInst(opType);
    }

    public static ArrayReadInst newArrayReadInst(Type opType) {
        return new BArrayReadInst(opType);
    }

    public static StaticGetInst newStaticGetInst(SootFieldRef fieldRef) {
        return new BStaticGetInst(fieldRef);
    }

    public static StaticPutInst newStaticPutInst(SootFieldRef fieldRef) {
        return new BStaticPutInst(fieldRef);
    }

    public static FieldGetInst newFieldGetInst(SootFieldRef fieldRef) {
        return new BFieldGetInst(fieldRef);
    }

    public static FieldPutInst newFieldPutInst(SootFieldRef fieldRef) {
        return new BFieldPutInst(fieldRef);
    }

    public static AddInst newAddInst(Type opType) {
        return new BAddInst(opType);
    }

    public static PopInst newPopInst(Type aType) {
        return new BPopInst(aType);
    }

    public static SubInst newSubInst(Type opType) {
        return new BSubInst(opType);
    }

    public static MulInst newMulInst(Type opType) {
        return new BMulInst(opType);
    }

    public static DivInst newDivInst(Type opType) {
        return new BDivInst(opType);
    }

    public static AndInst newAndInst(Type opType) {
        return new BAndInst(opType);
    }

    public static ArrayLengthInst newArrayLengthInst() {
        return new BArrayLengthInst();
    }

    public static NegInst newNegInst(Type opType) {
        return new BNegInst(opType);
    }

    public static OrInst newOrInst(Type opType) {
        return new BOrInst(opType);
    }

    public static RemInst newRemInst(Type opType) {
        return new BRemInst(opType);
    }

    public static ShlInst newShlInst(Type opType) {
        return new BShlInst(opType);
    }

    public static ShrInst newShrInst(Type opType) {
        return new BShrInst(opType);
    }

    public static UshrInst newUshrInst(Type opType) {
        return new BUshrInst(opType);
    }

    public static XorInst newXorInst(Type opType) {
        return new BXorInst(opType);
    }

    public static InstanceCastInst newInstanceCastInst(Type opType) {
        return new BInstanceCastInst(opType);
    }

    public static InstanceOfInst newInstanceOfInst(Type opType) {
        return new BInstanceOfInst(opType);
    }

    public static PrimitiveCastInst newPrimitiveCastInst(Type fromType, Type toType) {
        return new BPrimitiveCastInst(fromType, toType);
    }

    public static NewInst newNewInst(RefType opType) {
        return new BNewInst(opType);
    }

    public static NewArrayInst newNewArrayInst(Type opType) {
        return new BNewArrayInst(opType);
    }

    public static NewMultiArrayInst newNewMultiArrayInst(ArrayType opType, int dimensions) {
        return new BNewMultiArrayInst(opType, dimensions);
    }

    public static DynamicInvokeInst newDynamicInvokeInst(SootMethodRef bsmMethodRef, List<Value> bsmArgs, SootMethodRef methodRef,
                                                         int tag) {
        return new BDynamicInvokeInst(bsmMethodRef, bsmArgs, methodRef, tag);
    }

    public static StaticInvokeInst newStaticInvokeInst(SootMethodRef methodRef) {
        return new BStaticInvokeInst(methodRef);
    }

    public static SpecialInvokeInst newSpecialInvokeInst(SootMethodRef methodRef) {
        return new BSpecialInvokeInst(methodRef);
    }

    public static VirtualInvokeInst newVirtualInvokeInst(SootMethodRef methodRef) {
        return new BVirtualInvokeInst(methodRef);
    }

    public static InterfaceInvokeInst newInterfaceInvokeInst(SootMethodRef methodRef, int argCount) {
        return new BInterfaceInvokeInst(methodRef, argCount);
    }

    public static ReturnInst newReturnInst(Type opType) {
        return new BReturnInst(opType);
    }

    public static IfCmpEqInst newIfCmpEqInst(Type opType, Unit unit) {
        return new BIfCmpEqInst(opType, unit);
    }

    public static IfCmpGeInst newIfCmpGeInst(Type opType, Unit unit) {
        return new BIfCmpGeInst(opType, unit);
    }

    public static IfCmpGtInst newIfCmpGtInst(Type opType, Unit unit) {
        return new BIfCmpGtInst(opType, unit);
    }

    public static IfCmpLeInst newIfCmpLeInst(Type opType, Unit unit) {
        return new BIfCmpLeInst(opType, unit);
    }

    public static IfCmpLtInst newIfCmpLtInst(Type opType, Unit unit) {
        return new BIfCmpLtInst(opType, unit);
    }

    public static IfCmpNeInst newIfCmpNeInst(Type opType, Unit unit) {
        return new BIfCmpNeInst(opType, unit);
    }

    public static CmpInst newCmpInst(Type opType) {
        return new BCmpInst(opType);
    }

    public static CmpgInst newCmpgInst(Type opType) {
        return new BCmpgInst(opType);
    }

    public static CmplInst newCmplInst(Type opType) {
        return new BCmplInst(opType);
    }

    public static IfEqInst newIfEqInst(Unit unit) {
        return new BIfEqInst(unit);
    }

    public static IfGeInst newIfGeInst(Unit unit) {
        return new BIfGeInst(unit);
    }

    public static IfGtInst newIfGtInst(Unit unit) {
        return new BIfGtInst(unit);
    }

    public static IfLeInst newIfLeInst(Unit unit) {
        return new BIfLeInst(unit);
    }

    public static IfLtInst newIfLtInst(Unit unit) {
        return new BIfLtInst(unit);
    }

    public static IfNeInst newIfNeInst(Unit unit) {
        return new BIfNeInst(unit);
    }

    public static IfNullInst newIfNullInst(Unit unit) {
        return new BIfNullInst(unit);
    }

    public static IfNonNullInst newIfNonNullInst(Unit unit) {
        return new BIfNonNullInst(unit);
    }

    public static ThrowInst newThrowInst() {
        return new BThrowInst();
    }

    public static SwapInst newSwapInst(Type fromType, Type toType) {
        return new BSwapInst(fromType, toType);
    }

    /*
     *public static DupInst newDupInst(Type type) { return new BDupInst(new ArrayList(), Arrays.asList(new Type[] {type})); }
     */

    public static Dup1Inst newDup1Inst(Type type) {
        return new BDup1Inst(type);
    }

    public static Dup2Inst newDup2Inst(Type aOp1Type, Type aOp2Type) {
        return new BDup2Inst(aOp1Type, aOp2Type);
    }

    public static Dup1_x1Inst newDup1_x1Inst(Type aOpType, Type aUnderType) {
        return new BDup1_x1Inst(aOpType, aUnderType);
    }

    public static Dup1_x2Inst newDup1_x2Inst(Type aOpType, Type aUnder1Type, Type aUnder2Type) {
        return new BDup1_x2Inst(aOpType, aUnder1Type, aUnder2Type);
    }

    public static Dup2_x1Inst newDup2_x1Inst(Type aOp1Type, Type aOp2Type, Type aUnderType) {
        return new BDup2_x1Inst(aOp1Type, aOp2Type, aUnderType);
    }

    public static Dup2_x2Inst newDup2_x2Inst(Type aOp1Type, Type aOp2Type, Type aUnder1Type, Type aUnder2Type) {
        return new BDup2_x2Inst(aOp1Type, aOp2Type, aUnder1Type, aUnder2Type);
    }

    public static IncInst newIncInst(Local aLocal, Constant aConstant) {
        return new BIncInst(aLocal, aConstant);
    }

    public static LookupSwitchInst newLookupSwitchInst(Unit defaultTarget, List<IntConstant> lookupValues, List targets) {
        return new BLookupSwitchInst(defaultTarget, lookupValues, targets);
    }

    public static TableSwitchInst newTableSwitchInst(Unit defaultTarget, int lowIndex, int highIndex, List targets) {
        return new BTableSwitchInst(defaultTarget, lowIndex, highIndex, targets);
    }

    public static String bafDescriptorOf(Type type) {
        TypeSwitch sw;

        type.apply(sw = new TypeSwitch() {
            public void caseBooleanType(BooleanType t) {
                setResult("b");
            }

            public void caseByteType(ByteType t) {
                setResult("b");
            }

            public void caseCharType(CharType t) {
                setResult("c");
            }

            public void caseDoubleType(DoubleType t) {
                setResult("d");
            }

            public void caseFloatType(FloatType t) {
                setResult("f");
            }

            public void caseIntType(IntType t) {
                setResult("i");
            }

            public void caseLongType(LongType t) {
                setResult("l");
            }

            public void caseShortType(ShortType t) {
                setResult("s");
            }

            public void defaultCase(Type t) {
                throw new RuntimeException("Invalid type: " + t);
            }

            public void caseRefType(RefType t) {
                setResult("r");
            }

        });

        return (String) sw.getResult();
    }

    /**
     * Returns an empty BafBody associated with method m.
     */
    public static BafBody newBody(SootMethod m, Options myOptions, Printer myPrinter) {
        return new BafBody(m, myOptions, myPrinter);
    }

    /**
     * Returns a BafBody constructed from b.
     */
    public static BafBody newBody(JimpleBody b, Options myOptions, Printer myPrinter, PackManager myPackmanager, Scene myScene, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory) {
        return new BafBody(b, Collections.<String, String>emptyMap(), myOptions, myPrinter, myPackmanager, myScene, primTypeCollector, constantFactory);
    }

    /**
     * Returns a BafBody constructed from b.
     */
    public static BafBody newBody(JimpleBody b, String phase, PhaseOptions myPhaseOptions, Options myOptions, Printer myPrinter, PackManager myPackmanager, Scene myScene, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory) {
        Map<String, String> options = myPhaseOptions.getPhaseOptions(phase);
        return new BafBody(b, options, myOptions, myPrinter, myPackmanager, myScene, primTypeCollector, constantFactory);
    }
}
