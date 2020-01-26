package soot.grimp;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1999 Patrick Lam
 * Copyright (C) 2004 Ondrej Lhotak
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General public static License as
 * published by the Free Software Foundation, either version 2.1 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser public static License for more details.
 *
 * You should have received a copy of the GNU General Lesser public static
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/lgpl-2.1.html>.
 * #L%
 */

import java.util.ArrayList;
import java.util.List;

import com.google.inject.Inject;
import soot.*;
import soot.grimp.internal.ExprBox;
import soot.grimp.internal.GAddExpr;
import soot.grimp.internal.GAndExpr;
import soot.grimp.internal.GArrayRef;
import soot.grimp.internal.GAssignStmt;
import soot.grimp.internal.GCastExpr;
import soot.grimp.internal.GCmpExpr;
import soot.grimp.internal.GCmpgExpr;
import soot.grimp.internal.GCmplExpr;
import soot.grimp.internal.GDivExpr;
import soot.grimp.internal.GDynamicInvokeExpr;
import soot.grimp.internal.GEnterMonitorStmt;
import soot.grimp.internal.GEqExpr;
import soot.grimp.internal.GExitMonitorStmt;
import soot.grimp.internal.GGeExpr;
import soot.grimp.internal.GGtExpr;
import soot.grimp.internal.GIdentityStmt;
import soot.grimp.internal.GIfStmt;
import soot.grimp.internal.GInstanceFieldRef;
import soot.grimp.internal.GInstanceOfExpr;
import soot.grimp.internal.GInterfaceInvokeExpr;
import soot.grimp.internal.GInvokeStmt;
import soot.grimp.internal.GLeExpr;
import soot.grimp.internal.GLengthExpr;
import soot.grimp.internal.GLookupSwitchStmt;
import soot.grimp.internal.GLtExpr;
import soot.grimp.internal.GMulExpr;
import soot.grimp.internal.GNeExpr;
import soot.grimp.internal.GNegExpr;
import soot.grimp.internal.GNewArrayExpr;
import soot.grimp.internal.GNewInvokeExpr;
import soot.grimp.internal.GNewMultiArrayExpr;
import soot.grimp.internal.GOrExpr;
import soot.grimp.internal.GRValueBox;
import soot.grimp.internal.GRemExpr;
import soot.grimp.internal.GReturnStmt;
import soot.grimp.internal.GShlExpr;
import soot.grimp.internal.GShrExpr;
import soot.grimp.internal.GSpecialInvokeExpr;
import soot.grimp.internal.GStaticInvokeExpr;
import soot.grimp.internal.GSubExpr;
import soot.grimp.internal.GTableSwitchStmt;
import soot.grimp.internal.GThrowStmt;
import soot.grimp.internal.GTrap;
import soot.grimp.internal.GUshrExpr;
import soot.grimp.internal.GVirtualInvokeExpr;
import soot.grimp.internal.GXorExpr;
import soot.grimp.internal.ObjExprBox;
import soot.jimple.AbstractExprSwitch;
import soot.jimple.AddExpr;
import soot.jimple.AndExpr;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BreakpointStmt;
import soot.jimple.CastExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.CmpExpr;
import soot.jimple.CmpgExpr;
import soot.jimple.CmplExpr;
import soot.jimple.Constant;
import soot.jimple.ConstantFactory;
import soot.jimple.DivExpr;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.EqExpr;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.Expr;
import soot.jimple.GeExpr;
import soot.jimple.GotoStmt;
import soot.jimple.GtExpr;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceOfExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.LeExpr;
import soot.jimple.LengthExpr;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.LtExpr;
import soot.jimple.MulExpr;
import soot.jimple.NeExpr;
import soot.jimple.NegExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NopStmt;
import soot.jimple.OrExpr;
import soot.jimple.ParameterRef;
import soot.jimple.RemExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.ShlExpr;
import soot.jimple.ShrExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.SubExpr;
import soot.jimple.TableSwitchStmt;
import soot.jimple.ThisRef;
import soot.jimple.ThrowStmt;
import soot.jimple.UshrExpr;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.XorExpr;
import soot.options.Options;

/**
 * The Grimp class contains all the constructors for the components of the Grimp grammar for the Grimp body. <br>
 * <br>
 * <p>
 * Immediate -> Local | Constant <br>
 * RValue -> Local | Constant | ConcreteRef | Expr<br>
 * Variable -> Local | ArrayRef | InstanceFieldRef | StaticFieldRef <br>
 */

public class Grimp {

    @Inject
    public Grimp() {
    }


    /**
     * Constructs a XorExpr(Expr, Expr) grammar chunk.
     */

    public static XorExpr newXorExpr(Value op1, Value op2) {
        return new GXorExpr(op1, op2);
    }

    /**
     * Constructs a UshrExpr(Expr, Expr) grammar chunk.
     */

    public static UshrExpr newUshrExpr(Value op1, Value op2) {
        return new GUshrExpr(op1, op2);
    }

    /**
     * Constructs a SubExpr(Expr, Expr) grammar chunk.
     */

    public static SubExpr newSubExpr(Value op1, Value op2) {
        return new GSubExpr(op1, op2);
    }

    /**
     * Constructs a ShrExpr(Expr, Expr) grammar chunk.
     */

    public static ShrExpr newShrExpr(Value op1, Value op2) {
        return new GShrExpr(op1, op2);
    }

    /**
     * Constructs a ShlExpr(Expr, Expr) grammar chunk.
     */

    public static ShlExpr newShlExpr(Value op1, Value op2) {
        return new GShlExpr(op1, op2);
    }

    /**
     * Constructs a RemExpr(Expr, Expr) grammar chunk.
     */

    public static RemExpr newRemExpr(Value op1, Value op2) {
        return new GRemExpr(op1, op2);
    }

    /**
     * Constructs a OrExpr(Expr, Expr) grammar chunk.
     */

    public static OrExpr newOrExpr(Value op1, Value op2) {
        return new GOrExpr(op1, op2);
    }

    /**
     * Constructs a NeExpr(Expr, Expr) grammar chunk.
     */

    public static NeExpr newNeExpr(Value op1, Value op2) {
        return new GNeExpr(op1, op2);
    }

    /**
     * Constructs a MulExpr(Expr, Expr) grammar chunk.
     */

    public static MulExpr newMulExpr(Value op1, Value op2) {
        return new GMulExpr(op1, op2);
    }

    /**
     * Constructs a LeExpr(Expr, Expr) grammar chunk.
     */

    public static LeExpr newLeExpr(Value op1, Value op2) {
        return new GLeExpr(op1, op2);
    }

    /**
     * Constructs a GeExpr(Expr, Expr) grammar chunk.
     */

    public static GeExpr newGeExpr(Value op1, Value op2) {
        return new GGeExpr(op1, op2);
    }

    /**
     * Constructs a EqExpr(Expr, Expr) grammar chunk.
     */

    public static EqExpr newEqExpr(Value op1, Value op2) {
        return new GEqExpr(op1, op2);
    }

    /**
     * Constructs a DivExpr(Expr, Expr) grammar chunk.
     */

    public static DivExpr newDivExpr(Value op1, Value op2) {
        return new GDivExpr(op1, op2);
    }

    /**
     * Constructs a CmplExpr(Expr, Expr) grammar chunk.
     */

    public static CmplExpr newCmplExpr(Value op1, Value op2) {
        return new GCmplExpr(op1, op2);
    }

    /**
     * Constructs a CmpgExpr(Expr, Expr) grammar chunk.
     */

    public static CmpgExpr newCmpgExpr(Value op1, Value op2) {
        return new GCmpgExpr(op1, op2);
    }

    /**
     * Constructs a CmpExpr(Expr, Expr) grammar chunk.
     */

    public static CmpExpr newCmpExpr(Value op1, Value op2) {
        return new GCmpExpr(op1, op2);
    }

    /**
     * Constructs a GtExpr(Expr, Expr) grammar chunk.
     */

    public static GtExpr newGtExpr(Value op1, Value op2) {
        return new GGtExpr(op1, op2);
    }

    /**
     * Constructs a LtExpr(Expr, Expr) grammar chunk.
     */

    public static LtExpr newLtExpr(Value op1, Value op2) {
        return new GLtExpr(op1, op2);
    }

    /**
     * Constructs a AddExpr(Expr, Expr) grammar chunk.
     */

    public static AddExpr newAddExpr(Value op1, Value op2) {
        return new GAddExpr(op1, op2);
    }

    /**
     * Constructs a AndExpr(Expr, Expr) grammar chunk.
     */

    public static AndExpr newAndExpr(Value op1, Value op2) {
        return new GAndExpr(op1, op2);
    }

    /**
     * Constructs a NegExpr(Expr, Expr) grammar chunk.
     */

    public static NegExpr newNegExpr(Value op) {
        return new GNegExpr(op);
    }

    /**
     * Constructs a LengthExpr(Expr) grammar chunk.
     */

    public static LengthExpr newLengthExpr(Value op) {
        return new GLengthExpr(op);
    }

    /**
     * Constructs a CastExpr(Expr, Type) grammar chunk.
     */

    public static CastExpr newCastExpr(Value op1, Type t) {
        return new GCastExpr(op1, t);
    }

    /**
     * Constructs a InstanceOfExpr(Expr, Type) grammar chunk.
     */

    public static InstanceOfExpr newInstanceOfExpr(Value op1, Type t) {
        return new GInstanceOfExpr(op1, t);
    }

    /**
     * Constructs a NewExpr(RefType) grammar chunk.
     */

    public static NewExpr newNewExpr(RefType type) {
        return Jimple.newNewExpr(type);
    }

    /**
     * Constructs a NewArrayExpr(Type, Expr) grammar chunk.
     */

    public static NewArrayExpr newNewArrayExpr(Type type, Value size) {
        return new GNewArrayExpr(type, size);
    }

    /**
     * Constructs a NewMultiArrayExpr(ArrayType, List of Expr) grammar chunk.
     */

    public static NewMultiArrayExpr newNewMultiArrayExpr(ArrayType type, List sizes) {
        return new GNewMultiArrayExpr(type, sizes);
    }

    /**
     * Constructs a NewInvokeExpr(Local base, List of Expr) grammar chunk.
     */

    public static NewInvokeExpr newNewInvokeExpr(RefType base, SootMethodRef method, List args) {
        return new GNewInvokeExpr(base, method, args);
    }

    /**
     * Constructs a StaticInvokeExpr(ArrayType, List of Expr) grammar chunk.
     */

    public static StaticInvokeExpr newStaticInvokeExpr(SootMethodRef method, List args) {
        return new GStaticInvokeExpr(method, args);
    }

    /**
     * Constructs a SpecialInvokeExpr(Local base, SootMethodRef method, List of Expr) grammar chunk.
     */

    public static SpecialInvokeExpr newSpecialInvokeExpr(Local base, SootMethodRef method, List args) {
        return new GSpecialInvokeExpr(base, method, args);
    }

    /**
     * Constructs a VirtualInvokeExpr(Local base, SootMethodRef method, List of Expr) grammar chunk.
     */

    public static VirtualInvokeExpr newVirtualInvokeExpr(Local base, SootMethodRef method, List args) {
        return new GVirtualInvokeExpr(base, method, args);
    }

    /**
     * Constructs a new DynamicInvokeExpr grammar chunk.
     */
    public static DynamicInvokeExpr newDynamicInvokeExpr(SootMethodRef bootstrapMethodRef, List<Value> bootstrapArgs,
                                                         SootMethodRef methodRef, int tag, List args) {
        return new GDynamicInvokeExpr(bootstrapMethodRef, bootstrapArgs, methodRef, tag, args);
    }

    /**
     * Constructs a InterfaceInvokeExpr(Local base, SootMethodRef method, List of Expr) grammar chunk.
     */

    public static InterfaceInvokeExpr newInterfaceInvokeExpr(Local base, SootMethodRef method, List args) {
        return new GInterfaceInvokeExpr(base, method, args);
    }

    /**
     * Constructs a ThrowStmt(Expr) grammar chunk.
     */

    public static ThrowStmt newThrowStmt(Value op) {
        return new GThrowStmt(op);
    }

    public static ThrowStmt newThrowStmt(ThrowStmt s) {
        return new GThrowStmt(s.getOp());
    }

    /**
     * Constructs a ExitMonitorStmt(Expr) grammar chunk
     */

    public static ExitMonitorStmt newExitMonitorStmt(Value op) {
        return new GExitMonitorStmt(op);
    }

    public static ExitMonitorStmt newExitMonitorStmt(ExitMonitorStmt s) {
        return new GExitMonitorStmt(s.getOp());
    }

    /**
     * Constructs a EnterMonitorStmt(Expr) grammar chunk.
     */

    public static EnterMonitorStmt newEnterMonitorStmt(Value op) {
        return new GEnterMonitorStmt(op);
    }

    public static EnterMonitorStmt newEnterMonitorStmt(EnterMonitorStmt s) {
        return new GEnterMonitorStmt(s.getOp());
    }

    /**
     * Constructs a BreakpointStmt() grammar chunk.
     */

    public static BreakpointStmt newBreakpointStmt() {
        return Jimple.newBreakpointStmt();
    }

    public static BreakpointStmt newBreakpointStmt(BreakpointStmt s) {
        return Jimple.newBreakpointStmt();
    }

    /**
     * Constructs a GotoStmt(Stmt) grammar chunk.
     */

    public static GotoStmt newGotoStmt(Unit target) {
        return Jimple.newGotoStmt(target);
    }

    public static GotoStmt newGotoStmt(GotoStmt s) {
        return Jimple.newGotoStmt(s.getTarget());
    }

    /**
     * Constructs a NopStmt() grammar chunk.
     */

    public static NopStmt newNopStmt() {
        return Jimple.newNopStmt();
    }

    public static NopStmt newNopStmt(NopStmt s) {
        return Jimple.newNopStmt();
    }

    /**
     * Constructs a ReturnVoidStmt() grammar chunk.
     */

    public static ReturnVoidStmt newReturnVoidStmt() {
        return Jimple.newReturnVoidStmt();
    }

    public static ReturnVoidStmt newReturnVoidStmt(ReturnVoidStmt s) {
        return Jimple.newReturnVoidStmt();
    }

    /**
     * Constructs a ReturnStmt(Expr) grammar chunk.
     */

    public static ReturnStmt newReturnStmt(Value op) {
        return new GReturnStmt(op);
    }

    public static ReturnStmt newReturnStmt(ReturnStmt s) {
        return new GReturnStmt(s.getOp());
    }

    /**
     * Constructs a IfStmt(Condition, Stmt) grammar chunk.
     */

    public static IfStmt newIfStmt(Value condition, Unit target) {
        return new GIfStmt(condition, target);
    }

    public static IfStmt newIfStmt(IfStmt s) {
        return new GIfStmt(s.getCondition(), s.getTarget());
    }

    /**
     * Constructs a IdentityStmt(Local, IdentityRef) grammar chunk.
     */

    public static IdentityStmt newIdentityStmt(Value local, Value identityRef) {
        return new GIdentityStmt(local, identityRef);
    }

    public static IdentityStmt newIdentityStmt(IdentityStmt s) {
        return new GIdentityStmt(s.getLeftOp(), s.getRightOp());
    }

    /**
     * Constructs a AssignStmt(Variable, RValue) grammar chunk.
     */

    public static AssignStmt newAssignStmt(Value variable, Value rvalue) {
        return new GAssignStmt(variable, rvalue);
    }

    public static AssignStmt newAssignStmt(AssignStmt s) {
        return new GAssignStmt(s.getLeftOp(), s.getRightOp());
    }

    /**
     * Constructs a InvokeStmt(InvokeExpr) grammar chunk.
     */

    public static InvokeStmt newInvokeStmt(Value op) {
        return new GInvokeStmt(op);
    }

    public static InvokeStmt newInvokeStmt(InvokeStmt s) {
        return new GInvokeStmt(s.getInvokeExpr());
    }

    /**
     * Constructs a TableSwitchStmt(Expr, int, int, List of Unit, Stmt) grammar chunk.
     */

    public static TableSwitchStmt newTableSwitchStmt(Value key, int lowIndex, int highIndex, List targets, Unit defaultTarget) {
        return new GTableSwitchStmt(key, lowIndex, highIndex, targets, defaultTarget);
    }

    public static TableSwitchStmt newTableSwitchStmt(TableSwitchStmt s) {
        return new GTableSwitchStmt(s.getKey(), s.getLowIndex(), s.getHighIndex(), s.getTargets(), s.getDefaultTarget());
    }

    /**
     * Constructs a LookupSwitchStmt(Expr, List of Expr, List of Unit, Stmt) grammar chunk.
     */

    public static LookupSwitchStmt newLookupSwitchStmt(Value key, List lookupValues, List targets, Unit defaultTarget) {
        return new GLookupSwitchStmt(key, lookupValues, targets, defaultTarget);
    }

    public static LookupSwitchStmt newLookupSwitchStmt(LookupSwitchStmt s) {
        return new GLookupSwitchStmt(s.getKey(), s.getLookupValues(), s.getTargets(), s.getDefaultTarget());
    }

    /**
     * Constructs a Local with the given name and type.
     */

    public static Local newLocal(String name, Type t) {
        return Jimple.newLocal(name, t);
    }

    /**
     * Constructs a new Trap for the given exception on the given Stmt range with the given Stmt handler.
     */

    public static Trap newTrap(SootClass exception, Unit beginStmt, Unit endStmt, Unit handlerStmt) {
        return new GTrap(exception, beginStmt, endStmt, handlerStmt);
    }

    public static Trap newTrap(Trap trap) {
        return new GTrap(trap.getException(), trap.getBeginUnit(), trap.getEndUnit(), trap.getHandlerUnit());
    }

    /**
     * Constructs a StaticFieldRef(SootFieldRef) grammar chunk.
     */

    public static StaticFieldRef newStaticFieldRef(SootFieldRef f) {
        return Jimple.newStaticFieldRef(f);
    }

    /**
     * Constructs a ThisRef(RefType) grammar chunk.
     */

    public static ThisRef newThisRef(RefType t) {
        return Jimple.newThisRef(t);
    }

    /**
     * Constructs a ParameterRef(SootMethod, int) grammar chunk.
     */

    public static ParameterRef newParameterRef(Type paramType, int number) {
        return Jimple.newParameterRef(paramType, number);
    }

    /**
     * Constructs a InstanceFieldRef(Value, SootFieldRef) grammar chunk.
     */

    public static InstanceFieldRef newInstanceFieldRef(Value base, SootFieldRef f) {
        return new GInstanceFieldRef(base, f);
    }

    /**
     * Constructs a CaughtExceptionRef() grammar chunk.
     *
     * @param myScene
     */

    public static CaughtExceptionRef newCaughtExceptionRef(Scene myScene) {
        return Jimple.newCaughtExceptionRef(myScene);
    }

    /**
     * Constructs a ArrayRef(Local, Expr) grammar chunk.
     */

    public static ArrayRef newArrayRef(Value base, Value index) {
        return new GArrayRef(base, index);
    }

    public static ValueBox newVariableBox(Value value) {
        return Jimple.newVariableBox(value);
    }

    public static ValueBox newLocalBox(Value value) {
        return Jimple.newLocalBox(value);
    }

    public static ValueBox newRValueBox(Value value) {
        return new GRValueBox(value);
    }

    public static ValueBox newImmediateBox(Value value) {
        return Jimple.newImmediateBox(value);
    }

    public static ValueBox newExprBox(Value value) {
        return new ExprBox(value);
    }

    public static ValueBox newArgBox(Value value) {
        return new ExprBox(value);
    }

    public static ValueBox newObjExprBox(Value value) {
        return new ObjExprBox(value);
    }

    public static ValueBox newIdentityRefBox(Value value) {
        return Jimple.newIdentityRefBox(value);
    }

    public static ValueBox newConditionExprBox(Value value) {
        return Jimple.newConditionExprBox(value);
    }

    public static ValueBox newInvokeExprBox(Value value) {
        return Jimple.newInvokeExprBox(value);
    }

    public static UnitBox newStmtBox(Unit unit) {
        return Jimple.newStmtBox(unit);
    }

    /**
     * Carries out the mapping from other Value's to Grimp Value's
     */
    public static Value newExpr(Value value, ConstantFactory constantFactory) {
        if (value instanceof Expr) {
            final ExprBox returnedExpr = new ExprBox(constantFactory.createIntConstant(0));
            ((Expr) value).apply(new AbstractExprSwitch() {
                public  void caseAddExpr(AddExpr v) {
                    returnedExpr.setValue(newAddExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseAndExpr(AndExpr v) {
                    returnedExpr.setValue(newAndExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseCmpExpr(CmpExpr v) {
                    returnedExpr.setValue(newCmpExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseCmpgExpr(CmpgExpr v) {
                    returnedExpr.setValue(newCmpgExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseCmplExpr(CmplExpr v) {
                    returnedExpr.setValue(newCmplExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseDivExpr(DivExpr v) {
                    returnedExpr.setValue(newDivExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseEqExpr(EqExpr v) {
                    returnedExpr.setValue(newEqExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseNeExpr(NeExpr v) {
                    returnedExpr.setValue(newNeExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseGeExpr(GeExpr v) {
                    returnedExpr.setValue(newGeExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseGtExpr(GtExpr v) {
                    returnedExpr.setValue(newGtExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseLeExpr(LeExpr v) {
                    returnedExpr.setValue(newLeExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseLtExpr(LtExpr v) {
                    returnedExpr.setValue(newLtExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseMulExpr(MulExpr v) {
                    returnedExpr.setValue(newMulExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseOrExpr(OrExpr v) {
                    returnedExpr.setValue(newOrExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseRemExpr(RemExpr v) {
                    returnedExpr.setValue(newRemExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseShlExpr(ShlExpr v) {
                    returnedExpr.setValue(newShlExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseShrExpr(ShrExpr v) {
                    returnedExpr.setValue(newShrExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseUshrExpr(UshrExpr v) {
                    returnedExpr.setValue(newUshrExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseSubExpr(SubExpr v) {
                    returnedExpr.setValue(newSubExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseXorExpr(XorExpr v) {
                    returnedExpr.setValue(newXorExpr(newExpr(v.getOp1(), constantFactory), newExpr(v.getOp2(), constantFactory)));
                }

                public  void caseInterfaceInvokeExpr(InterfaceInvokeExpr v) {
                    ArrayList newArgList = new ArrayList();
                    for (int i = 0; i < v.getArgCount(); i++) {
                        newArgList.add(newExpr(v.getArg(i), constantFactory));
                    }
                    returnedExpr.setValue(newInterfaceInvokeExpr((Local) (v.getBase()), v.getMethodRef(), newArgList));
                }

                public  void caseSpecialInvokeExpr(SpecialInvokeExpr v) {
                    ArrayList newArgList = new ArrayList();
                    for (int i = 0; i < v.getArgCount(); i++) {
                        newArgList.add(newExpr(v.getArg(i), constantFactory));
                    }
                    returnedExpr.setValue(newSpecialInvokeExpr((Local) (v.getBase()), v.getMethodRef(), newArgList));
                }

                public  void caseStaticInvokeExpr(StaticInvokeExpr v) {
                    ArrayList newArgList = new ArrayList();
                    for (int i = 0; i < v.getArgCount(); i++) {
                        newArgList.add(newExpr(v.getArg(i), constantFactory));
                    }
                    returnedExpr.setValue(newStaticInvokeExpr(v.getMethodRef(), newArgList));
                }

                public  void caseVirtualInvokeExpr(VirtualInvokeExpr v) {
                    ArrayList newArgList = new ArrayList();
                    for (int i = 0; i < v.getArgCount(); i++) {
                        newArgList.add(newExpr(v.getArg(i), constantFactory));
                    }
                    returnedExpr.setValue(newVirtualInvokeExpr((Local) (v.getBase()), v.getMethodRef(), newArgList));
                }

                public  void caseDynamicInvokeExpr(DynamicInvokeExpr v) {
                    ArrayList newArgList = new ArrayList();
                    for (int i = 0; i < v.getArgCount(); i++) {
                        newArgList.add(newExpr(v.getArg(i), constantFactory));
                    }
                    returnedExpr.setValue(newDynamicInvokeExpr(v.getBootstrapMethodRef(), v.getBootstrapArgs(), v.getMethodRef(),
                            v.getHandleTag(), newArgList));
                }

                public  void caseCastExpr(CastExpr v) {
                    returnedExpr.setValue(newCastExpr(newExpr(v.getOp(), constantFactory), v.getType()));
                }

                public  void caseInstanceOfExpr(InstanceOfExpr v) {
                    returnedExpr.setValue(newInstanceOfExpr(newExpr(v.getOp(), constantFactory), v.getCheckType()));
                }

                public  void caseNewArrayExpr(NewArrayExpr v) {
                    returnedExpr.setValue(newNewArrayExpr(v.getBaseType(), v.getSize()));
                }

                public  void caseNewMultiArrayExpr(NewMultiArrayExpr v) {
                    returnedExpr.setValue(newNewMultiArrayExpr(v.getBaseType(), v.getSizes()));
                }

                public  void caseNewExpr(NewExpr v) {
                    returnedExpr.setValue(newNewExpr(v.getBaseType()));
                }

                public  void caseLengthExpr(LengthExpr v) {
                    returnedExpr.setValue(newLengthExpr(newExpr(v.getOp(), constantFactory)));
                }

                public  void caseNegExpr(NegExpr v) {
                    returnedExpr.setValue(newNegExpr(newExpr(v.getOp(), constantFactory)));
                }

                public  void defaultCase(Object v) {
                    returnedExpr.setValue((Expr) v);
                }
            });
            return returnedExpr.getValue();
        } else {
            if (value instanceof ArrayRef) {
                return newArrayRef(((ArrayRef) value).getBase(), newExpr(((ArrayRef) value).getIndex(), constantFactory));
            }
            if (value instanceof InstanceFieldRef) {
                return newInstanceFieldRef(newExpr((((InstanceFieldRef) value).getBase()), constantFactory),
                        ((InstanceFieldRef) value).getFieldRef());
            }
            /* have Ref/Value, which is fine -- not Jimple-specific. */
            return value;
        }
    }

    /**
     * Returns an empty GrimpBody associated with method m.
     */
    public static GrimpBody newBody(SootMethod m, Options myOptions, Printer myPrinter) {
        return new GrimpBody(m, myOptions, myPrinter, constantFactory);
    }

    /**
     * Returns a GrimpBody constructed from b.
     */
    public static GrimpBody newBody(Body b, String phase, Options myOptions, Printer myPrinter, Grimp grimp, PackManager manager) {
        return new GrimpBody(b, myOptions, myPrinter, manager, constantFactory);
    }

    public static Value cloneIfNecessary(Value val) {
        if (val instanceof Local || val instanceof Constant) {
            return val;
        } else {
            return (Value) val.clone();
        }
    }
}
