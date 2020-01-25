package soot.toolkits.exceptions;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 2018 Raja Vallée-Rai and others
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import soot.AnySubType;
import soot.ArrayType;
import soot.DoubleType;
import soot.FloatType;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.ArrayRef;
import soot.jimple.DivExpr;
import soot.jimple.DoubleConstant;
import soot.jimple.FloatConstant;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.LongConstant;
import soot.jimple.RemExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.toolkits.exceptions.ExceptionTestUtility.ExceptionHashSet;

public class UnitThrowAnalysisTest {

	static {
		myScene.loadBasicClasses();
	}

	class ImmaculateInvokeUnitThrowAnalysis extends UnitThrowAnalysis {
		// A variant of UnitThrowAnalysis which assumes that invoked
		// methods will never throw any exceptions, rather than that
		// they might throw anything Throwable. This allows us to
		// test that individual arguments to invocations are being
		// examined.

		protected ThrowableSet mightThrow(SootMethod m) {
			return ThrowableSet.myManager.EMPTY;
		}
	}

	UnitThrowAnalysis unitAnalysis;
	UnitThrowAnalysis immaculateAnalysis;

	// A collection of Grimp values and expressions used in various tests:
	protected StaticFieldRef floatStaticFieldRef;
	protected Local floatLocal;
	protected FloatConstant floatConstant;
	protected Local floatConstantLocal;
	protected InstanceFieldRef floatInstanceFieldRef;
	protected ArrayRef floatArrayRef;
	protected VirtualInvokeExpr floatVirtualInvoke;
	protected StaticInvokeExpr floatStaticInvoke;

	private ExceptionTestUtility utility;

	@Before
	public void setUp() {
		unitAnalysis = new UnitThrowAnalysis();
		immaculateAnalysis = new ImmaculateInvokeUnitThrowAnalysis();

		// Ensure the Exception classes we need are represented in Soot:
		utility = new ExceptionTestUtility();

		List voidList = new ArrayList();
		SootClass bogusClass = new SootClass("BogusClass", myScene, myOptions, myPackageNamer);
		bogusClass.addMethod(myScene.makeSootMethod("floatFunction", voidList, primeTypeCollector.getFloatType()));
		bogusClass.addMethod(myScene.makeSootMethod("floatFunction",
				Arrays.asList(new Type[] { primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), }), primeTypeCollector.getFloatType(), Modifier.STATIC));
		SootFieldRef nanFieldRef = myScene.makeFieldRef(myScene.getSootClass("java.lang.Float"), "NaN",
				primeTypeCollector.getFloatType(), true);
		floatStaticFieldRef = myGrimp.newStaticFieldRef(nanFieldRef);
		floatLocal = myGrimp.newLocal("local", primeTypeCollector.getFloatType());
		floatConstant = FloatConstant.v(33.42f);
		floatConstantLocal = myGrimp.newLocal("local", RefType.v("soot.jimple.FloatConstant"));
		SootFieldRef valueFieldRef = myScene.makeFieldRef(bogusClass, "value", primeTypeCollector.getFloatType(), false);
		floatInstanceFieldRef = myGrimp.newInstanceFieldRef(floatConstantLocal, valueFieldRef);
		floatArrayRef = myGrimp.newArrayRef(myJimple.newLocal("local1", primeTypeCollector.getFloatType()), IntConstant.v(0));
		floatVirtualInvoke = myGrimp.newVirtualInvokeExpr(floatConstantLocal,
				myScene.makeMethodRef(bogusClass, "floatFunction", voidList, primeTypeCollector.getFloatType(), false), voidList);
		floatStaticInvoke = myGrimp.newStaticInvokeExpr(
				myScene.makeMethodRef(bogusClass, "floatFunction",
						Arrays.asList(new Type[] { primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), }), primeTypeCollector.getFloatType(), true),
				Arrays.asList(new Value[] { floatStaticFieldRef, floatArrayRef, }));
	}

	@Test
	public void testJBreakpointStmt() {
		Stmt s = myGrimp.newBreakpointStmt();
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGBreakpointStmt() {
		Stmt s = myGrimp.newBreakpointStmt();
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Ignore("Fails")
	@Test
	public void testJInvokeStmt() {
		List voidList = new ArrayList();
		Stmt s = myJimple.newInvokeStmt(
				myJimple.newVirtualInvokeExpr(myJimple.newLocal("local1", RefType.v("java.lang.Object",myScene)),
						myScene.makeMethodRef(myScene.getSootClass("java.lang.Object"), "wait", voidList,
								primeTypeCollector.getVoidType(), false),
						voidList));
		ExceptionHashSet expectedRep = new ExceptionHashSet(utility.VM_AND_RESOLVE_METHOD_ERRORS_REP);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		ExceptionHashSet expectedCatch = new ExceptionHashSet(utility.VM_AND_RESOLVE_METHOD_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertTrue(
				ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, immaculateAnalysis.mightThrow(s)));
		assertEquals(expectedCatch, utility.catchableSubset(immaculateAnalysis.mightThrow(s)));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		SootClass bogusClass = new SootClass("BogusClass", myScene, myOptions, myPackageNamer);
		bogusClass.addMethod(myScene.makeSootMethod("emptyMethod", voidList, primeTypeCollector.getVoidType(), Modifier.STATIC));
		s = myJimple.newInvokeStmt(myJimple.newStaticInvokeExpr(
				myScene.makeMethodRef(bogusClass, "emptyMethod", voidList, primeTypeCollector.getVoidType(), true), voidList));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_ERRORS_REP, Collections.EMPTY_SET,
				immaculateAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_ERRORS_PLUS_SUPERTYPES,
				utility.catchableSubset(immaculateAnalysis.mightThrow(s)));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Ignore("Fails")
	@Test
	public void testGInvokeStmt() {
		List voidList = new ArrayList();
		Stmt s = myGrimp.newInvokeStmt(
				myGrimp.newVirtualInvokeExpr(myGrimp.newLocal("local1", RefType.v("java.lang.Object",myScene)),
						myScene.makeMethodRef(myScene.getSootClass("java.lang.Object"), "wait", voidList,
								primeTypeCollector.getVoidType(), false),
						voidList));
		ExceptionHashSet expectedRep = new ExceptionHashSet(utility.VM_AND_RESOLVE_METHOD_ERRORS_REP);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		ExceptionHashSet expectedCatch = new ExceptionHashSet(utility.VM_AND_RESOLVE_METHOD_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertTrue(
				ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, immaculateAnalysis.mightThrow(s)));
		assertEquals(expectedCatch, utility.catchableSubset(immaculateAnalysis.mightThrow(s)));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		SootClass bogusClass = new SootClass("BogusClass", myScene, myOptions, myPackageNamer);
		bogusClass.addMethod(myScene.makeSootMethod("emptyMethod", voidList, primeTypeCollector.getVoidType(), Modifier.STATIC));
		s = myJimple.newInvokeStmt(myJimple.newStaticInvokeExpr(
				myScene.makeMethodRef(bogusClass, "emptyMethod", voidList, primeTypeCollector.getVoidType(), true), voidList));
		s = myGrimp.newInvokeStmt(myGrimp.newStaticInvokeExpr(
				myScene.makeMethodRef(bogusClass, "emptyMethod", voidList, primeTypeCollector.getVoidType(), true), voidList));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_ERRORS_REP, Collections.EMPTY_SET,
				immaculateAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_ERRORS_PLUS_SUPERTYPES,
				utility.catchableSubset(immaculateAnalysis.mightThrow(s)));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJAssignStmt() {

		// local0 = 0
		Stmt s = myJimple.newAssignStmt(myJimple.newLocal("local0", primeTypeCollector.getIntType()), IntConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		ArrayRef arrayRef = myJimple.newArrayRef(
				myJimple.newLocal("local1", ArrayType.v(RefType.v("java.lang.Object",myScene), 1)), IntConstant.v(0));
		Local scalarRef = myJimple.newLocal("local2", RefType.v("java.lang.Object",myScene));

		// local2 = local1[0]
		s = myJimple.newAssignStmt(scalarRef, arrayRef);

		Set<RefLikeType> expectedRep = new ExceptionHashSet<RefLikeType>(utility.VM_ERRORS);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		expectedRep.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.<AnySubType>emptySet(),
				unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		// local1[0] = local2
		s = myJimple.newAssignStmt(arrayRef, scalarRef);
		expectedRep.add(utility.ARRAY_STORE_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		expectedCatch.add(utility.ARRAY_STORE_EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGAssignStmt() {

		// local0 = 0
		Stmt s = myGrimp.newAssignStmt(myGrimp.newLocal("local0", primeTypeCollector.getIntType()), IntConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		ArrayRef arrayRef = myGrimp.newArrayRef(
				myGrimp.newLocal("local1", ArrayType.v(RefType.v("java.lang.Object",myScene), 1)), IntConstant.v(0));
		Local scalarRef = myGrimp.newLocal("local2", RefType.v("java.lang.Object",myScene));

		// local2 = local1[0]
		s = myGrimp.newAssignStmt(scalarRef, arrayRef);

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		expectedRep.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		// local1[0] = local2
		s = myGrimp.newAssignStmt(arrayRef, scalarRef);
		expectedRep.add(utility.ARRAY_STORE_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		expectedCatch.add(utility.ARRAY_STORE_EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJIdentityStmt() {

		Stmt s = myJimple.newIdentityStmt(myGrimp.newLocal("local0", primeTypeCollector.getIntType()),
				myJimple.newCaughtExceptionRef());
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		s = myJimple.newIdentityStmt(myGrimp.newLocal("local0", RefType.v("java.lang.NullPointerException")),
				myJimple.newThisRef(RefType.v("java.lang.NullPointerException")));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		s = myJimple.newIdentityStmt(myGrimp.newLocal("local0", RefType.v("java.lang.NullPointerException")),
				myJimple.newParameterRef(RefType.v("java.lang.NullPointerException"), 0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGIdentityStmt() {

		Stmt s = myGrimp.newIdentityStmt(myGrimp.newLocal("local0", primeTypeCollector.getIntType()),
				myGrimp.newCaughtExceptionRef());
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		s = myGrimp.newIdentityStmt(myGrimp.newLocal("local0", RefType.v("java.lang.NullPointerException")),
				myGrimp.newThisRef(RefType.v("java.lang.NullPointerException")));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		s = myGrimp.newIdentityStmt(myGrimp.newLocal("local0", RefType.v("java.lang.NullPointerException")),
				myGrimp.newParameterRef(RefType.v("java.lang.NullPointerException"), 0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJEnterMonitorStmt() {
		Stmt s = myJimple.newEnterMonitorStmt(StringConstant.v("test"));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGEnterMonitorStmt() {
		Stmt s = myGrimp.newEnterMonitorStmt(StringConstant.v("test"));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);

		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJExitMonitorStmt() {
		Stmt s = myJimple.newExitMonitorStmt(StringConstant.v("test"));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGExitMonitorStmt() {
		Stmt s = myGrimp.newExitMonitorStmt(StringConstant.v("test"));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);

		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJGotoStmt() {
		Stmt nop = myJimple.newNopStmt();
		Stmt s = myJimple.newGotoStmt(nop);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGGotoStmt() {
		Stmt nop = myGrimp.newNopStmt();
		Stmt s = myGrimp.newGotoStmt(nop);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJIfStmt() {
		IfStmt s = myJimple.newIfStmt(myJimple.newEqExpr(IntConstant.v(1), IntConstant.v(1)), (Unit) null);
		s.setTarget(s); // A very tight infinite loop.
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGIfStmt() {
		IfStmt s = myGrimp.newIfStmt(myGrimp.newEqExpr(IntConstant.v(1), IntConstant.v(1)), (Unit) null);
		s.setTarget(s); // A very tight infinite loop.
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJLookupSwitchStmt() {
		Stmt target = myJimple.newAssignStmt(myJimple.newLocal("local0", primeTypeCollector.getIntType()), IntConstant.v(0));
		Stmt s = myJimple.newLookupSwitchStmt(IntConstant.v(1), Collections.singletonList(IntConstant.v(1)),
				Collections.singletonList(target), target);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGLookupSwitchStmt() {
		Stmt target = myGrimp.newAssignStmt(myGrimp.newLocal("local0", primeTypeCollector.getIntType()), IntConstant.v(0));
		Stmt s = myGrimp.newLookupSwitchStmt(IntConstant.v(1), Arrays.asList(new Value[] { IntConstant.v(1) }),
				Arrays.asList(new Unit[] { target }), target);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJNopStmt() {
		Stmt s = myJimple.newNopStmt();
		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGNopStmt() {
		Stmt s = myGrimp.newNopStmt();
		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
	}

	@Ignore("Fails")
	@Test
	public void testJReturnStmt() {
		Stmt s = myJimple.newReturnStmt(IntConstant.v(1));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Ignore("Fails")
	@Test
	public void testGReturnStmt() {
		Stmt s = myGrimp.newReturnStmt(IntConstant.v(1));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Ignore("Fails")
	@Test
	public void testJReturnVoidStmt() {
		Stmt s = myJimple.newReturnVoidStmt();

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Ignore("Fails")
	@Test
	public void testGReturnVoidStmt() {
		Stmt s = myGrimp.newReturnVoidStmt();

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.ILLEGAL_MONITOR_STATE_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJTableSwitchStmt() {
		Stmt target = myJimple.newAssignStmt(myJimple.newLocal("local0", primeTypeCollector.getIntType()), IntConstant.v(0));
		Stmt s = myJimple.newTableSwitchStmt(IntConstant.v(1), 0, 1, Arrays.asList(new Unit[] { target }), target);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGTableSwitchStmt() {
		Stmt target = myGrimp.newAssignStmt(myGrimp.newLocal("local0", primeTypeCollector.getIntType()), IntConstant.v(0));
		Stmt s = myGrimp.newTableSwitchStmt(IntConstant.v(1), 0, 1, Arrays.asList(new Unit[] { target }), target);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJThrowStmt() {

		// First test with an argument that is included in
		// PERENNIAL_THROW_EXCEPTIONS.
		ThrowStmt s = myJimple
				.newThrowStmt(myJimple.newLocal("local0", RefType.v("java.lang.NullPointerException")));
		Set expectedRep = new ExceptionHashSet(utility.PERENNIAL_THROW_EXCEPTIONS);
		expectedRep.remove(utility.NULL_POINTER_EXCEPTION);
		expectedRep.add(AnySubType.v(utility.NULL_POINTER_EXCEPTION));
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.PERENNIAL_THROW_EXCEPTIONS_PLUS_SUPERTYPES,
				utility.catchableSubset(unitAnalysis.mightThrow(s)));

		// Throw a local of type IncompatibleClassChangeError.
		Local local = myJimple.newLocal("local1", utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);
		s.setOp(local);
		expectedRep = new ExceptionHashSet(utility.THROW_PLUS_INCOMPATIBLE_CLASS_CHANGE);
		expectedRep.remove(utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);
		expectedRep.add(AnySubType.v(utility.INCOMPATIBLE_CLASS_CHANGE_ERROR));
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.THROW_PLUS_INCOMPATIBLE_CLASS_CHANGE_PLUS_SUBTYPES_PLUS_SUPERTYPES,
				utility.catchableSubset(unitAnalysis.mightThrow(s)));

		// Throw a local of unknown type.
		local = myJimple.newLocal("local1", soot.UnknownType.v());
		s.setOp(local);
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testGThrowStmt() {
		ThrowStmt s = myGrimp.newThrowStmt(myGrimp.newLocal("local0", RefType.v("java.util.zip.ZipException")));

		Set expectedRep = new ExceptionHashSet(utility.PERENNIAL_THROW_EXCEPTIONS);
		expectedRep.add(AnySubType.v(myScene.getRefType("java.util.zip.ZipException")));
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));

		Set expectedCatch = new ExceptionHashSet(utility.PERENNIAL_THROW_EXCEPTIONS_PLUS_SUPERTYPES);
		// We don't need to add java.util.zip.ZipException, since it is not
		// in the universe of test Throwables.
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(s)));

		// Now throw a new IncompatibleClassChangeError.
		s = myGrimp.newThrowStmt(myGrimp.newNewInvokeExpr(utility.INCOMPATIBLE_CLASS_CHANGE_ERROR,
				myScene.makeMethodRef(utility.INCOMPATIBLE_CLASS_CHANGE_ERROR.getSootClass(), "void <init>",
						Collections.EMPTY_LIST, primeTypeCollector.getVoidType(), false),
				new ArrayList()));
		assertTrue(ExceptionTestUtility.sameMembers(utility.THROW_PLUS_INCOMPATIBLE_CLASS_CHANGE, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(s)));
		assertEquals(utility.THROW_PLUS_INCOMPATIBLE_CLASS_CHANGE_PLUS_SUPERTYPES,
				utility.catchableSubset(unitAnalysis.mightThrow(s)));

		// Throw a local of type IncompatibleClassChangeError.
		Local local = myGrimp.newLocal("local1", utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);
		s.setOp(local);
		expectedRep = new ExceptionHashSet(utility.PERENNIAL_THROW_EXCEPTIONS);
		expectedRep.remove(utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);
		expectedRep.add(AnySubType.v(utility.INCOMPATIBLE_CLASS_CHANGE_ERROR));
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(s)));
		assertEquals(utility.THROW_PLUS_INCOMPATIBLE_CLASS_CHANGE_PLUS_SUBTYPES_PLUS_SUPERTYPES,
				utility.catchableSubset(unitAnalysis.mightThrow(s)));

		// Throw a local of unknown type.
		local = myJimple.newLocal("local1", soot.UnknownType.v());
		s.setOp(local);
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(s)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(s)));
	}

	@Test
	public void testJArrayRef() {
		ArrayRef arrayRef = myJimple.newArrayRef(
				myJimple.newLocal("local1", ArrayType.v(RefType.v("java.lang.Object",myScene), 1)), IntConstant.v(0));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		expectedRep.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(arrayRef)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(arrayRef)));
	}

	@Test
	public void testGArrayRef() {
		ArrayRef arrayRef = myGrimp.newArrayRef(
				myGrimp.newLocal("local1", ArrayType.v(RefType.v("java.lang.Object",myScene), 1)), IntConstant.v(0));

		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		expectedRep.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(arrayRef)));

		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(arrayRef)));
	}

	@Test
	public void testJDivExpr() {
		Set vmAndArithmetic = new ExceptionHashSet(utility.VM_ERRORS);
		vmAndArithmetic.add(utility.ARITHMETIC_EXCEPTION);
		Set vmAndArithmeticAndSupertypes = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		vmAndArithmeticAndSupertypes.add(utility.ARITHMETIC_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.RUNTIME_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.EXCEPTION);

		Local intLocal = myJimple.newLocal("intLocal", primeTypeCollector.getIntType());
		Local longLocal = myJimple.newLocal("longLocal", primeTypeCollector.getLongType());
		Local floatLocal = myJimple.newLocal("floatLocal", primeTypeCollector.getFloatType());
		Local doubleLocal = myJimple.newLocal("doubleLocal", primeTypeCollector.getDoubleType());

		DivExpr v = myJimple.newDivExpr(intLocal, IntConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(intLocal, IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(IntConstant.v(0), IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(intLocal, intLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(longLocal, LongConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(longLocal, LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(LongConstant.v(0), LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(longLocal, longLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(floatLocal, FloatConstant.v(0.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(floatLocal, FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(FloatConstant.v(0), FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(floatLocal, floatLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(doubleLocal, DoubleConstant.v(0.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(doubleLocal, DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(DoubleConstant.v(0), DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newDivExpr(doubleLocal, doubleLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testGDivExpr() {
		Set vmAndArithmetic = new ExceptionHashSet(utility.VM_ERRORS);
		vmAndArithmetic.add(utility.ARITHMETIC_EXCEPTION);
		Set vmAndArithmeticAndSupertypes = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		vmAndArithmeticAndSupertypes.add(utility.ARITHMETIC_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.RUNTIME_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.EXCEPTION);

		Local intLocal = myGrimp.newLocal("intLocal", primeTypeCollector.getIntType());
		Local longLocal = myGrimp.newLocal("longLocal", primeTypeCollector.getLongType());
		Local floatLocal = myGrimp.newLocal("floatLocal", primeTypeCollector.getFloatType());
		Local doubleLocal = myGrimp.newLocal("doubleLocal", primeTypeCollector.getDoubleType());

		DivExpr v = myGrimp.newDivExpr(intLocal, IntConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(intLocal, IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(IntConstant.v(0), IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(intLocal, intLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(myGrimp.newAddExpr(intLocal, intLocal), myGrimp.newMulExpr(intLocal, intLocal));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(longLocal, LongConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(longLocal, LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(LongConstant.v(0), LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(longLocal, longLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(myGrimp.newAddExpr(longLocal, longLocal),
				myGrimp.newMulExpr(longLocal, longLocal));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(floatLocal, FloatConstant.v(0.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(floatLocal, FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(FloatConstant.v(0), FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(floatLocal, floatLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(doubleLocal, DoubleConstant.v(0.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(doubleLocal, DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(DoubleConstant.v(0), DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newDivExpr(doubleLocal, doubleLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testJRemExpr() {
		Set vmAndArithmetic = new ExceptionHashSet(utility.VM_ERRORS);
		vmAndArithmetic.add(utility.ARITHMETIC_EXCEPTION);
		Set vmAndArithmeticAndSupertypes = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		vmAndArithmeticAndSupertypes.add(utility.ARITHMETIC_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.RUNTIME_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.EXCEPTION);

		Local intLocal = myJimple.newLocal("intLocal", primeTypeCollector.getIntType());
		Local longLocal = myJimple.newLocal("longLocal", primeTypeCollector.getLongType());
		Local floatLocal = myJimple.newLocal("floatLocal", primeTypeCollector.getFloatType());
		Local doubleLocal = myJimple.newLocal("doubleLocal", primeTypeCollector.getDoubleType());

		RemExpr v = myJimple.newRemExpr(intLocal, IntConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(intLocal, IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(IntConstant.v(0), IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(intLocal, intLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(longLocal, LongConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(longLocal, LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(LongConstant.v(0), LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(longLocal, longLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(floatLocal, FloatConstant.v(0.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(floatLocal, FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(FloatConstant.v(0), FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(floatLocal, floatLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(doubleLocal, DoubleConstant.v(0.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(doubleLocal, DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(DoubleConstant.v(0), DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newRemExpr(doubleLocal, doubleLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testGRemExpr() {
		Set vmAndArithmetic = new ExceptionHashSet(utility.VM_ERRORS);
		vmAndArithmetic.add(utility.ARITHMETIC_EXCEPTION);
		Set vmAndArithmeticAndSupertypes = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		vmAndArithmeticAndSupertypes.add(utility.ARITHMETIC_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.RUNTIME_EXCEPTION);
		vmAndArithmeticAndSupertypes.add(utility.EXCEPTION);

		Local intLocal = myGrimp.newLocal("intLocal", primeTypeCollector.getIntType());
		Local longLocal = myGrimp.newLocal("longLocal", primeTypeCollector.getLongType());
		Local floatLocal = myGrimp.newLocal("floatLocal", primeTypeCollector.getFloatType());
		Local doubleLocal = myGrimp.newLocal("doubleLocal", primeTypeCollector.getDoubleType());

		RemExpr v = myGrimp.newRemExpr(intLocal, IntConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(intLocal, IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(IntConstant.v(0), IntConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(intLocal, intLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(myGrimp.newAddExpr(intLocal, intLocal), myGrimp.newMulExpr(intLocal, intLocal));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(longLocal, LongConstant.v(0));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(longLocal, LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(LongConstant.v(0), LongConstant.v(2));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(longLocal, longLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(myGrimp.newAddExpr(longLocal, longLocal),
				myGrimp.newMulExpr(longLocal, longLocal));
		assertTrue(
				ExceptionTestUtility.sameMembers(vmAndArithmetic, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(vmAndArithmeticAndSupertypes, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(floatLocal, FloatConstant.v(0.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(floatLocal, FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(FloatConstant.v(0), FloatConstant.v(2.0f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(floatLocal, floatLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(doubleLocal, DoubleConstant.v(0.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(doubleLocal, DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(DoubleConstant.v(0), DoubleConstant.v(2.0));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newRemExpr(doubleLocal, doubleLocal);
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testJBinOpExp() {
		Value v = myJimple.newAddExpr(IntConstant.v(456), myJimple.newLocal("local", primeTypeCollector.getIntType()));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newOrExpr(myJimple.newLocal("local", primeTypeCollector.getLongType()), LongConstant.v(33));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newLeExpr(myJimple.newLocal("local", primeTypeCollector.getFloatType()), FloatConstant.v(33.42f));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myJimple.newEqExpr(DoubleConstant.v(-33.45e-3), myJimple.newLocal("local", primeTypeCollector.getDoubleType()));
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Ignore("Fails")
	@Test
	public void testGBinOpExp() {
		Value v = myGrimp.newAddExpr(floatStaticFieldRef, floatConstant);
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_ERRORS_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(v)));
		assertEquals(utility.ALL_TEST_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newOrExpr(v, floatConstant);
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_ERRORS_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(v)));
		assertEquals(utility.ALL_TEST_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		Set expectedRep = new ExceptionHashSet(utility.ALL_ERRORS_REP);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);

		Set expectedCatch = new ExceptionHashSet(utility.ALL_TEST_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);

		v = myGrimp.newLeExpr(floatInstanceFieldRef, v);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		v = myGrimp.newEqExpr(v, floatVirtualInvoke);
		assertTrue(
				ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, immaculateAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(immaculateAnalysis.mightThrow(v)));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(v)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		expectedRep.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.ARRAY_INDEX_OUT_OF_BOUNDS_EXCEPTION);
		expectedCatch.add(utility.INDEX_OUT_OF_BOUNDS_EXCEPTION);

		v = myGrimp.newNeExpr(v, floatStaticInvoke);
		assertEquals(expectedCatch, utility.catchableSubset(immaculateAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(immaculateAnalysis.mightThrow(v)));
		assertTrue(ExceptionTestUtility.sameMembers(utility.ALL_THROWABLES_REP, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(v)));
		assertEquals(utility.ALL_TEST_THROWABLES, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testJCastExpr() {
		// First an upcast that can be statically proved safe.
		Value v = myJimple.newCastExpr(myJimple.newLocal("local", utility.INCOMPATIBLE_CLASS_CHANGE_ERROR),
				utility.LINKAGE_ERROR);
		Set expectedRep = new ExceptionHashSet(utility.VM_AND_RESOLVE_CLASS_ERRORS_REP);
		Set expectedCatch = new ExceptionHashSet(utility.VM_AND_RESOLVE_CLASS_ERRORS_PLUS_SUPERTYPES);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		// Then a vacuous cast which can be statically proved safe.
		v = myJimple.newCastExpr(myJimple.newLocal("local", utility.LINKAGE_ERROR), utility.LINKAGE_ERROR);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		// Finally a downcast which is not necessarily safe:
		v = myJimple.newCastExpr(myJimple.newLocal("local", utility.LINKAGE_ERROR),
				utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);

		expectedRep.add(utility.CLASS_CAST_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));

		expectedCatch.add(utility.CLASS_CAST_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);

		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testGCastExpr() {
		// First an upcast that can be statically proved safe.
		Value v = myGrimp.newCastExpr(myJimple.newLocal("local", utility.INCOMPATIBLE_CLASS_CHANGE_ERROR),
				utility.LINKAGE_ERROR);
		Set expectedRep = new ExceptionHashSet(utility.VM_AND_RESOLVE_CLASS_ERRORS_REP);
		Set expectedCatch = new ExceptionHashSet(utility.VM_AND_RESOLVE_CLASS_ERRORS_PLUS_SUPERTYPES);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		// Then a vacuous cast which can be statically proved safe.
		v = myJimple.newCastExpr(myJimple.newLocal("local", utility.LINKAGE_ERROR), utility.LINKAGE_ERROR);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));

		// Finally a downcast which is not necessarily safe:
		v = myJimple.newCastExpr(myJimple.newLocal("local", utility.LINKAGE_ERROR),
				utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);

		expectedRep.add(utility.CLASS_CAST_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));

		expectedCatch.add(utility.CLASS_CAST_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);

		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testGInstanceFieldRef() {
		Local local = myGrimp.newLocal("local", utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);

		Set expectedRep = new ExceptionHashSet(utility.VM_AND_RESOLVE_FIELD_ERRORS_REP);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);

		Set expectedCatch = new ExceptionHashSet(utility.VM_AND_RESOLVE_FIELD_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);

		Value v = myGrimp.newInstanceFieldRef(local, myScene.makeFieldRef(utility.THROWABLE.getSootClass(),
				"detailMessage", RefType.v("java.lang.String",myScene), false));
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testStringConstant() {
		Value v = StringConstant.v("test");
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(v)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(v)));
	}

	@Test
	public void testJLocal() {
		Local local = myJimple.newLocal("local1", utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);
		assertTrue(ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(local)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(local)));
	}

	@Test
	public void testGLocal() {
		Local local = myGrimp.newLocal("local1", utility.INCOMPATIBLE_CLASS_CHANGE_ERROR);
		assertTrue(ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET,
				unitAnalysis.mightThrow(local)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(local)));
	}

	@Test
	public void testBAddInst() {
		soot.baf.AddInst i = soot.baf.myBaf.newAddInst(primeTypeCollector.getIntType());
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(i)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(i)));
	}

	@Test
	public void testBAndInst() {
		soot.baf.AndInst i = soot.baf.myBaf.newAndInst(primeTypeCollector.getIntType());
		assertTrue(
				ExceptionTestUtility.sameMembers(utility.VM_ERRORS, Collections.EMPTY_SET, unitAnalysis.mightThrow(i)));
		assertEquals(utility.VM_ERRORS_PLUS_SUPERTYPES, utility.catchableSubset(unitAnalysis.mightThrow(i)));
	}

	@Test
	public void testBArrayLengthInst() {
		soot.baf.ArrayLengthInst i = soot.baf.myBaf.newArrayLengthInst();
		Set expectedRep = new ExceptionHashSet(utility.VM_ERRORS);
		expectedRep.add(utility.NULL_POINTER_EXCEPTION);
		assertTrue(ExceptionTestUtility.sameMembers(expectedRep, Collections.EMPTY_SET, unitAnalysis.mightThrow(i)));
		Set expectedCatch = new ExceptionHashSet(utility.VM_ERRORS_PLUS_SUPERTYPES);
		expectedCatch.add(utility.NULL_POINTER_EXCEPTION);
		expectedCatch.add(utility.RUNTIME_EXCEPTION);
		expectedCatch.add(utility.EXCEPTION);
		assertEquals(expectedCatch, utility.catchableSubset(unitAnalysis.mightThrow(i)));
	}
}
