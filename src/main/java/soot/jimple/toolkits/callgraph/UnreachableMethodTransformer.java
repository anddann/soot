package soot.jimple.toolkits.callgraph;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
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

import java.util.List;
import java.util.Map;
import java.util.Vector;

import com.google.inject.Inject;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.StringConstant;

public class UnreachableMethodTransformer extends BodyTransformer {

  private Scene myScene;
  private Jimple myJimple;

  @Inject
  public UnreachableMethodTransformer(Scene myScene, Jimple myJimple){

    this.myScene = myScene;
    this.myJimple = myJimple;
  }


  protected void internalTransform(Body b, String phaseName, Map options) {
    // System.out.println( "Performing UnreachableMethodTransformer" );
    ReachableMethods reachableMethods = myScene.getReachableMethods();
    SootMethod method = b.getMethod();
    // System.out.println( "Method: " + method.getName() );
    if (reachableMethods.contains(method)) {
      return;
    }

    JimpleBody body = (JimpleBody) method.getActiveBody();

    PatchingChain units = body.getUnits();
    List<Unit> list = new Vector<Unit>();

    Local tmpRef = myJimple.newLocal("tmpRef", RefType.v("java.io.PrintStream",myScene));
    body.getLocals().add(tmpRef);
    list.add(myJimple.newAssignStmt(tmpRef,
        myJimple.newStaticFieldRef(myScene.getField("<java.lang.System: java.io.PrintStream out>").makeRef())));

    SootMethod toCall = myScene.getMethod("<java.lang.Thread: void dumpStack()>");
    list.add(myJimple.newInvokeStmt(myJimple.newStaticInvokeExpr(toCall.makeRef())));

    toCall = myScene.getMethod("<java.io.PrintStream: void println(java.lang.String)>");
    list.add(myJimple.newInvokeStmt(myJimple.newVirtualInvokeExpr(tmpRef, toCall.makeRef(),
        constancFactory.createStringConstant("Executing supposedly unreachable method:"))));
    list.add(myJimple.newInvokeStmt(myJimple.newVirtualInvokeExpr(tmpRef, toCall.makeRef(),
        constancFactory.createStringConstant("\t" + method.getDeclaringClass().getName() + "." + method.getName()))));

    toCall = myScene.getMethod("<java.lang.System: void exit(int)>");
    list.add(myJimple.newInvokeStmt(myJimple.newStaticInvokeExpr(toCall.makeRef(), constancFactory.createIntConstant(1))));

    /*
     * Stmt r; if( method.getReturnType() instanceof VoidType ) { list.add( r=myJimple.newReturnVoidStmt() ); } else if(
     * method.getReturnType() instanceof RefLikeType ) { list.add( r=myJimple.newReturnStmt( myNullConstant ) ); } else
     * if( method.getReturnType() instanceof PrimType ) { if( method.getReturnType() instanceof DoubleType ) { list.add(
     * r=myJimple.newReturnStmt( constancFactory.createDoubleConstant( 0 ) ) ); } else if( method.getReturnType() instanceof LongType ) {
     * list.add( r=myJimple.newReturnStmt( constancFactory.createLongConstant( 0 ) ) ); } else if( method.getReturnType() instanceof FloatType
     * ) { list.add( r=myJimple.newReturnStmt( FloatConstant.v( 0 ) ) ); } else { list.add( r=myJimple.newReturnStmt(
     * constancFactory.createIntConstant( 0 ) ) ); } } else { throw new RuntimeException( "Wrong return method type: " + method.getReturnType()
     * ); }
     */

    /*
     * if( method.getName().equals( "<init>" ) || method.getName().equals( "<clinit>" ) ) {
     *
     * Object o = units.getFirst(); boolean insertFirst = false; while( true ) { //System.out.println( "Unit: " + o );
     * //System.out.println( "\tClass: " + o.getClass() ); if( o == null ) { insertFirst = true; break; } if( o instanceof
     * JInvokeStmt ) { JInvokeStmt stmt = (JInvokeStmt) o; if( (stmt.getInvokeExpr() instanceof SpecialInvokeExpr) ) {
     * SootMethodRef break; } } o = units.getSuccOf( o ); } if( insertFirst ) { units.insertBefore( list, units.getFirst() );
     * } else { units.insertAfter( list, o ) ; } } else {
     */
    {
      units.insertBefore(list, units.getFirst());
    }
    /*
     * ArrayList toRemove = new ArrayList(); for( Iterator sIt = units.iterator(r); sIt.hasNext(); ) { final Stmt s = (Stmt)
     * sIt.next(); if(s == r) continue; toRemove.add(s); } for( Iterator sIt = toRemove.iterator(); sIt.hasNext(); ) { final
     * Stmt s = (Stmt) sIt.next(); units.getNonPatchingChain().remove(s); } body.getTraps().clear();
     */
  }
}
