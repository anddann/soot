package soot.jimple.toolkits.pointer;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Ondrej Lhotak
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

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import soot.Local;
import soot.MethodOrMethodContext;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.FullObjectFactory;
import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Filter;
import soot.jimple.toolkits.callgraph.TransitiveTargets;

/** Generates side-effect information from a PointsToAnalysis. */
public class SideEffectAnalysis {
  PointsToAnalysis pa;
  CallGraph cg;
  Map<SootMethod, MethodRWSet> methodToNTReadSet = new HashMap<SootMethod, MethodRWSet>();
  Map<SootMethod, MethodRWSet> methodToNTWriteSet = new HashMap<SootMethod, MethodRWSet>();
  int rwsetcount = 0;
  TransitiveTargets tt;
  private FullObjectFactory fullObjectFactory;

  public void findNTRWSets(SootMethod method) {
    if (methodToNTReadSet.containsKey(method) && methodToNTWriteSet.containsKey(method)) {
      return;
    }

    MethodRWSet read = null;
    MethodRWSet write = null;
    for (Iterator<Unit> sIt = method.retrieveActiveBody().getUnits().iterator(); sIt.hasNext();) {
      final Stmt s = (Stmt) sIt.next();
      RWSet ntr = ntReadSet(method, s);
      if (ntr != null) {
        if (read == null) {
          read = new MethodRWSet(fullObjectFactory);
        }
        read.union(ntr);
      }
      RWSet ntw = ntWriteSet(method, s);
      if (ntw != null) {
        if (write == null) {
          write = new MethodRWSet(fullObjectFactory);
        }
        write.union(ntw);
      }
    }
    methodToNTReadSet.put(method, read);
    methodToNTWriteSet.put(method, write);
  }

  public RWSet nonTransitiveReadSet(SootMethod method) {
    findNTRWSets(method);
    return methodToNTReadSet.get(method);
  }

  public RWSet nonTransitiveWriteSet(SootMethod method) {
    findNTRWSets(method);
    return methodToNTWriteSet.get(method);
  }


  public SideEffectAnalysis(PointsToAnalysis pa, CallGraph cg, FullObjectFactory fullObjectFactory) {
    this.pa = pa;
    this.cg = cg;
    this.tt = new TransitiveTargets(cg);
    this.fullObjectFactory = fullObjectFactory;
  }

  public SideEffectAnalysis(PointsToAnalysis pa, CallGraph cg, Filter filter, FullObjectFactory fullObjectFactory) {
    // This constructor allows customization of call graph edges to
    // consider via the use of a transitive targets filter.
    // For example, using the NonClinitEdgesPred, you can create a
    // SideEffectAnalysis that will ignore static initializers
    // - R. Halpert 2006-12-02
    this.pa = pa;
    this.cg = cg;
    this.fullObjectFactory = fullObjectFactory;
    this.tt = new TransitiveTargets(cg, filter);
  }

  private RWSet ntReadSet(SootMethod method, Stmt stmt) {
    if (stmt instanceof AssignStmt) {
      AssignStmt a = (AssignStmt) stmt;
      Value r = a.getRightOp();
      return addValue(r, method, stmt);
    }
    return null;
  }

  public RWSet readSet(SootMethod method, Stmt stmt) {
    RWSet ret = null;
    Iterator<MethodOrMethodContext> targets = tt.iterator(stmt);
    while (targets.hasNext()) {
      SootMethod target = (SootMethod) targets.next();
      if (target.isNative()) {
        if (ret == null) {
          ret = new SiteRWSet();
        }
        ret.setCallsNative();
      } else if (target.isConcrete()) {
        RWSet ntr = nonTransitiveReadSet(target);
        if (ntr != null) {
          if (ret == null) {
            ret = new SiteRWSet();
          }
          ret.union(ntr);
        }
      }
    }
    if (ret == null) {
      return ntReadSet(method, stmt);
    }
    ret.union(ntReadSet(method, stmt));
    return ret;
  }

  private RWSet ntWriteSet(SootMethod method, Stmt stmt) {
    if (stmt instanceof AssignStmt) {
      AssignStmt a = (AssignStmt) stmt;
      Value l = a.getLeftOp();
      return addValue(l, method, stmt);
    }
    return null;
  }

  public RWSet writeSet(SootMethod method, Stmt stmt) {
    RWSet ret = null;
    Iterator<MethodOrMethodContext> targets = tt.iterator(stmt);
    while (targets.hasNext()) {
      SootMethod target = (SootMethod) targets.next();
      if (target.isNative()) {
        if (ret == null) {
          ret = new SiteRWSet();
        }
        ret.setCallsNative();
      } else if (target.isConcrete()) {
        RWSet ntw = nonTransitiveWriteSet(target);
        if (ntw != null) {
          if (ret == null) {
            ret = new SiteRWSet();
          }
          ret.union(ntw);
        }
      }
    }
    if (ret == null) {
      return ntWriteSet(method, stmt);
    }
    ret.union(ntWriteSet(method, stmt));
    return ret;
  }

  protected RWSet addValue(Value v, SootMethod m, Stmt s) {
    RWSet ret = null;
    if (v instanceof InstanceFieldRef) {
      InstanceFieldRef ifr = (InstanceFieldRef) v;
      PointsToSet base = pa.reachingObjects((Local) ifr.getBase());
      ret = new StmtRWSet();
      ret.addFieldRef(base, ifr.getField());
    } else if (v instanceof StaticFieldRef) {
      StaticFieldRef sfr = (StaticFieldRef) v;
      ret = new StmtRWSet();
      ret.addGlobal(sfr.getField());
    } else if (v instanceof ArrayRef) {
      ArrayRef ar = (ArrayRef) v;
      PointsToSet base = pa.reachingObjects((Local) ar.getBase());
      ret = new StmtRWSet();
      ret.addFieldRef(base, PointsToAnalysis.ARRAY_ELEMENTS_NODE);
    }
    return ret;
  }

  public String toString() {
    return "SideEffectAnalysis: PA=" + pa + " CG=" + cg;
  }
}
