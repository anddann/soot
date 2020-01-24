package soot.jimple.toolkits.ide.icfg;

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

import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;

import heros.SynchronizedBy;
import heros.solver.IDESolver;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import soot.ArrayType;
import soot.Body;
import soot.FastHierarchy;
import soot.Local;
import soot.NullType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.SourceLocator;
import soot.Transform;
import soot.Unit;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.toolkits.pointer.LocalMustNotAliasAnalysis;
import soot.options.Options;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.graph.interaction.InteractionHandler;

/**
 * This is an implementation of AbstractJimpleBasedICFG that computes the ICFG on-the-fly. In other words, it can be used
 * without pre-computing a call graph. Instead this implementation resolves calls through Class Hierarchy Analysis (CHA), as
 * implemented through FastHierarchy. The CHA is supported by LocalMustNotAliasAnalysis, which is used to determine cases
 * where the concrete type of an object at an InvokeVirtual or InvokeInterface callsite is known. In these cases the call can
 * be resolved concretely, i.e., to a single target.
 *
 * To be sound, for InvokeInterface calls that cannot be resolved concretely, OnTheFlyJimpleBasedICFG requires that all
 * classes on the classpath be loaded at least to signatures. This must be done before the FastHierarchy is computed such
 * that the hierarchy is intact. Clients should call {@link #loadAllClassesOnClassPathToSignatures()} to load all required
 * classes to this level.
 *
 * @see FastHierarchy#resolveConcreteDispatch(SootClass, SootMethod)
 * @see FastHierarchy#resolveAbstractDispatch(SootClass, SootMethod)
 */
public class OnTheFlyJimpleBasedICFG extends AbstractJimpleBasedICFG {

  @SynchronizedBy("by use of synchronized LoadingCache class")
  protected final LoadingCache<Body, LocalMustNotAliasAnalysis> bodyToLMNAA;

  @SynchronizedBy("by use of synchronized LoadingCache class")
  protected final LoadingCache<Unit, Set<SootMethod>> unitToCallees
      = IDESolver.DEFAULT_CACHE_BUILDER.build(new CacheLoader<Unit, Set<SootMethod>>() {
        @Override
        public Set<SootMethod> load(Unit u) throws Exception {
          Stmt stmt = (Stmt) u;
          InvokeExpr ie = stmt.getInvokeExpr();
          FastHierarchy fastHierarchy = myScene.getFastHierarchy();
          // FIXME Handle Thread.start etc.
          if (ie instanceof InstanceInvokeExpr) {
            if (ie instanceof SpecialInvokeExpr) {
              // special
              return Collections.singleton(ie.getMethod());
            } else {
              // virtual and interface
              InstanceInvokeExpr iie = (InstanceInvokeExpr) ie;
              Local base = (Local) iie.getBase();
              RefType concreteType = bodyToLMNAA.getUnchecked(getBodyOf(u)).concreteType(base, stmt);
              if (concreteType != null) {
                // the base variable definitely points to a single concrete type
                SootMethod singleTargetMethod
                    = fastHierarchy.resolveConcreteDispatch(concreteType.getSootClass(), iie.getMethod());
                return Collections.singleton(singleTargetMethod);
              } else {
                SootClass baseTypeClass;
                if (base.getType() instanceof RefType) {
                  RefType refType = (RefType) base.getType();
                  baseTypeClass = refType.getSootClass();
                } else if (base.getType() instanceof ArrayType) {
                  baseTypeClass = myScene.getSootClass("java.lang.Object");
                } else if (base.getType() instanceof NullType) {
                  // if the base is definitely null then there is no call target
                  return Collections.emptySet();
                } else {
                  throw new InternalError("Unexpected base type:" + base.getType());
                }
                return fastHierarchy.resolveAbstractDispatch(baseTypeClass, iie.getMethod());
              }
            }
          } else {
            // static
            return Collections.singleton(ie.getMethod());
          }
        }
      });

  @SynchronizedBy("explicit lock on data structure")
  protected Map<SootMethod, Set<Unit>> methodToCallers = new HashMap<SootMethod, Set<Unit>>();
  private InteractionHandler myInteractionHandler;
  private Scene myScene;
    private Options myOptions;

    public OnTheFlyJimpleBasedICFG(final Options myOptions, InteractionHandler myInteractionHandler,
      ThrowAnalysis throwAnalysis, SootMethod... entryPoints) {
    this(Arrays.asList(entryPoints), throwAnalysis, myOptions, myInteractionHandler);

  }

  public OnTheFlyJimpleBasedICFG(Collection<SootMethod> entryPoints, ThrowAnalysis throwAnalysis, final Options myOptions,
      InteractionHandler myInteractionHandler) {
    super(throwAnalysis);
    this.myInteractionHandler = myInteractionHandler;
    for (SootMethod m : entryPoints) {
      initForMethod(m);
    }
    bodyToLMNAA = IDESolver.DEFAULT_CACHE_BUILDER.build(new CacheLoader<Body, LocalMustNotAliasAnalysis>() {
      @Override
      public LocalMustNotAliasAnalysis load(Body body) throws Exception {
        return new LocalMustNotAliasAnalysis(getOrCreateUnitGraph(body), body, myOptions.interactive_mode(),
            OnTheFlyJimpleBasedICFG.this.myInteractionHandler);
      }
    });
    ;
  }

  protected Body initForMethod(SootMethod m) {
    assert myScene.hasFastHierarchy();
    Body b = null;
    if (m.isConcrete()) {
      SootClass declaringClass = m.getDeclaringClass();
      ensureClassHasBodies(declaringClass);
      synchronized (myScene) {
        b = m.retrieveActiveBody();
      }
      if (b != null) {
        for (Unit u : b.getUnits()) {
          if (!setOwnerStatement(u, b)) {
            // if the unit was registered already then so were all units;
            // simply skip the rest
            break;
          }
        }
      }
    }
    assert myScene.hasFastHierarchy();
    return b;
  }

  private synchronized void ensureClassHasBodies(SootClass cl) {
    assert myScene.hasFastHierarchy();
    if (cl.resolvingLevel() < SootClass.BODIES) {
      myScene.forceResolve(cl.getName(), SootClass.BODIES);
      myScene.getOrMakeFastHierarchy();
    }
    assert myScene.hasFastHierarchy();
  }

  @Override
  public Set<SootMethod> getCalleesOfCallAt(Unit u) {
    Set<SootMethod> targets = unitToCallees.getUnchecked(u);
    for (SootMethod m : targets) {
      addCallerForMethod(u, m);
      initForMethod(m);
    }
    return targets;
  }

  private void addCallerForMethod(Unit callSite, SootMethod target) {
    synchronized (methodToCallers) {
      Set<Unit> callers = methodToCallers.get(target);
      if (callers == null) {
        callers = new HashSet<Unit>();
        methodToCallers.put(target, callers);
      }
      callers.add(callSite);
    }
  }

  @Override
  public Set<Unit> getCallersOf(SootMethod m) {
    Set<Unit> callers = methodToCallers.get(m);
    return callers == null ? Collections.<Unit>emptySet() : callers;

    // throw new UnsupportedOperationException("This class is not suited for unbalanced problems");
  }





}
