package soot.jimple.toolkits.annotation.nullcheck;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 1999 Raja Vallee-Rai
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

import java.util.Date;
import java.util.Iterator;
import java.util.Map;

import com.google.inject.Inject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.BodyTransformer;
import soot.PhaseOptions;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.LengthExpr;
import soot.jimple.MonitorStmt;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.jimple.toolkits.annotation.tags.NullCheckTag;
import soot.options.Options;
import soot.tagkit.Tag;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.FlowSet;
import soot.util.Chain;
import soot.util.PhaseDumper;

/*
ArrayRef
GetField
PutField
InvokeVirtual
InvokeSpecial
InvokeInterface
ArrayLength
-	AThrow
-	MonitorEnter
-	MonitorExit
*/

public class NullPointerChecker extends BodyTransformer {
  private static final Logger logger = LoggerFactory.getLogger(NullPointerChecker.class);
  private Options myOptions;
  private Scene myScene;
  private Jimple myJimple;
  private ThrowableSet.Manager myManager;
  private ThrowAnalysis mythrowAnalysis;
  private PhaseDumper myPhaseDumper;


  @Inject
  public NullPointerChecker(Options myOptions, Scene myScene, Jimple myJimple, ThrowableSet.Manager myManager, ThrowAnalysis mythrowAnalysis, PhaseDumper myPhaseDumper) {
    this.myOptions = myOptions;
    this.myScene = myScene;
    this.myJimple = myJimple;
    this.myManager = myManager;
    this.mythrowAnalysis = mythrowAnalysis;
    this.myPhaseDumper = myPhaseDumper;
  }


  private boolean isProfiling = false;

  private boolean enableOther = true;

  protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
    isProfiling = PhaseOptions.getBoolean(options, "profiling");
    enableOther = !PhaseOptions.getBoolean(options, "onlyarrayref");

    {
      Date start = new Date();

      if (myOptions.verbose()) {
        logger.debug("[npc] Null pointer check for " + body.getMethod().getName() + " started on " + start);
      }

      BranchedRefVarsAnalysis analysis = new BranchedRefVarsAnalysis(new ExceptionalUnitGraph(body, mythrowAnalysis, myOptions.omit_excepting_unit_edges(),   myManager,myPhaseDumper));

      SootClass counterClass = null;
      SootMethod increase = null;

      if (isProfiling) {
        counterClass = myScene.loadClassAndSupport("MultiCounter");
        increase = counterClass.getMethod("void increase(int)");
      }

      Chain<Unit> units = body.getUnits();

      Iterator<Unit> stmtIt = units.snapshotIterator();

      while (stmtIt.hasNext()) {
        Stmt s = (Stmt) stmtIt.next();

        Value obj = null;

        if (s.containsArrayRef()) {
          ArrayRef aref = s.getArrayRef();
          obj = aref.getBase();
        } else {
          if (enableOther) {
            // Throw
            if (s instanceof ThrowStmt) {
              obj = ((ThrowStmt) s).getOp();
            } else if (s instanceof MonitorStmt) {
              // Monitor enter and exit
              obj = ((MonitorStmt) s).getOp();
            } else {
              Iterator<ValueBox> boxIt;
              boxIt = s.getDefBoxes().iterator();
              while (boxIt.hasNext()) {
                ValueBox vBox = (ValueBox) boxIt.next();
                Value v = vBox.getValue();

                // putfield, and getfield
                if (v instanceof InstanceFieldRef) {
                  obj = ((InstanceFieldRef) v).getBase();
                  break;
                } else if (v instanceof InstanceInvokeExpr) {
                  // invokevirtual, invokespecial, invokeinterface
                  obj = ((InstanceInvokeExpr) v).getBase();
                  break;
                } else if (v instanceof LengthExpr) {
                  // arraylength
                  obj = ((LengthExpr) v).getOp();
                  break;
                }
              }
              boxIt = s.getUseBoxes().iterator();
              while (boxIt.hasNext()) {
                ValueBox vBox = (ValueBox) boxIt.next();
                Value v = vBox.getValue();

                // putfield, and getfield
                if (v instanceof InstanceFieldRef) {
                  obj = ((InstanceFieldRef) v).getBase();
                  break;
                } else if (v instanceof InstanceInvokeExpr) {
                  // invokevirtual, invokespecial, invokeinterface
                  obj = ((InstanceInvokeExpr) v).getBase();
                  break;
                } else if (v instanceof LengthExpr) {
                  // arraylength
                  obj = ((LengthExpr) v).getOp();
                  break;
                }
              }
            }
          }
        }

        // annotate it or now
        if (obj != null) {
          FlowSet beforeSet = (FlowSet) analysis.getFlowBefore(s);

          int vInfo = analysis.anyRefInfo(obj, beforeSet);

          boolean needCheck = (vInfo != BranchedRefVarsAnalysis.kNonNull);

          if (isProfiling) {
            int whichCounter = 5;
            if (!needCheck) {
              whichCounter = 6;
            }

            units.insertBefore(
                myJimple.newInvokeStmt(myJimple.newStaticInvokeExpr(increase.makeRef(), IntConstant.v(whichCounter))),
                s);
          }

          {
            Tag nullTag = new NullCheckTag(needCheck);
            s.addTag(nullTag);
          }
        }
      }

      Date finish = new Date();
      if (myOptions.verbose()) {
        long runtime = finish.getTime() - start.getTime();
        long mins = runtime / 60000;
        long secs = (runtime % 60000) / 1000;
        logger.debug("[npc] Null pointer checker finished. It took " + mins + " mins and " + secs + " secs.");
      }
    }
  }
}
