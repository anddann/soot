package soot.jimple.toolkits.annotation;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Jennifer Lhotak
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

import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.PhaseOptions;
import soot.Scene;
import soot.SideEffectTester;
import soot.jimple.NaiveSideEffectTester;
import soot.jimple.toolkits.pointer.PASideEffectTester;
import soot.jimple.toolkits.scalar.PessimisticAvailableExpressionsAnalysis;
import soot.jimple.toolkits.scalar.SlowAvailableExpressionsAnalysis;
import soot.options.AETOptions;
import soot.options.Options;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.interaction.InteractionHandler;
import soot.util.PhaseDumper;

/**
 * A body transformer that records avail expression information in tags. - both pessimistic and optimistic options
 */
public class AvailExprTagger extends BodyTransformer {

  private Scene myScene;
  private ThrowableSet.Manager myManager;
  private Options myOptions;
  private PhaseDumper myPhaseDumper;
  private InteractionHandler myInteractionHandler;

  @Inject
  public AvailExprTagger(Scene myScene, ThrowableSet.Manager myManager, Options myOptions, PhaseDumper myPhaseDumper, InteractionHandler myInteractionHandler) {
    this.myScene = myScene;
    this.myManager = myManager;
    this.myOptions = myOptions;
    this.myPhaseDumper = myPhaseDumper;
    this.myInteractionHandler = myInteractionHandler;
  }

  protected void internalTransform(Body b, String phaseName, Map opts) {

    SideEffectTester sideEffect;
    if (myScene.hasCallGraph() && !PhaseOptions.getBoolean(opts, "naive-side-effect")) {
      sideEffect = new PASideEffectTester(myScene);
    } else {
      sideEffect = new NaiveSideEffectTester();
    }
    sideEffect.newMethod(b.getMethod());

    AETOptions options = new AETOptions(opts);
    if (options.kind() == AETOptions.kind_optimistic) {
      new SlowAvailableExpressionsAnalysis(new ExceptionalUnitGraph(b,  myManager, myOptions.omit_excepting_unit_edges(), myPhaseDumper, myScene),myOptions.interactive_mode(), myInteractionHandler);
    } else {
      new PessimisticAvailableExpressionsAnalysis(new ExceptionalUnitGraph(b,  myManager, myOptions.omit_excepting_unit_edges(), myPhaseDumper, myScene), b.getMethod(), sideEffect, myInteractionHandler, myOptions.interactive_mode());
    }
  }
}
