package soot.jimple.toolkits.annotation.purity;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2005 Antoine Mine
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

import java.util.Map;

import com.google.inject.Inject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Scene;
import soot.SceneTransformer;
import soot.SourceLocator;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.options.Options;
import soot.options.PurityOptions;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.graph.interaction.InteractionHandler;
import soot.util.PhaseDumper;

/**
 * Purity analysis phase.
 *
 * TODO: - test, test, and test (and correct the potentially infinite bugs) - optimise PurityGraph, especially methodCall) -
 * find a better abstraction for exceptions (throw & catch) - output nicer graphs (especially clusters!)
 */
public class PurityAnalysis extends SceneTransformer {
  private static final Logger logger = LoggerFactory.getLogger(PurityAnalysis.class);
  private Scene myScene;
  private SourceLocator mySourceLocator;
  private ThrowAnalysis throwAnalysis;
  private boolean omitExceptingUnitEdges;
  private ThrowableSet.Manager myManager;
  private PhaseDumper myPhaseDumper;
  private Options myOptions;
  private InteractionHandler myInteractionHandler;


  @Inject
  public PurityAnalysis(Scene myScene, SourceLocator mySourceLocator, ThrowAnalysis throwAnalysis, boolean omitExceptingUnitEdges, ThrowableSet.Manager myManager, PhaseDumper myPhaseDumper, Options myOptions, InteractionHandler myInteractionHandler) {

    this.myScene = myScene;
    this.mySourceLocator = mySourceLocator;
    this.throwAnalysis = throwAnalysis;
    this.omitExceptingUnitEdges = omitExceptingUnitEdges;
    this.myManager = myManager;
    this.myPhaseDumper = myPhaseDumper;
    this.myOptions = myOptions;
    this.myInteractionHandler = myInteractionHandler;
  }


  @Override
  protected void internalTransform(String phaseName, Map<String, String> options) {
    PurityOptions opts = new PurityOptions(options);

    logger.debug("[AM] Analysing purity");

    CallGraph cg = myScene.getCallGraph();

    // launch the analysis
    new PurityInterproceduralAnalysis(cg, myScene.getEntryPoints().iterator(), opts, mySourceLocator, throwAnalysis, omitExceptingUnitEdges, myManager, myPhaseDumper, myOptions, myInteractionHandler);
  }
}
