package soot.jimple.toolkits.callgraph;

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

import com.google.inject.Inject;

import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Scene;
import soot.SceneTransformer;
import soot.jimple.toolkits.pointer.DumbPointerAnalysis;
import soot.options.CHAOptions;

/** Builds an invoke graph using Class Hierarchy Analysis. */
public class CHATransformer extends SceneTransformer {
  private static final Logger logger = LoggerFactory.getLogger(CHATransformer.class);
  private DumbPointerAnalysis myDumbPointerAnalysis;
  private Scene myScene;

  @Inject
  public CHATransformer(DumbPointerAnalysis myDumbPointerAnalysis, Scene myScene) {
    this.myDumbPointerAnalysis = myDumbPointerAnalysis;
    this.myScene = myScene;
  }

  protected void internalTransform(String phaseName, Map<String, String> opts) {
    CHAOptions options = new CHAOptions(opts);
    CallGraphBuilder cg = options.apponly() ? new CallGraphBuilder() : new CallGraphBuilder(myDumbPointerAnalysis);
    cg.build();
    if (options.verbose()) {
      logger.debug("" + "Number of reachable methods: " + myScene.getReachableMethods().size());
    }
  }
}
