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

import java.util.Map;

import com.google.inject.Inject;
import soot.Body;
import soot.BodyTransformer;
import soot.Scene;
import soot.options.Options;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.interaction.InteractionHandler;
import soot.util.PhaseDumper;

/** A body transformer that simply calls the CastCheckEliminator analysis. */
public class CastCheckEliminatorDumper extends BodyTransformer {
  private PhaseDumper myPhaseDumper;
  private Options myOptions;
  private InteractionHandler myInteractionHandler;
  private Scene myScene;

  @Inject
  public CastCheckEliminatorDumper(PhaseDumper myPhaseDumper, Options myOptions, InteractionHandler myInteractionHandler, Scene myScene) {
    this.myPhaseDumper = myPhaseDumper;
    this.myOptions = myOptions;
    this.myInteractionHandler = myInteractionHandler;
    this.myScene = myScene;
  }


  public String getDefaultOptions() {
    return "";
  }

  protected void internalTransform(Body b, String phaseName, Map options) {
    CastCheckEliminator cce = new CastCheckEliminator(new BriefUnitGraph(b, myPhaseDumper), myOptions, myInteractionHandler, myScene);
  }
}
