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
import soot.toolkits.graph.BriefUnitGraph;
import soot.util.PhaseDumper;

/** A body transformer that simply calls the CastCheckEliminator analysis. */
public class CastCheckEliminatorDumper extends BodyTransformer {
  private PhaseDumper myPhaseDumper;

  @Inject
  public CastCheckEliminatorDumper(PhaseDumper myPhaseDumper) {
    this.myPhaseDumper = myPhaseDumper;
  }


  public String getDefaultOptions() {
    return "";
  }

  protected void internalTransform(Body b, String phaseName, Map options) {
    CastCheckEliminator cce = new CastCheckEliminator(new BriefUnitGraph(b, myPhaseDumper), myOptions, getMyInteractionHandler());
  }
}
