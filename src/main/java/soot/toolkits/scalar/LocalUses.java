package soot.toolkits.scalar;

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

import static soot.toolkits.scalar.LocalDefs.Factory.newLocalDefs;

import java.util.List;

import soot.Body;
import soot.Unit;
import soot.options.Options;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.graph.interaction.InteractionHandler;
import soot.util.PhaseDumper;

/**
 * Provides an interface to find the Units that use a Local defined at a given Unit.
 */
public interface LocalUses {
  static final public class Factory {
    private Factory() {
    }

    public static LocalUses newLocalUses(Body body, Options myOptions, InteractionHandler myInteractionHandler, ThrowAnalysis throwAnalysis, ThrowableSet.Manager myManager, PhaseDumper phaseDumper) {
      return newLocalUses(body, newLocalDefs(body,throwAnalysis,myManager, myOptions , phaseDumper, myInteractionHandler));
    }

    public static LocalUses newLocalUses(Body body, LocalDefs localDefs) {
      return new SimpleLocalUses(body, localDefs);
    }

    public static LocalUses newLocalUses(UnitGraph graph, Options myOptions, InteractionHandler myInteractionHandler) {
      return newLocalUses(graph.getBody(), newLocalDefs(graph, myOptions, myInteractionHandler));
    }

    public static LocalUses newLocalUses(UnitGraph graph, LocalDefs localDefs) {
      return newLocalUses(graph.getBody(), localDefs);
    }
  }

  /**
   * Returns a list of the Units that use the Local that is defined by a given Unit.
   * 
   * @param s
   *          the unit we wish to query for the use of the Local it defines.
   * @return a list of the Local's uses.
   */
  public List<UnitValueBoxPair> getUsesOf(Unit s);
}
