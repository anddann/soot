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

import java.util.List;

import soot.Body;
import soot.Local;
import soot.Unit;
import soot.options.Options;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.SimpleLocalDefs.FlowAnalysisMode;
import soot.util.PhaseDumper;

/**
 * Provides an interface for querying for the definitions of a Local at a given Unit in a method.
 */
public interface LocalDefs {
  static final public class Factory {
    private Factory() {
    }

    /**
     * Creates a new LocalDefs analysis based on a {@code ExceptionalUnitGraph}
     *
     * @see ExceptionalUnitGraph#ExceptionalUnitGraph(Body, soot.toolkits.exceptions.ThrowableSet.Manager)
     * @see soot.validation.UsesValidator
     * @param body
     * @param myManager
     * @param myOptions
     * @param phaseDumper
     * @return a new LocalDefs instance
     */
    public static LocalDefs newLocalDefs(Body body, ThrowAnalysis throwAnalysis,  ThrowableSet.Manager myManager, Options myOptions, PhaseDumper phaseDumper) {
      return newLocalDefs(body, false, throwAnalysis, myOptions, myManager, phaseDumper);
    }

    /**
     * Creates a new LocalDefs analysis based on a {@code ExceptionalUnitGraph} If you don't trust the input you should set
     * <code>expectUndefined</code> to <code>true</code>
     *
     * @see ExceptionalUnitGraph# ExceptionalUnitGraph(Body, soot.toolkits.exceptions.ThrowableSet.Manager)
     * @param expectUndefinedUses
     *          if you expect uses of locals that are undefined
     * @param body
     * @param myThrowAnalysis
     * @param myOptions
     * @param myManager
     * @param phaseDumper
     * @return a new LocalDefs instance
     */
    public static LocalDefs newLocalDefs(Body body, boolean expectUndefined, ThrowAnalysis myThrowAnalysis, Options myOptions, ThrowableSet.Manager myManager, PhaseDumper phaseDumper) {
      return newLocalDefs(new ExceptionalUnitGraph(body, myThrowAnalysis,myOptions.omit_excepting_unit_edges(), myManager, phaseDumper), expectUndefined, myOptions);
    }

    /**
     * Creates a new LocalDefs analysis based on a given {@code UnitGraph}
     *
     * @see soot.toolkits.graph.UnitGraph#UnitGraph(Body)
     * @param graph
     *          the graph to work with
     * @param myOptions
     * @return a new LocalDefs instance
     */
    public static LocalDefs newLocalDefs(UnitGraph graph, Options myOptions) {
      return newLocalDefs(graph, false, myOptions);
    }

    /**
     * Creates a new LocalDefs analysis based on a given {@code UnitGraph}. If you don't trust the input you should set
     * <code>expectUndefined</code> to <code>true</code>
     *
     * @see soot.toolkits.graph.UnitGraph#UnitGraph(Body)
     * @see soot.validation.UsesValidator
     * @param graph
     *          the graph to work with
     * @param expectUndefined
     *          if you expect uses of locals that are undefined
     * @param myOptions
     * @return a new LocalDefs instance
     */
    public static LocalDefs newLocalDefs(UnitGraph graph, boolean expectUndefined, Options myOptions) {
      // return new SmartLocalDefs(graph, LiveLocals.Factory.newLiveLocals(graph));
      return new SimpleLocalDefs(graph, expectUndefined ? FlowAnalysisMode.OmitSSA : FlowAnalysisMode.Automatic, myOptions);
    }

    /**
     * Creates a new LocalDefs analysis based on a given {@code UnitGraph}. This analysis will be flow-insensitive, i.e., for
     * a given local, it will always give all statements that ever write to that local regardless of potential redefinitions
     * in between.
     *
     * @see soot.toolkits.graph.UnitGraph#UnitGraph(Body)
     * @see soot.validation.UsesValidator
     * @param graph
     *          the graph to work with
     * @param myOptions
     * @return a new LocalDefs instance
     */
    public static LocalDefs newLocalDefsFlowInsensitive(UnitGraph graph, Options myOptions) {
      // return new SmartLocalDefs(graph, LiveLocals.Factory.newLiveLocals(graph));
      return new SimpleLocalDefs(graph, FlowAnalysisMode.FlowInsensitive, myOptions);
    }
  }

  /**
   * Returns the definition sites for a Local at a certain point (Unit) in a method.
   *
   * You can assume this method never returns {@code null}.
   *
   * @param l
   *          the Local in question.
   * @param s
   *          a unit that specifies the method context (location) to query for the definitions of the Local.
   * @return a list of Units where the local is defined in the current method context. If there are no uses an empty list
   *         will returned.
   */
  public List<Unit> getDefsOfAt(Local l, Unit s);

  /**
   * Returns the definition sites for a Local merged over all points in a method.
   *
   * You can assume this method never returns {@code null}.
   *
   * @param l
   *          the Local in question.
   * @return a list of Units where the local is defined in the current method context. If there are no uses an empty list
   *         will returned.
   */
  public List<Unit> getDefsOf(Local l);

}
