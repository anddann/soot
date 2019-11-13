package soot;

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

import soot.jimple.JimpleBody;
import soot.options.JBOptions;
import soot.options.Options;

/**
 * A wrapper object for a pack of optimizations. Provides chain-like operations, except that the key is the phase name. This
 * is a specific one for the very messy jb phase.
 */
public class JimpleBodyPack extends BodyPack {
  public JimpleBodyPack() {
    super("jb");
  }

  /** Applies the transformations corresponding to the given options. */
  private void applyPhaseOptions(JimpleBody b, Map<String, String> opts) {
    JBOptions options = new JBOptions(opts);

    if (options.use_original_names()) {
      myPhaseOptions().setPhaseOptionIfUnset("jb.lns", "only-stack-locals");
    }

    if (myOptions.time()) {
      myTimers.splitTimer.start();
    }

    PackmyManager.getTransform("jb.tt").apply(b); // TrapTigthener
    PackmyManager.getTransform("jb.dtr").apply(b); // DuplicateCatchAllTrapRemover

    // UnreachableCodeEliminator: We need to do this before splitting
    // locals for not creating disconnected islands of useless assignments
    // that afterwards mess up type assignment.
    PackmyManager.getTransform("jb.uce").apply(b);

    PackmyManager.getTransform("jb.ls").apply(b);

    if (myOptions.time()) {
      myTimers.splitTimer.end();
    }

    PackmyManager.getTransform("jb.a").apply(b);
    PackmyManager.getTransform("jb.ule").apply(b);

    if (myOptions.time()) {
      myTimers.assignTimer.start();
    }

    PackmyManager.getTransform("jb.tr").apply(b);

    if (myOptions.time()) {
      myTimers.assignTimer.end();
    }

    if (options.use_original_names()) {
      PackmyManager.getTransform("jb.ulp").apply(b);
    }
    PackmyManager.getTransform("jb.lns").apply(b); // LocalNameStandardizer
    PackmyManager.getTransform("jb.cp").apply(b); // CopyPropagator
    PackmyManager.getTransform("jb.dae").apply(b); // DeadAssignmentElimintaor
    PackmyManager.getTransform("jb.cp-ule").apply(b); // UnusedLocalEliminator
    PackmyManager.getTransform("jb.lp").apply(b); // LocalPacker
    PackmyManager.getTransform("jb.ne").apply(b); // NopEliminator
    PackmyManager.getTransform("jb.uce").apply(b); // UnreachableCodeEliminator: Again, we might have new dead code

    // LocalNameStandardizer: After all these changes, some locals
    // may end up being eliminated. If we want a stable local iteration
    // order between soot instances, running LocalNameStandardizer
    // again after all other changes is required.
    if (options.stabilize_local_names()) {
      myPhaseOptions().setPhaseOption("jb.lns", "sort-locals:true");
      PackmyManager.getTransform("jb.lns").apply(b);
    }

    if (myOptions.time()) {
      myTimers.stmtCount += b.getUnits().size();
    }
  }

  protected void internalApply(Body b) {
    applyPhaseOptions((JimpleBody) b, myPhaseOptions().getPhaseOptions(getPhaseName()));
  }
}
