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
import soot.options.JJOptions;
import soot.options.Options;

/**
 * A wrapper object for a pack of optimizations. Provides chain-like operations, except that the key is the phase name. This
 * is a specific one for the very messy jb phase.
 */
public class JavaToJimpleBodyPack extends BodyPack {
  public JavaToJimpleBodyPack() {
    super("jj");
  }

  /** Applies the transformations corresponding to the given options. */
  private void applyPhaseOptions(JimpleBody b, Map<String, String> opts) {
    JJOptions options = new JJOptions(opts);

    if (options.use_original_names()) {
      myPhaseOptions().setPhaseOptionIfUnset("jj.lns", "only-stack-locals");
    }

    if (myOptions.time()) {
      myTimers.splitTimer.start();
    }

    PackmyManager.getTransform("jj.ls").apply(b);

    if (myOptions.time()) {
      myTimers.splitTimer.end();
    }

    PackmyManager.getTransform("jj.a").apply(b);
    PackmyManager.getTransform("jj.ule").apply(b);
    PackmyManager.getTransform("jj.ne").apply(b);

    if (myOptions.time()) {
      myTimers.assignTimer.start();
    }

    PackmyManager.getTransform("jj.tr").apply(b);

    if (myOptions.time()) {
      myTimers.assignTimer.end();
    }

    if (options.use_original_names()) {
      PackmyManager.getTransform("jj.ulp").apply(b);
    }
    PackmyManager.getTransform("jj.lns").apply(b);
    PackmyManager.getTransform("jj.cp").apply(b);
    PackmyManager.getTransform("jj.dae").apply(b);
    PackmyManager.getTransform("jj.cp-ule").apply(b);
    PackmyManager.getTransform("jj.lp").apply(b);
    // PackmyManager.getTransform( "jj.ct" ).apply( b );
    PackmyManager.getTransform("jj.uce").apply(b);

    if (myOptions.time()) {
      myTimers.stmtCount += b.getUnits().size();
    }
  }

  protected void internalApply(Body b) {
    applyPhaseOptions((JimpleBody) b, myPhaseOptions().getPhaseOptions(getPhaseName()));
  }
}
