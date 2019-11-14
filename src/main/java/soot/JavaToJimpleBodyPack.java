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
import soot.toolkits.graph.interaction.InteractionHandler;

/**
 * A wrapper object for a pack of optimizations. Provides chain-like operations, except that the key is the phase name. This
 * is a specific one for the very messy jb phase.
 */
public class JavaToJimpleBodyPack extends BodyPack {
  public JavaToJimpleBodyPack(PhaseOptions myPhaseOptions, Options myOptions, InteractionHandler interactionHandler) {
    super("jj",myPhaseOptions,myOptions,interactionHandler);
  }

  /** Applies the transformations corresponding to the given options. */
  private void applyPhaseOptions(JimpleBody b, Map<String, String> opts) {
    JJOptions options = new JJOptions(opts);

    if (options.use_original_names()) {
      getMyPhaseOptions().setPhaseOptionIfUnset("jj.lns", "only-stack-locals");
    }

//    if (getMyOptions().time()) {
//      myTimers.splitTimer.start();
//    }

    getMyPhaseOptions().getPM().getTransform("jj.ls").apply(b);

//    if (getMyOptions().time()) {
//      myTimers.splitTimer.end();
//    }

    getMyPhaseOptions().getPM().getTransform("jj.a").apply(b);
    getMyPhaseOptions().getPM().getTransform("jj.ule").apply(b);
    getMyPhaseOptions().getPM().getTransform("jj.ne").apply(b);

//    if (getMyOptions().time()) {
//      myTimers.assignTimer.start();
//    }

    getMyPhaseOptions().getPM().getTransform("jj.tr").apply(b);

//    if (getMyOptions().time()) {
//      myTimers.assignTimer.end();
//    }

    if (options.use_original_names()) {
      getMyPhaseOptions().getPM().getTransform("jj.ulp").apply(b);
    }
    getMyPhaseOptions().getPM().getTransform("jj.lns").apply(b);
    getMyPhaseOptions().getPM().getTransform("jj.cp").apply(b);
    getMyPhaseOptions().getPM().getTransform("jj.dae").apply(b);
    getMyPhaseOptions().getPM().getTransform("jj.cp-ule").apply(b);
    getMyPhaseOptions().getPM().getTransform("jj.lp").apply(b);
    // getMyPhaseOptions().getPM().getTransform( "jj.ct" ).apply( b );
    getMyPhaseOptions().getPM().getTransform("jj.uce").apply(b);

//    if (getMyOptions().time()) {
//      myTimers.stmtCount += b.getUnits().size();
//    }
  }

  protected void internalApply(Body b) {
    applyPhaseOptions((JimpleBody) b, getMyPhaseOptions().getPhaseOptions(getPhaseName()));
  }
}
