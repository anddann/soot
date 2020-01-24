
package soot.jimple.toolkits.thread.mhp;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 2018 Raja Vallée-Rai and others
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

import soot.Scene;
import soot.SceneTransformer;
import soot.options.Options;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.exceptions.ThrowableSet;
import soot.util.PhaseDumper;

/**
 *
 */

public class MhpTransformer extends SceneTransformer {
  private Scene myScene;
  private ThrowAnalysis throwAnalysis;
  private ThrowableSet.Manager myManager;
  private PhaseDumper myPhaseDumper;
  private Options myOptions;

  @Inject
  public MhpTransformer(Scene myScene, ThrowAnalysis throwAnalysis, ThrowableSet.Manager myManager,
      PhaseDumper myPhaseDumper, Options myOptions) {
    this.myScene = myScene;
    this.throwAnalysis = throwAnalysis;
    this.myManager = myManager;
    this.myPhaseDumper = myPhaseDumper;
    this.myOptions = myOptions;
  }

  MhpTester mhpTester;

  protected void internalTransform(String phaseName, Map options) {
    getMhpTester().printMhpSummary();
  }

  public MhpTester getMhpTester() {
    if (mhpTester == null) {
      mhpTester = new SynchObliviousMhpAnalysis(myScene, throwAnalysis, myManager, myPhaseDumper, myOptions, myPedanticThrowAnalysis, myInteractionHandler);
    }
    return mhpTester;
  }

  public void setMhpTester(MhpTester mhpTester) {
    this.mhpTester = mhpTester;
  }
}
