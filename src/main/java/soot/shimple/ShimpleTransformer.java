package soot.shimple;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Navindra Umanee <navindra@cs.mcgill.ca>
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

import java.util.Iterator;
import java.util.Map;

import com.google.inject.Inject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.options.Options;
import soot.MethodSource;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;

/**
 * Traverses all methods, in all classes from the Scene, and transforms them to Shimple. Typically used for whole-program
 * analysis on Shimple.
 *
 * @author Navindra Umanee
 **/
public class ShimpleTransformer extends SceneTransformer {
  private static final Logger logger = LoggerFactory.getLogger(ShimpleTransformer.class);
  private Options myOptions;
  private Scene myScene;
  private Shimple myShimple;

  @Inject
  public ShimpleTransformer(Options myOptions, Scene myScene, Shimple myShimple) {
    this.myOptions = myOptions;
    this.myScene = myScene;
    this.myShimple = myShimple;
  }


  protected void internalTransform(String phaseName, Map options) {
    if (myOptions.verbose()) {
      logger.debug("Transforming all classes in the Scene to Shimple...");
    }

    // *** FIXME: Add debug output to indicate which class/method is being shimplified.
    // *** FIXME: Is ShimpleTransformer the right solution? The call graph may deem
    // some classes unreachable.

    Iterator classesIt = myScene.getClasses().iterator();
    while (classesIt.hasNext()) {
      SootClass sClass = (SootClass) classesIt.next();
      if (sClass.isPhantom()) {
        continue;
      }

      Iterator methodsIt = sClass.getMethods().iterator();
      while (methodsIt.hasNext()) {
        SootMethod method = (SootMethod) methodsIt.next();
        if (!method.isConcrete()) {
          continue;
        }

        if (method.hasActiveBody()) {
          Body body = method.getActiveBody();
          ShimpleBody sBody = null;

          if (body instanceof ShimpleBody) {
            sBody = (ShimpleBody) body;
            if (!sBody.isSSA()) {
              sBody.rebuild();
            }
          } else {
            sBody = myShimple.newBody(body);
          }

          method.setActiveBody(sBody);
        } else {
          MethodSource ms = new ShimpleMethodSource(method.getSource());
          method.setSource(ms);
        }
      }
    }
  }
}
