package soot.asm;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 2014 Raja Vallee-Rai and others
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

import soot.*;
import soot.jimple.ConstantFactory;
import soot.options.Options;

/**
 * Objectweb ASM class provider.
 * 
 * @author Aaloan Miftah
 */
public class AsmClassProvider implements ClassProvider {

  private SourceLocator mySourceLocator;
  private PrimTypeCollector primTypeCollector;
  private ConstantFactory constantFactory;

  public AsmClassProvider(SourceLocator mySourceLocator, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory) {

    this.mySourceLocator = mySourceLocator;
    this.primTypeCollector = primTypeCollector;
    this.constantFactory = constantFactory;
  }

  public ClassSource find(String cls, Scene myScene,  Options myOptions, SootResolver mySootResolver) {
    String clsFile = cls.replace('.', '/') + ".class";
    FoundFile file = mySourceLocator.lookupInClassPath(clsFile);
    return file == null ? null : new AsmClassSource(cls, file, myScene, mySootResolver, myOptions, primTypeCollector, constantFactory, myLambdaMetaFactory, myPackManager, myCoffiUtil, myPhaseOptions);
  }
}
