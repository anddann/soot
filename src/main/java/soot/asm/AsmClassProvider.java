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
import soot.coffi.Util;
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
  private Scene myScene;
  private LambdaMetaFactory myLambdaMetaFactory;
  private Options myOptions;
  private SootResolver mySootResolver;
  private PackManager myPackManager;
  private Util myCoffiUtil;
  private PhaseOptions myPhaseOptions;

  public AsmClassProvider(SourceLocator mySourceLocator, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, Scene myScene, LambdaMetaFactory myLambdaMetaFactory, Options myOptions, SootResolver mySootResolver, PackManager myPackManager, Util myCoffiUtil, PhaseOptions myPhaseOptions) {

    this.mySourceLocator = mySourceLocator;
    this.primTypeCollector = primTypeCollector;
    this.constantFactory = constantFactory;
    this.myScene = myScene;
    this.myLambdaMetaFactory = myLambdaMetaFactory;
    this.myOptions = myOptions;
    this.mySootResolver = mySootResolver;
    this.myPackManager = myPackManager;
    this.myCoffiUtil = myCoffiUtil;
    this.myPhaseOptions = myPhaseOptions;
  }

  public ClassSource find(String cls) {
    String clsFile = cls.replace('.', '/') + ".class";
    FoundFile file = mySourceLocator.lookupInClassPath(clsFile);
    return file == null ? null : new AsmClassSource(cls, file, myScene, mySootResolver, myOptions, primTypeCollector, constantFactory, myLambdaMetaFactory, myPackManager, myCoffiUtil, myPhaseOptions, myPrinter);
  }
}
