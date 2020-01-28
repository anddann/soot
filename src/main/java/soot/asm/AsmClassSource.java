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

import java.io.IOException;
import java.io.InputStream;

import org.objectweb.asm.ClassReader;

import soot.*;
import soot.coffi.Util;
import soot.javaToJimple.IInitialResolver.Dependencies;
import soot.jimple.ConstantFactory;
import soot.options.Options;

/**
 * ASM class source implementation.
 * 
 * @author Aaloan Miftah
 */
public class AsmClassSource extends ClassSource {

  protected FoundFile foundFile;
  private Scene myScene;
  private SootResolver mySootResolver;
  private Options myOptions;
  private PrimTypeCollector primTypeCollector;
  private ConstantFactory constantFactory;
  private LambdaMetaFactory myLambdaMetaFactory;
  private PackManager myPackManager;
  private Util myCoffiUtil;
  private PhaseOptions myPhaseOptions;
  private Printer myPrinter;

  /**
   * Constructs a new ASM class source.
   * @param cls
   *          fully qualified name of the class.
   * @param myScene
   * @param mySootResolver
   * @param myOptions
   * @param primTypeCollector
   * @param constantFactory
   * @param myLambdaMetaFactory
   * @param myPackManager
   * @param myCoffiUtil
   * @param myPhaseOptions
   * @param myPrinter
   */
  protected AsmClassSource(String cls, FoundFile foundFile, Scene myScene, SootResolver mySootResolver, Options myOptions, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, LambdaMetaFactory myLambdaMetaFactory, PackManager myPackManager, Util myCoffiUtil, PhaseOptions myPhaseOptions, Printer myPrinter) {
    super(cls);
    this.myScene = myScene;
    this.mySootResolver = mySootResolver;
    this.myOptions = myOptions;
    this.primTypeCollector = primTypeCollector;
    this.constantFactory = constantFactory;
    this.myLambdaMetaFactory = myLambdaMetaFactory;
    this.myPackManager = myPackManager;
    this.myCoffiUtil = myCoffiUtil;
    this.myPhaseOptions = myPhaseOptions;
    this.myPrinter = myPrinter;
    if (foundFile == null) {
      throw new IllegalStateException("Error: The FoundFile must not be null.");
    }
    this.foundFile = foundFile;
  }

  @Override
  public Dependencies resolve(SootClass sc) {
    InputStream d = null;
    try {
      d = foundFile.inputStream();
      ClassReader clsr = new ClassReader(d);
      SootClassBuilder scb = new SootClassBuilder(sc, myScene, mySootResolver,  myOptions, primTypeCollector, constantFactory, myLambdaMetaFactory, myPackManager, myCoffiUtil, myPhaseOptions, myPrinter);
      clsr.accept(scb, ClassReader.SKIP_FRAMES);
      Dependencies deps = new Dependencies();
      deps.typesToSignature.addAll(scb.deps);
      return deps;
    } catch (IOException e) {
      throw new RuntimeException("Error: Failed to create class reader from class source.", e);
    } finally {
      try {
        if (d != null) {
          d.close();
          d = null;
        }
      } catch (IOException e) {
        throw new RuntimeException("Error: Failed to close source input stream.", e);
      } finally {
        close();
      }
    }
  }

  @Override
  public void close() {
    if (foundFile != null) {
      foundFile.close();
      foundFile = null;
    }
  }
}