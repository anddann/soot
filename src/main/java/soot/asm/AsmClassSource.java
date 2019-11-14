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

import soot.ClassSource;
import soot.FoundFile;
import soot.Scene;
import soot.SootClass;
import soot.SootResolver;
import soot.javaToJimple.IInitialResolver.Dependencies;
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

  /**
   * Constructs a new ASM class source.
   *
   * @param data
   *          stream containing data for class.
   * @param cls
   *          fully qualified name of the class.
   * @param myScene
   * @param mySootResolver
   * @param myOptions
   */
  protected AsmClassSource(String cls, FoundFile foundFile, Scene myScene, SootResolver mySootResolver, Options myOptions) {
    super(cls);
    this.myScene = myScene;
    this.mySootResolver = mySootResolver;
    this.myOptions = myOptions;
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
      SootClassBuilder scb = new SootClassBuilder(sc, myScene, mySootResolver,  myOptions);
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