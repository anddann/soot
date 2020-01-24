package soot;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2004 Ondrej Lhotak
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

import java.io.File;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


import soot.javaToJimple.IInitialResolver;
import soot.javaToJimple.IInitialResolver.Dependencies;

/**
 * A class source for resolving from .java files using javaToJimple.
 */
public class JavaClassSource extends ClassSource {
  private static final Logger logger = LoggerFactory.getLogger(JavaClassSource.class);

  public JavaClassSource(String className, File fullPath) {
    super(className);
    this.fullPath = fullPath;
  }

  public JavaClassSource(String className) {
    super(className);
  }

  public Dependencies resolve(SootClass sc) {
//    if (myOptions.verbose()) {
//      logger.debug("resolving [from .java]: " + className);
//    }

    IInitialResolver resolver = null;
//    if (myOptions.polyglot()) {
//      resolver = myInitialResolver;
//    } else {
//      resolver = JastAddmyInitialResolver;
//    }
//
//    if (fullPath != null) {
//      resolver.formAst(fullPath.getPath(), mySourceLocator.sourcePath(), className);
//    }
    // System.out.println("about to call initial resolver in j2j: "+sc.getName());
    Dependencies references = resolver.resolveFromJavaFile(sc);
//
//    /*
//     * 1st March 2006 Nomair This seems to be a good place to calculate all the AST Metrics needed from Java's AST
//     */
//    if (myOptions.ast_metrics()) {
//      // System.out.println("CALLING COMPUTEASTMETRICS!!!!!!!");
//      Node ast = myInitialResolver.getAst();
//      if (ast == null) {
//        logger.debug("No compatible AST available for AST metrics. Skipping. Try -polyglot option.");
//      } else {
//        ComputeASTMetrics metrics = new ComputeASTMetrics(ast);
//        metrics.apply();
//      }
//    }

    return references;
  }

  private File fullPath;
}
