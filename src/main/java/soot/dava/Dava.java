package soot.dava;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Jerome Miecznikowski
 * Copyright (C) 2004 - 2005 Nomair A. Naeem
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

import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.UnsupportedEncodingException;
import java.io.Writer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.CompilationDeathException;
import soot.Local;
import soot.PhaseOptions;
import soot.PrimTypeCollector;
import soot.Printer;
import soot.Scene;
import soot.SootMethod;
import soot.Type;
import soot.baf.Baf;
import soot.dava.toolkits.base.AST.ASTWalker;
import soot.dava.toolkits.base.AST.TryContentsFinder;
import soot.dava.toolkits.base.AST.UselessTryRemover;
import soot.dava.toolkits.base.AST.transformations.UselessLabelFinder;
import soot.dava.toolkits.base.AST.traversals.ClosestAbruptTargetFinder;
import soot.dava.toolkits.base.finders.AbruptEdgeFinder;
import soot.dava.toolkits.base.finders.CycleFinder;
import soot.dava.toolkits.base.finders.ExceptionFinder;
import soot.dava.toolkits.base.finders.IfFinder;
import soot.dava.toolkits.base.finders.LabeledBlockFinder;
import soot.dava.toolkits.base.finders.SequenceFinder;
import soot.dava.toolkits.base.finders.SwitchFinder;
import soot.dava.toolkits.base.finders.SynchronizedBlockFinder;
import soot.dava.toolkits.base.misc.MonitorConverter;
import soot.dava.toolkits.base.misc.PackageNamer;
import soot.dava.toolkits.base.misc.ThrowNullConverter;
import soot.grimp.Grimp;
import soot.jimple.ConstantFactory;
import soot.jimple.Jimple;
import soot.options.Options;
import soot.util.IterableSet;
import soot.util.PhaseDumper;

public class Dava {
    private static final Logger logger = LoggerFactory.getLogger(Dava.class);
    private final ExceptionFinder myExceptionFinder;
    private final CycleFinder myCycleFinder;
    private final IfFinder myIfFinder;
    private final SwitchFinder mySwitchFinder;
    private final SynchronizedBlockFinder mySynchronizedBlockFinder;
    private final SequenceFinder mySequenceFinder;
    private final LabeledBlockFinder myLabeledBlockFinder;
    private final AbruptEdgeFinder myAbruptEdgeFinder;
    private final MonitorConverter myMonitorConverter;
    private final ThrowNullConverter myThrowNullConverter;
    private final UselessTryRemover myUselessTryRemover;
    private final PhaseOptions myPhaseOptions;
    private ClosestAbruptTargetFinder myClosestAbruptTargetFinder;
    private Options myOptions;
    private Printer myPrinter;
    private ConstantFactory constantFactory;
    private PhaseDumper myPhaseDumper;
    ;
    private PrimTypeCollector primTypeCollector;
    private Baf myBaf;
    private TryContentsFinder myTryContentsFinder;
    private ASTWalker myASTWalker;
    private Scene myScene;
    private PackageNamer myPackageNamer;
    private UselessLabelFinder myUselessLabelFinder;

    @Inject
    public Dava(ExceptionFinder myExceptionFinder, CycleFinder myCycleFinder, IfFinder myIfFinder,
                SwitchFinder mySwitchFinder, SynchronizedBlockFinder mySynchronizedBlockFinder, SequenceFinder mySequenceFinder,
                LabeledBlockFinder myLabeledBlockFinder, AbruptEdgeFinder myAbruptEdgeFinder, MonitorConverter myMonitorConverter,
                ThrowNullConverter myThrowNullConverter, UselessTryRemover myUselessTryRemover, PhaseOptions myPhaseOptions,
                ClosestAbruptTargetFinder myClosestAbruptTargetFinder, Options myOptions, Printer myPrinter,
                ConstantFactory constantFactory, PhaseDumper myPhaseDumper, , PrimTypeCollector primTypeCollector,
                Baf myBaf, TryContentsFinder myTryContentsFinder, ASTWalker myASTWalker, Scene myScene, PackageNamer myPackageNamer, UselessLabelFinder myUselessLabelFinder) {
        this.myExceptionFinder = myExceptionFinder;
        this.myCycleFinder = myCycleFinder;
        this.myIfFinder = myIfFinder;
        this.mySwitchFinder = mySwitchFinder;
        this.mySynchronizedBlockFinder = mySynchronizedBlockFinder;
        this.mySequenceFinder = mySequenceFinder;
        this.myLabeledBlockFinder = myLabeledBlockFinder;
        this.myAbruptEdgeFinder = myAbruptEdgeFinder;
        this.myMonitorConverter = myMonitorConverter;
        this.myThrowNullConverter = myThrowNullConverter;
        this.myUselessTryRemover = myUselessTryRemover;
        this.myPhaseOptions = myPhaseOptions;
        this.myClosestAbruptTargetFinder = myClosestAbruptTargetFinder;
        this.myOptions = myOptions;
        this.myPrinter = myPrinter;
        this.constantFactory = constantFactory;
        this.myPhaseDumper = myPhaseDumper;

        this.primTypeCollector = primTypeCollector;
        this.myBaf = myBaf;
        this.myTryContentsFinder = myTryContentsFinder;
        this.myASTWalker = myASTWalker;
        this.myScene = myScene;
        this.myPackageNamer = myPackageNamer;
        this.myUselessLabelFinder = myUselessLabelFinder;
    }

    private static final String LOG_TO_FILE = null;
    private static final PrintStream LOG_TO_SCREEN = null;

    private Writer iOut = null;
    private IterableSet currentPackageContext = null;
    private String currentPackage;

    public void set_CurrentPackage(String cp) {
        currentPackage = cp;
    }

    public String get_CurrentPackage() {
        return currentPackage;
    }

    public void set_CurrentPackageContext(IterableSet cpc) {
        currentPackageContext = cpc;
    }

    public IterableSet get_CurrentPackageContext() {
        return currentPackageContext;
    }

    public DavaBody newBody(SootMethod m) {
        DavaBody davaBody = new DavaBody(m, myOptions, myPrinter, myExceptionFinder, myCycleFinder, myIfFinder, mySwitchFinder,
                mySynchronizedBlockFinder, mySequenceFinder, myLabeledBlockFinder, myAbruptEdgeFinder, myMonitorConverter,
                myThrowNullConverter, myUselessTryRemover, myPhaseOptions, myTryContentsFinder, myASTWalker, myPackageNamer, primTypeCollector, this,
                myClosestAbruptTargetFinder, constantFactory,  myBaf, myScene, myUselessLabelFinder);
        return davaBody;
    }

    /**
     * Returns a DavaBody constructed from the given body b.
     */
    public DavaBody newBody(Body b) {
        return new DavaBody(b, myOptions, myPrinter, myMonitorConverter,
                myExceptionFinder, mySynchronizedBlockFinder,
                myThrowNullConverter, mySequenceFinder, myLabeledBlockFinder,
                myCycleFinder, myIfFinder, mySwitchFinder, myAbruptEdgeFinder,
                myUselessTryRemover, myPhaseOptions,
                myClosestAbruptTargetFinder, this, constantFactory, myPhaseDumper,  primTypeCollector, myBaf, myTryContentsFinder, myASTWalker, myScene, myPackageNamer, myUselessLabelFinder);

    }

    public Local newLocal(String name, Type t) {
        return Jimple.newLocal(name, t);
    }

    public void log(String s) {
        if (LOG_TO_SCREEN != null) {
            LOG_TO_SCREEN.println(s);
            LOG_TO_SCREEN.flush();
        }

        if (LOG_TO_FILE != null) {
            if (iOut == null) {
                try {
                    iOut = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(LOG_TO_FILE), "US-ASCII"));
                } catch (FileNotFoundException fnfe) {
                    logger.debug("" + "Unable to open " + LOG_TO_FILE);
                    logger.error(fnfe.getMessage(), fnfe);
                    throw new CompilationDeathException(CompilationDeathException.COMPILATION_ABORTED);
                } catch (UnsupportedEncodingException uee) {
                    logger.debug("" + "This system doesn't support US-ASCII encoding!!");
                    logger.error(uee.getMessage(), uee);
                    throw new CompilationDeathException(CompilationDeathException.COMPILATION_ABORTED);
                }
            }

            try {
                iOut.write(s);
                iOut.write("\n");
                iOut.flush();
            } catch (IOException ioe) {
                logger.debug("" + "Unable to write to " + LOG_TO_FILE);
                logger.error(ioe.getMessage(), ioe);
                throw new CompilationDeathException(CompilationDeathException.COMPILATION_ABORTED);
            }
        }
    }
}
