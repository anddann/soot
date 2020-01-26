package soot;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 - 2004 Ondrej Lhotak
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

import heros.solver.CountingThreadPoolExecutor;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.zip.GZIPOutputStream;
import java.util.zip.ZipEntry;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.baf.Baf;
import soot.baf.BafASMBackend;
import soot.baf.BafBody;
import soot.baf.toolkits.base.LoadStoreOptimizer;
import soot.baf.toolkits.base.PeepholeOptimizer;
import soot.baf.toolkits.base.StoreChainOptimizer;
import soot.dava.Dava;
import soot.dava.DavaBody;
import soot.dava.DavaBuildFile;
import soot.dava.DavaPrinter;
import soot.dava.DavaStaticBlockCleaner;
import soot.dava.toolkits.base.AST.interProcedural.InterProceduralAnalyses;
import soot.dava.toolkits.base.AST.transformations.RemoveEmptyBodyDefaultConstructor;
import soot.dava.toolkits.base.AST.transformations.VoidReturnRemover;
import soot.dava.toolkits.base.misc.PackageNamer;
import soot.dava.toolkits.base.misc.ThrowFinder;
import soot.grimp.Grimp;
import soot.grimp.toolkits.base.ConstructorFolder;
import soot.jimple.ConstantFactory;
import soot.jimple.JimpleBody;
import soot.jimple.paddle.PaddleHook;
import soot.jimple.spark.SparkTransformer;
import soot.jimple.spark.fieldrw.FieldTagAggregator;
import soot.jimple.spark.fieldrw.FieldTagger;
import soot.jimple.toolkits.annotation.AvailExprTagger;
import soot.jimple.toolkits.annotation.DominatorsTagger;
import soot.jimple.toolkits.annotation.LineNumberAdder;
import soot.jimple.toolkits.annotation.arraycheck.ArrayBoundsChecker;
import soot.jimple.toolkits.annotation.arraycheck.RectangularArrayFinder;
import soot.jimple.toolkits.annotation.callgraph.CallGraphGrapher;
import soot.jimple.toolkits.annotation.callgraph.CallGraphTagger;
import soot.jimple.toolkits.annotation.defs.ReachingDefsTagger;
import soot.jimple.toolkits.annotation.fields.UnreachableFieldsTagger;
import soot.jimple.toolkits.annotation.liveness.LiveVarsTagger;
import soot.jimple.toolkits.annotation.logic.LoopInvariantFinder;
import soot.jimple.toolkits.annotation.methods.UnreachableMethodsTagger;
import soot.jimple.toolkits.annotation.nullcheck.NullCheckEliminator;
import soot.jimple.toolkits.annotation.nullcheck.NullPointerChecker;
import soot.jimple.toolkits.annotation.nullcheck.NullPointerColorer;
import soot.jimple.toolkits.annotation.parity.ParityTagger;
import soot.jimple.toolkits.annotation.profiling.ProfilingGenerator;
import soot.jimple.toolkits.annotation.purity.PurityAnalysis;
import soot.jimple.toolkits.annotation.qualifiers.TightestQualifiersTagger;
import soot.jimple.toolkits.annotation.tags.ArrayNullTagAggregator;
import soot.jimple.toolkits.base.Aggregator;
import soot.jimple.toolkits.base.RenameDuplicatedClasses;
import soot.jimple.toolkits.callgraph.CHATransformer;
import soot.jimple.toolkits.callgraph.CallGraphPack;
import soot.jimple.toolkits.callgraph.UnreachableMethodTransformer;
import soot.jimple.toolkits.invoke.StaticInliner;
import soot.jimple.toolkits.invoke.StaticMethodBinder;
import soot.jimple.toolkits.pointer.CastCheckEliminatorDumper;
import soot.jimple.toolkits.pointer.DependenceTagAggregator;
import soot.jimple.toolkits.pointer.ParameterAliasTagger;
import soot.jimple.toolkits.pointer.SideEffectTagger;
import soot.jimple.toolkits.reflection.ConstantInvokeMethodBaseTransformer;
import soot.jimple.toolkits.scalar.CommonSubexpressionEliminator;
import soot.jimple.toolkits.scalar.ConditionalBranchFolder;
import soot.jimple.toolkits.scalar.ConstantPropagatorAndFolder;
import soot.jimple.toolkits.scalar.CopyPropagator;
import soot.jimple.toolkits.scalar.DeadAssignmentEliminator;
import soot.jimple.toolkits.scalar.EmptySwitchEliminator;
import soot.jimple.toolkits.scalar.LocalNameStandardizer;
import soot.jimple.toolkits.scalar.NopEliminator;
import soot.jimple.toolkits.scalar.UnconditionalBranchFolder;
import soot.jimple.toolkits.scalar.UnreachableCodeEliminator;
import soot.jimple.toolkits.scalar.pre.BusyCodeMotion;
import soot.jimple.toolkits.scalar.pre.LazyCodeMotion;
import soot.jimple.toolkits.thread.mhp.MhpTransformer;
import soot.jimple.toolkits.thread.synchronization.LockAllocator;
import soot.jimple.toolkits.typing.TypeAssigner;
import soot.options.Options;
import soot.shimple.Shimple;
import soot.shimple.ShimpleBody;
import soot.shimple.ShimpleTransformer;
import soot.sootify.TemplatePrinter;
import soot.tagkit.InnerClassTagAggregator;
import soot.tagkit.LineNumberTagAggregator;
import soot.toDex.DexPrinter;
import soot.toDex.FastDexTrapTightener;
import soot.toDex.SynchronizedMethodTransformer;
import soot.toDex.TrapSplitter;
import soot.toolkits.exceptions.DuplicateCatchAllTrapRemover;
import soot.toolkits.exceptions.TrapTightener;
import soot.toolkits.graph.interaction.InteractionHandler;
import soot.toolkits.scalar.ConstantInitializerToTagTransformer;
import soot.toolkits.scalar.ConstantValueToInitializerTransformer;
import soot.toolkits.scalar.LocalPacker;
import soot.toolkits.scalar.LocalSplitter;
import soot.toolkits.scalar.UnusedLocalEliminator;
import soot.util.Chain;
import soot.util.EscapedWriter;
import soot.util.JasminOutputStream;
import soot.util.PhaseDumper;
import soot.xml.TagCollector;
import soot.xml.XMLPrinter;

/** Manages the Packs containing the various phases and their options. */
public class PackManager {
  private static final Logger logger = LoggerFactory.getLogger(PackManager.class);
  public static boolean DEBUG = false;
  private final Map<String, Pack> packNameToPack = new HashMap<String, Pack>();
  private final List<Pack> packList = new LinkedList<Pack>();
  private final FieldTagger myFieldTagger;
  private boolean onlyStandardPacks = false;
  private JarOutputStream jarFile = null;
  protected DexPrinter dexPrinter = null;
  private Options myOptions;
  private PhaseOptions myPhaseOptions;
  private SourceLocator mySourceLocator;

  // FIXME: subtypes for inject...
  private TrapTightener myTrapTightener;
  private DuplicateCatchAllTrapRemover myDuplicateCatchAllTrapRemover;
  private LocalSplitter myLocalSplitter;
  private TypeAssigner myTypeAssigner;
  private LocalPacker myLocalPacker;
  private EmptySwitchEliminator myEmptySwitchEliminator;
  private Aggregator myAggregator;
  private LocalNameStandardizer myLocalNameStandardizer;
  private UnusedLocalEliminator myUnusedLocalEliminator;
  private CopyPropagator myCopyPropagator;
  private DeadAssignmentEliminator myDeadAssignmentEliminator;
  private UnreachableCodeEliminator myUnreachableCodeEliminator;
  private NopEliminator myNopEliminator;
  private ConstantInvokeMethodBaseTransformer myConstantInvokeMethodBaseTransformer;
  private CHATransformer myCHATransformer;
  private PaddleHook myPaddleHook;
  private MhpTransformer myMhpTransformer;
  private SparkTransformer mySparkTransformer;
  private LockAllocator myLockAllocator;
  private RenameDuplicatedClasses myRenameDuplicatedClasses;
  private StaticMethodBinder myStaticMethodBinder;
  private StaticInliner myStaticInliner;
  private UnreachableMethodsTagger myUnreachableMethodsTagger;
  private UnreachableFieldsTagger myUnreachableFieldsTagger;
  private TightestQualifiersTagger myTightestQualifiersTagger;
  private Scene myScene;
  private RectangularArrayFinder myRectangularArrayFinder;
  private CallGraphGrapher myCallGraphGrapher;
  private PurityAnalysis myPurityAnalysis;
  private ConstantPropagatorAndFolder myConstantPropagatorAndFolder;
  private CommonSubexpressionEliminator myCommonSubexpressionEliminator;
  private LazyCodeMotion myLazyCodeMotion;
  private BusyCodeMotion myBusyCodeMotion;
  private UnconditionalBranchFolder myUnconditionalBranchFolder;
  private ConditionalBranchFolder myConditionalBranchFolder;
  private NullPointerChecker myNullPointerChecker;
  private NullPointerColorer myNullPointerColorer;
  private ArrayBoundsChecker myArrayBoundsChecker;
  private ProfilingGenerator myProfilingGenerator;
  private SideEffectTagger mySideEffectTagger;
  private CallGraphTagger myCallGraphTagger;
  private ParityTagger myParityTagger;
  private ParameterAliasTagger myParameterAliasTagger;
  private ReachingDefsTagger myReachingDefsTagger;
  private LiveVarsTagger myLiveVarsTagger;
  private CastCheckEliminatorDumper myCastCheckEliminatorDumper;
  private LoopInvariantFinder myLoopInvariantFinder;
  private AvailExprTagger myAvailExprTagger;
  private DominatorsTagger myDominatorsTagger;
  private ConstructorFolder myConstructorFolder;
  private LoadStoreOptimizer myLoadStoreOptimizer;
  private PeepholeOptimizer myPeepholeOptimizer;
  private LineNumberTagAggregator myLineNumberTagAggregator;
  private StoreChainOptimizer myStoreChainOptimizer;
  private ArrayNullTagAggregator myArrayNullTagAggregator;
  private DependenceTagAggregator myDependenceTagAggregator;
  private FieldTagAggregator myFieldTagAggregator;
  private LineNumberAdder myLineNumberAdder;
  private InteractionHandler myInteractionHandler;
  private PhaseDumper myPhaseDumper;
  private ShimpleTransformer myShimpleTransformer;
  private ThrowFinder myThrowFinder;
  private PackageNamer myPackageNamer;
  private InnerClassTagAggregator myInnerClassTagAggregator;
  private DavaStaticBlockCleaner myDavaStaticBlockCleaner;
  private DavaPrinter myDavaPrinter;
  private Shimple myShimple;
  ;
  private Dava myDava;
  private Baf myBaf;
  private Printer myPrinter;
  private XMLPrinter myXMLPrinter;
  private TemplatePrinter myTemplatePrinter;
  private NullCheckEliminator myNullCheckEliminator;
  private SynchronizedMethodTransformer mySynchronizedMethodTransformer;
  private EntryPoints myEntryPoints;
  private FastDexTrapTightener myFastDexTrapTightener;
  private TrapSplitter myTrapSplitter;
  private ConstantInitializerToTagTransformer myConstantInitializerToTagTransformer;
  private UnreachableMethodTransformer myUnreachableMethodTransformer;
    private ConstantFactory constantFactory;

    @Inject
  public PackManager(PhaseOptions myPhaseOptions, FieldTagger myFieldTagger, Options myOptions,
                     SourceLocator mySourceLocator, TrapTightener myTrapTightener,
                     DuplicateCatchAllTrapRemover myDuplicateCatchAllTrapRemover, LocalSplitter myLocalSplitter,
                     TypeAssigner myTypeAssigner, LocalPacker myLocalPacker, EmptySwitchEliminator myEmptySwitchEliminator,
                     Aggregator myAggregator, LocalNameStandardizer myLocalNameStandardizer, UnusedLocalEliminator myUnusedLocalEliminator,
                     CopyPropagator myCopyPropagator, DeadAssignmentEliminator myDeadAssignmentEliminator,
                     UnreachableCodeEliminator myUnreachableCodeEliminator, NopEliminator myNopEliminator,
                     ConstantInvokeMethodBaseTransformer myConstantInvokeMethodBaseTransformer, CHATransformer myCHATransformer,
                     PaddleHook myPaddleHook, MhpTransformer myMhpTransformer, SparkTransformer mySparkTransformer,
                     LockAllocator myLockAllocator, RenameDuplicatedClasses myRenameDuplicatedClasses,
                     StaticMethodBinder myStaticMethodBinder, StaticInliner myStaticInliner,
                     UnreachableMethodsTagger myUnreachableMethodsTagger, UnreachableFieldsTagger myUnreachableFieldsTagger,
                     TightestQualifiersTagger myTightestQualifiersTagger, Scene myScene, RectangularArrayFinder myRectangularArrayFinder,
                     CallGraphGrapher myCallGraphGrapher, PurityAnalysis myPurityAnalysis,
                     ConstantPropagatorAndFolder myConstantPropagatorAndFolder,
                     CommonSubexpressionEliminator myCommonSubexpressionEliminator, LazyCodeMotion myLazyCodeMotion,
                     BusyCodeMotion myBusyCodeMotion, UnconditionalBranchFolder myUnconditionalBranchFolder,
                     ConditionalBranchFolder myConditionalBranchFolder, NullPointerChecker myNullPointerChecker,
                     NullPointerColorer myNullPointerColorer, ArrayBoundsChecker myArrayBoundsChecker,
                     ProfilingGenerator myProfilingGenerator, SideEffectTagger mySideEffectTagger, CallGraphTagger myCallGraphTagger,
                     ParityTagger myParityTagger, ParameterAliasTagger myParameterAliasTagger, ReachingDefsTagger myReachingDefsTagger,
                     LiveVarsTagger myLiveVarsTagger, CastCheckEliminatorDumper myCastCheckEliminatorDumper,
                     LoopInvariantFinder myLoopInvariantFinder, AvailExprTagger myAvailExprTagger, DominatorsTagger myDominatorsTagger,
                     ConstructorFolder myConstructorFolder, LoadStoreOptimizer myLoadStoreOptimizer, PeepholeOptimizer myPeepholeOptimizer,
                     LineNumberTagAggregator myLineNumberTagAggregator, StoreChainOptimizer myStoreChainOptimizer,
                     ArrayNullTagAggregator myArrayNullTagAggregator, DependenceTagAggregator myDependenceTagAggregator,
                     FieldTagAggregator myFieldTagAggregator, LineNumberAdder myLineNumberAdder, InteractionHandler myInteractionHandler,
                     PhaseDumper myPhaseDumper, ShimpleTransformer myShimpleTransformer, ThrowFinder myThrowFinder,
                     PackageNamer myPackageNamer, InnerClassTagAggregator myInnerClassTagAggregator,
                     DavaStaticBlockCleaner myDavaStaticBlockCleaner, DavaPrinter myDavaPrinter, Shimple myShimple, ,
                     Dava myDava, Baf myBaf, Printer myPrinter, XMLPrinter myXMLPrinter, TemplatePrinter myTemplatePrinter,
                     NullCheckEliminator myNullCheckEliminator, SynchronizedMethodTransformer mySynchronizedMethodTransformer,
                     EntryPoints myEntryPoints, FastDexTrapTightener myFastDexTrapTightener, TrapSplitter myTrapSplitter,
                     ConstantInitializerToTagTransformer myConstantInitializerToTagTransformer,
                     UnreachableMethodTransformer myUnreachableMethodTransformer, ConstantFactory constantFactory) {
    this.myPhaseOptions = myPhaseOptions;
    this.myOptions = myOptions;
    // myPhaseOptions.setPackManager(this);
    this.myFieldTagger = myFieldTagger;
    this.mySourceLocator = mySourceLocator;
    this.myTrapTightener = myTrapTightener;
    this.myDuplicateCatchAllTrapRemover = myDuplicateCatchAllTrapRemover;
    this.myLocalSplitter = myLocalSplitter;
    this.myTypeAssigner = myTypeAssigner;
    this.myLocalPacker = myLocalPacker;
    this.myEmptySwitchEliminator = myEmptySwitchEliminator;
    this.myAggregator = myAggregator;
    this.myLocalNameStandardizer = myLocalNameStandardizer;
    this.myUnusedLocalEliminator = myUnusedLocalEliminator;
    this.myCopyPropagator = myCopyPropagator;
    this.myDeadAssignmentEliminator = myDeadAssignmentEliminator;
    this.myUnreachableCodeEliminator = myUnreachableCodeEliminator;
    this.myNopEliminator = myNopEliminator;
    this.myConstantInvokeMethodBaseTransformer = myConstantInvokeMethodBaseTransformer;
    this.myCHATransformer = myCHATransformer;
    this.myPaddleHook = myPaddleHook;
    this.myMhpTransformer = myMhpTransformer;
    this.mySparkTransformer = mySparkTransformer;
    this.myLockAllocator = myLockAllocator;
    this.myRenameDuplicatedClasses = myRenameDuplicatedClasses;
    this.myStaticMethodBinder = myStaticMethodBinder;
    this.myStaticInliner = myStaticInliner;
    this.myUnreachableMethodsTagger = myUnreachableMethodsTagger;
    this.myUnreachableFieldsTagger = myUnreachableFieldsTagger;
    this.myTightestQualifiersTagger = myTightestQualifiersTagger;
    this.myScene = myScene;
    this.myRectangularArrayFinder = myRectangularArrayFinder;
    this.myCallGraphGrapher = myCallGraphGrapher;
    this.myPurityAnalysis = myPurityAnalysis;
    this.myConstantPropagatorAndFolder = myConstantPropagatorAndFolder;
    this.myCommonSubexpressionEliminator = myCommonSubexpressionEliminator;
    this.myLazyCodeMotion = myLazyCodeMotion;
    this.myBusyCodeMotion = myBusyCodeMotion;
    this.myUnconditionalBranchFolder = myUnconditionalBranchFolder;
    this.myConditionalBranchFolder = myConditionalBranchFolder;
    this.myNullPointerChecker = myNullPointerChecker;
    this.myNullPointerColorer = myNullPointerColorer;
    this.myArrayBoundsChecker = myArrayBoundsChecker;
    this.myProfilingGenerator = myProfilingGenerator;
    this.mySideEffectTagger = mySideEffectTagger;
    this.myCallGraphTagger = myCallGraphTagger;
    this.myParityTagger = myParityTagger;
    this.myParameterAliasTagger = myParameterAliasTagger;
    this.myReachingDefsTagger = myReachingDefsTagger;
    this.myLiveVarsTagger = myLiveVarsTagger;
    this.myCastCheckEliminatorDumper = myCastCheckEliminatorDumper;
    this.myLoopInvariantFinder = myLoopInvariantFinder;
    this.myAvailExprTagger = myAvailExprTagger;
    this.myDominatorsTagger = myDominatorsTagger;
    this.myConstructorFolder = myConstructorFolder;
    this.myLoadStoreOptimizer = myLoadStoreOptimizer;
    this.myPeepholeOptimizer = myPeepholeOptimizer;
    this.myLineNumberTagAggregator = myLineNumberTagAggregator;
    this.myStoreChainOptimizer = myStoreChainOptimizer;
    this.myArrayNullTagAggregator = myArrayNullTagAggregator;
    this.myDependenceTagAggregator = myDependenceTagAggregator;
    this.myFieldTagAggregator = myFieldTagAggregator;
    this.myLineNumberAdder = myLineNumberAdder;
    this.myInteractionHandler = myInteractionHandler;
    this.myPhaseDumper = myPhaseDumper;
    this.myShimpleTransformer = myShimpleTransformer;
    this.myThrowFinder = myThrowFinder;
    this.myPackageNamer = myPackageNamer;
    this.myInnerClassTagAggregator = myInnerClassTagAggregator;
    this.myDavaStaticBlockCleaner = myDavaStaticBlockCleaner;
    this.myDavaPrinter = myDavaPrinter;
    this.myShimple = myShimple;

    this.myDava = myDava;
    this.myBaf = myBaf;
    this.myPrinter = myPrinter;
    this.myXMLPrinter = myXMLPrinter;
    this.myTemplatePrinter = myTemplatePrinter;
    this.myNullCheckEliminator = myNullCheckEliminator;
    this.mySynchronizedMethodTransformer = mySynchronizedMethodTransformer;
    this.myEntryPoints = myEntryPoints;
    this.myFastDexTrapTightener = myFastDexTrapTightener;
    this.myTrapSplitter = myTrapSplitter;
    ;
    this.myConstantInitializerToTagTransformer = myConstantInitializerToTagTransformer;
    this.myUnreachableMethodTransformer = myUnreachableMethodTransformer;
        this.constantFactory = constantFactory;
        init();
  }

  public boolean onlyStandardPacks() {
    return onlyStandardPacks;
  }

  void notifyAddPack() {
    onlyStandardPacks = false;
  }

  private void init() {
    Pack p;

    // Jimple body creation
    addPack(p = new JimpleBodyPack(myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("jb.tt", myTrapTightener, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.dtr", myDuplicateCatchAllTrapRemover, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.ese", myEmptySwitchEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.ls", myLocalSplitter, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.a", myAggregator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.ule", myUnusedLocalEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.tr", myTypeAssigner, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.ulp", myLocalPacker, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.lns", myLocalNameStandardizer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.cp", myCopyPropagator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.dae", myDeadAssignmentEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.cp-ule", myUnusedLocalEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.lp", myLocalPacker, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.ne", myNopEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jb.uce", myUnreachableCodeEliminator, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Java to Jimple - Jimple body creation
    addPack(p = new JavaToJimpleBodyPack(myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("jj.ls", myLocalSplitter, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.a", myAggregator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.ule", myUnusedLocalEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.ne", myNopEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.tr", myTypeAssigner, myOptions, myPhaseOptions, myPhaseDumper));
      // p.add(new Transform("jj.ct", myCondTransformer));
      p.add(new Transform("jj.ulp", myLocalPacker, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.lns", myLocalNameStandardizer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.cp", myCopyPropagator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.dae", myDeadAssignmentEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.cp-ule", myUnusedLocalEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.lp", myLocalPacker, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jj.uce", myUnreachableCodeEliminator, myOptions, myPhaseOptions, myPhaseDumper));

    }

    // Whole-Jimple Pre-processing Pack
    addPack(p = new ScenePack("wjpp", myPhaseOptions));
    {
      p.add(new Transform("wjpp.cimbt", myConstantInvokeMethodBaseTransformer, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Whole-Shimple Pre-processing Pack
    addPack(p = new ScenePack("wspp", myPhaseOptions));

    // Call graph pack
    addPack(p = new CallGraphPack("cg", myPhaseOptions, myScene, myEntryPoints));
    {
      p.add(new Transform("cg.cha", myCHATransformer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("cg.spark", mySparkTransformer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("cg.paddle", myPaddleHook, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Whole-Shimple transformation pack
    addPack(p = new ScenePack("wstp", myPhaseOptions));

    // Whole-Shimple Optimization pack
    addPack(p = new ScenePack("wsop", myPhaseOptions));

    // Whole-Jimple transformation pack
    addPack(p = new ScenePack("wjtp", myPhaseOptions));
    {
      p.add(new Transform("wjtp.mhp", myMhpTransformer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjtp.tn", myLockAllocator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjtp.rdc", myRenameDuplicatedClasses, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Whole-Jimple Optimization pack
    addPack(p = new ScenePack("wjop", myPhaseOptions));
    {
      p.add(new Transform("wjop.smb", myStaticMethodBinder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjop.si", myStaticInliner, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Give another chance to do Whole-Jimple transformation
    // The RectangularArrayFinder will be put into this package.
    addPack(p = new ScenePack("wjap", myPhaseOptions));
    {
      p.add(new Transform("wjap.ra", myRectangularArrayFinder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjap.umt", myUnreachableMethodsTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjap.uft", myUnreachableFieldsTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjap.tqt", myTightestQualifiersTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjap.cgg", myCallGraphGrapher, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("wjap.purity", myPurityAnalysis, myOptions, myPhaseOptions, myPhaseDumper)); // [AM]
    }

    // Shimple pack
    addPack(p = new BodyPack(Shimple.PHASE, myPhaseOptions, myOptions, myInteractionHandler));

    // Shimple transformation pack
    addPack(p = new BodyPack("stp", myPhaseOptions, myOptions, myInteractionHandler));

    // Shimple optimization pack
    addPack(p = new BodyPack("sop", myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("sop.cpf", myConstantPropagatorAndFolder, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Jimple transformation pack
    addPack(p = new BodyPack("jtp", myPhaseOptions, myOptions, myInteractionHandler));

    // Jimple optimization pack
    addPack(p = new BodyPack("jop", myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("jop.cse", myCommonSubexpressionEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.bcm", myBusyCodeMotion, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.lcm", myLazyCodeMotion, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.cp", myCopyPropagator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.cpf", myConstantPropagatorAndFolder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.cbf", myConditionalBranchFolder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.dae", myDeadAssignmentEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.nce", myNullCheckEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.uce1", myUnreachableCodeEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.ubf1", myUnconditionalBranchFolder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.uce2", myUnreachableCodeEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.ubf2", myUnconditionalBranchFolder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jop.ule", myUnusedLocalEliminator, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Jimple annotation pack
    addPack(p = new BodyPack("jap", myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("jap.npc", myNullPointerChecker, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.npcolorer", myNullPointerColorer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.abc", myArrayBoundsChecker, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.profiling", myProfilingGenerator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.sea", mySideEffectTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.fieldrw", myFieldTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.cgtagger", myCallGraphTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.parity", myParityTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.pat", myParameterAliasTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.rdtagger", myReachingDefsTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.lvtagger", myLiveVarsTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.che", myCastCheckEliminatorDumper, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.umt", myUnreachableMethodTransformer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.lit", myLoopInvariantFinder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.aet", myAvailExprTagger, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("jap.dmt", myDominatorsTagger, myOptions, myPhaseOptions, myPhaseDumper));

    }

    // CFG Viewer
    /*
     * addPack(p = new BodyPack("cfg")); { p.add(new Transform("cfg.output", CFGmyPrinter)); }
     */

    // Grimp body creation
    addPack(p = new BodyPack("gb", myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("gb.a1", myAggregator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("gb.cf", myConstructorFolder, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("gb.a2", myAggregator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("gb.ule", myUnusedLocalEliminator, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Grimp optimization pack
    addPack(p = new BodyPack("gop", myPhaseOptions, myOptions, myInteractionHandler));

    // Baf body creation
    addPack(p = new BodyPack("bb", myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("bb.lso", myLoadStoreOptimizer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("bb.pho", myPeepholeOptimizer, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("bb.ule", myUnusedLocalEliminator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("bb.lp", myLocalPacker, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("bb.sco", myStoreChainOptimizer, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Baf optimization pack
    addPack(p = new BodyPack("bop", myPhaseOptions, myOptions, myInteractionHandler));

    // Code attribute tag aggregation pack
    addPack(p = new BodyPack("tag", myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("tag.ln", myLineNumberTagAggregator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("tag.an", myArrayNullTagAggregator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("tag.dep", myDependenceTagAggregator, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("tag.fieldrw", myFieldTagAggregator, myOptions, myPhaseOptions, myPhaseDumper));
    }

    // Dummy Dava Phase
    /*
     * Nomair A. Naeem 13th Feb 2006 Added so that Dava Options can be added as phase options rather than main soot options
     * since they only make sense when decompiling The db phase options are added in soot_options.xml
     */
    addPack(p = new BodyPack("db", myPhaseOptions, myOptions, myInteractionHandler));
    {
      p.add(new Transform("db.transformations", null, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("db.renamer", null, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("db.deobfuscate", null, myOptions, myPhaseOptions, myPhaseDumper));
      p.add(new Transform("db.force-recompile", null, myOptions, myPhaseOptions, myPhaseDumper));
    }

    onlyStandardPacks = true;
  }

  private void addPack(Pack p) {
    if (packNameToPack.containsKey(p.getPhaseName())) {
      throw new RuntimeException("Duplicate pack " + p.getPhaseName());
    }
    packNameToPack.put(p.getPhaseName(), p);
    packList.add(p);
  }

  public boolean hasPack(String phaseName) {
    return getPhase(phaseName) != null;
  }

  public Pack getPack(String phaseName) {
    Pack p = packNameToPack.get(phaseName);
    return p;
  }

  public boolean hasPhase(String phaseName) {
    return getPhase(phaseName) != null;
  }

  public HasPhaseOptions getPhase(String phaseName) {
    int index = phaseName.indexOf(".");
    if (index < 0) {
      return getPack(phaseName);
    }
    String packName = phaseName.substring(0, index);
    if (!hasPack(packName)) {
      return null;
    }
    return getPack(packName).get(phaseName);
  }

  public Transform getTransform(String phaseName) {
    return (Transform) getPhase(phaseName);
  }

  public Collection<Pack> allPacks() {
    return Collections.unmodifiableList(packList);
  }

  public void runPacks() {
    if (myOptions.oaat()) {
      runPacksForOneClassAtATime();
    } else {
      runPacksNormally();
    }
  }

  private void runPacksForOneClassAtATime() {
    if (myOptions.src_prec() == Options.src_prec_class && myOptions.keep_line_number()) {
      LineNumberAdder lineNumAdder = myLineNumberAdder;
      lineNumAdder.internalTransform("", null);
    }

    setupJAR();
    for (String path : myOptions.process_dir()) {
      // hack1: resolve to signatures only
      for (String cl : mySourceLocator.getClassesUnder(path)) {
        SootClass clazz = myScene.forceResolve(cl, SootClass.SIGNATURES);
        clazz.setApplicationClass();
      }
      // hack2: for each class one after another:
      // a) resolve to bodies
      // b) run packs
      // c) write class
      // d) remove bodies
      for (String cl : mySourceLocator.getClassesUnder(path)) {
        SootClass clazz = null;
        ClassSource source = mySourceLocator.getClassSource(cl);
        try {
          if (source == null) {
            throw new RuntimeException("Could not locate class source");
          }
          clazz = myScene.getSootClass(cl);
          clazz.setResolvingLevel(SootClass.BODIES);
          source.resolve(clazz);
        } finally {
          if (source != null) {
            source.close();
          }
        }

        // Create tags from all values we only have in code assingments
        // now
        for (SootClass sc : myScene.getApplicationClasses()) {
          if (myOptions.validate()) {
            sc.validate();
          }
          if (!sc.isPhantom) {
            myConstantInitializerToTagTransformer.transformClass(sc, true);
          }
        }

        runBodyPacks(clazz);
        // generate output
        writeClass(clazz);

        if (!myOptions.no_writeout_body_releasing()) {
          releaseBodies(clazz);
        }
      }

      // for (String cl : mySourceLocator.getClassesUnder(path)) {
      // SootClass clazz = myScene.forceResolve(cl, SootClass.BODIES);
      // releaseBodies(clazz);
      // myScene.removeClass(clazz);
      // }
    }
    tearDownJAR();

    handleInnerClasses();
  }

  private void runPacksNormally() {
    if (myOptions.src_prec() == Options.src_prec_class && myOptions.keep_line_number()) {
      LineNumberAdder lineNumAdder = myLineNumberAdder;
      lineNumAdder.internalTransform("", null);
    }

    if (myOptions.whole_program() || myOptions.whole_shimple()) {
      runWholeProgramPacks();
    }
    retrieveAllBodies();

    // Create tags from all values we only have in code assignments now
    for (SootClass sc : myScene.getApplicationClasses()) {
      if (myOptions.validate()) {
        sc.validate();
      }
      if (!sc.isPhantom) {
        myConstantInitializerToTagTransformer.transformClass(sc, true);
      }
    }

    // if running coffi cfg metrics, print out results and exit
    if (soot.jbco.Main.metrics) {
      System.exit(0);
    }

    preProcessDAVA();
    if (myOptions.interactive_mode()) {
      if (myInteractionHandler.getInteractionListener() == null) {
        logger.debug("Cannot run in interactive mode. No listeners available. Continuing in regular mode.");
        myOptions.set_interactive_mode(false);
      } else {
        logger.debug("Running in interactive mode.");
      }
    }
    runBodyPacks();
    handleInnerClasses();
  }


  public void runBodyPacks() {
    runBodyPacks(reachableClasses());
  }

  public JarOutputStream getJarFile() {
    return jarFile;
  }

  public void writeOutput() {
    setupJAR();
    if (myOptions.verbose()) {
      myPhaseDumper.dumpBefore("output");
    }
    if (myOptions.output_format() == Options.output_format_dava) {
      postProcessDAVA();
      outputDava();
    } else if (myOptions.output_format() == Options.output_format_dex
        || myOptions.output_format() == Options.output_format_force_dex) {
      writeDexOutput();
    } else {
      writeOutput(reachableClasses());
      tearDownJAR();
    }
    postProcessXML(reachableClasses());

    if (!myOptions.no_writeout_body_releasing()) {
      releaseBodies(reachableClasses());
    }
    if (myOptions.verbose()) {
      myPhaseDumper.dumpAfter("output");
    }
  }

  protected void writeDexOutput() {
    dexPrinter = new DexPrinter(myScene, myOptions, mySourceLocator, this, myEmptySwitchEliminator,
        mySynchronizedMethodTransformer, myFastDexTrapTightener, myTrapSplitter, myJimple, constantFactory);
    writeOutput(reachableClasses());
    dexPrinter.print();
    dexPrinter = null;
  }

  private void setupJAR() {
    if (myOptions.output_jar()) {
      String outFileName = mySourceLocator.getOutputJarName();
      try {
        jarFile = new JarOutputStream(new FileOutputStream(outFileName));
      } catch (IOException e) {
        throw new CompilationDeathException("Cannot open output Jar file " + outFileName);
      }
    } else {
      jarFile = null;
    }
  }

  private void runWholeProgramPacks() {
    if (myOptions.whole_shimple()) {
      myShimpleTransformer.transform();
      getPack("wspp").apply();
      getPack("cg").apply();
      getPack("wstp").apply();
      getPack("wsop").apply();
    } else {
      getPack("wjpp").apply();
      getPack("cg").apply();
      getPack("wjtp").apply();
      getPack("wjop").apply();
      getPack("wjap").apply();
    }
    myPaddleHook.finishPhases();
  }

  /* preprocess classes for DAVA */
  private void preProcessDAVA() {
    if (myOptions.output_format() == Options.output_format_dava) {

      Map<String, String> options = myPhaseOptions.getPhaseOptions("db");
      boolean isSourceJavac = PhaseOptions.getBoolean(options, "source-is-javac");
      if (!isSourceJavac) {
        /*
         * It turns out that the exception attributes of a method i.e. those exceptions that a method can throw are only
         * checked by the Java compiler and not the JVM
         *
         * Javac does place this information into the attributes but other compilers dont hence if the source is not javac
         * then we have to do this fancy analysis to find all the potential exceptions that might get thrown
         *
         * BY DEFAULT the option javac of db is set to true so we assume that the source is javac
         *
         * See ThrowFinder for more details
         */
        if (DEBUG) {
          System.out.println("Source is not Javac hence invoking ThrowFinder");
        }

        myThrowFinder.find();
      } else {
        if (DEBUG) {
          System.out.println("Source is javac hence we dont need to invoke ThrowFinder");
        }
      }

      myPackageNamer.fixNames();

    }
  }

  private void runBodyPacks(final Iterator<SootClass> classes) {
    int threadNum = Runtime.getRuntime().availableProcessors();
    CountingThreadPoolExecutor executor
        = new CountingThreadPoolExecutor(threadNum, threadNum, 30, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());

    while (classes.hasNext()) {
      final SootClass c = classes.next();
      executor.execute(() -> runBodyPacks(c));
    }

    // Wait till all packs have been executed
    try {
      executor.awaitCompletion();
      executor.shutdown();
    } catch (InterruptedException e) {
      // Something went horribly wrong
      throw new RuntimeException("Could not wait for pack threads to " + "finish: " + e.getMessage(), e);
    }

    // If something went wrong, we tell the world
    if (executor.getException() != null) {
      if (executor.getException() instanceof RuntimeException) {
        throw (RuntimeException) executor.getException();
      } else {
        throw new RuntimeException(executor.getException());
      }
    }
  }

  private void handleInnerClasses() {
    InnerClassTagAggregator agg = myInnerClassTagAggregator;
    agg.internalTransform("", null);
  }

  protected void writeOutput(Iterator<SootClass> classes) {
    // If we're writing individual class files, we can write them
    // concurrently. Otherwise, we need to synchronize for not destroying
    // the shared output stream.
    int threadNum = myOptions.output_format() == Options.output_format_class && jarFile == null
        ? Runtime.getRuntime().availableProcessors()
        : 1;
    CountingThreadPoolExecutor executor
        = new CountingThreadPoolExecutor(threadNum, threadNum, 30, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());

    while (classes.hasNext()) {
      final SootClass c = classes.next();
      executor.execute(() -> writeClass(c));
    }

    // Wait till all classes have been written
    try {
      executor.awaitCompletion();
      executor.shutdown();
    } catch (InterruptedException e) {
      // Something went horribly wrong
      throw new RuntimeException("Could not wait for writer threads to " + "finish: " + e.getMessage(), e);
    }

    // If something went wrong, we tell the world
    if (executor.getException() != null) {
      if (executor.getException() instanceof RuntimeException) {
        throw (RuntimeException) executor.getException();
      } else {
        throw new RuntimeException(executor.getException());
      }
    }
  }

  private void tearDownJAR() {
    try {
      if (jarFile != null) {
        jarFile.close();
      }
    } catch (IOException e) {
      throw new CompilationDeathException("Error closing output jar: " + e);
    }
  }

  private void releaseBodies(Iterator<SootClass> classes) {
    while (classes.hasNext()) {
      releaseBodies(classes.next());
    }
  }

  private Iterator<SootClass> reachableClasses() {
    return myScene.getApplicationClasses().snapshotIterator();
  }

  /* post process for DAVA */
  private void postProcessDAVA() {

    Chain<SootClass> appClasses = myScene.getApplicationClasses();

    Map<String, String> options = myPhaseOptions.getPhaseOptions("db.transformations");
    boolean transformations = PhaseOptions.getBoolean(options, "enabled");
    /*
     * apply analyses etc
     */
    for (SootClass s : appClasses) {
      String fileName = mySourceLocator.getFileNameFor(s, myOptions.output_format());

      /*
       * Nomair A. Naeem 5-Jun-2005 Added to remove the *final* bug in Dava (often seen in AspectJ programs)
       */
      myDavaStaticBlockCleaner.staticBlockInlining(s);

      // remove returns from void methods
      VoidReturnRemover.cleanClass(s);

      // remove the default constructor if this is the only one present
      RemoveEmptyBodyDefaultConstructor.checkAndRemoveDefault(s);

      /*
       * Nomair A. Naeem 1st March 2006 Check if we want to apply transformations one reason we might not want to do this is
       * when gathering old metrics data!!
       */

      // debug("analyzeAST","Advanced Analyses ALL DISABLED");

      logger.debug("Analyzing " + fileName + "... ");

      /*
       * Nomair A. Naeem 29th Jan 2006 Added hook into going through each decompiled method again Need it for all the
       * implemented AST analyses
       */
      for (SootMethod m : s.getMethods()) {
        /*
         * 3rd April 2006 Fixing RuntimeException caused when you retrieve an active body when one is not present
         *
         */
        if (m.hasActiveBody()) {
          DavaBody body = (DavaBody) m.getActiveBody();
          // System.out.println("body"+body.toString());
          if (transformations) {
            body.analyzeAST();
          } // if tansformations are enabled
          else {
            body.applyBugFixes();
          }
        } else {
          continue;
        }
      }

    } // going through all classes

    /*
     * Nomair A. Naeem March 6th, 2006
     *
     * SHOULD BE INVOKED ONLY ONCE!!! If interprocedural analyses are turned off they are checked within this method.
     *
     * HAVE TO invoke this analysis since this invokes the renamer!!
     */
    if (transformations) {
      InterProceduralAnalyses.applyInterProceduralAnalyses(myScene, myPhaseOptions, constantFactory, myScene.getPrimTypeCollector(), myClosestAbruptTargetFinder, );
    }
  }

  private void outputDava() {
    Chain<SootClass> appClasses = myScene.getApplicationClasses();

    /*
     * Generate decompiled code
     */
    String pathForBuild = null;
    ArrayList<String> decompiledClasses = new ArrayList<String>();
    Iterator<SootClass> classIt = appClasses.iterator();
    while (classIt.hasNext()) {
      SootClass s = classIt.next();

      OutputStream streamOut = null;
      PrintWriter writerOut = null;
      String fileName = mySourceLocator.getFileNameFor(s, myOptions.output_format());
      decompiledClasses.add(fileName.substring(fileName.lastIndexOf('/') + 1));
      if (pathForBuild == null) {
        pathForBuild = fileName.substring(0, fileName.lastIndexOf('/') + 1);
        // System.out.println(pathForBuild);
      }
      if (myOptions.gzip()) {
        fileName = fileName + ".gz";
      }

      try {
        if (jarFile != null) {
          JarEntry entry = new JarEntry(fileName.replace('\\', '/'));
          jarFile.putNextEntry(entry);
          streamOut = jarFile;
        } else {
          streamOut = new FileOutputStream(fileName);
        }
        if (myOptions.gzip()) {
          streamOut = new GZIPOutputStream(streamOut);
        }
        writerOut = new PrintWriter(new OutputStreamWriter(streamOut));
      } catch (IOException e) {
        throw new CompilationDeathException("Cannot output file " + fileName, e);
      }

      logger.debug("Generating " + fileName + "... ");

      //G.v().out.flush();

      myDavaPrinter.printTo(s, writerOut);

     // G.v().out.flush();

      {
        try {
          writerOut.flush();
          if (jarFile == null) {
            streamOut.close();
          }
        } catch (IOException e) {
          throw new CompilationDeathException("Cannot close output file " + fileName);
        }
      }
    } // going through all classes

    /*
     * Create the build.xml for Dava
     */
    if (pathForBuild != null) {
      // path for build is probably ending in sootoutput/dava/src
      // definetly remove the src
      if (pathForBuild.endsWith("src/")) {
        pathForBuild = pathForBuild.substring(0, pathForBuild.length() - 4);
      }

      String fileName = pathForBuild + "build.xml";

      try {
        OutputStream streamOut = new FileOutputStream(fileName);
        PrintWriter writerOut = new PrintWriter(new OutputStreamWriter(streamOut));
        DavaBuildFile.generate(writerOut, decompiledClasses);
        writerOut.flush();
        streamOut.close();
      } catch (IOException e) {
        throw new CompilationDeathException("Cannot output file " + fileName, e);
      }
    }
  }

  @SuppressWarnings("fallthrough")
  private void runBodyPacks(SootClass c) {
    final int format = myOptions.output_format();
    if (format == Options.output_format_dava) {
      logger.debug("Decompiling {}...", c.getName());

      // January 13th, 2006 SootMethodAddedByDava is set to false for
      // SuperFirstStmtHandler
     // FIXME G.v().SootMethodAddedByDava = false;
    } else {
      logger.debug("Transforming {}...", c.getName());
    }

    boolean produceBaf = false, produceGrimp = false, produceDava = false, produceJimple = true, produceShimple = false;

    switch (format) {
      case Options.output_format_none:
      case Options.output_format_xml:
      case Options.output_format_jimple:
      case Options.output_format_jimp:
      case Options.output_format_template:
      case Options.output_format_dex:
      case Options.output_format_force_dex:
        break;
      case Options.output_format_shimp:
      case Options.output_format_shimple:
        produceShimple = true;
        // FLIP produceJimple
        produceJimple = false;
        break;
      case Options.output_format_dava:
        produceDava = true;
        // FALL THROUGH
      case Options.output_format_grimp:
      case Options.output_format_grimple:
        produceGrimp = true;
        break;
      case Options.output_format_baf:
      case Options.output_format_b:
        produceBaf = true;
        break;
      case Options.output_format_jasmin:
      case Options.output_format_class:
      case Options.output_format_asm:
        produceGrimp = myOptions.via_grimp();
        produceBaf = !produceGrimp;
        break;
      default:
        throw new RuntimeException();
    }

    soot.xml.TagCollector tc = new soot.xml.TagCollector();

    boolean wholeShimple = myOptions.whole_shimple();
    if (myOptions.via_shimple()) {
      produceShimple = true;
    }

    // here we create a copy of the methods so that transformers are able
    // to add method bodies during the following iteration;
    // such adding of methods happens in rare occasions: for instance when
    // resolving a method reference to a non-existing method, then this
    // method is created as a phantom method when phantom-refs are enabled
    ArrayList<SootMethod> methodsCopy = new ArrayList<SootMethod>(c.getMethods());
    for (SootMethod m : methodsCopy) {
      if (DEBUG) {
        if (m.getExceptions().size() != 0) {
          System.out.println("PackManager printing out jimple body exceptions for method " + m.toString() + " "
              + m.getExceptions().toString());
        }
      }

      if (!m.isConcrete()) {
        continue;
      }

      if (produceShimple || wholeShimple) {
        ShimpleBody sBody = null;

        // whole shimple or not?
        {
          Body body = m.retrieveActiveBody();

          if (body instanceof ShimpleBody) {
            sBody = (ShimpleBody) body;
            if (!sBody.isSSA()) {
              sBody.rebuild();
            }
          } else {
            sBody = myShimple.newBody(body);
          }
        }

        m.setActiveBody(sBody);
        getPack("stp").apply(sBody);
        getPack("sop").apply(sBody);

        if (produceJimple || (wholeShimple && !produceShimple)) {
          m.setActiveBody(sBody.toJimpleBody());
        }
      }

      if (produceJimple) {
        Body body = m.retrieveActiveBody();
        // Change
        myCopyPropagator.transform(body);
        myConditionalBranchFolder.transform(body);
        myUnreachableCodeEliminator.transform(body);
        myDeadAssignmentEliminator.transform(body);
        myUnusedLocalEliminator.transform(body);
        getPack("jtp").apply(body);
        if (myOptions.validate()) {
          body.validate();
        }
        getPack("jop").apply(body);
        getPack("jap").apply(body);
        if (myOptions.xml_attributes() && myOptions.output_format() != Options.output_format_jimple) {
          // System.out.println("collecting body tags");
          tc.collectBodyTags(body);
        }
      }

      // myPackManager.getPack("cfg").apply(m.retrieveActiveBody());

      if (produceGrimp) {
        m.setActiveBody(Grimp.newBody(m.getActiveBody(), "gb", myOptions, myPrinter,  this));
        getPack("gop").apply(m.getActiveBody());
      } else if (produceBaf) {
        m.setActiveBody(convertJimpleBodyToBaf(m));
      }
    }

    if (myOptions.xml_attributes() && myOptions.output_format() != Options.output_format_jimple) {
      processXMLForClass(c, tc);
      // System.out.println("processed xml for class");
    }

    if (produceDava) {
      for (SootMethod m : c.getMethods()) {
        if (!m.isConcrete()) {
          continue;
        }
        // all the work done in decompilation is done in DavaBody which
        // is invoked from within newBody
        m.setActiveBody(myDava.newBody(m.getActiveBody()));
      }

      /*
       * January 13th, 2006 SuperFirstStmtHandler might have set SootMethodAddedByDava if it needs to create a new method.
       */
      // could use G to add new method...................
      //FIXME
//      if (G.v().SootMethodAddedByDava) {
//        // System.out.println("PACKMANAGER SAYS:----------------Have to
//        // add the new method(s)");
//        ArrayList<SootMethod> sootMethodsAdded = G.v().SootMethodsAdded;
//        Iterator<SootMethod> it = sootMethodsAdded.iterator();
//        while (it.hasNext()) {
//          c.addMethod(it.next());
//        }
//        G.v().SootMethodsAdded = new ArrayList<SootMethod>();
//        G.v().SootMethodAddedByDava = false;
//      }

    } // end if produceDava
  }

  public BafBody convertJimpleBodyToBaf(SootMethod m) {
    JimpleBody body = (JimpleBody) m.getActiveBody().clone();
    // Change
    // myConditionalBranchFolder.transform(body);
    // myUnreachableCodeEliminator.transform(body);
    // myDeadAssignmentEliminator.transform(body);
    // myUnusedLocalEliminator.transform(body);
    BafBody bafBody = myBaf.newBody(body);
    getPack("bop").apply(bafBody);
    getPack("tag").apply(bafBody);
    if (myOptions.validate()) {
      bafBody.validate();
    }
    return bafBody;
  }

  protected void writeClass(SootClass c) {
    // Create code assignments for those values we only have in code
    // assignments
    if (myOptions.output_format() == Options.output_format_jimple) {
      if (!c.isPhantom) {
        ConstantValueToInitializerTransformer.v().transformClass(c);
      }
    }

    final int format = myOptions.output_format();
    if (format == Options.output_format_none) {
      return;
    }
    if (format == Options.output_format_dava) {
      return;
    }
    if (format == Options.output_format_dex || format == Options.output_format_force_dex) {
      // just add the class to the dex printer, writing is done after
      // adding all classes
      dexPrinter.add(c);
      return;
    }

    OutputStream streamOut = null;
    PrintWriter writerOut = null;

    String fileName = mySourceLocator.getFileNameFor(c, format);
    if (myOptions.gzip()) {
      fileName = fileName + ".gz";
    }

    try {
      if (jarFile != null) {
        // Fix path delimiters according to ZIP specification
        fileName = fileName.replace("\\", "/");
        JarEntry entry = new JarEntry(fileName);
        entry.setMethod(ZipEntry.DEFLATED);
        jarFile.putNextEntry(entry);
        streamOut = jarFile;
      } else {
        new File(fileName).getParentFile().mkdirs();
        streamOut = new FileOutputStream(fileName);
      }
      if (myOptions.gzip()) {
        streamOut = new GZIPOutputStream(streamOut);
      }
      if (format == Options.output_format_class) {
        if (myOptions.jasmin_backend()) {
          streamOut = new JasminOutputStream(streamOut);
        }
      }
      writerOut = new PrintWriter(new OutputStreamWriter(streamOut));
      logger.debug("Writing to " + fileName);
    } catch (IOException e) {
      throw new CompilationDeathException("Cannot output file " + fileName, e);
    }

    if (myOptions.xml_attributes()) {
      myPrinter.setOption(Printer.ADD_JIMPLE_LN);
    }

    switch (format) {
      case Options.output_format_class:
        if (!myOptions.jasmin_backend()) {
          createASMBackend(c).generateClassFile(streamOut);
          break;
        }
      case Options.output_format_jasmin:
        createJasminBackend(c).print(writerOut);
        break;
      case Options.output_format_jimp:
      case Options.output_format_shimp:
      case Options.output_format_b:
      case Options.output_format_grimp:
        myPrinter.setOption(Printer.USE_ABBREVIATIONS);
        myPrinter.printTo(c, writerOut);
        break;
      case Options.output_format_baf:
      case Options.output_format_jimple:
      case Options.output_format_shimple:
      case Options.output_format_grimple:
        writerOut = new PrintWriter(new EscapedWriter(new OutputStreamWriter(streamOut)));
        myPrinter.printTo(c, writerOut);
        break;
      case Options.output_format_xml:
        writerOut = new PrintWriter(new EscapedWriter(new OutputStreamWriter(streamOut)));
        myXMLPrinter.printJimpleStyleTo(c, writerOut);
        break;
      case Options.output_format_template:
        writerOut = new PrintWriter(new OutputStreamWriter(streamOut));
        myTemplatePrinter.printTo(c, writerOut);
        break;
      case Options.output_format_asm:
        createASMBackend(c).generateTextualRepresentation(writerOut);
        break;
      default:
        throw new RuntimeException();
    }

    try {
      writerOut.flush();
      if (jarFile == null) {
        streamOut.close();
        writerOut.close();
      } else {
        jarFile.closeEntry();
      }
    } catch (IOException e) {
      throw new CompilationDeathException("Cannot close output file " + fileName);
    }
  }

  /**
   * Factory method for creating a new backend on top of Jasmin
   *
   * @param c
   *          The class for which to create a Jasmin-based backend
   * @return The Jasmin-based backend for writing the given class into bytecode
   */
  private AbstractJasminClass createJasminBackend(SootClass c) {
    if (c.containsBafBody()) {
      return new soot.baf.JasminClass(c);
    } else {
      return new soot.jimple.JasminClass(c, myOptions);
    }
  }

  /**
   * Factory method for creating a new backend on top of ASM. At the moment, we always start from BAF. Custom implementations
   * can use other techniques.
   *
   * @param c
   *          The class for which to create the ASM backend
   * @return The ASM backend for writing the class into bytecode
   */
  protected BafASMBackend createASMBackend(SootClass c) {
    int java_version = myOptions.java_version();
    return new BafASMBackend(c, java_version, myScene, myOptions, myScene.getPrimTypeCollector());
  }

  private void postProcessXML(Iterator<SootClass> classes) {
    if (!myOptions.xml_attributes()) {
      return;
    }
    if (myOptions.output_format() != Options.output_format_jimple) {
      return;
    }
    while (classes.hasNext()) {
      SootClass c = classes.next();
      processXMLForClass(c);
    }
  }

  private void processXMLForClass(SootClass c, TagCollector tc) {
    int ofmt = myOptions.output_format();
    final int format = ofmt != Options.output_format_none ? ofmt : Options.output_format_jimple;
    String fileName = mySourceLocator.getFileNameFor(c, format);
    XMLAttributesPrinter xap = new XMLAttributesPrinter(fileName, mySourceLocator.getOutputDir());
    xap.printAttrs(c, tc);
  }

  /**
   * assumption: only called when <code>myOptions.output_format() == Options.output_format_jimple</code>
   */
  private void processXMLForClass(SootClass c) {
    final int format = myOptions.output_format();
    String fileName = mySourceLocator.getFileNameFor(c, format);
    XMLAttributesPrinter xap = new XMLAttributesPrinter(fileName, mySourceLocator.getOutputDir());
    xap.printAttrs(c);
  }

  private void releaseBodies(SootClass cl) {
    Iterator<SootMethod> methodIt = cl.methodIterator();
    while (methodIt.hasNext()) {
      SootMethod m = methodIt.next();

      if (m.hasActiveBody()) {
        m.releaseActiveBody();
      }
    }
  }

  private void retrieveAllBodies() {
    // The old coffi front-end is not thread-safe
    int threadNum = myOptions.coffi() ? 1 : Runtime.getRuntime().availableProcessors();
    CountingThreadPoolExecutor executor
        = new CountingThreadPoolExecutor(threadNum, threadNum, 30, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());

    Iterator<SootClass> clIt = reachableClasses();
    while (clIt.hasNext()) {
      SootClass cl = clIt.next();
      // note: the following is a snapshot iterator;
      // this is necessary because it can happen that phantom methods
      // are added during resolution
      Iterator<SootMethod> methodIt = new ArrayList<SootMethod>(cl.getMethods()).iterator();
      while (methodIt.hasNext()) {
        final SootMethod m = methodIt.next();
        if (m.isConcrete()) {
          executor.execute(new Runnable() {

            @Override
            public void run() {
              m.retrieveActiveBody();
            }

          });
        }
      }
    }

    // Wait till all method bodies have been loaded
    try {
      executor.awaitCompletion();
      executor.shutdown();
    } catch (InterruptedException e) {
      // Something went horribly wrong
      throw new RuntimeException("Could not wait for loader threads to " + "finish: " + e.getMessage(), e);
    }

    // If something went wrong, we tell the world
    if (executor.getException() != null) {
      if (executor.getException() instanceof RuntimeException) {
        throw (RuntimeException) executor.getException();
      } else {
        throw new RuntimeException(executor.getException());
      }
    }
  }

}
