package soot.dava.toolkits.base.misc;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Jerome Miecznikowski
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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;

import soot.Modifier;
import soot.PrimTypeCollector;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.baf.Baf;
import soot.dava.DavaBody;
import soot.dava.internal.asg.AugmentedStmt;
import soot.dava.internal.javaRep.DStaticInvokeExpr;
import soot.dava.internal.javaRep.DVirtualInvokeExpr;
import soot.grimp.Grimp;
import soot.grimp.internal.GInvokeStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.MonitorStmt;
import soot.options.Options;

public class MonitorConverter {

  private final Scene myScene;
  private final PackageNamer myPackageNamer;
  private final Options myOptions;
  ;
  private Baf myBaf;

  @Inject
  public MonitorConverter(Scene myScene, PackageNamer myPackageNamer, Options myOptions,
                          , Baf myBaf, PrimTypeCollector primTypeCollector) {
    this.myScene = myScene;
    this.myPackageNamer = myPackageNamer;
    this.myOptions = myOptions;

    this.myBaf = myBaf;
    SootClass davaMonitor = new SootClass("soot.dava.toolkits.base.DavaMonitor.DavaMonitor", this.myOptions, Modifier.PUBLIC,
        this.myScene, this.myPackageNamer);
    davaMonitor.setSuperclass(this.myScene.loadClassAndSupport("java.lang.Object"));

    LinkedList objectSingleton = new LinkedList();
    objectSingleton.add(RefType.v("java.lang.Object", myScene));
    v = this.myScene.makeSootMethod("v", new LinkedList(),
        RefType.v("soot.dava.toolkits.base.DavaMonitor.DavaMonitor", myScene), Modifier.PUBLIC | Modifier.STATIC);
    enter = this.myScene.makeSootMethod("enter", objectSingleton, primTypeCollector.getVoidType(),
        Modifier.PUBLIC | Modifier.SYNCHRONIZED);
    exit = this.myScene.makeSootMethod("exit", objectSingleton, primTypeCollector.getVoidType(),
        Modifier.PUBLIC | Modifier.SYNCHRONIZED);
    davaMonitor.addMethod(v);
    davaMonitor.addMethod(enter);
    davaMonitor.addMethod(exit);

    this.myScene.addClass(davaMonitor);
  }

  private final SootMethod v, enter, exit;

  public void convert(DavaBody body) {
    for (AugmentedStmt mas : body.get_MonitorFacts()) {
      MonitorStmt ms = (MonitorStmt) mas.get_Stmt();

      body.addToImportList("soot.dava.toolkits.base.DavaMonitor.DavaMonitor");

      ArrayList arg = new ArrayList();
      arg.add(ms.getOp());

      if (ms instanceof EnterMonitorStmt) {
        mas.set_Stmt(new GInvokeStmt(new DVirtualInvokeExpr(new DStaticInvokeExpr(v.makeRef(), new ArrayList(), ),
            enter.makeRef(), arg, new HashSet<Object>(),  myBaf, myScene)));
      } else {
        mas.set_Stmt(new GInvokeStmt(new DVirtualInvokeExpr(new DStaticInvokeExpr(v.makeRef(), new ArrayList(), ),
            exit.makeRef(), arg, new HashSet<Object>(),  myBaf, myScene)));
      }
    }
  }
}
