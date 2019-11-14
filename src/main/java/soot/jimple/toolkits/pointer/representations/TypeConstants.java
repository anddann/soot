package soot.jimple.toolkits.pointer.representations;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Feng Qian
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

import soot.AnySubType;
import soot.G;
import soot.PhaseOptions;
import soot.RefType;
import soot.Scene;
import soot.Type;
import soot.options.CGOptions;

public class TypeConstants {
  private final PhaseOptions myPhaseOptions;


  public Type OBJECTCLASS;
  public Type STRINGCLASS;
  public Type CLASSLOADERCLASS;
  public Type PROCESSCLASS;
  public Type THREADCLASS;
  public Type CLASSCLASS;
  public Type LEASTCLASS;
  public Type FIELDCLASS;
  public Type METHODCLASS;
  public Type CONSTRUCTORCLASS;
  public Type FILESYSTEMCLASS;
  public Type PRIVILEGEDACTIONEXCEPTION;

  @Inject
  public TypeConstants(PhaseOptions myPhaseOptions, Scene myScene) {
    this.myPhaseOptions = myPhaseOptions;
    int jdkver = new CGOptions(myPhaseOptions.getPhaseOptions("cg")).jdkver();

    OBJECTCLASS = RefType.v("java.lang.Object",myScene);

    STRINGCLASS = RefType.v("java.lang.String",myScene);

    CLASSLOADERCLASS = AnySubType.v(RefType.v("java.lang.ClassLoader",myScene));

    PROCESSCLASS = AnySubType.v(RefType.v("java.lang.Process",myScene));

    THREADCLASS = AnySubType.v(RefType.v("java.lang.Thread",myScene));

    CLASSCLASS = RefType.v("java.lang.Class",myScene);

    LEASTCLASS = AnySubType.v(RefType.v("java.lang.Object",myScene));

    FIELDCLASS = RefType.v("java.lang.reflect.Field",myScene);

    METHODCLASS = RefType.v("java.lang.reflect.Method",myScene);

    CONSTRUCTORCLASS = RefType.v("java.lang.reflect.Constructor",myScene);

    if (jdkver >= 2) {
      FILESYSTEMCLASS = AnySubType.v(RefType.v("java.io.FileSystem",myScene));
    }

    if (jdkver >= 2) {
      PRIVILEGEDACTIONEXCEPTION = AnySubType.v(RefType.v("java.security.PrivilegedActionException",myScene));
    }
  }
}
