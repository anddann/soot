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

public class Environment {

  private TypeConstants myTypeConstants;

  @Inject
  public Environment(TypeConstants myTypeConstants) {
    this.myTypeConstants = myTypeConstants;
  }


  private final ConstantObject clsloaders = new GeneralConstObject(myTypeConstants.CLASSLOADERCLASS, "classloader");

  private final ConstantObject processes = new GeneralConstObject(myTypeConstants.PROCESSCLASS, "process");

  private final ConstantObject threads = new GeneralConstObject(myTypeConstants.THREADCLASS, "thread");

  private final ConstantObject filesystem = new GeneralConstObject(myTypeConstants.FILESYSTEMCLASS, "filesystem");

  /*
   * representing all possible java.lang.Class type objects, mostly used by reflection.
   */
  private final ConstantObject classobject = new GeneralConstObject(myTypeConstants.CLASSCLASS, "unknownclass");

  /*
   * representing all possible java.lang.String objects, used by any getName() or similiar methods.
   */
  private final ConstantObject stringobject = new GeneralConstObject(myTypeConstants.STRINGCLASS, "unknownstring");

  /*
   * to get finer resolution, it is worth to distinguish arrays and general scalars. WARNING: making array with
   * java.lang.Object type may be a problem!
   */
  private final ConstantObject leastarray = new GeneralConstObject(myTypeConstants.LEASTCLASS, "leastarray");

  /*
   * makes a general unknown object, WARNING: unknown object must have the least type, it won't be useful when resolve
   * virtual calls. Null type is a good candidate for this.
   */
  private final ConstantObject leastobject = new GeneralConstObject(myTypeConstants.LEASTCLASS, "leastobject");

  /*
   * provides an abstract java.lang.reflect.Field object.
   */
  private final ConstantObject fieldobject = new GeneralConstObject(myTypeConstants.FIELDCLASS, "field");

  /*
   * provides an abstract java.lang.reflect.Method object
   */
  private final ConstantObject methodobject = new GeneralConstObject(myTypeConstants.METHODCLASS, "method");

  /*
   * provides an abstract java.lang.reflect.Constructor object
   */
  private final ConstantObject constructorobject = new GeneralConstObject(myTypeConstants.CONSTRUCTORCLASS, "constructor");

  /*
   * represents the PrivilegedActionException thrown by AccessController.doPrivileged
   */
  private final ConstantObject privilegedActionException
      = new GeneralConstObject(myTypeConstants.PRIVILEGEDACTIONEXCEPTION, "constructor");

  /********************* INTERFACE to NATIVE METHODS *******************/
  public ConstantObject getClassLoaderObject() {
    return clsloaders;
  }

  public ConstantObject getProcessObject() {
    return processes;
  }

  public ConstantObject getThreadObject() {
    return threads;
  }

  public ConstantObject getClassObject() {
    return classobject;
  }

  public ConstantObject getStringObject() {
    return stringobject;
  }

  public ConstantObject getLeastArrayObject() {
    return leastarray;
  }

  public ConstantObject getLeastObject() {
    return leastobject;
  }

  public ConstantObject getFieldObject() {
    return fieldobject;
  }

  public ConstantObject getMethodObject() {
    return methodobject;
  }

  public ConstantObject getConstructorObject() {
    return constructorobject;
  }

  public ConstantObject getFileSystemObject() {
    return filesystem;
  }

  public ConstantObject getPrivilegedActionExceptionObject() {
    return privilegedActionException;
  }
}
