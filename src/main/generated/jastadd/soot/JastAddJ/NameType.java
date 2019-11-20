package soot.JastAddJ;

import soot.*;
import soot.jimple.Jimple;

/**
  * @ast class
 * 
 */
public class NameType extends java.lang.Object {

    private NameType() {
      super();
    }


    public static final NameType NO_NAME = new NameType();


    public static final NameType PACKAGE_NAME = new NameType() {
      public Access reclassify(String name, int start, int end, Scene myScene, PrimTypeCollector primTypeCollector, Jimple myJimple) { return new PackageAccess(name, start, end); }
    };


    public static final NameType TYPE_NAME = new NameType() {
      public Access reclassify(String name, int start, int end, Scene myScene, PrimTypeCollector primTypeCollector, Jimple myJimple) { return new TypeAccess(name, start, end,myScene,primTypeCollector,myJimple); }
    };


    public static final NameType PACKAGE_OR_TYPE_NAME = new NameType() {
      public Access reclassify(String name, int start, int end, Scene myScene, PrimTypeCollector primTypeCollector, Jimple myJimple) { return new PackageOrTypeAccess(name, start, end); }
    };


    public static final NameType AMBIGUOUS_NAME = new NameType() {
      public Access reclassify(String name, int start, int end, Scene myScene, PrimTypeCollector primTypeCollector, Jimple myJimple) { return new AmbiguousAccess(name, start, end); }
    };


    public static final NameType METHOD_NAME = new NameType();


    public static final NameType ARRAY_TYPE_NAME = new NameType();


    public static final NameType ARRAY_READ_NAME = new NameType();


    public static final NameType EXPRESSION_NAME = new NameType() {
      public Access reclassify(String name, int start, int end, Scene myScene, PrimTypeCollector primTypeCollector, Jimple myJimple) { return new VarAccess(name, start, end); }
    };



    public Access reclassify(String name, int start, int end, Scene myScene, PrimTypeCollector primTypeCollector, Jimple myJimple) {
      throw new Error("Can not reclassify ParseName node " + name);
    }


}
