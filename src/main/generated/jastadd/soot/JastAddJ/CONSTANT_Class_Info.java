package soot.JastAddJ;

import soot.*;
import soot.jimple.*;

/**
  * @ast class
 * 
 */
public class CONSTANT_Class_Info extends CONSTANT_Info {

    public int name_index;
    private Scene myScene;
    private Jimple myJimple;
    private PrimTypeCollector primeTypeCollector;


    public CONSTANT_Class_Info(BytecodeParser parser, Scene myScene, Jimple myJimple, PrimTypeCollector primeTypeCollector) {
      super(parser);
        this.myScene = myScene;
        this.myJimple = myJimple;
        this.primeTypeCollector = primeTypeCollector;
        name_index = p.u2();
    }



    public String toString() {
      return "ClassInfo: " + name();
    }



    public String name() {
      String name = ((CONSTANT_Utf8_Info) this.p.constantPool[name_index]).string();
      //name = name.replaceAll("\\/", ".");
      name = name.replace('/', '.');
      return name;
    }



    public String simpleName() {
      String name = name();
      //name = name.replace('$', '.');
      int pos = name.lastIndexOf('.');
      return name.substring(pos + 1, name.length());
    }



    public String packageDecl() {
      String name = name();
      //name = name.replace('$', '.');
      int pos = name.lastIndexOf('.');
      if(pos == -1)
        return "";
      return name.substring(0, pos);
    }



    public Access access() {
      String name = name();
      int pos = name.lastIndexOf('.');
      String typeName = name.substring(pos + 1, name.length());
      String packageName = pos == -1 ? "" : name.substring(0, pos);
      if(typeName.indexOf('$') != -1)
        return new BytecodeTypeAccess(packageName, typeName);
      else
        return new TypeAccess(packageName, typeName,myScene, primeTypeCollector,myJimple);
    }


}
