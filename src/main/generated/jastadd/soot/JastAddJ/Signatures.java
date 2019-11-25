package soot.JastAddJ;

import java.util.ArrayList;
import java.util.Collection;

import soot.PhaseOptions;
import soot.PrimTypeCollector;
import soot.Scene;
import soot.SootResolver;
import soot.dava.toolkits.base.misc.PackageNamer;
import soot.jimple.ConstantFactory;
import soot.jimple.Jimple;
import soot.options.Options;

/**
  * @ast class
 * 
 */
public class Signatures extends java.lang.Object {

    // simple parser framework
    String data;


    int pos;
  private Scene myScene;
  private Options myOptions;
  private PackageNamer myPackageNamer;
  private Jimple myJimple;
  private PrimTypeCollector primTypeCollector;
  private ConstantFactory constantFactory;
  private SootResolver mySootResolver;
  private PhaseOptions myPhaseOptions;


  public Signatures(String s, Scene myScene, Options myOptions, PackageNamer myPackageNamer, Jimple myJimple, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, SootResolver mySootResolver, PhaseOptions myPhaseOptions) {
      data = s;
    this.myScene = myScene;
    this.myOptions = myOptions;
    this.myPackageNamer = myPackageNamer;
    this.myJimple = myJimple;
    this.primTypeCollector = primTypeCollector;
    this.constantFactory = constantFactory;
    this.mySootResolver = mySootResolver;
    this.myPhaseOptions = myPhaseOptions;
    pos = 0;
    }



    public boolean next(String s) {
      for(int i = 0; i < s.length(); i++)
        if(data.charAt(pos + i) != s.charAt(i))
          return false;
      return true;
    }



    public void eat(String s) {
      for(int i = 0; i < s.length(); i++)
        if(data.charAt(pos + i) != s.charAt(i))
          error(s);
      pos += s.length();
    }



    public void error(String s) {
      throw new Error("Expected " + s + " but found " + data.substring(pos));
    }



    public String identifier() {
      int i = pos;
      while(Character.isJavaIdentifierPart(data.charAt(i)))
        i++;
      String result = data.substring(pos, i);
      pos = i;
      return result;
    }



    public boolean eof() {
      return pos == data.length();
    }



    // 4.4.4 Signatures

    public static class ClassSignature extends Signatures {
      public ClassSignature(String s, Scene myScene, Options myOptions, PackageNamer myPackageNamer, Jimple myJimple, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, SootResolver mySootResolver, PhaseOptions myPhaseOptions) {
        super(s, myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);
        this.myScene = myScene;
        this.myOptions = myOptions;
        this.myPackageNamer = myPackageNamer;
        this.myJimple = myJimple;
        this.primTypeCollector = primTypeCollector;
        this.constantFactory = constantFactory;
        this.mySootResolver = mySootResolver;
        this.myPhaseOptions = myPhaseOptions;
        classSignature();
      }
      void classSignature() {
        if(next("<"))
          formalTypeParameters();
        superclassSignature = parseSuperclassSignature();
        while(!eof()) {
          superinterfaceSignature.add(parseSuperinterfaceSignature());
        }
      }

      public boolean hasFormalTypeParameters() { return typeParameters != null; }
      public List typeParameters() { return typeParameters; }

      public boolean hasSuperclassSignature() { return superclassSignature != null; }
      public Access superclassSignature() { return superclassSignature; }
      protected Access superclassSignature;

      public boolean hasSuperinterfaceSignature() { return superinterfaceSignature.getNumChildNoTransform() != 0; }
      public List superinterfaceSignature() { return superinterfaceSignature; }

      private Scene myScene;
      private Options myOptions;
      private PackageNamer myPackageNamer;
      private Jimple myJimple;
      private PrimTypeCollector primTypeCollector;
      private ConstantFactory constantFactory;
      private SootResolver mySootResolver;
      private PhaseOptions myPhaseOptions;
      protected List superinterfaceSignature = new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);

      Access parseSuperclassSignature() {
        return classTypeSignature();
      }

      Access parseSuperinterfaceSignature() {
        return classTypeSignature();
      }
    }



    public static class FieldSignature extends Signatures {
      public FieldSignature(String s, Scene myScene,Options myOptions, PackageNamer myPackageNamer, Jimple myJimple, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, SootResolver mySootResolver, PhaseOptions myPhaseOptions) {
        super(s, myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);
        fieldTypeAccess = fieldTypeSignature();
      }
      Access fieldTypeAccess() {
        return fieldTypeAccess;
      }
      private Access fieldTypeAccess;
    }



    public static class MethodSignature extends Signatures {
      public MethodSignature(String s, Scene myScene, Options myOptions, PackageNamer myPackageNamer, Jimple myJimple, ConstantFactory constantFactory, PrimTypeCollector primTypeCollector, SootResolver mySootResolver, PhaseOptions myPhaseOptions) {
        super(s, myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);
        this.myScene = myScene;
        this.myOptions = myOptions;
        this.myPackageNamer = myPackageNamer;
        this.myJimple = myJimple;
        this.constantFactory = constantFactory;
        this.primTypeCollector = primTypeCollector;
        this.mySootResolver = mySootResolver;
        this.myPhaseOptions = myPhaseOptions;
        methodTypeSignature();
      }
      void methodTypeSignature() {
        if(next("<"))
          formalTypeParameters();
        eat("(");
        while(!next(")")) {
          parameterTypes.add(typeSignature());
        }
        eat(")");
        returnType = parseReturnType();
        while(!eof()) {
          exceptionList.add(throwsSignature());
        }
      }
      Access parseReturnType() {
        if(next("V")) {
          eat("V");
          return new PrimitiveTypeAccess("void");
        }
        else {
          return typeSignature();
        }
      }

      Access throwsSignature() {
        eat("^");
        if(next("L")) {
          return classTypeSignature();
        }
        else {
          return typeVariableSignature();
        }
      }

      public boolean hasFormalTypeParameters() { return typeParameters != null; }
      public List typeParameters() { return typeParameters; }

      public Collection parameterTypes() { return parameterTypes; }
      protected Collection parameterTypes = new ArrayList();

      public List exceptionList() { return exceptionList; }
      public boolean hasExceptionList() { return exceptionList.getNumChildNoTransform() != 0; }

      private Scene myScene;
      private Options myOptions;
      private PackageNamer myPackageNamer;
      private Jimple myJimple;
      private ConstantFactory constantFactory;
      private PrimTypeCollector primTypeCollector;
      private SootResolver mySootResolver;
      private PhaseOptions myPhaseOptions;
      protected List exceptionList = new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);

      protected Access returnType = null;
      public boolean hasReturnType() { return returnType != null; }
      public Access returnType() { return returnType; }
    }



    protected List typeParameters;



    void formalTypeParameters() {
      eat("<");
      typeParameters = new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);
      do {
        typeParameters.add(formalTypeParameter());
      } while(!next(">"));
      eat(">");
    }



    TypeVariable formalTypeParameter() {
      String id = identifier();
      List bounds = new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);
      Access classBound = classBound();
      if(classBound != null)
        bounds.add(classBound);
      while(next(":")) {
        bounds.add(interfaceBound());
      }
      if(bounds.getNumChildNoTransform() == 0)
        bounds.add(new TypeAccess("java.lang", "Object",myScene,primTypeCollector,myJimple));
      Modifiers astNodes = new Modifiers(new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions), myPhaseOptions,myScene, myOptions, myPackageNamer, myJimple, constantFactory, primTypeCollector, mySootResolver);
      List list = new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);
      return new TypeVariable(astNodes, id, list, bounds,myScene,myJimple,mySootResolver,myPackageNamer,myOptions,primTypeCollector,constantFactory,myPhaseOptions);
    }



    Access classBound() {
      eat(":");
      if(nextIsFieldTypeSignature()) {
        return fieldTypeSignature();
      }
      else {
        return null;
        //return new TypeAccess("java.lang", "Object");
      }
    }



    Access interfaceBound() {
      eat(":");
      return fieldTypeSignature();
    }




    Access fieldTypeSignature() {
      if(next("L"))
        return classTypeSignature();
      else if(next("["))
        return arrayTypeSignature();
      else if(next("T"))
        return typeVariableSignature();
      else
        error("L or [ or T");
      return null; // error never returns
    }


    boolean nextIsFieldTypeSignature() {
      return next("L") || next("[") || next("T");
    }



    Access classTypeSignature() {
      eat("L");
      // Package and Type Name
      StringBuffer packageName = new StringBuffer();
      String typeName = identifier();
      while(next("/")) {
        eat("/");
        if(packageName.length() != 0)
          packageName.append(".");
        packageName.append(typeName);
        typeName = identifier();
      }
      Access a = typeName.indexOf('$') == -1 ?
        new TypeAccess(packageName.toString(), typeName,myScene,primTypeCollector,myJimple) :
        new BytecodeTypeAccess(packageName.toString(), typeName);
      if(next("<")) { // type arguments of top level type
        a = new ParTypeAccess(a, typeArguments());
      }
      while(next(".")) { // inner classes
        a = a.qualifiesAccess(classTypeSignatureSuffix());
      }
      eat(";");
      return a;
    }



    Access classTypeSignatureSuffix() {
      eat(".");
      String id = identifier();
      Access a = id.indexOf('$') == -1 ?
        new TypeAccess(id,myScene,primTypeCollector,myJimple) : new BytecodeTypeAccess("", id);
      if(next("<")) {
        a = new ParTypeAccess(a, typeArguments());
      }
      return a;
    }



    Access typeVariableSignature() {
      eat("T");
      String id = identifier();
      eat(";");
      return new TypeAccess(id,myScene,primTypeCollector,myJimple);
    }



    List typeArguments() {
      eat("<");
      List list = new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions);
      do {
        list.add(typeArgument());
      } while(!next(">"));
      eat(">");
      return list;
    }



    Access typeArgument() {
      if(next("*")) {
        eat("*");
        return new Wildcard();
      }
      else if(next("+")) {
        eat("+");
        return new WildcardExtends(fieldTypeSignature());
      }
      else if(next("-")) {
        eat("-");
        return new WildcardSuper(fieldTypeSignature());
      }
      else {
        return fieldTypeSignature();
      }
    }



    Access arrayTypeSignature() {
      eat("[");
      return new ArrayTypeAccess(typeSignature());
    }



    Access typeSignature() {
      if(nextIsFieldTypeSignature()) {
        return fieldTypeSignature();
      }
      else {
        return baseType();
      }
    }



    Access baseType() {
      if(next("B")) { eat("B"); return new PrimitiveTypeAccess("byte"); }
      else if(next("C")) { eat("C"); return new PrimitiveTypeAccess("char"); }
      else if(next("D")) { eat("D"); return new PrimitiveTypeAccess("double"); }
      else if(next("F")) { eat("F"); return new PrimitiveTypeAccess("float"); }
      else if(next("I")) { eat("I"); return new PrimitiveTypeAccess("int"); }
      else if(next("J")) { eat("J"); return new PrimitiveTypeAccess("long"); }
      else if(next("S")) { eat("S"); return new PrimitiveTypeAccess("short"); }
      else if(next("Z")) { eat("Z"); return new PrimitiveTypeAccess("boolean"); }
      error("baseType");
      return null; // error never returns
    }


}
