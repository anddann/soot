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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.Attribute;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import soot.*;
import soot.coffi.Util;
import soot.jimple.ConstantFactory;
import soot.options.Options;
import soot.tagkit.DoubleConstantValueTag;
import soot.tagkit.EnclosingMethodTag;
import soot.tagkit.FloatConstantValueTag;
import soot.tagkit.InnerClassTag;
import soot.tagkit.IntegerConstantValueTag;
import soot.tagkit.LongConstantValueTag;
import soot.tagkit.SignatureTag;
import soot.tagkit.SourceFileTag;
import soot.tagkit.StringConstantValueTag;
import soot.tagkit.Tag;

/**
 * Constructs a Soot class from a visited class.
 *
 * @author Aaloan Miftah
 */
@SuppressWarnings({ "unchecked", "rawtypes" })
public class SootClassBuilder extends ClassVisitor {

  protected TagBuilder tb;
  protected final SootClass klass;
  protected final Set<soot.Type> deps;
  private Scene myScene;
  private SootResolver mySootResolver;
  private Options myOptions;
  private PrimTypeCollector primTypeCollector;
  private ConstantFactory constantFactory;
  private LambdaMetaFactory myLambdaMetaFactory;
  private PackManager myPackManager;
  private Util myCoffiUtil;
  private PhaseOptions myPhaseOptions;

  /**
   * Constructs a new Soot class builder.
   * @param klass
   *          Soot class to build.
   * @param myScene
   * @param mySootResolver
   * @param myOptions
   * @param primTypeCollector
   * @param constantFactory
   * @param myLambdaMetaFactory
   * @param myPackManager
   * @param myCoffiUtil
   * @param myPhaseOptions
   */
  protected SootClassBuilder(SootClass klass, Scene myScene, SootResolver mySootResolver, Options myOptions, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, LambdaMetaFactory myLambdaMetaFactory, PackManager myPackManager, Util myCoffiUtil, PhaseOptions myPhaseOptions) {
    super(Opcodes.ASM5);
    this.klass = klass;
    this.myScene = myScene;
    this.mySootResolver = mySootResolver;
    this.myOptions = myOptions;
    this.primTypeCollector = primTypeCollector;
    this.constantFactory = constantFactory;
    this.myLambdaMetaFactory = myLambdaMetaFactory;
    this.myPackManager = myPackManager;
    this.myCoffiUtil = myCoffiUtil;
    this.myPhaseOptions = myPhaseOptions;
    this.deps = new HashSet();
  }

  private TagBuilder getTagBuilder() {
    TagBuilder t = tb;
    if (t == null) {
      t = tb = new TagBuilder(klass, this);
    }
    return t;
  }

  void addDep(String s) {
    addDep(RefType.v(AsmUtil.baseTypeName(s), myScene));
  }

  /**
   * Adds a dependency of the target class.
   *
   * @param s
   *          name, or type of class.
   */
  void addDep(soot.Type s) {
    deps.add(s);
  }

  @Override
  public void visit(int version, int access, String name, String signature, String superName, String[] interfaces) {
    name = AsmUtil.toQualifiedName(name);
    if (!name.equals(klass.getName())) {
      throw new RuntimeException("Class names not equal! " + name + " != " + klass.getName());
    }
    klass.setModifiers(access & ~Opcodes.ACC_SUPER);
    if (superName != null) {
      superName = AsmUtil.toQualifiedName(superName);
      addDep(RefType.v(superName, myScene));
      klass.setSuperclass(mySootResolver.makeClassRef(superName));
    }
    for (String intrf : interfaces) {
      intrf = AsmUtil.toQualifiedName(intrf);
      addDep(RefType.v(intrf, myScene));

      SootClass interfaceClass = mySootResolver.makeClassRef(intrf);
      interfaceClass.setModifiers(interfaceClass.getModifiers() | Modifier.INTERFACE);
      klass.addInterface(interfaceClass);
    }
    if (signature != null) {
      klass.addTag(new SignatureTag(signature));
    }
  }

  @Override
  public FieldVisitor visitField(int access, String name, String desc, String signature, Object value) {
    soot.Type type = AsmUtil.toJimpleType(desc, primTypeCollector, myScene);
    addDep(type);
    SootField field = myScene.makeSootField(name, type, access);
    Tag tag;
    if (value instanceof Integer) {
      tag = new IntegerConstantValueTag((Integer) value);
    } else if (value instanceof Float) {
      tag = new FloatConstantValueTag((Float) value, constantFactory);
    } else if (value instanceof Long) {
      tag = new LongConstantValueTag((Long) value);
    } else if (value instanceof Double) {
      tag = new DoubleConstantValueTag((Double) value, constantFactory);
    } else if (value instanceof String) {
      tag = new StringConstantValueTag(value.toString(), constantFactory);
    } else {
      tag = null;
    }
    if (tag != null) {
      field.addTag(tag);
    }
    if (signature != null) {
      field.addTag(new SignatureTag(signature));
    }
    field = klass.getOrAddField(field);
    return new FieldBuilder(field, this);
  }

  @Override
  public MethodVisitor visitMethod(int access, String name, String desc, String signature, String[] exceptions) {
    List<SootClass> thrownExceptions;
    if (exceptions == null || exceptions.length == 0) {
      thrownExceptions = Collections.emptyList();
    } else {
      int len = exceptions.length;
      thrownExceptions = new ArrayList<SootClass>(len);
      for (int i = 0; i != len; i++) {
        String ex = AsmUtil.toQualifiedName(exceptions[i]);
        addDep(RefType.v(ex, myScene));
        thrownExceptions.add(mySootResolver.makeClassRef(ex));
      }
    }
    List<soot.Type> sigTypes = AsmUtil.toJimpleDesc(desc, primTypeCollector, myScene);
    for (soot.Type type : sigTypes) {
      addDep(type);
    }
    SootMethod method
        = myScene.makeSootMethod(name, sigTypes, sigTypes.remove(sigTypes.size() - 1), access, thrownExceptions);
    if (signature != null) {
      method.addTag(new SignatureTag(signature));
    }
    method = klass.getOrAddMethod(method);
    return new MethodBuilder(method, this, desc, exceptions, myScene, myOptions, primTypeCollector, constantFactory, myLambdaMetaFactory, myPackManager, myCoffiUtil, myPhaseOptions, myPrinter);
  }

  @Override
  public void visitSource(String source, String debug) {
    if (source != null) {
      klass.addTag(new SourceFileTag(source));
    }
  }

  @Override
  public void visitInnerClass(String name, String outerName, String innerName, int access) {
    klass.addTag(new InnerClassTag(name, outerName, innerName, access));

    // soot does not resolve all inner classes, e.g., java.util.stream.FindOps$FindSink$... is not resolved
    String innerClassname = AsmUtil.toQualifiedName(name);
    deps.add(RefType.v(innerClassname, myScene));

  }

  @Override
  public void visitOuterClass(String owner, String name, String desc) {

    if (name != null) {
      klass.addTag(new EnclosingMethodTag(owner, name, desc));
    }

    owner = AsmUtil.toQualifiedName(owner);
    deps.add(RefType.v(owner, myScene));
    klass.setOuterClass(mySootResolver.makeClassRef(owner));
  }

  @Override
  public AnnotationVisitor visitAnnotation(String desc, boolean visible) {
    return getTagBuilder().visitAnnotation(desc, visible);
  }

  @Override
  public void visitAttribute(Attribute attr) {
    getTagBuilder().visitAttribute(attr);
  }
}
