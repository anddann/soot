package soot.javaToJimple;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2004 Jennifer Lhotak
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
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Stack;

import polyglot.ast.Block;
import polyglot.ast.FieldDecl;
import polyglot.ast.Try;
import polyglot.util.IdentityKey;

import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.Trap;
import soot.Value;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.Stmt;

public class JimpleBodyBuilder extends AbstractJimpleBodyBuilder {

  public JimpleBodyBuilder() {
    // ext(null);
    // base(this);
  }

  protected List<List<Stmt>> beforeReturn; // list used to exclude return
  // stmts from synch try blocks
  protected List<List<Stmt>> afterReturn; // list used to exclude return stmts
  // from synch try blocks

  protected ArrayList<Trap> exceptionTable; // list of exceptions
  protected Stack<Stmt> endControlNoop = new Stack<Stmt>(); // for break
  protected Stack<Stmt> condControlNoop = new Stack<Stmt>(); // continue
  protected Stack<Value> monitorStack; // for synchronized blocks
  protected Stack<Try> tryStack; // for try stmts in case of returns
  protected Stack<Try> catchStack; // for catch stmts in case of returns

  protected Stack<Stmt> trueNoop = new Stack<Stmt>();
  protected Stack<Stmt> falseNoop = new Stack<Stmt>();

  protected HashMap<String, Stmt> labelBreakMap; // for break label --> nop to
  // jump to
  protected HashMap<String, Stmt> labelContinueMap; // for continue label -->
  // nop to jump to

  protected HashMap<polyglot.ast.Stmt, Stmt> labelMap;
  protected HashMap<IdentityKey, Local> localsMap = new HashMap<IdentityKey, Local>(); // localInst
  // -->
  // soot
  // local

  protected HashMap getThisMap = new HashMap(); // type --> local to ret
  protected Local specialThisLocal; // === body.getThisLocal();
  protected Local outerClassParamLocal; // outer class this

  protected int paramRefCount = 0; // counter for param ref stmts

  protected LocalGenerator lg; // for generated locals not in orig src

  /**
   * Jimple Body Creation
   */
  @Override
  public soot.jimple.JimpleBody createJimpleBody(polyglot.ast.Block block, List formals, soot.SootMethod sootMethod) {

    createBody(sootMethod);

    lg = new LocalGenerator(body);
    // create this formal except for static methods
    if (!soot.Modifier.isStatic(sootMethod.getModifiers())) {

      soot.RefType type = sootMethod.getDeclaringClass().getType();
      specialThisLocal = soot.jimple.myJimple.newLocal("this", type);
      body.getLocals().add(specialThisLocal);

      soot.jimple.ThisRef thisRef = soot.jimple.myJimple.newThisRef(type);

      soot.jimple.Stmt thisStmt = soot.jimple.myJimple.newIdentityStmt(specialThisLocal, thisRef);
      body.getUnits().add(thisStmt);

      // this is causing problems - no this in java code -> no tags
      // Util.addLineTag(thisStmt, block);
    }

    int formalsCounter = 0;

    // create outer class this param ref for inner classes except for static
    // inner classes - this is not needed
    int outerIndex = sootMethod.getDeclaringClass().getName().lastIndexOf("$");

    if ((outerIndex != -1) && (sootMethod.getName().equals("<init>"))) {
      SootField this0Field = sootMethod.getDeclaringClass().getFieldByNameUnsafe("this$0");
      if (this0Field != null) {
        // we know its an inner non static class can get outer class
        // from field ref of the this$0 field
        soot.SootClass outerClass = ((soot.RefType) this0Field.getType()).getSootClass();
        soot.Local outerLocal = lg.generateLocal(outerClass.getType());

        soot.jimple.ParameterRef paramRef = soot.jimple.myJimple.newParameterRef(outerClass.getType(), formalsCounter);
        paramRefCount++;
        soot.jimple.Stmt stmt = soot.jimple.myJimple.newIdentityStmt(outerLocal, paramRef);
        stmt.addTag(new soot.tagkit.EnclosingTag());
        body.getUnits().add(stmt);

        ((soot.javaToJimple.PolyglotMethodSource) sootMethod.getSource()).setOuterClassThisInit(outerLocal);
        outerClassParamLocal = outerLocal;
        formalsCounter++;
      }
    }

    // handle formals
    if (formals != null) {
      String[] formalNames = new String[formals.size()];
      Iterator formalsIt = formals.iterator();
      while (formalsIt.hasNext()) {
        polyglot.ast.Formal formal = (polyglot.ast.Formal) formalsIt.next();
        createFormal(formal, formalsCounter);
        formalNames[formalsCounter] = formal.name();
        formalsCounter++;
      }
      body.getMethod().addTag(new soot.tagkit.ParamNamesTag(formalNames));
    }

    // handle final local params
    ArrayList<SootField> finalsList = ((PolyglotMethodSource) body.getMethod().getSource()).getFinalsList();
    if (finalsList != null) {
      Iterator<SootField> finalsIt = finalsList.iterator();
      while (finalsIt.hasNext()) {
        soot.SootField sf = finalsIt.next();
        soot.jimple.ParameterRef paramRef = soot.jimple.myJimple.newParameterRef(sf.getType(), formalsCounter);
        paramRefCount++;
        soot.jimple.Stmt stmt = soot.jimple.myJimple.newIdentityStmt(lg.generateLocal(sf.getType()), paramRef);
        body.getUnits().add(stmt);
        formalsCounter++;
      }
    }

    createBlock(block);

    // if method is <clinit> handle static field inits
    if (sootMethod.getName().equals("<clinit>")) {

      handleAssert(sootMethod);
      handleStaticFieldInits(sootMethod);
      handleStaticInitializerBlocks(sootMethod);
    }

    // determine if body has a return stmt
    boolean hasReturn = false;
    if (block != null) {
      Iterator it = block.statements().iterator();
      while (it.hasNext()) {
        Object next = it.next();
        if (next instanceof polyglot.ast.Return) {
          hasReturn = true;
        }
      }
    }

    soot.Type retType = body.getMethod().getReturnType();
    // only do this if noexplicit return
    if ((!hasReturn) && (retType instanceof soot.VoidType)) {
      soot.jimple.Stmt retStmt = soot.jimple.myJimple.newReturnVoidStmt();
      body.getUnits().add(retStmt);
    }

    // add exceptions from exceptionTable
    if (exceptionTable != null) {
      Iterator<Trap> trapsIt = exceptionTable.iterator();
      while (trapsIt.hasNext()) {
        body.getTraps().add(trapsIt.next());
      }
    }
    return body;

  }

  private void handleAssert(soot.SootMethod sootMethod) {
    if (!((soot.javaToJimple.PolyglotMethodSource) sootMethod.getSource()).hasAssert()) {
      return;
    }
    ((soot.javaToJimple.PolyglotMethodSource) sootMethod.getSource()).addAssertInits(body);
  }

  /**
   * adds any needed field inits
   */
  private void handleFieldInits(soot.SootMethod sootMethod) {

    ArrayList<FieldDecl> fieldInits = ((soot.javaToJimple.PolyglotMethodSource) sootMethod.getSource()).getFieldInits();
    if (fieldInits != null) {
      handleFieldInits(fieldInits);
    }
  }

  protected void handleFieldInits(ArrayList<FieldDecl> fieldInits) {
    Iterator<FieldDecl> fieldInitsIt = fieldInits.iterator();
    while (fieldInitsIt.hasNext()) {
      polyglot.ast.FieldDecl field = fieldInitsIt.next();
      String fieldName = field.name();
      polyglot.ast.Expr initExpr = field.init();
      soot.SootClass currentClass = body.getMethod().getDeclaringClass();
      soot.SootFieldRef sootField = soot.myScene.makeFieldRef(currentClass, fieldName,
          Util.getSootType(field.type().type()), field.flags().isStatic());

      soot.Local base = specialThisLocal;

      soot.jimple.FieldRef fieldRef = soot.jimple.myJimple.newInstanceFieldRef(base, sootField);

      soot.Value sootExpr;
      if (initExpr instanceof polyglot.ast.ArrayInit) {
        sootExpr = getArrayInitLocal((polyglot.ast.ArrayInit) initExpr, field.type().type());
      } else {
        // System.out.println("field init expr: "+initExpr);
        sootExpr = base().createAggressiveExpr(initExpr, false, false);
        // System.out.println("soot expr: "+sootExpr);
      }
      if (sootExpr instanceof soot.jimple.ConditionExpr) {
        sootExpr = handleCondBinExpr((soot.jimple.ConditionExpr) sootExpr);
      }

      soot.jimple.AssignStmt assign;
      if (sootExpr instanceof soot.Local) {
        assign = soot.jimple.myJimple.newAssignStmt(fieldRef, sootExpr);
      } else if (sootExpr instanceof soot.jimple.Constant) {
        assign = soot.jimple.myJimple.newAssignStmt(fieldRef, sootExpr);
      } else {
        throw new RuntimeException("fields must assign to local or constant only");
      }
      body.getUnits().add(assign);
      Util.addLnPosTags(assign, initExpr.position());
      Util.addLnPosTags(assign.getRightOpBox(), initExpr.position());
    }
  }

  /**
   * adds this field for the outer class
   */
  private void handleOuterClassThisInit(soot.SootMethod sootMethod) {
    // static inner classes are different
    SootField this0Field = body.getMethod().getDeclaringClass().getFieldByNameUnsafe("this$0");
    if (this0Field != null) {
      soot.jimple.FieldRef fieldRef = soot.jimple.myJimple.newInstanceFieldRef(specialThisLocal, this0Field.makeRef());
      soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(fieldRef, outerClassParamLocal);
      body.getUnits().add(stmt);
    }
  }

  /**
   * adds any needed static field inits
   */
  private void handleStaticFieldInits(soot.SootMethod sootMethod) {

    ArrayList<FieldDecl> staticFieldInits
        = ((soot.javaToJimple.PolyglotMethodSource) sootMethod.getSource()).getStaticFieldInits();
    if (staticFieldInits != null) {
      Iterator<FieldDecl> staticFieldInitsIt = staticFieldInits.iterator();
      while (staticFieldInitsIt.hasNext()) {
        polyglot.ast.FieldDecl field = staticFieldInitsIt.next();
        String fieldName = field.name();
        polyglot.ast.Expr initExpr = field.init();
        soot.SootClass currentClass = body.getMethod().getDeclaringClass();
        soot.SootFieldRef sootField = soot.myScene.makeFieldRef(currentClass, fieldName,
            Util.getSootType(field.type().type()), field.flags().isStatic());
        soot.jimple.FieldRef fieldRef = soot.jimple.myJimple.newStaticFieldRef(sootField);

        // System.out.println("initExpr: "+initExpr);
        soot.Value sootExpr;
        if (initExpr instanceof polyglot.ast.ArrayInit) {
          sootExpr = getArrayInitLocal((polyglot.ast.ArrayInit) initExpr, field.type().type());
        } else {
          // System.out.println("field init expr: "+initExpr);
          sootExpr = base().createAggressiveExpr(initExpr, false, false);
          // System.out.println("soot expr: "+sootExpr);

          if (sootExpr instanceof soot.jimple.ConditionExpr) {
            sootExpr = handleCondBinExpr((soot.jimple.ConditionExpr) sootExpr);
          }
        }

        soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(fieldRef, sootExpr);

        body.getUnits().add(assign);
        Util.addLnPosTags(assign, initExpr.position());

      }
    }
  }

  /**
   * init blocks get created within init methods in Jimple
   */
  private void handleInitializerBlocks(soot.SootMethod sootMethod) {
    ArrayList<Block> initializerBlocks
        = ((soot.javaToJimple.PolyglotMethodSource) sootMethod.getSource()).getInitializerBlocks();

    if (initializerBlocks != null) {

      handleStaticBlocks(initializerBlocks);
    }
  }

  protected void handleStaticBlocks(ArrayList<Block> initializerBlocks) {
    Iterator<Block> initBlocksIt = initializerBlocks.iterator();
    while (initBlocksIt.hasNext()) {
      createBlock(initBlocksIt.next());
    }
  }

  /**
   * static init blocks get created in clinit methods in Jimple
   */
  private void handleStaticInitializerBlocks(soot.SootMethod sootMethod) {
    ArrayList<Block> staticInitializerBlocks
        = ((soot.javaToJimple.PolyglotMethodSource) sootMethod.getSource()).getStaticInitializerBlocks();

    if (staticInitializerBlocks != null) {

      Iterator<Block> staticInitBlocksIt = staticInitializerBlocks.iterator();
      while (staticInitBlocksIt.hasNext()) {
        createBlock(staticInitBlocksIt.next());
      }
    }
  }

  /**
   * create body and make it be active
   */
  private void createBody(soot.SootMethod sootMethod) {
    body = soot.jimple.myJimple.newBody(sootMethod);
    sootMethod.setActiveBody(body);

  }

  /**
   * Block creation
   */
  private void createBlock(polyglot.ast.Block block) {

    if (block == null) {
      return;
    }

    // handle stmts
    Iterator it = block.statements().iterator();
    while (it.hasNext()) {
      Object next = it.next();
      if (next instanceof polyglot.ast.Stmt) {
        createStmt((polyglot.ast.Stmt) next);
      } else {
        throw new RuntimeException("Unexpected - Unhandled Node");
      }
    }
  }

  /**
   * Catch Formal creation - method parameters
   */
  private soot.Local createCatchFormal(polyglot.ast.Formal formal) {

    soot.Type sootType = Util.getSootType(formal.type().type());
    soot.Local formalLocal = createLocal(formal.localInstance());
    soot.jimple.CaughtExceptionRef exceptRef = soot.jimple.myJimple.newCaughtExceptionRef();
    soot.jimple.Stmt stmt = soot.jimple.myJimple.newIdentityStmt(formalLocal, exceptRef);
    body.getUnits().add(stmt);

    Util.addLnPosTags(stmt, formal.position());
    Util.addLnPosTags(((soot.jimple.IdentityStmt) stmt).getRightOpBox(), formal.position());

    String[] names = new String[] { formal.name() };
    stmt.addTag(new soot.tagkit.ParamNamesTag(names));
    return formalLocal;
  }

  /**
   * Formal creation - method parameters
   */
  private void createFormal(polyglot.ast.Formal formal, int counter) {

    soot.Type sootType = Util.getSootType(formal.type().type());
    soot.Local formalLocal = createLocal(formal.localInstance());
    soot.jimple.ParameterRef paramRef = soot.jimple.myJimple.newParameterRef(sootType, counter);
    paramRefCount++;
    soot.jimple.Stmt stmt = soot.jimple.myJimple.newIdentityStmt(formalLocal, paramRef);

    body.getUnits().add(stmt);

    Util.addLnPosTags(((soot.jimple.IdentityStmt) stmt).getRightOpBox(), formal.position());
    Util.addLnPosTags(stmt, formal.position());

  }

  /**
   * Literal Creation
   */
  private soot.Value createLiteral(polyglot.ast.Lit lit) {
    if (lit instanceof polyglot.ast.IntLit) {
      polyglot.ast.IntLit intLit = (polyglot.ast.IntLit) lit;
      long litValue = intLit.value();
      if (intLit.kind() == polyglot.ast.IntLit.INT) {
        return soot.jimple.IntConstant.v((int) litValue);
      } else {
        // System.out.println(litValue);
        return soot.jimple.LongConstant.v(litValue);
      }
    } else if (lit instanceof polyglot.ast.StringLit) {
      String litValue = ((polyglot.ast.StringLit) lit).value();
      return soot.jimple.StringConstant.v(litValue);
    } else if (lit instanceof polyglot.ast.NullLit) {
      return soot.jimple.myNullConstant;
    } else if (lit instanceof polyglot.ast.FloatLit) {
      polyglot.ast.FloatLit floatLit = (polyglot.ast.FloatLit) lit;
      double litValue = floatLit.value();
      if (floatLit.kind() == polyglot.ast.FloatLit.DOUBLE) {
        return soot.jimple.DoubleConstant.v(floatLit.value());
      } else {
        return soot.jimple.FloatConstant.v((float) (floatLit.value()));
      }
    } else if (lit instanceof polyglot.ast.CharLit) {
      char litValue = ((polyglot.ast.CharLit) lit).value();
      return soot.jimple.IntConstant.v(litValue);
    } else if (lit instanceof polyglot.ast.BooleanLit) {
      boolean litValue = ((polyglot.ast.BooleanLit) lit).value();
      if (litValue) {
        return soot.jimple.IntConstant.v(1);
      } else {
        return soot.jimple.IntConstant.v(0);
      }
    } else if (lit instanceof polyglot.ast.ClassLit) {
      return getSpecialClassLitLocal((polyglot.ast.ClassLit) lit);
    } else {
      throw new RuntimeException("Unknown Literal - Unhandled: " + lit.getClass());
    }
  }

  /**
   * Local Creation
   */

  // this should be used for polyglot locals and formals
  private soot.Local createLocal(polyglot.types.LocalInstance localInst) {

    soot.Type sootType = Util.getSootType(localInst.type());
    String name = localInst.name();
    soot.Local sootLocal = createLocal(name, sootType);

    localsMap.put(new polyglot.util.IdentityKey(localInst), sootLocal);
    return sootLocal;
  }

  // this should be used for generated locals only
  private soot.Local createLocal(String name, soot.Type sootType) {
    soot.Local sootLocal = soot.jimple.myJimple.newLocal(name, sootType);
    body.getLocals().add(sootLocal);
    return sootLocal;
  }

  /**
   * Local Retreival
   */
  private soot.Local getLocal(polyglot.ast.Local local) {

    return getLocal(local.localInstance());
  }

  /**
   * Local Retreival
   */
  private soot.Local getLocal(polyglot.types.LocalInstance li) {

    if (localsMap.containsKey(new polyglot.util.IdentityKey(li))) {
      soot.Local sootLocal = localsMap.get(new polyglot.util.IdentityKey(li));
      return sootLocal;
    } else if (body.getMethod().getDeclaringClass().declaresField("val$" + li.name(), Util.getSootType(li.type()))) {
      soot.Local fieldLocal = generateLocal(li.type());
      soot.SootFieldRef field = soot.myScene.makeFieldRef(body.getMethod().getDeclaringClass(), "val$" + li.name(),
          Util.getSootType(li.type()), false);
      soot.jimple.FieldRef fieldRef = soot.jimple.myJimple.newInstanceFieldRef(specialThisLocal, field);
      soot.jimple.AssignStmt assign = soot.jimple.myJimple.newAssignStmt(fieldLocal, fieldRef);
      body.getUnits().add(assign);
      return fieldLocal;
    }
    /*
     * else { throw new RuntimeException("Trying unsuccessfully to get local: "+li.name()); }
     */
    else {
      // else create access meth in outer for val$fieldname
      // get the this$0 field to find the type of an outer class - has
      // to have one because local/anon inner can't declare static
      // memebers so for deepnesting not in static context for these
      // cases

      soot.SootClass currentClass = body.getMethod().getDeclaringClass();
      boolean fieldFound = false;

      while (!fieldFound) {
        if (!currentClass.declaresFieldByName("this$0")) {
          throw new RuntimeException(
              "Trying to get field val$" + li.name() + " from some outer class but can't access the outer class of: "
                  + currentClass.getName() + "!" + " current class contains fields: " + currentClass.getFields());
        }
        soot.SootClass outerClass = ((soot.RefType) currentClass.getFieldByName("this$0").getType()).getSootClass();
        // look for field of type li.type and name val$li.name in outer
        // class
        if (outerClass.declaresField("val$" + li.name(), Util.getSootType(li.type()))) {
          fieldFound = true;
        }
        currentClass = outerClass;
        // repeat until found in some outer class
      }
      // create and add accessor to that outer class (indic as current)
      soot.SootMethod methToInvoke = makeLiFieldAccessMethod(currentClass, li);

      // invoke and return
      // generate a local that corresponds to the invoke of that meth
      ArrayList methParams = new ArrayList();
      methParams.add(getThis(currentClass.getType()));

      soot.Local res = Util.getPrivateAccessFieldInvoke(methToInvoke.makeRef(), methParams, body, lg);
      return res;
    }
  }

  private soot.SootMethod makeLiFieldAccessMethod(soot.SootClass classToInvoke, polyglot.types.LocalInstance li) {
    String name = "access$" + soot.javaToJimple.myInitialResolver.getNextPrivateAccessCounter() + "00";
    ArrayList paramTypes = new ArrayList();
    paramTypes.add(classToInvoke.getType());

    soot.SootMethod meth = myScene.makeSootMethod(name, paramTypes, Util.getSootType(li.type()), soot.Modifier.STATIC);

    classToInvoke.addMethod(meth);
    PrivateFieldAccMethodSource src
        = new PrivateFieldAccMethodSource(Util.getSootType(li.type()), "val$" + li.name(), false, classToInvoke);
    meth.setActiveBody(src.getBody(meth, null));
    meth.addTag(new soot.tagkit.SyntheticTag());
    return meth;
  }

  /**
   * Stmt creation
   */
  @Override
  protected void createStmt(polyglot.ast.Stmt stmt) {
    // System.out.println("stmt: "+stmt.getClass());
    if (stmt instanceof polyglot.ast.Eval) {
      base().createAggressiveExpr(((polyglot.ast.Eval) stmt).expr(), false, false);
    } else if (stmt instanceof polyglot.ast.If) {
      createIf2((polyglot.ast.If) stmt);
    } else if (stmt instanceof polyglot.ast.LocalDecl) {
      createLocalDecl((polyglot.ast.LocalDecl) stmt);
    } else if (stmt instanceof polyglot.ast.Block) {
      createBlock((polyglot.ast.Block) stmt);
    } else if (stmt instanceof polyglot.ast.While) {
      createWhile2((polyglot.ast.While) stmt);
    } else if (stmt instanceof polyglot.ast.Do) {
      createDo2((polyglot.ast.Do) stmt);
    } else if (stmt instanceof polyglot.ast.For) {
      createForLoop2((polyglot.ast.For) stmt);
    } else if (stmt instanceof polyglot.ast.Switch) {
      createSwitch((polyglot.ast.Switch) stmt);
    } else if (stmt instanceof polyglot.ast.Return) {
      createReturn((polyglot.ast.Return) stmt);
    } else if (stmt instanceof polyglot.ast.Branch) {
      createBranch((polyglot.ast.Branch) stmt);
    } else if (stmt instanceof polyglot.ast.ConstructorCall) {
      createConstructorCall((polyglot.ast.ConstructorCall) stmt);
    } else if (stmt instanceof polyglot.ast.Empty) {
      // do nothing empty stmt
    } else if (stmt instanceof polyglot.ast.Throw) {
      createThrow((polyglot.ast.Throw) stmt);
    } else if (stmt instanceof polyglot.ast.Try) {
      createTry((polyglot.ast.Try) stmt);
    } else if (stmt instanceof polyglot.ast.Labeled) {
      createLabeled((polyglot.ast.Labeled) stmt);
    } else if (stmt instanceof polyglot.ast.Synchronized) {
      createSynchronized((polyglot.ast.Synchronized) stmt);
    } else if (stmt instanceof polyglot.ast.Assert) {
      createAssert((polyglot.ast.Assert) stmt);
    } else if (stmt instanceof polyglot.ast.LocalClassDecl) {
      createLocalClassDecl((polyglot.ast.LocalClassDecl) stmt);
    } else {
      throw new RuntimeException("Unhandled Stmt: " + stmt.getClass());
    }
  }

  private boolean needSootIf(soot.Value sootCond) {
    if (sootCond instanceof soot.jimple.IntConstant) {
      if (((soot.jimple.IntConstant) sootCond).value == 1) {
        return false;
      }
    }
    return true;
  }

  /**
   * If Stmts Creation - only add line-number tags to if (the other stmts needing tags are created elsewhere
   */
  /*
   * private void createIf(polyglot.ast.If ifExpr){
   *
   * // create true/false noops to handle cond and/or trueNoop.push(soot.jimple.myJimple.newNopStmt());
   * falseNoop.push(soot.jimple.myJimple.newNopStmt());
   *
   * // handle cond polyglot.ast.Expr condition = ifExpr.cond(); soot.Value sootCond = base().createExpr(condition);
   *
   * // pop true false noops right away soot.jimple.Stmt tNoop = (soot.jimple.Stmt)trueNoop.pop(); soot.jimple.Stmt fNoop =
   * (soot.jimple.Stmt)falseNoop.pop();
   *
   * boolean needIf = needSootIf(sootCond); if (!(sootCond instanceof soot.jimple.ConditionExpr)) { sootCond =
   * soot.jimple.myJimple.newEqExpr(sootCond, soot.jimple.IntConstant.v(0)); } else { sootCond =
   * reverseCondition((soot.jimple.ConditionExpr)sootCond); sootCond = handleDFLCond((soot.jimple.ConditionExpr)sootCond); }
   *
   * // add if soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
   *
   * if (needIf) { soot.jimple.IfStmt ifStmt = soot.jimple.myJimple.newIfStmt(sootCond, noop1);
   * body.getUnits().add(ifStmt); // add line and pos tags Util.addLnPosTags(ifStmt.getConditionBox(), condition.position());
   * Util.addLnPosTags(ifStmt, condition.position()); }
   *
   * // add true nop body.getUnits().add(tNoop);
   *
   * // add consequence polyglot.ast.Stmt consequence = ifExpr.consequent(); createStmt(consequence);
   *
   * soot.jimple.Stmt noop2 = null; if (ifExpr.alternative() != null){ noop2 = soot.jimple.myJimple.newNopStmt();
   * soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(noop2); body.getUnits().add(goto1); }
   *
   * body.getUnits().add(noop1);
   *
   * // add false nop body.getUnits().add(fNoop);
   *
   *
   * // handle alternative polyglot.ast.Stmt alternative = ifExpr.alternative(); if (alternative != null){
   * createStmt(alternative); body.getUnits().add(noop2); }
   *
   *
   * }
   */

  /**
   * If Stmts Creation - only add line-number tags to if (the other stmts needing tags are created elsewhere
   */
  private void createIf2(polyglot.ast.If ifExpr) {

    soot.jimple.NopStmt endTgt = soot.jimple.myJimple.newNopStmt();
    soot.jimple.NopStmt brchTgt = soot.jimple.myJimple.newNopStmt();

    // handle cond
    polyglot.ast.Expr condition = ifExpr.cond();
    createBranchingExpr(condition, brchTgt, false);

    // add consequence
    polyglot.ast.Stmt consequence = ifExpr.consequent();
    createStmt(consequence);

    soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(endTgt);
    body.getUnits().add(goto1);

    body.getUnits().add(brchTgt);

    // handle alternative
    polyglot.ast.Stmt alternative = ifExpr.alternative();
    if (alternative != null) {
      createStmt(alternative);
    }
    body.getUnits().add(endTgt);

  }

  private void createBranchingExpr(polyglot.ast.Expr expr, soot.jimple.Stmt tgt, boolean boto) {
    if (expr instanceof polyglot.ast.Binary && ((polyglot.ast.Binary) expr).operator() == polyglot.ast.Binary.COND_AND) {
      polyglot.ast.Binary cond_and = (polyglot.ast.Binary) expr;
      if (boto) {
        soot.jimple.Stmt t1 = soot.jimple.myJimple.newNopStmt();
        createBranchingExpr(cond_and.left(), t1, false);
        createBranchingExpr(cond_and.right(), tgt, true);
        body.getUnits().add(t1);
      } else {
        createBranchingExpr(cond_and.left(), tgt, false);
        createBranchingExpr(cond_and.right(), tgt, false);
      }
    } else if (expr instanceof polyglot.ast.Binary
        && ((polyglot.ast.Binary) expr).operator() == polyglot.ast.Binary.COND_OR) {
      polyglot.ast.Binary cond_or = (polyglot.ast.Binary) expr;
      if (boto) {
        createBranchingExpr(cond_or.left(), tgt, true);
        createBranchingExpr(cond_or.right(), tgt, true);
      } else {
        soot.jimple.Stmt t1 = soot.jimple.myJimple.newNopStmt();
        createBranchingExpr(cond_or.left(), t1, true);
        createBranchingExpr(cond_or.right(), tgt, false);
        body.getUnits().add(t1);
      }

    } else if (expr instanceof polyglot.ast.Unary && ((polyglot.ast.Unary) expr).operator() == polyglot.ast.Unary.NOT) {
      polyglot.ast.Unary not = (polyglot.ast.Unary) expr;
      createBranchingExpr(not.expr(), tgt, !boto);
    } else {
      soot.Value sootCond = base().createAggressiveExpr(expr, false, false);

      boolean needIf = needSootIf(sootCond);
      if (needIf) {
        if (!(sootCond instanceof soot.jimple.ConditionExpr)) {
          if (!boto) {
            sootCond = soot.jimple.myJimple.newEqExpr(sootCond, soot.jimple.IntConstant.v(0));
          } else {
            sootCond = soot.jimple.myJimple.newNeExpr(sootCond, soot.jimple.IntConstant.v(0));
          }
        }

        else {
          sootCond = handleDFLCond((soot.jimple.ConditionExpr) sootCond);
          if (!boto) {
            sootCond = reverseCondition((soot.jimple.ConditionExpr) sootCond);
          }
        }

        soot.jimple.IfStmt ifStmt = soot.jimple.myJimple.newIfStmt(sootCond, tgt);
        body.getUnits().add(ifStmt);
        // add line and pos tags
        Util.addLnPosTags(ifStmt.getConditionBox(), expr.position());
        Util.addLnPosTags(ifStmt, expr.position());
      }
      // for an "if(true) goto tgt" we have to branch always; for an
      // "if(true) goto tgt" we just
      // do nothing at all
      // (if boto is false then we have to reverse the meaning)
      else if (sootCond instanceof IntConstant && (((IntConstant) sootCond).value == 1) == boto) {
        soot.jimple.GotoStmt gotoStmt = soot.jimple.myJimple.newGotoStmt(tgt);
        body.getUnits().add(gotoStmt);
        // add line and pos tags
        Util.addLnPosTags(gotoStmt, expr.position());
      }
    }
  }

  /**
   * While Stmts Creation
   */
  /*
   * private void createWhile(polyglot.ast.While whileStmt){
   *
   * // create true/false noops to handle cond and/or trueNoop.push(soot.jimple.myJimple.newNopStmt());
   * falseNoop.push(soot.jimple.myJimple.newNopStmt());
   *
   * soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt(); soot.jimple.Stmt noop2 =
   * soot.jimple.myJimple.newNopStmt();
   *
   * // these are for break and continue endControlNoop.push(soot.jimple.myJimple.newNopStmt());
   * condControlNoop.push(soot.jimple.myJimple.newNopStmt());
   *
   * body.getUnits().add(noop2);
   *
   * // handle cond soot.jimple.Stmt continueStmt = (soot.jimple.Stmt)condControlNoop.pop();
   * body.getUnits().add(continueStmt); condControlNoop.push(continueStmt);
   *
   * polyglot.ast.Expr condition = whileStmt.cond(); soot.Value sootCond = base().createExpr(condition); soot.jimple.Stmt
   * tNoop = (soot.jimple.Stmt)trueNoop.pop(); soot.jimple.Stmt fNoop = (soot.jimple.Stmt)falseNoop.pop(); boolean needIf =
   * needSootIf(sootCond); if (!(sootCond instanceof soot.jimple.ConditionExpr)) { sootCond =
   * soot.jimple.myJimple.newEqExpr(sootCond, soot.jimple.IntConstant.v(0)); } else { sootCond =
   * reverseCondition((soot.jimple.ConditionExpr)sootCond); sootCond = handleDFLCond((soot.jimple.ConditionExpr)sootCond); }
   *
   * if (needIf){ soot.jimple.IfStmt ifStmt = soot.jimple.myJimple.newIfStmt(sootCond, noop1);
   *
   * body.getUnits().add(ifStmt); Util.addLnPosTags(ifStmt.getConditionBox(), condition.position());
   * Util.addLnPosTags(ifStmt, condition.position()); }
   *
   * body.getUnits().add(tNoop); createStmt(whileStmt.body()); soot.jimple.GotoStmt gotoLoop =
   * soot.jimple.myJimple.newGotoStmt(noop2); body.getUnits().add(gotoLoop);
   *
   * body.getUnits().add((soot.jimple.Stmt)(endControlNoop.pop())); body.getUnits().add(noop1); body.getUnits().add(fNoop);
   * condControlNoop.pop(); }
   */

  /**
   * While Stmts Creation
   */
  private void createWhile2(polyglot.ast.While whileStmt) {

    soot.jimple.Stmt brchTgt = soot.jimple.myJimple.newNopStmt();
    soot.jimple.Stmt beginTgt = soot.jimple.myJimple.newNopStmt();

    body.getUnits().add(beginTgt);

    // these are for break and continue
    endControlNoop.push(soot.jimple.myJimple.newNopStmt());
    condControlNoop.push(soot.jimple.myJimple.newNopStmt());

    // handle cond
    soot.jimple.Stmt continueStmt = condControlNoop.pop();
    body.getUnits().add(continueStmt);
    condControlNoop.push(continueStmt);

    polyglot.ast.Expr condition = whileStmt.cond();
    createBranchingExpr(condition, brchTgt, false);
    createStmt(whileStmt.body());
    soot.jimple.GotoStmt gotoLoop = soot.jimple.myJimple.newGotoStmt(beginTgt);
    body.getUnits().add(gotoLoop);

    body.getUnits().add((endControlNoop.pop()));
    body.getUnits().add(brchTgt);
    condControlNoop.pop();
  }

  /**
   * DoWhile Stmts Creation
   */
  /*
   * private void createDo(polyglot.ast.Do doStmt){
   *
   * // create true/false noops to handle cond and/or soot.jimple.Stmt tNoop = soot.jimple.myJimple.newNopStmt();
   * soot.jimple.Stmt fNoop = soot.jimple.myJimple.newNopStmt();
   *
   * soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt(); body.getUnits().add(noop1);
   *
   * // add true noop - for cond and/or body.getUnits().add(tNoop);
   *
   * // these are for break and continue endControlNoop.push(soot.jimple.myJimple.newNopStmt());
   * condControlNoop.push(soot.jimple.myJimple.newNopStmt());
   *
   * // handle body createStmt(doStmt.body());
   *
   * // handle cond soot.jimple.Stmt continueStmt = (soot.jimple.Stmt)condControlNoop.pop();
   * body.getUnits().add(continueStmt); condControlNoop.push(continueStmt);
   *
   * // handle label continue //if ((labelContinueMap != null) && (labelContinueMap.containsKey(lastLabel))){ if (labelMap !=
   * null && labelMap.containsKey(doStmt)){ body.getUnits().add((soot.jimple.Stmt)labelMap.get(doStmt)); } /*if
   * ((labelContinueMap != null) && (labelStack != null) && (!labelStack.isEmpty()) &&
   * (labelContinueMap.containsKey(((LabelKey)labelStack.peek()).label()))){
   * body.getUnits().add((soot.jimple.Stmt)labelContinueMap.get(((LabelKey) labelStack.peek()).label())); }
   */

  /*
   * trueNoop.push(tNoop); falseNoop.push(fNoop);
   *
   * polyglot.ast.Expr condition = doStmt.cond(); soot.Value sootCond = base().createExpr(condition);
   *
   * trueNoop.pop();
   *
   * boolean needIf = needSootIf(sootCond); if (!(sootCond instanceof soot.jimple.ConditionExpr)) { sootCond =
   * soot.jimple.myJimple.newNeExpr(sootCond, soot.jimple.IntConstant.v(0)); } else { sootCond =
   * handleDFLCond((soot.jimple.ConditionExpr)sootCond); } if (needIf){ soot.jimple.IfStmt ifStmt =
   * soot.jimple.myJimple.newIfStmt(sootCond, noop1); body.getUnits().add(ifStmt); Util.addPosTag(ifStmt.getConditionBox(),
   * condition.position()); Util.addLnPosTags(ifStmt, condition.position()); } else { soot.jimple.GotoStmt gotoIf =
   * soot.jimple.myJimple.newGotoStmt(noop1); body.getUnits().add(gotoIf); }
   * body.getUnits().add((soot.jimple.Stmt)(endControlNoop.pop())); condControlNoop.pop();
   * body.getUnits().add(falseNoop.pop()); }
   */

  /**
   * DoWhile Stmts Creation
   */
  private void createDo2(polyglot.ast.Do doStmt) {

    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(noop1);

    // these are for break and continue
    endControlNoop.push(soot.jimple.myJimple.newNopStmt());
    condControlNoop.push(soot.jimple.myJimple.newNopStmt());

    // handle body
    createStmt(doStmt.body());

    // handle cond
    soot.jimple.Stmt continueStmt = condControlNoop.pop();
    body.getUnits().add(continueStmt);
    condControlNoop.push(continueStmt);

    if (labelMap != null && labelMap.containsKey(doStmt)) {
      body.getUnits().add(labelMap.get(doStmt));
    }

    polyglot.ast.Expr condition = doStmt.cond();

    createBranchingExpr(condition, noop1, true);

    body.getUnits().add((endControlNoop.pop()));
    condControlNoop.pop();
  }

  /**
   * For Loop Stmts Creation
   */
  /*
   * private void createForLoop(polyglot.ast.For forStmt){
   *
   * // create true/false noops to handle cond and/or soot.jimple.Stmt tNoop = soot.jimple.myJimple.newNopStmt();
   * soot.jimple.Stmt fNoop = soot.jimple.myJimple.newNopStmt();
   *
   * // these ()are for break and continue endControlNoop.push(soot.jimple.myJimple.newNopStmt());
   * condControlNoop.push(soot.jimple.myJimple.newNopStmt());
   *
   * // handle for inits Iterator initsIt = forStmt.inits().iterator(); while (initsIt.hasNext()){
   * createStmt((polyglot.ast.Stmt)initsIt.next()); } soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
   * soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();
   *
   * body.getUnits().add(noop2);
   *
   * // handle cond
   *
   * polyglot.ast.Expr condition = forStmt.cond(); if (condition != null) { trueNoop.push(tNoop); falseNoop.push(fNoop);
   * soot.Value sootCond = base().createExpr(condition); trueNoop.pop(); falseNoop.pop();
   *
   * boolean needIf = needSootIf(sootCond); if (!(sootCond instanceof soot.jimple.ConditionExpr)) { sootCond =
   * soot.jimple.myJimple.newEqExpr(sootCond, soot.jimple.IntConstant.v(0)); } else { sootCond =
   * reverseCondition((soot.jimple.ConditionExpr)sootCond); sootCond = handleDFLCond((soot.jimple.ConditionExpr)sootCond); }
   * if (needIf){ soot.jimple.IfStmt ifStmt = soot.jimple.myJimple.newIfStmt(sootCond, noop1);
   *
   * // add cond body.getUnits().add(ifStmt);
   *
   * // add line and pos tags Util.addLnPosTags(ifStmt.getConditionBox(), condition.position()); Util.addLnPosTags(ifStmt,
   * condition.position()); } //else { // soot.jimple.GotoStmt gotoIf = soot.jimple.myJimple.newGotoStmt(noop1); //
   * body.getUnits().add(gotoIf); //}
   *
   * } //else { // soot.jimple.Stmt goto2 = soot.jimple.myJimple.newGotoStmt(noop1); // body.getUnits().add(goto2);
   *
   * //}
   *
   *
   * // handle body //soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt(); //soot.jimple.Stmt goto1 =
   * soot.jimple.myJimple.newGotoStmt(noop2); //body.getUnits().add(goto1); //body.getUnits().add(noop1);
   * body.getUnits().add(tNoop); createStmt(forStmt.body());
   *
   * // handle continue body.getUnits().add((soot.jimple.Stmt)(condControlNoop.pop()));
   *
   * // handle label continue //if ((labelContinueMap != null) && (labelContinueMap.containsKey(lastLabel))){ if (labelMap !=
   * null && labelMap.containsKey(forStmt)){ body.getUnits().add((soot.jimple.Stmt)labelMap.get(forStmt)); }
   *
   * /*if ((labelContinueMap != null) && (labelStack != null) && (!labelStack.isEmpty()) &&
   * (labelContinueMap.containsKey(((LabelKey)labelStack.peek()).label()))){
   * body.getUnits().add((soot.jimple.Stmt)labelContinueMap.get(((LabelKey) labelStack.peek()).label()));
   * //System.out.println("lastLabel: "+lastLabel); //if (!body.getUnits().contains((soot.jimple.Stmt)labelContinueMap.get(
   * lastLabel))){ // body.getUnits().add((soot.jimple.Stmt)labelContinueMap.get(lastLabel)); //} }
   */

  // handle iters
  /*
   * Iterator itersIt = forStmt.iters().iterator(); //System.out.println("for iters: "+forStmt.iters()); while
   * (itersIt.hasNext()){ createStmt((polyglot.ast.Stmt)itersIt.next()); } soot.jimple.Stmt goto1 =
   * soot.jimple.myJimple.newGotoStmt(noop2); body.getUnits().add(goto1); //body.getUnits().add(noop2);
   *
   * // handle cond
   *
   * /*polyglot.ast.Expr condition = forStmt.cond(); if (condition != null) { soot.Value sootCond =
   * base().createExpr(condition); boolean needIf = needSootIf(sootCond); if (!(sootCond instanceof
   * soot.jimple.ConditionExpr)) { sootCond = soot.jimple.myJimple.newNeExpr(sootCond, soot.jimple.IntConstant.v(0)); }
   * else { sootCond = handleDFLCond((soot.jimple.ConditionExpr)sootCond); } if (needIf){ soot.jimple.IfStmt ifStmt =
   * soot.jimple.myJimple.newIfStmt(sootCond, noop1);
   *
   * // add cond body.getUnits().add(ifStmt);
   *
   * // add line and pos tags Util.addLnPosTags(ifStmt.getConditionBox(), condition.position()); Util.addLnPosTags(ifStmt,
   * condition.position()); } else { soot.jimple.GotoStmt gotoIf = soot.jimple.myJimple.newGotoStmt(noop1);
   * body.getUnits().add(gotoIf); }
   *
   * } else { soot.jimple.Stmt goto2 = soot.jimple.myJimple.newGotoStmt(noop1); body.getUnits().add(goto2);
   *
   * }
   */
  /*
   * body.getUnits().add(noop1); body.getUnits().add((soot.jimple.Stmt)(endControlNoop.pop())); body.getUnits().add(fNoop);
   *
   * }
   */

  /**
   * For Loop Stmts Creation
   */
  private void createForLoop2(polyglot.ast.For forStmt) {

    // these ()are for break and continue
    endControlNoop.push(soot.jimple.myJimple.newNopStmt());
    condControlNoop.push(soot.jimple.myJimple.newNopStmt());

    // handle for inits
    Iterator initsIt = forStmt.inits().iterator();
    while (initsIt.hasNext()) {
      createStmt((polyglot.ast.Stmt) initsIt.next());
    }
    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();

    body.getUnits().add(noop2);

    // handle cond

    polyglot.ast.Expr condition = forStmt.cond();
    if (condition != null) {
      createBranchingExpr(condition, noop1, false);
    }
    createStmt(forStmt.body());

    // handle continue
    body.getUnits().add((condControlNoop.pop()));

    if (labelMap != null && labelMap.containsKey(forStmt)) {
      body.getUnits().add(labelMap.get(forStmt));
    }

    // handle iters
    Iterator itersIt = forStmt.iters().iterator();
    while (itersIt.hasNext()) {
      createStmt((polyglot.ast.Stmt) itersIt.next());
    }
    soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(noop2);
    body.getUnits().add(goto1);
    body.getUnits().add(noop1);
    body.getUnits().add((endControlNoop.pop()));

  }

  /**
   * Local Decl Creation
   */
  private void createLocalDecl(polyglot.ast.LocalDecl localDecl) {

    // System.out.println("local decl: "+localDecl);
    String name = localDecl.name();
    polyglot.types.LocalInstance localInst = localDecl.localInstance();
    soot.Value lhs = createLocal(localInst);
    polyglot.ast.Expr expr = localDecl.init();
    if (expr != null) {
      // System.out.println("expr: "+expr+" get type: "+expr.getClass());
      soot.Value rhs;
      if (expr instanceof polyglot.ast.ArrayInit) {
        // System.out.println("creating array from localdecl:
        // "+localInst.type());
        rhs = getArrayInitLocal((polyglot.ast.ArrayInit) expr, localInst.type());
      } else {
        // System.out.println("create local decl: "+expr+" is a:
        // "+expr.getClass());
        rhs = base().createAggressiveExpr(expr, false, false);
        // System.out.println("rhs is: "+rhs+" is a: "+rhs.getClass());
      }
      if (rhs instanceof soot.jimple.ConditionExpr) {
        rhs = handleCondBinExpr((soot.jimple.ConditionExpr) rhs);
      }
      // System.out.println("rhs: "+rhs);
      soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(lhs, rhs);
      body.getUnits().add(stmt);
      // Util.addLineTag(stmt, localDecl);
      Util.addLnPosTags(stmt, localDecl.position());
      // this is a special case for position tags
      if (localDecl.position() != null) {
        Util.addLnPosTags(stmt.getLeftOpBox(), localDecl.position().line(), localDecl.position().endLine(),
            localDecl.position().endColumn() - name.length(), localDecl.position().endColumn());
        if (expr != null) {
          Util.addLnPosTags(stmt, localDecl.position().line(), expr.position().endLine(), localDecl.position().column(),
              expr.position().endColumn());
        } else {
          Util.addLnPosTags(stmt, localDecl.position().line(), localDecl.position().endLine(), localDecl.position().column(),
              localDecl.position().endColumn());
        }
      } else {
      }
      if (expr != null) {
        Util.addLnPosTags(stmt.getRightOpBox(), expr.position());
      }
    }
  }

  /**
   * Switch Stmts Creation
   */
  private void createSwitch(polyglot.ast.Switch switchStmt) {

    polyglot.ast.Expr value = switchStmt.expr();
    soot.Value sootValue = base().createAggressiveExpr(value, false, false);

    if (switchStmt.elements().size() == 0) {
      return;
    }

    soot.jimple.Stmt defaultTarget = null;

    polyglot.ast.Case[] caseArray = new polyglot.ast.Case[switchStmt.elements().size()];
    soot.jimple.Stmt[] targetsArray = new soot.jimple.Stmt[switchStmt.elements().size()];

    ArrayList<Stmt> targets = new ArrayList<Stmt>();
    HashMap<Object, Stmt> targetsMap = new HashMap<Object, Stmt>();
    int counter = 0;
    Iterator it = switchStmt.elements().iterator();
    while (it.hasNext()) {
      Object next = it.next();
      if (next instanceof polyglot.ast.Case) {
        soot.jimple.Stmt noop = soot.jimple.myJimple.newNopStmt();
        if (!((polyglot.ast.Case) next).isDefault()) {
          targets.add(noop);
          caseArray[counter] = (polyglot.ast.Case) next;
          targetsArray[counter] = noop;
          counter++;
          targetsMap.put(next, noop);
        } else {
          defaultTarget = noop;
        }
      }
    }

    // sort targets map
    int lowIndex = 0;
    int highIndex = 0;

    for (int i = 0; i < counter; i++) {
      for (int j = i + 1; j < counter; j++) {
        if (caseArray[j].value() < caseArray[i].value()) {
          polyglot.ast.Case tempCase = caseArray[i];
          soot.jimple.Stmt tempTarget = targetsArray[i];
          caseArray[i] = caseArray[j];
          targetsArray[i] = targetsArray[j];
          caseArray[j] = tempCase;
          targetsArray[j] = tempTarget;
        }
      }
    }

    ArrayList sortedTargets = new ArrayList();

    for (int i = 0; i < counter; i++) {
      sortedTargets.add(targetsArray[i]);
    }

    // deal with default
    boolean hasDefaultTarget = true;
    if (defaultTarget == null) {
      soot.jimple.Stmt noop = soot.jimple.myJimple.newNopStmt();
      defaultTarget = noop;
      hasDefaultTarget = false;

    }

    // lookup or tableswitch
    soot.jimple.Stmt sootSwitchStmt;
    if (isLookupSwitch(switchStmt)) {

      ArrayList values = new ArrayList();
      for (int i = 0; i < counter; i++) {
        if (!caseArray[i].isDefault()) {
          values.add(soot.jimple.IntConstant.v((int) caseArray[i].value()));
        }
      }

      soot.jimple.LookupSwitchStmt lookupStmt
          = soot.jimple.myJimple.newLookupSwitchStmt(sootValue, values, sortedTargets, defaultTarget);

      Util.addLnPosTags(lookupStmt.getKeyBox(), value.position());
      sootSwitchStmt = lookupStmt;

    } else {
      long lowVal = 0;
      long highVal = 0;
      boolean unknown = true;

      it = switchStmt.elements().iterator();
      while (it.hasNext()) {
        Object next = it.next();
        if (next instanceof polyglot.ast.Case) {
          if (!((polyglot.ast.Case) next).isDefault()) {
            long temp = ((polyglot.ast.Case) next).value();
            if (unknown) {
              highVal = temp;
              lowVal = temp;
              unknown = false;
            }
            if (temp > highVal) {
              highVal = temp;
            }
            if (temp < lowVal) {
              lowVal = temp;
            }
          }
        }

      }

      soot.jimple.TableSwitchStmt tableStmt
          = soot.jimple.myJimple.newTableSwitchStmt(sootValue, (int) lowVal, (int) highVal, sortedTargets, defaultTarget);

      Util.addLnPosTags(tableStmt.getKeyBox(), value.position());
      sootSwitchStmt = tableStmt;

    }

    body.getUnits().add(sootSwitchStmt);

    Util.addLnPosTags(sootSwitchStmt, switchStmt.position());
    endControlNoop.push(soot.jimple.myJimple.newNopStmt());

    it = switchStmt.elements().iterator();
    Iterator<Stmt> targetsIt = targets.iterator();

    while (it.hasNext()) {
      Object next = it.next();
      if (next instanceof polyglot.ast.Case) {
        if (!((polyglot.ast.Case) next).isDefault()) {
          body.getUnits().add(targetsMap.get(next));
        } else {
          body.getUnits().add(defaultTarget);
        }
      } else {
        polyglot.ast.SwitchBlock blockStmt = (polyglot.ast.SwitchBlock) next;
        createBlock(blockStmt);

      }
    }

    if (!hasDefaultTarget) {
      body.getUnits().add(defaultTarget);
    }
    body.getUnits().add((endControlNoop.pop()));
  }

  /**
   * Determine if switch should be lookup or table - this doesn't always get the same result as javac lookup: non-table
   * table: sequential (no gaps)
   */
  private boolean isLookupSwitch(polyglot.ast.Switch switchStmt) {

    int lowest = 0;
    int highest = 0;
    int counter = 0;
    Iterator it = switchStmt.elements().iterator();
    while (it.hasNext()) {
      Object next = it.next();
      if (next instanceof polyglot.ast.Case) {
        polyglot.ast.Case caseStmt = (polyglot.ast.Case) next;
        if (caseStmt.isDefault()) {
          continue;
        }
        int caseValue = (int) caseStmt.value();
        if (caseValue <= lowest || counter == 0) {
          lowest = caseValue;
        }
        if (caseValue >= highest || counter == 0) {
          highest = caseValue;
        }
        counter++;
      }
    }

    if ((counter - 1) == (highest - lowest)) {
      return false;
    }
    return true;
  }

  /**
   * Branch Stmts Creation
   */
  private void createBranch(polyglot.ast.Branch branchStmt) {

    // handle finally blocks before branch if inside try block
    if (tryStack != null && !tryStack.isEmpty()) {
      polyglot.ast.Try currentTry = tryStack.pop();
      if (currentTry.finallyBlock() != null) {
        createBlock(currentTry.finallyBlock());
        tryStack.push(currentTry);
      } else {
        tryStack.push(currentTry);
      }
    }

    // handle finally blocks before branch if inside catch block
    if (catchStack != null && !catchStack.isEmpty()) {
      polyglot.ast.Try currentTry = catchStack.pop();
      if (currentTry.finallyBlock() != null) {
        createBlock(currentTry.finallyBlock());
        catchStack.push(currentTry);
      } else {
        catchStack.push(currentTry);
      }
    }

    body.getUnits().add(soot.jimple.myJimple.newNopStmt());
    if (branchStmt.kind() == polyglot.ast.Branch.BREAK) {
      if (branchStmt.label() == null) {
        soot.jimple.Stmt gotoEndNoop = endControlNoop.pop();

        // handle monitor exits before break if necessary
        if (monitorStack != null) {
          Stack<Local> putBack = new Stack<Local>();
          while (!monitorStack.isEmpty()) {
            soot.Local exitVal = (soot.Local) monitorStack.pop();
            putBack.push(exitVal);
            soot.jimple.ExitMonitorStmt emStmt = soot.jimple.myJimple.newExitMonitorStmt(exitVal);
            body.getUnits().add(emStmt);
          }
          while (!putBack.isEmpty()) {
            monitorStack.push(putBack.pop());
          }
        }

        soot.jimple.Stmt gotoEnd = soot.jimple.myJimple.newGotoStmt(gotoEndNoop);
        endControlNoop.push(gotoEndNoop);
        body.getUnits().add(gotoEnd);
        Util.addLnPosTags(gotoEnd, branchStmt.position());
      } else {
        soot.jimple.Stmt gotoLabel = soot.jimple.myJimple.newGotoStmt(labelBreakMap.get(branchStmt.label()));
        body.getUnits().add(gotoLabel);
        Util.addLnPosTags(gotoLabel, branchStmt.position());
      }
    } else if (branchStmt.kind() == polyglot.ast.Branch.CONTINUE) {
      if (branchStmt.label() == null) {
        soot.jimple.Stmt gotoCondNoop = condControlNoop.pop();

        // handle monitor exits before continue if necessary
        if (monitorStack != null) {
          Stack<Local> putBack = new Stack<Local>();
          while (!monitorStack.isEmpty()) {
            soot.Local exitVal = (soot.Local) monitorStack.pop();
            putBack.push(exitVal);
            soot.jimple.ExitMonitorStmt emStmt = soot.jimple.myJimple.newExitMonitorStmt(exitVal);
            body.getUnits().add(emStmt);
          }
          while (!putBack.isEmpty()) {
            monitorStack.push(putBack.pop());
          }
        }

        soot.jimple.Stmt gotoCond = soot.jimple.myJimple.newGotoStmt(gotoCondNoop);
        condControlNoop.push(gotoCondNoop);
        body.getUnits().add(gotoCond);
        Util.addLnPosTags(gotoCond, branchStmt.position());
      } else {
        soot.jimple.Stmt gotoLabel = soot.jimple.myJimple.newGotoStmt(labelContinueMap.get(branchStmt.label()));
        body.getUnits().add(gotoLabel);
        Util.addLnPosTags(gotoLabel, branchStmt.position());
      }

    }

  }

  /**
   * Labeled Stmt Creation
   */
  private void createLabeled(polyglot.ast.Labeled labeledStmt) {
    String label = labeledStmt.label();
    // lastLabel = label;
    polyglot.ast.Stmt stmt = labeledStmt.statement();

    soot.jimple.Stmt noop = soot.jimple.myJimple.newNopStmt();
    // System.out.println("labeled stmt type: "+stmt.getClass());
    if (!(stmt instanceof polyglot.ast.For) && !(stmt instanceof polyglot.ast.Do)) {
      body.getUnits().add(noop);
    }
    /*
     * else { if (labelStack == null){ labelStack = new Stack(); } labelStack.push(new LabelKey(label, noop)); }
     */

    if (labelMap == null) {
      labelMap = new HashMap<polyglot.ast.Stmt, Stmt>();
    }

    labelMap.put(stmt, noop);

    if (labelBreakMap == null) {
      labelBreakMap = new HashMap<String, Stmt>();
    }

    if (labelContinueMap == null) {
      labelContinueMap = new HashMap<String, Stmt>();
    }

    labelContinueMap.put(label, noop);
    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();
    labelBreakMap.put(label, noop2);

    createStmt(stmt);

    /*
     * if (labelStack != null && !labelStack.isEmpty() && (stmt instanceof polyglot.ast.For || stmt instanceof
     * polyglot.ast.Do)){ labelStack.pop(); }
     */

    body.getUnits().add(noop2);

    // the idea here is to make a map of labels to the first
    // jimple stmt of the stmt (a noop) to be created - so
    // there is something to look up for breaks and continues
    // with labels
  }

  /*
   * class LabelKey{
   *
   * public LabelKey(String label, soot.jimple.Stmt noop){ this.label = label; this.noop = noop; } private String label;
   * public String label(){ return label; } private soot.jimple.Stmt noop; public soot.jimple.Stmt noop(){ return noop; } }
   */

  /**
   * Assert Stmt Creation
   */
  private void createAssert(polyglot.ast.Assert assertStmt) {

    // check if assertions are disabled
    soot.Local testLocal = lg.generateLocal(soot.BooleanType.v());
    soot.SootFieldRef assertField = soot.myScene.makeFieldRef(body.getMethod().getDeclaringClass(), "$assertionsDisabled",
        soot.BooleanType.v(), true);
    soot.jimple.FieldRef assertFieldRef = soot.jimple.myJimple.newStaticFieldRef(assertField);
    soot.jimple.AssignStmt fieldAssign = soot.jimple.myJimple.newAssignStmt(testLocal, assertFieldRef);
    body.getUnits().add(fieldAssign);

    soot.jimple.NopStmt nop1 = soot.jimple.myJimple.newNopStmt();
    soot.jimple.ConditionExpr cond1 = soot.jimple.myJimple.newNeExpr(testLocal, soot.jimple.IntConstant.v(0));
    soot.jimple.IfStmt testIf = soot.jimple.myJimple.newIfStmt(cond1, nop1);
    body.getUnits().add(testIf);

    // actual cond test
    if ((assertStmt.cond() instanceof polyglot.ast.BooleanLit) && (!((polyglot.ast.BooleanLit) assertStmt.cond()).value())) {
      // don't makeif
    } else {
      soot.Value sootCond = base().createAggressiveExpr(assertStmt.cond(), false, false);
      boolean needIf = needSootIf(sootCond);
      if (!(sootCond instanceof soot.jimple.ConditionExpr)) {
        sootCond = soot.jimple.myJimple.newEqExpr(sootCond, soot.jimple.IntConstant.v(1));
      } else {
        sootCond = handleDFLCond((soot.jimple.ConditionExpr) sootCond);
      }

      if (needIf) {
        // add if
        soot.jimple.IfStmt ifStmt = soot.jimple.myJimple.newIfStmt(sootCond, nop1);
        body.getUnits().add(ifStmt);

        Util.addLnPosTags(ifStmt.getConditionBox(), assertStmt.cond().position());
        Util.addLnPosTags(ifStmt, assertStmt.position());
      }
    }

    // assertion failure code
    soot.Local failureLocal = lg.generateLocal(soot.RefType.v("java.lang.AssertionError"));
    soot.jimple.NewExpr newExpr = soot.jimple.myJimple.newNewExpr(soot.RefType.v("java.lang.AssertionError"));
    soot.jimple.AssignStmt newAssign = soot.jimple.myJimple.newAssignStmt(failureLocal, newExpr);
    body.getUnits().add(newAssign);

    soot.SootMethodRef methToInvoke;
    ArrayList paramTypes = new ArrayList();
    ArrayList params = new ArrayList();
    if (assertStmt.errorMessage() != null) {
      soot.Value errorExpr = base().createAggressiveExpr(assertStmt.errorMessage(), false, false);
      if (errorExpr instanceof soot.jimple.ConditionExpr) {
        errorExpr = handleCondBinExpr((soot.jimple.ConditionExpr) errorExpr);
      }
      soot.Type errorType = errorExpr.getType();

      if (assertStmt.errorMessage().type().isChar()) {
        errorType = soot.CharType.v();
      }
      if (errorType instanceof soot.IntType) {
        paramTypes.add(soot.IntType.v());
      } else if (errorType instanceof soot.LongType) {
        paramTypes.add(soot.LongType.v());
      } else if (errorType instanceof soot.FloatType) {
        paramTypes.add(soot.FloatType.v());
      } else if (errorType instanceof soot.DoubleType) {
        paramTypes.add(soot.DoubleType.v());
      } else if (errorType instanceof soot.CharType) {
        paramTypes.add(soot.CharType.v());
      } else if (errorType instanceof soot.BooleanType) {
        paramTypes.add(soot.BooleanType.v());
      } else if (errorType instanceof soot.ShortType) {
        paramTypes.add(soot.IntType.v());
      } else if (errorType instanceof soot.ByteType) {
        paramTypes.add(soot.IntType.v());
      } else {
        paramTypes.add(soot.myScene.getSootClass("java.lang.Object").getType());
      }

      params.add(errorExpr);
    }
    methToInvoke = soot.myScene.makeMethodRef(soot.myScene.getSootClass("java.lang.AssertionError"), "<init>",
        paramTypes, soot.VoidType.v(), false);

    soot.jimple.SpecialInvokeExpr invokeExpr
        = soot.jimple.myJimple.newSpecialInvokeExpr(failureLocal, methToInvoke, params);
    soot.jimple.InvokeStmt invokeStmt = soot.jimple.myJimple.newInvokeStmt(invokeExpr);
    body.getUnits().add(invokeStmt);

    if (assertStmt.errorMessage() != null) {
      Util.addLnPosTags(invokeExpr.getArgBox(0), assertStmt.errorMessage().position());
    }

    soot.jimple.ThrowStmt throwStmt = soot.jimple.myJimple.newThrowStmt(failureLocal);
    body.getUnits().add(throwStmt);

    // end
    body.getUnits().add(nop1);

  }

  /**
   * Synchronized Stmt Creation
   */
  private void createSynchronized(polyglot.ast.Synchronized synchStmt) {
    soot.Value sootExpr = base().createAggressiveExpr(synchStmt.expr(), false, false);

    soot.jimple.EnterMonitorStmt enterMon = soot.jimple.myJimple.newEnterMonitorStmt(sootExpr);
    body.getUnits().add(enterMon);

    if (beforeReturn == null) {
      beforeReturn = new ArrayList<List<Stmt>>();
    }
    if (afterReturn == null) {
      afterReturn = new ArrayList<List<Stmt>>();
    }
    beforeReturn.add(new ArrayList<Stmt>());
    afterReturn.add(new ArrayList<Stmt>());

    if (monitorStack == null) {
      monitorStack = new Stack<Value>();
    }
    monitorStack.push(sootExpr);

    Util.addLnPosTags(enterMon.getOpBox(), synchStmt.expr().position());
    Util.addLnPosTags(enterMon, synchStmt.expr().position());

    soot.jimple.Stmt startNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(startNoop);

    createBlock(synchStmt.body());

    soot.jimple.ExitMonitorStmt exitMon = soot.jimple.myJimple.newExitMonitorStmt(sootExpr);
    body.getUnits().add(exitMon);

    monitorStack.pop();
    Util.addLnPosTags(exitMon.getOpBox(), synchStmt.expr().position());
    Util.addLnPosTags(exitMon, synchStmt.expr().position());

    soot.jimple.Stmt endSynchNoop = soot.jimple.myJimple.newNopStmt();
    soot.jimple.Stmt gotoEnd = soot.jimple.myJimple.newGotoStmt(endSynchNoop);

    soot.jimple.Stmt endNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(endNoop);

    body.getUnits().add(gotoEnd);

    soot.jimple.Stmt catchAllBeforeNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(catchAllBeforeNoop);

    // catch all
    soot.Local formalLocal = lg.generateLocal(soot.RefType.v("java.lang.Throwable"));

    soot.jimple.CaughtExceptionRef exceptRef = soot.jimple.myJimple.newCaughtExceptionRef();
    soot.jimple.Stmt stmt = soot.jimple.myJimple.newIdentityStmt(formalLocal, exceptRef);
    body.getUnits().add(stmt);

    // catch
    soot.jimple.Stmt catchBeforeNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(catchBeforeNoop);

    soot.Local local = lg.generateLocal(soot.RefType.v("java.lang.Throwable"));

    soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(local, formalLocal);

    body.getUnits().add(assign);
    soot.jimple.ExitMonitorStmt catchExitMon = soot.jimple.myJimple.newExitMonitorStmt(sootExpr);

    body.getUnits().add(catchExitMon);
    Util.addLnPosTags(catchExitMon.getOpBox(), synchStmt.expr().position());

    soot.jimple.Stmt catchAfterNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(catchAfterNoop);

    // throw
    soot.jimple.Stmt throwStmt = soot.jimple.myJimple.newThrowStmt(local);
    body.getUnits().add(throwStmt);

    body.getUnits().add(endSynchNoop);

    /*
     * add to the exceptionList all the ranges dictated by the returns found (the problem is that return statements are not
     * within the traps because just before the return all locks have already been released)
     */
    List<Stmt> before = beforeReturn.get(beforeReturn.size() - 1); // last
    // element
    List<Stmt> after = afterReturn.get(afterReturn.size() - 1); // last
    // element

    if (before.size() > 0) {
      addToExceptionList(startNoop, before.get(0), catchAllBeforeNoop, soot.myScene.getSootClass("java.lang.Throwable"));
      for (int i = 1; i < before.size(); i++) {
        addToExceptionList(after.get(i - 1), before.get(i), catchAllBeforeNoop,
            soot.myScene.getSootClass("java.lang.Throwable"));
      }
      addToExceptionList(after.get(after.size() - 1), endNoop, catchAllBeforeNoop,
          soot.myScene.getSootClass("java.lang.Throwable"));
    } else {
      addToExceptionList(startNoop, endNoop, catchAllBeforeNoop, soot.myScene.getSootClass("java.lang.Throwable"));
    }
    beforeReturn.remove(before);
    afterReturn.remove(after);

    addToExceptionList(catchBeforeNoop, catchAfterNoop, catchAllBeforeNoop,
        soot.myScene.getSootClass("java.lang.Throwable"));

  }

  /**
   * Return Stmts Creation
   */
  private void createReturn(polyglot.ast.Return retStmt) {
    polyglot.ast.Expr expr = retStmt.expr();
    soot.Value sootLocal = null;
    if (expr != null) {
      sootLocal = base().createAggressiveExpr(expr, false, false);
    }

    // handle monitor exits before return if necessary
    if (monitorStack != null) {
      Stack<Local> putBack = new Stack<Local>();
      while (!monitorStack.isEmpty()) {
        soot.Local exitVal = (soot.Local) monitorStack.pop();
        putBack.push(exitVal);
        soot.jimple.ExitMonitorStmt emStmt = soot.jimple.myJimple.newExitMonitorStmt(exitVal);
        body.getUnits().add(emStmt);
      }
      while (!putBack.isEmpty()) {
        monitorStack.push(putBack.pop());
      }

      // put label after exitmonitor(s) to mark where to stop the synch
      // try block
      soot.jimple.Stmt stopNoop = soot.jimple.myJimple.newNopStmt();
      body.getUnits().add(stopNoop);
      if (beforeReturn != null) // add to the list(s) of returns to be
      // handled in the createSynch method
      {
        for (List<Stmt> v : beforeReturn) {
          v.add(stopNoop);
        }
      }
    }

    // handle finally blocks before return if inside try block
    if (tryStack != null && !tryStack.isEmpty()) {
      polyglot.ast.Try currentTry = tryStack.pop();
      if (currentTry.finallyBlock() != null) {
        createBlock(currentTry.finallyBlock());
        tryStack.push(currentTry);
        // if return stmt contains a return don't create the other
        // return
        // ReturnStmtChecker rsc = new ReturnStmtChecker();
        // currentTry.finallyBlock().visit(rsc);
        // if (rsc.hasRet()){
        // return;
        // }
      } else {
        tryStack.push(currentTry);
      }
    }

    // handle finally blocks before return if inside catch block
    if (catchStack != null && !catchStack.isEmpty()) {
      polyglot.ast.Try currentTry = catchStack.pop();
      if (currentTry.finallyBlock() != null) {
        createBlock(currentTry.finallyBlock());
        catchStack.push(currentTry);
        // if return stmt contains a return don't create the other
        // return
        // extra return remove with some Soot phase
        // ReturnStmtChecker rsc = new ReturnStmtChecker();
        // currentTry.finallyBlock().visit(rsc);
        // if (rsc.hasRet()){
        // return;
        // }
      } else {
        catchStack.push(currentTry);
      }
    }

    // return
    if (expr == null) {
      soot.jimple.Stmt retStmtVoid = soot.jimple.myJimple.newReturnVoidStmt();
      body.getUnits().add(retStmtVoid);
      Util.addLnPosTags(retStmtVoid, retStmt.position());
    } else {
      // soot.Value sootLocal = createExpr(expr);
      if (sootLocal instanceof soot.jimple.ConditionExpr) {
        sootLocal = handleCondBinExpr((soot.jimple.ConditionExpr) sootLocal);
      }
      soot.jimple.ReturnStmt retStmtLocal = soot.jimple.myJimple.newReturnStmt(sootLocal);
      body.getUnits().add(retStmtLocal);
      Util.addLnPosTags(retStmtLocal.getOpBox(), expr.position());
      Util.addLnPosTags(retStmtLocal, retStmt.position());
    }

    // after the return is handled, put another label to show the new start
    // point of the synch try block
    soot.jimple.Stmt startNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(startNoop);
    if (afterReturn != null) // add to the list(s) of returns to be handled
    // in the createSynch method
    {
      for (List<Stmt> v : afterReturn) {
        v.add(startNoop);
      }
    }
  }

  /**
   * Throw Stmt Creation
   */
  private void createThrow(polyglot.ast.Throw throwStmt) {
    soot.Value toThrow = base().createAggressiveExpr(throwStmt.expr(), false, false);
    soot.jimple.ThrowStmt throwSt = soot.jimple.myJimple.newThrowStmt(toThrow);
    body.getUnits().add(throwSt);
    Util.addLnPosTags(throwSt, throwStmt.position());
    Util.addLnPosTags(throwSt.getOpBox(), throwStmt.expr().position());
  }

  /**
   * Try Stmt Creation
   */
  private void createTry(polyglot.ast.Try tryStmt) {

    polyglot.ast.Block finallyBlock = tryStmt.finallyBlock();

    if (finallyBlock == null) {
      createTryCatch(tryStmt);
    } else {
      createTryCatchFinally(tryStmt);
    }
  }

  /**
   * handles try/catch (try/catch/finally is separate for simplicity)
   */
  private void createTryCatch(polyglot.ast.Try tryStmt) {

    // try
    polyglot.ast.Block tryBlock = tryStmt.tryBlock();

    // this nop is for the fromStmt of try
    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(noop1);

    if (tryStack == null) {
      tryStack = new Stack<Try>();
    }
    tryStack.push(tryStmt);
    createBlock(tryBlock);
    tryStack.pop();

    // this nop is for the toStmt of try
    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(noop2);

    // create end nop for after entire try/catch
    soot.jimple.Stmt endNoop = soot.jimple.myJimple.newNopStmt();

    soot.jimple.Stmt tryEndGoto = soot.jimple.myJimple.newGotoStmt(endNoop);
    body.getUnits().add(tryEndGoto);

    Iterator it = tryStmt.catchBlocks().iterator();
    while (it.hasNext()) {

      soot.jimple.Stmt noop3 = soot.jimple.myJimple.newNopStmt();
      body.getUnits().add(noop3);

      // create catch stmts
      polyglot.ast.Catch catchBlock = (polyglot.ast.Catch) it.next();

      // create catch ref
      createCatchFormal(catchBlock.formal());

      if (catchStack == null) {
        catchStack = new Stack<Try>();
      }
      catchStack.push(tryStmt);
      createBlock(catchBlock.body());
      catchStack.pop();

      soot.jimple.Stmt catchEndGoto = soot.jimple.myJimple.newGotoStmt(endNoop);
      body.getUnits().add(catchEndGoto);

      soot.Type sootType = Util.getSootType(catchBlock.catchType());

      addToExceptionList(noop1, noop2, noop3, soot.myScene.getSootClass(sootType.toString()));

    }

    body.getUnits().add(endNoop);
  }

  /**
   * handles try/catch/finally (try/catch is separate for simplicity)
   */
  private void createTryCatchFinally(polyglot.ast.Try tryStmt) {

    HashMap<Stmt, Stmt> gotoMap = new HashMap<Stmt, Stmt>();

    // try
    polyglot.ast.Block tryBlock = tryStmt.tryBlock();

    // this nop is for the fromStmt of try
    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(noop1);

    if (tryStack == null) {
      tryStack = new Stack<Try>();
    }
    tryStack.push(tryStmt);
    createBlock(tryBlock);
    tryStack.pop();

    // this nop is for the toStmt of try
    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(noop2);

    // create end nop for after entire try/catch
    soot.jimple.Stmt endNoop = soot.jimple.myJimple.newNopStmt();

    // to finally
    soot.jimple.Stmt tryGotoFinallyNoop = soot.jimple.myJimple.newNopStmt();

    body.getUnits().add(tryGotoFinallyNoop);
    soot.jimple.Stmt tryFinallyNoop = soot.jimple.myJimple.newNopStmt();

    soot.jimple.Stmt tryGotoFinally = soot.jimple.myJimple.newGotoStmt(tryFinallyNoop);
    body.getUnits().add(tryGotoFinally);

    // goto end stmts
    soot.jimple.Stmt beforeEndGotoNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(beforeEndGotoNoop);
    soot.jimple.Stmt tryEndGoto = soot.jimple.myJimple.newGotoStmt(endNoop);
    body.getUnits().add(tryEndGoto);

    gotoMap.put(tryFinallyNoop, beforeEndGotoNoop);

    // catch section
    soot.jimple.Stmt catchAllBeforeNoop = soot.jimple.myJimple.newNopStmt();
    Iterator it = tryStmt.catchBlocks().iterator();
    while (it.hasNext()) {

      soot.jimple.Stmt noop3 = soot.jimple.myJimple.newNopStmt();
      body.getUnits().add(noop3);

      // create catch stmts
      polyglot.ast.Catch catchBlock = (polyglot.ast.Catch) it.next();

      // create catch ref
      soot.jimple.Stmt catchRefNoop = soot.jimple.myJimple.newNopStmt();
      body.getUnits().add(catchRefNoop);

      createCatchFormal(catchBlock.formal());

      soot.jimple.Stmt catchStmtsNoop = soot.jimple.myJimple.newNopStmt();
      body.getUnits().add(catchStmtsNoop);

      if (catchStack == null) {
        catchStack = new Stack<Try>();
      }
      catchStack.push(tryStmt);
      createBlock(catchBlock.body());
      catchStack.pop();

      // to finally
      soot.jimple.Stmt catchGotoFinallyNoop = soot.jimple.myJimple.newNopStmt();
      body.getUnits().add(catchGotoFinallyNoop);
      soot.jimple.Stmt catchFinallyNoop = soot.jimple.myJimple.newNopStmt();

      soot.jimple.Stmt catchGotoFinally = soot.jimple.myJimple.newGotoStmt(catchFinallyNoop);
      body.getUnits().add(catchGotoFinally);

      // goto end stmts
      soot.jimple.Stmt beforeCatchEndGotoNoop = soot.jimple.myJimple.newNopStmt();
      body.getUnits().add(beforeCatchEndGotoNoop);
      soot.jimple.Stmt catchEndGoto = soot.jimple.myJimple.newGotoStmt(endNoop);
      body.getUnits().add(catchEndGoto);

      gotoMap.put(catchFinallyNoop, beforeCatchEndGotoNoop);

      soot.Type sootType = Util.getSootType(catchBlock.catchType());

      addToExceptionList(noop1, noop2, noop3, soot.myScene.getSootClass(sootType.toString()));
      addToExceptionList(catchStmtsNoop, beforeCatchEndGotoNoop, catchAllBeforeNoop,
          soot.myScene.getSootClass("java.lang.Throwable"));
    }

    // catch all ref
    soot.Local formalLocal = lg.generateLocal(soot.RefType.v("java.lang.Throwable"));

    body.getUnits().add(catchAllBeforeNoop);
    soot.jimple.CaughtExceptionRef exceptRef = soot.jimple.myJimple.newCaughtExceptionRef();
    soot.jimple.Stmt stmt = soot.jimple.myJimple.newIdentityStmt(formalLocal, exceptRef);
    body.getUnits().add(stmt);

    // catch all assign
    soot.jimple.Stmt beforeCatchAllAssignNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(beforeCatchAllAssignNoop);
    soot.Local catchAllAssignLocal = lg.generateLocal(soot.RefType.v("java.lang.Throwable"));
    soot.jimple.Stmt catchAllAssign = soot.jimple.myJimple.newAssignStmt(catchAllAssignLocal, formalLocal);

    body.getUnits().add(catchAllAssign);

    // catch all finally
    soot.jimple.Stmt catchAllFinallyNoop = soot.jimple.myJimple.newNopStmt();
    soot.jimple.Stmt catchAllGotoFinally = soot.jimple.myJimple.newGotoStmt(catchAllFinallyNoop);
    body.getUnits().add(catchAllGotoFinally);

    // catch all throw
    soot.jimple.Stmt catchAllBeforeThrowNoop = soot.jimple.myJimple.newNopStmt();
    body.getUnits().add(catchAllBeforeThrowNoop);
    soot.jimple.Stmt throwStmt = soot.jimple.myJimple.newThrowStmt(catchAllAssignLocal);
    throwStmt.addTag(new soot.tagkit.ThrowCreatedByCompilerTag());
    body.getUnits().add(throwStmt);

    gotoMap.put(catchAllFinallyNoop, catchAllBeforeThrowNoop);

    // catch all goto end
    soot.jimple.Stmt catchAllGotoEnd = soot.jimple.myJimple.newGotoStmt(endNoop);
    body.getUnits().add(catchAllGotoEnd);

    addToExceptionList(beforeCatchAllAssignNoop, catchAllBeforeThrowNoop, catchAllBeforeNoop,
        soot.myScene.getSootClass("java.lang.Throwable"));

    // create finally's
    Iterator<Stmt> finallyIt = gotoMap.keySet().iterator();
    while (finallyIt.hasNext()) {

      soot.jimple.Stmt noopStmt = finallyIt.next();
      body.getUnits().add(noopStmt);

      createBlock(tryStmt.finallyBlock());
      soot.jimple.Stmt backToStmt = gotoMap.get(noopStmt);
      soot.jimple.Stmt backToGoto = soot.jimple.myJimple.newGotoStmt(backToStmt);
      body.getUnits().add(backToGoto);
    }
    body.getUnits().add(endNoop);

    addToExceptionList(noop1, beforeEndGotoNoop, catchAllBeforeNoop, soot.myScene.getSootClass("java.lang.Throwable"));
  }

  /**
   * add exceptions to a list that gets added at end of method
   */
  private void addToExceptionList(soot.jimple.Stmt from, soot.jimple.Stmt to, soot.jimple.Stmt with,
      soot.SootClass exceptionClass) {
    if (exceptionTable == null) {
      exceptionTable = new ArrayList<Trap>();
    }
    soot.Trap trap = soot.jimple.myJimple.newTrap(exceptionClass, from, to, with);
    exceptionTable.add(trap);
  }

  public soot.jimple.Constant createConstant(polyglot.ast.Expr expr) {
    Object constantVal = expr.constantValue();
    // System.out.println("expr: "+expr);

    return getConstant(constantVal, expr.type());
  }

  /**
   * Expression Creation
   */
  /*
   * protected soot.Value createExpr(polyglot.ast.Expr expr){
   * //System.out.println("create expr: "+expr+" type: "+expr.getClass()); // maybe right here check if expr has constant val
   * and return that // instead if (expr.isConstant() && expr.constantValue() != null && expr.type() != null && !(expr
   * instanceof polyglot.ast.Binary && expr.type().toString().equals("java.lang.String")) ){ return createConstant(expr); }
   * if (expr instanceof polyglot.ast.Assign) { return getAssignLocal((polyglot.ast.Assign)expr); } else if (expr instanceof
   * polyglot.ast.Lit) { return createLiteral((polyglot.ast.Lit)expr); } else if (expr instanceof polyglot.ast.Local) {
   * return getLocal((polyglot.ast.Local)expr); } else if (expr instanceof polyglot.ast.Binary) { return
   * getBinaryLocal((polyglot.ast.Binary)expr); } else if (expr instanceof polyglot.ast.Unary) { return
   * getUnaryLocal((polyglot.ast.Unary)expr); } else if (expr instanceof polyglot.ast.Cast) { return
   * getCastLocal((polyglot.ast.Cast)expr); } //else if (expr instanceof polyglot.ast.ArrayInit) { // array init are special
   * and get created elsewhere //} else if (expr instanceof polyglot.ast.ArrayAccess) { return
   * getArrayRefLocal((polyglot.ast.ArrayAccess)expr); } else if (expr instanceof polyglot.ast.NewArray) { return
   * getNewArrayLocal((polyglot.ast.NewArray)expr); } else if (expr instanceof polyglot.ast.Call) { return
   * getCallLocal((polyglot.ast.Call)expr); } else if (expr instanceof polyglot.ast.New) { return
   * getNewLocal((polyglot.ast.New)expr); } else if (expr instanceof polyglot.ast.Special) { return
   * getSpecialLocal((polyglot.ast.Special)expr); } else if (expr instanceof polyglot.ast.Instanceof) { return
   * getInstanceOfLocal((polyglot.ast.Instanceof)expr); } else if (expr instanceof polyglot.ast.Conditional) { return
   * getConditionalLocal((polyglot.ast.Conditional)expr); } else if (expr instanceof polyglot.ast.Field) { return
   * getFieldLocal((polyglot.ast.Field)expr); } else { throw new RuntimeException("Unhandled Expression: "+expr); }
   *
   * }
   */

  /**
   * Aggressive Expression Creation make reduceAggressively true to not reduce all the way to a local
   */
  @Override
  protected soot.Value createAggressiveExpr(polyglot.ast.Expr expr, boolean reduceAggressively, boolean reverseCondIfNec) {
    // System.out.println("create expr: "+expr+" type: "+expr.getClass());
    // maybe right here check if expr has constant val and return that
    // instead
    if (expr.isConstant() && expr.constantValue() != null && expr.type() != null
        && !(expr instanceof polyglot.ast.Binary && expr.type().toString().equals("java.lang.String"))) {
      return createConstant(expr);
    }
    if (expr instanceof polyglot.ast.Assign) {
      return getAssignLocal((polyglot.ast.Assign) expr);
    } else if (expr instanceof polyglot.ast.Lit) {
      return createLiteral((polyglot.ast.Lit) expr);
    } else if (expr instanceof polyglot.ast.Local) {
      return getLocal((polyglot.ast.Local) expr);
    } else if (expr instanceof polyglot.ast.Binary) {
      return getBinaryLocal2((polyglot.ast.Binary) expr, reduceAggressively);
    } else if (expr instanceof polyglot.ast.Unary) {
      return getUnaryLocal((polyglot.ast.Unary) expr);
    } else if (expr instanceof polyglot.ast.Cast) {
      return getCastLocal((polyglot.ast.Cast) expr);
    }
    // else if (expr instanceof polyglot.ast.ArrayInit) {
    // array init are special and get created elsewhere
    // }
    else if (expr instanceof polyglot.ast.ArrayAccess) {
      return getArrayRefLocal((polyglot.ast.ArrayAccess) expr);
    } else if (expr instanceof polyglot.ast.NewArray) {
      return getNewArrayLocal((polyglot.ast.NewArray) expr);
    } else if (expr instanceof polyglot.ast.Call) {
      return getCallLocal((polyglot.ast.Call) expr);
    } else if (expr instanceof polyglot.ast.New) {
      return getNewLocal((polyglot.ast.New) expr);
    } else if (expr instanceof polyglot.ast.Special) {
      return getSpecialLocal((polyglot.ast.Special) expr);
    } else if (expr instanceof polyglot.ast.Instanceof) {
      return getInstanceOfLocal((polyglot.ast.Instanceof) expr);
    } else if (expr instanceof polyglot.ast.Conditional) {
      return getConditionalLocal((polyglot.ast.Conditional) expr);
    } else if (expr instanceof polyglot.ast.Field) {
      return getFieldLocal((polyglot.ast.Field) expr);
    } else {
      throw new RuntimeException("Unhandled Expression: " + expr);
    }

  }

  @Override
  protected soot.Local handlePrivateFieldUnarySet(polyglot.ast.Unary unary) {
    polyglot.ast.Field fLeft = (polyglot.ast.Field) unary.expr();

    soot.Value base = base().getBaseLocal(fLeft.target());
    soot.Value fieldGetLocal = getPrivateAccessFieldLocal(fLeft, base);

    soot.Local tmp = generateLocal(fLeft.type());
    soot.jimple.AssignStmt stmt1 = soot.jimple.myJimple.newAssignStmt(tmp, fieldGetLocal);
    body.getUnits().add(stmt1);
    Util.addLnPosTags(stmt1, unary.position());

    soot.Value incVal = base().getConstant(Util.getSootType(fLeft.type()), 1);

    soot.jimple.BinopExpr binExpr;
    if (unary.operator() == polyglot.ast.Unary.PRE_INC || unary.operator() == polyglot.ast.Unary.POST_INC) {
      binExpr = soot.jimple.myJimple.newAddExpr(tmp, incVal);
    } else {
      binExpr = soot.jimple.myJimple.newSubExpr(tmp, incVal);
    }

    soot.Local tmp2 = generateLocal(fLeft.type());
    soot.jimple.AssignStmt assign = soot.jimple.myJimple.newAssignStmt(tmp2, binExpr);
    body.getUnits().add(assign);

    if (unary.operator() == polyglot.ast.Unary.PRE_INC || unary.operator() == polyglot.ast.Unary.PRE_DEC) {
      return base().handlePrivateFieldSet(fLeft, tmp2, base);
    } else {
      base().handlePrivateFieldSet(fLeft, tmp2, base);
      return tmp;
    }
  }

  @Override
  protected soot.Local handlePrivateFieldAssignSet(polyglot.ast.Assign assign) {
    polyglot.ast.Field fLeft = (polyglot.ast.Field) assign.left();
    // soot.Value right = createExpr(assign.right());

    // if assign is not = but +=, -=, *=, /=, >>=, >>>-, <<=, %=,
    // |= &= or ^= then compute it all into a local first
    // if (assign.operator() != polyglot.ast.Assign.ASSIGN){
    // in this cas can cast to local (never a string const here
    // as it has to be a lhs
    soot.Value right;
    soot.Value fieldBase = base().getBaseLocal(fLeft.target());
    if (assign.operator() == polyglot.ast.Assign.ASSIGN) {
      right = base().getSimpleAssignRightLocal(assign);
    } else if ((assign.operator() == polyglot.ast.Assign.ADD_ASSIGN)
        && assign.type().toString().equals("java.lang.String")) {
      right = getStringConcatAssignRightLocal(assign);
    } else {
      // here the lhs is a private field and needs to use get call
      soot.Local leftLocal = getPrivateAccessFieldLocal(fLeft, fieldBase);
      // soot.Local leftLocal = (soot.Local)base().createExpr(fLeft);
      right = base().getAssignRightLocal(assign, leftLocal);
    }

    return handlePrivateFieldSet(fLeft, right, fieldBase);
  }

  @Override
  protected soot.Local handlePrivateFieldSet(polyglot.ast.Expr expr, soot.Value right, soot.Value base) {
    // in normal j2j its always a field (and checked before call)
    // only has an expr for param for extensibility
    polyglot.ast.Field fLeft = (polyglot.ast.Field) expr;
    soot.SootClass containClass = ((soot.RefType) Util.getSootType(fLeft.target().type())).getSootClass();
    soot.SootMethod methToUse = addSetAccessMeth(containClass, fLeft, right);
    ArrayList params = new ArrayList();
    if (!fLeft.flags().isStatic()) {
      // this is the this ref if needed
      // params.add(getThis(Util.getSootType(fLeft.target().type())));
      params.add(base);
    }
    params.add(right);
    soot.jimple.InvokeExpr invoke = soot.jimple.myJimple.newStaticInvokeExpr(methToUse.makeRef(), params);
    soot.Local retLocal = lg.generateLocal(right.getType());
    soot.jimple.AssignStmt assignStmt = soot.jimple.myJimple.newAssignStmt(retLocal, invoke);
    body.getUnits().add(assignStmt);

    return retLocal;
  }

  private soot.SootMethod addSetAccessMeth(soot.SootClass conClass, polyglot.ast.Field field, soot.Value param) {
    if ((myInitialResolver.getPrivateFieldSetAccessMap() != null) && (myInitialResolver.getPrivateFieldSetAccessMap()
        .containsKey(new polyglot.util.IdentityKey(field.fieldInstance())))) {
      return myInitialResolver.getPrivateFieldSetAccessMap().get(new polyglot.util.IdentityKey(field.fieldInstance()));
    }
    String name = "access$" + soot.javaToJimple.myInitialResolver.getNextPrivateAccessCounter() + "00";
    ArrayList paramTypes = new ArrayList();
    if (!field.flags().isStatic()) {
      // add this param type
      paramTypes.add(conClass.getType());
      // paramTypes.add(Util.getSootType(field.target().type()));
    }
    soot.Type retType;
    paramTypes.add(Util.getSootType(field.type()));
    retType = Util.getSootType(field.type());
    /*
     * if (param.getType() instanceof soot.NullType){ paramTypes.add(soot.RefType.v("java.lang.Object")); retType =
     * soot.RefType.v("java.lang.Object"); } else { paramTypes.add(param.getType()); retType = param.getType(); }
     */
    soot.SootMethod meth = myScene.makeSootMethod(name, paramTypes, retType, soot.Modifier.STATIC);
    PrivateFieldSetMethodSource pfsms
        = new PrivateFieldSetMethodSource(Util.getSootType(field.type()), field.name(), field.flags().isStatic());

    conClass.addMethod(meth);
    meth.setActiveBody(pfsms.getBody(meth, null));

    myInitialResolver.addToPrivateFieldSetAccessMap(field, meth);
    meth.addTag(new soot.tagkit.SyntheticTag());
    return meth;
  }

  private soot.SootMethod addGetFieldAccessMeth(soot.SootClass conClass, polyglot.ast.Field field) {
    if ((myInitialResolver.getPrivateFieldGetAccessMap() != null) && (myInitialResolver.getPrivateFieldGetAccessMap()
        .containsKey(new polyglot.util.IdentityKey(field.fieldInstance())))) {
      return myInitialResolver.getPrivateFieldGetAccessMap().get(new polyglot.util.IdentityKey(field.fieldInstance()));
    }
    String name = "access$" + soot.javaToJimple.myInitialResolver.getNextPrivateAccessCounter() + "00";
    ArrayList paramTypes = new ArrayList();
    if (!field.flags().isStatic()) {
      // add this param type
      paramTypes.add(conClass.getType());// (soot.Local)getBaseLocal(field.target()));
      // paramTypes.add(Util.getSootType(field.target().type()));
    }
    soot.SootMethod meth = myScene.makeSootMethod(name, paramTypes, Util.getSootType(field.type()), soot.Modifier.STATIC);
    PrivateFieldAccMethodSource pfams
        = new PrivateFieldAccMethodSource(Util.getSootType(field.type()), field.name(), field.flags().isStatic(), conClass);

    conClass.addMethod(meth);
    meth.setActiveBody(pfams.getBody(meth, null));

    myInitialResolver.addToPrivateFieldGetAccessMap(field, meth);
    meth.addTag(new soot.tagkit.SyntheticTag());
    return meth;
  }

  private soot.SootMethod addGetMethodAccessMeth(soot.SootClass conClass, polyglot.ast.Call call) {
    if ((myInitialResolver.getPrivateMethodGetAccessMap() != null) && (myInitialResolver.getPrivateMethodGetAccessMap()
        .containsKey(new polyglot.util.IdentityKey(call.methodInstance())))) {
      return myInitialResolver.getPrivateMethodGetAccessMap().get(new polyglot.util.IdentityKey(call.methodInstance()));
    }
    String name = "access$" + soot.javaToJimple.myInitialResolver.getNextPrivateAccessCounter() + "00";
    ArrayList paramTypes = new ArrayList();
    if (!call.methodInstance().flags().isStatic()) {
      // add this param type
      // paramTypes.add(Util.getSootType(call.methodInstance().container()));
      paramTypes.add(conClass.getType());
    }
    ArrayList sootParamsTypes = getSootParamsTypes(call);
    paramTypes.addAll(sootParamsTypes);
    soot.SootMethod meth = myScene.makeSootMethod(name, paramTypes, Util.getSootType(call.methodInstance().returnType()),
        soot.Modifier.STATIC);
    PrivateMethodAccMethodSource pmams = new PrivateMethodAccMethodSource(call.methodInstance());

    conClass.addMethod(meth);
    meth.setActiveBody(pmams.getBody(meth, null));

    myInitialResolver.addToPrivateMethodGetAccessMap(call, meth);
    meth.addTag(new soot.tagkit.SyntheticTag());
    return meth;
  }

  @Override
  protected soot.Value getAssignRightLocal(polyglot.ast.Assign assign, soot.Local leftLocal) {

    if (assign.operator() == polyglot.ast.Assign.ASSIGN) {
      return base().getSimpleAssignRightLocal(assign);
    } else if (assign.operator() == polyglot.ast.Assign.ADD_ASSIGN && assign.type().toString().equals("java.lang.String")) {
      return getStringConcatAssignRightLocal(assign);
    } else {
      return getComplexAssignRightLocal(assign, leftLocal);
    }
  }

  @Override
  protected soot.Value getSimpleAssignRightLocal(polyglot.ast.Assign assign) {
    boolean repush = false;
    soot.jimple.Stmt tNoop = null;
    soot.jimple.Stmt fNoop = null;
    if (!trueNoop.empty() && !falseNoop.empty()) {
      tNoop = trueNoop.pop();
      fNoop = falseNoop.pop();
      repush = true;
    }

    soot.Value right = base().createAggressiveExpr(assign.right(), false, false);

    if (repush) {
      trueNoop.push(tNoop);
      falseNoop.push(fNoop);
    }

    if (right instanceof soot.jimple.ConditionExpr) {
      right = handleCondBinExpr((soot.jimple.ConditionExpr) right);
    }
    return right;
  }

  private soot.Local getStringConcatAssignRightLocal(polyglot.ast.Assign assign) {
    soot.Local sb = createStringBuffer(assign);
    sb = generateAppends(assign.left(), sb);
    sb = generateAppends(assign.right(), sb);
    soot.Local rLocal = createToString(sb, assign);
    return rLocal;
  }

  private soot.Local getComplexAssignRightLocal(polyglot.ast.Assign assign, soot.Local leftLocal) {
    soot.Value right = base().createAggressiveExpr(assign.right(), false, false);
    if (right instanceof soot.jimple.ConditionExpr) {
      right = handleCondBinExpr((soot.jimple.ConditionExpr) right);
    }

    soot.jimple.BinopExpr binop = null;
    if (assign.operator() == polyglot.ast.Assign.ADD_ASSIGN) {
      binop = soot.jimple.myJimple.newAddExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.SUB_ASSIGN) {
      binop = soot.jimple.myJimple.newSubExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.MUL_ASSIGN) {
      binop = soot.jimple.myJimple.newMulExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.DIV_ASSIGN) {
      binop = soot.jimple.myJimple.newDivExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.MOD_ASSIGN) {
      binop = soot.jimple.myJimple.newRemExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.SHL_ASSIGN) {
      binop = soot.jimple.myJimple.newShlExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.SHR_ASSIGN) {
      binop = soot.jimple.myJimple.newShrExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.USHR_ASSIGN) {
      binop = soot.jimple.myJimple.newUshrExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.BIT_AND_ASSIGN) {
      binop = soot.jimple.myJimple.newAndExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.BIT_OR_ASSIGN) {
      binop = soot.jimple.myJimple.newOrExpr(leftLocal, right);
    } else if (assign.operator() == polyglot.ast.Assign.BIT_XOR_ASSIGN) {
      binop = soot.jimple.myJimple.newXorExpr(leftLocal, right);
    }

    soot.Local retLocal = lg.generateLocal(leftLocal.getType());
    soot.jimple.AssignStmt assignStmt = soot.jimple.myJimple.newAssignStmt(retLocal, binop);
    body.getUnits().add(assignStmt);

    Util.addLnPosTags(binop.getOp1Box(), assign.left().position());
    Util.addLnPosTags(binop.getOp2Box(), assign.right().position());

    return retLocal;
  }

  private soot.Value getSimpleAssignLocal(polyglot.ast.Assign assign) {
    soot.jimple.AssignStmt stmt;
    soot.Value left = base().createLHS(assign.left());

    soot.Value right = base().getSimpleAssignRightLocal(assign);
    stmt = soot.jimple.myJimple.newAssignStmt(left, right);
    body.getUnits().add(stmt);
    Util.addLnPosTags(stmt, assign.position());
    Util.addLnPosTags(stmt.getRightOpBox(), assign.right().position());
    Util.addLnPosTags(stmt.getLeftOpBox(), assign.left().position());
    if (left instanceof soot.Local) {
      return left;
    } else {
      return right;
    }

  }

  private soot.Value getStrConAssignLocal(polyglot.ast.Assign assign) {
    soot.jimple.AssignStmt stmt;
    soot.Value left = base().createLHS(assign.left());

    soot.Value right = getStringConcatAssignRightLocal(assign);
    stmt = soot.jimple.myJimple.newAssignStmt(left, right);
    body.getUnits().add(stmt);
    Util.addLnPosTags(stmt, assign.position());
    Util.addLnPosTags(stmt.getRightOpBox(), assign.right().position());
    Util.addLnPosTags(stmt.getLeftOpBox(), assign.left().position());
    if (left instanceof soot.Local) {
      return left;
    } else {
      return right;
    }

  }

  /**
   * Assign Expression Creation
   */
  protected soot.Value getAssignLocal(polyglot.ast.Assign assign) {

    // handle private access field assigns
    // HashMap accessMap =
    // ((PolyglotMethodSource)body.getMethod().getSource()).getPrivateAccessMap();
    // if assigning to a field and the field is private and its not in
    // this class (then it had better be in some outer class and will
    // be handled as such)
    if (base().needsAccessor(assign.left())) {
      // if ((assign.left() instanceof polyglot.ast.Field) &&
      // (needsPrivateAccessor((polyglot.ast.Field)assign.left()) ||
      // needsProtectedAccessor((polyglot.ast.Field)assign.left()))){
      // ((polyglot.ast.Field)assign.left()).fieldInstance().flags().isPrivate()
      // &&
      // !Util.getSootType(((polyglot.ast.Field)assign.left()).fieldInstance()
      // .container()).equals(body.getMethod().getDeclaringClass().getType())){
      return base().handlePrivateFieldAssignSet(assign);
    }

    if (assign.operator() == polyglot.ast.Assign.ASSIGN) {
      return getSimpleAssignLocal(assign);
    }

    if ((assign.operator() == polyglot.ast.Assign.ADD_ASSIGN) && assign.type().toString().equals("java.lang.String")) {
      return getStrConAssignLocal(assign);
    }

    soot.jimple.AssignStmt stmt;
    soot.Value left = base().createLHS(assign.left());
    soot.Value left2 = (soot.Value) left.clone();

    soot.Local leftLocal;
    if (left instanceof soot.Local) {
      leftLocal = (soot.Local) left;

    } else {
      leftLocal = lg.generateLocal(left.getType());
      soot.jimple.AssignStmt stmt1 = soot.jimple.myJimple.newAssignStmt(leftLocal, left);
      body.getUnits().add(stmt1);
      Util.addLnPosTags(stmt1, assign.position());
    }

    soot.Value right = base().getAssignRightLocal(assign, leftLocal);
    soot.jimple.AssignStmt stmt2 = soot.jimple.myJimple.newAssignStmt(leftLocal, right);
    body.getUnits().add(stmt2);
    Util.addLnPosTags(stmt2, assign.position());
    Util.addLnPosTags(stmt2.getRightOpBox(), assign.right().position());
    Util.addLnPosTags(stmt2.getLeftOpBox(), assign.left().position());

    if (!(left instanceof soot.Local)) {
      soot.jimple.AssignStmt stmt3 = soot.jimple.myJimple.newAssignStmt(left2, leftLocal);
      body.getUnits().add(stmt3);
      Util.addLnPosTags(stmt3, assign.position());
      Util.addLnPosTags(stmt3.getRightOpBox(), assign.right().position());
      Util.addLnPosTags(stmt3.getLeftOpBox(), assign.left().position());
    }

    return leftLocal;

  }

  /**
   * Field Expression Creation - LHS
   */
  private soot.Value getFieldLocalLeft(polyglot.ast.Field field) {
    polyglot.ast.Receiver receiver = field.target();
    if ((field.name().equals("length")) && (receiver.type() instanceof polyglot.types.ArrayType)) {
      return getSpecialArrayLengthLocal(field);
    } else {
      return getFieldRef(field);
    }
  }

  /**
   * Field Expression Creation
   */
  private soot.Value getFieldLocal(polyglot.ast.Field field) {

    polyglot.ast.Receiver receiver = field.target();
    soot.javaToJimple.PolyglotMethodSource ms = (soot.javaToJimple.PolyglotMethodSource) body.getMethod().getSource();

    if ((field.name().equals("length")) && (receiver.type() instanceof polyglot.types.ArrayType)) {
      return getSpecialArrayLengthLocal(field);
    } else if (field.name().equals("class")) {
      throw new RuntimeException("Should go through ClassLit");
    } else if (base().needsAccessor(field)) {
      // else if (needsPrivateAccessor(field) ||
      // needsProtectedAccessor(field)){
      // ((field.fieldInstance().flags().isPrivate() &&
      // !Util.getSootType(field.fieldInstance().container()).equals(body.getMethod().getDeclaringClass().getType()))
      // ||()){

      soot.Value base = base().getBaseLocal(field.target());
      return getPrivateAccessFieldLocal(field, base);
    }
    if ((field.target() instanceof polyglot.ast.Special)
        && (((polyglot.ast.Special) field.target()).kind() == polyglot.ast.Special.SUPER)
        && (((polyglot.ast.Special) field.target()).qualifier() != null)) {
      return getSpecialSuperQualifierLocal(field);
    } else if (shouldReturnConstant(field)) {

      return getReturnConstant(field);
      // in this case don't return fieldRef but a string constant
    } else {

      soot.jimple.FieldRef fieldRef = getFieldRef(field);
      soot.Local baseLocal = generateLocal(field.type());
      soot.jimple.AssignStmt fieldAssignStmt = soot.jimple.myJimple.newAssignStmt(baseLocal, fieldRef);

      body.getUnits().add(fieldAssignStmt);
      Util.addLnPosTags(fieldAssignStmt, field.position());
      Util.addLnPosTags(fieldAssignStmt.getRightOpBox(), field.position());
      return baseLocal;
    }
  }

  @Override
  protected boolean needsAccessor(polyglot.ast.Expr expr) {
    if (!(expr instanceof polyglot.ast.Field) && !(expr instanceof polyglot.ast.Call)) {
      return false;
    } else {
      if (expr instanceof polyglot.ast.Field) {
        return needsAccessor(((polyglot.ast.Field) expr).fieldInstance());
      } else {
        return needsAccessor(((polyglot.ast.Call) expr).methodInstance());
      }
    }
  }

  /**
   * needs accessors: when field or meth is private and in some other class when field or meth is protected and in
   */
  protected boolean needsAccessor(polyglot.types.MemberInstance inst) {
    if (inst.flags().isPrivate()) {
      if (!Util.getSootType(inst.container()).equals(body.getMethod().getDeclaringClass().getType())) {
        return true;
      }
    } else if (inst.flags().isProtected()) {
      if (Util.getSootType(inst.container()).equals(body.getMethod().getDeclaringClass().getType())) {
        return false;
      }
      soot.SootClass currentClass = body.getMethod().getDeclaringClass();
      if (currentClass.getSuperclass().getType().equals(Util.getSootType(inst.container()))) {
        return false;
      }
      while (currentClass.hasOuterClass()) {
        currentClass = currentClass.getOuterClass();
        if (Util.getSootType(inst.container()).equals(currentClass.getType())) {
          return false;
        } else if (Util.getSootType(inst.container()).equals(currentClass.getSuperclass().getType())) {
          return true;
        }
      }
      return false;
    }

    return false;
  }

  /**
   * needs a private access method if field is private and in some other class
   */
  /*
   * protected boolean needsPrivateAccessor(polyglot.ast.Field field){ if (field.fieldInstance().flags().isPrivate()){ if
   * (!Util.getSootType(field.fieldInstance().container()).equals(body. getMethod().getDeclaringClass().getType())){ return
   * true; } } return false; }
   */

  /**
   * needs a protected access method if field is protected and in a super class of the outer class of the innerclass trying
   * to access the field (ie not in self or in outer of self)
   */
  /*
   * protected boolean needsProtectedAccessor(polyglot.ast.Field field){ //return false; if
   * (field.fieldInstance().flags().isProtected()){ if (Util.getSootType(field.fieldInstance().container()).equals(body.
   * getMethod().getDeclaringClass().getType())){ return false; } soot.SootClass currentClass =
   * body.getMethod().getDeclaringClass(); while (currentClass.hasOuterClass()){ currentClass = currentClass.getOuterClass();
   * if (Util.getSootType(field.fieldInstance().container()).equals(currentClass. getType())){ return false; } else if
   * (Util.getSootType(field.fieldInstance().container()).equals(currentClass. getSuperclass().getType())){ return true; } }
   * return false; } return false; /* if (field.fieldInstance().flags().isProtected()){ if
   * (!Util.getSootType(field.fieldInstance().container()).equals(body. getMethod().getDeclaringClass().getType())){
   * soot.SootClass checkClass = body.getMethod().getDeclaringClass(); while (checkClass.hasOuterClass()){ checkClass =
   * checkClass.getOuterClass(); if (Util.getSootType(field.fieldInstance().container()).equals(checkClass. getType())){
   * return false; }
   *
   * } return true; } } return false;
   */
  // }

  private soot.jimple.Constant getReturnConstant(polyglot.ast.Field field) {
    return getConstant(field.constantValue(), field.type());
  }

  private soot.jimple.Constant getConstant(Object constVal, polyglot.types.Type type) {
    // System.out.println("getConstant: "+constVal);
    if (constVal instanceof String) {
      return soot.jimple.StringConstant.v((String) constVal);
    } else if (constVal instanceof Boolean) {
      boolean val = ((Boolean) constVal).booleanValue();
      return soot.jimple.IntConstant.v(val ? 1 : 0);
    } else if (type.isChar()) {
      char val;

      if (constVal instanceof Integer) {
        val = (char) ((Integer) constVal).intValue();
      } else {
        val = ((Character) constVal).charValue();
      }
      // System.out.println("val: "+val);
      return soot.jimple.IntConstant.v(val);
    } else {
      Number num = (Number) constVal;
      // System.out.println("num: "+num);
      num = createConstantCast(type, num);
      // System.out.println("num: "+num);
      if (num instanceof Long) {
        // System.out.println(((Long)num).longValue());
        return soot.jimple.LongConstant.v(((Long) num).longValue());
      } else if (num instanceof Double) {
        return soot.jimple.DoubleConstant.v(((Double) num).doubleValue());
      } else if (num instanceof Float) {
        return soot.jimple.FloatConstant.v(((Float) num).floatValue());
      } else if (num instanceof Byte) {
        return soot.jimple.IntConstant.v(((Byte) num).byteValue());
      } else if (num instanceof Short) {
        return soot.jimple.IntConstant.v(((Short) num).shortValue());
      } else {
        return soot.jimple.IntConstant.v(((Integer) num).intValue());
      }
    }
  }

  private Number createConstantCast(polyglot.types.Type fieldType, Number constant) {
    if (constant instanceof Integer) {
      if (fieldType.isDouble()) {
        return new Double(((Integer) constant).intValue());
      } else if (fieldType.isFloat()) {
        return new Float(((Integer) constant).intValue());
      } else if (fieldType.isLong()) {
        return new Long(((Integer) constant).intValue());
      }
    }
    return constant;
  }

  private boolean shouldReturnConstant(polyglot.ast.Field field) {
    if (field.isConstant() && field.constantValue() != null) {
      return true;
    }
    return false;
  }

  /**
   * creates a field ref
   */
  @Override
  protected soot.jimple.FieldRef getFieldRef(polyglot.ast.Field field) {

    soot.SootClass receiverClass = ((soot.RefType) Util.getSootType(field.target().type())).getSootClass();
    soot.SootFieldRef receiverField
        = soot.myScene.makeFieldRef(receiverClass, field.name(), Util.getSootType(field.type()), field.flags().isStatic());

    soot.jimple.FieldRef fieldRef;
    if (field.fieldInstance().flags().isStatic()) {
      fieldRef = soot.jimple.myJimple.newStaticFieldRef(receiverField);
    } else {
      soot.Local base;
      base = (soot.Local) base().getBaseLocal(field.target());
      fieldRef = soot.jimple.myJimple.newInstanceFieldRef(base, receiverField);
    }

    if (field.target() instanceof polyglot.ast.Local && fieldRef instanceof soot.jimple.InstanceFieldRef) {
      Util.addLnPosTags(((soot.jimple.InstanceFieldRef) fieldRef).getBaseBox(), field.target().position());
    }
    return fieldRef;
  }

  /**
   * For Inner Classes - to access private fields of their outer class
   */
  private soot.Local getPrivateAccessFieldLocal(polyglot.ast.Field field, soot.Value base) {

    // need to add access method
    // if private add to the containing class
    // but if its protected then add to outer class - not containing
    // class because in this case the containing class is the super class

    soot.SootMethod toInvoke;
    soot.SootClass invokeClass;
    if (field.fieldInstance().flags().isPrivate()) {
      toInvoke = addGetFieldAccessMeth(((soot.RefType) Util.getSootType(field.fieldInstance().container())).getSootClass(),
          field);
      invokeClass = ((soot.RefType) Util.getSootType(field.fieldInstance().container())).getSootClass();
    } else {
      if (myInitialResolver.hierarchy() == null) {
        myInitialResolver.hierarchy(new soot.FastHierarchy(myScene));
      }
      soot.SootClass containingClass = ((soot.RefType) Util.getSootType(field.fieldInstance().container())).getSootClass();
      soot.SootClass addToClass;
      if (body.getMethod().getDeclaringClass().hasOuterClass()) {
        addToClass = body.getMethod().getDeclaringClass().getOuterClass();

        while (!myInitialResolver.hierarchy().canStoreType(containingClass.getType(), addToClass.getType())) {
          if (addToClass.hasOuterClass()) {
            addToClass = addToClass.getOuterClass();
          } else {
            break;
          }
        }
      } else {
        addToClass = containingClass;
      }
      invokeClass = addToClass;
      toInvoke = addGetFieldAccessMeth(addToClass, field);
    }

    ArrayList params = new ArrayList();
    if (!field.fieldInstance().flags().isStatic()) {
      params.add(base);
      /*
       * if (field.target() instanceof polyglot.ast.Expr){ params.add((soot.Local)base().getBaseLocal(field.target())); }
       * else if (body.getMethod().getDeclaringClass().declaresFieldByName( "this$0")){
       * params.add(getThis(invokeClass.getType())); } else { soot.Local local =
       * (soot.Local)base().getBaseLocal(field.target()); params.add(local); }
       */

      // (soot.Local)getBaseLocal(field.target()));
      /*
       * if (Util.getSootType(field.target().type()).equals(invokeClass. getType())){
       */
      // params.add(getThis(invokeClass.getType()));//(soot.Local)getBaseLocal(field.target()));
      // }
      /* else { */

      // soot.Local local = (soot.Local)getBaseLocal(field.target());

      // params.add(getThis(invokeClass.getType()));//(soot.Local)getBaseLocal(field.target()));
      // soot.Local local = (soot.Local)getBaseLocal(field.target());
      // params.add(local);
      // }
    }

    return Util.getPrivateAccessFieldInvoke(toInvoke.makeRef(), params, body, lg);
  }

  /**
   * To get the local for the special .class literal
   */
  private soot.Local getSpecialClassLitLocal(polyglot.ast.ClassLit lit) {

    if (lit.typeNode().type().isPrimitive()) {
      polyglot.types.PrimitiveType primType = (polyglot.types.PrimitiveType) lit.typeNode().type();
      soot.Local retLocal = lg.generateLocal(soot.RefType.v("java.lang.Class"));
      soot.SootFieldRef primField = null;
      if (primType.isBoolean()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Boolean"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isByte()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Byte"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isChar()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Character"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isDouble()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Double"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isFloat()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Float"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isInt()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Integer"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isLong()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Long"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isShort()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Short"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      } else if (primType.isVoid()) {
        primField = soot.myScene.makeFieldRef(soot.myScene.getSootClass("java.lang.Void"), "TYPE",
            soot.RefType.v("java.lang.Class"), true);
      }
      soot.jimple.StaticFieldRef fieldRef = soot.jimple.myJimple.newStaticFieldRef(primField);
      soot.jimple.AssignStmt assignStmt = soot.jimple.myJimple.newAssignStmt(retLocal, fieldRef);
      body.getUnits().add(assignStmt);
      return retLocal;
    } else {
      // this class
      soot.SootClass thisClass = body.getMethod().getDeclaringClass();
      String fieldName = Util.getFieldNameForClassLit(lit.typeNode().type());
      soot.Type fieldType = soot.RefType.v("java.lang.Class");
      soot.Local fieldLocal = lg.generateLocal(soot.RefType.v("java.lang.Class"));
      soot.SootFieldRef sootField = null;
      if (thisClass.isInterface()) {
        HashMap<SootClass, SootClass> specialAnonMap = myInitialResolver.specialAnonMap();
        if ((specialAnonMap != null) && (specialAnonMap.containsKey(thisClass))) {
          soot.SootClass specialClass = specialAnonMap.get(thisClass);
          sootField = soot.myScene.makeFieldRef(specialClass, fieldName, fieldType, true);
        } else {
          throw new RuntimeException(
              "Class is interface so it must have an anon class to handle class lits but its anon class cannot be found.");
        }
      } else {
        sootField = soot.myScene.makeFieldRef(thisClass, fieldName, fieldType, true);
      }
      soot.jimple.StaticFieldRef fieldRef = soot.jimple.myJimple.newStaticFieldRef(sootField);
      soot.jimple.Stmt fieldAssign = soot.jimple.myJimple.newAssignStmt(fieldLocal, fieldRef);
      body.getUnits().add(fieldAssign);

      soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
      soot.jimple.Expr neExpr = soot.jimple.myJimple.newNeExpr(fieldLocal, soot.jimple.myNullConstant);
      soot.jimple.Stmt ifStmt = soot.jimple.myJimple.newIfStmt(neExpr, noop1);
      body.getUnits().add(ifStmt);

      ArrayList paramTypes = new ArrayList();
      paramTypes.add(soot.RefType.v("java.lang.String"));
      soot.SootMethodRef invokeMeth = null;
      if (thisClass.isInterface()) {
        HashMap<SootClass, SootClass> specialAnonMap = myInitialResolver.specialAnonMap();
        if ((specialAnonMap != null) && (specialAnonMap.containsKey(thisClass))) {
          soot.SootClass specialClass = specialAnonMap.get(thisClass);
          invokeMeth
              = soot.myScene.makeMethodRef(specialClass, "class$", paramTypes, soot.RefType.v("java.lang.Class"), true);
        } else {
          throw new RuntimeException(
              "Class is interface so it must have an anon class to handle class lits but its anon class cannot be found.");
        }
      } else {
        invokeMeth = soot.myScene.makeMethodRef(thisClass, "class$", paramTypes, soot.RefType.v("java.lang.Class"), true);
      }
      ArrayList params = new ArrayList();
      params.add(soot.jimple.StringConstant.v(Util.getParamNameForClassLit(lit.typeNode().type())));
      soot.jimple.Expr classInvoke = soot.jimple.myJimple.newStaticInvokeExpr(invokeMeth, params);
      soot.Local methLocal = lg.generateLocal(soot.RefType.v("java.lang.Class"));
      soot.jimple.Stmt invokeAssign = soot.jimple.myJimple.newAssignStmt(methLocal, classInvoke);
      body.getUnits().add(invokeAssign);

      soot.jimple.Stmt assignField = soot.jimple.myJimple.newAssignStmt(fieldRef, methLocal);
      body.getUnits().add(assignField);

      soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();
      soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(noop2);
      body.getUnits().add(goto1);

      body.getUnits().add(noop1);
      fieldAssign = soot.jimple.myJimple.newAssignStmt(methLocal, fieldRef);
      body.getUnits().add(fieldAssign);
      body.getUnits().add(noop2);

      return methLocal;
    }
  }

  /**
   * Array Length local for example a.length w/o brackets gets length of array
   */
  private soot.Local getSpecialArrayLengthLocal(polyglot.ast.Field field) {

    soot.Local localField;
    polyglot.ast.Receiver receiver = field.target();
    if (receiver instanceof polyglot.ast.Local) {
      localField = getLocal((polyglot.ast.Local) receiver);
    } else if (receiver instanceof polyglot.ast.Expr) {
      localField = (soot.Local) base().createAggressiveExpr((polyglot.ast.Expr) receiver, false, false);
    } else {
      localField = generateLocal(receiver.type());
    }
    soot.jimple.LengthExpr lengthExpr = soot.jimple.myJimple.newLengthExpr(localField);
    soot.Local retLocal = lg.generateLocal(soot.IntType.v());
    soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(retLocal, lengthExpr);
    body.getUnits().add(assign);
    Util.addLnPosTags(assign, field.position());
    Util.addLnPosTags(lengthExpr.getOpBox(), field.target().position());
    return retLocal;
  }

  /**
   * Binary Expression Creation
   */
  private soot.Value getBinaryLocal2(polyglot.ast.Binary binary, boolean reduceAggressively) {
    // System.out.println("binary: "+binary+" class: "+binary.getClass());

    soot.Value rhs;

    if (binary.operator() == polyglot.ast.Binary.COND_AND) {
      return createCondAnd(binary);
    }
    if (binary.operator() == polyglot.ast.Binary.COND_OR) {
      return createCondOr(binary);
    }

    if (binary.type().toString().equals("java.lang.String")) {
      // System.out.println("binary: "+binary);
      if (areAllStringLits(binary)) {
        String result = createStringConstant(binary);
        // System.out.println("created string constant: "+result);
        return soot.jimple.StringConstant.v(result);
      } else {
        soot.Local sb = createStringBuffer(binary);
        sb = generateAppends(binary.left(), sb);
        sb = generateAppends(binary.right(), sb);
        return createToString(sb, binary);
      }
    }

    // System.out.println("bin exp left: "+binary.left());
    // System.out.println("bin exp right: "+binary.right());
    soot.Value lVal = base().createAggressiveExpr(binary.left(), true, false);
    soot.Value rVal = base().createAggressiveExpr(binary.right(), true, false);

    if (isComparisonBinary(binary.operator())) {
      // System.out.println("bin exp: "+binary);
      rhs = getBinaryComparisonExpr(lVal, rVal, binary.operator());
    } else {
      rhs = getBinaryExpr(lVal, rVal, binary.operator());
    }

    if (rhs instanceof soot.jimple.BinopExpr) {
      Util.addLnPosTags(((soot.jimple.BinopExpr) rhs).getOp1Box(), binary.left().position());
      Util.addLnPosTags(((soot.jimple.BinopExpr) rhs).getOp2Box(), binary.right().position());
    }

    if (rhs instanceof soot.jimple.ConditionExpr && !reduceAggressively) {
      return rhs;
    } else if (rhs instanceof soot.jimple.ConditionExpr) {
      rhs = handleCondBinExpr((soot.jimple.ConditionExpr) rhs, true);
    }

    soot.Local lhs = generateLocal(binary.type());

    soot.jimple.AssignStmt assignStmt = soot.jimple.myJimple.newAssignStmt(lhs, rhs);
    body.getUnits().add(assignStmt);
    // System.out.println("binary pos: "+binary.position());

    Util.addLnPosTags(assignStmt.getRightOpBox(), binary.position());
    Util.addLnPosTags(assignStmt, binary.position());
    return lhs;
  }

  private boolean areAllStringLits(polyglot.ast.Node node) {

    // System.out.println("node in is string lit: "+node+" kind:
    // "+node.getClass());
    if (node instanceof polyglot.ast.StringLit) {
      return true;
    } else if (node instanceof polyglot.ast.Field) {
      if (shouldReturnConstant((polyglot.ast.Field) node)) {
        return true;
      } else {
        return false;
      }
    } else if (node instanceof polyglot.ast.Binary) {
      if (areAllStringLitsBinary((polyglot.ast.Binary) node)) {
        return true;
      }
      return false;
    } else if (node instanceof polyglot.ast.Unary) {
      polyglot.ast.Unary unary = (polyglot.ast.Unary) node;
      if (unary.isConstant()) {
        return true;
      }
      return false;
    } else if (node instanceof polyglot.ast.Cast) {
      polyglot.ast.Cast cast = (polyglot.ast.Cast) node;
      if (cast.isConstant()) {
        return true;
      }
      return false;
    } else if (node instanceof polyglot.ast.Lit) {
      polyglot.ast.Lit lit = (polyglot.ast.Lit) node;
      // System.out.println("lit: "+lit+" is constant:
      // "+(lit.isConstant()?true:false));
      if (lit.isConstant()) {
        return true;
      }
      return false;
    }
    return false;
  }

  private boolean areAllStringLitsBinary(polyglot.ast.Binary binary) {
    if (areAllStringLits(binary.left()) && areAllStringLits(binary.right())) {
      return true;
    } else {
      return false;
    }
  }

  private String createStringConstant(polyglot.ast.Node node) {
    // System.out.println("creatinf string constant:
    // "+createConstant((polyglot.ast.Expr)node));
    String s = null;
    if (node instanceof polyglot.ast.StringLit) {
      s = ((polyglot.ast.StringLit) node).value();
    } else if (node instanceof polyglot.ast.Cast) {
      polyglot.ast.Cast cast = (polyglot.ast.Cast) node;
      if (cast.type().isChar()) {
        s = "" + ((Character) cast.constantValue()).charValue();
      } else {
        s = "" + cast.constantValue();
      }
    } else if (node instanceof polyglot.ast.Unary) {
      polyglot.ast.Unary unary = (polyglot.ast.Unary) node;
      s = "" + unary.constantValue();
    } else if (node instanceof polyglot.ast.CharLit) {
      s = "" + ((polyglot.ast.CharLit) node).value();
    } else if (node instanceof polyglot.ast.BooleanLit) {
      s = "" + ((polyglot.ast.BooleanLit) node).value();
    } else if (node instanceof polyglot.ast.IntLit) {
      s = "" + ((polyglot.ast.IntLit) node).value();
    } else if (node instanceof polyglot.ast.FloatLit) {
      s = "" + ((polyglot.ast.FloatLit) node).value();
    } else if (node instanceof polyglot.ast.NullLit) {
      s = "null";
    } else if (node instanceof polyglot.ast.Field) {
      polyglot.ast.Field field = (polyglot.ast.Field) node;
      if (field.fieldInstance().constantValue() instanceof String) {
        s = (String) field.constantValue();
      } else if (field.fieldInstance().constantValue() instanceof Boolean) {
        boolean val = ((Boolean) field.constantValue()).booleanValue();
        int temp = val ? 1 : 0;
        s = "" + temp;
      } else if (field.type().isChar()) {

        char val = (char) ((Integer) field.constantValue()).intValue();
        s = "" + val;
      } else {
        Number num = (Number) field.fieldInstance().constantValue();
        num = createConstantCast(field.type(), num);
        if (num instanceof Long) {
          s = "" + ((Long) num).longValue();
        } else if (num instanceof Double) {
          s = "" + ((Double) num).doubleValue();
        } else if (num instanceof Float) {
          s = "" + ((Float) num).floatValue();
        } else if (num instanceof Byte) {
          s = "" + ((Byte) num).byteValue();
        } else if (num instanceof Short) {
          s = "" + ((Short) num).shortValue();
        } else {
          s = "" + ((Integer) num).intValue();
        }
      }

    } else if (node instanceof polyglot.ast.Binary) {
      s = createStringConstantBinary((polyglot.ast.Binary) node);
    } else {
      throw new RuntimeException("No other string constant folding done");
    }
    return s;
  }

  private String createStringConstantBinary(polyglot.ast.Binary binary) {
    // System.out.println("create string binary: type"+binary.type());
    String s = null;
    if (Util.getSootType(binary.type()).toString().equals("java.lang.String")) {
      // here if type is a string return string constant
      s = createStringConstant(binary.left()) + createStringConstant(binary.right());
    } else {
      // else eval and return string of the eval result
      s = binary.constantValue().toString();
    }
    return s;

  }

  private boolean isComparisonBinary(polyglot.ast.Binary.Operator op) {
    if ((op == polyglot.ast.Binary.EQ) || (op == polyglot.ast.Binary.NE) || (op == polyglot.ast.Binary.GE)
        || (op == polyglot.ast.Binary.GT) || (op == polyglot.ast.Binary.LE) || (op == polyglot.ast.Binary.LT)) {

      return true;
    } else {
      return false;
    }

  }

  /**
   * Creates a binary expression that is not a comparison
   */
  private soot.Value getBinaryExpr(soot.Value lVal, soot.Value rVal, polyglot.ast.Binary.Operator operator) {

    soot.Value rValue = null;

    if (lVal instanceof soot.jimple.ConditionExpr) {
      lVal = handleCondBinExpr((soot.jimple.ConditionExpr) lVal);
    }
    if (rVal instanceof soot.jimple.ConditionExpr) {
      rVal = handleCondBinExpr((soot.jimple.ConditionExpr) rVal);
    }
    if (operator == polyglot.ast.Binary.ADD) {

      rValue = soot.jimple.myJimple.newAddExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.SUB) {
      rValue = soot.jimple.myJimple.newSubExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.MUL) {
      rValue = soot.jimple.myJimple.newMulExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.DIV) {
      rValue = soot.jimple.myJimple.newDivExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.SHR) {
      if (rVal.getType().equals(soot.LongType.v())) {
        soot.Local intVal = lg.generateLocal(soot.IntType.v());
        soot.jimple.CastExpr castExpr = soot.jimple.myJimple.newCastExpr(rVal, soot.IntType.v());
        soot.jimple.AssignStmt assignStmt = soot.jimple.myJimple.newAssignStmt(intVal, castExpr);
        body.getUnits().add(assignStmt);
        rValue = soot.jimple.myJimple.newShrExpr(lVal, intVal);
      } else {
        rValue = soot.jimple.myJimple.newShrExpr(lVal, rVal);
      }
    } else if (operator == polyglot.ast.Binary.USHR) {
      if (rVal.getType().equals(soot.LongType.v())) {
        soot.Local intVal = lg.generateLocal(soot.IntType.v());
        soot.jimple.CastExpr castExpr = soot.jimple.myJimple.newCastExpr(rVal, soot.IntType.v());
        soot.jimple.AssignStmt assignStmt = soot.jimple.myJimple.newAssignStmt(intVal, castExpr);
        body.getUnits().add(assignStmt);
        rValue = soot.jimple.myJimple.newUshrExpr(lVal, intVal);
      } else {
        rValue = soot.jimple.myJimple.newUshrExpr(lVal, rVal);
      }
    } else if (operator == polyglot.ast.Binary.SHL) {
      if (rVal.getType().equals(soot.LongType.v())) {
        soot.Local intVal = lg.generateLocal(soot.IntType.v());
        soot.jimple.CastExpr castExpr = soot.jimple.myJimple.newCastExpr(rVal, soot.IntType.v());
        soot.jimple.AssignStmt assignStmt = soot.jimple.myJimple.newAssignStmt(intVal, castExpr);
        body.getUnits().add(assignStmt);
        rValue = soot.jimple.myJimple.newShlExpr(lVal, intVal);
      } else {
        rValue = soot.jimple.myJimple.newShlExpr(lVal, rVal);
      }
    } else if (operator == polyglot.ast.Binary.BIT_AND) {
      rValue = soot.jimple.myJimple.newAndExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.BIT_OR) {
      rValue = soot.jimple.myJimple.newOrExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.BIT_XOR) {
      rValue = soot.jimple.myJimple.newXorExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.MOD) {
      rValue = soot.jimple.myJimple.newRemExpr(lVal, rVal);
    } else {
      throw new RuntimeException("Binary not yet handled!");
    }

    return rValue;
  }

  /**
   * Creates a binary expr that is a comparison
   */
  private soot.Value getBinaryComparisonExpr(soot.Value lVal, soot.Value rVal, polyglot.ast.Binary.Operator operator) {

    soot.Value rValue;

    if (operator == polyglot.ast.Binary.EQ) {
      // System.out.println("processing:
      // "+body.getMethod().getDeclaringClass());
      // System.out.println("lval: "+lVal+" rval: "+rVal);
      rValue = soot.jimple.myJimple.newEqExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.GE) {
      rValue = soot.jimple.myJimple.newGeExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.GT) {
      rValue = soot.jimple.myJimple.newGtExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.LE) {
      rValue = soot.jimple.myJimple.newLeExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.LT) {
      rValue = soot.jimple.myJimple.newLtExpr(lVal, rVal);
    } else if (operator == polyglot.ast.Binary.NE) {
      rValue = soot.jimple.myJimple.newNeExpr(lVal, rVal);
    } else {
      throw new RuntimeException("Unknown Comparison Expr");
    }

    return rValue;
  }

  /**
   * in bytecode and Jimple the conditions in conditional binary expressions are often reversed
   */
  private soot.Value reverseCondition(soot.jimple.ConditionExpr cond) {

    soot.jimple.ConditionExpr newExpr;
    if (cond instanceof soot.jimple.EqExpr) {
      newExpr = soot.jimple.myJimple.newNeExpr(cond.getOp1(), cond.getOp2());
    } else if (cond instanceof soot.jimple.NeExpr) {
      newExpr = soot.jimple.myJimple.newEqExpr(cond.getOp1(), cond.getOp2());
    } else if (cond instanceof soot.jimple.GtExpr) {
      newExpr = soot.jimple.myJimple.newLeExpr(cond.getOp1(), cond.getOp2());
    } else if (cond instanceof soot.jimple.GeExpr) {
      newExpr = soot.jimple.myJimple.newLtExpr(cond.getOp1(), cond.getOp2());
    } else if (cond instanceof soot.jimple.LtExpr) {
      newExpr = soot.jimple.myJimple.newGeExpr(cond.getOp1(), cond.getOp2());
    } else if (cond instanceof soot.jimple.LeExpr) {
      newExpr = soot.jimple.myJimple.newGtExpr(cond.getOp1(), cond.getOp2());
    } else {
      throw new RuntimeException("Unknown Condition Expr");
    }

    newExpr.getOp1Box().addAllTagsOf(cond.getOp1Box());
    newExpr.getOp2Box().addAllTagsOf(cond.getOp2Box());
    return newExpr;
  }

  /**
   * Special conditions for doubles and floats and longs
   */
  private soot.Value handleDFLCond(soot.jimple.ConditionExpr cond) {
    soot.Local result = lg.generateLocal(soot.ByteType.v());
    soot.jimple.Expr cmExpr = null;
    if (isDouble(cond.getOp1()) || isDouble(cond.getOp2()) || isFloat(cond.getOp1()) || isFloat(cond.getOp2())) {
      // use cmpg and cmpl
      if ((cond instanceof soot.jimple.GeExpr) || (cond instanceof soot.jimple.GtExpr)) {
        // use cmpg
        cmExpr = soot.jimple.myJimple.newCmpgExpr(cond.getOp1(), cond.getOp2());
      } else {
        // use cmpl
        cmExpr = soot.jimple.myJimple.newCmplExpr(cond.getOp1(), cond.getOp2());
      }
    } else if (isLong(cond.getOp1()) || isLong(cond.getOp2())) {
      // use cmp
      cmExpr = soot.jimple.myJimple.newCmpExpr(cond.getOp1(), cond.getOp2());
    } else {
      return cond;
    }
    soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(result, cmExpr);
    body.getUnits().add(assign);

    if (cond instanceof soot.jimple.EqExpr) {
      cond = soot.jimple.myJimple.newEqExpr(result, soot.jimple.IntConstant.v(0));
    } else if (cond instanceof soot.jimple.GeExpr) {
      cond = soot.jimple.myJimple.newGeExpr(result, soot.jimple.IntConstant.v(0));
    } else if (cond instanceof soot.jimple.GtExpr) {
      cond = soot.jimple.myJimple.newGtExpr(result, soot.jimple.IntConstant.v(0));
    } else if (cond instanceof soot.jimple.LeExpr) {
      cond = soot.jimple.myJimple.newLeExpr(result, soot.jimple.IntConstant.v(0));
    } else if (cond instanceof soot.jimple.LtExpr) {
      cond = soot.jimple.myJimple.newLtExpr(result, soot.jimple.IntConstant.v(0));
    } else if (cond instanceof soot.jimple.NeExpr) {
      cond = soot.jimple.myJimple.newNeExpr(result, soot.jimple.IntConstant.v(0));
    } else {
      throw new RuntimeException("Unknown Comparison Expr");
    }

    return cond;
  }

  private boolean isDouble(soot.Value val) {
    if (val.getType() instanceof soot.DoubleType) {
      return true;
    }
    return false;
  }

  private boolean isFloat(soot.Value val) {
    if (val.getType() instanceof soot.FloatType) {
      return true;
    }
    return false;
  }

  private boolean isLong(soot.Value val) {
    if (val.getType() instanceof soot.LongType) {
      return true;
    }
    return false;
  }

  /**
   * Creates a conitional AND expr
   */
  private soot.Value createCondAnd(polyglot.ast.Binary binary) {

    soot.Local retLocal = lg.generateLocal(soot.BooleanType.v());

    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();

    soot.Value lVal = base().createAggressiveExpr(binary.left(), false, false);
    boolean leftNeedIf = needSootIf(lVal);
    if (!(lVal instanceof soot.jimple.ConditionExpr)) {
      lVal = soot.jimple.myJimple.newEqExpr(lVal, soot.jimple.IntConstant.v(0));
    } else {
      lVal = reverseCondition((soot.jimple.ConditionExpr) lVal);
      lVal = handleDFLCond((soot.jimple.ConditionExpr) lVal);
    }

    if (leftNeedIf) {
      soot.jimple.IfStmt ifLeft;
      /*
       * if (!falseNoop.empty()){ soot.jimple.Stmt fNoop = (soot.jimple.Stmt)falseNoop.peek(); ifLeft =
       * soot.jimple.myJimple.newIfStmt(lVal, fNoop); } else {
       */
      ifLeft = soot.jimple.myJimple.newIfStmt(lVal, noop1);
      // }
      body.getUnits().add(ifLeft);
      Util.addLnPosTags(ifLeft.getConditionBox(), binary.left().position());
      Util.addLnPosTags(ifLeft, binary.left().position());
    }

    soot.jimple.Stmt endNoop = soot.jimple.myJimple.newNopStmt();
    soot.Value rVal = base().createAggressiveExpr(binary.right(), false, false);
    boolean rightNeedIf = needSootIf(rVal);
    if (!(rVal instanceof soot.jimple.ConditionExpr)) {
      rVal = soot.jimple.myJimple.newEqExpr(rVal, soot.jimple.IntConstant.v(0));
    } else {
      rVal = reverseCondition((soot.jimple.ConditionExpr) rVal);
      rVal = handleDFLCond((soot.jimple.ConditionExpr) rVal);
    }
    if (rightNeedIf) {
      soot.jimple.IfStmt ifRight;
      /*
       * if (!falseNoop.empty()){ soot.jimple.Stmt fNoop = (soot.jimple.Stmt)falseNoop.peek(); ifRight =
       * soot.jimple.myJimple.newIfStmt(rVal, fNoop); } else {
       */
      ifRight = soot.jimple.myJimple.newIfStmt(rVal, noop1);
      // }
      body.getUnits().add(ifRight);
      Util.addLnPosTags(ifRight.getConditionBox(), binary.right().position());
      Util.addLnPosTags(ifRight, binary.right().position());
    }

    // return if cond will be used in if
    /*
     * if (!falseNoop.empty()){ return soot.jimple.IntConstant.v(1); }
     */

    soot.jimple.Stmt assign1 = soot.jimple.myJimple.newAssignStmt(retLocal, soot.jimple.IntConstant.v(1));
    body.getUnits().add(assign1);
    soot.jimple.Stmt gotoEnd1 = soot.jimple.myJimple.newGotoStmt(endNoop);
    body.getUnits().add(gotoEnd1);

    body.getUnits().add(noop1);

    soot.jimple.Stmt assign2 = soot.jimple.myJimple.newAssignStmt(retLocal, soot.jimple.IntConstant.v(0));
    body.getUnits().add(assign2);

    body.getUnits().add(endNoop);

    Util.addLnPosTags(assign1, binary.position());
    Util.addLnPosTags(assign2, binary.position());

    return retLocal;
  }

  int inLeftOr = 0;

  /**
   * Creates a conditional OR expr
   */
  private soot.Value createCondOr(polyglot.ast.Binary binary) {
    // System.out.println("cond or binary: "+binary);
    soot.Local retLocal = lg.generateLocal(soot.BooleanType.v());

    // end
    soot.jimple.Stmt endNoop = soot.jimple.myJimple.newNopStmt();

    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();
    // inLeftOr++;
    soot.Value lVal = base().createAggressiveExpr(binary.left(), false, false);
    // inLeftOr--;

    // System.out.println("leftval : "+lVal);
    boolean leftNeedIf = needSootIf(lVal);
    if (!(lVal instanceof soot.jimple.ConditionExpr)) {
      lVal = soot.jimple.myJimple.newNeExpr(lVal, soot.jimple.IntConstant.v(0));
    } else {
      // no reversing of condition needed for first expr in conditional
      // or expression
      lVal = handleDFLCond((soot.jimple.ConditionExpr) lVal);
    }

    if (leftNeedIf) {
      soot.jimple.IfStmt ifLeft;
      /*
       * if (!trueNoop.empty()){ ifLeft = soot.jimple.myJimple.newIfStmt(lVal, (soot.jimple.Stmt)trueNoop.peek()); } else {
       */
      ifLeft = soot.jimple.myJimple.newIfStmt(lVal, noop1);
      // }
      body.getUnits().add(ifLeft);
      Util.addLnPosTags(ifLeft, binary.left().position());
      Util.addLnPosTags(ifLeft.getConditionBox(), binary.left().position());
    }

    soot.Value rVal = base().createAggressiveExpr(binary.right(), false, false);
    boolean rightNeedIf = needSootIf(rVal);
    if (!(rVal instanceof soot.jimple.ConditionExpr)) {
      rVal = soot.jimple.myJimple.newEqExpr(rVal, soot.jimple.IntConstant.v(0));
    } else {
      // need to reverse right part of conditional or expr
      if (/* !trueNoop.empty() && */ inLeftOr == 0) {
        rVal = reverseCondition((soot.jimple.ConditionExpr) rVal);
      }
      rVal = handleDFLCond((soot.jimple.ConditionExpr) rVal);
    }
    if (rightNeedIf) {

      soot.jimple.IfStmt ifRight;
      /*
       * if (!trueNoop.empty()){ if (inLeftOr == 0){ ifRight = soot.jimple.myJimple.newIfStmt(rVal,
       * (soot.jimple.Stmt)falseNoop.peek()); } else { ifRight = soot.jimple.myJimple.newIfStmt(rVal,
       * (soot.jimple.Stmt)trueNoop.peek()); } } else {
       */
      ifRight = soot.jimple.myJimple.newIfStmt(rVal, noop2);
      // }
      body.getUnits().add(ifRight);
      Util.addLnPosTags(ifRight, binary.right().position());
      Util.addLnPosTags(ifRight.getConditionBox(), binary.right().position());
    }

    // return if cond will be used in if
    /*
     * if (!trueNoop.empty()){ return soot.jimple.IntConstant.v(1); }
     */

    body.getUnits().add(noop1);

    soot.jimple.Stmt assign2 = soot.jimple.myJimple.newAssignStmt(retLocal, soot.jimple.IntConstant.v(1));
    body.getUnits().add(assign2);
    Util.addLnPosTags(assign2, binary.position());
    soot.jimple.Stmt gotoEnd2 = soot.jimple.myJimple.newGotoStmt(endNoop);
    body.getUnits().add(gotoEnd2);

    body.getUnits().add(noop2);

    soot.jimple.Stmt assign3 = soot.jimple.myJimple.newAssignStmt(retLocal, soot.jimple.IntConstant.v(0));
    body.getUnits().add(assign3);
    Util.addLnPosTags(assign3, binary.position());

    body.getUnits().add(endNoop);
    Util.addLnPosTags(assign2, binary.position());
    Util.addLnPosTags(assign3, binary.position());

    return retLocal;
  }

  private soot.Local handleCondBinExpr(soot.jimple.ConditionExpr condExpr) {

    soot.Local boolLocal = lg.generateLocal(soot.BooleanType.v());

    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();

    soot.Value newVal;

    newVal = reverseCondition(condExpr);
    newVal = handleDFLCond((soot.jimple.ConditionExpr) newVal);

    soot.jimple.Stmt ifStmt = soot.jimple.myJimple.newIfStmt(newVal, noop1);
    body.getUnits().add(ifStmt);

    body.getUnits().add(soot.jimple.myJimple.newAssignStmt(boolLocal, soot.jimple.IntConstant.v(1)));

    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();

    soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(noop2);

    body.getUnits().add(goto1);

    body.getUnits().add(noop1);

    body.getUnits().add(soot.jimple.myJimple.newAssignStmt(boolLocal, soot.jimple.IntConstant.v(0)));

    body.getUnits().add(noop2);

    return boolLocal;

  }

  private soot.Local handleCondBinExpr(soot.jimple.ConditionExpr condExpr, boolean reverse) {

    soot.Local boolLocal = lg.generateLocal(soot.BooleanType.v());

    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();

    soot.Value newVal = condExpr;

    if (reverse) {
      newVal = reverseCondition(condExpr);
    }
    newVal = handleDFLCond((soot.jimple.ConditionExpr) newVal);

    soot.jimple.Stmt ifStmt = soot.jimple.myJimple.newIfStmt(newVal, noop1);
    body.getUnits().add(ifStmt);

    body.getUnits().add(soot.jimple.myJimple.newAssignStmt(boolLocal, soot.jimple.IntConstant.v(1)));

    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();

    soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(noop2);

    body.getUnits().add(goto1);

    body.getUnits().add(noop1);

    body.getUnits().add(soot.jimple.myJimple.newAssignStmt(boolLocal, soot.jimple.IntConstant.v(0)));

    body.getUnits().add(noop2);

    return boolLocal;

  }

  private soot.Local createStringBuffer(polyglot.ast.Expr expr) {
    // create and add one string buffer
    soot.Local local = lg.generateLocal(soot.RefType.v("java.lang.StringBuffer"));
    soot.jimple.NewExpr newExpr = soot.jimple.myJimple.newNewExpr(soot.RefType.v("java.lang.StringBuffer"));
    soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(local, newExpr);

    body.getUnits().add(assign);
    Util.addLnPosTags(assign, expr.position());

    soot.SootClass classToInvoke1 = soot.myScene.getSootClass("java.lang.StringBuffer");
    soot.SootMethodRef methodToInvoke1
        = soot.myScene.makeMethodRef(classToInvoke1, "<init>", new ArrayList(), soot.VoidType.v(), false);

    soot.jimple.SpecialInvokeExpr invoke = soot.jimple.myJimple.newSpecialInvokeExpr(local, methodToInvoke1);

    soot.jimple.Stmt invokeStmt = soot.jimple.myJimple.newInvokeStmt(invoke);
    body.getUnits().add(invokeStmt);
    Util.addLnPosTags(invokeStmt, expr.position());

    return local;
  }

  private soot.Local createToString(soot.Local sb, polyglot.ast.Expr expr) {
    // invoke toString on local (type StringBuffer)
    soot.Local newString = lg.generateLocal(soot.RefType.v("java.lang.String"));
    soot.SootClass classToInvoke2 = soot.myScene.getSootClass("java.lang.StringBuffer");
    soot.SootMethodRef methodToInvoke2 = soot.myScene.makeMethodRef(classToInvoke2, "toString", new ArrayList(),
        soot.RefType.v("java.lang.String"), false);

    soot.jimple.VirtualInvokeExpr toStringInvoke = soot.jimple.myJimple.newVirtualInvokeExpr(sb, methodToInvoke2);

    soot.jimple.Stmt lastAssign = soot.jimple.myJimple.newAssignStmt(newString, toStringInvoke);

    body.getUnits().add(lastAssign);
    Util.addLnPosTags(lastAssign, expr.position());

    return newString;
  }

  private boolean isStringConcat(polyglot.ast.Expr expr) {
    if (expr instanceof polyglot.ast.Binary) {
      polyglot.ast.Binary bin = (polyglot.ast.Binary) expr;
      if (bin.operator() == polyglot.ast.Binary.ADD) {
        if (bin.type().toString().equals("java.lang.String")) {
          return true;
        }
        return false;
      }
      return false;
    } else if (expr instanceof polyglot.ast.Assign) {
      polyglot.ast.Assign assign = (polyglot.ast.Assign) expr;
      if (assign.operator() == polyglot.ast.Assign.ADD_ASSIGN) {
        if (assign.type().toString().equals("java.lang.String")) {
          return true;
        }
        return false;
      }
      return false;
    }
    return false;
  }

  /**
   * Generates one part of a concatenation String
   */
  private soot.Local generateAppends(polyglot.ast.Expr expr, soot.Local sb) {

    // System.out.println("generate appends for expr: "+expr);
    if (isStringConcat(expr)) {
      if (expr instanceof polyglot.ast.Binary) {
        sb = generateAppends(((polyglot.ast.Binary) expr).left(), sb);
        sb = generateAppends(((polyglot.ast.Binary) expr).right(), sb);
      } else {
        sb = generateAppends(((polyglot.ast.Assign) expr).left(), sb);
        sb = generateAppends(((polyglot.ast.Assign) expr).right(), sb);
      }
    } else {
      soot.Value toApp = base().createAggressiveExpr(expr, false, false);
      // System.out.println("toApp: "+toApp+" type: "+toApp.getType());
      soot.Type appendType = null;
      if (toApp instanceof soot.jimple.StringConstant) {
        appendType = soot.RefType.v("java.lang.String");
      } else if (toApp instanceof soot.jimple.NullConstant) {
        appendType = soot.RefType.v("java.lang.Object");
      } else if (toApp instanceof soot.jimple.Constant) {
        appendType = toApp.getType();
      } else if (toApp instanceof soot.Local) {
        if (((soot.Local) toApp).getType() instanceof soot.PrimType) {
          appendType = ((soot.Local) toApp).getType();
        } else if (((soot.Local) toApp).getType() instanceof soot.RefType) {
          if (((soot.Local) toApp).getType().toString().equals("java.lang.String")) {
            appendType = soot.RefType.v("java.lang.String");
          } else if (((soot.Local) toApp).getType().toString().equals("java.lang.StringBuffer")) {
            appendType = soot.RefType.v("java.lang.StringBuffer");
          } else {
            appendType = soot.RefType.v("java.lang.Object");
          }
        } else {
          // this is for arrays
          appendType = soot.RefType.v("java.lang.Object");
        }
      } else if (toApp instanceof soot.jimple.ConditionExpr) {
        toApp = handleCondBinExpr((soot.jimple.ConditionExpr) toApp);
        appendType = soot.BooleanType.v();
      }

      // handle shorts
      if (appendType instanceof soot.ShortType || appendType instanceof soot.ByteType) {
        soot.Local intLocal = lg.generateLocal(soot.IntType.v());
        soot.jimple.Expr cast = soot.jimple.myJimple.newCastExpr(toApp, soot.IntType.v());
        soot.jimple.Stmt castAssign = soot.jimple.myJimple.newAssignStmt(intLocal, cast);
        body.getUnits().add(castAssign);
        toApp = intLocal;
        appendType = soot.IntType.v();
      }

      ArrayList paramsTypes = new ArrayList();
      paramsTypes.add(appendType);
      ArrayList params = new ArrayList();
      params.add(toApp);

      soot.SootClass classToInvoke = soot.myScene.getSootClass("java.lang.StringBuffer");
      soot.SootMethodRef methodToInvoke = soot.myScene.makeMethodRef(classToInvoke, "append", paramsTypes,
          soot.RefType.v("java.lang.StringBuffer"), false);

      soot.jimple.VirtualInvokeExpr appendInvoke = soot.jimple.myJimple.newVirtualInvokeExpr(sb, methodToInvoke, params);

      Util.addLnPosTags(appendInvoke.getArgBox(0), expr.position());

      soot.Local tmp = lg.generateLocal(soot.RefType.v("java.lang.StringBuffer"));
      soot.jimple.Stmt appendStmt = soot.jimple.myJimple.newAssignStmt(tmp, appendInvoke);

      sb = tmp;

      body.getUnits().add(appendStmt);

      Util.addLnPosTags(appendStmt, expr.position());
    }
    return sb;
  }

  /**
   * Unary Expression Creation
   */
  private soot.Value getUnaryLocal(polyglot.ast.Unary unary) {

    polyglot.ast.Expr expr = unary.expr();
    polyglot.ast.Unary.Operator op = unary.operator();

    if (op == polyglot.ast.Unary.POST_INC || op == polyglot.ast.Unary.PRE_INC || op == polyglot.ast.Unary.POST_DEC
        || op == polyglot.ast.Unary.PRE_DEC) {
      if (base().needsAccessor(unary.expr())) {
        return base().handlePrivateFieldUnarySet(unary);
      }

      soot.Value left = base().createLHS(unary.expr());

      // do necessary cloning
      soot.Value leftClone = Jimple.cloneIfNecessary(left);

      soot.Local tmp = lg.generateLocal(left.getType());
      soot.jimple.AssignStmt stmt1 = soot.jimple.myJimple.newAssignStmt(tmp, left);
      body.getUnits().add(stmt1);
      Util.addLnPosTags(stmt1, unary.position());

      soot.Value incVal = base().getConstant(left.getType(), 1);

      soot.jimple.BinopExpr binExpr;
      if (unary.operator() == polyglot.ast.Unary.PRE_INC || unary.operator() == polyglot.ast.Unary.POST_INC) {
        binExpr = soot.jimple.myJimple.newAddExpr(tmp, incVal);
      } else {
        binExpr = soot.jimple.myJimple.newSubExpr(tmp, incVal);
      }

      soot.Local tmp2 = lg.generateLocal(left.getType());
      soot.jimple.AssignStmt assign = soot.jimple.myJimple.newAssignStmt(tmp2, binExpr);
      body.getUnits().add(assign);

      // if (base().needsAccessor(unary.expr())){
      // base().handlePrivateFieldSet(unary.expr(), tmp2);
      // }
      // else {
      soot.jimple.AssignStmt stmt3 = soot.jimple.myJimple.newAssignStmt(leftClone, tmp2);
      body.getUnits().add(stmt3);
      // }

      if (unary.operator() == polyglot.ast.Unary.POST_DEC || unary.operator() == polyglot.ast.Unary.POST_INC) {
        return tmp;
      } else {
        return tmp2;
      }
    }
    /*
     * if (op == polyglot.ast.Unary.POST_INC){ soot.Local retLocal = generateLocal(expr.type()); soot.Value sootExpr =
     * base().createExpr(expr); soot.jimple.AssignStmt preStmt = soot.jimple.myJimple.newAssignStmt(retLocal, sootExpr);
     * body.getUnits().add(preStmt);
     *
     * soot.jimple.AddExpr addExpr = soot.jimple.myJimple.newAddExpr(sootExpr, getConstant(retLocal.getType(), 1));
     *
     * Util.addLnPosTags(addExpr.getOp1Box(), expr.position());
     *
     * soot.Local local = generateLocal(expr.type()); soot.jimple.AssignStmt stmt =
     * soot.jimple.myJimple.newAssignStmt(local, addExpr); body.getUnits().add(stmt);
     *
     * Util.addLnPosTags(stmt, expr.position()); soot.jimple.AssignStmt aStmt =
     * soot.jimple.myJimple.newAssignStmt(sootExpr, local); body.getUnits().add(aStmt);
     *
     * Util.addLnPosTags(aStmt, expr.position()); Util.addLnPosTags(aStmt, unary.position());
     *
     * if ((expr instanceof polyglot.ast.Field) || (expr instanceof polyglot.ast.ArrayAccess)) { //if ((expr instanceof
     * polyglot.ast.Field) && (needsPrivateAccessor((polyglot.ast.Field)expr) ||
     * needsProtectedAccessor((polyglot.ast.Field)expr))){ if (base().needsAccessor(expr)){ handlePrivateFieldSet(expr,
     * local); } else { soot.Value actualUnaryExpr = createLHS(expr); soot.jimple.AssignStmt s =
     * soot.jimple.myJimple.newAssignStmt(actualUnaryExpr, local); body.getUnits().add(s); Util.addLnPosTags(s,
     * expr.position()); Util.addLnPosTags(s.getLeftOpBox(), expr.position()); }
     *
     * } return retLocal;
     *
     * } else if (op == polyglot.ast.Unary.POST_DEC) { soot.Local retLocal = generateLocal(expr.type());
     *
     * soot.Value sootExpr = base().createExpr(expr);
     *
     * soot.jimple.AssignStmt preStmt = soot.jimple.myJimple.newAssignStmt(retLocal, sootExpr);
     * body.getUnits().add(preStmt);
     *
     * soot.jimple.SubExpr subExpr = soot.jimple.myJimple.newSubExpr(sootExpr, getConstant(retLocal.getType(), 1));
     * Util.addLnPosTags(subExpr.getOp1Box(), expr.position());
     *
     * soot.Local local = generateLocal(expr.type()); soot.jimple.AssignStmt stmt =
     * soot.jimple.myJimple.newAssignStmt(local, subExpr); body.getUnits().add(stmt); Util.addLnPosTags(stmt,
     * expr.position());
     *
     * soot.jimple.AssignStmt aStmt = soot.jimple.myJimple.newAssignStmt(sootExpr, local); body.getUnits().add(aStmt);
     *
     * Util.addLnPosTags(aStmt, expr.position()); Util.addLnPosTags(aStmt, unary.position());
     *
     * if ((expr instanceof polyglot.ast.Field) || (expr instanceof polyglot.ast.ArrayAccess)) { //if ((expr instanceof
     * polyglot.ast.Field) && (needsPrivateAccessor((polyglot.ast.Field)expr) ||
     * needsProtectedAccessor((polyglot.ast.Field)expr))){ if (base().needsAccessor(expr)){ handlePrivateFieldSet(expr,
     * local); } else { soot.Value actualUnaryExpr = createLHS(expr); soot.jimple.AssignStmt s =
     * soot.jimple.myJimple.newAssignStmt(actualUnaryExpr, local); body.getUnits().add(s);
     *
     * Util.addLnPosTags(s, expr.position()); Util.addLnPosTags(s.getLeftOpBox(), expr.position()); } }
     *
     * return retLocal;
     *
     * } else if (op == polyglot.ast.Unary.PRE_INC) {
     *
     * soot.Value sootExpr = base().createExpr(expr);
     *
     * soot.jimple.AddExpr addExpr = soot.jimple.myJimple.newAddExpr(sootExpr, getConstant(sootExpr.getType(), 1));
     * Util.addLnPosTags(addExpr.getOp1Box(), expr.position());
     *
     * soot.Local local = generateLocal(expr.type());
     *
     * soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(local, addExpr);
     *
     * body.getUnits().add(stmt); Util.addLnPosTags(stmt, expr.position());
     *
     * if ((expr instanceof polyglot.ast.Field) || (expr instanceof polyglot.ast.ArrayAccess) || (expr instanceof
     * polyglot.ast.Local)) { //if ((expr instanceof polyglot.ast.Field) && (needsPrivateAccessor((polyglot.ast.Field)expr)
     * || needsProtectedAccessor((polyglot.ast.Field)expr))){ if (base().needsAccessor(expr)){ handlePrivateFieldSet(expr,
     * local); } else { soot.Value actualUnaryExpr = createLHS(expr);
     * body.getUnits().add(soot.jimple.myJimple.newAssignStmt( actualUnaryExpr, local)); } }
     *
     * return local;
     *
     * } else if (op == polyglot.ast.Unary.PRE_DEC) {
     *
     * soot.Value sootExpr = base().createExpr(expr);
     *
     * soot.jimple.SubExpr subExpr = soot.jimple.myJimple.newSubExpr(sootExpr, getConstant(sootExpr.getType(), 1));
     * Util.addLnPosTags(subExpr.getOp1Box(), expr.position());
     *
     * soot.Local local = generateLocal(expr.type());
     *
     * soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(local, subExpr);
     *
     * body.getUnits().add(stmt); Util.addLnPosTags(stmt, expr.position());
     *
     * if ((expr instanceof polyglot.ast.Field) || (expr instanceof polyglot.ast.ArrayAccess) || (expr instanceof
     * polyglot.ast.Local)) {
     *
     * //if ((expr instanceof polyglot.ast.Field) && (needsPrivateAccessor((polyglot.ast.Field)expr) ||
     * needsProtectedAccessor((polyglot.ast.Field)expr))){ if (base().needsAccessor(expr)){ handlePrivateFieldSet(expr,
     * local); } else { soot.Value actualUnaryExpr = createLHS(expr);
     * body.getUnits().add(soot.jimple.myJimple.newAssignStmt( actualUnaryExpr, local)); } }
     *
     * return local;
     *
     * }
     */
    else if (op == polyglot.ast.Unary.BIT_NOT) {
      soot.jimple.IntConstant int1 = soot.jimple.IntConstant.v(-1);

      soot.Local retLocal = generateLocal(expr.type());

      soot.Value sootExpr = base().createAggressiveExpr(expr, false, false);

      soot.jimple.XorExpr xor = soot.jimple.myJimple.newXorExpr(sootExpr, base().getConstant(sootExpr.getType(), -1));

      Util.addLnPosTags(xor.getOp1Box(), expr.position());
      soot.jimple.Stmt assign1 = soot.jimple.myJimple.newAssignStmt(retLocal, xor);

      body.getUnits().add(assign1);

      Util.addLnPosTags(assign1, unary.position());

      return retLocal;
    } else if (op == polyglot.ast.Unary.NEG) {
      soot.Value sootExpr;
      if (expr instanceof polyglot.ast.IntLit) {

        long longVal = ((polyglot.ast.IntLit) expr).value();
        if (((polyglot.ast.IntLit) expr).kind() == polyglot.ast.IntLit.LONG) {
          sootExpr = soot.jimple.LongConstant.v(-longVal);
        } else {
          sootExpr = soot.jimple.IntConstant.v(-(int) longVal);
        }
      } else if (expr instanceof polyglot.ast.FloatLit) {
        double doubleVal = ((polyglot.ast.FloatLit) expr).value();
        if (((polyglot.ast.FloatLit) expr).kind() == polyglot.ast.FloatLit.DOUBLE) {
          sootExpr = soot.jimple.DoubleConstant.v(-doubleVal);
        } else {
          sootExpr = soot.jimple.FloatConstant.v(-(float) doubleVal);
        }
      } else {
        soot.Value local = base().createAggressiveExpr(expr, false, false);

        soot.jimple.NegExpr negExpr = soot.jimple.myJimple.newNegExpr(local);
        sootExpr = negExpr;
        Util.addLnPosTags(negExpr.getOpBox(), expr.position());
      }

      soot.Local retLocal = generateLocal(expr.type());

      soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(retLocal, sootExpr);

      body.getUnits().add(assign);

      Util.addLnPosTags(assign, expr.position());

      return retLocal;

    } else if (op == polyglot.ast.Unary.POS) {
      soot.Local retLocal = generateLocal(expr.type());
      soot.Value sootExpr = base().createAggressiveExpr(expr, false, false);
      soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(retLocal, sootExpr);
      body.getUnits().add(assign);

      Util.addLnPosTags(assign, expr.position());

      return retLocal;
    } else if (op == polyglot.ast.Unary.NOT) {

      // pop any trueNoop and falseNoop - if its in an if and in a unary
      // then it needs old style generation
      boolean repush = false;
      soot.jimple.Stmt tNoop = null;
      soot.jimple.Stmt fNoop = null;
      if (!trueNoop.empty() && !falseNoop.empty()) {
        tNoop = trueNoop.pop();
        fNoop = falseNoop.pop();
        repush = true;
      }

      soot.Value local = base().createAggressiveExpr(expr, false, false);

      // repush right away to optimize ! for ifs
      if (repush) {
        trueNoop.push(tNoop);
        falseNoop.push(fNoop);
      }

      if (local instanceof soot.jimple.ConditionExpr) {
        local = handleCondBinExpr((soot.jimple.ConditionExpr) local);
      }
      soot.jimple.NeExpr neExpr = soot.jimple.myJimple.newNeExpr(local, base().getConstant(local.getType(), 0));

      soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();

      soot.jimple.IfStmt ifStmt;
      if (!falseNoop.empty()) {
        ifStmt = soot.jimple.myJimple.newIfStmt(neExpr, falseNoop.peek());
      } else {
        ifStmt = soot.jimple.myJimple.newIfStmt(neExpr, noop1);
      }
      body.getUnits().add(ifStmt);
      Util.addLnPosTags(ifStmt, expr.position());
      Util.addLnPosTags(ifStmt.getConditionBox(), expr.position());

      if (!falseNoop.empty()) {
        return soot.jimple.IntConstant.v(1);
      }
      soot.Local retLocal = lg.generateLocal(local.getType());

      soot.jimple.Stmt assign1 = soot.jimple.myJimple.newAssignStmt(retLocal, base().getConstant(retLocal.getType(), 1));

      body.getUnits().add(assign1);
      Util.addLnPosTags(assign1, expr.position());

      soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();

      soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(noop2);

      body.getUnits().add(goto1);

      body.getUnits().add(noop1);

      soot.jimple.Stmt assign2 = soot.jimple.myJimple.newAssignStmt(retLocal, base().getConstant(retLocal.getType(), 0));

      body.getUnits().add(assign2);
      Util.addLnPosTags(assign2, expr.position());

      body.getUnits().add(noop2);

      return retLocal;
    } else {
      throw new RuntimeException("Unhandled Unary Expr");
    }

  }

  /**
   * Returns a needed constant given a type and val
   */
  @Override
  protected soot.jimple.Constant getConstant(soot.Type type, int val) {

    if (type instanceof soot.DoubleType) {
      return soot.jimple.DoubleConstant.v(val);
    } else if (type instanceof soot.FloatType) {
      return soot.jimple.FloatConstant.v(val);
    } else if (type instanceof soot.LongType) {
      return soot.jimple.LongConstant.v(val);
    } else {
      return soot.jimple.IntConstant.v(val);
    }
  }

  /**
   * Cast Expression Creation
   */
  private soot.Value getCastLocal(polyglot.ast.Cast castExpr) {

    // if its already the right type
    if (castExpr.expr().type().equals(castExpr.type())
        || (castExpr.type().isClass() && Util.getSootType(castExpr.type()).toString().equals("java.lang.Object"))) {
      return base().createAggressiveExpr(castExpr.expr(), false, false);
    }

    soot.Value val;
    val = base().createAggressiveExpr(castExpr.expr(), false, false);
    soot.Type type = Util.getSootType(castExpr.type());

    soot.jimple.CastExpr cast = soot.jimple.myJimple.newCastExpr(val, type);
    Util.addLnPosTags(cast.getOpBox(), castExpr.expr().position());
    soot.Local retLocal = lg.generateLocal(cast.getCastType());
    soot.jimple.Stmt castAssign = soot.jimple.myJimple.newAssignStmt(retLocal, cast);
    body.getUnits().add(castAssign);
    Util.addLnPosTags(castAssign, castExpr.position());

    return retLocal;
  }

  /**
   * Procedure Call Helper Methods Returns list of params
   */
  private ArrayList getSootParams(polyglot.ast.ProcedureCall call) {

    ArrayList sootParams = new ArrayList();
    Iterator it = call.arguments().iterator();
    while (it.hasNext()) {
      polyglot.ast.Expr next = (polyglot.ast.Expr) it.next();
      soot.Value nextExpr = base().createAggressiveExpr(next, false, false);
      if (nextExpr instanceof soot.jimple.ConditionExpr) {
        nextExpr = handleCondBinExpr((soot.jimple.ConditionExpr) nextExpr);
      }
      sootParams.add(nextExpr);
    }
    return sootParams;
  }

  /**
   * Returns list of param types
   */
  private ArrayList getSootParamsTypes(polyglot.ast.ProcedureCall call) {

    ArrayList sootParamsTypes = new ArrayList();
    Iterator it = call.procedureInstance().formalTypes().iterator();
    while (it.hasNext()) {
      Object next = it.next();
      sootParamsTypes.add(Util.getSootType((polyglot.types.Type) next));
    }
    return sootParamsTypes;
  }

  /**
   * Gets the Soot Method form the given Soot Class
   */
  private soot.SootMethodRef getMethodFromClass(soot.SootClass sootClass, String name, ArrayList paramTypes,
      soot.Type returnType, boolean isStatic) {
    soot.SootMethodRef ref = soot.myScene.makeMethodRef(sootClass, name, paramTypes, returnType, isStatic);
    return ref;
  }

  /**
   * Adds extra params
   */
  private void handleFinalLocalParams(ArrayList sootParams, ArrayList sootParamTypes, polyglot.types.ClassType keyType) {

    HashMap<IdentityKey, AnonLocalClassInfo> finalLocalInfo = soot.javaToJimple.myInitialResolver.finalLocalInfo();
    if (finalLocalInfo != null) {
      if (finalLocalInfo.containsKey(new polyglot.util.IdentityKey(keyType))) {
        AnonLocalClassInfo alci = finalLocalInfo.get(new polyglot.util.IdentityKey(keyType));

        ArrayList<IdentityKey> finalLocals = alci.finalLocalsUsed();
        if (finalLocals != null) {
          Iterator<IdentityKey> it = finalLocals.iterator();
          while (it.hasNext()) {
            Object next = it.next();
            polyglot.types.LocalInstance li = (polyglot.types.LocalInstance) ((polyglot.util.IdentityKey) next).object();
            sootParamTypes.add(Util.getSootType(li.type()));
            sootParams.add(getLocal(li));
          }
        }
      }
    }
  }

  @Override
  protected soot.Local getThis(soot.Type sootType) {

    return Util.getThis(sootType, body, getThisMap, lg);
  }

  protected boolean needsOuterClassRef(polyglot.types.ClassType typeToInvoke) {
    // anon and local
    AnonLocalClassInfo info = myInitialResolver.finalLocalInfo().get(new polyglot.util.IdentityKey(typeToInvoke));

    if (myInitialResolver.isAnonInCCall(typeToInvoke)) {
      return false;
    }

    if ((info != null) && (!info.inStaticMethod())) {
      return true;
    }

    // other nested
    else if (typeToInvoke.isNested() && !typeToInvoke.flags().isStatic() && !typeToInvoke.isAnonymous()
        && !typeToInvoke.isLocal()) {
      return true;
    }

    return false;
  }

  /**
   * adds outer class params
   */
  private void handleOuterClassParams(ArrayList sootParams, soot.Value qVal, ArrayList sootParamsTypes,
      polyglot.types.ClassType typeToInvoke) {

    ArrayList needsRef = soot.javaToJimple.myInitialResolver.getHasOuterRefInInit();

    boolean addRef = needsOuterClassRef(typeToInvoke);// (needsRef != null)
    // &&
    // (needsRef.contains(Util.getSootType(typeToInvoke)));
    if (addRef) {
      // if adding an outer type ref always add exact type
      soot.SootClass outerClass = ((soot.RefType) Util.getSootType(typeToInvoke.outer())).getSootClass();
      sootParamsTypes.add(outerClass.getType());
    }

    if (addRef && !typeToInvoke.isAnonymous() && (qVal != null)) {
      // for nested and local if qualifier use that for param
      sootParams.add(qVal);
    } else if (addRef && !typeToInvoke.isAnonymous()) {
      soot.SootClass outerClass = ((soot.RefType) Util.getSootType(typeToInvoke.outer())).getSootClass();
      sootParams.add(getThis(outerClass.getType()));
    } else if (addRef && typeToInvoke.isAnonymous()) {
      soot.SootClass outerClass = ((soot.RefType) Util.getSootType(typeToInvoke.outer())).getSootClass();
      sootParams.add(getThis(outerClass.getType()));
    }

    // handle anon qualifiers
    if (typeToInvoke.isAnonymous() && (qVal != null)) {
      sootParamsTypes.add(qVal.getType());
      sootParams.add(qVal);
    }
  }

  /**
   * Constructor Call Creation
   */
  private void createConstructorCall(polyglot.ast.ConstructorCall cCall) {

    ArrayList sootParams = new ArrayList();
    ArrayList sootParamsTypes = new ArrayList();

    polyglot.types.ConstructorInstance cInst = cCall.constructorInstance();
    String containerName = null;

    if (cInst.container() instanceof polyglot.types.ClassType) {
      containerName = ((polyglot.types.ClassType) cInst.container()).fullName();
    }

    soot.SootClass classToInvoke;

    if (cCall.kind() == polyglot.ast.ConstructorCall.SUPER) {

      classToInvoke = ((soot.RefType) Util.getSootType(cInst.container())).getSootClass();
    } else if (cCall.kind() == polyglot.ast.ConstructorCall.THIS) {
      classToInvoke = body.getMethod().getDeclaringClass();
    } else {
      throw new RuntimeException("Unknown kind of Constructor Call");
    }
    soot.Local base = specialThisLocal;

    polyglot.types.ClassType objType = (polyglot.types.ClassType) cInst.container();
    soot.Local qVal = null;
    if (cCall.qualifier() != null) {
      // && (!(cCall.qualifier() instanceof
      // polyglot.ast.Special &&
      // ((polyglot.ast.Special)cCall.qualifier()).kind()
      // == polyglot.ast.Special.THIS)) ){
      qVal = (soot.Local) base().createAggressiveExpr(cCall.qualifier(), false, false);
    }
    handleOuterClassParams(sootParams, qVal, sootParamsTypes, objType);
    sootParams.addAll(getSootParams(cCall));
    sootParamsTypes.addAll(getSootParamsTypes(cCall));
    handleFinalLocalParams(sootParams, sootParamsTypes, (polyglot.types.ClassType) cCall.constructorInstance().container());

    soot.SootMethodRef methodToInvoke
        = getMethodFromClass(classToInvoke, "<init>", sootParamsTypes, soot.VoidType.v(), false);

    soot.jimple.SpecialInvokeExpr specialInvokeExpr
        = soot.jimple.myJimple.newSpecialInvokeExpr(base, methodToInvoke, sootParams);

    soot.jimple.Stmt invokeStmt = soot.jimple.myJimple.newInvokeStmt(specialInvokeExpr);

    body.getUnits().add(invokeStmt);
    Util.addLnPosTags(invokeStmt, cCall.position());

    // this is clearly broken if an outer class this ref was added as first
    // param
    int numParams = 0;
    Iterator invokeParamsIt = cCall.arguments().iterator();
    while (invokeParamsIt.hasNext()) {
      Util.addLnPosTags(specialInvokeExpr.getArgBox(numParams), ((polyglot.ast.Expr) invokeParamsIt.next()).position());
      numParams++;
    }

    // if method is <init> handle field inits
    if (body.getMethod().getName().equals("<init>") && (cCall.kind() == polyglot.ast.ConstructorCall.SUPER)) {

      handleOuterClassThisInit(body.getMethod());
      handleFinalLocalInits();
      handleFieldInits(body.getMethod());
      handleInitializerBlocks(body.getMethod());
    }

  }

  private void handleFinalLocalInits() {
    ArrayList<SootField> finalsList = ((PolyglotMethodSource) body.getMethod().getSource()).getFinalsList();
    if (finalsList == null) {
      return;
    }
    int paramCount = paramRefCount - finalsList.size();
    Iterator<SootField> it = finalsList.iterator();
    while (it.hasNext()) {
      soot.SootField sf = it.next();

      soot.jimple.FieldRef fieldRef = soot.jimple.myJimple.newInstanceFieldRef(specialThisLocal, sf.makeRef());
      soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(fieldRef, body.getParameterLocal(paramCount));
      body.getUnits().add(stmt);
      paramCount++;
    }
  }

  /**
   * Local Class Decl - Local Inner Class
   */
  private void createLocalClassDecl(polyglot.ast.LocalClassDecl cDecl) {
    BiMap lcMap = myInitialResolver.getLocalClassMap();
    String name = Util.getSootType(cDecl.decl().type()).toString();
    if (!myInitialResolver.hasClassInnerTag(body.getMethod().getDeclaringClass(), name)) {
      Util.addInnerClassTag(body.getMethod().getDeclaringClass(), name, null, cDecl.decl().name(),
          Util.getModifier(cDecl.decl().flags()));
    }
  }

  /**
   * New Expression Creation
   */
  private soot.Local getNewLocal(polyglot.ast.New newExpr) {

    // handle parameters/args
    ArrayList sootParams = new ArrayList();
    ArrayList sootParamsTypes = new ArrayList();

    polyglot.types.ClassType objType = (polyglot.types.ClassType) newExpr.objectType().type();

    if (newExpr.anonType() != null) {
      objType = newExpr.anonType();
      // add inner class tags for any anon classes created
      String name = Util.getSootType(objType).toString();
      polyglot.types.ClassType outerType = objType.outer();
      if (!myInitialResolver.hasClassInnerTag(body.getMethod().getDeclaringClass(), name)) {
        Util.addInnerClassTag(body.getMethod().getDeclaringClass(), name, null, null,
            outerType.flags().isInterface() ? soot.Modifier.PUBLIC | soot.Modifier.STATIC
                : Util.getModifier(objType.flags()));
      }
    } else {
      // not an anon class but actually invoking a new something
      if (!objType.isTopLevel()) {
        String name = Util.getSootType(objType).toString();
        polyglot.types.ClassType outerType = objType.outer();
        if (!myInitialResolver.hasClassInnerTag(body.getMethod().getDeclaringClass(), name)) {
          Util.addInnerClassTag(body.getMethod().getDeclaringClass(), name, Util.getSootType(outerType).toString(),
              objType.name(), outerType.flags().isInterface() ? soot.Modifier.PUBLIC | soot.Modifier.STATIC
                  : Util.getModifier(objType.flags()));
        }

      }
    }
    soot.RefType sootType = (soot.RefType) Util.getSootType(objType);
    soot.Local retLocal = lg.generateLocal(sootType);
    soot.jimple.NewExpr sootNew = soot.jimple.myJimple.newNewExpr(sootType);

    soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(retLocal, sootNew);
    body.getUnits().add(stmt);
    Util.addLnPosTags(stmt, newExpr.position());
    Util.addLnPosTags(stmt.getRightOpBox(), newExpr.position());

    soot.SootClass classToInvoke = sootType.getSootClass();
    // if no qualifier --> X to invoke is static
    soot.Value qVal = null;
    // System.out.println("new qualifier: "+newExpr.qualifier());
    // if (newExpr.qualifier() != null) {
    if (newExpr.qualifier() != null) {
      // && (!(newExpr.qualifier()
      // instanceof polyglot.ast.Special
      // &&
      // ((polyglot.ast.Special)newExpr.qualifier()).kind()
      // == polyglot.ast.Special.THIS)) ){
      qVal = base().createAggressiveExpr(newExpr.qualifier(), false, false);
    }
    handleOuterClassParams(sootParams, qVal, sootParamsTypes, objType);

    boolean repush = false;
    soot.jimple.Stmt tNoop = null;
    soot.jimple.Stmt fNoop = null;

    if (!trueNoop.empty() && !falseNoop.empty()) {
      tNoop = trueNoop.pop();
      fNoop = falseNoop.pop();
      repush = true;
    }

    sootParams.addAll(getSootParams(newExpr));

    if (repush) {
      trueNoop.push(tNoop);
      falseNoop.push(fNoop);
    }

    sootParamsTypes.addAll(getSootParamsTypes(newExpr));

    handleFinalLocalParams(sootParams, sootParamsTypes, objType);

    soot.SootMethodRef methodToInvoke
        = getMethodFromClass(classToInvoke, "<init>", sootParamsTypes, soot.VoidType.v(), false);
    soot.jimple.SpecialInvokeExpr specialInvokeExpr
        = soot.jimple.myJimple.newSpecialInvokeExpr(retLocal, methodToInvoke, sootParams);

    soot.jimple.Stmt invokeStmt = soot.jimple.myJimple.newInvokeStmt(specialInvokeExpr);

    body.getUnits().add(invokeStmt);
    Util.addLnPosTags(invokeStmt, newExpr.position());

    int numParams = 0;
    Iterator invokeParamsIt = newExpr.arguments().iterator();
    while (invokeParamsIt.hasNext()) {
      Util.addLnPosTags(specialInvokeExpr.getArgBox(numParams), ((polyglot.ast.Expr) invokeParamsIt.next()).position());
      numParams++;
    }

    return retLocal;
  }

  @Override
  protected soot.SootMethodRef getSootMethodRef(polyglot.ast.Call call) {
    soot.Type sootRecType;
    soot.SootClass receiverTypeClass;
    if (Util.getSootType(call.methodInstance().container()).equals(soot.RefType.v("java.lang.Object"))) {
      sootRecType = soot.RefType.v("java.lang.Object");
      receiverTypeClass = soot.myScene.getSootClass("java.lang.Object");
    } else {
      if (call.target().type() == null) {
        sootRecType = Util.getSootType(call.methodInstance().container());
      } else {
        sootRecType = Util.getSootType(call.target().type());
      }
      if (sootRecType instanceof soot.RefType) {
        receiverTypeClass = ((soot.RefType) sootRecType).getSootClass();
      } else if (sootRecType instanceof soot.ArrayType) {
        receiverTypeClass = soot.myScene.getSootClass("java.lang.Object");
      } else {
        throw new RuntimeException("call target problem: " + call);
      }
    }

    polyglot.types.MethodInstance methodInstance = call.methodInstance();
    soot.Type sootRetType = Util.getSootType(methodInstance.returnType());
    ArrayList sootParamsTypes = getSootParamsTypes(call);

    soot.SootMethodRef callMethod = soot.myScene.makeMethodRef(receiverTypeClass, methodInstance.name(), sootParamsTypes,
        sootRetType, methodInstance.flags().isStatic());
    return callMethod;
  }

  /**
   * Call Expression Creation
   */
  private soot.Local getCallLocal(polyglot.ast.Call call) {

    // handle name
    String name = call.name();
    // handle receiver/target
    polyglot.ast.Receiver receiver = call.target();
    // System.out.println("call: "+call+" receiver: "+receiver);
    soot.Local baseLocal;
    if ((receiver instanceof polyglot.ast.Special)
        && (((polyglot.ast.Special) receiver).kind() == polyglot.ast.Special.SUPER)
        && (((polyglot.ast.Special) receiver).qualifier() != null)) {
      baseLocal = getSpecialSuperQualifierLocal(call);
      return baseLocal;

    }
    baseLocal = (soot.Local) base().getBaseLocal(receiver);

    // System.out.println("base local: "+baseLocal);

    boolean repush = false;
    soot.jimple.Stmt tNoop = null;
    soot.jimple.Stmt fNoop = null;
    if (!trueNoop.empty() && !falseNoop.empty()) {
      tNoop = trueNoop.pop();
      fNoop = falseNoop.pop();
      repush = true;
    }
    ArrayList sootParams = getSootParams(call);

    if (repush) {
      trueNoop.push(tNoop);
      falseNoop.push(fNoop);
    }

    soot.SootMethodRef callMethod = base().getSootMethodRef(call);

    soot.Type sootRecType;
    soot.SootClass receiverTypeClass;
    if (Util.getSootType(call.methodInstance().container()).equals(soot.RefType.v("java.lang.Object"))) {
      sootRecType = soot.RefType.v("java.lang.Object");
      receiverTypeClass = soot.myScene.getSootClass("java.lang.Object");
    } else {
      if (call.target().type() == null) {
        sootRecType = Util.getSootType(call.methodInstance().container());
      } else {
        sootRecType = Util.getSootType(call.target().type());
      }
      if (sootRecType instanceof soot.RefType) {
        receiverTypeClass = ((soot.RefType) sootRecType).getSootClass();
      } else if (sootRecType instanceof soot.ArrayType) {
        receiverTypeClass = soot.myScene.getSootClass("java.lang.Object");
      } else {
        throw new RuntimeException("call target problem: " + call);
      }
    }

    polyglot.types.MethodInstance methodInstance = call.methodInstance();
    /*
     * soot.Type sootRetType = Util.getSootType(methodInstance.returnType()); ArrayList sootParamsTypes =
     * getSootParamsTypes(call); ArrayList sootParams = getSootParams(call);
     *
     * soot.SootMethodRef callMethod = soot.myScene.makeMethodRef(receiverTypeClass, methodInstance.name(),
     * sootParamsTypes, sootRetType, methodInstance.flags().isStatic());
     */

    boolean isPrivateAccess = false;
    // if (call.methodInstance().flags().isPrivate() &&
    // !Util.getSootType(call.methodInstance().container()).equals(body.getMethod().getDeclaringClass().getType())){
    if (needsAccessor(call)) {

      soot.SootClass containingClass = ((soot.RefType) Util.getSootType(call.methodInstance().container())).getSootClass();
      soot.SootClass classToAddMethTo = containingClass;

      if (call.methodInstance().flags().isProtected()) {

        if (myInitialResolver.hierarchy() == null) {
          myInitialResolver.hierarchy(new soot.FastHierarchy(myScene));
        }
        soot.SootClass addToClass;
        if (body.getMethod().getDeclaringClass().hasOuterClass()) {
          addToClass = body.getMethod().getDeclaringClass().getOuterClass();

          while (!myInitialResolver.hierarchy().canStoreType(containingClass.getType(), addToClass.getType())) {
            if (addToClass.hasOuterClass()) {
              addToClass = addToClass.getOuterClass();
            } else {
              break;
            }
          }
        } else {
          addToClass = containingClass;
        }
        classToAddMethTo = addToClass;
      }

      callMethod = addGetMethodAccessMeth(classToAddMethTo, call).makeRef();
      if (!call.methodInstance().flags().isStatic()) {

        if (call.target() instanceof polyglot.ast.Expr) {
          sootParams.add(0, baseLocal);
        }

        else if (body.getMethod().getDeclaringClass().declaresFieldByName("this$0")) {
          sootParams.add(0, getThis(Util.getSootType(call.methodInstance().container())));// baseLocal);
        } else {
          sootParams.add(0, baseLocal);
        }
      }
      isPrivateAccess = true;
    }

    soot.jimple.InvokeExpr invokeExpr;
    if (isPrivateAccess) {
      // for accessing private methods in outer class -> always static
      invokeExpr = soot.jimple.myJimple.newStaticInvokeExpr(callMethod, sootParams);
    } else if (soot.Modifier.isInterface(receiverTypeClass.getModifiers()) && methodInstance.flags().isAbstract()) {
      // if reciever class is interface and method is abstract ->
      // interface
      invokeExpr = soot.jimple.myJimple.newInterfaceInvokeExpr(baseLocal, callMethod, sootParams);
    } else if (methodInstance.flags().isStatic()) {
      // if flag isStatic -> static invoke
      invokeExpr = soot.jimple.myJimple.newStaticInvokeExpr(callMethod, sootParams);
    } else if (methodInstance.flags().isPrivate()) {
      // if flag isPrivate -> special invoke
      invokeExpr = soot.jimple.myJimple.newSpecialInvokeExpr(baseLocal, callMethod, sootParams);
    } else if ((receiver instanceof polyglot.ast.Special)
        && (((polyglot.ast.Special) receiver).kind() == polyglot.ast.Special.SUPER)) {
      // receiver is special super -> special
      invokeExpr = soot.jimple.myJimple.newSpecialInvokeExpr(baseLocal, callMethod, sootParams);
    } else {
      // else virtual invoke
      invokeExpr = soot.jimple.myJimple.newVirtualInvokeExpr(baseLocal, callMethod, sootParams);

    }

    int numParams = 0;
    Iterator callParamsIt = call.arguments().iterator();
    while (callParamsIt.hasNext()) {
      Util.addLnPosTags(invokeExpr.getArgBox(numParams), ((polyglot.ast.Expr) callParamsIt.next()).position());
      numParams++;
    }

    if (invokeExpr instanceof soot.jimple.InstanceInvokeExpr) {
      Util.addLnPosTags(((soot.jimple.InstanceInvokeExpr) invokeExpr).getBaseBox(), call.target().position());
    }

    // create an assign stmt so invoke can be used somewhere else

    if (invokeExpr.getMethodRef().returnType().equals(soot.VoidType.v())) {
      soot.jimple.Stmt invoke = soot.jimple.myJimple.newInvokeStmt(invokeExpr);
      body.getUnits().add(invoke);
      Util.addLnPosTags(invoke, call.position());
      return null;
    } else {
      soot.Local retLocal = lg.generateLocal(invokeExpr.getMethodRef().returnType());

      soot.jimple.Stmt assignStmt = soot.jimple.myJimple.newAssignStmt(retLocal, invokeExpr);

      // add assign stmt to body
      body.getUnits().add(assignStmt);

      Util.addLnPosTags(assignStmt, call.position());
      return retLocal;
    }
  }

  @Override
  protected soot.Value getBaseLocal(polyglot.ast.Receiver receiver) {

    if (receiver instanceof polyglot.ast.TypeNode) {
      return generateLocal(((polyglot.ast.TypeNode) receiver).type());
    } else {
      soot.Value val = base().createAggressiveExpr((polyglot.ast.Expr) receiver, false, false);
      if (val instanceof soot.jimple.Constant) {
        soot.Local retLocal = lg.generateLocal(val.getType());
        soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(retLocal, val);
        body.getUnits().add(stmt);
        return retLocal;
      }
      return val;
    }
  }

  /**
   * NewArray Expression Creation
   */
  private soot.Local getNewArrayLocal(polyglot.ast.NewArray newArrExpr) {

    soot.Type sootType = Util.getSootType(newArrExpr.type());

    // System.out.println("creating new array of type: "+sootType);
    soot.jimple.Expr expr;
    if (newArrExpr.numDims() == 1) {

      soot.Value dimLocal;
      if (newArrExpr.additionalDims() == 1) {
        dimLocal = soot.jimple.IntConstant.v(1);
      } else {
        dimLocal = base().createAggressiveExpr((polyglot.ast.Expr) newArrExpr.dims().get(0), false, false);
      }
      // System.out.println("creating new array:
      // "+((soot.ArrayType)sootType).getElementType());
      soot.jimple.NewArrayExpr newArrayExpr
          = soot.jimple.myJimple.newNewArrayExpr(((soot.ArrayType) sootType).getElementType(), dimLocal);
      expr = newArrayExpr;
      if (newArrExpr.additionalDims() != 1) {
        Util.addLnPosTags(newArrayExpr.getSizeBox(), ((polyglot.ast.Expr) newArrExpr.dims().get(0)).position());
      }
    } else {

      ArrayList valuesList = new ArrayList();
      Iterator it = newArrExpr.dims().iterator();
      while (it.hasNext()) {
        valuesList.add(base().createAggressiveExpr((polyglot.ast.Expr) it.next(), false, false));
      }

      if (newArrExpr.additionalDims() != 0) {
        valuesList.add(soot.jimple.IntConstant.v(newArrExpr.additionalDims()));
      }
      soot.jimple.NewMultiArrayExpr newMultiArrayExpr
          = soot.jimple.myJimple.newNewMultiArrayExpr((soot.ArrayType) sootType, valuesList);

      expr = newMultiArrayExpr;
      Iterator sizeBoxIt = newArrExpr.dims().iterator();
      int counter = 0;
      while (sizeBoxIt.hasNext()) {
        Util.addLnPosTags(newMultiArrayExpr.getSizeBox(counter), ((polyglot.ast.Expr) sizeBoxIt.next()).position());
        counter++;
      }
    }

    soot.Local retLocal = lg.generateLocal(sootType);

    soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(retLocal, expr);

    body.getUnits().add(stmt);

    Util.addLnPosTags(stmt, newArrExpr.position());
    Util.addLnPosTags(stmt.getRightOpBox(), newArrExpr.position());

    // handle array init if one exists
    if (newArrExpr.init() != null) {
      soot.Value initVal = getArrayInitLocal(newArrExpr.init(), newArrExpr.type());
      soot.jimple.AssignStmt initStmt = soot.jimple.myJimple.newAssignStmt(retLocal, initVal);

      body.getUnits().add(initStmt);

    }

    return retLocal;

  }

  /**
   * create ArrayInit given init and the array local
   */
  private soot.Local getArrayInitLocal(polyglot.ast.ArrayInit arrInit, polyglot.types.Type lhsType) {

    // System.out.println("lhs type: "+lhsType);

    soot.Local local = generateLocal(lhsType);

    // System.out.println("creating new array:
    // "+((soot.ArrayType)local.getType()).getElementType());
    soot.jimple.NewArrayExpr arrExpr = soot.jimple.myJimple.newNewArrayExpr(
        ((soot.ArrayType) local.getType()).getElementType(), soot.jimple.IntConstant.v(arrInit.elements().size()));

    soot.jimple.Stmt assign = soot.jimple.myJimple.newAssignStmt(local, arrExpr);

    body.getUnits().add(assign);
    Util.addLnPosTags(assign, arrInit.position());

    Iterator it = arrInit.elements().iterator();
    int index = 0;

    while (it.hasNext()) {

      polyglot.ast.Expr elemExpr = (polyglot.ast.Expr) it.next();
      soot.Value elem;
      if (elemExpr instanceof polyglot.ast.ArrayInit) {

        if (((polyglot.ast.ArrayInit) elemExpr).type() instanceof polyglot.types.NullType) {
          if (lhsType instanceof polyglot.types.ArrayType) {
            // System.out.println("coming from 1 in get
            // arrayinitlocal"+((polyglot.types.ArrayType)lhsType).base());
            elem = getArrayInitLocal((polyglot.ast.ArrayInit) elemExpr, ((polyglot.types.ArrayType) lhsType).base());
          } else {
            // System.out.println("coming from 2 in get
            // arrayinitlocal"+((polyglot.types.ArrayType)lhsType).base());
            elem = getArrayInitLocal((polyglot.ast.ArrayInit) elemExpr, lhsType);

          }
        } else {
          // System.out.println("coming from 3 in get
          // arrayinitlocal"+((polyglot.types.ArrayType)lhsType).base());
          // elem =
          // getArrayInitLocal((polyglot.ast.ArrayInit)elemExpr,
          // ((polyglot.ast.ArrayInit)elemExpr).type());
          elem = getArrayInitLocal((polyglot.ast.ArrayInit) elemExpr, ((polyglot.types.ArrayType) lhsType).base());
        }
      } else {
        elem = base().createAggressiveExpr(elemExpr, false, false);
      }
      soot.jimple.ArrayRef arrRef = soot.jimple.myJimple.newArrayRef(local, soot.jimple.IntConstant.v(index));

      soot.jimple.AssignStmt elemAssign = soot.jimple.myJimple.newAssignStmt(arrRef, elem);
      body.getUnits().add(elemAssign);
      Util.addLnPosTags(elemAssign, elemExpr.position());
      Util.addLnPosTags(elemAssign.getRightOpBox(), elemExpr.position());

      index++;
    }

    return local;
  }

  /**
   * create LHS expressions
   */
  @Override
  protected soot.Value createLHS(polyglot.ast.Expr expr) {
    if (expr instanceof polyglot.ast.Local) {
      return getLocal((polyglot.ast.Local) expr);
    } else if (expr instanceof polyglot.ast.ArrayAccess) {
      return getArrayRefLocalLeft((polyglot.ast.ArrayAccess) expr);
    } else if (expr instanceof polyglot.ast.Field) {
      return getFieldLocalLeft((polyglot.ast.Field) expr);
    } else {
      throw new RuntimeException("Unhandled LHS");
    }
  }

  /**
   * Array Ref Expression Creation - LHS
   */
  private soot.Value getArrayRefLocalLeft(polyglot.ast.ArrayAccess arrayRefExpr) {
    polyglot.ast.Expr array = arrayRefExpr.array();
    polyglot.ast.Expr access = arrayRefExpr.index();

    soot.Local arrLocal = (soot.Local) base().createAggressiveExpr(array, false, false);
    soot.Value arrAccess = base().createAggressiveExpr(access, false, false);

    soot.Local retLocal = generateLocal(arrayRefExpr.type());

    soot.jimple.ArrayRef ref = soot.jimple.myJimple.newArrayRef(arrLocal, arrAccess);

    Util.addLnPosTags(ref.getBaseBox(), arrayRefExpr.array().position());
    Util.addLnPosTags(ref.getIndexBox(), arrayRefExpr.index().position());
    return ref;
  }

  /**
   * Array Ref Expression Creation
   */
  private soot.Value getArrayRefLocal(polyglot.ast.ArrayAccess arrayRefExpr) {

    polyglot.ast.Expr array = arrayRefExpr.array();
    polyglot.ast.Expr access = arrayRefExpr.index();

    soot.Local arrLocal = (soot.Local) base().createAggressiveExpr(array, false, false);
    soot.Value arrAccess = base().createAggressiveExpr(access, false, false);

    soot.Local retLocal = generateLocal(arrayRefExpr.type());

    soot.jimple.ArrayRef ref = soot.jimple.myJimple.newArrayRef(arrLocal, arrAccess);

    Util.addLnPosTags(ref.getBaseBox(), arrayRefExpr.array().position());
    Util.addLnPosTags(ref.getIndexBox(), arrayRefExpr.index().position());

    soot.jimple.Stmt stmt = soot.jimple.myJimple.newAssignStmt(retLocal, ref);
    body.getUnits().add(stmt);
    Util.addLnPosTags(stmt, arrayRefExpr.position());

    return retLocal;
  }

  private soot.Local getSpecialSuperQualifierLocal(polyglot.ast.Expr expr) {
    soot.SootClass classToInvoke;
    ArrayList methodParams = new ArrayList();
    if (expr instanceof polyglot.ast.Call) {
      polyglot.ast.Special target = (polyglot.ast.Special) ((polyglot.ast.Call) expr).target();
      classToInvoke = ((soot.RefType) Util.getSootType(target.qualifier().type())).getSootClass();
      methodParams = getSootParams((polyglot.ast.Call) expr);
    } else if (expr instanceof polyglot.ast.Field) {
      polyglot.ast.Special target = (polyglot.ast.Special) ((polyglot.ast.Field) expr).target();
      classToInvoke = ((soot.RefType) Util.getSootType(target.qualifier().type())).getSootClass();
    } else {
      throw new RuntimeException("Trying to create special super qualifier for: " + expr + " which is not a field or call");
    }
    // make an access method
    soot.SootMethod methToInvoke = makeSuperAccessMethod(classToInvoke, expr);
    // invoke it
    soot.Local classToInvokeLocal = Util.getThis(classToInvoke.getType(), body, getThisMap, lg);
    methodParams.add(0, classToInvokeLocal);

    soot.jimple.InvokeExpr invokeExpr = soot.jimple.myJimple.newStaticInvokeExpr(methToInvoke.makeRef(), methodParams);

    // return the local of return type if not void
    if (!methToInvoke.getReturnType().equals(soot.VoidType.v())) {
      soot.Local retLocal = lg.generateLocal(methToInvoke.getReturnType());
      soot.jimple.AssignStmt stmt = soot.jimple.myJimple.newAssignStmt(retLocal, invokeExpr);
      body.getUnits().add(stmt);

      return retLocal;
    } else {
      body.getUnits().add(soot.jimple.myJimple.newInvokeStmt(invokeExpr));
      return null;
    }
  }

  /**
   * Special Expression Creation
   */
  private soot.Local getSpecialLocal(polyglot.ast.Special specialExpr) {

    // System.out.println(specialExpr);
    if (specialExpr.kind() == polyglot.ast.Special.SUPER) {
      if (specialExpr.qualifier() == null) {
        return specialThisLocal;
      } else {
        // this isn't enough
        // need to getThis for the type which may be several levels up
        // add access$N method to class of the type which returns
        // field or method wanted
        // invoke it
        // and it needs to be called specially when getting fields
        // or calls because need to know field or method to access
        // as it access' a field or meth in the super class of the
        // outer class refered to by the qualifier
        return getThis(Util.getSootType(specialExpr.qualifier().type()));
      }
    } else if (specialExpr.kind() == polyglot.ast.Special.THIS) {
      // System.out.println("this is special this: "+specialExpr);
      if (specialExpr.qualifier() == null) {
        return specialThisLocal;
      } else {
        return getThis(Util.getSootType(specialExpr.qualifier().type()));
      }
    } else {
      throw new RuntimeException("Unknown Special");
    }
  }

  private soot.SootMethod makeSuperAccessMethod(soot.SootClass classToInvoke, Object memberToAccess) {
    String name = "access$" + soot.javaToJimple.myInitialResolver.getNextPrivateAccessCounter() + "00";
    ArrayList paramTypes = new ArrayList();
    paramTypes.add(classToInvoke.getType());

    soot.SootMethod meth;
    soot.MethodSource src;
    if (memberToAccess instanceof polyglot.ast.Field) {
      polyglot.ast.Field fieldToAccess = (polyglot.ast.Field) memberToAccess;
      meth = myScene.makeSootMethod(name, paramTypes, Util.getSootType(fieldToAccess.type()), soot.Modifier.STATIC);
      PrivateFieldAccMethodSource fSrc = new PrivateFieldAccMethodSource(Util.getSootType(fieldToAccess.type()),
          fieldToAccess.name(), fieldToAccess.flags().isStatic(),
          ((soot.RefType) Util.getSootType(fieldToAccess.target().type())).getSootClass());
      src = fSrc;
    } else if (memberToAccess instanceof polyglot.ast.Call) {
      polyglot.ast.Call methToAccess = (polyglot.ast.Call) memberToAccess;
      paramTypes.addAll(getSootParamsTypes(methToAccess));
      meth = myScene.makeSootMethod(name, paramTypes, Util.getSootType(methToAccess.methodInstance().returnType()),
          soot.Modifier.STATIC);
      PrivateMethodAccMethodSource mSrc = new PrivateMethodAccMethodSource(methToAccess.methodInstance());
      src = mSrc;
    } else {
      throw new RuntimeException("trying to access unhandled member type: " + memberToAccess);
    }
    classToInvoke.addMethod(meth);
    meth.setActiveBody(src.getBody(meth, null));
    meth.addTag(new soot.tagkit.SyntheticTag());
    return meth;
  }

  /**
   * InstanceOf Expression Creation
   */
  private soot.Local getInstanceOfLocal(polyglot.ast.Instanceof instExpr) {

    soot.Type sootType = Util.getSootType(instExpr.compareType().type());

    soot.Value local = base().createAggressiveExpr(instExpr.expr(), false, false);

    soot.jimple.InstanceOfExpr instOfExpr = soot.jimple.myJimple.newInstanceOfExpr(local, sootType);

    soot.Local lhs = lg.generateLocal(soot.BooleanType.v());

    soot.jimple.AssignStmt instAssign = soot.jimple.myJimple.newAssignStmt(lhs, instOfExpr);
    body.getUnits().add(instAssign);
    Util.addLnPosTags(instAssign, instExpr.position());
    Util.addLnPosTags(instAssign.getRightOpBox(), instExpr.position());

    Util.addLnPosTags(instOfExpr.getOpBox(), instExpr.expr().position());
    return lhs;
  }

  /**
   * Condition Expression Creation - can maybe merge with If
   */
  private soot.Local getConditionalLocal(polyglot.ast.Conditional condExpr) {

    // handle cond
    soot.jimple.Stmt noop1 = soot.jimple.myJimple.newNopStmt();
    polyglot.ast.Expr condition = condExpr.cond();
    createBranchingExpr(condition, noop1, false);

    soot.Local retLocal = generateLocal(condExpr.type());

    // handle consequence
    polyglot.ast.Expr consequence = condExpr.consequent();

    soot.Value conseqVal = base().createAggressiveExpr(consequence, false, false);
    if (conseqVal instanceof soot.jimple.ConditionExpr) {
      conseqVal = handleCondBinExpr((soot.jimple.ConditionExpr) conseqVal);
    }
    soot.jimple.AssignStmt conseqAssignStmt = soot.jimple.myJimple.newAssignStmt(retLocal, conseqVal);
    body.getUnits().add(conseqAssignStmt);
    Util.addLnPosTags(conseqAssignStmt, condExpr.position());
    Util.addLnPosTags(conseqAssignStmt.getRightOpBox(), consequence.position());

    soot.jimple.Stmt noop2 = soot.jimple.myJimple.newNopStmt();
    soot.jimple.Stmt goto1 = soot.jimple.myJimple.newGotoStmt(noop2);
    body.getUnits().add(goto1);

    // handle alternative

    body.getUnits().add(noop1);
    polyglot.ast.Expr alternative = condExpr.alternative();
    if (alternative != null) {
      soot.Value altVal = base().createAggressiveExpr(alternative, false, false);
      if (altVal instanceof soot.jimple.ConditionExpr) {
        altVal = handleCondBinExpr((soot.jimple.ConditionExpr) altVal);
      }
      soot.jimple.AssignStmt altAssignStmt = soot.jimple.myJimple.newAssignStmt(retLocal, altVal);
      body.getUnits().add(altAssignStmt);
      Util.addLnPosTags(altAssignStmt, condExpr.position());
      Util.addLnPosTags(altAssignStmt, alternative.position());
      Util.addLnPosTags(altAssignStmt.getRightOpBox(), alternative.position());
    }
    body.getUnits().add(noop2);

    return retLocal;
  }

  /**
   * Utility methods
   */
  /*
   * private boolean isLitOrLocal(polyglot.ast.Expr exp) { if (exp instanceof polyglot.ast.Lit) return true; if (exp
   * instanceof polyglot.ast.Local) return true; else return false; }
   */

  /**
   * Extra Local Variables Generation
   */
  @Override
  protected soot.Local generateLocal(polyglot.types.Type polyglotType) {
    soot.Type type = Util.getSootType(polyglotType);
    return lg.generateLocal(type);
  }

  @Override
  protected soot.Local generateLocal(soot.Type sootType) {
    return lg.generateLocal(sootType);
  }
}
