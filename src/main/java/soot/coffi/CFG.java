package soot.coffi;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 Clark Verbrugge
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.Vector;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.ArrayType;
import soot.Local;
import soot.Modifier;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.StmtAddressType;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.ConditionExpr;
import soot.jimple.ConstantFactory;
import soot.jimple.Expr;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.NullConstant;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.TableSwitchStmt;
import soot.options.Options;
import soot.tagkit.BytecodeOffsetTag;
import soot.tagkit.LineNumberTag;
import soot.tagkit.Tag;
import soot.util.ArraySet;
import soot.util.Chain;

/**
 * A Control Flow Graph.
 *
 * @author Clark Verbrugge
 */
public class CFG {
  private static final Logger logger = LoggerFactory.getLogger(CFG.class);

  /**
   * Method for which this is a control flow graph.
   *
   * @see method_info
   */
  private method_info method;
  /**
   * Ordered list of BasicBlocks comprising the code of this CFG.
   */
  BasicBlock cfg;

  Chain<Unit> units;
  JimpleBody listBody;

  Map<Instruction, Stmt> instructionToFirstStmt;
  Map<Instruction, Stmt> instructionToLastStmt;
  SootMethod jmethod;
  Scene cm;

  Instruction firstInstruction;
  Instruction lastInstruction;

  private Instruction sentinel;
  private Hashtable<Instruction, BasicBlock> h2bb, t2bb;
  private Options myOptions;
  private Scene myScene;
  private Util myCoffiUtil;
  private Jimple myJimple;
  private ConstantFactory constancFactory;

  /**
   * Constructs a new control flow graph for the given method.
   *
   * @param m
   *          the method in question.
   * @param myOptions
   * @param myScene
   * @param myCoffiUtil
   * @param myJimple
   * @param constancFactory
   * @see method_info
   */
  public CFG(method_info m, Options myOptions, Scene myScene, Util myCoffiUtil, Jimple myJimple, ConstantFactory constancFactory) {
    this.method = m;
    this.myOptions = myOptions;
    this.myScene = myScene;
    this.myCoffiUtil = myCoffiUtil;
    this.myJimple = myJimple;
    this.constancFactory = constancFactory;

    this.sentinel = new Instruction_Nop();
    this.sentinel.next = m.instructions;
    m.instructions.prev = this.sentinel;

    // printInstructions();
    // printExceptionTable();

    eliminateJsrRets();

    // printInstructions();
    // printExceptionTable();

    buildBBCFG();

    // printBBs();
    // printBBCFGSucc();

    m.cfg = this;

    if (cfg != null) {
      cfg.beginCode = true;
      firstInstruction = cfg.head;
    } else {
      firstInstruction = null;
    }

    // calculate complexity metrics
    if (soot.jbco.Main.metrics) {
      complexity();
    }
  }

  public static HashMap<SootMethod, int[]> methodsToVEM = new HashMap<SootMethod, int[]>();

  private void complexity() {
    // ignore all non-app classes
    if (!method.jmethod.getDeclaringClass().isApplicationClass()) {
      return;
    }

    BasicBlock b = this.cfg;
    HashMap<BasicBlock, Integer> block2exc = new HashMap<BasicBlock, Integer>();
    int tmp, nodes = 0, edges = 0, highest = 0;

    while (b != null) {
      tmp = 0;
      for (exception_table_entry element : method.code_attr.exception_table) {
        Instruction start = element.start_inst;
        Instruction end = element.start_inst;
        if ((start.label >= b.head.label && start.label <= b.tail.label)
            || (end.label > b.head.label && (b.tail.next == null || end.label <= b.tail.next.label))) {
          tmp++;
        }
      }
      block2exc.put(b, new Integer(tmp));
      b = b.next;
    }

    b = this.cfg;
    while (b != null) {
      nodes++;
      tmp = b.succ.size() + block2exc.get(b).intValue();

      // exceptions are not counted in succs and preds so we need to do so manually
      int deg = b.pred.size() + tmp + (b.beginException ? 1 : 0);
      if (deg > highest) {
        highest = deg;
      }
      edges += tmp;
      b = b.next;
    }
    methodsToVEM.put(method.jmethod, new int[] { nodes, edges, highest });
  }

  // Constructs the actual control flow graph. Assumes the hash table
  // currently associates leaders with BasicBlocks, this function
  // builds the next[] and prev[] pointer arrays.
  private void buildBBCFG() {
    Object branches[];
    Code_attribute ca = method.locate_code_attribute();

    {
      h2bb = new Hashtable<Instruction, BasicBlock>(100, 25);
      t2bb = new Hashtable<Instruction, BasicBlock>(100, 25);

      Instruction insn = this.sentinel.next;
      BasicBlock blast = null;
      if (insn != null) {
        Instruction tail = buildBasicBlock(insn);
        cfg = new BasicBlock(insn, tail);
        h2bb.put(insn, cfg);
        t2bb.put(tail, cfg);
        insn = tail.next;
        blast = cfg;
      }

      while (insn != null) {
        Instruction tail = buildBasicBlock(insn);
        BasicBlock block = new BasicBlock(insn, tail);
        blast.next = block;
        blast = block;
        h2bb.put(insn, block);
        t2bb.put(tail, block);
        insn = tail.next;
      }
    }

    BasicBlock block = cfg;

    while (block != null) {
      Instruction insn = block.tail;

      if (insn.branches) {
        if (insn instanceof Instruction_Athrow) {
          // see how many targets it can reach. Note that this is a
          // subset of the exception_table.
          HashSet<Instruction> ethandlers = new HashSet<Instruction>();

          // not quite a subset---could also be that control
          // exits this method, so start icount at 1
          for (int i = 0; i < ca.exception_table_length; i++) {
            exception_table_entry etentry = ca.exception_table[i];

            if (insn.label >= etentry.start_inst.label
                && (etentry.end_inst == null || insn.label < etentry.end_inst.label)) {
              ethandlers.add(etentry.handler_inst);
            }
          }

          branches = ethandlers.toArray();
        } else {
          branches = insn.branchpoints(insn.next);
        }

        if (branches != null) {
          block.succ.ensureCapacity(block.succ.size() + branches.length);

          for (Object element : branches) {
            if (element != null) {
              BasicBlock bb = h2bb.get(element);

              if (bb == null) {
                logger.warn("target of a branch is null");
                logger.debug("" + insn);
              } else {
                block.succ.addElement(bb);
                bb.pred.addElement(block);
              }
            }
          }
        }
      } else if (block.next != null) { // BB ended not with a branch, so just go to next
        block.succ.addElement(block.next);
        block.next.pred.addElement(block);
      }
      block = block.next;
    }

    // One final step, run through exception handlers and mark which
    // basic blocks begin their code
    for (int i = 0; i < ca.exception_table_length; i++) {
      BasicBlock bb = h2bb.get(ca.exception_table[i].handler_inst);
      if (bb == null) {
        logger.warn("No basic block found for" + " start of exception handler code.");
      } else {
        bb.beginException = true;
        ca.exception_table[i].b = bb;
      }
    }
  }

  /*
   * given the list of instructions head, this pulls off the front basic block, terminates it with a null, and returns the
   * next instruction after.
   */
  private static Instruction buildBasicBlock(Instruction head) {
    Instruction insn, next;
    insn = head;
    next = insn.next;

    if (next == null) {
      return insn;
    }

    do {
      if (insn.branches || next.labelled) {
        break;
      } else {
        insn = next;
        next = insn.next;
      }
    } while (next != null);

    return insn;
  }

  /* We only handle simple cases. */
  Map<Instruction, Instruction> jsr2astore = new HashMap<Instruction, Instruction>();
  Map<Instruction, Instruction> astore2ret = new HashMap<Instruction, Instruction>();

  LinkedList<Instruction> jsrorder = new LinkedList<Instruction>();

  /*
   * Eliminate subroutines ( JSR/RET instructions ) by inlining the routine bodies.
   */
  private boolean eliminateJsrRets() {
    Instruction insn = this.sentinel;

    // find the last instruction, for copying blocks.
    while (insn.next != null) {
      insn = insn.next;
    }
    this.lastInstruction = insn;

    HashMap<Instruction, Instruction> todoBlocks = new HashMap<Instruction, Instruction>();
    todoBlocks.put(this.sentinel.next, this.lastInstruction);
    LinkedList<Instruction> todoList = new LinkedList<Instruction>();
    todoList.add(this.sentinel.next);

    while (!todoList.isEmpty()) {
      Instruction firstInsn = todoList.removeFirst();
      Instruction lastInsn = todoBlocks.get(firstInsn);

      jsrorder.clear();
      jsr2astore.clear();
      astore2ret.clear();

      if (findOutmostJsrs(firstInsn, lastInsn)) {
        HashMap<Instruction, Instruction> newblocks = inliningJsrTargets();
        todoBlocks.putAll(newblocks);
        todoList.addAll(newblocks.keySet());
      }
    }

    /* patch exception table and others. */
    {
      method.instructions = this.sentinel.next;

      adjustExceptionTable();
      adjustLineNumberTable();
      adjustBranchTargets();
    }

    // we should prune the code and exception table here.
    // remove any exception handler whose region is in a jsr/ret block.
    // pruneExceptionTable();

    return true;
  }

  // find outmost jsr/ret pairs in a code area, all information is
  // saved in jsr2astore, and astore2ret
  // start : start instruction, inclusively.
  // end : the last instruction, inclusively.
  // return the last instruction encounted ( before end )
  // the caller cleans jsr2astore, astore2ret
  private boolean findOutmostJsrs(Instruction start, Instruction end) {
    // use to put innerJsrs.
    HashSet<Instruction> innerJsrs = new HashSet<Instruction>();
    boolean unusual = false;

    Instruction insn = start;
    do {
      if (insn instanceof Instruction_Jsr || insn instanceof Instruction_Jsr_w) {
        if (innerJsrs.contains(insn)) {
          // skip it
          insn = insn.next;
          continue;
        }

        Instruction astore = ((Instruction_branch) insn).target;
        if (!(astore instanceof Interface_Astore)) {
          unusual = true;
          break;
        }

        Instruction ret = findMatchingRet(astore, insn, innerJsrs);

        /*
         * if (ret == null) { unusual = true; break; }
         */

        jsrorder.addLast(insn);
        jsr2astore.put(insn, astore);
        astore2ret.put(astore, ret);
      }

      insn = insn.next;

    } while (insn != end.next);

    if (unusual) {
      logger.debug("Sorry, I cannot handle this method.");
      return false;
    }

    return true;
  }

  private Instruction findMatchingRet(Instruction astore, Instruction jsr, HashSet<Instruction> innerJsrs) {
    int astorenum = ((Interface_Astore) astore).getLocalNumber();

    Instruction insn = astore.next;
    while (insn != null) {
      if (insn instanceof Instruction_Ret || insn instanceof Instruction_Ret_w) {
        int retnum = ((Interface_OneIntArg) insn).getIntArg();
        if (astorenum == retnum) {
          return insn;
        }
      } else if (insn instanceof Instruction_Jsr || insn instanceof Instruction_Jsr_w) {
        /* adjust the jsr inlining order. */
        innerJsrs.add(insn);
      }

      insn = insn.next;
    }

    return null;
  }

  // make copies of jsr/ret blocks
  // return new blocks
  private HashMap<Instruction, Instruction> inliningJsrTargets() {
    /*
     * for (int i=0, n=jsrorder.size(); i<n; i++) { Instruction jsr = (Instruction)jsrorder.get(i); Instruction astore =
     * (Instruction)jsr2astore.get(jsr); Instruction ret = (Instruction)astore2ret.get(astore);
     * logger.debug("jsr"+jsr.label+"\t" +"as"+astore.label+"\t" +"ret"+ret.label); }
     */
    HashMap<Instruction, Instruction> newblocks = new HashMap<Instruction, Instruction>();

    while (!jsrorder.isEmpty()) {
      Instruction jsr = jsrorder.removeFirst();
      Instruction astore = jsr2astore.get(jsr);

      Instruction ret = astore2ret.get(astore);

      // make a copy of the code, append to the last instruction.
      Instruction newhead = makeCopyOf(astore, ret, jsr.next);

      // jsr is replaced by goto newhead
      // astore has been removed
      // ret is replaced by goto jsr.next
      Instruction_Goto togo = new Instruction_Goto();
      togo.target = newhead;
      newhead.labelled = true;
      togo.label = jsr.label;
      togo.labelled = jsr.labelled;
      togo.prev = jsr.prev;
      togo.next = jsr.next;
      togo.prev.next = togo;
      togo.next.prev = togo;

      replacedInsns.put(jsr, togo);

      // just quick hack
      if (ret != null) {
        newblocks.put(newhead, this.lastInstruction);
      }
    }

    return newblocks;
  }

  /*
   * make a copy of code between from and to exclusively, fixup targets of branch instructions in the code.
   */
  private Instruction makeCopyOf(Instruction astore, Instruction ret, Instruction target) {
    // do a quick hacker for ret == null
    if (ret == null) {
      return astore.next;
    }

    Instruction last = this.lastInstruction;
    Instruction headbefore = last;

    int curlabel = this.lastInstruction.label;

    // mapping from original instructions to new instructions.
    HashMap<Instruction, Instruction> insnmap = new HashMap<Instruction, Instruction>();
    Instruction insn = astore.next;

    while (insn != ret && insn != null) {
      try {
        Instruction newone = (Instruction) insn.clone();

        newone.label = ++curlabel;
        newone.prev = last;
        last.next = newone;
        last = newone;

        insnmap.put(insn, newone);
      } catch (CloneNotSupportedException e) {
        logger.debug("Error !");
      }
      insn = insn.next;
    }

    // replace ret by a goto
    Instruction_Goto togo = new Instruction_Goto();
    togo.target = target;
    target.labelled = true;
    togo.label = ++curlabel;
    last.next = togo;
    togo.prev = last;
    last = togo;

    this.lastInstruction = last;

    // The ret instruction is removed,
    insnmap.put(astore, headbefore.next);
    insnmap.put(ret, togo);

    // fixup targets in new instruction (only in the scope of
    // new instructions).
    // do not forget set target labelled as TRUE
    insn = headbefore.next;
    while (insn != last) {
      if (insn instanceof Instruction_branch) {
        Instruction oldtgt = ((Instruction_branch) insn).target;
        Instruction newtgt = insnmap.get(oldtgt);
        if (newtgt != null) {
          ((Instruction_branch) insn).target = newtgt;
          newtgt.labelled = true;
        }
      } else if (insn instanceof Instruction_Lookupswitch) {
        Instruction_Lookupswitch switchinsn = (Instruction_Lookupswitch) insn;

        Instruction newdefault = insnmap.get(switchinsn.default_inst);
        if (newdefault != null) {
          switchinsn.default_inst = newdefault;
          newdefault.labelled = true;
        }

        for (int i = 0; i < switchinsn.match_insts.length; i++) {
          Instruction newtgt = insnmap.get(switchinsn.match_insts[i]);
          if (newtgt != null) {
            switchinsn.match_insts[i] = newtgt;
            newtgt.labelled = true;
          }
        }
      } else if (insn instanceof Instruction_Tableswitch) {
        Instruction_Tableswitch switchinsn = (Instruction_Tableswitch) insn;

        Instruction newdefault = insnmap.get(switchinsn.default_inst);
        if (newdefault != null) {
          switchinsn.default_inst = newdefault;
          newdefault.labelled = true;
        }

        for (int i = 0; i < switchinsn.jump_insts.length; i++) {
          Instruction newtgt = insnmap.get(switchinsn.jump_insts[i]);
          if (newtgt != null) {
            switchinsn.jump_insts[i] = newtgt;
            newtgt.labelled = true;
          }
        }
      }

      insn = insn.next;
    }

    // do we need to copy a new exception table entry?
    // new exception table has new exception range,
    // and the new exception handler.
    {
      Code_attribute ca = method.locate_code_attribute();

      LinkedList<exception_table_entry> newentries = new LinkedList<exception_table_entry>();

      int orig_start_of_subr = astore.next.originalIndex; // inclusive
      int orig_end_of_subr = ret.originalIndex; // again, inclusive

      for (int i = 0; i < ca.exception_table_length; i++) {
        exception_table_entry etentry = ca.exception_table[i];

        int orig_start_of_trap = etentry.start_pc; // inclusive
        int orig_end_of_trap = etentry.end_pc; // exclusive
        if (orig_start_of_trap < orig_end_of_subr && orig_end_of_trap > orig_start_of_subr) {
          // At least a portion of the cloned subroutine is trapped.
          exception_table_entry newone = new exception_table_entry();
          if (orig_start_of_trap <= orig_start_of_subr) {
            newone.start_inst = headbefore.next;
          } else {
            Instruction ins = insnmap.get(etentry.start_inst);
            if (ins != null) {
              newone.start_inst = insnmap.get(etentry.start_inst);
            } else {
              newone.start_inst = etentry.start_inst;
            }
          }
          if (orig_end_of_trap > orig_end_of_subr) {
            newone.end_inst = null; // Representing the insn after
            // the last instruction in the
            // subr; we need to fix it if
            // we inline another subr.
          } else {
            newone.end_inst = insnmap.get(etentry.end_inst);
          }

          newone.handler_inst = insnmap.get(etentry.handler_inst);
          if (newone.handler_inst == null) {
            newone.handler_inst = etentry.handler_inst;
          }

          // We can leave newone.start_pc == 0 and newone.end_pc == 0.
          // since that cannot overlap the range of any other
          // subroutines that get inlined later.

          newentries.add(newone);
        }
        // Finally, fix up the old entry if its protected area
        // ran to the end of the method we have just lengthened:
        // patch its end marker to be the first
        // instruction in the subroutine we've just inlined.
        if (etentry.end_inst == null) {
          etentry.end_inst = headbefore.next;
        }
      }

      if (newentries.size() > 0) {
        ca.exception_table_length += newentries.size();
        exception_table_entry[] newtable = new exception_table_entry[ca.exception_table_length];
        System.arraycopy(ca.exception_table, 0, newtable, 0, ca.exception_table.length);
        for (int i = 0, j = ca.exception_table.length; i < newentries.size(); i++, j++) {
          newtable[j] = newentries.get(i);
        }

        ca.exception_table = newtable;
      }
    }

    return headbefore.next;
  }

  /* if a jsr/astore/ret is replaced by some other instruction, it will be put on this table. */
  private final Hashtable<Instruction, Instruction_Goto> replacedInsns = new Hashtable<Instruction, Instruction_Goto>();
  /* bootstrap methods table */
  private BootstrapMethods_attribute bootstrap_methods_attribute;

  /* do not forget set the target labelled as TRUE. */
  private void adjustBranchTargets() {
    Instruction insn = this.sentinel.next;
    while (insn != null) {
      if (insn instanceof Instruction_branch) {
        Instruction_branch binsn = (Instruction_branch) insn;
        Instruction newtgt = replacedInsns.get(binsn.target);
        if (newtgt != null) {
          binsn.target = newtgt;
          newtgt.labelled = true;
        }
      } else if (insn instanceof Instruction_Lookupswitch) {
        Instruction_Lookupswitch switchinsn = (Instruction_Lookupswitch) insn;

        Instruction newdefault = replacedInsns.get(switchinsn.default_inst);
        if (newdefault != null) {
          switchinsn.default_inst = newdefault;
          newdefault.labelled = true;
        }

        for (int i = 0; i < switchinsn.npairs; i++) {
          Instruction newtgt = replacedInsns.get(switchinsn.match_insts[i]);
          if (newtgt != null) {
            switchinsn.match_insts[i] = newtgt;
            newtgt.labelled = true;
          }
        }
      } else if (insn instanceof Instruction_Tableswitch) {
        Instruction_Tableswitch switchinsn = (Instruction_Tableswitch) insn;

        Instruction newdefault = replacedInsns.get(switchinsn.default_inst);
        if (newdefault != null) {
          switchinsn.default_inst = newdefault;
          newdefault.labelled = true;
        }

        for (int i = 0; i <= switchinsn.high - switchinsn.low; i++) {
          Instruction newtgt = replacedInsns.get(switchinsn.jump_insts[i]);
          if (newtgt != null) {
            switchinsn.jump_insts[i] = newtgt;
            newtgt.labelled = true;
          }
        }
      }

      insn = insn.next;
    }
  }

  private void adjustExceptionTable() {
    Code_attribute codeAttribute = method.locate_code_attribute();

    for (int i = 0; i < codeAttribute.exception_table_length; i++) {
      exception_table_entry entry = codeAttribute.exception_table[i];

      Instruction oldinsn = entry.start_inst;
      Instruction newinsn = replacedInsns.get(oldinsn);
      if (newinsn != null) {
        entry.start_inst = newinsn;
      }

      oldinsn = entry.end_inst;
      if (entry.end_inst != null) {
        newinsn = replacedInsns.get(oldinsn);
        if (newinsn != null) {
          entry.end_inst = newinsn;
        }
      }

      oldinsn = entry.handler_inst;
      newinsn = replacedInsns.get(oldinsn);
      if (newinsn != null) {
        entry.handler_inst = newinsn;
      }
    }
  }

  private void adjustLineNumberTable() {
    if (!myOptions.keep_line_number()) {
      return;
    }
    if (method.code_attr == null) {
      return;
    }

    attribute_info[] attributes = method.code_attr.attributes;

    for (attribute_info element : attributes) {
      if (element instanceof LineNumberTable_attribute) {
        LineNumberTable_attribute lntattr = (LineNumberTable_attribute) element;
        for (line_number_table_entry element0 : lntattr.line_number_table) {
          Instruction oldinst = element0.start_inst;
          Instruction newinst = replacedInsns.get(oldinst);
          if (newinst != null) {
            element0.start_inst = newinst;
          }
        }
      }
    }
  }

  /**
   * Reconstructs the instruction stream by appending the Instruction lists associated with each basic block.
   * <p>
   * Note that this joins up the basic block Instruction lists, and so they will no longer end with <i>null</i> after this.
   *
   * @return the head of the list of instructions.
   */
  public Instruction reconstructInstructions() {
    if (cfg != null) {
      return cfg.head;
    } else {
      return null;
    }
  }

  /**
   * myMain entry point for converting list of Instructions to Jimple statements; performs flow analysis, constructs Jimple
   * statements, and fixes jumps.
   *
   * @param constant_pool
   *          constant pool of ClassFile.
   * @param this_class
   *          constant pool index of the CONSTANT_Class_info object for this' class.
   * @param bootstrap_methods_attribute
   * @return <i>true</i> if all ok, <i>false</i> if there was an error.
   * @see Stmt
   */
  public boolean jimplify(cp_info constant_pool[], int this_class, BootstrapMethods_attribute bootstrap_methods_attribute,
      JimpleBody listBody) {
    this.bootstrap_methods_attribute = bootstrap_methods_attribute;

    Chain<Unit> units = listBody.getUnits();

    this.listBody = listBody;
    this.units = units;
    instructionToFirstStmt = new HashMap<Instruction, Stmt>();
    instructionToLastStmt = new HashMap<Instruction, Stmt>();

    jmethod = listBody.getMethod();
    cm = myScene;

    // TypeArray.setClassManager(cm);
    // TypeStack.setClassManager(cm);

    Set<Local> initialLocals = new ArraySet<Local>();

    List<Type> parameterTypes = jmethod.getParameterTypes();

    // Initialize nameToLocal which is an index*Type->Local map, which is used
    // to determine local in bytecode references.
    {
      Code_attribute ca = method.locate_code_attribute();
      LocalVariableTable_attribute la = ca.findLocalVariableTable();
      LocalVariableTypeTable_attribute lt = ca.findLocalVariableTypeTable();

      myCoffiUtil.bodySetup(la, lt, constant_pool);

      boolean isStatic = Modifier.isStatic(jmethod.getModifiers());

      int currentLocalIndex = 0;

      // Initialize the 'this' variable
      {
        if (!isStatic) {
          Local local = myCoffiUtil.getLocalForParameter(listBody, currentLocalIndex);
          currentLocalIndex++;

          units.add(myJimple.newIdentityStmt(local, myJimple.newThisRef(jmethod.getDeclaringClass().getType())));
        }
      }

      // Initialize parameters
      {
        Iterator<Type> typeIt = parameterTypes.iterator();
        int argCount = 0;

        while (typeIt.hasNext()) {
          Local local = myCoffiUtil.getLocalForParameter(listBody, currentLocalIndex);
          Type type = typeIt.next();
          initialLocals.add(local);

          units.add(myJimple.newIdentityStmt(local, myJimple.newParameterRef(type, argCount)));

          if (type.equals(myScene.getPrimTypeCollector().getDoubleType())
              || type.equals(myScene.getPrimTypeCollector().getLongType())) {
            currentLocalIndex += 2;
          } else {
            currentLocalIndex += 1;
          }

          argCount++;
        }
      }

      myCoffiUtil.resetEasyNames();
    }

    jimplify(constant_pool, this_class);

    return true;
  }

  private void buildInsnCFGfromBBCFG() {
    BasicBlock block = cfg;

    while (block != null) {
      Instruction insn = block.head;
      while (insn != block.tail) {
        Instruction[] succs = new Instruction[1];
        succs[0] = insn.next;
        insn.succs = succs;
        insn = insn.next;
      }

      {
        // The successors are the ones from the basic block.
        Vector<BasicBlock> bsucc = block.succ;
        int size = bsucc.size();
        Instruction[] succs = new Instruction[size];

        for (int i = 0; i < size; i++) {
          succs[i] = bsucc.elementAt(i).head;
        }
        insn.succs = succs;
      }

      block = block.next;
    }
  }

  /**
   * myMain entry point for converting list of Instructions to Jimple statements; performs flow analysis, constructs Jimple
   * statements, and fixes jumps.
   *
   * @param constant_pool
   *          constant pool of ClassFile.
   * @param this_class
   *          constant pool index of the CONSTANT_Class_info object for this' class. if <i>true</i> semantic stacks will be
   *          deleted after the process is complete.
   * @return <i>true</i> if all ok, <i>false</i> if there was an error.
   * @see CFG#jimplify(cp_info[], int)
   * @see Stmt
   */
  void jimplify(cp_info constant_pool[], int this_class) {
    Code_attribute codeAttribute = method.locate_code_attribute();
    Set<Instruction> handlerInstructions = new ArraySet<Instruction>();

    Map<Instruction, SootClass> handlerInstructionToException = new HashMap<Instruction, SootClass>();
    Map<Instruction, TypeStack> instructionToTypeStack;
    Map<Instruction, TypeStack> instructionToPostTypeStack;

    {
      // build graph in
      buildInsnCFGfromBBCFG();

      // Put in successors due to exception handlers
      {
        for (int i = 0; i < codeAttribute.exception_table_length; i++) {
          Instruction startIns = codeAttribute.exception_table[i].start_inst;
          Instruction endIns = codeAttribute.exception_table[i].end_inst;
          Instruction handlerIns = codeAttribute.exception_table[i].handler_inst;

          handlerInstructions.add(handlerIns);

          // Determine exception to catch
          {
            int catchType = codeAttribute.exception_table[i].catch_type;

            SootClass exception;

            if (catchType != 0) {
              CONSTANT_Class_info classinfo = (CONSTANT_Class_info) constant_pool[catchType];

              String name = ((CONSTANT_Utf8_info) (constant_pool[classinfo.name_index])).convert();
              name = name.replace('/', '.');

              exception = cm.getSootClass(name);
            } else {
              exception = cm.getSootClass("java.lang.Throwable");
            }

            handlerInstructionToException.put(handlerIns, exception);
          }

          if (startIns == endIns) {
            throw new RuntimeException("Empty catch range for exception handler");
          }

          Instruction ins = startIns;

          for (;;) {
            Instruction[] succs = ins.succs;
            Instruction[] newsuccs = new Instruction[succs.length + 1];

            System.arraycopy(succs, 0, newsuccs, 0, succs.length);

            newsuccs[succs.length] = handlerIns;
            ins.succs = newsuccs;

            ins = ins.next;
            if (ins == endIns || ins == null) {
              break;
            }
          }
        }
      }
    }

    Set<Instruction> reachableInstructions = new HashSet<Instruction>();

    // Mark all the reachable instructions
    {
      LinkedList<Instruction> instructionsToVisit = new LinkedList<Instruction>();

      reachableInstructions.add(firstInstruction);
      instructionsToVisit.addLast(firstInstruction);

      while (!instructionsToVisit.isEmpty()) {
        Instruction ins = instructionsToVisit.removeFirst();

        Instruction[] succs = ins.succs;

        for (Instruction succ : succs) {
          if (!reachableInstructions.contains(succ)) {
            reachableInstructions.add(succ);
            instructionsToVisit.addLast(succ);
          }
        }
      }
    }

    /*
     * // Check to see if any instruction is unmarked. { BasicBlock b = cfg;
     *
     * while(b != null) { Instruction ins = b.head;
     *
     * while(ins != null) { if(!reachableInstructions.contains(ins)) throw new
     * RuntimeException("Method to jimplify contains unreachable code!  (not handled for now)");
     *
     * ins = ins.next; }
     *
     * b = b.next; } }
     */

    // Perform the flow analysis, and build up instructionToTypeStack and instructionToLocalArray
    {
      instructionToTypeStack = new HashMap<Instruction, TypeStack>();
      instructionToPostTypeStack = new HashMap<Instruction, TypeStack>();

      Set<Instruction> visitedInstructions = new HashSet<Instruction>();
      List<Instruction> changedInstructions = new ArrayList<Instruction>();

      TypeStack initialTypeStack;

      // Build up initial type stack and initial local array (for the first instruction)
      {
        initialTypeStack = TypeStack.v();
        // the empty stack with nothing on it.
      }

      // Get the loop cranked up.
      {
        instructionToTypeStack.put(firstInstruction, initialTypeStack);

        visitedInstructions.add(firstInstruction);
        changedInstructions.add(firstInstruction);
      }

      {
        while (!changedInstructions.isEmpty()) {
          Instruction ins = changedInstructions.get(0);

          changedInstructions.remove(0);

          OutFlow ret = processFlow(ins, instructionToTypeStack.get(ins), constant_pool);

          instructionToPostTypeStack.put(ins, ret.typeStack);

          Instruction[] successors = ins.succs;

          for (Instruction s : successors) {
            if (!visitedInstructions.contains(s)) {
              // Special case for the first time visiting.

              if (handlerInstructions.contains(s)) {
                TypeStack exceptionTypeStack
                    = (TypeStack.v()).push(RefType.v(handlerInstructionToException.get(s).getName(), myScene));

                instructionToTypeStack.put(s, exceptionTypeStack);
              } else {
                instructionToTypeStack.put(s, ret.typeStack);
              }

              visitedInstructions.add(s);
              changedInstructions.add(s);

              // logger.debug("adding successor: " + s);
            } else {
              // logger.debug("considering successor: " + s);

              TypeStack newTypeStack, oldTypeStack = instructionToTypeStack.get(s);

              if (handlerInstructions.contains(s)) {
                // The type stack for an instruction handler should always be that of
                // single object on the stack.

                TypeStack exceptionTypeStack
                    = (TypeStack.v()).push(RefType.v(handlerInstructionToException.get(s).getName(), myScene));

                newTypeStack = exceptionTypeStack;
              } else {
                try {
                  newTypeStack = ret.typeStack.merge(oldTypeStack, myScene);
                } catch (RuntimeException re) {
                  logger.debug("Considering " + s);
                  throw re;
                }
              }
              if (!newTypeStack.equals(oldTypeStack)) {
                changedInstructions.add(s);
                // logger.debug("requires a revisit: " + s);
              }

              instructionToTypeStack.put(s, newTypeStack);
            }
          }
        }
      }
    }

    // logger.debug("Producing Jimple code...");

    // Jimplify each statement
    {
      BasicBlock b = cfg;

      while (b != null) {
        Instruction ins = b.head;
        b.statements = new ArrayList<Stmt>();

        List<Stmt> blockStatements = b.statements;

        for (;;) {
          List<Stmt> statementsForIns = new ArrayList<Stmt>();

          if (reachableInstructions.contains(ins)) {
            generateJimple(ins, instructionToTypeStack.get(ins), instructionToPostTypeStack.get(ins), constant_pool,
                statementsForIns, b);
          } else {
            statementsForIns.add(myJimple.newNopStmt());
          }

          if (!statementsForIns.isEmpty()) {
            for (int i = 0; i < statementsForIns.size(); i++) {
              units.add(statementsForIns.get(i));
              blockStatements.add(statementsForIns.get(i));
            }

            instructionToFirstStmt.put(ins, statementsForIns.get(0));
            instructionToLastStmt.put(ins, statementsForIns.get(statementsForIns.size() - 1));
          }

          if (ins == b.tail) {
            break;
          }

          ins = ins.next;
        }

        b = b.next;
      }
    }

    jimpleTargetFixup(); // fix up jump targets

    /*
     * // Print out basic blocks { BasicBlock b = cfg;
     *
     * logger.debug("Basic blocks for: " + jmethod.getName());
     *
     * while(b != null) { Instruction ins = b.head;
     *
     *
     *
     * while(ins != null) { logger.debug(""+ins.toString()); ins = ins.next; }
     *
     * b = b.next; } }
     */

    // Insert beginCatch/endCatch statements for exception handling
    {
      Map<Stmt, Stmt> targetToHandler = new HashMap<Stmt, Stmt>();

      for (int i = 0; i < codeAttribute.exception_table_length; i++) {
        Instruction startIns = codeAttribute.exception_table[i].start_inst;
        Instruction endIns = codeAttribute.exception_table[i].end_inst;
        Instruction targetIns = codeAttribute.exception_table[i].handler_inst;

        if (!instructionToFirstStmt.containsKey(startIns)
            || (endIns != null && (!instructionToLastStmt.containsKey(endIns)))) {
          throw new RuntimeException("Exception range does not coincide with jimple instructions");
        }

        if (!instructionToFirstStmt.containsKey(targetIns)) {
          throw new RuntimeException("Exception handler does not coincide with jimple instruction");
        }

        SootClass exception;

        // Determine exception to catch
        {
          int catchType = codeAttribute.exception_table[i].catch_type;
          if (catchType != 0) {
            CONSTANT_Class_info classinfo = (CONSTANT_Class_info) constant_pool[catchType];

            String name = ((CONSTANT_Utf8_info) (constant_pool[classinfo.name_index])).convert();
            name = name.replace('/', '.');
            exception = cm.getSootClass(name);
          } else {
            exception = cm.getSootClass("java.lang.Throwable");
          }
        }

        Stmt newTarget;

        // Insert assignment of exception
        {
          Stmt firstTargetStmt = instructionToFirstStmt.get(targetIns);

          if (targetToHandler.containsKey(firstTargetStmt)) {
            newTarget = targetToHandler.get(firstTargetStmt);
          } else {
            Local local = myCoffiUtil.getLocalCreatingIfNecessary(listBody, "$stack0",
                myScene.getPrimTypeCollector().getUnknownType());

            newTarget = myJimple.newIdentityStmt(local, myJimple.newCaughtExceptionRef());

            // changed to account for catch blocks which are also part of normal control flow
            // units.insertBefore(newTarget, firstTargetStmt);
            ((PatchingChain<Unit>) units).insertBeforeNoRedirect(newTarget, firstTargetStmt);

            targetToHandler.put(firstTargetStmt, newTarget);
            if (units.getFirst() != newTarget) {
              Unit prev = (Unit) units.getPredOf(newTarget);
              if (prev != null && prev.fallsThrough()) {
                units.insertAfter(myJimple.newGotoStmt(firstTargetStmt), prev);
              }
            }
          }
        }

        // Insert trap
        {
          Stmt firstStmt = instructionToFirstStmt.get(startIns);
          Stmt afterEndStmt;
          if (endIns == null) {
            // A kludge which isn't really correct, but
            // gets us closer to correctness (until we
            // clean up the rest of Soot to properly
            // represent Traps which extend to the end
            // of a method): if the protected code extends
            // to the end of the method, use the last Stmt
            // as the endUnit of the Trap, even though
            // that will leave the last unit outside
            // the protected area.
            afterEndStmt = (Stmt) units.getLast();
          } else {
            afterEndStmt = instructionToLastStmt.get(endIns);
            IdentityStmt catchStart = (IdentityStmt) targetToHandler.get(afterEndStmt);
            // (Cast to IdentityStmt as an assertion check.)
            if (catchStart != null) {
              // The protected region extends to the beginning of an
              // exception handler, so we need to reset afterEndStmt
              // to the identity statement which we have inserted
              // before the old afterEndStmt.
              if (catchStart != units.getPredOf(afterEndStmt)) {
                throw new IllegalStateException("Assertion failure: catchStart != pred of afterEndStmt");
              }
              afterEndStmt = catchStart;
            }
          }

          Trap trap = myJimple.newTrap(exception, firstStmt, afterEndStmt, newTarget);
          listBody.getTraps().add(trap);
        }
      }
    }

    /* convert line number table to tags attached to statements */
    if (myOptions.keep_line_number()) {
      HashMap<Stmt, Tag> stmtstags = new HashMap<Stmt, Tag>();
      LinkedList<Stmt> startstmts = new LinkedList<Stmt>();

      attribute_info[] attrs = codeAttribute.attributes;
      for (attribute_info element : attrs) {
        if (element instanceof LineNumberTable_attribute) {
          LineNumberTable_attribute lntattr = (LineNumberTable_attribute) element;
          for (line_number_table_entry element0 : lntattr.line_number_table) {
            Stmt start_stmt = instructionToFirstStmt.get(element0.start_inst);

            if (start_stmt != null) {
              LineNumberTag lntag = new LineNumberTag(element0.line_number);
              stmtstags.put(start_stmt, lntag);
              startstmts.add(start_stmt);
            }
          }
        }
      }

      /*
       * if the predecessor of a statement is a caughtexcetionref, give it the tag of its successor
       */
      for (Iterator<Stmt> stmtIt = new ArrayList<Stmt>(stmtstags.keySet()).iterator(); stmtIt.hasNext();) {
        final Stmt stmt = stmtIt.next();
        Stmt pred = stmt;
        Tag tag = stmtstags.get(stmt);
        while (true) {
          pred = (Stmt) units.getPredOf(pred);
          if (pred == null) {
            break;
          }
          if (!(pred instanceof IdentityStmt)) {
            break;
          }
          stmtstags.put(pred, tag);
          pred.addTag(tag);
        }
      }

      /* attach line number tag to each statement. */
      for (int i = 0; i < startstmts.size(); i++) {
        Stmt stmt = startstmts.get(i);
        Tag tag = stmtstags.get(stmt);

        stmt.addTag(tag);

        stmt = (Stmt) units.getSuccOf(stmt);
        while (stmt != null && !stmtstags.containsKey(stmt)) {
          stmt.addTag(tag);
          stmt = (Stmt) units.getSuccOf(stmt);
        }
      }
    }
  }

  private Type byteCodeTypeOf(Type type) {
    if (type.equals(myScene.getPrimTypeCollector().getShortType())
        || type.equals(myScene.getPrimTypeCollector().getCharType())
        || type.equals(myScene.getPrimTypeCollector().getByteType())
        || type.equals(myScene.getPrimTypeCollector().getBooleanType())) {
      return myScene.getPrimTypeCollector().getIntType();
    } else {
      return type;
    }
  }

  OutFlow processFlow(Instruction ins, TypeStack typeStack, cp_info[] constant_pool) {
    int x;
    x = ((ins.code)) & 0xff;

    switch (x) {
      case ByteCode.BIPUSH:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.SIPUSH:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.LDC1:
        return processCPEntry(constant_pool, ((Instruction_Ldc1) ins).arg_b, typeStack, jmethod);

      case ByteCode.LDC2:
      case ByteCode.LDC2W:
        return processCPEntry(constant_pool, ((Instruction_intindex) ins).arg_i, typeStack, jmethod);

      case ByteCode.ACONST_NULL:
        typeStack = typeStack.push(RefType.v("java.lang.Object", myScene));
        break;

      case ByteCode.ICONST_M1:
      case ByteCode.ICONST_0:
      case ByteCode.ICONST_1:
      case ByteCode.ICONST_2:
      case ByteCode.ICONST_3:
      case ByteCode.ICONST_4:
      case ByteCode.ICONST_5:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;
      case ByteCode.LCONST_0:
      case ByteCode.LCONST_1:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;
      case ByteCode.FCONST_0:
      case ByteCode.FCONST_1:
      case ByteCode.FCONST_2:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;
      case ByteCode.DCONST_0:
      case ByteCode.DCONST_1:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;
      case ByteCode.ILOAD:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.FLOAD:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.ALOAD:
        typeStack = typeStack.push(RefType.v("java.lang.Object", myScene));
        // this is highly imprecise
        break;

      case ByteCode.DLOAD:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;

      case ByteCode.LLOAD:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.ILOAD_0:
      case ByteCode.ILOAD_1:
      case ByteCode.ILOAD_2:
      case ByteCode.ILOAD_3:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.FLOAD_0:
      case ByteCode.FLOAD_1:
      case ByteCode.FLOAD_2:
      case ByteCode.FLOAD_3:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.ALOAD_0:
      case ByteCode.ALOAD_1:
      case ByteCode.ALOAD_2:
      case ByteCode.ALOAD_3:
        typeStack = typeStack.push(RefType.v("java.lang.Object", myScene));
        // this is highly imprecise
        break;

      case ByteCode.LLOAD_0:
      case ByteCode.LLOAD_1:
      case ByteCode.LLOAD_2:
      case ByteCode.LLOAD_3:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.DLOAD_0:
      case ByteCode.DLOAD_1:
      case ByteCode.DLOAD_2:
      case ByteCode.DLOAD_3:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;

      case ByteCode.ISTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.FSTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.ASTORE:
        typeStack = typeStack.pop();
        break;

      case ByteCode.LSTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        break;

      case ByteCode.DSTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        break;

      case ByteCode.ISTORE_0:
      case ByteCode.ISTORE_1:
      case ByteCode.ISTORE_2:
      case ByteCode.ISTORE_3:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.FSTORE_0:
      case ByteCode.FSTORE_1:
      case ByteCode.FSTORE_2:
      case ByteCode.FSTORE_3:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.ASTORE_0:
      case ByteCode.ASTORE_1:
      case ByteCode.ASTORE_2:
      case ByteCode.ASTORE_3:
        if (!(typeStack.top() instanceof StmtAddressType) && !(typeStack.top() instanceof RefType)
            && !(typeStack.top() instanceof ArrayType)) {
          throw new RuntimeException("Astore failed, invalid stack type: " + typeStack.top());
        }

        typeStack = typeStack.pop();
        break;

      case ByteCode.LSTORE_0:
      case ByteCode.LSTORE_1:
      case ByteCode.LSTORE_2:
      case ByteCode.LSTORE_3:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        break;

      case ByteCode.DSTORE_0:
      case ByteCode.DSTORE_1:
      case ByteCode.DSTORE_2:
      case ByteCode.DSTORE_3:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        break;

      case ByteCode.IINC:
        break;

      case ByteCode.WIDE:
        throw new RuntimeException("Wide instruction should not be encountered");
        // break;

      case ByteCode.NEWARRAY: {
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        Type baseType = jimpleTypeOfAtype(((Instruction_Newarray) ins).atype);

        typeStack = typeStack.push(ArrayType.v(baseType, 1, myScene));
        break;
      }

      case ByteCode.ANEWARRAY: {
        CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[((Instruction_Anewarray) ins).arg_i];

        String name = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();
        name = name.replace('/', '.');

        Type baseType;

        if (name.startsWith("[")) {
          String baseName = getClassName(constant_pool, ((Instruction_Anewarray) ins).arg_i);
          baseType = myCoffiUtil.jimpleTypeOfFieldDescriptor(baseName);
        } else {
          baseType = RefType.v(name, myScene);
        }

        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = typeStack.push(baseType.makeArrayType());
        break;
      }

      case ByteCode.MULTIANEWARRAY: {
        int bdims = (((Instruction_Multianewarray) ins).dims);

        CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[((Instruction_Multianewarray) ins).arg_i];

        String arrayDescriptor = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();

        ArrayType arrayType = (ArrayType) myCoffiUtil.jimpleTypeOfFieldDescriptor(arrayDescriptor);

        for (int j = 0; j < bdims; j++) {
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        }

        typeStack = typeStack.push(arrayType);
        break;
      }

      case ByteCode.ARRAYLENGTH:
        typeStack = popSafeRefType(typeStack);
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.IALOAD:
      case ByteCode.BALOAD:
      case ByteCode.CALOAD:
      case ByteCode.SALOAD:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;
      case ByteCode.FALOAD:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = popSafeRefType(typeStack);
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.AALOAD: {

        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());

        if (typeStack.top() instanceof ArrayType) {
          ArrayType arrayType = (ArrayType) typeStack.top();
          typeStack = popSafeRefType(typeStack);

          if (arrayType.numDimensions == 1) {
            typeStack = typeStack.push(arrayType.baseType);
          } else {
            typeStack = typeStack.push(ArrayType.v(arrayType.baseType, arrayType.numDimensions - 1, myScene));
          }
        } else {
          // it's a null object

          typeStack = popSafeRefType(typeStack);

          typeStack = typeStack.push(RefType.v("java.lang.Object", myScene));
        }

        break;
      }
      case ByteCode.LALOAD:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.DALOAD:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;

      case ByteCode.IASTORE:
      case ByteCode.BASTORE:
      case ByteCode.CASTORE:
      case ByteCode.SASTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.AASTORE:
        typeStack = popSafeRefType(typeStack);
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.FASTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.LASTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.DASTORE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.NOP:
        break;

      case ByteCode.POP:
        typeStack = typeStack.pop();
        break;

      case ByteCode.POP2:
        typeStack = typeStack.pop();
        typeStack = typeStack.pop();
        break;

      case ByteCode.DUP:
        typeStack = typeStack.push(typeStack.top());
        break;

      case ByteCode.DUP2: {
        Type topType = typeStack.get(typeStack.topIndex()), secondType = typeStack.get(typeStack.topIndex() - 1);
        typeStack = (typeStack.push(secondType)).push(topType);
        break;
      }

      case ByteCode.DUP_X1: {
        Type topType = typeStack.get(typeStack.topIndex()), secondType = typeStack.get(typeStack.topIndex() - 1);

        typeStack = typeStack.pop().pop();

        typeStack = typeStack.push(topType).push(secondType).push(topType);
        break;
      }

      case ByteCode.DUP_X2: {
        Type topType = typeStack.get(typeStack.topIndex()), secondType = typeStack.get(typeStack.topIndex() - 1),
            thirdType = typeStack.get(typeStack.topIndex() - 2);

        typeStack = typeStack.pop().pop().pop();

        typeStack = typeStack.push(topType).push(thirdType).push(secondType).push(topType);
        break;
      }

      case ByteCode.DUP2_X1: {
        Type topType = typeStack.get(typeStack.topIndex()), secondType = typeStack.get(typeStack.topIndex() - 1),
            thirdType = typeStack.get(typeStack.topIndex() - 2);

        typeStack = typeStack.pop().pop().pop();

        typeStack = typeStack.push(secondType).push(topType).push(thirdType).push(secondType).push(topType);
        break;
      }

      case ByteCode.DUP2_X2: {
        Type topType = typeStack.get(typeStack.topIndex()), secondType = typeStack.get(typeStack.topIndex() - 1),
            thirdType = typeStack.get(typeStack.topIndex() - 2), fourthType = typeStack.get(typeStack.topIndex() - 3);

        typeStack = typeStack.pop().pop().pop().pop();

        typeStack = typeStack.push(secondType).push(topType).push(fourthType).push(thirdType).push(secondType).push(topType);
        break;
      }

      case ByteCode.SWAP: {
        Type topType = typeStack.top();

        typeStack = typeStack.pop();

        Type secondType = typeStack.top();

        typeStack = typeStack.pop();

        typeStack = typeStack.push(topType);
        typeStack = typeStack.push(secondType);
        break;
      }

      case ByteCode.IADD:
      case ByteCode.ISUB:
      case ByteCode.IMUL:
      case ByteCode.IDIV:
      case ByteCode.IREM:
      case ByteCode.ISHL:
      case ByteCode.ISHR:
      case ByteCode.IUSHR:
      case ByteCode.IAND:
      case ByteCode.IOR:
      case ByteCode.IXOR:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.LUSHR:
      case ByteCode.LSHR:
      case ByteCode.LSHL:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.LREM:
      case ByteCode.LDIV:
      case ByteCode.LMUL:
      case ByteCode.LSUB:
      case ByteCode.LADD:
      case ByteCode.LAND:
      case ByteCode.LOR:
      case ByteCode.LXOR:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.FREM:
      case ByteCode.FDIV:
      case ByteCode.FMUL:
      case ByteCode.FSUB:
      case ByteCode.FADD:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.DREM:
      case ByteCode.DDIV:
      case ByteCode.DMUL:
      case ByteCode.DSUB:
      case ByteCode.DADD:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;

      case ByteCode.INEG:
      case ByteCode.LNEG:
      case ByteCode.FNEG:
      case ByteCode.DNEG:
        // Doesn't check to see if the required types are on the stack, but it should
        // if it wanted to be safe.
        break;

      case ByteCode.I2L:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.I2F:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.I2D:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;

      case ByteCode.L2I:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.L2F:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.L2D:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;

      case ByteCode.F2I:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.F2L:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.F2D:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        break;

      case ByteCode.D2I:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.D2L:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        break;

      case ByteCode.D2F:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.INT2BYTE:
        break;
      case ByteCode.INT2CHAR:
        break;
      case ByteCode.INT2SHORT:
        break;

      case ByteCode.IFEQ:
      case ByteCode.IFGT:
      case ByteCode.IFLT:
      case ByteCode.IFLE:
      case ByteCode.IFNE:
      case ByteCode.IFGE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.IFNULL:
      case ByteCode.IFNONNULL:
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.IF_ICMPEQ:
      case ByteCode.IF_ICMPLT:
      case ByteCode.IF_ICMPLE:
      case ByteCode.IF_ICMPNE:
      case ByteCode.IF_ICMPGT:
      case ByteCode.IF_ICMPGE:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.LCMP:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.FCMPL:
      case ByteCode.FCMPG:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.DCMPL:
      case ByteCode.DCMPG:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.IF_ACMPEQ:
      case ByteCode.IF_ACMPNE:
        typeStack = popSafeRefType(typeStack);
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.GOTO:
      case ByteCode.GOTO_W:
        break;

      case ByteCode.JSR:
      case ByteCode.JSR_W:
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getStmtAddressType());
        break;

      case ByteCode.RET:
        break;

      case ByteCode.RET_W:
        break;

      case ByteCode.RETURN:
        break;

      case ByteCode.IRETURN:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.FRETURN:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getFloatType());
        break;

      case ByteCode.ARETURN:
        typeStack = popSafeRefType(typeStack);
        break;

      case ByteCode.DRETURN:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        break;

      case ByteCode.LRETURN:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        break;

      case ByteCode.BREAKPOINT:
        break;

      case ByteCode.TABLESWITCH:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.LOOKUPSWITCH:
        typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getIntType());
        break;

      case ByteCode.PUTFIELD: {
        Type type = byteCodeTypeOf(jimpleTypeOfFieldInFieldRef(cm, constant_pool, ((Instruction_Putfield) ins).arg_i));

        if (type.equals(myScene.getPrimTypeCollector().getDoubleType())) {
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        } else if (type.equals(myScene.getPrimTypeCollector().getLongType())) {
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        } else if (type instanceof RefType) {
          typeStack = popSafeRefType(typeStack);
        } else {
          typeStack = popSafe(typeStack, type);
        }

        typeStack = popSafeRefType(typeStack);
        break;
      }

      case ByteCode.GETFIELD: {
        Type type = byteCodeTypeOf(jimpleTypeOfFieldInFieldRef(cm, constant_pool, ((Instruction_Getfield) ins).arg_i));

        typeStack = popSafeRefType(typeStack);

        if (type.equals(myScene.getPrimTypeCollector().getDoubleType())) {
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        } else if (type.equals(myScene.getPrimTypeCollector().getLongType())) {
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        } else {
          typeStack = typeStack.push(type);
        }
        break;
      }

      case ByteCode.PUTSTATIC: {
        Type type = byteCodeTypeOf(jimpleTypeOfFieldInFieldRef(cm, constant_pool, ((Instruction_Putstatic) ins).arg_i));

        if (type.equals(myScene.getPrimTypeCollector().getDoubleType())) {
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
        } else if (type.equals(myScene.getPrimTypeCollector().getLongType())) {
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
          typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());
        } else if (type instanceof RefType) {
          typeStack = popSafeRefType(typeStack);
        } else {
          typeStack = popSafe(typeStack, type);
        }

        break;
      }

      case ByteCode.GETSTATIC: {
        Type type = byteCodeTypeOf(jimpleTypeOfFieldInFieldRef(cm, constant_pool, ((Instruction_Getstatic) ins).arg_i));

        if (type.equals(myScene.getPrimTypeCollector().getDoubleType())) {
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
        } else if (type.equals(myScene.getPrimTypeCollector().getLongType())) {
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
          typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
        } else {
          typeStack = typeStack.push(type);
        }
        break;
      }

      case ByteCode.INVOKEDYNAMIC: {
        Instruction_Invokedynamic iv = (Instruction_Invokedynamic) ins;
        CONSTANT_InvokeDynamic_info iv_info = (CONSTANT_InvokeDynamic_info) constant_pool[iv.invoke_dynamic_index];
        int args = cp_info.countParams(constant_pool, iv_info.name_and_type_index);
        Type returnType = byteCodeTypeOf(jimpleReturnTypeOfNameAndType(cm, constant_pool, iv_info.name_and_type_index));

        // pop off parameters.
        for (int j = args - 1; j >= 0; j--) {
          if (typeStack.top().equals(myScene.getPrimTypeCollector().getLong2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());

          } else if (typeStack.top().equals(myScene.getPrimTypeCollector().getDouble2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
          } else {
            typeStack = popSafe(typeStack, typeStack.top());
          }
        }

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          typeStack = smartPush(typeStack, returnType);
        }
        break;
      }

      case ByteCode.INVOKEVIRTUAL: {
        Instruction_Invokevirtual iv = (Instruction_Invokevirtual) ins;
        int args = cp_info.countParams(constant_pool, iv.arg_i);
        Type returnType = byteCodeTypeOf(jimpleReturnTypeOfMethodRef(cm, constant_pool, iv.arg_i));

        // pop off parameters.
        for (int j = args - 1; j >= 0; j--) {
          if (typeStack.top().equals(myScene.getPrimTypeCollector().getLong2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());

          } else if (typeStack.top().equals(myScene.getPrimTypeCollector().getDouble2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
          } else {
            typeStack = popSafe(typeStack, typeStack.top());
          }
        }

        typeStack = popSafeRefType(typeStack);

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          typeStack = smartPush(typeStack, returnType);
        }
        break;
      }

      case ByteCode.INVOKENONVIRTUAL: {
        Instruction_Invokenonvirtual iv = (Instruction_Invokenonvirtual) ins;
        int args = cp_info.countParams(constant_pool, iv.arg_i);
        Type returnType = byteCodeTypeOf(jimpleReturnTypeOfMethodRef(cm, constant_pool, iv.arg_i));

        // pop off parameters.
        for (int j = args - 1; j >= 0; j--) {
          if (typeStack.top().equals(myScene.getPrimTypeCollector().getLong2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());

          } else if (typeStack.top().equals(myScene.getPrimTypeCollector().getDouble2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
          } else {
            typeStack = popSafe(typeStack, typeStack.top());
          }
        }

        typeStack = popSafeRefType(typeStack);

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          typeStack = smartPush(typeStack, returnType);
        }
        break;
      }

      case ByteCode.INVOKESTATIC: {
        Instruction_Invokestatic iv = (Instruction_Invokestatic) ins;
        int args = cp_info.countParams(constant_pool, iv.arg_i);
        Type returnType = byteCodeTypeOf(jimpleReturnTypeOfMethodRef(cm, constant_pool, iv.arg_i));

        // pop off parameters.
        for (int j = args - 1; j >= 0; j--) {
          if (typeStack.top().equals(myScene.getPrimTypeCollector().getLong2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());

          } else if (typeStack.top().equals(myScene.getPrimTypeCollector().getDouble2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
          } else {
            typeStack = popSafe(typeStack, typeStack.top());
          }
        }

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          typeStack = smartPush(typeStack, returnType);
        }
        break;
      }

      case ByteCode.INVOKEINTERFACE: {
        Instruction_Invokeinterface iv = (Instruction_Invokeinterface) ins;
        int args = cp_info.countParams(constant_pool, iv.arg_i);
        Type returnType = byteCodeTypeOf(jimpleReturnTypeOfInterfaceMethodRef(cm, constant_pool, iv.arg_i));

        // pop off parameters.
        for (int j = args - 1; j >= 0; j--) {
          if (typeStack.top().equals(myScene.getPrimTypeCollector().getLong2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLong2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getLongType());

          } else if (typeStack.top().equals(myScene.getPrimTypeCollector().getDouble2ndHalfType())) {
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDouble2ndHalfType());
            typeStack = popSafe(typeStack, myScene.getPrimTypeCollector().getDoubleType());
          } else {
            typeStack = popSafe(typeStack, typeStack.top());
          }
        }

        typeStack = popSafeRefType(typeStack);

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          typeStack = smartPush(typeStack, returnType);
        }
        break;
      }

      case ByteCode.ATHROW:
        // technically athrow leaves the stack in an undefined
        // state. In fact, the top value is the one we actually
        // throw, but it should stay on the stack since the exception
        // handler expects to start that way, at least in the real JVM.
        break;

      case ByteCode.NEW: {
        Type type = RefType.v(getClassName(constant_pool, ((Instruction_New) ins).arg_i), myScene);

        typeStack = typeStack.push(type);
        break;
      }

      case ByteCode.CHECKCAST: {
        String className = getClassName(constant_pool, ((Instruction_Checkcast) ins).arg_i);

        Type castType;

        if (className.startsWith("[")) {
          castType
              = myCoffiUtil.jimpleTypeOfFieldDescriptor(getClassName(constant_pool, ((Instruction_Checkcast) ins).arg_i));
        } else {
          castType = RefType.v(className, myScene);
        }

        typeStack = popSafeRefType(typeStack);
        typeStack = typeStack.push(castType);
        break;
      }

      case ByteCode.INSTANCEOF: {
        typeStack = popSafeRefType(typeStack);
        typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
        break;
      }

      case ByteCode.MONITORENTER:
        typeStack = popSafeRefType(typeStack);
        break;
      case ByteCode.MONITOREXIT:
        typeStack = popSafeRefType(typeStack);
        break;

      default:
        throw new RuntimeException("processFlow failed: Unknown bytecode instruction: " + x);
    }

    return new OutFlow(typeStack);
  }

  private Type jimpleTypeOfFieldInFieldRef(Scene cm, cp_info[] constant_pool, int index) {
    CONSTANT_Fieldref_info fr = (CONSTANT_Fieldref_info) (constant_pool[index]);

    CONSTANT_NameAndType_info nat = (CONSTANT_NameAndType_info) (constant_pool[fr.name_and_type_index]);

    String fieldDescriptor = ((CONSTANT_Utf8_info) (constant_pool[nat.descriptor_index])).convert();

    return myCoffiUtil.jimpleTypeOfFieldDescriptor(fieldDescriptor);
  }

  private Type jimpleReturnTypeOfNameAndType(Scene cm, cp_info[] constant_pool, int index) {
    CONSTANT_NameAndType_info nat = (CONSTANT_NameAndType_info) (constant_pool[index]);

    String methodDescriptor = ((CONSTANT_Utf8_info) (constant_pool[nat.descriptor_index])).convert();

    return myCoffiUtil.jimpleReturnTypeOfMethodDescriptor(methodDescriptor);
  }

  private Type jimpleReturnTypeOfMethodRef(Scene cm, cp_info[] constant_pool, int index) {
    CONSTANT_Methodref_info mr = (CONSTANT_Methodref_info) (constant_pool[index]);

    CONSTANT_NameAndType_info nat = (CONSTANT_NameAndType_info) (constant_pool[mr.name_and_type_index]);

    String methodDescriptor = ((CONSTANT_Utf8_info) (constant_pool[nat.descriptor_index])).convert();

    return myCoffiUtil.jimpleReturnTypeOfMethodDescriptor(methodDescriptor);
  }

  private Type jimpleReturnTypeOfInterfaceMethodRef(Scene cm, cp_info[] constant_pool, int index) {
    CONSTANT_InterfaceMethodref_info mr = (CONSTANT_InterfaceMethodref_info) (constant_pool[index]);

    CONSTANT_NameAndType_info nat = (CONSTANT_NameAndType_info) (constant_pool[mr.name_and_type_index]);

    String methodDescriptor = ((CONSTANT_Utf8_info) (constant_pool[nat.descriptor_index])).convert();

    return myCoffiUtil.jimpleReturnTypeOfMethodDescriptor(methodDescriptor);
  }

  private OutFlow processCPEntry(cp_info constant_pool[], int i, TypeStack typeStack, SootMethod jmethod) {
    cp_info c = constant_pool[i];

    if (c instanceof CONSTANT_Integer_info) {
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getIntType());
    } else if (c instanceof CONSTANT_Float_info) {
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getFloatType());
    } else if (c instanceof CONSTANT_Long_info) {
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
    } else if (c instanceof CONSTANT_Double_info) {
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
    } else if (c instanceof CONSTANT_String_info) {
      typeStack = typeStack.push(RefType.v("java.lang.String", myScene));
    } else if (c instanceof CONSTANT_Utf8_info) {
      typeStack = typeStack.push(RefType.v("java.lang.String", myScene));
    } else if (c instanceof CONSTANT_Class_info) {
      CONSTANT_Class_info info = (CONSTANT_Class_info) c;
      String name = ((CONSTANT_Utf8_info) (constant_pool[info.name_index])).convert();
      name = name.replace('/', '.');
      if (name.charAt(0) == '[') {
        int dim = 0;
        while (name.charAt(dim) == '[') {
          dim++;
        }
        // array type
        Type baseType = null;
        char typeIndicator = name.charAt(dim);
        switch (typeIndicator) {
          case 'I':
            baseType = myScene.getPrimTypeCollector().getIntType();
            break;
          case 'C':
            baseType = myScene.getPrimTypeCollector().getCharType();
            break;
          case 'F':
            baseType = myScene.getPrimTypeCollector().getFloatType();
            break;
          case 'D':
            baseType = myScene.getPrimTypeCollector().getDoubleType();
            break;
          case 'B':
            baseType = myScene.getPrimTypeCollector().getByteType();
            break;
          case 'S':
            baseType = myScene.getPrimTypeCollector().getShortType();
            break;
          case 'Z':
            baseType = myScene.getPrimTypeCollector().getBooleanType();
            break;
          case 'J':
            baseType = myScene.getPrimTypeCollector().getLongType();
            break;
          case 'L':
            baseType = RefType.v(name.substring(dim + 1, name.length() - 1), myScene);
            break;
          default:
            throw new RuntimeException("Unknown Array Base Type in Class Constant");
        }
        typeStack = typeStack.push(ArrayType.v(baseType, dim, myScene));
      } else {
        typeStack = typeStack.push(RefType.v(name, myScene));
      }
    } else {
      throw new RuntimeException("Attempting to push a non-constant cp entry" + c.getClass());
    }

    return new OutFlow(typeStack);
  }

  TypeStack smartPush(TypeStack typeStack, Type type) {
    if (type.equals(myScene.getPrimTypeCollector().getLongType())) {
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getLongType());
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getLong2ndHalfType());
    } else if (type.equals(myScene.getPrimTypeCollector().getDoubleType())) {
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getDoubleType());
      typeStack = typeStack.push(myScene.getPrimTypeCollector().getDouble2ndHalfType());
    } else {
      typeStack = typeStack.push(type);
    }

    return typeStack;
  }

  TypeStack popSafeRefType(TypeStack typeStack) {
    /*
     * if(!(typeStack.top() instanceof RefType) && !(typeStack.top() instanceof ArrayType)) { throw new
     * RuntimeException("popSafe failed; top: " + typeStack.top() + " required: RefType"); }
     */

    return typeStack.pop();
  }

  TypeStack popSafeArrayType(TypeStack typeStack) {
    /*
     * if(!(typeStack.top() instanceof ArrayType) && !(RefType.v("null").equals(typeStack.top()))) { throw new
     * RuntimeException("popSafe failed; top: " + typeStack.top() + " required: ArrayType"); }
     */

    return typeStack.pop();
  }

  TypeStack popSafe(TypeStack typeStack, Type requiredType) {
    /*
     * if(!typeStack.top().equals(requiredType)) throw new RuntimeException("popSafe failed; top: " + typeStack.top() +
     * " required: " + requiredType);
     */

    return typeStack.pop();
  }

  void confirmType(Type actualType, Type requiredType) {
    /*
     * if(!actualType.equals(requiredType)) throw new RuntimeException("confirmType failed; actualType: " + actualType +
     * "  required: " + requiredType);
     */
  }

  String getClassName(cp_info[] constant_pool, int index) {
    CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[index];

    String name = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();

    return name.replace('/', '.');
  }

  void confirmRefType(Type actualType) {
    /*
     * if(!(actualType instanceof RefType) && !(actualType instanceof ArrayType)) throw new
     * RuntimeException("confirmRefType failed; actualType: " + actualType);
     */
  }

  /**
   * Runs through the given bbq contents performing the target fix-up pass; Requires all reachable blocks to have their done
   * flags set to true, and this resets them all back to false;
   *
   * @param bbq
   *          queue of BasicBlocks to process.
   */
  private void processTargetFixup(BBQ bbq) {
    BasicBlock b, p;
    Stmt s;
    while (!bbq.isEmpty()) {
      try {
        b = bbq.pull();
      } catch (NoSuchElementException e) {
        break;
      }

      s = b.getTailJStmt();

      if (s instanceof GotoStmt) {
        if (b.succ.size() == 1) {
          // Regular goto

          ((GotoStmt) s).setTarget(b.succ.firstElement().getHeadJStmt());
        } else {
          // Goto derived from a jsr bytecode
          /*
           * if((BasicBlock)(b.succ.firstElement())==b.next) ((GotoStmt)s).setTarget(((BasicBlock)
           * b.succ.elementAt(1)).getHeadJStmt()); else ((GotoStmt)s).setTarget(((BasicBlock)
           * b.succ.firstElement()).getHeadJStmt());
           */
          logger.debug("Error :");
          for (int i = 0; i < b.statements.size(); i++) {
            logger.debug("" + b.statements.get(i));
          }

          throw new RuntimeException(b + " has " + b.succ.size() + " successors.");
        }
      } else if (s instanceof IfStmt) {
        if (b.succ.size() != 2) {
          logger.debug("How can an if not have 2 successors?");
        }

        if ((b.succ.firstElement()) == b.next) {
          ((IfStmt) s).setTarget(b.succ.elementAt(1).getHeadJStmt());
        } else {
          ((IfStmt) s).setTarget(b.succ.firstElement().getHeadJStmt());
        }

      } else if (s instanceof TableSwitchStmt) {
        int count = 0;
        TableSwitchStmt sts = (TableSwitchStmt) s;
        // Successors of the basic block ending with a switch statement
        // are listed in the successor vector in order, with the
        // default as the very first (0-th entry)

        for (BasicBlock basicBlock : b.succ) {
          p = (basicBlock);
          if (count == 0) {
            sts.setDefaultTarget(p.getHeadJStmt());
          } else {
            sts.setTarget(count - 1, p.getHeadJStmt());
          }
          count++;
        }
      } else if (s instanceof LookupSwitchStmt) {
        int count = 0;
        LookupSwitchStmt sls = (LookupSwitchStmt) s;
        // Successors of the basic block ending with a switch statement
        // are listed in the successor vector in order, with the
        // default as the very first (0-th entry)

        for (BasicBlock basicBlock : b.succ) {
          p = (basicBlock);
          if (count == 0) {
            sls.setDefaultTarget(p.getHeadJStmt());
          } else {
            sls.setTarget(count - 1, p.getHeadJStmt());
          }
          count++;
        }
      }

      b.done = false;
      for (BasicBlock basicBlock : b.succ) {
        p = (basicBlock);
        if (p.done) {
          bbq.push(p);
        }
      }
    }
  }

  /**
   * After the initial jimple construction, a second pass is made to fix up missing Stmt targets for <tt>goto</tt>s,
   * <tt>if</tt>'s etc.
   *
   * code attribute of this method.
   * 
   * @see CFG#jimplify
   */
  void jimpleTargetFixup() {
    BasicBlock b;
    BBQ bbq = new BBQ();

    Code_attribute c = method.locate_code_attribute();
    if (c == null) {
      return;
    }

    // Reset all the dones to true
    {
      BasicBlock bb = cfg;

      while (bb != null) {
        bb.done = true;
        bb = bb.next;
      }
    }

    // first process the main code
    bbq.push(cfg);
    processTargetFixup(bbq);

    // then the exceptions
    if (bbq.isEmpty()) {
      int i;
      for (i = 0; i < c.exception_table_length; i++) {
        b = c.exception_table[i].b;
        // if block hasn't yet been processed...
        if (b != null && b.done) {
          bbq.push(b);
          processTargetFixup(bbq);
          if (!bbq.isEmpty()) {
            logger.debug("Error 2nd processing exception block.");
            break;
          }
        }
      }
    }
  }

  private void generateJimpleForCPEntry(cp_info constant_pool[], int i, TypeStack typeStack, TypeStack postTypeStack,
      SootMethod jmethod, List<Stmt> statements) {
    Stmt stmt;
    Value rvalue;

    cp_info c = constant_pool[i];

    if (c instanceof CONSTANT_Integer_info) {
      CONSTANT_Integer_info ci = (CONSTANT_Integer_info) c;

      rvalue = constancFactory.createIntConstant((int) ci.bytes);
      stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
          rvalue);
    } else if (c instanceof CONSTANT_Float_info) {
      CONSTANT_Float_info cf = (CONSTANT_Float_info) c;

      rvalue = constancFactory.createFloatConstant(cf.convert());
      stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
          rvalue);
    } else if (c instanceof CONSTANT_Long_info) {
      CONSTANT_Long_info cl = (CONSTANT_Long_info) c;

      rvalue = constancFactory.createLongConstant(cl.convert());
      stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
          rvalue);
    } else if (c instanceof CONSTANT_Double_info) {
      CONSTANT_Double_info cd = (CONSTANT_Double_info) c;

      rvalue = constancFactory.createDoubleConstant(cd.convert());

      stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
          rvalue);
    } else if (c instanceof CONSTANT_String_info) {
      CONSTANT_String_info cs = (CONSTANT_String_info) c;

      String constant = cs.toString(constant_pool);

      if (constant.startsWith("\"") && constant.endsWith("\"")) {
        constant = constant.substring(1, constant.length() - 1);
      }

      rvalue = constancFactory.createStringConstant(constant);
      stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
          rvalue);
    } else if (c instanceof CONSTANT_Utf8_info) {
      CONSTANT_Utf8_info cu = (CONSTANT_Utf8_info) c;

      String constant = cu.convert();

      if (constant.startsWith("\"") && constant.endsWith("\"")) {
        constant = constant.substring(1, constant.length() - 1);
      }

      rvalue = constancFactory.createStringConstant(constant);
      stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
          rvalue);
    } else if (c instanceof CONSTANT_Class_info) {

      String className = ((CONSTANT_Utf8_info) (constant_pool[((CONSTANT_Class_info) c).name_index])).convert();

      rvalue = constancFactory.createClassConstant(className);
      stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
          rvalue);
    } else {
      throw new RuntimeException("Attempting to push a non-constant cp entry" + c);
    }

    statements.add(stmt);
  }

  void generateJimple(Instruction ins, TypeStack typeStack, TypeStack postTypeStack, cp_info constant_pool[],
      List<Stmt> statements, BasicBlock basicBlock) {
    Value[] params;
    Local l1 = null, l2 = null, l3 = null, l4 = null;

    Expr rhs = null;
    ConditionExpr co = null;

    ArrayRef a = null;
    int args;
    Value rvalue;

    // int localIndex;

    Stmt stmt = null;

    int x = ((ins.code)) & 0xff;

    switch (x) {
      case ByteCode.BIPUSH:
        rvalue = constancFactory.createIntConstant(((Instruction_Bipush) ins).arg_b);
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rvalue);
        break;

      case ByteCode.SIPUSH:
        rvalue = constancFactory.createIntConstant(((Instruction_Sipush) ins).arg_i);
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rvalue);
        break;

      case ByteCode.LDC1:
        generateJimpleForCPEntry(constant_pool, ((Instruction_Ldc1) ins).arg_b, typeStack, postTypeStack, jmethod,
            statements);
        break;

      case ByteCode.LDC2:
      case ByteCode.LDC2W:
        generateJimpleForCPEntry(constant_pool, ((Instruction_intindex) ins).arg_i, typeStack, postTypeStack, jmethod,
            statements);
        break;

      case ByteCode.ACONST_NULL:
        rvalue = constancFactory.getNullConstant();
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rvalue);
        break;

      case ByteCode.ICONST_M1:
      case ByteCode.ICONST_0:
      case ByteCode.ICONST_1:
      case ByteCode.ICONST_2:
      case ByteCode.ICONST_3:
      case ByteCode.ICONST_4:
      case ByteCode.ICONST_5:
        rvalue = constancFactory.createIntConstant(x - ByteCode.ICONST_0);
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rvalue);
        break;

      case ByteCode.LCONST_0:
      case ByteCode.LCONST_1:
        rvalue = constancFactory.createLongConstant(x - ByteCode.LCONST_0);
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rvalue);
        break;

      case ByteCode.FCONST_0:
      case ByteCode.FCONST_1:
      case ByteCode.FCONST_2:
        rvalue = constancFactory.createFloatConstant((x - ByteCode.FCONST_0));
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rvalue);
        break;

      case ByteCode.DCONST_0:
      case ByteCode.DCONST_1:
        rvalue = constancFactory.createDoubleConstant((x - ByteCode.DCONST_0));
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rvalue);
        break;

      case ByteCode.ILOAD: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.FLOAD: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.ALOAD: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.DLOAD: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.LLOAD: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.ILOAD_0:
      case ByteCode.ILOAD_1:
      case ByteCode.ILOAD_2:
      case ByteCode.ILOAD_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.ILOAD_0), ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.FLOAD_0:
      case ByteCode.FLOAD_1:
      case ByteCode.FLOAD_2:
      case ByteCode.FLOAD_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.FLOAD_0), ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.ALOAD_0:
      case ByteCode.ALOAD_1:
      case ByteCode.ALOAD_2:
      case ByteCode.ALOAD_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.ALOAD_0), ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.LLOAD_0:
      case ByteCode.LLOAD_1:
      case ByteCode.LLOAD_2:
      case ByteCode.LLOAD_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.LLOAD_0), ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.DLOAD_0:
      case ByteCode.DLOAD_1:
      case ByteCode.DLOAD_2:
      case ByteCode.DLOAD_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.DLOAD_0), ins);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            local);
        break;
      }

      case ByteCode.ISTORE: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.FSTORE: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.ASTORE: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.LSTORE: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.DSTORE: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_bytevar) ins).arg_b, ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.ISTORE_0:
      case ByteCode.ISTORE_1:
      case ByteCode.ISTORE_2:
      case ByteCode.ISTORE_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.ISTORE_0), ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.FSTORE_0:
      case ByteCode.FSTORE_1:
      case ByteCode.FSTORE_2:
      case ByteCode.FSTORE_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.FSTORE_0), ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.ASTORE_0:
      case ByteCode.ASTORE_1:
      case ByteCode.ASTORE_2:
      case ByteCode.ASTORE_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.ASTORE_0), ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.LSTORE_0:
      case ByteCode.LSTORE_1:
      case ByteCode.LSTORE_2:
      case ByteCode.LSTORE_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.LSTORE_0), ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.DSTORE_0:
      case ByteCode.DSTORE_1:
      case ByteCode.DSTORE_2:
      case ByteCode.DSTORE_3: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, (x - ByteCode.DSTORE_0), ins);

        stmt = myJimple.newAssignStmt(local, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.IINC: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_Iinc) ins).arg_b, ins);

        int amt = (((Instruction_Iinc) ins).arg_c);
        rhs = myJimple.newAddExpr(local, constancFactory.createIntConstant(amt));
        stmt = myJimple.newAssignStmt(local, rhs);
        break;
      }

      case ByteCode.WIDE:
        throw new RuntimeException("WIDE instruction should not be encountered anymore");
        // break;

      case ByteCode.NEWARRAY: {
        Type baseType = jimpleTypeOfAtype(((Instruction_Newarray) ins).atype);

        rhs = myJimple.newNewArrayExpr(baseType, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);

        break;
      }

      case ByteCode.ANEWARRAY: {
        String baseName = getClassName(constant_pool, ((Instruction_Anewarray) ins).arg_i);

        Type baseType;

        if (baseName.startsWith("[")) {
          baseType
              = myCoffiUtil.jimpleTypeOfFieldDescriptor(getClassName(constant_pool, ((Instruction_Anewarray) ins).arg_i));
        } else {
          baseType = RefType.v(baseName, myScene);
        }

        rhs = myJimple.newNewArrayExpr(baseType, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;
      }

      case ByteCode.MULTIANEWARRAY: {
        int bdims = (((Instruction_Multianewarray) ins).dims);
        List<Value> dims = new ArrayList<Value>();

        for (int j = 0; j < bdims; j++) {
          dims.add(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - bdims + j + 1));
        }

        String mstype = constant_pool[((Instruction_Multianewarray) ins).arg_i].toString(constant_pool);

        ArrayType jimpleType = (ArrayType) myCoffiUtil.jimpleTypeOfFieldDescriptor(mstype);

        rhs = myJimple.newNewMultiArrayExpr(jimpleType, dims);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;
      }

      case ByteCode.ARRAYLENGTH:
        rhs = myJimple.newLengthExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.IALOAD:
      case ByteCode.BALOAD:
      case ByteCode.CALOAD:
      case ByteCode.SALOAD:
      case ByteCode.FALOAD:
      case ByteCode.LALOAD:
      case ByteCode.DALOAD:
      case ByteCode.AALOAD:
        a = myJimple.newArrayRef(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()), a);

        break;

      case ByteCode.IASTORE:
      case ByteCode.FASTORE:
      case ByteCode.AASTORE:
      case ByteCode.BASTORE:
      case ByteCode.CASTORE:
      case ByteCode.SASTORE:
        a = myJimple.newArrayRef(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(a, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;

      case ByteCode.LASTORE:
      case ByteCode.DASTORE:
        a = myJimple.newArrayRef(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2));

        stmt = myJimple.newAssignStmt(a, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;

      case ByteCode.NOP:
        stmt = myJimple.newNopStmt();
        break;

      case ByteCode.POP:
      case ByteCode.POP2:
        stmt = myJimple.newNopStmt();
        break;

      case ByteCode.DUP:
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;

      case ByteCode.DUP2:
        if (typeSize(typeStack.top()) == 2) {
          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1),
              myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));
        } else {
          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1),
              myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

          statements.add(stmt);

          stmt = null;
        }
        break;

      case ByteCode.DUP_X1:
        l1 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());
        l2 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()), l1);

        statements.add(stmt);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1),
            l2);

        statements.add(stmt);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 2),
            myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()));

        statements.add(stmt);

        stmt = null;
        break;

      case ByteCode.DUP_X2:
        if (typeSize(typeStack.get(typeStack.topIndex() - 2)) == 2) {
          l3 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2);
          l1 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 2), l3);

          statements.add(stmt);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 3), l1);

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              l1);

          statements.add(stmt);

          stmt = null;
        } else {
          l3 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2);
          l2 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1);
          l1 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              l1);

          statements.add(stmt);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1), l2);

          statements.add(stmt);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 2), l3);

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 3),
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()));

          statements.add(stmt);

          stmt = null;
        }
        break;

      case ByteCode.DUP2_X1:
        if (typeSize(typeStack.get(typeStack.topIndex() - 1)) == 2) {
          l2 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1);
          l3 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1), l2);

          statements.add(stmt);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 2), l3);

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 4),
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1));

          statements.add(stmt);

          stmt = null;
        } else {
          l3 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2);
          l2 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1);
          l1 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              l1);

          statements.add(stmt);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1), l2);

          statements.add(stmt);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 2), l3);

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 3),
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()));

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 4),
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1));

          statements.add(stmt);

          stmt = null;
        }
        break;

      case ByteCode.DUP2_X2:
        if (typeSize(typeStack.get(typeStack.topIndex() - 1)) == 2) {
          l2 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1), l2);

          statements.add(stmt);
        } else {
          l1 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());
          l2 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1), l2);

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              l1);

          statements.add(stmt);

        }

        if (typeSize(typeStack.get(typeStack.topIndex() - 3)) == 2) {
          l4 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 3), l4);

          statements.add(stmt);
        } else {
          l4 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3);
          l3 = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 3), l4);

          statements.add(stmt);

          stmt = myJimple
              .newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 2), l3);

          statements.add(stmt);

        }

        if (typeSize(typeStack.get(typeStack.topIndex() - 1)) == 2) {
          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 5),
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1));

          statements.add(stmt);
        } else {
          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 5),
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1));

          statements.add(stmt);

          stmt = myJimple.newAssignStmt(
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 4),
              myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()));

          statements.add(stmt);
        }
        stmt = null;
        break;

      case ByteCode.SWAP: {
        Local first;

        typeStack = typeStack.push(typeStack.top());
        first = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());
        typeStack = typeStack.pop();
        // generation of a free temporary

        Local second = myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex());

        Local third = myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex() - 1);

        stmt = myJimple.newAssignStmt(first, second);
        statements.add(stmt);

        stmt = myJimple.newAssignStmt(second, third);
        statements.add(stmt);

        stmt = myJimple.newAssignStmt(third, first);
        statements.add(stmt);

        stmt = null;
        break;
      }

      case ByteCode.FADD:
      case ByteCode.IADD:
        rhs = myJimple.newAddExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.DADD:
      case ByteCode.LADD:
        rhs = myJimple.newAddExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.FSUB:
      case ByteCode.ISUB:
        rhs = myJimple.newSubExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.DSUB:
      case ByteCode.LSUB:
        rhs = myJimple.newSubExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.FMUL:
      case ByteCode.IMUL:
        rhs = myJimple.newMulExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.DMUL:
      case ByteCode.LMUL:
        rhs = myJimple.newMulExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.FDIV:
      case ByteCode.IDIV:
        rhs = myJimple.newDivExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.DDIV:
      case ByteCode.LDIV:
        rhs = myJimple.newDivExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.FREM:
      case ByteCode.IREM:
        rhs = myJimple.newRemExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.DREM:
      case ByteCode.LREM:
        rhs = myJimple.newRemExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.INEG:
      case ByteCode.LNEG:
      case ByteCode.FNEG:
      case ByteCode.DNEG:
        rhs = myJimple.newNegExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.ISHL:
        rhs = myJimple.newShlExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.ISHR:
        rhs = myJimple.newShrExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.IUSHR:
        rhs = myJimple.newUshrExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.LSHL:
        rhs = myJimple.newShlExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.LSHR:
        rhs = myJimple.newShrExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.LUSHR:
        rhs = myJimple.newUshrExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 2),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.IAND:
        rhs = myJimple.newAndExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.LAND:
        rhs = myJimple.newAndExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.IOR:
        rhs = myJimple.newOrExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.LOR:
        rhs = myJimple.newOrExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.IXOR:
        rhs = myJimple.newXorExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.LXOR:
        rhs = myJimple.newXorExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.D2L:
      case ByteCode.F2L:
      case ByteCode.I2L:
        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            myScene.getPrimTypeCollector().getLongType());

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.D2F:
      case ByteCode.L2F:
      case ByteCode.I2F:
        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            myScene.getPrimTypeCollector().getFloatType());

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.I2D:
      case ByteCode.L2D:
      case ByteCode.F2D:
        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            myScene.getPrimTypeCollector().getDoubleType());

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.L2I:
      case ByteCode.F2I:
      case ByteCode.D2I:
        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            myScene.getPrimTypeCollector().getIntType());

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.INT2BYTE:
        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            myScene.getPrimTypeCollector().getByteType());

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.INT2CHAR:
        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            myScene.getPrimTypeCollector().getCharType());

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.INT2SHORT:
        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            myScene.getPrimTypeCollector().getShortType());

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.IFEQ:
        co = myJimple.newEqExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.createIntConstant(0));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IFNULL:
        co = myJimple.newEqExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.getNullConstant());

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IFLT:
        co = myJimple.newLtExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.createIntConstant(0));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IFLE:
        co = myJimple.newLeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.createIntConstant(0));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IFNE:
        co = myJimple.newNeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.createIntConstant(0));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IFNONNULL:
        co = myJimple.newNeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.getNullConstant());

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IFGT:
        co = myJimple.newGtExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.createIntConstant(0));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IFGE:
        co = myJimple.newGeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), constancFactory.createIntConstant(0));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IF_ICMPEQ:
        co = myJimple.newEqExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IF_ICMPLT:
        co = myJimple.newLtExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IF_ICMPLE:
        co = myJimple.newLeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IF_ICMPNE:
        co = myJimple.newNeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IF_ICMPGT:
        co = myJimple.newGtExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IF_ICMPGE:
        co = myJimple.newGeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.LCMP:
        rhs = myJimple.newCmpExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.FCMPL:
        rhs = myJimple.newCmplExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.FCMPG:
        rhs = myJimple.newCmpgExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.DCMPL:
        rhs = myJimple.newCmplExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.DCMPG:
        rhs = myJimple.newCmpgExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 3),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;

      case ByteCode.IF_ACMPEQ:
        co = myJimple.newEqExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.IF_ACMPNE:
        co = myJimple.newNeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - 1),
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));

        stmt = myJimple.newIfStmt(co, new FutureStmt());
        break;

      case ByteCode.GOTO:
        stmt = myJimple.newGotoStmt(new FutureStmt());
        break;

      case ByteCode.GOTO_W:
        stmt = myJimple.newGotoStmt(new FutureStmt());
        break;
      /*
       * case ByteCode.JSR: case ByteCode.JSR_W: { stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody,
       * postTypeStack, postTypeStack.topIndex()), myJimple.newNextNextStmtRef());
       *
       * statements.add(stmt);
       *
       * stmt = myJimple.newGotoStmt(new FutureStmt()); statements.add(stmt);
       *
       * stmt = null; break; }
       */

      case ByteCode.RET: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_Ret) ins).arg_b, ins);

        stmt = myJimple.newRetStmt(local);
        break;
      }

      case ByteCode.RET_W: {
        Local local = myCoffiUtil.getLocalForIndex(listBody, ((Instruction_Ret_w) ins).arg_i, ins);

        stmt = myJimple.newRetStmt(local);
        break;
      }

      case ByteCode.RETURN:
        stmt = myJimple.newReturnVoidStmt();
        break;

      case ByteCode.LRETURN:
      case ByteCode.DRETURN:
      case ByteCode.IRETURN:
      case ByteCode.FRETURN:
      case ByteCode.ARETURN:
        stmt = myJimple.newReturnStmt(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;

      case ByteCode.BREAKPOINT:
        stmt = myJimple.newBreakpointStmt();
        break;

      case ByteCode.TABLESWITCH: {
        int lowIndex = ((Instruction_Tableswitch) ins).low, highIndex = ((Instruction_Tableswitch) ins).high;

        int npairs = highIndex - lowIndex + 1;

        stmt = myJimple.newTableSwitchStmt(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            lowIndex, highIndex, Arrays.asList(new FutureStmt[npairs]), new FutureStmt());
        break;
      }

      case ByteCode.LOOKUPSWITCH: {
        List<IntConstant> matches = new ArrayList<IntConstant>();
        int npairs = ((Instruction_Lookupswitch) ins).npairs;

        for (int j = 0; j < npairs; j++) {
          matches.add(constancFactory.createIntConstant(((Instruction_Lookupswitch) ins).match_offsets[j * 2]));
        }

        stmt = myJimple.newLookupSwitchStmt(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            matches, Arrays.asList(new FutureStmt[npairs]), new FutureStmt());
        break;
      }

      case ByteCode.PUTFIELD: {
        CONSTANT_Fieldref_info fieldInfo = (CONSTANT_Fieldref_info) constant_pool[((Instruction_Putfield) ins).arg_i];

        CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[fieldInfo.class_index];

        String className = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();
        className = className.replace('/', '.');

        CONSTANT_NameAndType_info i = (CONSTANT_NameAndType_info) constant_pool[fieldInfo.name_and_type_index];

        String fieldName = ((CONSTANT_Utf8_info) (constant_pool[i.name_index])).convert();
        String fieldDescriptor = ((CONSTANT_Utf8_info) (constant_pool[i.descriptor_index])).convert();

        Type fieldType = myCoffiUtil.jimpleTypeOfFieldDescriptor(fieldDescriptor);

        SootClass bclass = cm.getSootClass(className);

        SootFieldRef fieldRef = myScene.makeFieldRef(bclass, fieldName, fieldType, false);

        InstanceFieldRef fr = myJimple.newInstanceFieldRef(
            myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex() - typeSize(typeStack.top())), fieldRef);

        rvalue = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());
        stmt = myJimple.newAssignStmt(fr, rvalue);
        break;
      }

      case ByteCode.GETFIELD: {
        InstanceFieldRef fr = null;

        CONSTANT_Fieldref_info fieldInfo = (CONSTANT_Fieldref_info) constant_pool[((Instruction_Getfield) ins).arg_i];

        CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[fieldInfo.class_index];

        String className = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();
        className = className.replace('/', '.');

        CONSTANT_NameAndType_info i = (CONSTANT_NameAndType_info) constant_pool[fieldInfo.name_and_type_index];

        String fieldName = ((CONSTANT_Utf8_info) (constant_pool[i.name_index])).convert();
        String fieldDescriptor = ((CONSTANT_Utf8_info) (constant_pool[i.descriptor_index])).convert();

        if (className.charAt(0) == '[') {
          className = "java.lang.Object";
        }

        SootClass bclass = cm.getSootClass(className);

        Type fieldType = myCoffiUtil.jimpleTypeOfFieldDescriptor(fieldDescriptor);
        SootFieldRef fieldRef = myScene.makeFieldRef(bclass, fieldName, fieldType, false);

        fr = myJimple.newInstanceFieldRef(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            fieldRef);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()), fr);
        break;
      }

      case ByteCode.PUTSTATIC: {
        StaticFieldRef fr = null;

        CONSTANT_Fieldref_info fieldInfo = (CONSTANT_Fieldref_info) constant_pool[((Instruction_Putstatic) ins).arg_i];

        CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[fieldInfo.class_index];

        String className = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();
        className = className.replace('/', '.');

        CONSTANT_NameAndType_info i = (CONSTANT_NameAndType_info) constant_pool[fieldInfo.name_and_type_index];

        String fieldName = ((CONSTANT_Utf8_info) (constant_pool[i.name_index])).convert();
        String fieldDescriptor = ((CONSTANT_Utf8_info) (constant_pool[i.descriptor_index])).convert();

        Type fieldType = myCoffiUtil.jimpleTypeOfFieldDescriptor(fieldDescriptor);

        SootClass bclass = cm.getSootClass(className);
        SootFieldRef fieldRef = myScene.makeFieldRef(bclass, fieldName, fieldType, true);

        fr = myJimple.newStaticFieldRef(fieldRef);

        stmt = myJimple.newAssignStmt(fr, myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      }

      case ByteCode.GETSTATIC: {
        StaticFieldRef fr = null;

        CONSTANT_Fieldref_info fieldInfo = (CONSTANT_Fieldref_info) constant_pool[((Instruction_Getstatic) ins).arg_i];

        CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[fieldInfo.class_index];

        String className = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();
        className = className.replace('/', '.');

        CONSTANT_NameAndType_info i = (CONSTANT_NameAndType_info) constant_pool[fieldInfo.name_and_type_index];

        String fieldName = ((CONSTANT_Utf8_info) (constant_pool[i.name_index])).convert();
        String fieldDescriptor = ((CONSTANT_Utf8_info) (constant_pool[i.descriptor_index])).convert();

        Type fieldType = myCoffiUtil.jimpleTypeOfFieldDescriptor(fieldDescriptor);

        SootClass bclass = cm.getSootClass(className);
        SootFieldRef fieldRef = myScene.makeFieldRef(bclass, fieldName, fieldType, true);

        fr = myJimple.newStaticFieldRef(fieldRef);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()), fr);
        break;
      }

      case ByteCode.INVOKEDYNAMIC: {
        Instruction_Invokedynamic iv = (Instruction_Invokedynamic) ins;
        CONSTANT_InvokeDynamic_info iv_info = (CONSTANT_InvokeDynamic_info) constant_pool[iv.invoke_dynamic_index];
        args = cp_info.countParams(constant_pool, iv_info.name_and_type_index);

        SootMethodRef bootstrapMethodRef;
        List<Value> bootstrapArgs = new LinkedList<Value>();
        int kind;
        {
          short[] bootstrapMethodTable = bootstrap_methods_attribute.method_handles;
          short methodSigIndex = bootstrapMethodTable[iv_info.bootstrap_method_index];
          CONSTANT_MethodHandle_info mhInfo = (CONSTANT_MethodHandle_info) constant_pool[methodSigIndex];
          CONSTANT_Methodref_info bsmInfo = (CONSTANT_Methodref_info) constant_pool[mhInfo.target_index];
          bootstrapMethodRef = createMethodRef(constant_pool, bsmInfo, false);
          kind = mhInfo.kind;

          short[] bsmArgIndices = bootstrap_methods_attribute.arg_indices[iv_info.bootstrap_method_index];
          if (bsmArgIndices.length > 0) {
            // logger.debug("Soot does not currently support static arguments to bootstrap methods. They will be stripped.");
            for (short bsmArgIndex : bsmArgIndices) {
              cp_info cpEntry = constant_pool[bsmArgIndex];
              Value val = cpEntry.createJimpleConstantValue(constant_pool);
              bootstrapArgs.add(val);
            }
          }
        }

        SootMethodRef methodRef = null;

        CONSTANT_NameAndType_info nameAndTypeInfo = (CONSTANT_NameAndType_info) constant_pool[iv_info.name_and_type_index];

        String methodName = ((CONSTANT_Utf8_info) (constant_pool[nameAndTypeInfo.name_index])).convert();
        String methodDescriptor = ((CONSTANT_Utf8_info) (constant_pool[nameAndTypeInfo.descriptor_index])).convert();

        SootClass bclass = cm.getSootClass(SootClass.INVOKEDYNAMIC_DUMMY_CLASS_NAME);

        List<Type> parameterTypes;
        Type returnType;

        // Generate parameters & returnType & parameterTypes
        {
          Type[] types = myCoffiUtil.jimpleTypesOfFieldOrMethodDescriptor(methodDescriptor);

          parameterTypes = new ArrayList<Type>();

          for (int k = 0; k < types.length - 1; k++) {
            parameterTypes.add(types[k]);
          }

          returnType = types[types.length - 1];
        }
        // we always model invokeDynamic method refs as static method references of methods on the type
        // SootClass.INVOKEDYNAMIC_DUMMY_CLASS_NAME
        methodRef = myScene.makeMethodRef(bclass, methodName, parameterTypes, returnType, true);

        // build Vector of parameters
        params = new Value[args];
        for (int j = args - 1; j >= 0; j--) {
          params[j] = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          if (typeSize(typeStack.top()) == 2) {
            typeStack = typeStack.pop();
            typeStack = typeStack.pop();
          } else {
            typeStack = typeStack.pop();
          }
        }

        rvalue = myJimple.newDynamicInvokeExpr(bootstrapMethodRef, bootstrapArgs, methodRef, kind, Arrays.asList(params));

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              rvalue);
        } else {
          stmt = myJimple.newInvokeStmt(rvalue);
        }

        break;
      }

      case ByteCode.INVOKEVIRTUAL: {
        Instruction_Invokevirtual iv = (Instruction_Invokevirtual) ins;
        args = cp_info.countParams(constant_pool, iv.arg_i);

        CONSTANT_Methodref_info methodInfo = (CONSTANT_Methodref_info) constant_pool[iv.arg_i];

        SootMethodRef methodRef = createMethodRef(constant_pool, methodInfo, false);

        Type returnType = methodRef.returnType();
        // build array of parameters
        params = new Value[args];
        for (int j = args - 1; j >= 0; j--) {
          params[j] = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          if (typeSize(typeStack.top()) == 2) {
            typeStack = typeStack.pop();
            typeStack = typeStack.pop();
          } else {
            typeStack = typeStack.pop();
          }
        }

        rvalue = myJimple.newVirtualInvokeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            methodRef, Arrays.asList(params));

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              rvalue);
        } else {
          stmt = myJimple.newInvokeStmt(rvalue);
        }
        break;
      }

      case ByteCode.INVOKENONVIRTUAL: {
        Instruction_Invokenonvirtual iv = (Instruction_Invokenonvirtual) ins;
        args = cp_info.countParams(constant_pool, iv.arg_i);

        CONSTANT_Methodref_info methodInfo = (CONSTANT_Methodref_info) constant_pool[iv.arg_i];

        SootMethodRef methodRef = createMethodRef(constant_pool, methodInfo, false);

        Type returnType = methodRef.returnType();

        // build array of parameters
        params = new Value[args];
        for (int j = args - 1; j >= 0; j--) {
          params[j] = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          if (typeSize(typeStack.top()) == 2) {
            typeStack = typeStack.pop();
            typeStack = typeStack.pop();
          } else {
            typeStack = typeStack.pop();
          }
        }

        rvalue = myJimple.newSpecialInvokeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            methodRef, Arrays.asList(params));

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              rvalue);
        } else {
          stmt = myJimple.newInvokeStmt(rvalue);
        }
        break;
      }

      case ByteCode.INVOKESTATIC: {
        Instruction_Invokestatic is = (Instruction_Invokestatic) ins;
        args = cp_info.countParams(constant_pool, is.arg_i);

        CONSTANT_Methodref_info methodInfo = (CONSTANT_Methodref_info) constant_pool[is.arg_i];

        SootMethodRef methodRef = createMethodRef(constant_pool, methodInfo, true);

        Type returnType = methodRef.returnType();

        // build Vector of parameters
        params = new Value[args];
        for (int j = args - 1; j >= 0; j--) {
          /*
           * logger.debug("BeforeTypeStack"); typeStack.print(G.v().out);
           *
           * logger.debug("AfterTypeStack"); postTypeStack.print(G.v().out);
           */

          params[j] = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          if (typeSize(typeStack.top()) == 2) {
            typeStack = typeStack.pop();
            typeStack = typeStack.pop();
          } else {
            typeStack = typeStack.pop();
          }
        }

        rvalue = myJimple.newStaticInvokeExpr(methodRef, Arrays.asList(params));

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              rvalue);
        } else {
          stmt = myJimple.newInvokeStmt(rvalue);
        }

        break;
      }

      case ByteCode.INVOKEINTERFACE: {
        Instruction_Invokeinterface ii = (Instruction_Invokeinterface) ins;
        args = cp_info.countParams(constant_pool, ii.arg_i);

        CONSTANT_InterfaceMethodref_info methodInfo = (CONSTANT_InterfaceMethodref_info) constant_pool[ii.arg_i];

        SootMethodRef methodRef = createMethodRef(constant_pool, methodInfo, false);

        Type returnType = methodRef.returnType();

        // build Vector of parameters
        params = new Value[args];
        for (int j = args - 1; j >= 0; j--) {
          params[j] = myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex());

          if (typeSize(typeStack.top()) == 2) {
            typeStack = typeStack.pop();
            typeStack = typeStack.pop();
          } else {
            typeStack = typeStack.pop();
          }
        }

        rvalue = myJimple.newInterfaceInvokeExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            methodRef, Arrays.asList(params));

        if (!returnType.equals(myScene.getPrimTypeCollector().getVoidType())) {
          stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
              rvalue);
        } else {
          stmt = myJimple.newInvokeStmt(rvalue);
        }
        break;
      }

      case ByteCode.ATHROW:
        stmt = myJimple.newThrowStmt(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;

      case ByteCode.NEW: {
        SootClass bclass = cm.getSootClass(getClassName(constant_pool, ((Instruction_New) ins).arg_i));

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            myJimple.newNewExpr(RefType.v(bclass.getName(), myScene)));
        break;
      }

      case ByteCode.CHECKCAST: {
        String className = getClassName(constant_pool, ((Instruction_Checkcast) ins).arg_i);

        Type castType;

        if (className.startsWith("[")) {
          castType
              = myCoffiUtil.jimpleTypeOfFieldDescriptor(getClassName(constant_pool, ((Instruction_Checkcast) ins).arg_i));
        } else {
          castType = RefType.v(className, myScene);
        }

        rhs = myJimple.newCastExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()), castType);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;
      }

      case ByteCode.INSTANCEOF: {
        Type checkType;

        String className = getClassName(constant_pool, ((Instruction_Instanceof) ins).arg_i);

        if (className.startsWith("[")) {
          checkType
              = myCoffiUtil.jimpleTypeOfFieldDescriptor(getClassName(constant_pool, ((Instruction_Instanceof) ins).arg_i));
        } else {
          checkType = RefType.v(className, myScene);
        }

        rhs = myJimple.newInstanceOfExpr(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()),
            checkType);

        stmt = myJimple.newAssignStmt(myCoffiUtil.getLocalForStackOp(listBody, postTypeStack, postTypeStack.topIndex()),
            rhs);
        break;
      }

      case ByteCode.MONITORENTER:
        stmt = myJimple.newEnterMonitorStmt(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;
      case ByteCode.MONITOREXIT:
        stmt = myJimple.newExitMonitorStmt(myCoffiUtil.getLocalForStackOp(listBody, typeStack, typeStack.topIndex()));
        break;

      default:
        throw new RuntimeException("Unrecognized bytecode instruction: " + x);
    }

    if (stmt != null) {
      if (myOptions.keep_offset()) {
        stmt.addTag(new BytecodeOffsetTag(ins.label));
      }
      statements.add(stmt);
    }
  }

  private SootMethodRef createMethodRef(cp_info[] constant_pool, ICONSTANT_Methodref_info methodInfo, boolean isStatic) {
    SootMethodRef methodRef;

    CONSTANT_Class_info c = (CONSTANT_Class_info) constant_pool[methodInfo.getClassIndex()];

    String className = ((CONSTANT_Utf8_info) (constant_pool[c.name_index])).convert();
    className = className.replace('/', '.');

    CONSTANT_NameAndType_info i = (CONSTANT_NameAndType_info) constant_pool[methodInfo.getNameAndTypeIndex()];

    String methodName = ((CONSTANT_Utf8_info) (constant_pool[i.name_index])).convert();
    String methodDescriptor = ((CONSTANT_Utf8_info) (constant_pool[i.descriptor_index])).convert();

    if (className.charAt(0) == '[') {
      className = "java.lang.Object";
    }

    SootClass bclass = cm.getSootClass(className);

    List<Type> parameterTypes;
    Type returnType;
    // Generate parameters & returnType & parameterTypes
    {
      Type[] types = myCoffiUtil.jimpleTypesOfFieldOrMethodDescriptor(methodDescriptor);

      parameterTypes = new ArrayList<Type>();

      for (int k = 0; k < types.length - 1; k++) {
        parameterTypes.add(types[k]);
      }

      returnType = types[types.length - 1];
    }

    methodRef = myScene.makeMethodRef(bclass, methodName, parameterTypes, returnType, isStatic);
    return methodRef;
  }

  Type jimpleTypeOfAtype(int atype) {
    switch (atype) {
      case 4:
        return myScene.getPrimTypeCollector().getBooleanType();

      case 5:
        return myScene.getPrimTypeCollector().getCharType();

      case 6:
        return myScene.getPrimTypeCollector().getFloatType();

      case 7:
        return myScene.getPrimTypeCollector().getDoubleType();

      case 8:
        return myScene.getPrimTypeCollector().getByteType();

      case 9:
        return myScene.getPrimTypeCollector().getShortType();

      case 10:
        return myScene.getPrimTypeCollector().getIntType();

      case 11:
        return myScene.getPrimTypeCollector().getLongType();

      default:
        throw new RuntimeException("Undefined 'atype' in NEWARRAY byte instruction");
    }
  }

  int typeSize(Type type) {
    if (type.equals(myScene.getPrimTypeCollector().getLongType())
        || type.equals(myScene.getPrimTypeCollector().getDoubleType())
        || type.equals(myScene.getPrimTypeCollector().getLong2ndHalfType())
        || type.equals(myScene.getPrimTypeCollector().getDouble2ndHalfType())) {
      return 2;
    } else {
      return 1;
    }
  }
}

class OutFlow {
  TypeStack typeStack;

  OutFlow(TypeStack typeStack) {
    this.typeStack = typeStack;
  }
}
