package soot.dexpler.instructions;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2012 Michael Markert, Frank Hartmann
 * 
 * (c) 2012 University of Luxembourg - Interdisciplinary Centre for
 * Security Reliability and Trust (SnT) - All rights reserved
 * Alexandre Bartel
 * 
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

import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.ThreeRegisterInstruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction23x;

import soot.Local;
import soot.PrimTypeCollector;
import soot.Type;
import soot.dexpler.DexBody;
import soot.dexpler.IDalvikTyper;
import soot.dexpler.tags.DoubleOpTag;
import soot.dexpler.tags.FloatOpTag;
import soot.dexpler.tags.LongOpTag;
import soot.dexpler.typing.DalvikTyper;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.Expr;
import soot.jimple.Jimple;
import soot.jimple.internal.JAssignStmt;
import soot.options.Options;

public class CmpInstruction extends TaggedInstruction {

  private PrimTypeCollector primTypeCollector;

  public CmpInstruction(Instruction instruction, int codeAdress, Options myOptions, PrimTypeCollector primTypeCollector) {
    super(instruction, codeAdress, myOptions);
    this.primTypeCollector = primTypeCollector;
  }

  @Override
  public void jimplify(DexBody body, Jimple myJimple, DalvikTyper myDalvikTyper) {
    if (!(instruction instanceof Instruction23x)) {
      throw new IllegalArgumentException("Expected Instruction23x but got: " + instruction.getClass());
    }

    Instruction23x cmpInstr = (Instruction23x) instruction;
    int dest = cmpInstr.getRegisterA();

    Local first = body.getRegisterLocal(cmpInstr.getRegisterB());
    Local second = body.getRegisterLocal(cmpInstr.getRegisterC());

    // Expr cmpExpr;
    // Type type = null
    Opcode opcode = instruction.getOpcode();
    Expr cmpExpr = null;
    Type type = null;
    switch (opcode) {
      case CMPL_DOUBLE:
        setTag(new DoubleOpTag());
        type = primTypeCollector.getDoubleType();
        cmpExpr = Jimple.newCmplExpr(first, second);
        break;
      case CMPL_FLOAT:
        setTag(new FloatOpTag());
        type = primTypeCollector.getFloatType();
        cmpExpr = Jimple.newCmplExpr(first, second);
        break;
      case CMPG_DOUBLE:
        setTag(new DoubleOpTag());
        type = primTypeCollector.getDoubleType();
        cmpExpr = Jimple.newCmpgExpr(first, second);
        break;
      case CMPG_FLOAT:
        setTag(new FloatOpTag());
        type = primTypeCollector.getFloatType();
        cmpExpr = Jimple.newCmpgExpr(first, second);
        break;
      case CMP_LONG:
        setTag(new LongOpTag());
        type = primTypeCollector.getLongType();
        cmpExpr = Jimple.newCmpExpr(first, second);
        break;
      default:
        throw new RuntimeException("no opcode for CMP: " + opcode);
    }

    AssignStmt assign = Jimple.newAssignStmt(body.getRegisterLocal(dest), cmpExpr);
    assign.addTag(getTag());

    setUnit(assign);
    addTags(assign);
    body.add(assign);

    if (IDalvikTyper.ENABLE_DVKTYPER) {
      getTag().getName();
      BinopExpr bexpr = (BinopExpr) cmpExpr;
      myDalvikTyper.setType(bexpr.getOp1Box(), type, true);
      myDalvikTyper.setType(bexpr.getOp2Box(), type, true);
      myDalvikTyper.setType(((JAssignStmt) assign).leftBox, primTypeCollector.getIntType(), false);
    }
  }

  @Override
  boolean overridesRegister(int register) {
    ThreeRegisterInstruction i = (ThreeRegisterInstruction) instruction;
    int dest = i.getRegisterA();
    return register == dest;
  }

}
