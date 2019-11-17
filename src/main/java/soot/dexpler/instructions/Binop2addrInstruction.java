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
import org.jf.dexlib2.iface.instruction.TwoRegisterInstruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction12x;

import soot.Local;
import soot.Value;
import soot.dexpler.DexBody;
import soot.dexpler.tags.DoubleOpTag;
import soot.dexpler.tags.FloatOpTag;
import soot.dexpler.tags.IntOpTag;
import soot.dexpler.tags.LongOpTag;
import soot.jimple.AssignStmt;
import soot.jimple.Jimple;

public class Binop2addrInstruction extends TaggedInstruction {

  public Binop2addrInstruction(Instruction instruction, int codeAdress) {
    super(instruction, codeAdress);
  }

  @Override
  public void jimplify(DexBody body) {
    if (!(instruction instanceof Instruction12x)) {
      throw new IllegalArgumentException("Expected Instruction12x but got: " + instruction.getClass());
    }

    Instruction12x binOp2AddrInstr = (Instruction12x) instruction;
    int dest = binOp2AddrInstr.getRegisterA();

    Local source1 = body.getRegisterLocal(binOp2AddrInstr.getRegisterA());
    Local source2 = body.getRegisterLocal(binOp2AddrInstr.getRegisterB());

    Value expr = getExpression(source1, source2);

    AssignStmt assign = myJimple.newAssignStmt(body.getRegisterLocal(dest), expr);
    assign.addTag(getTag());

    setUnit(assign);
    addTags(assign);
    body.add(assign);

    /*
     * if (IDalvikTyper.ENABLE_DVKTYPER) { BinopExpr bexpr = (BinopExpr)expr; short op = instruction.getOpcode().value;
     * myDalvikTyper().setType(bexpr.getOp1Box(), op1BinType[op-0xb0], true); myDalvikTyper().setType(bexpr.getOp2Box(),
     * op2BinType[op-0xb0], true); myDalvikTyper().setType(assign.getLeftOpBox(), resBinType[op-0xb0], false); }
     */
  }

  private Value getExpression(Local source1, Local source2) {
    Opcode opcode = instruction.getOpcode();
    switch (opcode) {
      case ADD_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newAddExpr(source1, source2);
      case ADD_FLOAT_2ADDR:
        setTag(new FloatOpTag());
        return myJimple.newAddExpr(source1, source2);
      case ADD_DOUBLE_2ADDR:
        setTag(new DoubleOpTag());
        return myJimple.newAddExpr(source1, source2);
      case ADD_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newAddExpr(source1, source2);

      case SUB_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newSubExpr(source1, source2);
      case SUB_FLOAT_2ADDR:
        setTag(new FloatOpTag());
        return myJimple.newSubExpr(source1, source2);
      case SUB_DOUBLE_2ADDR:
        setTag(new DoubleOpTag());
        return myJimple.newSubExpr(source1, source2);
      case SUB_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newSubExpr(source1, source2);

      case MUL_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newMulExpr(source1, source2);
      case MUL_FLOAT_2ADDR:
        setTag(new FloatOpTag());
        return myJimple.newMulExpr(source1, source2);
      case MUL_DOUBLE_2ADDR:
        setTag(new DoubleOpTag());
        return myJimple.newMulExpr(source1, source2);
      case MUL_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newMulExpr(source1, source2);

      case DIV_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newDivExpr(source1, source2);
      case DIV_FLOAT_2ADDR:
        setTag(new FloatOpTag());
        return myJimple.newDivExpr(source1, source2);
      case DIV_DOUBLE_2ADDR:
        setTag(new DoubleOpTag());
        return myJimple.newDivExpr(source1, source2);
      case DIV_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newDivExpr(source1, source2);

      case REM_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newRemExpr(source1, source2);
      case REM_FLOAT_2ADDR:
        setTag(new FloatOpTag());
        return myJimple.newRemExpr(source1, source2);
      case REM_DOUBLE_2ADDR:
        setTag(new DoubleOpTag());
        return myJimple.newRemExpr(source1, source2);
      case REM_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newRemExpr(source1, source2);

      case AND_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newAndExpr(source1, source2);
      case AND_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newAndExpr(source1, source2);

      case OR_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newOrExpr(source1, source2);
      case OR_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newOrExpr(source1, source2);

      case XOR_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newXorExpr(source1, source2);
      case XOR_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newXorExpr(source1, source2);

      case SHL_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newShlExpr(source1, source2);
      case SHL_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newShlExpr(source1, source2);

      case SHR_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newShrExpr(source1, source2);
      case SHR_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newShrExpr(source1, source2);

      case USHR_LONG_2ADDR:
        setTag(new LongOpTag());
        return myJimple.newUshrExpr(source1, source2);
      case USHR_INT_2ADDR:
        setTag(new IntOpTag());
        return myJimple.newUshrExpr(source1, source2);

      default:
        throw new RuntimeException("Invalid Opcode: " + opcode);
    }
  }

  @Override
  boolean overridesRegister(int register) {
    TwoRegisterInstruction i = (TwoRegisterInstruction) instruction;
    int dest = i.getRegisterA();
    return register == dest;
  }

}
