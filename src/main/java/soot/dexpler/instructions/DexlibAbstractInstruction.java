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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.jf.dexlib2.iface.instruction.FiveRegisterInstruction;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.RegisterRangeInstruction;

import soot.Type;
import soot.Unit;
import soot.dexpler.DexBody;
import soot.dexpler.typing.DalvikTyper;
import soot.jimple.Jimple;
import soot.options.Options;
import soot.tagkit.BytecodeOffsetTag;
import soot.tagkit.Host;
import soot.tagkit.LineNumberTag;
import soot.tagkit.SourceLineNumberTag;

/**
 * This class represents a wrapper around dexlib instruction.
 *
 */
public abstract class DexlibAbstractInstruction {

  protected int lineNumber = -1;

  protected final Instruction instruction;
  protected final int codeAddress;
  // protected Unit beginUnit;
  // protected Unit endUnit;
  protected Unit unit;
  private Options myOptions;

  public Instruction getInstruction() {
    return instruction;
  }

  /**
   * Jimplify this instruction.
   *  @param body
   *          to jimplify into.
   * @param myJimple
   * @param myDalvikTyper
   */
  public abstract void jimplify(DexBody body, Jimple myJimple, DalvikTyper myDalvikTyper);

  /**
   * Return the target register that is a copy of the given register. For instruction such as v0 = v3 (v0 gets the content of
   * v3), movesRegister(3) returns 0 movesRegister(0) returns -1
   *
   * Instructions should override this if they copy register content.
   *
   * @param register
   *          the number of the register
   * @return the new register number or -1 if it does not move.
   */
  int movesRegister(int register) {
    return -1;
  }

  /**
   * Return the source register that is moved to the given register. For instruction such as v0 = v3 (v0 gets the content of
   * v3), movesToRegister(3) returns -1 movesToRegister(0) returns 3
   *
   * Instructions should override this if they copy register content.
   *
   * @param register
   *          the number of the register
   * @return the source register number or -1 if it does not move.
   */
  int movesToRegister(int register) {
    return -1;
  }

  /**
   * Return if the instruction overrides the value in the register.
   *
   * Instructions should override this if they modify the registers.
   *
   * @param register
   *          the number of the register
   */
  boolean overridesRegister(int register) {
    return false;
  }

  /**
   * Return if the value in the register is used as a floating point.
   *
   * Instructions that have this context information and may deal with integers or floating points should override this.
   *
   * @param register
   *          the number of the register
   * @param body
   *          the body containing the instruction
   */
  boolean isUsedAsFloatingPoint(DexBody body, int register) {
    return false;
  }

  /**
   * Return the types that are be introduced by this instruction.
   *
   * Instructions that may introduce types should override this.
   */
  public Set<Type> introducedTypes() {
    return Collections.emptySet();
  }

  /**
   * @param instruction
   *          the underlying dexlib instruction
   * @param codeAddress
   * @param myOptions
   */
  public DexlibAbstractInstruction(Instruction instruction, int codeAddress, Options myOptions) {
    this.instruction = instruction;
    this.codeAddress = codeAddress;
    this.myOptions = myOptions;
  }

  public int getLineNumber() {
    return lineNumber;
  }

  public void setLineNumber(int lineNumber) {
    this.lineNumber = lineNumber;
  }

  /**
   * Tag the passed host with: - this instructions line number (if one is set) - the original bytecode offset
   *
   * @param host
   *          the host to tag
   */
  protected void addTags(Host host) {
    Options options = myOptions;
    if (options.keep_line_number() && lineNumber != -1) {
      host.addTag(new LineNumberTag(lineNumber));
      host.addTag(new SourceLineNumberTag(lineNumber));
    }
    if (options.keep_offset()) {
      host.addTag(new BytecodeOffsetTag(codeAddress));
    }
  }

  // /**
  // * Return the first of the jimple units that represent this instruction.
  // *
  // */
  // public Unit getBeginUnit() {
  // return beginUnit;
  // }
  //
  // /**
  // * Return the last of the jimple units that represent this instruction.
  // *
  // */
  // public Unit getEndUnit() {
  // return endUnit;
  // }
  public Unit getUnit() {
    return unit;
  }

  /**
   * Set the Jimple Unit, that comprises this instruction.
   *
   * Does not override already set units.
   */
  protected void setUnit(Unit u) {
    unit = u;
    // defineBlock(stmt, stmt);
  }

  // /**
  // * Set the first and last Jimple Unit, that comprise this instruction.
  // *
  // * Does not override already set units.
  // */
  // protected void defineBlock(Unit begin, Unit end) {
  // if (beginUnit == null)
  // beginUnit = begin;
  // if (endUnit == null)
  // endUnit = end;
  // }

  // FT
  // All uses for the array have been commented out.
  // Calling all v()s for all types make no sense if we do not use them
  /*
   * protected Type [] opUnType = { primeTypeCollector.getIntType(), // 0x7B neg-int vx, vy primeTypeCollector.getIntType(), // 0x7C primeTypeCollector.getLongType(), // 0x7D
   * primeTypeCollector.getLongType(), // 0x7E primeTypeCollector.getFloatType(), // 0x7F primeTypeCollector.getDoubleType(), // 0x80 primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(),
   * primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType(),
   * primeTypeCollector.getDoubleType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType() // 0x8F int-to-short vx, vy };
   *
   * protected Type [] resUnType = { primeTypeCollector.getIntType(), // 0x7B primeTypeCollector.getIntType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getFloatType(),
   * primeTypeCollector.getDoubleType(), primeTypeCollector.getLongType(), primeTypeCollector.getFloatType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getIntType(), primeTypeCollector.getFloatType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getIntType(),
   * primeTypeCollector.getLongType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getIntType(), primeTypeCollector.getLongType(), primeTypeCollector.getFloatType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType() // 0x8F };
   *
   * protected Type [] resBinType = { primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(),
   * primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(),
   * primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getFloatType(),
   * primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType(),
   * primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType() };
   *
   * protected Type [] op1BinType = { primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(),
   * primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(),
   * primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getFloatType(),
   * primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType(),
   * primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType() };
   *
   * protected Type [] op2BinType = { primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(),
   * primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(),
   * primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getLongType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getIntType(), primeTypeCollector.getFloatType(),
   * primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getFloatType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType(),
   * primeTypeCollector.getDoubleType(), primeTypeCollector.getDoubleType() };
   */

  // public abstract void getConstraint(IDalvikTyper myDalvikTyper());

  /**
   * Return the indices used in the given instruction.
   *
   * @param instruction
   *          a range invocation instruction
   * @return a list of register indices
   */
  protected List<Integer> getUsedRegistersNums(RegisterRangeInstruction instruction) {
    List<Integer> regs = new ArrayList<Integer>();
    int start = instruction.getStartRegister();
    for (int i = start; i < start + instruction.getRegisterCount(); i++) {
      regs.add(i);
    }

    return regs;
  }

  /**
   * Return the indices used in the given instruction.
   *
   * @param instruction
   *          a invocation instruction
   * @return a list of register indices
   */
  protected List<Integer> getUsedRegistersNums(FiveRegisterInstruction instruction) {
    int[] regs = { instruction.getRegisterC(), instruction.getRegisterD(), instruction.getRegisterE(),
        instruction.getRegisterF(), instruction.getRegisterG(), };
    List<Integer> l = new ArrayList<Integer>();
    for (int i = 0; i < instruction.getRegisterCount(); i++) {
      l.add(regs[i]);
    }
    return l;
  }

}
