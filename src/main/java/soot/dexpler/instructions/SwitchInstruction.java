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

import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.OffsetInstruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;

import soot.Local;
import soot.Unit;
import soot.dexpler.DexBody;
import soot.dexpler.typing.DalvikTyper;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.options.Options;

public abstract class SwitchInstruction extends PseudoInstruction implements DeferableInstruction {
  protected Unit markerUnit;
  protected Jimple myJimple;

  public SwitchInstruction(Instruction instruction, int codeAdress, Jimple myJimple, Options myOptions) {
    super(instruction, codeAdress, myOptions);
    this.myJimple = myJimple;
  }

  /**
   * Return a switch statement based on given target data on the given key.
   *
   */
  protected abstract Stmt switchStatement(DexBody body, Instruction targetData, Local key);

  public void jimplify(DexBody body, Jimple myJimple, DalvikTyper myDalvikTyper) {
    markerUnit = Jimple.newNopStmt();
    unit = markerUnit;
    body.add(markerUnit);
    body.addDeferredJimplification(this);
  }

  public void deferredJimplify(DexBody body) {
    int keyRegister = ((OneRegisterInstruction) instruction).getRegisterA();
    int offset = ((OffsetInstruction) instruction).getCodeOffset();
    Local key = body.getRegisterLocal(keyRegister);
    int targetAddress = codeAddress + offset;
    Instruction targetData = body.instructionAtAddress(targetAddress).instruction;
    Stmt stmt = switchStatement(body, targetData, key);
    body.getBody().getUnits().insertAfter(stmt, markerUnit);
  }

}
