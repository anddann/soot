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
import java.util.List;

import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.SwitchElement;
import org.jf.dexlib2.iface.instruction.formats.SparseSwitchPayload;

import soot.Local;
import soot.PrimTypeCollector;
import soot.Unit;
import soot.dexpler.DexBody;
import soot.dexpler.IDalvikTyper;
import soot.dexpler.typing.DalvikTyper;
import soot.jimple.ConstantFactory;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.Stmt;
import soot.options.Options;

public class SparseSwitchInstruction extends SwitchInstruction {

  private ConstantFactory constancFactory;
  private DalvikTyper myDalvikTyper;
  private PrimTypeCollector primTypeCollector;

  public SparseSwitchInstruction(Instruction instruction, int codeAdress, Jimple myJimple, ConstantFactory constancFactory, DalvikTyper myDalvikTyper, PrimTypeCollector primTypeCollector, Options myOptions) {
    super(instruction, codeAdress, myJimple, myOptions);
    this.constancFactory = constancFactory;
    this.myDalvikTyper = myDalvikTyper;
    this.primTypeCollector = primTypeCollector;
  }

  @Override
  protected Stmt switchStatement(DexBody body, Instruction targetData, Local key) {
    SparseSwitchPayload i = (SparseSwitchPayload) targetData;
    List<? extends SwitchElement> seList = i.getSwitchElements();

    // the default target always follows the switch statement
    int defaultTargetAddress = codeAddress + instruction.getCodeUnits();
    Unit defaultTarget = body.instructionAtAddress(defaultTargetAddress).getUnit();

    List<IntConstant> lookupValues = new ArrayList<IntConstant>();
    List<Unit> targets = new ArrayList<Unit>();
    for (SwitchElement se : seList) {
      lookupValues.add(constancFactory.createIntConstant(se.getKey()));
      int offset = se.getOffset();
      targets.add(body.instructionAtAddress(codeAddress + offset).getUnit());
    }
    LookupSwitchStmt switchStmt = myJimple.newLookupSwitchStmt(key, lookupValues, targets, defaultTarget);
    setUnit(switchStmt);
    addTags(switchStmt);

    if (IDalvikTyper.ENABLE_DVKTYPER) {
      myDalvikTyper.setType(switchStmt.getKeyBox(), primTypeCollector.getIntType(), true);
    }

    return switchStmt;
  }

  @Override
  public void computeDataOffsets(DexBody body) {
    // System.out.println("class of instruction: "+ instruction.getClass());
    // int offset = ((OffsetInstruction) instruction).getCodeOffset();
    // int targetAddress = codeAddress + offset;
    // Instruction targetData = body.instructionAtAddress(targetAddress).instruction;
    // SparseSwitchPayload ssInst = (SparseSwitchPayload) targetData;
    // List<? extends SwitchElement> targetAddresses = ssInst.getSwitchElements();
    // int size = targetAddresses.size() * 2; // @ are on 32bits
    //
    // // From org.jf.dexlib.Code.Format.SparseSwitchDataPseudoInstruction we learn
    // // that there are 2 bytes after the magic number that we have to jump.
    // // 2 bytes to jump = address + 1
    // //
    // // out.writeByte(0x00); // magic
    // // out.writeByte(0x02); // number
    // // out.writeShort(targets.length); // 2 bytes
    // // out.writeInt(firstKey);
    //
    // setDataFirstByte (targetAddress + 1);
    // setDataLastByte (targetAddress + 1 + size - 1);
    // setDataSize (size);
    //
    // ByteArrayAnnotatedOutput out = new ByteArrayAnnotatedOutput();
    // ssInst.write(out, targetAddress);
    //
    // byte[] outa = out.getArray();
    // byte[] data = new byte[outa.length-2];
    // for (int i=2; i<outa.length; i++) {
    // data[i-2] = outa[i];
    // }
    // setData (data);
  }

}
