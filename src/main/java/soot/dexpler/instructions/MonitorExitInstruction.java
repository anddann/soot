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
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;

import soot.Local;
import soot.RefType;
import soot.Scene;
import soot.dexpler.DexBody;
import soot.dexpler.IDalvikTyper;
import soot.dexpler.typing.DalvikTyper;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.Jimple;
import soot.options.Options;

public class MonitorExitInstruction extends DexlibAbstractInstruction {

  private Jimple myJimple;
  private DalvikTyper myDalvikTyper;
  private Scene myScene;

  public MonitorExitInstruction(Instruction instruction, int codeAdress, Options myOptions, Jimple myJimple, DalvikTyper myDalvikTyper, Scene myScene) {
    super(instruction, codeAdress, myOptions);
    this.myJimple = myJimple;
    this.myDalvikTyper = myDalvikTyper;
    this.myScene = myScene;
  }

  @Override
  public void jimplify(DexBody body, Jimple myJimple, DalvikTyper myDalvikTyper) {
    int reg = ((OneRegisterInstruction) instruction).getRegisterA();
    Local object = body.getRegisterLocal(reg);
    ExitMonitorStmt exitMonitorStmt = Jimple.newExitMonitorStmt(object);
    setUnit(exitMonitorStmt);
    addTags(exitMonitorStmt);
    body.add(exitMonitorStmt);

    if (IDalvikTyper.ENABLE_DVKTYPER) {
      // Debug.printDbg(IDalvikTyper.DEBUG, "constraint: "+ exitMonitorStmt);
      this.myDalvikTyper.setType(exitMonitorStmt.getOpBox(), RefType.v("java.lang.Object",myScene), true);
    }
  }
}
