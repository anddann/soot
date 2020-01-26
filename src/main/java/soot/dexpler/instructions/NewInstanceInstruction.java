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

import static soot.dexpler.Util.dottedClassName;

import java.util.HashSet;
import java.util.Set;

import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.OneRegisterInstruction;
import org.jf.dexlib2.iface.instruction.ReferenceInstruction;
import org.jf.dexlib2.iface.instruction.formats.Instruction21c;
import org.jf.dexlib2.iface.reference.TypeReference;

import soot.RefType;
import soot.Scene;
import soot.Type;
import soot.dexpler.DexBody;
import soot.dexpler.DexType;
import soot.dexpler.IDalvikTyper;
import soot.dexpler.typing.DalvikTyper;
import soot.jimple.AssignStmt;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.options.Options;

public class NewInstanceInstruction extends DexlibAbstractInstruction {

  private Jimple myJimple;
  private Scene myScene;
  private DalvikTyper myDalvikTyper;

  public NewInstanceInstruction(Instruction instruction, int codeAdress, Jimple myJimple, Options myOptions, Scene myScene, DalvikTyper myDalvikTyper) {
    super(instruction, codeAdress, myOptions);
    this.myJimple = myJimple;
    this.myScene = myScene;
    this.myDalvikTyper = myDalvikTyper;
  }

  @Override
  public void jimplify(DexBody body, Jimple myJimple, DalvikTyper myDalvikTyper) {
    Instruction21c i = (Instruction21c) instruction;
    int dest = i.getRegisterA();
    String className = dottedClassName(((TypeReference) (i.getReference())).toString(), myScene);
    RefType type = RefType.v(className,myScene);
    NewExpr n = Jimple.newNewExpr(type);
    AssignStmt assign = Jimple.newAssignStmt(body.getRegisterLocal(dest), n);
    setUnit(assign);
    addTags(assign);
    body.add(assign);

    if (IDalvikTyper.ENABLE_DVKTYPER) {
      // myDalvikTyper().captureAssign((JAssignStmt)assign, op); // TODO: ref. type may be null!
      this.myDalvikTyper.setType(assign.getLeftOpBox(), type, false);
    }
  }

  @Override
  boolean overridesRegister(int register) {
    OneRegisterInstruction i = (OneRegisterInstruction) instruction;
    int dest = i.getRegisterA();
    return register == dest;
  }

  @Override
  public Set<Type> introducedTypes() {
    ReferenceInstruction i = (ReferenceInstruction) instruction;

    Set<Type> types = new HashSet<Type>();
    types.add(DexType.toSoot((TypeReference) i.getReference()));
    return types;
  }
}
