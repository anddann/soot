package soot.jimple.internal;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1999 Patrick Lam
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

import soot.Unit;
import soot.UnitBox;
import soot.UnitPrinter;
import soot.Value;
import soot.ValueBox;
import soot.baf.Baf;
import soot.baf.PlaceholderInst;
import soot.jimple.ConvertToBaf;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleToBafContext;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.StmtSwitch;
import soot.util.Switch;

public class JLookupSwitchStmt extends AbstractSwitchStmt implements LookupSwitchStmt {
  /**
   * List of lookup values from the corresponding bytecode instruction, represented as IntConstants.
   */
  List<IntConstant> lookupValues;

  // This method is necessary to deal with constructor-must-be-first-ism.
  private static UnitBox[] getTargetBoxesArray(List<? extends Unit> targets) {
    UnitBox[] targetBoxes = new UnitBox[targets.size()];
    for (int i = 0; i < targetBoxes.length; i++) {
      targetBoxes[i] = myJimple.newStmtBox(targets.get(i));
    }
    return targetBoxes;
  }

  public Object clone() {
    int lookupValueCount = lookupValues.size();
    List<IntConstant> clonedLookupValues = new ArrayList<IntConstant>(lookupValueCount);

    for (int i = 0; i < lookupValueCount; i++) {
      clonedLookupValues.add(i, IntConstant.v(getLookupValue(i)));
    }

    return new JLookupSwitchStmt(getKey(), clonedLookupValues, getTargets(), getDefaultTarget());
  }

  /** Constructs a new JLookupSwitchStmt. lookupValues should be a list of IntConst s. */
  public JLookupSwitchStmt(Value key, List<IntConstant> lookupValues, List<? extends Unit> targets, Unit defaultTarget) {
    this(myJimple.newImmediateBox(key), lookupValues, getTargetBoxesArray(targets), myJimple.newStmtBox(defaultTarget));
  }

  /** Constructs a new JLookupSwitchStmt. lookupValues should be a list of IntConst s. */
  public JLookupSwitchStmt(Value key, List<IntConstant> lookupValues, List<? extends UnitBox> targets,
      UnitBox defaultTarget) {
    this(myJimple.newImmediateBox(key), lookupValues, targets.toArray(new UnitBox[targets.size()]), defaultTarget);
  }

  protected JLookupSwitchStmt(ValueBox keyBox, List<IntConstant> lookupValues, UnitBox[] targetBoxes,
      UnitBox defaultTargetBox) {
    super(keyBox, defaultTargetBox, targetBoxes);
    setLookupValues(lookupValues);
  }

  public String toString() {
    StringBuffer buffer = new StringBuffer();
    String endOfLine = " ";

    buffer.append(Jimple.LOOKUPSWITCH + "(" + keyBox.getValue().toString() + ")" + endOfLine);

    buffer.append("{" + endOfLine);

    for (int i = 0; i < lookupValues.size(); i++) {
      Unit target = getTarget(i);
      buffer.append("    " + Jimple.CASE + " " + lookupValues.get(i) + ": " + Jimple.GOTO + " "
          + (target == this ? "self" : target) + ";" + endOfLine);
    }

    Unit target = getDefaultTarget();
    buffer.append("    " + Jimple.DEFAULT + ": " + Jimple.GOTO + " " + (target == this ? "self" : target) + ";" + endOfLine);

    buffer.append("}");

    return buffer.toString();
  }

  public void toString(UnitPrinter up) {
    up.literal(Jimple.LOOKUPSWITCH);
    up.literal("(");
    keyBox.toString(up);
    up.literal(")");
    up.newline();
    up.literal("{");
    up.newline();
    for (int i = 0; i < lookupValues.size(); i++) {
      up.literal("    ");
      up.literal(Jimple.CASE);
      up.literal(" ");
      up.constant(lookupValues.get(i));
      up.literal(": ");
      up.literal(Jimple.GOTO);
      up.literal(" ");
      targetBoxes[i].toString(up);
      up.literal(";");
      up.newline();
    }

    up.literal("    ");
    up.literal(Jimple.DEFAULT);
    up.literal(": ");
    up.literal(Jimple.GOTO);
    up.literal(" ");
    defaultTargetBox.toString(up);
    up.literal(";");
    up.newline();
    up.literal("}");
  }

  public void setLookupValues(List<IntConstant> lookupValues) {
    this.lookupValues = new ArrayList<IntConstant>(lookupValues);
  }

  public void setLookupValue(int index, int value) {
    lookupValues.set(index, IntConstant.v(value));
  }

  public int getLookupValue(int index) {
    return lookupValues.get(index).value;
  }

  public List<IntConstant> getLookupValues() {
    return Collections.unmodifiableList(lookupValues);
  }

  public void apply(Switch sw) {
    ((StmtSwitch) sw).caseLookupSwitchStmt(this);
  }

  public void convertToBaf(JimpleToBafContext context, List<Unit> out) {
    List<PlaceholderInst> targetPlaceholders = new ArrayList<PlaceholderInst>();

    ((ConvertToBaf) getKey()).convertToBaf(context, out);

    for (Unit target : getTargets()) {
      targetPlaceholders.add(myBaf.newPlaceholderInst(target));
    }

    Unit u
        = myBaf.newLookupSwitchInst(myBaf.newPlaceholderInst(getDefaultTarget()), getLookupValues(), targetPlaceholders);
    u.addAllTagsOf(this);
    out.add(u);
  }
}
