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

import java.util.List;

import soot.*;
import soot.baf.Baf;
import soot.jimple.*;
import soot.util.Switch;

public class JReturnStmt extends AbstractOpStmt implements ReturnStmt {

  public JReturnStmt(Value returnValue) {
    this(Jimple.newImmediateBox(returnValue));
  }

  protected JReturnStmt(ValueBox returnValueBox) {
    super(returnValueBox);
  }

  public Object clone() {
    return new JReturnStmt(Jimple.cloneIfNecessary(getOp()));
  }

  public String toString() {
    return Jimple.RETURN + " " + opBox.getValue().toString();
  }

  public void toString(UnitPrinter up) {
    up.literal(Jimple.RETURN);
    up.literal(" ");
    opBox.toString(up);
  }

  public void apply(Switch sw) {
    ((StmtSwitch) sw).caseReturnStmt(this);
  }

  public void convertToBaf(JimpleToBafContext context, List<Unit> out, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, final Scene myScene) {
    ((ConvertToBaf) (getOp())).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);

    Unit u = Baf.newReturnInst(getOp().getType());
    u.addAllTagsOf(this);
    out.add(u);
  }

  public boolean fallsThrough() {
    return false;
  }

  public boolean branches() {
    return false;
  }

}
