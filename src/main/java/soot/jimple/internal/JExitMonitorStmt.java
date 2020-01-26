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

public class JExitMonitorStmt extends AbstractOpStmt implements ExitMonitorStmt {
  public JExitMonitorStmt(Value op) {
    this(myJimple.newImmediateBox(op));
  }

  protected JExitMonitorStmt(ValueBox opBox) {
    super(opBox);
  }

  public Object clone() {
    return new JExitMonitorStmt(Jimple.cloneIfNecessary(getOp()));
  }

  public String toString() {
    return Jimple.EXITMONITOR + " " + opBox.getValue().toString();
  }

  public void toString(UnitPrinter up) {
    up.literal(Jimple.EXITMONITOR);
    up.literal(" ");
    opBox.toString(up);
  }

  public void apply(Switch sw) {
    ((StmtSwitch) sw).caseExitMonitorStmt(this);

  }

  public void convertToBaf(JimpleToBafContext context, List<Unit> out, Baf myBaf, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, final Scene myScene) {
    ((ConvertToBaf) (getOp())).convertToBaf(context, out, myBaf, primTypeCollector, constantFactory, myScene);

    Unit u = myBaf.newExitMonitorInst();
    u.addAllTagsOf(this);
    out.add(u);
  }

  public boolean fallsThrough() {
    return true;
  }

  public boolean branches() {
    return false;
  }

}
