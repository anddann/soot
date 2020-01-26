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
import java.util.List;

import soot.*;
import soot.baf.Baf;
import soot.jimple.*;
import soot.util.Switch;

public class JInvokeStmt extends AbstractStmt implements InvokeStmt {
  final ValueBox invokeExprBox;

  public JInvokeStmt(Value c) {
    this(Jimple.newInvokeExprBox(c));
  }

  protected JInvokeStmt(ValueBox invokeExprBox) {
    this.invokeExprBox = invokeExprBox;
  }

  public Object clone() {
    return new JInvokeStmt(Jimple.cloneIfNecessary(getInvokeExpr()));
  }

  public boolean containsInvokeExpr() {
    return true;
  }

  public String toString() {
    return invokeExprBox.getValue().toString();
  }

  public void toString(UnitPrinter up) {
    invokeExprBox.toString(up);
  }

  public void setInvokeExpr(Value invokeExpr) {
    invokeExprBox.setValue(invokeExpr);
  }

  public InvokeExpr getInvokeExpr() {
    return (InvokeExpr) invokeExprBox.getValue();
  }

  public ValueBox getInvokeExprBox() {
    return invokeExprBox;
  }

  public List<ValueBox> getUseBoxes() {
    List<ValueBox> list = new ArrayList<ValueBox>();

    list.addAll(invokeExprBox.getValue().getUseBoxes());
    list.add(invokeExprBox);

    return list;
  }

  public void apply(Switch sw) {
    ((StmtSwitch) sw).caseInvokeStmt(this);
  }

  public void convertToBaf(JimpleToBafContext context, List<Unit> out, Baf myBaf, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, final Scene myScene) {
    InvokeExpr ie = getInvokeExpr();

    context.setCurrentUnit(this);

    ((ConvertToBaf) ie).convertToBaf(context, out, myBaf, primTypeCollector, constantFactory, myScene);
    if (!ie.getMethodRef().returnType().equals(primTypeCollector.getVoidType())) {
      Unit u = myBaf.newPopInst(ie.getMethodRef().returnType());
      u.addAllTagsOf(this);
      out.add(u);
    }
  }

  public boolean fallsThrough() {
    return true;
  }

  public boolean branches() {
    return false;
  }

}
