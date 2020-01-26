package soot.dava.internal.javaRep;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Jerome Miecznikowski
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

import soot.*;
import soot.grimp.Grimp;
import soot.grimp.internal.AbstractGrimpIntBinopExpr;
import soot.jimple.CmpgExpr;
import soot.jimple.ExprSwitch;
import soot.util.Switch;

public class DCmpgExpr extends AbstractGrimpIntBinopExpr implements CmpgExpr {
  private final Grimp myGrimp;

  public DCmpgExpr(Value op1, Value op2, Grimp myGrimp, PrimTypeCollector primTypeCollector) {
    super(op1, op2, myGrimp,primTypeCollector);
    this.myGrimp = myGrimp;
  }

  public final String getSymbol() {
    return " - ";
  }

  public final int getPrecedence() {
    return 700;
  }

  public void apply(Switch sw) {
    ((ExprSwitch) sw).caseCmpgExpr(this);
  }

  public Object clone() {
    return new DCmpgExpr(Grimp.cloneIfNecessary(getOp1()), Grimp.cloneIfNecessary(getOp2()), myGrimp,primTypeCollector);
  }

  public Type getType() {
    if (getOp1().getType().equals(getOp2().getType())) {
      return getOp1().getType();
    }

    return primTypeCollector.getIntType();
  }
}
