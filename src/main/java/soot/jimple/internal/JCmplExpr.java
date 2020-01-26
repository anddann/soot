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

import soot.Type;
import soot.Value;
import soot.baf.Baf;
import soot.jimple.CmplExpr;
import soot.jimple.ExprSwitch;
import soot.jimple.Jimple;
import soot.util.Switch;

public class JCmplExpr extends AbstractJimpleIntBinopExpr implements CmplExpr {
  public JCmplExpr(Value op1, Value op2) {
    super(op1, op2);
  }

  public final String getSymbol() {
    return " " + Jimple.CMPL + " ";
  }

  public void apply(Switch sw) {
    ((ExprSwitch) sw).caseCmplExpr(this);
  }

  Object makeBafInst(Type opType, Baf myBaf) {
    return myBaf.newCmplInst(this.getOp1().getType());
  }

  public Object clone() {
    return new JCmplExpr(Jimple.cloneIfNecessary(getOp1()), Jimple.cloneIfNecessary(getOp2()));
  }

}
