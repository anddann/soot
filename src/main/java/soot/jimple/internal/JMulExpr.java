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

import soot.PrimTypeCollector;
import soot.Type;
import soot.Value;
import soot.baf.Baf;
import soot.jimple.ExprSwitch;
import soot.jimple.Jimple;
import soot.jimple.MulExpr;
import soot.util.Switch;

public class JMulExpr extends AbstractJimpleFloatBinopExpr implements MulExpr {
  private final Jimple myJimple;

  public JMulExpr(Value op1, Value op2, Jimple myJimple, PrimTypeCollector primTypeCollector) {
    super(op1, op2, myJimple, primTypeCollector);
    this.myJimple = myJimple;
  }

  public final String getSymbol() {
    return " * ";
  }

  public void apply(Switch sw) {
    ((ExprSwitch) sw).caseMulExpr(this);
  }

  Object makeBafInst(Type opType, Baf myBaf) {
    return myBaf.newMulInst(this.getOp1().getType());
  }

  public Object clone() {
    return new JMulExpr(Jimple.cloneIfNecessary(getOp1()), Jimple.cloneIfNecessary(getOp2()),myJimple, primTypeCollector);
  }

}
