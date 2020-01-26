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
import soot.jimple.RemExpr;
import soot.util.Switch;

public class JRemExpr extends AbstractJimpleFloatBinopExpr implements RemExpr {
  private Jimple myJimple;

  public JRemExpr(Value op1, Value op2, PrimTypeCollector primTypeCollector, Jimple myJimple) {
    super(op1, op2, myJimple, primTypeCollector);
    this.myJimple = myJimple;
  }

  public String getSymbol() {
    return " % ";
  }

  public void apply(Switch sw) {
    ((ExprSwitch) sw).caseRemExpr(this);
  }

  Object makeBafInst(Type opType, Baf myBaf) {
    return myBaf.newRemInst(this.getOp1().getType(myScene));
  }

  public Object clone() {
    return new JRemExpr(Jimple.cloneIfNecessary(getOp1()), Jimple.cloneIfNecessary(getOp2()), primTypeCollector, myJimple);
  }

}
