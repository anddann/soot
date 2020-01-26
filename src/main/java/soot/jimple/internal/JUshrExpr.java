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

import soot.Scene;
import soot.Type;
import soot.Value;
import soot.baf.Baf;
import soot.jimple.ExprSwitch;
import soot.jimple.Jimple;
import soot.jimple.UshrExpr;
import soot.util.Switch;

public class JUshrExpr extends AbstractJimpleIntLongBinopExpr implements UshrExpr {
  public JUshrExpr(Value op1, Value op2) {
    super(op1, op2, primTypeCollector, jimple);
  }

  public final String getSymbol() {
    return " >>> ";
  }

  public void apply(Switch sw) {
    ((ExprSwitch) sw).caseUshrExpr(this);
  }

  Object makeBafInst(Type opType, Baf myBaf) {
    return myBaf.newUshrInst(this.getOp1().getType(myScene));
  }

  public Type getType(Scene myScene) {
    Value op1 = op1Box.getValue();
    Value op2 = op2Box.getValue();

    if (!isIntLikeType(op2.getType(myScene))) {
      return primTypeCollector.getUnknownType();
    }

    if (isIntLikeType(op1.getType(myScene))) {
      return primTypeCollector.getIntType();
    }
    if (op1.getType(myScene).equals(primTypeCollector.getLongType())) {
      return primTypeCollector.getLongType();
    }

    return primTypeCollector.getUnknownType();
  }

  public Object clone() {
    return new JUshrExpr(Jimple.cloneIfNecessary(getOp1()), Jimple.cloneIfNecessary(getOp2()));
  }

}
