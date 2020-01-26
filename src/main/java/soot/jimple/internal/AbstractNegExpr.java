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

import soot.*;
import soot.jimple.ExprSwitch;
import soot.jimple.Jimple;
import soot.jimple.NegExpr;
import soot.util.Switch;

@SuppressWarnings("serial")
public abstract class AbstractNegExpr extends AbstractUnopExpr implements NegExpr {
  protected AbstractNegExpr(ValueBox opBox, PrimTypeCollector primTypeCollector) {
    super(opBox, primTypeCollector);
  }

  /** Compares the specified object with this one for structural equality. */
  public boolean equivTo(Object o) {
    if (o instanceof AbstractNegExpr) {
      return opBox.getValue().equivTo(((AbstractNegExpr) o).opBox.getValue());
    }
    return false;
  }

  /** Returns a hash code for this object, consistent with structural equality. */
  public int equivHashCode() {
    return opBox.getValue().equivHashCode();
  }

  public abstract Object clone();

  public String toString() {
    return Jimple.NEG + " " + opBox.getValue().toString();
  }

  public void toString(UnitPrinter up) {
    up.literal(Jimple.NEG);
    up.literal(" ");
    opBox.toString(up);
  }

  public Type getType(Scene myScene) {
    Value op = opBox.getValue();

    if (op.getType(myScene).equals(primTypeCollector.getIntType()) || op.getType(myScene).equals(primTypeCollector.getByteType()) || op.getType(myScene).equals(primTypeCollector.getShortType())
        || op.getType(myScene).equals(primTypeCollector.getBooleanType()) || op.getType(myScene).equals(primTypeCollector.getCharType())) {
      return primTypeCollector.getIntType();
    } else if (op.getType(myScene).equals(primTypeCollector.getLongType())) {
      return primTypeCollector.getLongType();
    } else if (op.getType(myScene).equals(primTypeCollector.getDoubleType())) {
      return primTypeCollector.getDoubleType();
    } else if (op.getType(myScene).equals(primTypeCollector.getFloatType())) {
      return primTypeCollector.getFloatType();
    } else {
      return primTypeCollector.getUnknownType();
    }
  }

  public void apply(Switch sw) {
    ((ExprSwitch) sw).caseNegExpr(this);
  }
}
