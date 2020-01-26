package soot.dava.internal.javaRep;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2005 Nomair A. Naeem
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
import soot.jimple.internal.AbstractUnopExpr;
import soot.util.Switch;

//import soot.jimple.*;

public class DNotExpr extends AbstractUnopExpr {
  private Grimp myGrimp;

  public DNotExpr(Value op, Grimp myGrimp, PrimTypeCollector primTypeCollector) {
    super(myGrimp.newExprBox(op));
    this.myGrimp = myGrimp;
  }

  public Object clone() {
    return new DNotExpr(Grimp.cloneIfNecessary(getOpBox().getValue()), myGrimp, primTypeCollector);
  }

  public void toString(UnitPrinter up) {
    up.literal(" ! (");
    getOpBox().toString(up);
    up.literal(")");
  }

  public String toString() {
    return " ! (" + (getOpBox().getValue()).toString() + ")";
  }

  public Type getType() {
    Value op = getOpBox().getValue();

    if (op.getType().equals(primTypeCollector.getIntType()) || op.getType().equals(primTypeCollector.getByteType()) || op.getType().equals(primTypeCollector.getShortType())
        || op.getType().equals(primTypeCollector.getBooleanType()) || op.getType().equals(primTypeCollector.getCharType())) {
      return primTypeCollector.getIntType();
    } else if (op.getType().equals(primTypeCollector.getLongType())) {
      return primTypeCollector.getLongType();
    } else if (op.getType().equals(primTypeCollector.getDoubleType())) {
      return primTypeCollector.getDoubleType();
    } else if (op.getType().equals(primTypeCollector.getFloatType())) {
      return primTypeCollector.getFloatType();
    } else {
      return primTypeCollector.getUnknownType();
    }
  }

  /*
   * NOTE THIS IS AN EMPTY IMPLEMENTATION OF APPLY METHOD
   */
  public void apply(Switch sw) {
  }

  /** Compares the specified object with this one for structural equality. */
  public boolean equivTo(Object o) {
    if (o instanceof DNotExpr) {
      return getOpBox().getValue().equivTo(((DNotExpr) o).getOpBox().getValue());
    }
    return false;
  }

  /** Returns a hash code for this object, consistent with structural equality. */
  public int equivHashCode() {
    return getOpBox().getValue().equivHashCode();
  }
}
