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

@SuppressWarnings("serial")
abstract public class AbstractIntLongBinopExpr extends AbstractBinopExpr {

  public AbstractIntLongBinopExpr(ValueBox op1Box, ValueBox op2Box) {
    super(op1Box, op2Box);
  }

  public static boolean isIntLikeType(Type t) {
    PrimTypeCollector primTypeCollector =t.getMyScene().getPrimTypeCollector();
    return t.equals(primTypeCollector.getIntType()) || t.equals(primTypeCollector.getByteType()) || t.equals(primTypeCollector.getShortType()) || t.equals(primTypeCollector.getCharType())
        || t.equals(primTypeCollector.getBooleanType());
  }

  public Type getType() {
    Value op1 = op1Box.getValue();
    Value op2 = op2Box.getValue();
    PrimTypeCollector primTypeCollector =op1.getType().getMyScene().getPrimTypeCollector();

    if (isIntLikeType(op1.getType()) && isIntLikeType(op2.getType())) {
      return primTypeCollector.getIntType();
    } else if (op1.getType().equals(primTypeCollector.getLongType()) && op2.getType().equals(primTypeCollector.getLongType())) {
      return primTypeCollector.getLongType();
    } else {
      return primTypeCollector.getUnknownType();
    }
  }
}
