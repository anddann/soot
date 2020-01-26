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
public abstract class AbstractFloatBinopExpr extends AbstractBinopExpr {
    public AbstractFloatBinopExpr(ValueBox op1Box, ValueBox op2Box) {
        super(op1Box, op2Box);
    }

    public Type getType() {
        Value op1 = op1Box.getValue();
        Value op2 = op2Box.getValue();
        Type op1t = op1.getType();
        Type op2t = op2.getType();
        PrimTypeCollector primTypeCollector = op1.getType().getMyScene().getPrimTypeCollector();

        if ((op1t.equals(primTypeCollector.getIntType()) || op1t.equals(primTypeCollector.getByteType()) || op1t.equals(primTypeCollector.getShortType()) || op1t.equals(primTypeCollector.getCharType())
                || op1t.equals(primTypeCollector.getBooleanType()))
                && (op2t.equals(primTypeCollector.getIntType()) || op2t.equals(primTypeCollector.getByteType()) || op2t.equals(primTypeCollector.getShortType()) || op2t.equals(primTypeCollector.getCharType())
                || op2t.equals(primTypeCollector.getBooleanType()))) {
            return primTypeCollector.getIntType();
        } else if (op1t.equals(primTypeCollector.getLongType()) || op2t.equals(primTypeCollector.getLongType())) {
            return primTypeCollector.getLongType();
        } else if (op1t.equals(primTypeCollector.getDoubleType()) || op2t.equals(primTypeCollector.getDoubleType())) {
            return primTypeCollector.getDoubleType();
        } else if (op1t.equals(primTypeCollector.getFloatType()) || op2t.equals(primTypeCollector.getFloatType())) {
            return primTypeCollector.getFloatType();
        } else {
            return primTypeCollector.getUnknownType();
        }
    }
}
