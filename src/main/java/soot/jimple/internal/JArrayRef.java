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
import java.util.Iterator;
import java.util.List;

import soot.ArrayType;
import soot.Local;
import soot.PrimTypeCollector;
import soot.Scene;
import soot.Type;
import soot.Unit;
import soot.UnitPrinter;
import soot.Value;
import soot.ValueBox;
import soot.jimple.*;
import soot.tagkit.Tag;
import soot.util.Switch;

public class JArrayRef implements ArrayRef, ConvertToBaf {
    protected ValueBox baseBox;
    protected ValueBox indexBox;

    public JArrayRef(Value base, Value index) {
        this(Jimple.newLocalBox(base), Jimple.newImmediateBox(index));
    }

    protected JArrayRef(ValueBox baseBox, ValueBox indexBox) {
        this.baseBox = baseBox;
        this.indexBox = indexBox;
    }

    public Object clone() {
        return new JArrayRef(Jimple.cloneIfNecessary(getBase()), Jimple.cloneIfNecessary(getIndex()));
    }

    public boolean equivTo(Object o) {
        if (o instanceof ArrayRef) {
            return (getBase().equivTo(((ArrayRef) o).getBase()) && getIndex().equivTo(((ArrayRef) o).getIndex()));
        }
        return false;
    }

    /**
     * Returns a hash code for this object, consistent with structural equality.
     */
    public int equivHashCode() {
        return getBase().equivHashCode() * 101 + getIndex().equivHashCode() + 17;
    }

    public String toString() {
        return baseBox.getValue().toString() + "[" + indexBox.getValue().toString() + "]";
    }

    public void toString(UnitPrinter up) {
        baseBox.toString(up);
        up.literal("[");
        indexBox.toString(up);
        up.literal("]");
    }

    public Value getBase() {
        return baseBox.getValue();
    }

    public void setBase(Local base) {
        baseBox.setValue(base);
    }

    public ValueBox getBaseBox() {
        return baseBox;
    }

    public Value getIndex() {
        return indexBox.getValue();
    }

    public void setIndex(Value index) {
        indexBox.setValue(index);
    }

    public ValueBox getIndexBox() {
        return indexBox;
    }

    public List getUseBoxes() {
        List useBoxes = new ArrayList();

        useBoxes.addAll(baseBox.getValue().getUseBoxes());
        useBoxes.add(baseBox);

        useBoxes.addAll(indexBox.getValue().getUseBoxes());
        useBoxes.add(indexBox);

        return useBoxes;
    }

    public Type getType() {
        Value base = baseBox.getValue();
        Type type = base.getType();
        PrimTypeCollector primTypeCollector = base.getType().getMyScene().getPrimTypeCollector();

        if (type.equals(primTypeCollector.getUnknownType())) {
            return primTypeCollector.getUnknownType();
        } else if (type.equals(primTypeCollector.getNullType())) {
            return primTypeCollector.getNullType();
        } else {
            // use makeArrayType on non-array type references when they propagate to this point.
            // kludge, most likely not correct.
            // may stop spark from complaining when it gets passed phantoms.
            // ideally I'd want to find out just how they manage to get this far.
            ArrayType arrayType;
            if (type instanceof ArrayType) {
                arrayType = (ArrayType) type;
            } else {
                arrayType = (ArrayType) type.makeArrayType();
            }

            if (arrayType.numDimensions == 1) {
                return arrayType.baseType;
            } else {
                return ArrayType.v(arrayType.baseType, arrayType.numDimensions - 1);
            }
        }
    }

    public void apply(Switch sw) {
        ((RefSwitch) sw).caseArrayRef(this);
    }

    public void convertToBaf(JimpleToBafContext context, List<Unit> out, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, final Scene myScene) {
        ((ConvertToBaf) getBase()).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);
        ((ConvertToBaf) getIndex()).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);

        Unit currentUnit = context.getCurrentUnit();

        Unit x;

        out.add(x = Baf.newArrayReadInst(getType()));

        Iterator it = currentUnit.getTags().iterator();
        while (it.hasNext()) {
            x.addTag((Tag) it.next());
        }

    }
}
