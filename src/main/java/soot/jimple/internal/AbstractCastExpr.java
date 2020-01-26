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
import java.util.List;

import soot.*;
import soot.baf.Baf;
import soot.grimp.PrecedenceTest;
import soot.jimple.*;
import soot.util.Switch;

@SuppressWarnings("serial")
abstract public class AbstractCastExpr implements CastExpr, ConvertToBaf {
  final ValueBox opBox;
  Type type;
  private Baf myBaf;

  AbstractCastExpr(Value op, Type type, Jimple myJimple, Baf myBaf) {
    this(myJimple.newImmediateBox(op), type, myBaf);
  }

  public abstract Object clone();

  protected AbstractCastExpr(ValueBox opBox, Type type, Baf myBaf) {
    this.opBox = opBox;
    this.type = type;
    this.myBaf = myBaf;
  }

  public boolean equivTo(Object o) {
    if (o instanceof AbstractCastExpr) {
      AbstractCastExpr ace = (AbstractCastExpr) o;
      return opBox.getValue().equivTo(ace.opBox.getValue()) && type.equals(ace.type);
    }
    return false;
  }

  /** Returns a hash code for this object, consistent with structural equality. */
  public int equivHashCode() {
    return opBox.getValue().equivHashCode() * 101 + type.hashCode() + 17;
  }

  public String toString() {
    return "(" + type.toString() + ") " + opBox.getValue().toString();
  }

  public void toString(UnitPrinter up) {
    up.literal("(");
    up.type(type);
    up.literal(") ");
    if (PrecedenceTest.needsBrackets(opBox, this)) {
      up.literal("(");
    }
    opBox.toString(up);
    if (PrecedenceTest.needsBrackets(opBox, this)) {
      up.literal(")");
    }
  }

  @Override
  public Value getOp() {
    return opBox.getValue();
  }

  @Override
  public void setOp(Value op) {
    opBox.setValue(op);
  }

  @Override
  public ValueBox getOpBox() {
    return opBox;
  }

  @Override
  public final List<ValueBox> getUseBoxes() {
    List<ValueBox> list = new ArrayList<ValueBox>();

    list.addAll(opBox.getValue().getUseBoxes());
    list.add(opBox);

    return list;
  }

  public Type getCastType() {
    return type;
  }

  public void setCastType(Type castType) {
    this.type = castType;
  }

  public Type getType(Scene myScene) {
    return type;
  }

  public void apply(Switch sw) {
    ((ExprSwitch) sw).caseCastExpr(this);
  }

  public void convertToBaf(JimpleToBafContext context, List<Unit> out, Baf myBaf, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, final Scene myScene) {
    final Type toType = getCastType();
    final Type fromType = getOp().getType(myScene);

    ((ConvertToBaf) getOp()).convertToBaf(context, out, this.myBaf, primTypeCollector, constantFactory, myScene);

    Unit u;
    if (toType instanceof ArrayType || toType instanceof RefType) {
      u = this.myBaf.newInstanceCastInst(toType);
    } else {
      if (!fromType.equals(toType)) {
        u = this.myBaf.newPrimitiveCastInst(fromType, toType);
      } else {
        u = this.myBaf.newNopInst();
      }
    }

    out.add(u);

    u.addAllTagsOf(context.getCurrentUnit());
  }
}
