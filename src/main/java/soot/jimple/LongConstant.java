package soot.jimple;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 1999 Raja Vallee-Rai
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

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

import soot.PrimTypeCollector;
import soot.Type;
import soot.util.Switch;

public class LongConstant extends ArithmeticConstant {
  public final long value;
  private PrimTypeCollector primTypeCollector;

  @Inject
  public LongConstant(long value, @Assisted PrimTypeCollector primTypeCollector) {
    this.value = value;
    this.primTypeCollector = primTypeCollector;
  }

  public boolean equals(Object c) {
    return c instanceof LongConstant && ((LongConstant) c).value == this.value;
  }

  /** Returns a hash code for this DoubleConstant object. */
  public int hashCode() {
    return (int) (value ^ (value >>> 32));
  }

  // PTC 1999/06/28
  public NumericConstant add(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value + ((LongConstant) c).value, this.primTypeCollector);
  }

  public NumericConstant subtract(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value - ((LongConstant) c).value, this.primTypeCollector);
  }

  public NumericConstant multiply(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value * ((LongConstant) c).value, this.primTypeCollector);
  }

  public NumericConstant divide(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value / ((LongConstant) c).value, this.primTypeCollector);
  }

  public NumericConstant remainder(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value % ((LongConstant) c).value, this.primTypeCollector);
  }

  public NumericConstant equalEqual(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new IntConstant((this.value == ((LongConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant notEqual(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new IntConstant((this.value != ((LongConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant lessThan(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new IntConstant((this.value < ((LongConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant lessThanOrEqual(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new IntConstant((this.value <= ((LongConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant greaterThan(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new IntConstant((this.value > ((LongConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant greaterThanOrEqual(NumericConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new IntConstant((this.value >= ((LongConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public IntConstant cmp(LongConstant c) {
    if (this.value > c.value) {
      return new IntConstant(1,this.primTypeCollector);
    } else if (this.value == c.value) {
      return new IntConstant(0,this.primTypeCollector);
    } else {
      return new IntConstant(-1,this.primTypeCollector);
    }
  }

  public NumericConstant negate() {
    return new LongConstant(-(this.value), this.primTypeCollector);
  }

  public ArithmeticConstant and(ArithmeticConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value & ((LongConstant) c).value, this.primTypeCollector);
  }

  public ArithmeticConstant or(ArithmeticConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value | ((LongConstant) c).value, this.primTypeCollector);
  }

  public ArithmeticConstant xor(ArithmeticConstant c) {
    if (!(c instanceof LongConstant)) {
      throw new IllegalArgumentException("LongConstant expected");
    }
    return new LongConstant(this.value ^ ((LongConstant) c).value, this.primTypeCollector);
  }

  public ArithmeticConstant shiftLeft(ArithmeticConstant c) {
    // NOTE CAREFULLY: the RHS of a shift op is not (!)
    // of Long type. It is, in fact, an IntConstant.

    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new LongConstant(this.value << ((IntConstant) c).value, this.primTypeCollector);
  }

  public ArithmeticConstant shiftRight(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new LongConstant(this.value >> ((IntConstant) c).value, this.primTypeCollector);
  }

  public ArithmeticConstant unsignedShiftRight(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new LongConstant(this.value >>> ((IntConstant) c).value, this.primTypeCollector);
  }

  public String toString() {
    return new Long(value).toString() + "L";
  }

  public Type getType() {
    return primTypeCollector.getLongType();
  }

  public void apply(Switch sw) {
    ((ConstantSwitch) sw).caseLongConstant(this);
  }
}
