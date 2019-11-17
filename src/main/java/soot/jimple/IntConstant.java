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

import com.google.inject.assistedinject.Assisted;

import soot.IntType;
import soot.PrimTypeCollector;
import soot.Type;
import soot.util.Switch;

public class IntConstant extends ArithmeticConstant {
  public final int value;
  private PrimTypeCollector primTypeCollector;

  protected IntConstant(int value, @Assisted PrimTypeCollector primTypeCollector) {
    this.value = value;
    this.primTypeCollector = primTypeCollector;
  }

  public boolean equals(Object c) {
    return c instanceof IntConstant && ((IntConstant) c).value == value;
  }

  public int hashCode() {
    return value;
  }

  // PTC 1999/06/28
  public NumericConstant add(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value + ((IntConstant) c).value, this.primTypeCollector);
  }

  public NumericConstant subtract(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value - ((IntConstant) c).value,this.primTypeCollector);
  }

  public NumericConstant multiply(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value * ((IntConstant) c).value,this.primTypeCollector);
  }

  public NumericConstant divide(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value / ((IntConstant) c).value,this.primTypeCollector);
  }

  public NumericConstant remainder(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value % ((IntConstant) c).value,this.primTypeCollector);
  }

  public NumericConstant equalEqual(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant((this.value == ((IntConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant notEqual(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant((this.value != ((IntConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant lessThan(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant((this.value < ((IntConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant lessThanOrEqual(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant((this.value <= ((IntConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant greaterThan(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant((this.value > ((IntConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant greaterThanOrEqual(NumericConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant((this.value >= ((IntConstant) c).value) ? 1 : 0,this.primTypeCollector);
  }

  public NumericConstant negate() {
    return new IntConstant(-(this.value),this.primTypeCollector);
  }

  public ArithmeticConstant and(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value & ((IntConstant) c).value,this.primTypeCollector);
  }

  public ArithmeticConstant or(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value | ((IntConstant) c).value,this.primTypeCollector);
  }

  public ArithmeticConstant xor(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value ^ ((IntConstant) c).value,this.primTypeCollector);
  }

  public ArithmeticConstant shiftLeft(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value << ((IntConstant) c).value,this.primTypeCollector);
  }

  public ArithmeticConstant shiftRight(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value >> ((IntConstant) c).value,this.primTypeCollector);
  }

  public ArithmeticConstant unsignedShiftRight(ArithmeticConstant c) {
    if (!(c instanceof IntConstant)) {
      throw new IllegalArgumentException("IntConstant expected");
    }
    return new IntConstant(this.value >>> ((IntConstant) c).value,this.primTypeCollector);
  }

  public String toString() {
    return new Integer(value).toString();
  }

  public Type getType() {
    return primTypeCollector.getIntType();
  }

  public void apply(Switch sw) {
    ((ConstantSwitch) sw).caseIntConstant(this);
  }

}
