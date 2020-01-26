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
import soot.Scene;
import soot.Type;
import soot.util.Switch;

/**
 * Floating point constant with single precision.
 */
public class FloatConstant extends RealConstant {

  public final float value;
  private PrimTypeCollector primTypeCollector;

  @Inject
  public FloatConstant(float value, @Assisted PrimTypeCollector primTypeCollector) {
    this.value = value;
    this.primTypeCollector = primTypeCollector;
  }

  public boolean equals(Object c) {
    return c instanceof FloatConstant && Float.compare(((FloatConstant) c).value, value) == 0;
  }

  /**
   * Returns a hash code for this FloatConstant object.
   */
  @Override
  public int hashCode() {
    return Float.floatToIntBits(value);
  }

  // PTC 1999/06/28
  @Override
  public NumericConstant add(NumericConstant c) {
    assertInstanceOf(c);
    return new FloatConstant(this.value + ((FloatConstant) c).value, this.primTypeCollector);
  }

  @Override
  public NumericConstant subtract(NumericConstant c) {
    assertInstanceOf(c);
    return new FloatConstant(this.value - ((FloatConstant) c).value, this.primTypeCollector);
  }

  @Override
  public NumericConstant multiply(NumericConstant c) {
    assertInstanceOf(c);
    return new FloatConstant(this.value * ((FloatConstant) c).value, this.primTypeCollector);
  }

  @Override
  public NumericConstant divide(NumericConstant c) {
    assertInstanceOf(c);
    return new FloatConstant(this.value / ((FloatConstant) c).value, this.primTypeCollector);
  }

  @Override
  public NumericConstant remainder(NumericConstant c) {
    assertInstanceOf(c);
    return new FloatConstant(this.value % ((FloatConstant) c).value, this.primTypeCollector);
  }

  @Override
  public NumericConstant equalEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant(Float.compare(this.value, ((FloatConstant) c).value) == 0 ? 1 : 0, this.primTypeCollector);
  }

  @Override
  public NumericConstant notEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant(Float.compare(this.value, ((FloatConstant) c).value) != 0 ? 1 : 0, this.primTypeCollector);
  }

  @Override
  public NumericConstant lessThan(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant(Float.compare(this.value, ((FloatConstant) c).value) < 0 ? 1 : 0, this.primTypeCollector);
  }

  @Override
  public NumericConstant lessThanOrEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant(Float.compare(this.value, ((FloatConstant) c).value) <= 0 ? 1 : 0, this.primTypeCollector);
  }

  @Override
  public NumericConstant greaterThan(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant(Float.compare(this.value, ((FloatConstant) c).value) > 0 ? 1 : 0, this.primTypeCollector);
  }

  @Override
  public NumericConstant greaterThanOrEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant(Float.compare(this.value, ((FloatConstant) c).value) >= 0 ? 1 : 0, this.primTypeCollector);
  }

  @Override
  public IntConstant cmpg(RealConstant constant) {
    assertInstanceOf(constant);
    final float cValue = ((FloatConstant) constant).value;
    if (this.value < cValue) {
      return new IntConstant(-1, this.primTypeCollector);
    } else if (this.value == cValue) {
      return new IntConstant(0, this.primTypeCollector);
    } else {
      return new IntConstant(1, this.primTypeCollector);
    }
  }

  @Override
  public IntConstant cmpl(RealConstant constant) {
    assertInstanceOf(constant);
    final float cValue = ((FloatConstant) constant).value;
    if (this.value > cValue) {
      return new IntConstant(1, this.primTypeCollector);
    } else if (this.value == cValue) {
      return new IntConstant(0, this.primTypeCollector);
    } else {
      return new IntConstant(-1, this.primTypeCollector);
    }
  }

  @Override
  public NumericConstant negate() {
    return new FloatConstant(-(this.value), this.primTypeCollector);
  }

  @Override
  public String toString() {
    String floatString = Float.toString(value);

    if (floatString.equals("NaN") || floatString.equals("Infinity") || floatString.equals("-Infinity")) {
      return "#" + floatString + "F";
    } else {
      return floatString + "F";
    }
  }

  @Override
  public Type getType(Scene myScene) {
    return primTypeCollector.getFloatType();
  }

  @Override
  public void apply(Switch sw) {
    ((ConstantSwitch) sw).caseFloatConstant(this);
  }

  /**
   * Checks if passed argument is instance of expected class.
   *
   * @param constant
   *          the instance to check
   * @throws IllegalArgumentException
   *           when check fails
   */
  private void assertInstanceOf(NumericConstant constant) {
    if (!(constant instanceof FloatConstant)) {
      throw new IllegalArgumentException("FloatConstant expected");
    }
  }

}
