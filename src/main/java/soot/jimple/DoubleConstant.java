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
import soot.DoubleType;
import soot.PrimTypeCollector;
import soot.Type;
import soot.util.Switch;

/**
 * Floating point constant with double precision.
 */
public class DoubleConstant extends RealConstant {

  public final double value;
  private PrimTypeCollector primTypeCollector;

  @Inject 
  public DoubleConstant(double value, @Assisted PrimTypeCollector primTypeCollector) {
    this.value = value;
    this.primTypeCollector = primTypeCollector;
  }


  @Override
  public boolean equals(Object c) {
    return (c instanceof DoubleConstant && Double.compare(((DoubleConstant) c).value, this.value) == 0);
  }

  /**
   * Returns a hash code for this DoubleConstant object.
   */
  @Override
  public int hashCode() {
    long v = Double.doubleToLongBits(value);
    return (int) (v ^ (v >>> 32));
  }

  // PTC 1999/06/28
  @Override
  public NumericConstant add(NumericConstant c) {
    assertInstanceOf(c);
    return new DoubleConstant(this.value + ((DoubleConstant) c).value,this.primTypeCollector);
  }

  @Override
  public NumericConstant subtract(NumericConstant c) {
    assertInstanceOf(c);
    return new DoubleConstant(this.value - ((DoubleConstant) c).value,this.primTypeCollector);
  }

  @Override
  public NumericConstant multiply(NumericConstant c) {
    assertInstanceOf(c);
    return new DoubleConstant(this.value * ((DoubleConstant) c).value,this.primTypeCollector);
  }

  @Override
  public NumericConstant divide(NumericConstant c) {
    assertInstanceOf(c);
    return new DoubleConstant(this.value / ((DoubleConstant) c).value,this.primTypeCollector);
  }

  @Override
  public NumericConstant remainder(NumericConstant c) {
    assertInstanceOf(c);
    return new DoubleConstant(this.value % ((DoubleConstant) c).value,this.primTypeCollector);
  }

  @Override
  public NumericConstant equalEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant((Double.compare(this.value, ((DoubleConstant) c).value) == 0 ? 1 : 0),this.primTypeCollector);
  }

  @Override
  public NumericConstant notEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant((Double.compare(this.value, ((DoubleConstant) c).value) != 0 ? 1 : 0),this.primTypeCollector);
  }

  @Override
  public NumericConstant lessThan(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant((Double.compare(this.value, ((DoubleConstant) c).value) < 0 ? 1 : 0),this.primTypeCollector);
  }

  @Override
  public NumericConstant lessThanOrEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant((Double.compare(this.value, ((DoubleConstant) c).value) <= 0 ? 1 : 0),this.primTypeCollector);
  }

  @Override
  public NumericConstant greaterThan(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant((Double.compare(this.value, ((DoubleConstant) c).value) > 0 ? 1 : 0),this.primTypeCollector);
  }

  @Override
  public NumericConstant greaterThanOrEqual(NumericConstant c) {
    assertInstanceOf(c);
    return new IntConstant((Double.compare(this.value, ((DoubleConstant) c).value) >= 0 ? 1 : 0),this.primTypeCollector);
  }

  @Override
  public IntConstant cmpg(RealConstant constant) {
    assertInstanceOf(constant);
    final double cValue = ((DoubleConstant) constant).value;
    if (this.value < cValue) {
      return new IntConstant(-1,this.primTypeCollector);
    } else if (this.value == cValue) {
      return new IntConstant(0,this.primTypeCollector);
    } else {
      return new IntConstant(1,this.primTypeCollector);
    }
  }

  @Override
  public IntConstant cmpl(RealConstant constant) {
    assertInstanceOf(constant);
    final double cValue = ((DoubleConstant) constant).value;
    if (this.value > cValue) {
      return new IntConstant(1,this.primTypeCollector);
    } else if (this.value == cValue) {
      return new IntConstant(0,this.primTypeCollector);
    } else {
      return new IntConstant(-1,this.primTypeCollector);
    }
  }

  @Override
  public NumericConstant negate() {
    return new DoubleConstant(-(this.value),this.primTypeCollector);
  }

  @Override
  public String toString() {
    String doubleString = Double.toString(value);

    if (doubleString.equals("NaN") || doubleString.equals("Infinity") || doubleString.equals("-Infinity")) {
      return "#" + doubleString;
    } else {
      return doubleString;
    }
  }

  @Override
  public Type getType() {
    return primTypeCollector.getDoubleType();
  }

  @Override
  public void apply(Switch sw) {
    ((ConstantSwitch) sw).caseDoubleConstant(this);
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
    if (!(constant instanceof DoubleConstant)) {
      throw new IllegalArgumentException("DoubleConstant expected");
    }
  }

}
