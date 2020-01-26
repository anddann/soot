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
import soot.PrimTypeCollector;
import soot.Scene;
import soot.Type;
import soot.util.Switch;

public class NullConstant extends Constant {

  private PrimTypeCollector primTypeCollector;

  @Inject
  public NullConstant(PrimTypeCollector primTypeCollector) {
    this.primTypeCollector = primTypeCollector;
  }

  public boolean equals(Object c) {
    return c == this;
  }

  public int hashCode() {
    return 982;
  }

  public String toString() {
    return Jimple.NULL;
  }

  public Type getType(Scene myScene) {
    return primTypeCollector.getNullType();
  }

  public void apply(Switch sw) {
    ((ConstantSwitch) sw).caseNullConstant(this);
  }
}
