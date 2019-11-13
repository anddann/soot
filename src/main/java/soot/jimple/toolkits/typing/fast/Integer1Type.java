package soot.jimple.toolkits.typing.fast;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2008 Ben Bellamy 
 * 
 * All rights reserved.
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

import soot.IntegerType;
import soot.PrimType;
import soot.RefType;
import soot.Scene;

/**
 * @author Ben Bellamy
 */
public class Integer1Type extends PrimType implements IntegerType {
  private static Integer1Type instance;

  private Integer1Type() {
  }

  public static Integer1Type v() {
    if (instance == null) {
      instance = new Integer1Type();
    }
    return instance;
  }

  public String toString() {
    return "[0..1]";
  }

  public boolean equals(Object t) {
    return this == t;
  }

  @Override
  public RefType boxedType(Scene myScene) {
    return RefType.v("java.lang.Integer", myScene);
  }

  @Override
  public boolean isAllowedInFinalCode() {
    return false;
  }

}