package soot.jimple.spark.internal;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2002 Ondrej Lhotak
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

import soot.SootField;
import soot.SootMethod;

/**
 * Using this oracle one assumes, that a client of the target library can call every method and access every field.
 * 
 * @author Florian Kuebler
 *
 */
public class CompleteAccessibility implements ClientAccessibilityOracle {

  @Inject
  public CompleteAccessibility() {
  }

  @Override
  public boolean isAccessible(SootMethod method) {
    return true;
  }

  @Override
  public boolean isAccessible(SootField field) {
    return true;
  }

}
