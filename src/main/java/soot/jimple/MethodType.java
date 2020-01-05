package soot.jimple;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2005 - Jennifer Lhotak
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

import java.util.Collections;
import java.util.List;
import java.util.Objects;

import soot.RefType;
import soot.Scene;
import soot.SootMethod;
import soot.Type;
import soot.util.Switch;

public class MethodType extends Constant {

  private static final long serialVersionUID = 3523899677165980823L;
  protected Type returnType;
  protected List<Type> parameterTypes;
  private Scene myScene;

  @Inject
  private MethodType(List<Type> parameterTypes, Type returnType, @Assisted Scene myScene) {
    this.returnType = returnType;
    this.parameterTypes = parameterTypes;
    this.myScene = myScene;
  }

  public Type getType() {
    return RefType.v("java.lang.invoke.MethodType", myScene);
  }

  public String toString() {
    return "methodtype: " + SootMethod.getSubSignature("__METHODTYPE__", parameterTypes, returnType, myScene);
  }

  public List<Type> getParameterTypes() {
    return parameterTypes == null ? Collections.<Type>emptyList() : parameterTypes;
  }

  public Type getReturnType() {
    return returnType;
  }

  public void apply(Switch sw) {
    ((ConstantSwitch) sw).caseMethodType(this);
  }

  @Override
  public int hashCode() {
    int result = 17;
    result = 31 * result + Objects.hashCode(parameterTypes);
    result = 31 * result + Objects.hashCode(returnType);
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }
    MethodType other = (MethodType) obj;
    return Objects.equals(returnType, other.returnType) && Objects.equals(parameterTypes, other.parameterTypes);
  }

}