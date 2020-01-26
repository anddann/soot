package soot.dava.toolkits.base.misc;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2003 Jerome Miecznikowski
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

import java.util.ArrayList;
import java.util.Iterator;

import soot.NullType;
import soot.RefType;
import soot.Scene;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.dava.DavaBody;
import soot.dava.internal.javaRep.DNewInvokeExpr;
import soot.grimp.Grimp;
import soot.jimple.ThrowStmt;

public class ThrowNullConverter {

  private Grimp myGrimp;

  @Inject
  public ThrowNullConverter(Grimp myGrimp, Scene myScene) {
    this.myGrimp = myGrimp;
    this.myScene = myScene;
  }

  private Scene myScene;
  private final RefType npeRef = RefType.v(myScene.loadClassAndSupport("java.lang.NullPointerException"), myScene);

  public void convert(DavaBody body) {
    Iterator it = body.getUnits().iterator();
    while (it.hasNext()) {
      Unit u = (Unit) it.next();

      if (u instanceof ThrowStmt) {
        ValueBox opBox = ((ThrowStmt) u).getOpBox();
        Value op = opBox.getValue();

        if (op.getType(myScene) instanceof NullType) {
          opBox.setValue(new DNewInvokeExpr(npeRef, null, new ArrayList(), myGrimp));
        }
      }
    }
  }
}
