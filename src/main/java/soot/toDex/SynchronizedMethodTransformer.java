package soot.toDex;

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

import java.util.Iterator;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.Unit;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.Jimple;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

/**
 * The Dalvik VM requires synchronized methods to explicitly enter a monitor and leave it in a finally block again after
 * execution. See http://milk.com/kodebase/dalvik-docs-mirror/docs/debugger.html for more details
 *
 * @author Steven Arzt
 *
 */
public class SynchronizedMethodTransformer extends BodyTransformer {

  private Jimple myJimple;

  @Inject
  public SynchronizedMethodTransformer(Jimple myJimple) {
    this.myJimple = myJimple;
  }

  protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
    if (!b.getMethod().isSynchronized() || b.getMethod().isStatic()) {
      return;
    }

    Iterator<Unit> it = b.getUnits().snapshotIterator();
    while (it.hasNext()) {
      Unit u = it.next();
      if (u instanceof IdentityStmt) {
        continue;
      }

      // This the first real statement. If it is not a MonitorEnter
      // instruction, we generate one
      if (!(u instanceof EnterMonitorStmt)) {
        b.getUnits().insertBeforeNoRedirect(myJimple.newEnterMonitorStmt(b.getThisLocal()), u);

        // We also need to leave the monitor when the method terminates
        UnitGraph graph = new ExceptionalUnitGraph(b, myManager);
        for (Unit tail : graph.getTails()) {
          b.getUnits().insertBefore(myJimple.newExitMonitorStmt(b.getThisLocal()), tail);
        }
      }
      break;
    }
  }
}
