package soot.toolkits.scalar;

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
import java.util.BitSet;
import java.util.Iterator;
import java.util.Map;

import com.google.inject.Inject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.options.Options;
import soot.util.Chain;

/**
 * A BodyTransformer that removes all unused local variables from a given Body. Implemented as a singleton.
 * 
 * @see BodyTransformer
 * @see Body
 */
public class UnusedLocalEliminator extends BodyTransformer {
  private static final Logger logger = LoggerFactory.getLogger(UnusedLocalEliminator.class);
  private Options myOptions;


  @Inject
  public UnusedLocalEliminator(Options myOptions) {
    this.myOptions = myOptions;
  }


  @Override
  protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
    if (myOptions.verbose()) {
      logger.debug("[" + body.getMethod().getName() + "] Eliminating unused locals...");
    }

    int i = 0;
    int n = body.getLocals().size();
    int[] oldNumbers = new int[n];
    Chain<Local> locals = body.getLocals();
    for (Local local : locals) {
      oldNumbers[i] = local.getNumber();
      local.setNumber(i);
      i++;
    }

    BitSet usedLocals = new BitSet(n);

    // Traverse statements noting all the uses and defs
    for (Unit s : body.getUnits()) {
      for (ValueBox vb : s.getUseBoxes()) {
        Value v = vb.getValue();
        if (v instanceof Local) {
          Local l = (Local) v;
          assert locals.contains(l);
          usedLocals.set(l.getNumber());
        }
      }
      for (ValueBox vb : s.getDefBoxes()) {
        Value v = vb.getValue();
        if (v instanceof Local) {
          Local l = (Local) v;
          assert locals.contains(l);
          usedLocals.set(l.getNumber());
        }
      }
    }

    // Remove all locals that are unused.
    Iterator<Local> localIt = locals.iterator();
    while (localIt.hasNext()) {
      final Local local = localIt.next();
      final int lno = local.getNumber();
      if (!usedLocals.get(lno)) {
        localIt.remove();
      } else {
        local.setNumber(oldNumbers[lno]);
      }
    }
  }

}
