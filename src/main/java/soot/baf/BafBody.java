package soot.baf;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1999 Patrick Lam, Patrick Pominville and Raja Vallee-Rai
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.*;
import soot.baf.internal.BafLocal;
import soot.jimple.*;
import soot.options.Options;

public class BafBody extends Body {
  private static final Logger logger = LoggerFactory.getLogger(BafBody.class);


  private JimpleToBafContext jimpleToBafContext;

  public JimpleToBafContext getContext() {
    return jimpleToBafContext;
  }

  @Override
  public Object clone() {
    Body b = new BafBody(getMethod(), getMyOptions(), getMyPrinter());
    b.importBodyContentsFrom(this);
    return b;
  }

  BafBody(SootMethod m, Options myOptions, Printer myPrinter) {
    super(m, myOptions, myPrinter);
  }

  public BafBody(JimpleBody body, Map<String, String> options, Options myOptions, Printer myPrinter,
                 PackManager myPackManager, Scene myScene, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory) {
    super(body.getMethod(), myOptions, myPrinter);
    if (myOptions.verbose()) {
      logger.debug("[" + getMethod().getName() + "] Constructing BafBody...");
    }

    JimpleBody jimpleBody = (JimpleBody) body;

    JimpleToBafContext context = new JimpleToBafContext(jimpleBody.getLocalCount());
    this.jimpleToBafContext = context;
    // Convert all locals
    {
      for (Local l : jimpleBody.getLocals()) {
        Type t = l.getType();
        Local newLocal = Baf.newLocal(l.getName(), primTypeCollector.getUnknownType());

        if (t.equals(primTypeCollector.getDoubleType()) || t.equals(primTypeCollector.getLongType())) {
          newLocal.setType(primTypeCollector.getDoubleWordType());
        } else {
          newLocal.setType(primTypeCollector.getWordType());
        }

        context.setBafLocalOfJimpleLocal(l, newLocal);

        // We cannot use the context for the purpose of saving the old Jimple locals, because
        // some transformers in the bb-pack, which is called at the end of the method
        // copy the locals, thus invalidating the information in a map.
        ((BafLocal) newLocal).setOriginalLocal(l);
        getLocals().add(newLocal);
      }
    }

    Map<Stmt, Unit> stmtToFirstInstruction = new HashMap<Stmt, Unit>();

    // Convert all jimple instructions
    {
      for (Unit u : jimpleBody.getUnits()) {
        Stmt s = (Stmt) u;
        List<Unit> conversionList = new ArrayList<Unit>();

        context.setCurrentUnit(s);
        ((ConvertToBaf) s).convertToBaf(context, conversionList, primTypeCollector, constantFactory, myScene);

        stmtToFirstInstruction.put(s, conversionList.get(0));
        getUnits().addAll(conversionList);
      }
    }

    // Change all place holders
    {
      for (UnitBox box : getAllUnitBoxes()) {
        if (box.getUnit() instanceof PlaceholderInst) {
          Unit source = ((PlaceholderInst) box.getUnit()).getSource();
          box.setUnit(stmtToFirstInstruction.get(source));
        }
      }
    }

    // Convert all traps
    {
      for (Trap trap : jimpleBody.getTraps()) {
        getTraps().add(Baf.newTrap(trap.getException(), stmtToFirstInstruction.get(trap.getBeginUnit()),
            stmtToFirstInstruction.get(trap.getEndUnit()), stmtToFirstInstruction.get(trap.getHandlerUnit())));
      }
    }

    myPackManager.getPack("bb").apply(this);
  }
}
