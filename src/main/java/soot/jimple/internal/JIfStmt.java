package soot.jimple.internal;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1999 Patrick Lam
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
import java.util.Collections;
import java.util.List;

import soot.*;
import soot.baf.Baf;
import soot.jimple.*;
import soot.util.Switch;

public class JIfStmt extends AbstractStmt implements IfStmt {
  final ValueBox conditionBox;
  final UnitBox targetBox;

  final List<UnitBox> targetBoxes;

  public JIfStmt(Value condition, Unit target) {
    this(condition, Jimple.newStmtBox(target));
  }

  public JIfStmt(Value condition, UnitBox target) {
    this(Jimple.newConditionExprBox(condition), target);
  }

  protected JIfStmt(ValueBox conditionBox, UnitBox targetBox) {
    this.conditionBox = conditionBox;
    this.targetBox = targetBox;

    targetBoxes = Collections.singletonList(targetBox);
  }

  @Override
  public Object clone() {
    return new JIfStmt(Jimple.cloneIfNecessary(getCondition()), getTarget());
  }

  @Override
  public String toString() {
    Unit t = getTarget();
    String target = "(branch)";
    if (!t.branches()) {
      target = t.toString();
    }
    return Jimple.IF + " " + getCondition().toString() + " " + Jimple.GOTO + " " + target;
  }

  @Override
  public void toString(UnitPrinter up) {
    up.literal(Jimple.IF);
    up.literal(" ");
    conditionBox.toString(up);
    up.literal(" ");
    up.literal(Jimple.GOTO);
    up.literal(" ");
    targetBox.toString(up);
  }

  @Override
  public Value getCondition() {
    return conditionBox.getValue();
  }

  @Override
  public void setCondition(Value condition) {
    conditionBox.setValue(condition);
  }

  @Override
  public ValueBox getConditionBox() {
    return conditionBox;
  }

  @Override
  public Stmt getTarget() {
    return (Stmt) targetBox.getUnit();
  }

  @Override
  public void setTarget(Unit target) {
    targetBox.setUnit(target);
  }

  @Override
  public UnitBox getTargetBox() {
    return targetBox;
  }

  @Override
  public List<ValueBox> getUseBoxes() {
    List<ValueBox> useBoxes = new ArrayList<ValueBox>();

    useBoxes.addAll(conditionBox.getValue().getUseBoxes());
    useBoxes.add(conditionBox);

    return useBoxes;
  }

  @Override
  public final List<UnitBox> getUnitBoxes() {
    return targetBoxes;
  }

  @Override
  public void apply(Switch sw) {
    ((StmtSwitch) sw).caseIfStmt(this);
  }

  @Override
  public void convertToBaf(final JimpleToBafContext context, final List<Unit> out, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, final Scene myScene) {
    Value cond = getCondition();

    final Value op1 = ((BinopExpr) cond).getOp1();
    final Value op2 = ((BinopExpr) cond).getOp2();

    context.setCurrentUnit(this);

    // Handle simple subcase where op1 is null
    if (op2 instanceof NullConstant || op1 instanceof NullConstant) {
      if (op2 instanceof NullConstant) {
        ((ConvertToBaf) op1).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);
      } else {
        ((ConvertToBaf) op2).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);
      }
      Unit u;

      if (cond instanceof EqExpr) {
        u = Baf.newIfNullInst(Baf.newPlaceholderInst(getTarget()));
      } else if (cond instanceof NeExpr) {
        u = Baf.newIfNonNullInst(Baf.newPlaceholderInst(getTarget()));
      } else {
        throw new RuntimeException("invalid condition");
      }

      u.addAllTagsOf(this);
      out.add(u);
      return;
    }

    // Handle simple subcase where op2 is 0
    if (op2 instanceof IntConstant && ((IntConstant) op2).value == 0) {
      ((ConvertToBaf) op1).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);

      cond.apply(new AbstractJimpleValueSwitch() {
        private void add(Unit u) {
          u.addAllTagsOf(JIfStmt.this);
          out.add(u);
        }

        @Override
        public void caseEqExpr(EqExpr expr) {
          add(Baf.newIfEqInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseNeExpr(NeExpr expr) {
          add(Baf.newIfNeInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLtExpr(LtExpr expr) {
          add(Baf.newIfLtInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLeExpr(LeExpr expr) {
          add(Baf.newIfLeInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGtExpr(GtExpr expr) {
          add(Baf.newIfGtInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGeExpr(GeExpr expr) {
          add(Baf.newIfGeInst(Baf.newPlaceholderInst(getTarget())));
        }
      });

      return;
    }

    // Handle simple subcase where op1 is 0 (flip directions)
    if (op1 instanceof IntConstant && ((IntConstant) op1).value == 0) {
      ((ConvertToBaf) op2).convertToBaf(context, out, primTypeCollector,constantFactory,myScene);

      cond.apply(new AbstractJimpleValueSwitch() {
        private void add(Unit u) {
          u.addAllTagsOf(JIfStmt.this);
          out.add(u);
        }

        @Override
        public void caseEqExpr(EqExpr expr) {
          add(Baf.newIfEqInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseNeExpr(NeExpr expr) {
          add(Baf.newIfNeInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLtExpr(LtExpr expr) {
          add(Baf.newIfGtInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLeExpr(LeExpr expr) {
          add(Baf.newIfGeInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGtExpr(GtExpr expr) {
          add(Baf.newIfLtInst(Baf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGeExpr(GeExpr expr) {
          add(Baf.newIfLeInst(Baf.newPlaceholderInst(getTarget())));
        }
      });

      return;
    }

    ((ConvertToBaf) op1).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);
    ((ConvertToBaf) op2).convertToBaf(context, out, primTypeCollector, constantFactory, myScene);

    cond.apply(new AbstractJimpleValueSwitch() {
      private void add(Unit u) {
        u.addAllTagsOf(JIfStmt.this);
        out.add(u);
      }

      @Override
      public void caseEqExpr(EqExpr expr) {
        add(Baf.newIfCmpEqInst(op1.getType(), Baf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseNeExpr(NeExpr expr) {
        add(Baf.newIfCmpNeInst(op1.getType(), Baf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseLtExpr(LtExpr expr) {
        add(Baf.newIfCmpLtInst(op1.getType(), Baf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseLeExpr(LeExpr expr) {
        add(Baf.newIfCmpLeInst(op1.getType(), Baf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseGtExpr(GtExpr expr) {
        add(Baf.newIfCmpGtInst(op1.getType(), Baf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseGeExpr(GeExpr expr) {
        add(Baf.newIfCmpGeInst(op1.getType(), Baf.newPlaceholderInst(getTarget())));
      }
    });

  }

  @Override
  public boolean fallsThrough() {
    return true;
  }

  @Override
  public boolean branches() {
    return true;
  }

}
