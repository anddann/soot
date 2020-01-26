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
  private Jimple myJimple;
  private Baf myBaf;

  public JIfStmt(Value condition, Unit target, Jimple myJimple, Baf myBaf) {
    this(condition, myJimple.newStmtBox(target), myJimple, myBaf);
  }

  public JIfStmt(Value condition, UnitBox target, Jimple myJimple, Baf myBaf) {
    this(myJimple.newConditionExprBox(condition), target, myJimple, myBaf);
  }

  protected JIfStmt(ValueBox conditionBox, UnitBox targetBox, Jimple myJimple, Baf myBaf) {
    this.conditionBox = conditionBox;
    this.targetBox = targetBox;

    targetBoxes = Collections.singletonList(targetBox);
    this.myJimple = myJimple;
    this.myBaf = myBaf;
  }

  @Override
  public Object clone() {
    return new JIfStmt(Jimple.cloneIfNecessary(getCondition()), getTarget(), myJimple, myBaf);
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
  public void convertToBaf(final JimpleToBafContext context, final List<Unit> out, Baf myBaf, PrimTypeCollector primTypeCollector, ConstantFactory constantFactory, final Scene myScene) {
    Value cond = getCondition();

    final Value op1 = ((BinopExpr) cond).getOp1();
    final Value op2 = ((BinopExpr) cond).getOp2();

    context.setCurrentUnit(this);

    // Handle simple subcase where op1 is null
    if (op2 instanceof NullConstant || op1 instanceof NullConstant) {
      if (op2 instanceof NullConstant) {
        ((ConvertToBaf) op1).convertToBaf(context, out, this.myBaf, primTypeCollector, constantFactory, myScene);
      } else {
        ((ConvertToBaf) op2).convertToBaf(context, out, this.myBaf, primTypeCollector, constantFactory, myScene);
      }
      Unit u;

      if (cond instanceof EqExpr) {
        u = this.myBaf.newIfNullInst(this.myBaf.newPlaceholderInst(getTarget()));
      } else if (cond instanceof NeExpr) {
        u = this.myBaf.newIfNonNullInst(this.myBaf.newPlaceholderInst(getTarget()));
      } else {
        throw new RuntimeException("invalid condition");
      }

      u.addAllTagsOf(this);
      out.add(u);
      return;
    }

    // Handle simple subcase where op2 is 0
    if (op2 instanceof IntConstant && ((IntConstant) op2).value == 0) {
      ((ConvertToBaf) op1).convertToBaf(context, out, this.myBaf, primTypeCollector, constantFactory, myScene);

      cond.apply(new AbstractJimpleValueSwitch() {
        private void add(Unit u) {
          u.addAllTagsOf(JIfStmt.this);
          out.add(u);
        }

        @Override
        public void caseEqExpr(EqExpr expr) {
          add(JIfStmt.this.myBaf.newIfEqInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseNeExpr(NeExpr expr) {
          add(JIfStmt.this.myBaf.newIfNeInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLtExpr(LtExpr expr) {
          add(JIfStmt.this.myBaf.newIfLtInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLeExpr(LeExpr expr) {
          add(JIfStmt.this.myBaf.newIfLeInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGtExpr(GtExpr expr) {
          add(JIfStmt.this.myBaf.newIfGtInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGeExpr(GeExpr expr) {
          add(JIfStmt.this.myBaf.newIfGeInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }
      });

      return;
    }

    // Handle simple subcase where op1 is 0 (flip directions)
    if (op1 instanceof IntConstant && ((IntConstant) op1).value == 0) {
      ((ConvertToBaf) op2).convertToBaf(context, out, this.myBaf, primTypeCollector, constantFactory, myScene);

      cond.apply(new AbstractJimpleValueSwitch() {
        private void add(Unit u) {
          u.addAllTagsOf(JIfStmt.this);
          out.add(u);
        }

        @Override
        public void caseEqExpr(EqExpr expr) {
          add(JIfStmt.this.myBaf.newIfEqInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseNeExpr(NeExpr expr) {
          add(JIfStmt.this.myBaf.newIfNeInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLtExpr(LtExpr expr) {
          add(JIfStmt.this.myBaf.newIfGtInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseLeExpr(LeExpr expr) {
          add(JIfStmt.this.myBaf.newIfGeInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGtExpr(GtExpr expr) {
          add(JIfStmt.this.myBaf.newIfLtInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }

        @Override
        public void caseGeExpr(GeExpr expr) {
          add(JIfStmt.this.myBaf.newIfLeInst(JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
        }
      });

      return;
    }

    ((ConvertToBaf) op1).convertToBaf(context, out, this.myBaf, primTypeCollector, constantFactory, myScene);
    ((ConvertToBaf) op2).convertToBaf(context, out, this.myBaf, primTypeCollector, constantFactory, myScene);

    cond.apply(new AbstractJimpleValueSwitch() {
      private void add(Unit u) {
        u.addAllTagsOf(JIfStmt.this);
        out.add(u);
      }

      @Override
      public void caseEqExpr(EqExpr expr) {
        add(JIfStmt.this.myBaf.newIfCmpEqInst(op1.getType(myScene), JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseNeExpr(NeExpr expr) {
        add(JIfStmt.this.myBaf.newIfCmpNeInst(op1.getType(myScene), JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseLtExpr(LtExpr expr) {
        add(JIfStmt.this.myBaf.newIfCmpLtInst(op1.getType(myScene), JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseLeExpr(LeExpr expr) {
        add(JIfStmt.this.myBaf.newIfCmpLeInst(op1.getType(myScene), JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseGtExpr(GtExpr expr) {
        add(JIfStmt.this.myBaf.newIfCmpGtInst(op1.getType(myScene), JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
      }

      @Override
      public void caseGeExpr(GeExpr expr) {
        add(JIfStmt.this.myBaf.newIfCmpGeInst(op1.getType(myScene), JIfStmt.this.myBaf.newPlaceholderInst(getTarget())));
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
