package soot.jimple;

import java.util.List;

import soot.SootFieldRef;
import soot.SootMethodRef;
import soot.Type;
import soot.dexpler.typing.UntypedIntOrFloatConstant;
import soot.dexpler.typing.UntypedLongOrDoubleConstant;
import soot.shimple.toolkits.scalar.SEvaluator;

public interface ConstantFactory {

  public IntConstant createIntConstant(int value);

  public DoubleConstant createDoubleConstant(double value);

  public DoubleConstant createLongConstant(double value);

  public NullConstant createNullConstant();

  public FloatConstant createFloatConstant(float value);

  public StringConstant createStringConstant(String value);

  public ClassConstant createClassConstant(String value);

  public MethodType createMethodType(List<Type> paramaterTypes, Type returnType);

  public MethodHandle createMethodHandle(SootMethodRef ref, int tag);

  public MethodHandle createMethodHandle(SootFieldRef ref, int tag);

  public UntypedLongOrDoubleConstant createUntypedLongOrDoubleConstant(long value);

  public UntypedIntOrFloatConstant createUntypedIntOrFloatConstant(int value);

  public SEvaluator.TopConstant createTopConstant();

  public SEvaluator.BottomConstant createBottomConstant();

}
