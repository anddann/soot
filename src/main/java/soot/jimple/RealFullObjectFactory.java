package soot.jimple;

import com.google.inject.Inject;
import com.google.inject.Provider;

import soot.RefType;
import soot.Scene;
import soot.jimple.toolkits.pointer.FullObjectSet;

public class RealFullObjectFactory implements FullObjectFactory {
  private final Provider<Scene> creditServiceProvider;

  @Inject
  public RealFullObjectFactory(Provider<Scene> creditServiceProvider) {
    this.creditServiceProvider = creditServiceProvider;
  }

  @Override
  public FullObjectSet createFullObjectSet(RefType refType) {

      if (refType.getClassName().equals("java.lang.Object")) {
          return new FullObjectSet(creditServiceProvider.get());
      }
      return new FullObjectSet(refType);
  }

  @Override
  public FullObjectSet getFullObjectSet() {
    return new FullObjectSet(creditServiceProvider.get());
  }
}
