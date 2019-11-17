package soot.jimple;

import soot.RefType;
import soot.jimple.toolkits.pointer.FullObjectSet;

public interface FullObjectFactory {


    public FullObjectSet createFullObjectSet(RefType refType);

    public FullObjectSet getFullObjectSet();

}
