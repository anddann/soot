package soot.coffi;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 Clark Verbrugge
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

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.ArrayType;
import soot.Body;
import soot.Local;
import soot.Modifier;
import soot.PackManager;
import soot.PhaseOptions;
import soot.PrimTypeCollector;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootResolver;
import soot.Timers;
import soot.Type;
import soot.jimple.ConstantFactory;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.options.Options;
import soot.tagkit.AnnotationAnnotationElem;
import soot.tagkit.AnnotationArrayElem;
import soot.tagkit.AnnotationClassElem;
import soot.tagkit.AnnotationConstants;
import soot.tagkit.AnnotationDefaultTag;
import soot.tagkit.AnnotationDoubleElem;
import soot.tagkit.AnnotationElem;
import soot.tagkit.AnnotationEnumElem;
import soot.tagkit.AnnotationFloatElem;
import soot.tagkit.AnnotationIntElem;
import soot.tagkit.AnnotationLongElem;
import soot.tagkit.AnnotationStringElem;
import soot.tagkit.AnnotationTag;
import soot.tagkit.ConstantValueTag;
import soot.tagkit.DeprecatedTag;
import soot.tagkit.DoubleConstantValueTag;
import soot.tagkit.EnclosingMethodTag;
import soot.tagkit.FloatConstantValueTag;
import soot.tagkit.GenericAttribute;
import soot.tagkit.Host;
import soot.tagkit.InnerClassTag;
import soot.tagkit.IntegerConstantValueTag;
import soot.tagkit.LongConstantValueTag;
import soot.tagkit.SignatureTag;
import soot.tagkit.SourceFileTag;
import soot.tagkit.StringConstantValueTag;
import soot.tagkit.SyntheticTag;
import soot.tagkit.VisibilityAnnotationTag;
import soot.tagkit.VisibilityParameterAnnotationTag;

public class Util {
    private static final Logger logger = LoggerFactory.getLogger(Util.class);
    private Scene myScene;

    private SootResolver mySootResolver;
    private Jimple myJimple;
    private PhaseOptions myPhaseOptions;
    private Options myOptions;
    private PackManager myPackManager;
    private Timers myTimers;
    private PrimTypeCollector myPrimTypeCollector;
    private ConstantFactory constancFactory;

    @Inject
    public Util(Scene myScene, SootResolver mySootResolver, Jimple myJimple, PhaseOptions myPhaseOptions, Options myOptions,
                PackManager myPackManager, Timers myTimers,  PrimTypeCollector myPrimTypeCollector, ConstantFactory constancFactory) {
        this.myScene = myScene;
        this.mySootResolver = mySootResolver;
        this.myJimple = myJimple;
        this.myPhaseOptions = myPhaseOptions;
        this.myOptions = myOptions;
        this.myPackManager = myPackManager;
        this.myTimers = myTimers;
        this.myPrimTypeCollector = myPrimTypeCollector;
        this.constancFactory = constancFactory;
    }

    /*
     * maps from variable names to local variable slot indexes to soot Locals
     */
    private Map<String, Map<Integer, Local>> nameToIndexToLocal;
    private boolean useFaithfulNaming = false;


    public void setFaithfulNaming(boolean v) {
        useFaithfulNaming = v;
    }

    public boolean isUsingFaithfulNaming() {
        return useFaithfulNaming;
    }



    Type jimpleReturnTypeOfMethodDescriptor(String descriptor) {
        Type[] types = jimpleTypesOfFieldOrMethodDescriptor(descriptor);

        return types[types.length - 1];
    }

    private final ArrayList<Type> conversionTypes = new ArrayList<Type>();

    /*
     * private Map cache = new HashMap(); public Type[] jimpleTypesOfFieldOrMethodDescriptor( String descriptor) { Type[] ret =
     * (Type[]) cache.get(descriptor); if( ret != null ) return ret; conversionTypes.clear();
     *
     * while(descriptor.length() != 0) { boolean isArray = false; int numDimensions = 0; Type baseType;
     *
     * // Skip parenthesis if(descriptor.startsWith("(") || descriptor.startsWith(")")) { descriptor = descriptor.substring(1);
     * continue; }
     *
     * // Handle array case while(descriptor.startsWith("[")) { isArray = true; numDimensions++; descriptor =
     * descriptor.substring(1); }
     *
     * // Determine base type if(descriptor.startsWith("B")) { baseType = primeTypeCollector.getByteType(); descriptor = descriptor.substring(1); }
     * else if(descriptor.startsWith("C")) { baseType = primeTypeCollector.getCharType(); descriptor = descriptor.substring(1); } else
     * if(descriptor.startsWith("D")) { baseType = primeTypeCollector.getDoubleType(); descriptor = descriptor.substring(1); } else
     * if(descriptor.startsWith("F")) { baseType = primeTypeCollector.getFloatType(); descriptor = descriptor.substring(1); } else
     * if(descriptor.startsWith("I")) { baseType = primeTypeCollector.getIntType(); descriptor = descriptor.substring(1); } else
     * if(descriptor.startsWith("J")) { baseType = primeTypeCollector.getLongType(); descriptor = descriptor.substring(1); } else
     * if(descriptor.startsWith("L")) { int index = descriptor.indexOf(';');
     *
     * if(index == -1) throw new RuntimeException("Class reference has no ending ;" );
     *
     * String className = descriptor.substring(1, index);
     *
     * baseType = RefType.v(className.replace('/', '.'));
     *
     * descriptor = descriptor.substring(index + 1); } else if(descriptor.startsWith("S")) { baseType = primeTypeCollector.getShortType();
     * descriptor = descriptor.substring(1); } else if(descriptor.startsWith("Z")) { baseType = primeTypeCollector.getBooleanType(); descriptor =
     * descriptor.substring(1); } else if(descriptor.startsWith("V")) { baseType = primeTypeCollector.getVoidType(); descriptor =
     * descriptor.substring(1); } else throw new RuntimeException("Unknown field type!" );
     *
     * Type t;
     *
     * // Determine type if(isArray) t = ArrayType.v(baseType, numDimensions); else t = baseType;
     *
     * conversionTypes.add(t); }
     *
     * ret = (Type[]) conversionTypes.toArray(new Type[0]); cache.put(descriptor, ret); return ret; }
     */

    private final Map<String, Type[]> cache = new HashMap<String, Type[]>();

    public Type[] jimpleTypesOfFieldOrMethodDescriptor(String descriptor) {
        Type[] ret = null;
        synchronized (cache) {
            ret = cache.get(descriptor);
        }
        if (ret != null) {
            return ret;
        }
        char[] d = descriptor.toCharArray();
        int p = 0;
        List<Type> conversionTypes = new ArrayList<Type>();

        outer: while (p < d.length) {
            boolean isArray = false;
            int numDimensions = 0;
            Type baseType = null;

            swtch: while (p < d.length) {
                switch (d[p]) {
                    // Skip parenthesis
                    case '(':
                    case ')':
                        p++;
                        continue outer;

                    case '[':
                        isArray = true;
                        numDimensions++;
                        p++;
                        continue swtch;
                    case 'B':
                        baseType = myPrimTypeCollector.getByteType();
                        p++;
                        break swtch;
                    case 'C':
                        baseType = myPrimTypeCollector.getCharType();
                        p++;
                        break swtch;
                    case 'D':
                        baseType = myPrimTypeCollector.getDoubleType();
                        p++;
                        break swtch;
                    case 'F':
                        baseType = myPrimTypeCollector.getFloatType();
                        p++;
                        break swtch;
                    case 'I':
                        baseType = myPrimTypeCollector.getIntType();
                        p++;
                        break swtch;
                    case 'J':
                        baseType = myPrimTypeCollector.getLongType();
                        p++;
                        break swtch;
                    case 'L':
                        int index = p + 1;
                        while (index < d.length && d[index] != ';') {
                            if (d[index] == '/') {
                                d[index] = '.';
                            }
                            index++;
                        }
                        if (index >= d.length) {
                            throw new RuntimeException("Class reference has no ending ;");
                        }
                        String className = new String(d, p + 1, index - p - 1);
                        baseType = RefType.v(className,myScene);
                        p = index + 1;
                        break swtch;
                    case 'S':
                        baseType = myPrimTypeCollector.getShortType();
                        p++;
                        break swtch;
                    case 'Z':
                        baseType = myPrimTypeCollector.getBooleanType();
                        p++;
                        break swtch;
                    case 'V':
                        baseType = myPrimTypeCollector.getVoidType();
                        p++;
                        break swtch;
                    default:
                        throw new RuntimeException("Unknown field type!");
                }
            }
            if (baseType == null) {
                continue;
            }

            // Determine type
            Type t;
            if (isArray) {
                t = ArrayType.v(baseType, numDimensions,myScene);
            } else {
                t = baseType;
            }

            conversionTypes.add(t);
        }

        ret = conversionTypes.toArray(new Type[0]);
        synchronized (cache) {
            cache.put(descriptor, ret);
        }
        return ret;
    }

    public Type jimpleTypeOfFieldDescriptor(String descriptor) {
        boolean isArray = false;
        int numDimensions = 0;
        Type baseType;

        // Handle array case
        while (descriptor.startsWith("[")) {
            isArray = true;
            numDimensions++;
            descriptor = descriptor.substring(1);
        }

        // Determine base type
        if (descriptor.equals("B")) {
            baseType = myPrimTypeCollector.getByteType();
        } else if (descriptor.equals("C")) {
            baseType = myPrimTypeCollector.getCharType();
        } else if (descriptor.equals("D")) {
            baseType = myPrimTypeCollector.getDoubleType();
        } else if (descriptor.equals("F")) {
            baseType = myPrimTypeCollector.getFloatType();
        } else if (descriptor.equals("I")) {
            baseType = myPrimTypeCollector.getIntType();
        } else if (descriptor.equals("J")) {
            baseType = myPrimTypeCollector.getLongType();
        } else if (descriptor.equals("V")) {
            baseType = myPrimTypeCollector.getVoidType();
        } else if (descriptor.startsWith("L")) {
            if (!descriptor.endsWith(";")) {
                throw new RuntimeException("Class reference does not end with ;");
            }

            String className = descriptor.substring(1, descriptor.length() - 1);

            baseType = RefType.v(className.replace('/', '.'),myScene);
        } else if (descriptor.equals("S")) {
            baseType = myPrimTypeCollector.getShortType();
        } else if (descriptor.equals("Z")) {
            baseType = myPrimTypeCollector.getBooleanType();
        } else {
            throw new RuntimeException("Unknown field type: " + descriptor);
        }

        // Return type
        if (isArray) {
            return ArrayType.v(baseType, numDimensions,myScene);
        } else {
            return baseType;
        }
    }

    int nextEasyNameIndex;

    void resetEasyNames() {
        nextEasyNameIndex = 0;
    }

    String getNextEasyName() {
        final String[] easyNames = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r",
                "s", "t", "u", "v", "w", "x", "y", "z" };

        int justifiedIndex = nextEasyNameIndex++;

        if (justifiedIndex >= easyNames.length) {
            return "local" + (justifiedIndex - easyNames.length);
        } else {
            return easyNames[justifiedIndex];
        }
    }



    String getAbbreviationOfClassName(String className) {
        StringBuffer buffer = new StringBuffer(new Character(className.charAt(0)).toString());
        int periodIndex = 0;

        for (;;) {
            periodIndex = className.indexOf('.', periodIndex + 1);

            if (periodIndex == -1) {
                break;
            }

            buffer.append(Character.toLowerCase(className.charAt(periodIndex + 1)));
        }

        return buffer.toString();
    }

    String getNormalizedClassName(String className) {
        className = className.replace('/', '.');

        if (className.endsWith(";")) {
            className = className.substring(0, className.length() - 1);
        }

        // Handle array case
        {
            int numDimensions = 0;

            while (className.startsWith("[")) {
                numDimensions++;
                className = className.substring(1, className.length());
                className = className + "[]";
            }

            if (numDimensions != 0) {
                if (!className.startsWith("L")) {
                    throw new RuntimeException("For some reason an array reference does not start with L");
                }

                className = className.substring(1, className.length());
            }
        }

        return className;
    }

    private Local getLocalUnsafe(Body b, String name) {
        for (Local local : b.getLocals()) {
            if (local.getName().equals(name)) {
                return local;
            }
        }
        return null;
    }

    Local getLocalCreatingIfNecessary(JimpleBody listBody, String name, Type type) {
        Local l = getLocalUnsafe(listBody, name);
        if (l != null) {
            if (!l.getType().equals(type)) {
                throw new RuntimeException("The body already declares this local name with a different type.");
            }
        } else {
            l = myJimple.newLocal(name, type);
            listBody.getLocals().add(l);
        }
        return l;
    }







    /*
     * void setLocalType(Local local, List locals, int localIndex, Type type) { if(local.getType().equals(UnknownType .v()) ||
     * local.getType().equals(type)) { local.setType(type);
     *
     * if(local.getType().equals(DoubleType. v()) || local.getType().equals(primeTypeCollector.getLongType())) { // This means the next local
     * becomes voided, since these types occupy two // words.
     *
     * Local secondHalf = (Local) locals.get(localIndex + 1);
     *
     * secondHalf.setType(primeTypeCollector.getVoidType()); }
     *
     * return; }
     *
     * if(type.equals(primeTypeCollector.getIntType())) { if(local.getType().equals(BooleanType .v()) || local.getType().equals(primeTypeCollector.getCharType()) ||
     * local.getType().equals(primeTypeCollector.getShortType()) || local.getType().equals(primeTypeCollector.getByteType())) { // Even though it's not the same, it's
     * ok, because booleans, chars, shorts, and // bytes are all sort of treated like integers by the JVM. return; }
     *
     * }
     *
     * throw new RuntimeException("required and actual types do not match: " + type.toString() + " with " +
     * local.getType().toString()); }
     */

    /**
     * Verifies the prospective name for validity as a Jimple name. In particular, first-char is alpha | _ | $,
     * subsequent-chars are alphanum | _ | $.
     *
     * We could use isJavaIdentifier, except that Jimple's grammar doesn't support all of those, just ASCII.
     *
     * I'd put this in soot.Local, but that's an interface.
     *
     * @author Patrick Lam
     */
    boolean isValidJimpleName(String prospectiveName) {
        if (prospectiveName == null) {
            return false;
        }
        for (int i = 0; i < prospectiveName.length(); i++) {
            char c = prospectiveName.charAt(i);
            if (i == 0 && c >= '0' && c <= '9') {
                return false;
            }

            if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c == '_' || c == '$'))) {
                return false;
            }
        }
        return true;
    }








}
