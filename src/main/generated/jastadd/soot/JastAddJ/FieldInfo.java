package soot.JastAddJ;

import java.util.*;

/**
  * @ast class
 * 
 */
public class FieldInfo extends java.lang.Object {

    private BytecodeParser p;


    String name;


    int flags;


    private FieldDescriptor fieldDescriptor;


    private Attributes.FieldAttributes attributes;



    public FieldInfo(BytecodeParser parser) {
      p = parser;
      flags = p.u2();
      if(BytecodeParser.VERBOSE)
        p.print("Flags: " + flags);
      int name_index = p.u2();
      name = ((CONSTANT_Utf8_Info) p.constantPool[name_index]).string();

      fieldDescriptor = new FieldDescriptor(p, name);
      attributes = new Attributes.FieldAttributes(p);
    }



    public BodyDecl bodyDecl() {
      FieldDeclaration f;
      if((flags & Flags.ACC_ENUM) != 0)
        //EnumConstant : FieldDeclaration ::= Modifiers <ID:String> Arg:Expr* BodyDecl* /TypeAccess:Access/ /[Init:Expr]/;
        f = new EnumConstant(
            BytecodeParser.modifiers(flags),
            name,
            new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions),
            new List(myScene, myOptions, myPackageNamer, myJimple, primTypeCollector, constantFactory, mySootResolver, myPhaseOptions),
                myPhaseOptions, myScene, myOptions, mySootResolver, myPackageNamer, myJimple, constantFactory, primTypeCollector);
      else {
        Signatures.FieldSignature s = attributes.fieldSignature;
        Access type = s != null ? s.fieldTypeAccess() : fieldDescriptor.type();
        f = new FieldDeclaration(
            BytecodeParser.modifiers(flags),
            type,
            name,
            new Opt(),
                myScene, myPackageNamer, primTypeCollector, myJimple, constantFactory, mySootResolver, myPhaseOptions);
      }
      if(attributes.constantValue() != null)
        if(fieldDescriptor.isBoolean()) {
          f.setInit(attributes.constantValue().exprAsBoolean());
        }
        else {
          f.setInit(attributes.constantValue().expr());
        }

      if(attributes.annotations != null)
        for(Iterator iter = attributes.annotations.iterator(); iter.hasNext(); )
          f.getModifiersNoTransform().addModifier((Modifier)iter.next());

      return f;
    }



    public boolean isSynthetic() {
      return attributes.isSynthetic();
    }


}
