package soot.JastAddJ;

import soot.jimple.ConstantFactory;

/**
  * @ast class
 * 
 */
public class CONSTANT_Utf8_Info extends CONSTANT_Info {

    public String string;
    private ConstantFactory constantFactory;


    public CONSTANT_Utf8_Info(BytecodeParser parser, ConstantFactory constantFactory) {
      super(parser);
        this.constantFactory = constantFactory;
        string = p.readUTF();
    }



    public String toString() {
      return "Utf8Info: " + string;
    }



    public Expr expr() {
      return Literal.buildStringLiteral(string, constantFactory);
    }



    public String string() {
      return string;
    }


}
