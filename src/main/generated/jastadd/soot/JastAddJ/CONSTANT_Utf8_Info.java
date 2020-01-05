package soot.JastAddJ;

/**
  * @ast class
 * 
 */
public class CONSTANT_Utf8_Info extends CONSTANT_Info {

    public String string;



    public CONSTANT_Utf8_Info(BytecodeParser parser) {
      super(parser);
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
