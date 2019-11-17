package soot;

import com.google.inject.Inject;

import soot.baf.DoubleWordType;
import soot.baf.WordType;
import soot.coffi.Double2ndHalfType;
import soot.coffi.Long2ndHalfType;
import soot.jimple.toolkits.typing.fast.Integer127Type;
import soot.jimple.toolkits.typing.fast.Integer1Type;
import soot.jimple.toolkits.typing.fast.Integer32767Type;

public class PrimTypeCollector {

  private FloatType floatType;
  private NullType nullType;
  private ErroneousType errorneousType;
  private StmtAddressType stmtAddressType;
  private WordType wordType;
  private DoubleWordType doubleWordType;
  private RefType refType;
  private Double2ndHalfType double2ndHalfType;
  private Long2ndHalfType long2ndHalftType;

  public VoidType getVoidType() {
    return voidType;
  }

  public IntType getIntType() {
    return intType;
  }

  public ShortType getShortType() {
    return shortType;
  }

  public CharType getCharType() {
    return charType;
  }

  public ByteType getByteType() {
    return byteType;
  }

  public Integer1Type getInteger1Type() {
    return integer1Type;
  }

  public Integer32767Type getInteger32767Type() {
    return integer32767Type;
  }

  public Integer127Type getInteger127Type() {
    return integer127Type;
  }

  public DoubleType getDoubleType() {
    return doubleType;
  }

  public LongType getLongType() {
    return longType;
  }

  private BooleanType booleanType;
  private VoidType voidType;
  private IntType intType;
  private ShortType shortType;
  private CharType charType;
  private ByteType byteType;
  private Integer1Type integer1Type;
  private Integer32767Type integer32767Type;
  private Integer127Type integer127Type;
  private DoubleType doubleType;
  private LongType longType;

  private UnknownType unknownType;

  @Inject
  public PrimTypeCollector(FloatType floatType, NullType nullType, ErroneousType errorneousType,
      StmtAddressType stmtAddressType, WordType wordType, DoubleWordType doubleWordType, RefType refType,
      Double2ndHalfType double2ndHalfType, Long2ndHalfType long2ndHalftType, BooleanType booleanType, VoidType voidType,
      IntType intType, ShortType shortType, CharType charType, ByteType byteType, Integer1Type integer1Type,
      Integer32767Type integer32767Type, Integer127Type integer127Type, DoubleType doubleType, LongType longType,
      UnknownType unknownType) {
    this.floatType = floatType;
    this.nullType = nullType;
    this.errorneousType = errorneousType;
    this.stmtAddressType = stmtAddressType;
    this.wordType = wordType;
    this.doubleWordType = doubleWordType;
    this.refType = refType;
    this.double2ndHalfType = double2ndHalfType;
    this.long2ndHalftType = long2ndHalftType;

    this.booleanType = booleanType;
    this.voidType = voidType;
    this.intType = intType;
    this.shortType = shortType;
    this.charType = charType;
    this.byteType = byteType;
    this.integer1Type = integer1Type;
    this.integer32767Type = integer32767Type;
    this.integer127Type = integer127Type;
    this.doubleType = doubleType;
    this.longType = longType;
    this.unknownType = unknownType;
  }

  public BooleanType getBooleanType() {
    return booleanType;
  }

  public UnknownType getUnknownType() {
    return unknownType;
  }

  public FloatType getFloatType() {
    return this.floatType;
  }

  public NullType getNullType() {
    return this.nullType;
  }

  public ErroneousType getErrornousType() {
    return errorneousType;
  }

  public StmtAddressType getStmtAddressType() {
    return this.stmtAddressType;
  }

  public WordType getWordType() {
    return wordType;
  }

  public DoubleWordType getDoubleWordType() {
    return doubleWordType;
  }

  public RefType getRefType() {
    return refType;
  }

  public Double2ndHalfType getDouble2ndHalfType() {
    return double2ndHalfType;
  }

  public Long2ndHalfType getLong2ndHalfType() {
    return long2ndHalftType;
  }
}
