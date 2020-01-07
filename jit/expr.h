#ifndef QSYM_EXPR_H_
#define QSYM_EXPR_H_

#include <iostream>
#include <iomanip>
#include <map>
#include <unordered_set>
#include <set>
#include <sstream>
#include <vector>


//#include "common.h"
#include <llvm/ADT/APSInt.h>
#include "compiler.h"
#include "dependency.h"
#include "logging.h"
#define XXH_STATIC_LINKING_ONLY
#include "xxhash.h"

namespace RGDPROXY {
inline void LogError(const char *Str) {
  LOG_INFO(Str);
}

inline void LogErrorV(const char *Str) {
  LogError(Str);
}

const int32_t kMaxDepth = 100;

enum Kind {
  Bool, // 0
  Constant, // 1
  Read, // 2
  Concat, // 3
  Extract, // 4

  ZExt, // 5
  SExt, // 6

  // Arithmetic
  Add, // 7
  Sub, // 8
  Mul, // 9
  UDiv, // 10
  SDiv, // 11
  URem, // 12
  SRem, // 13
  Neg,  // 14

  // Bit
  Not, // 15
  And, // 16
  Or, // 17
  Xor, // 18
  Shl, // 19
  LShr, // 20
  AShr, // 21

  // Compare
  Equal, // 22
  Distinct, // 23
  Ult, // 24
  Ule, // 25
  Ugt, // 26
  Uge, // 27
  Slt, // 28
  Sle, // 29
  Sgt, // 30
  Sge, // 31

  // Logical
  LOr, // 32
  LAnd, // 33
  LNot, // 34

  // Special
  Ite, // 35

  //UCR hack extend opcodes
  Set,
  Pack,
  Vpack,
  Bsf,
  Bsr,
  Shufb,
  Pcmp,
  Pmov,
  Pcmpxchg,

  // Virtual operation
  Rol,
  Ror,
  Invalid
};

Kind swapKind(Kind kind);
Kind negateKind(Kind kind);
bool isNegatableKind(Kind kind);

// forward declaration
#define DECLARE_EXPR(cls) \
  class cls; \
  typedef std::shared_ptr<cls> glue(cls, Ref);

DECLARE_EXPR(Expr);
DECLARE_EXPR(ConstantExpr);
DECLARE_EXPR(NonConstantExpr);
DECLARE_EXPR(BoolExpr);

/*UCR hacking*/
DECLARE_EXPR(ExtractExpr);
DECLARE_EXPR(ReadExpr);

typedef std::weak_ptr<Expr> WeakExprRef;
typedef std::vector<WeakExprRef> WeakExprRefVectorTy;

template <class T>
inline std::shared_ptr<T> castAs(ExprRef e) {
  if (T::classOf(*e))
    return std::static_pointer_cast<T>(e);
  else
    return NULL;
}

template <class T>
inline std::shared_ptr<T> castAsNonNull(ExprRef e) {
  assert(T::classOf(*e));
  return std::static_pointer_cast<T>(e);
}

class ExprBuilder;
class IndexSearchTree;

void printLLVMIr(ExprRef e, int value);
void sendCmd(int cmd);
void gdReset();
void gdSolve();
//void mytest();

typedef std::set<int32_t> DepSet;

class Expr : public DependencyNode {
  public:
    Expr(Kind kind, uint32_t bits);
    virtual ~Expr();
    Expr(const Expr& that) = delete;

    XXH32_hash_t hash();

    Kind kind() const {
      return kind_;
    }

    uint32_t bits() const {
      return bits_;
    }


		void setTTFuzzLabelAndHash(uint32_t l, uint32_t h) {
			ttfuzz_hash = h;
			ttfuzz_label = l;
		}

		uint32_t TTFuzzHash() {
			return ttfuzz_hash;
		}

		uint32_t TTFuzzLabel() {
			return ttfuzz_label;
		}

    uint32_t bytes() const {
      // utility function to convert from bits to bytes
      assert(bits() % CHAR_BIT == 0);
      return bits() / CHAR_BIT;
    }

    inline ExprRef getChild(uint32_t index) const {
      return children_[index];
    }
 
    inline ExprRef getExtendedChild(uint32_t index) const {
      return extendedChildren_[index];
    } 

    inline int32_t num_children() const {
      return children_.size();
    }

    inline int32_t num_childrenExt() const {
      return extendedChildren_.size();
    }

    inline ExprRef getFirstChild() const {
      return getChild(0);
    }

    inline ExprRef getSecondChild() const {
      return getChild(1);
    }

    inline ExprRef getLeft() const {
      return getFirstChild();
    }

    inline ExprRef getRight() const {
      return getSecondChild();
    }

    int32_t depth();

    bool isConcrete() const {
      return isConcrete_;
    }

    bool isConstant() const {
      return kind_ == Constant;
    }

    bool isBool() const {
      return kind_ == Bool;
    }

    bool isZero() const;
    bool isAllOnes() const;
    bool isOne() const;

    DepSet& getDeps() {
      if (deps_ == NULL) {
        deps_ = new DepSet();
        DepSet& deps = *deps_;
        for (int32_t i = 0; i < num_children(); i++) {
          DepSet& other = getChild(i)->getDeps();
          deps.insert(other.begin(), other.end());
        }
      }
      return *deps_;
    }

    DependencySet computeDependencies() override;

    uint32_t countLeadingZeros() {
      if (leading_zeros_ == (uint32_t)-1)
        leading_zeros_ = _countLeadingZeros();
      return leading_zeros_;
    }
    virtual uint32_t _countLeadingZeros() const { return 0; }
    virtual void print(std::ostream& os=std::cerr, uint32_t depth=0) const;
    void printConstraints();
    std::string consToString();
    std::string toString() const;
    //UCR hacking
    std::string toStringExtOp() const;
    //UCR hacking end
    void simplify();
    //virtual std::string printLLVMIr() const {return "hahaah";}
    //virtual void doPrintLLVMIr(ostream& os=std::cerr) const {}


    
    friend bool equalMetadata(const Expr& l, const Expr& r) {
      return (const_cast<Expr&>(l).hash() == const_cast<Expr&>(r).hash()
          && l.kind_ == r.kind_
          && l.num_children() == r.num_children()
          && l.bits_ == r.bits_
          && l.equalAux(r));
    }

    friend bool equalShallowly(const Expr& l, const Expr& r) {
      // Check equality only in 1 depth if not return false
      if (!equalMetadata(l, r))
        return false;

      // If one of childrens is different, then false
      for (int32_t i = 0; i < l.num_children(); i++) {
        if (l.children_[i] != r.children_[i])
          return false;
      }
      return true;
    }

    friend bool operator==(const Expr& l, const Expr& r) {
      // 1. if metadata are different -> different
      if (!equalMetadata(l, r))
        return false;

      // 2. if metadata of children are different -> different
      for (int32_t i = 0; i < l.num_children(); i++) {
        if (!equalMetadata(*l.children_[i], *r.children_[i]))
          return false;
      }

      // 3. if all childrens are same --> same
      for (int32_t i = 0; i < l.num_children(); i++) {
        if (l.children_[i] != r.children_[i]
            && *l.children_[i] != *r.children_[i])
          return false;
      }
      return true;
    }

    friend bool operator!=(const Expr& l, const Expr& r) {
      return !(l == r);
    }
    
    void setExtended() { hasExtended = true;}
    void setExtendedOp(Kind opcode) { kindEx_ = opcode; }

    inline void addExtendedChild(ExprRef e) {
      extendedChildren_.push_back(e);
    }

    inline void addChild(ExprRef e) {
      children_.push_back(e);
      if (!e->isConcrete())
        isConcrete_ = false;
    }
    inline void addUse(WeakExprRef e) { uses_.push_back(e); }

    void addConstraint(Kind kind, llvm::APInt rhs, llvm::APInt adjustment);

    void concretize() {
      if (!isConcrete()) {
        isConcrete_ = true;
        for (auto it = uses_.begin(); it != uses_.end(); it++) {
          WeakExprRef& ref = *it;
          if (ref.expired())
            continue;
          ref.lock()->tryConcretize();
        }
      }
    }

    void tryConcretize() {
      if (isConcrete())
        return;

      for (int32_t i = 0; i < num_children(); i++) {
        ExprRef e = getChild(i);
        if (!e->isConcrete())
          return;
      }

      concretize();
    }

    ExprRef evaluate();

    //UCR hack
    //virtual llvm::Value *codegen() const;// {
    //  std::cerr << "code gen called" << std::endl;
    //  return nullptr;
    //}

  protected:
    Kind kind_;
    uint32_t bits_;
    std::vector< ExprRef > children_;
    //UCR hacking start
    std::vector< ExprRef > extendedChildren_;
    //UCR hacking end
    XXH32_hash_t* hash_;

    // concretization
    bool isConcrete_;

    //UCR hacking
    bool hasExtended;
    Kind kindEx_;

		//From TTFuzz 
		uint32_t ttfuzz_hash;
		uint32_t ttfuzz_label;

    int32_t depth_;
    DepSet* deps_;
    WeakExprRefVectorTy uses_;
    uint32_t leading_zeros_;
    ExprRef evaluation_;

    void printChildren(std::ostream& os, bool start, uint32_t depth) const;

    //UCR hacking
    void printChildrenExt(std::ostream& os, bool start, uint32_t depth) const;

    virtual bool printAux(std::ostream& os) const {
      return false;
    }

    
    virtual std::string getName() const = 0;
        virtual void hashAux(XXH32_state_t* state) { return; }
    virtual bool equalAux(const Expr& other) const { return true; }
    //virtual ExprRef evaluateImpl() = 0;

}; // class Expr

struct ExprRefHash {
  XXH32_hash_t operator()(const ExprRef e) const {
    return std::const_pointer_cast<Expr>(e)->hash();
  }
};

struct ExprRefEqual {
  bool operator()(const ExprRef l,
      const ExprRef r) const {
    return l == r || equalShallowly(*l, *r);
  }
};


class ConstantExpr : public Expr {
public:
  ConstantExpr(uint64_t value, uint32_t bits) :
    Expr(Constant, bits),
    value_(bits, value) {}

  ConstantExpr(const llvm::APInt& value, uint32_t bits) :
    Expr(Constant, bits),
    value_(value) {}

  inline llvm::APInt value() const { return value_; }
  inline bool isZero() const { return value_ == 0; }
  inline bool isOne() const { return value_ == 1; }
  inline bool isAllOnes() const { return value_.isAllOnesValue(); }
  static bool classOf(const Expr& e) { return e.kind() == Constant; }
  uint32_t getActiveBits() const { return value_.getActiveBits(); }
  void print(std::ostream& os, uint32_t depth) const override;
  uint32_t _countLeadingZeros() const override {
    return value_.countLeadingZeros();
  }

  //llvm::Value* codegen() const override; // {
   // std::cerr << "Constant code gen called" << std::endl;
   // llvm::Value* ret = llvm::ConstantInt::get(TheContext, value_);
   // std::cerr << "Constant code gen returned" << std::endl;
   // return ret;
 //}

protected:
  std::string getName() const override {
    return "Constant";
  }

  
  bool printAux(std::ostream& os) const override {
    os << "value=0x" << value_.toString(16, false)
      << ", bits=" << bits_;
    return true;
  }

  
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state,
        value_.getRawData(),
        value_.getNumWords() * sizeof(uint64_t));
  }

  bool equalAux(const Expr& other) const override {
    const ConstantExpr& typed_other = static_cast<const ConstantExpr&>(other);
    return value_ == typed_other.value();
  }

  //ExprRef evaluateImpl() override;
  llvm::APInt value_;
};


class NonConstantExpr : public Expr {
  public:
    using Expr::Expr;
    static bool classOf(const Expr& e) { return !ConstantExpr::classOf(e); }
};

class UnaryExpr : public NonConstantExpr {
public:
  UnaryExpr(Kind kind, ExprRef e, uint32_t bits)
    : NonConstantExpr(kind, bits) {
      addChild(e);
    }
  UnaryExpr(Kind kind, ExprRef e)
    : UnaryExpr(kind, e, e->bits()) {}

  ExprRef expr() const { return getFirstChild(); }

protected:
  //ExprRef evaluateImpl() override;
};

class BinaryExpr : public NonConstantExpr {
public:
  BinaryExpr(Kind kind, ExprRef l,
      ExprRef r, uint32_t bits) :
    NonConstantExpr(kind, bits) {
      addChild(l);
      addChild(r);
      assert(l->bits() == r->bits());
    }

  BinaryExpr(Kind kind,
      ExprRef l,
      ExprRef r) :
    BinaryExpr(kind, l, r, l->bits()) {}

  void print(std::ostream& os, uint32_t depth, const char* op) const;
protected:
  //ExprRef evaluateImpl() override;
};

class LinearBinaryExpr : public BinaryExpr {
using BinaryExpr::BinaryExpr;
};

class NonLinearBinaryExpr : public BinaryExpr {
using BinaryExpr::BinaryExpr;
};

class CompareExpr : public LinearBinaryExpr {
public:
  CompareExpr(Kind kind,
      ExprRef l,
      ExprRef r) :
    LinearBinaryExpr(kind, l, r, 1) {
      assert(l->bits() == r->bits());
    }
};

class BoolExpr : public NonConstantExpr {
public:
  BoolExpr(bool value) :
    NonConstantExpr(Bool, 1),
    value_(value) {}

  inline bool value() const { return value_; }
  static bool classOf(const Expr& e) { return e.kind() == Bool; }
  //llvm::Value* codegen() const override; // {
    //std::cerr << "Boolexpr code gen called" << std::endl;
    //if(value())
     // return llvm::ConstantInt::getTrue(TheContext);
    //else
     // return llvm::ConstantInt::getFalse(TheContext);
  //}

protected:
  std::string getName() const override {
    return "Bool";
  }

  bool printAux(std::ostream& os) const override {
    os << "value=" << value_;
    return true;
  }

  
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state, &value_, sizeof(value_));
  }

  bool equalAux(const Expr& other) const override {
    const BoolExpr& typed_other = static_cast<const BoolExpr&>(other);
    return value_ == typed_other.value();
  }

  //ExprRef evaluateImpl() override;
  bool value_;
};


class ReadExpr : public NonConstantExpr {
public:
  ReadExpr(uint32_t index)
    : NonConstantExpr(Read, 8), index_(index) {
    deps_ = new DepSet();
    deps_->insert(index);
    isConcrete_ = false;
  }

  std::string getName() const override {
    return "Read";
  }

  inline uint32_t index() const { return index_; }
  static bool classOf(const Expr& e) { return e.kind() == Read; }

  //Fix ReadExpr TODO
  //virtual llvm::Value* codegen() const override; // {
    //std::cerr << "ReadExpr code gen called" << std::endl;
    //llvm::Value* ret = llvm::ConstantInt::get(llvm::Type::getInt64Ty(TheContext),0);
    //std::cerr << "ReadExpr code gen returned" << std::endl;
    //return ret;
  //}

protected:
  bool printAux(std::ostream& os) const override {
    os << "index=" << index_;
    return true;
  }

  
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state, &index_, sizeof(index_));
  }

  bool equalAux(const Expr& other) const override {
    const ReadExpr& typed_other = static_cast<const ReadExpr&>(other);
    return index_ == typed_other.index();
  }

  //ExprRef evaluateImpl() override;
  uint32_t index_;
};

class ConcatExpr : public NonConstantExpr {
public:
  ConcatExpr(ExprRef l, ExprRef r)
    : NonConstantExpr(Concat, l->bits() + r->bits()) {
    addChild(l);
    addChild(r);
  }

  void print(std::ostream& os, uint32_t depth) const override;

  std::string getName() const override {
    return "Concat";
  }

  static bool classOf(const Expr& e) { return e.kind() == Concat; }
  uint32_t _countLeadingZeros() const override {
    uint32_t result = getChild(0)->countLeadingZeros();
    if (result == getChild(0)->bits())
      result += getChild(1)->countLeadingZeros();
    return result;
  }
  //TODO fix concat
  //llvm::Value* codegen() const override; // {

protected:

  //ExprRef evaluateImpl() override;
};

class ExtractExpr : public UnaryExpr {
public:
  ExtractExpr(ExprRef e, uint32_t index, uint32_t bits)
  : UnaryExpr(Extract, e, bits), index_(index) {
    assert(bits + index <= e->bits());
  }

  uint32_t index() const { return index_; }
  ExprRef expr() const { return getFirstChild(); }
  static bool classOf(const Expr& e) { return e.kind() == Extract; }
  //TODO fix extract
  //llvm::Value* codegen() const override; // {

protected:
  std::string getName() const override {
    return "Extract";
  }

  bool printAux(std::ostream& os) const override {
    os << "index=" << index_ << ", bits=" << bits_;
    return true;
  }

  
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state, &index_, sizeof(index_));
  }

  bool equalAux(const Expr& other) const override {
    const ExtractExpr& typed_other = static_cast<const ExtractExpr&>(other);
    return index_ == typed_other.index();
  }

  //ExprRef evaluateImpl() override;

  uint32_t index_;
};

class ExtExpr : public UnaryExpr {
public:
  using UnaryExpr::UnaryExpr;

  ExprRef expr() const { return getFirstChild(); }
  static bool classOf(const Expr& e) {
    return e.kind() == ZExt || e.kind() == SExt;
  }
};

class ZExtExpr : public ExtExpr {
public:
  ZExtExpr(ExprRef e, uint32_t bits)
    : ExtExpr(ZExt, e, bits) {}

  std::string getName() const override {
    return "ZExt";
  }

  static bool classOf(const Expr& e) { return e.kind() == ZExt; }
  uint32_t _countLeadingZeros() const override {
    return bits_ - getChild(0)->bits();
  }

  //llvm::Value* codegen() const override; 


protected:
  
  bool printAux(std::ostream& os) const override {
    os << "bits=" << bits_;
    return true;
  }

  //ExprRef evaluateImpl() override;
};

class SExtExpr : public ExtExpr {
public:
  SExtExpr(ExprRef e, uint32_t bits)
    : ExtExpr(SExt, e, bits) {}

  std::string getName() const override {
    return "SExt";
  }

  static bool classOf(const Expr& e) { return e.kind() == SExt; }

  //llvm::Value* codegen() const override;// {

protected:
  bool printAux(std::ostream& os) const override {
    os << "bits=" << bits_;
    return true;
  }
  
  //ExprRef evaluateImpl() override;
};

class NotExpr : public UnaryExpr {
public:
  NotExpr(ExprRef e)
    : UnaryExpr(Not, e) {}
  static bool classOf(const Expr& e) { return e.kind() == Not; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Not";
  }

};

class AndExpr : public NonLinearBinaryExpr {
public:
  AndExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(And, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == And; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "And";
  }
};

class OrExpr : public NonLinearBinaryExpr {
public:
  OrExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(Or, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Or; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Or";
  }

};

class XorExpr : public NonLinearBinaryExpr {
public:
  XorExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(Xor, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Xor; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Xor";
  }
  
};

class ShlExpr : public NonLinearBinaryExpr {
public:
  ShlExpr(ExprRef l, ExprRef r)
    : NonLinearBinaryExpr(Shl, l, r) {}

  static bool classOf(const Expr& e) { return e.kind() == Shl; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Shl";
  }

};

class LShrExpr : public NonLinearBinaryExpr {
public:
  LShrExpr(ExprRef l, ExprRef r)
    : NonLinearBinaryExpr(LShr, l, r) {}

  static bool classOf(const Expr& e) { return e.kind() == LShr; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "LShr";
  }

};

class AShrExpr : public NonLinearBinaryExpr {
public:
  AShrExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(AShr, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == AShr; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "AShr";
  }

};

class AddExpr : public LinearBinaryExpr {
public:
  AddExpr(ExprRef l, ExprRef h)
    : LinearBinaryExpr(Add, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Add; }
  void print(std::ostream& os, uint32_t depth) const override;

  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Add";
  }

};

class SubExpr : public LinearBinaryExpr {
public:
  SubExpr(ExprRef l, ExprRef h)
    : LinearBinaryExpr(Sub, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Sub; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Sub";
  }

  void print(std::ostream& os=std::cerr, uint32_t depth=0) const override;
};

class MulExpr : public NonLinearBinaryExpr {
public:
  MulExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(Mul, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Mul; }
  void print(std::ostream& os, uint32_t depth) const override;
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Mul";
  }

};

class UDivExpr : public NonLinearBinaryExpr {
public:
  UDivExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(UDiv, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == UDiv; }
  void print(std::ostream& os, uint32_t depth) const override;
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "UDiv";
  }

};

class SDivExpr : public NonLinearBinaryExpr {
public:
  SDivExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(SDiv, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == SDiv; }
  void print(std::ostream& os, uint32_t depth) const override;
  //llvm::Value* codegen() const override;//{

protected:
  std::string getName() const override {
    return "SDiv";
  }

};

class URemExpr : public NonLinearBinaryExpr {
public:
  URemExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(URem, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == URem; }
  void print(std::ostream& os, uint32_t depth) const override;
  //llvm::Value* codegen() const override;//{

protected:
  std::string getName() const override {
    return "URem";
  }

};

class SRemExpr : public NonLinearBinaryExpr {
public:
  SRemExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(SRem, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == SRem; }
  void print(std::ostream& os, uint32_t depth) const override;
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "SRem";
  }

};

class NegExpr : public UnaryExpr {
public:
  NegExpr(ExprRef e)
    : UnaryExpr(Neg, e) {}

  static bool classOf(const Expr& e) { return e.kind() == Neg; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Neg";
  }

};

class EqualExpr : public CompareExpr {
public:
  EqualExpr(ExprRef l, ExprRef h)
    : CompareExpr(Equal, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Equal; }

  //llvm::Value* codegen() const override;//{

protected:
  std::string getName() const override {
    return "Equal";
  }

};

class DistinctExpr : public CompareExpr {
public:
  DistinctExpr(ExprRef l, ExprRef h)
    : CompareExpr(Distinct, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Distinct; }

  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Distinct";
  }

};

class UltExpr : public CompareExpr {
public:
  UltExpr(ExprRef l, ExprRef h)
    : CompareExpr(Ult, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Ult; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Ult";
  }

};

class UleExpr : public CompareExpr {
public:
  UleExpr(ExprRef l, ExprRef h)
    : CompareExpr(Ule, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Ule; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Ule";
  }

};

class UgtExpr : public CompareExpr {
public:
  UgtExpr(ExprRef l, ExprRef h)
    : CompareExpr(Ugt, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Ugt; }
  //llvm::Value* codegen() const override;//{

protected:
  std::string getName() const override {
    return "Ugt";
  }

};

class UgeExpr : public CompareExpr {
public:
  UgeExpr(ExprRef l, ExprRef h)
    : CompareExpr(Uge, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Uge; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Uge";
  }

};

class SltExpr : public CompareExpr {
public:
  SltExpr(ExprRef l, ExprRef h)
    : CompareExpr(Slt, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Slt; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "Slt";
  }

};

class SleExpr : public CompareExpr {
public:
  SleExpr(ExprRef l, ExprRef h)
    : CompareExpr(Sle, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Sle; }
  //llvm::Value* codegen() const override;//{

protected:
  std::string getName() const override {
    return "Sle";
  }

};

class SgtExpr : public CompareExpr {
public:
  SgtExpr(ExprRef l, ExprRef h)
    : CompareExpr(Sgt, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == Sgt; }
  //llvm::Value* codegen() const override;//{

protected:
  std::string getName() const override {
    return "Sgt";
  }

};

class SgeExpr : public CompareExpr {
public:
  SgeExpr(ExprRef l, ExprRef h)
    : CompareExpr(Sge, l, h) {}
  //TODO fix Sge
  static bool classOf(const Expr& e) { return e.kind() == Sge; }
  //llvm::Value* codegen() const override;//{

protected:
  std::string getName() const override {
    return "Sge";
  }

};

class LAndExpr : public NonLinearBinaryExpr {
public:
  LAndExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(LAnd, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == LAnd; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "LAnd";
  }
  
};

class LOrExpr : public NonLinearBinaryExpr {
public:
  LOrExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(LOr, l, h) {}

  static bool classOf(const Expr& e) { return e.kind() == LOr; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "LOr";
  }

};

class LNotExpr : public UnaryExpr {
public:
  LNotExpr(ExprRef e)
    : UnaryExpr(LNot, e) {}

  static bool classOf(const Expr& e) { return e.kind() == LNot; }
  //llvm::Value* codegen() const override;// {

protected:
  std::string getName() const override {
    return "LNot";
  }

};

class IteExpr : public NonConstantExpr {
public:
  IteExpr(ExprRef expr_cond, ExprRef expr_true, ExprRef expr_false)
    : NonConstantExpr(Ite, expr_true->bits()) {
    assert(expr_true->bits() == expr_false->bits());
    addChild(expr_cond);
    addChild(expr_true);
    addChild(expr_false);
  }

  static bool classOf(const Expr& e) { return e.kind() == Ite; }
  ExprRef expr_cond() const { return getChild(0); }
  ExprRef expr_true() const { return getChild(1); }
  ExprRef expr_false() const { return getChild(2); }

protected:
  std::string getName() const override {
    return "Ite";
  }

  //ExprRef evaluateImpl() override;
};

// utility functions
bool isZeroBit(ExprRef e, uint32_t idx);
bool isOneBit(ExprRef e, uint32_t idx);
bool isRelational(const Expr* e);
bool isConstant(ExprRef e);
bool isConstSym(ExprRef e);
uint32_t getMSB(ExprRef e);
}
#endif // QSYM_EXPR_H_
