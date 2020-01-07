#include "expr_builder.h"
#include "expr.h"
//#include "solver.h"

// NOTE: Some simplification is ported from KLEE
namespace RGDPROXY {

Kind swapKind(Kind kind) {
  // function for finding neg_op s.t. x op y ==> y neg_op x
  switch (kind) {
    case Equal:
      return Equal;
    case Distinct:
      return Distinct;
    case Ult:
      return Ugt;
    case Ule:
      return Uge;
    case Ugt:
      return Ult; case Uge:
      return Ule;
    case Slt:
      return Sgt;
    case Sle:
      return Sge;
    case Sgt:
      return Slt;
    case Sge:
      return Sle;
    default:
      RGDPROXY_UNREACHABLE();
      return Invalid;
  }
}

Kind negateKind(Kind kind) {
  // function for finding neg_op s.t. x op y ==> y neg_op x
  switch (kind) {
    case Equal:
      return Distinct;
    case Distinct:
      return Equal;
    case Ult:
      return Uge;
    case Ule:
      return Ugt;
    case Ugt:
      return Ule;
    case Uge:
      return Ult;
    case Slt:
      return Sge;
    case Sle:
      return Sgt;
    case Sgt:
      return Sle;
    case Sge:
      return Slt;
    default:
      RGDPROXY_UNREACHABLE();
      return Invalid;
  }
}

bool isNegatableKind(Kind kind) {
  switch (kind) {
    case Distinct:
    case Equal:
    case Ult:
    case Ule:
    case Ugt:
    case Uge:
    case Slt:
    case Sle:
    case Sgt:
    case Sge:
      return true;
    default:
      return false;
  }
}

bool isZeroBit(ExprRef e, uint32_t idx) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e))
    return !ce->value()[idx];
  if (auto ce = castAs<ConcatExpr>(e)) {
    if (ce->getRight()->bits() <= idx)
      return isZeroBit(ce->getLeft(), idx - ce->getRight()->bits());
    else
      return isZeroBit(ce->getRight(), idx);
  }
  return false; // otherwise return false
}

bool isOneBit(ExprRef e, uint32_t idx) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e))
    return ce->value()[idx];
  if (auto ce = castAs<ConcatExpr>(e)) {
    if (ce->getRight()->bits() <= idx)
      return isOneBit(ce->getLeft(), idx - ce->getRight()->bits());
    else
      return isOneBit(ce->getRight(), idx);
  }
  return false; // otherwise return false
}

bool isRelational(const Expr* e) {
  switch (e->kind()) {
    case Distinct:
    case Equal:
    case Ult:
    case Ule:
    case Ugt:
    case Uge:
    case Slt:
    case Sle:
    case Sgt:
    case Sge:
    case LAnd:
    case LOr:
    case LNot:
      return true;
    default:
      return false;
  }
}

bool isConstant(ExprRef e) {
 return e->kind() == Constant;
}

bool isConstSym(ExprRef e) {
  if (e->num_children() != 2)
    return false;
  for (uint32_t i = 0; i < 2; i++) {
    if (isConstant(e->getChild(i))
        && !isConstant(e->getChild(1 - i)))
      return true;
  }
  return false;
}

uint32_t getMSB(
    ExprRef e)
{
  uint32_t i = 0;
  assert(e->bits() >= 1);
  for (i = e->bits() - 1; i-- > 0;) {
    if (!isZeroBit(e, i))
      break;
  }

  return i + 1;
}

// Expr declaration
Expr::Expr(Kind kind, uint32_t bits)
  : DependencyNode()
  , kind_(kind)
  , bits_(bits)
  , children_()
  , hash_(NULL)
  , isConcrete_(true)
  , hasExtended(false)
  , depth_(-1)
  , deps_(NULL)
  , leading_zeros_((uint32_t)-1)
  , evaluation_(NULL)
  {}

Expr::~Expr() {
  delete hash_;
  delete deps_;
}

DependencySet Expr::computeDependencies() {
  DependencySet deps;
  for (const int& dep : getDeps()) {
    deps.insert((size_t)dep);
  }
  return deps;
}

XXH32_hash_t Expr::hash() {
  if (hash_ == NULL) {
    XXH32_state_t state;
    XXH32_reset(&state, 0); // seed = 0
    XXH32_update(&state, &kind_, sizeof(kind_));
    XXH32_update(&state, &bits_, sizeof(bits_));
    for (int32_t i = 0; i < num_children(); i++) {
      XXH32_hash_t h = children_[i]->hash();
      XXH32_update(&state, &h, sizeof(h));
    }
    hashAux(&state);
    hash_ = new XXH32_hash_t(XXH32_digest(&state));
  }
  return *hash_;
}

int32_t Expr::depth() {
  if (depth_ == -1) {
    int32_t max_depth = 0;
    for (int32_t i = 0; i < num_children(); i++) {
      int32_t child_depth = getChild(i)->depth();
      if (child_depth > max_depth)
        max_depth = child_depth;
    }
    depth_ = max_depth + 1;
  }
  return depth_;
}


void Expr::print(std::ostream& os, uint32_t depth) const {
  os << getName() << "(";
  bool begin = !printAux(os);
  printChildren(os, begin, depth);
  os << ")";
}


std::string Expr::toString() const {
  std::ostringstream stream;
  this->print(stream);
  return stream.str();
}


void Expr::printChildren(std::ostream& os, bool start, uint32_t depth) const {
  for (int32_t i = 0; i < num_children(); i++) {
    if (start)
      start = false;
    else
      os << ", ";
    children_[i]->print(os, depth + 1);
  }
}


bool Expr::isZero() const {
  if (isConstant()) {
    const ConstantExpr* me = static_cast<const ConstantExpr*>(this);
    return me->isZero();
  }
  else
    return false;
}

bool Expr::isAllOnes() const {
  if (isConstant()) {
    const ConstantExpr* me = static_cast<const ConstantExpr*>(this);
    return me->isAllOnes();
  }
  else
    return false;
}

bool Expr::isOne() const {
  if (isConstant()) {
    const ConstantExpr* me = static_cast<const ConstantExpr*>(this);
    return me->isOne();
  }
  else
    return false;
}



void ConstantExpr::print(std::ostream& os, uint32_t depth) const {
    os << "0x" << value_.toString(16, false);
}

void ConcatExpr::print(std::ostream& os, uint32_t depth) const {
  bool start = true;
  for (int32_t i = 0; i < num_children(); i++) {
    if (start)
      start = false;
    else
      os << " | ";
    children_[i]->print(os, depth + 1);
  }
}

void BinaryExpr::print(std::ostream& os, uint32_t depth, const char* op) const {
  ExprRef c0 = getChild(0);
  ExprRef c1 = getChild(1);
  bool c0_const = c0->isConstant();
  bool c1_const = c1->isConstant();

  if (!c0_const)
    os << "(";
  c0->print(os, depth + 1);
  if (!c0_const)
    os << ")";

  os << " " << op << " ";

  if (!c1_const)
    os << "(";
  c1->print(os, depth + 1);
  if (!c1_const)
    os << ")";
}

void AddExpr::print(std::ostream& os, uint32_t depth) const {
	BinaryExpr::print(os, depth, "+");
}

void SubExpr::print(std::ostream& os, uint32_t depth) const {
	BinaryExpr::print(os, depth, "-");
}

void MulExpr::print(std::ostream& os, uint32_t depth) const {
	BinaryExpr::print(os, depth, "*");
}

void SDivExpr::print(std::ostream& os, uint32_t depth) const {
	BinaryExpr::print(os, depth, "/_s");
}

void UDivExpr::print(std::ostream& os, uint32_t depth) const {
	BinaryExpr::print(os, depth, "/_u");
}

void SRemExpr::print(std::ostream& os, uint32_t depth) const {
	BinaryExpr::print(os, depth, "%_s");
}

void URemExpr::print(std::ostream& os, uint32_t depth) const {
	BinaryExpr::print(os, depth, "%_u");
}

}

