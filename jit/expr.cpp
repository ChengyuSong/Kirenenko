#include "expr.h"
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


std::string Expr::toString() const {
  std::ostringstream stream;
  this->print(stream);
  return stream.str();
}


DependencySet Expr::computeDependencies() {
  DependencySet deps;
  for (const int& dep : getDeps()) {
    deps.insert((size_t)dep);
  }
  return deps;
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


void Expr::print(std::ostream& os, uint32_t depth) const {
  os << getName() << "(";
  bool begin = !printAux(os);
  printChildren(os, begin, depth);
  os << ")";
}

void ConstantExpr::print(std::ostream& os, uint32_t depth) const {
    os << "0x" << value_.toString(16, false);
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


