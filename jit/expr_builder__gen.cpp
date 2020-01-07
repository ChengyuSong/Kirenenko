#include "expr_builder.h"
//#include "solver.h"
#include <llvm/ADT/StringRef.h>

namespace RGDPROXY {
namespace {
const int32_t kComplexityThresholdForSimplify = 16;

void addUses(ExprRef e) {
  for (int32_t i = 0; i < e->num_children(); i++)
    e->getChild(i)->addUse(e);
}

// utility function for checking values
bool isZero(ExprRef e) {
  ConstantExprRef ce = castAs<ConstantExpr>(e);
  return ce != NULL && ce->isZero();
}

bool isOne(ExprRef e) {
  ConstantExprRef ce = castAs<ConstantExpr>(e);
  return ce != NULL && ce->isOne();
}

bool isAllOnes(ExprRef e) {
  ConstantExprRef ce = castAs<ConstantExpr>(e);
  return ce != NULL && ce->isAllOnes();
}

} // namespace

bool canEvaluateTruncated(ExprRef e, uint32_t bits, uint32_t depth=0) {
  if (depth > 1)
    return false;

  switch (e->kind()) {
    default:
      return false;
    case Mul:
      return canEvaluateTruncated(e->getChild(0), depth + 1)
        && canEvaluateTruncated(e->getChild(1), depth + 1);
    case UDiv:
    case URem: {
      uint32_t high_bits = e->bits() - bits;
      if (e->getChild(0)->countLeadingZeros() >= high_bits
          && e->getChild(1)->countLeadingZeros() >= high_bits) {
        return canEvaluateTruncated(e->getChild(0), depth + 1)
          && canEvaluateTruncated(e->getChild(1), depth + 1);
      }
      else
        return false;
    }
    case ZExt:
    case SExt:
    case Constant:
    case Concat:
      return true;
  }
}

ExprRef evaluateInDifferentType(ExprBuilder* builder, ExprRef op, uint32_t index, uint32_t bits) {
  // TODO: recursive evaluation
  switch (op->kind()) {
    default:
      return NULL;
    case Mul:
    case UDiv:
    case URem: {
      ExprRef e1 = builder->createExtract(op->getChild(0), index, bits);
      ExprRef e2 = builder->createExtract(op->getChild(1), index, bits);

      return builder->createBinaryExpr(op->kind(),
          builder->createExtract(op->getChild(0), index, bits),
          builder->createExtract(op->getChild(1), index, bits));
    }
  }
}

ExprBuilder::ExprBuilder() : next_(NULL) {}

void ExprBuilder::setNext(ExprBuilder* next) {
  next_ = next;
}

ExprBuilder* SymbolicExprBuilder::create() {
  ExprBuilder* base = new BaseExprBuilder();
  ExprBuilder* commu = new CommutativeExprBuilder();
  ExprBuilder* common = new CommonSimplifyExprBuilder();
  ExprBuilder* const_folding = new ConstantFoldingExprBuilder();
  ExprBuilder* symbolic = new SymbolicExprBuilder();
  ExprBuilder* cache = new CacheExprBuilder();

  // commu -> symbolic -> common -> constant folding -> base
  commu->setNext(symbolic);
  symbolic->setNext(common);
  common->setNext(const_folding);
  const_folding->setNext(cache);
  cache->setNext(base);
  return commu;
}

ExprBuilder* ConstantFoldingExprBuilder::create() {
  // constant folding -> base
  ExprBuilder* const_folding = new ConstantFoldingExprBuilder();
  ExprBuilder* base = new BaseExprBuilder();

  // commu -> symbolic -> common -> constant folding -> base
  const_folding->setNext(base);
  return const_folding;
}

ExprRef ExprBuilder::createTrue() {
  return createBool(true);
}

ExprRef ExprBuilder::createFalse() {
  return createBool(false);
}

ExprRef ExprBuilder::createMsb(ExprRef e) {
  return createExtract(e, e->bits() - 1, 1);
}

ExprRef ExprBuilder::createLsb(ExprRef e) {
  return createExtract(e, 0, 1);
}

ExprRef ExprBuilder::bitToBool(ExprRef e) {
  RGDPROXY_ASSERT(e->bits() == 1);
  ExprRef one = createConstant(1, e->bits());
  return createEqual(e, one);
}

ExprRef ExprBuilder::boolToBit(ExprRef e, uint32_t bits) {
  std::cout << "Ju in ExprBuilder::boolToBit" << std::endl;
  ExprRef e1 = createConstant(1, bits);
  ExprRef e0 = createConstant(0, bits);
  ExprRef ret = createIte(e, e1, e0);
  /* UCR hacking */
  ret->addExtendedChild(e);
  ret->setExtended();
  ret->setExtendedOp(Set);
  return ret;
}

ExprRef ExprBuilder::createConcat(std::list<ExprRef> exprs) {
  assert(!exprs.empty());
  auto it = exprs.begin();

  // get a first element from the list
  ExprRef e = *it;
  it++;

  for (; it != exprs.end(); it++)
    e = createConcat(e, *it);

  return e;
}

ExprRef ExprBuilder::createLAnd(std::list<ExprRef> exprs) {
  assert(!exprs.empty());
  auto it = exprs.begin();

  // get a first element from the list
  ExprRef e = *it;
  it++;

  for (; it != exprs.end(); it++)
    e = createLAnd(e, *it);

  return e;
}

ExprRef ExprBuilder::createTrunc(ExprRef e, uint32_t bits) {
  return createExtract(e, 0, bits);
}

ExprRef BaseExprBuilder::createRead(uint32_t off) {
  static std::vector<ExprRef> cache;
  if (off >= cache.size())
    cache.resize(off + 1);

  if (cache[off] == NULL)
    cache[off] = std::make_shared<ReadExpr>(off);

  return cache[off];
}

ExprRef BaseExprBuilder::createExtract(ExprRef e, uint32_t index, uint32_t bits)
{
  if (bits == e->bits())
    return e;
  ExprRef ref = std::make_shared<ExtractExpr>(e, index, bits);
  addUses(ref);
  return ref;
}

ExprRef
CacheExprBuilder::findOrInsert(ExprRef new_expr) {
  if (ExprRef cached = findInCache(new_expr))
    return cached;
  RGDPROXY_ASSERT(new_expr != NULL);
  insertToCache(new_expr);
  return new_expr;
}

void CacheExprBuilder::insertToCache(ExprRef e) {
  cache_.insert(e);
}

ExprRef CacheExprBuilder::findInCache(ExprRef e) {
  return cache_.find(e);
}

ExprRef CommutativeExprBuilder::createSub(ExprRef l, ExprRef r)
{
  NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (nce_l != NULL && ce_r != NULL) {
    // X - C_0 = -C_0 + X
    return createAdd(createNeg(ce_r), nce_l);
  }
  else
    return ExprBuilder::createSub(l, r);
}

ExprRef CommonSimplifyExprBuilder::createConcat(ExprRef l, ExprRef r) {
  // C(E(e, x, y), E(e, y, z)) => E(e, x, z)
  if (auto ee_l = castAs<ExtractExpr>(l)) {
    if (auto ee_r = castAs<ExtractExpr>(r)) {
      if (ee_l->expr() == ee_r->expr()
          && ee_r->index() + ee_r->bits() == ee_l->index()) {
        return createExtract(ee_l->expr(), ee_r->index(), ee_r->bits() + ee_l->bits());
      }
    }
  }

  // C(E(Ext(e), e->bits(), bits), e) == E(Ext(e), 0, e->bits() + bits)
  if (auto ee_l = castAs<ExtractExpr>(l)) {
    if (auto ext = castAs<ExtExpr>(ee_l->expr())) {
      if (ee_l->index() == r->bits()
          && equalShallowly(*ext->expr(), *r)) {
        // Here we used equalShallowly
        // because same ExtractExpr can have different addresses,
        // but using deep comparison is expensive
        return createExtract(ee_l->expr(), 0, ee_l->bits() + r->bits());
      }
    }
  }

  return ExprBuilder::createConcat(l, r);
}

ExprRef CommonSimplifyExprBuilder::createExtract(
    ExprRef e, uint32_t index, uint32_t bits) {
  if (auto ce = castAs<ConcatExpr>(e)) {
    // skips right part
    if (index >= ce->getRight()->bits())
      return createExtract(ce->getLeft(), index - ce->getRight()->bits(), bits);

    // skips left part
    if (index + bits <= ce->getRight()->bits())
      return createExtract(ce->getRight(), index, bits);

    // E(C(C_0,y)) ==> C(E(C_0), E(y))
    if (ce->getLeft()->isConstant()) {
      return createConcat(
          createExtract(ce->getLeft(), 0, bits - ce->getRight()->bits() + index),
          createExtract(ce->getRight(), index, ce->getRight()->bits() - index));
    }
  }
  else if (auto ee = castAs<ExtExpr>(e)) {
    // E(Ext(x), i, b) && len(x) >= i + b == E(x, i, b)
    if (ee->expr()->bits() >= index + bits)
      return createExtract(ee->expr(), index, bits);

    // E(ZExt(x), i, b) && len(x) < i == 0
    if (ee->kind() == ZExt
        && index >= ee->expr()->bits())
      return createConstant(0, bits);
  }
  else if (auto ee = castAs<ExtractExpr>(e)) {
    // E(E(x, i1, b1), i2, b2) == E(x, i1 + i2, b2)
    return createExtract(ee->expr(), ee->index() + index, bits);
  }

  if (index == 0 && e->bits() == bits)
    return e;
  return ExprBuilder::createExtract(e, index, bits);
}

ExprRef CommonSimplifyExprBuilder::createZExt(
    ExprRef e, uint32_t bits) {
  // allow shrinking
  if (e->bits() > bits)
    return createExtract(e, 0, bits);
  if (e->bits() == bits)
    return e;
  return ExprBuilder::createZExt(e, bits);
}

ExprRef CommonSimplifyExprBuilder::createAdd(ExprRef l, ExprRef r)
{
  if (isZero(l))
    return r;

  return ExprBuilder::createAdd(l, r);
}

ExprRef CommonSimplifyExprBuilder::createMul(ExprRef l, ExprRef r) {
  NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  // 0 * X ==> 0
  if (isZero(l))
    return l;

  // 1 * X ==> X
  if (isOne(l))
    return r;

  return ExprBuilder::createMul(l, r);
}

ExprRef CommonSimplifyExprBuilder::simplifyAnd(ExprRef l, ExprRef r) {
  // l & 0 ==> 0
  if (isZero(l))
    return l;

  // l & 11...1b ==> l;
  if (isAllOnes(l))
    return r;

  return NULL;
}

ExprRef CommonSimplifyExprBuilder::createAnd(ExprRef l, ExprRef r)
{
  if (ExprRef simplified = simplifyAnd(l, r))
    return simplified;

  // 0x00ff0000  & 0xaabbccdd = 0x00bb0000
  if (auto const_l = castAs<ConstantExpr>(l)) {
    if (auto concat_r = castAs<ConcatExpr>(r)) {
      ExprRef r_left = concat_r->getLeft();
      ExprRef r_right = concat_r->getRight();
      ExprRef l_left = createExtract(l, r_right->bits(), r_left->bits());

      if (ExprRef and_left = simplifyAnd(l_left, r_left)) {
        return createConcat(
            and_left,
            createAnd(
              createExtract(l, 0,  r_right->bits()),
              r_right));
      }
    }
  }

  return ExprBuilder::createAnd(l, r);
}

ExprRef CommonSimplifyExprBuilder::simplifyOr(ExprRef l, ExprRef r) {
  // 0 | X ==> 0
  if (isZero(l))
    return r;

  // 111...1b | X ==> 111...1b
  if (isAllOnes(l))
    return l;

  return NULL;
}

ExprRef CommonSimplifyExprBuilder::createOr(ExprRef l, ExprRef r) {
  if (ExprRef simplified = simplifyOr(l, r))
    return simplified;

  if (auto const_l = castAs<ConstantExpr>(l)) {
    if (auto concat_r = castAs<ConcatExpr>(r)) {
      ExprRef r_left = concat_r->getLeft();
      ExprRef r_right = concat_r->getRight();
      ExprRef l_left = createExtract(l, r_right->bits(), r_left->bits());

      if (ExprRef and_left = simplifyOr(l_left, r_left)) {
        return createConcat(
            and_left,
            createOr(
              createExtract(l, 0,  r_right->bits()),
              r_right));
      }
    }
  }

  return ExprBuilder::createOr(l, r);
}

ExprRef CommonSimplifyExprBuilder::simplifyXor(ExprRef l, ExprRef r) {
  // 0 ^ X ==> X
  if (isZero(l))
    return r;

  return NULL;
}

ExprRef CommonSimplifyExprBuilder::createXor(ExprRef l, ExprRef r) {
  if (ExprRef simplified = simplifyXor(l, r))
    return simplified;

  if (auto const_l = castAs<ConstantExpr>(l)) {
    if (auto concat_r = castAs<ConcatExpr>(r)) {
      ExprRef r_left = concat_r->getLeft();
      ExprRef r_right = concat_r->getRight();
      ExprRef l_left = createExtract(l, r_right->bits(), r_left->bits());

      if (ExprRef and_left = simplifyXor(l_left, r_left)) {
        return createConcat(
            and_left,
            createXor(
              createExtract(l, 0,  r_right->bits()),
              r_right));
      }
    }
  }

  return ExprBuilder::createXor(l, r);
}

ExprRef CommonSimplifyExprBuilder::createShl(ExprRef l, ExprRef r) {
  if (isZero(l))
    return l;

  if (ConstantExprRef ce_r = castAs<ConstantExpr>(r)) {
    uint32_t rval = ce_r->value().getLimitedValue();
    if (rval == 0)
      return l;

    // l << larger_than_l_size == 0
    if (rval >= l->bits())
      return createConstant(0, l->bits());

    // from z3: (bvshl x k) -> (concat (extract [n-1-k:0] x) bv0:k)
    // but byte granuality
    if (rval % CHAR_BIT == 0) {
      ExprRef zero = createConstant(0, rval);
      ExprRef partial = createExtract(l, 0, l->bits() - rval);
      return createConcat(partial, zero);
    }
  }

  return ExprBuilder::createShl(l, r);
}

ExprRef CommonSimplifyExprBuilder::createLShr(ExprRef l, ExprRef r) {
  if (isZero(l))
    return l;

  if (ConstantExprRef ce_r = castAs<ConstantExpr>(r)) {
    uint32_t rval = ce_r->value().getLimitedValue();
    if (rval == 0)
      return l;

    // l << larger_than_l_size == 0
    if (rval >= l->bits())
      return createConstant(0, l->bits());

    // from z3: (bvlshr x k) -> (concat bv0:k (extract [n-1:k] x))
    // but byte granuality
    if (rval % CHAR_BIT == 0) {
      ExprRef zero = createConstant(0, rval);
      ExprRef partial = createExtract(l, rval, l->bits() - rval);
      return createConcat(zero, partial);
    }
  }

  return ExprBuilder::createLShr(l, r);
}

ExprRef CommonSimplifyExprBuilder::createAShr(ExprRef l, ExprRef r) {
  if (ConstantExprRef ce_r = castAs<ConstantExpr>(r)) {
    uint32_t rval = ce_r->value().getLimitedValue();
    if (rval == 0)
      return l;
  }

  return ExprBuilder::createAShr(l, r);
}

ExprRef CommonSimplifyExprBuilder::createEqual(ExprRef l, ExprRef r) {
  NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (auto be_l = castAs<BoolExpr>(l))
    return (be_l->value()) ? r : createLNot(r);

  return ExprBuilder::createEqual(l, r);
}

ExprRef ConstantFoldingExprBuilder::createDistinct(ExprRef l, ExprRef r) {
  ConstantExprRef ce_l = castAs<ConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (ce_l != NULL && ce_r != NULL) {
    RGDPROXY_ASSERT(l->bits() == r->bits());
    return createBool(ce_l->value() != ce_r->value());
  }

  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL) {
    return createBool(be0->value() != be1->value());
  }

  return ExprBuilder::createDistinct(l, r);
}

ExprRef ConstantFoldingExprBuilder::createEqual(ExprRef l, ExprRef r) {
  ConstantExprRef ce_l = castAs<ConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (ce_l != NULL && ce_r != NULL) {
    RGDPROXY_ASSERT(l->bits() == r->bits());
    return createBool(ce_l->value() == ce_r->value());
  }

  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL)
    return createBool(be0->value() == be1->value());

  return ExprBuilder::createEqual(l, r);
}

ExprRef ConstantFoldingExprBuilder::createLAnd(ExprRef l, ExprRef r) {
  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL)
    return createBool(be0->value() && be1->value());
  else
    return ExprBuilder::createLAnd(l, r);
}

ExprRef ConstantFoldingExprBuilder::createLOr(ExprRef l, ExprRef r) {
  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL)
    return createBool(be0->value() || be1->value());
  else
    return ExprBuilder::createLOr(l, r);
}

ExprRef ConstantFoldingExprBuilder::createConcat(ExprRef l, ExprRef r) {
  // C(l, r) && l == constant && r == constant  => l << r_bits | r
  ConstantExprRef ce_l = castAs<ConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (ce_l != NULL && ce_r != NULL) {
    uint32_t bits = ce_l->bits() + ce_r->bits();
    llvm::APInt lval = ce_l->value().zext(bits);
    llvm::APInt rval = ce_r->value().zext(bits);
    llvm::APInt res = (lval << ce_r->bits()) | rval;
    return createConstant(res, bits);
  }
  else
    return ExprBuilder::createConcat(l, r);
}

ExprRef ConstantFoldingExprBuilder::createIte(ExprRef expr_cond,
    ExprRef expr_true, ExprRef expr_false) {
  if (auto be = castAs<BoolExpr>(expr_cond)) {
    if (be->value())
      return expr_true;
    else
      return expr_false;
  }

  return ExprBuilder::createIte(expr_cond, expr_true, expr_false);
}

ExprRef ConstantFoldingExprBuilder::createExtract(
    ExprRef e, uint32_t index, uint32_t bits) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e)) {
    llvm::APInt v = ce->value().lshr(index);
    v = v.zextOrTrunc(bits);
    return createConstant(v, bits);
  }
  else
    return ExprBuilder::createExtract(e, index, bits);
}

ExprRef ConstantFoldingExprBuilder::createZExt(ExprRef e, uint32_t bits) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e)) {
    return createConstant(ce->value().zext(bits), bits);
  }
  else
    return ExprBuilder::createZExt(e, bits);
}

ExprRef ConstantFoldingExprBuilder::createSExt(ExprRef e, uint32_t bits) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e)) {
    return createConstant(ce->value().sext(bits), bits);
  }
  else
    return ExprBuilder::createSExt(e, bits);
}

ExprRef ConstantFoldingExprBuilder::createNeg(ExprRef e) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e))
    return createConstant(-ce->value(), ce->bits());
  else
    return ExprBuilder::createNeg(e);
}

ExprRef ConstantFoldingExprBuilder::createNot(ExprRef e) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e))
    return createConstant(~ce->value(), ce->bits());
  else
    return ExprBuilder::createNot(e);
}

ExprRef ConstantFoldingExprBuilder::createLNot(ExprRef e) {
  if (BoolExprRef be = castAs<BoolExpr>(e))
    return createBool(!be->value());
  else
    return ExprBuilder::createLNot(e);
}

ExprRef SymbolicExprBuilder::createConcat(ExprRef l, ExprRef r) {
  // C(l, C(x, y)) && l, x == constant => C(l|x, y)
  if (auto ce = castAs<ConcatExpr>(r)) {
    ConstantExprRef ce_l = castAs<ConstantExpr>(l);
    ConstantExprRef ce_x = castAs<ConstantExpr>(ce->getLeft());
    if (ce_l != NULL && ce_x != NULL)
      return createConcat(createConcat(ce_l, ce_x), ce->getRight());
  }

  // C(C(x ,y), z) => C(x, C(y, z))
  if (auto ce = castAs<ConcatExpr>(l)) {
    return createConcat(l->getLeft(),
        createConcat(l->getRight(), r));
  }

  return ExprBuilder::createConcat(l, r);
}

ExprRef SymbolicExprBuilder::createExtract(ExprRef op, uint32_t index, uint32_t bits) {
  // Only byte-wise simplification
  if (index == 0
      && bits % 8 == 0
      && canEvaluateTruncated(op, bits)) {
      if (ExprRef e = evaluateInDifferentType(this, op, index, bits))
        return e;
  }
  return ExprBuilder::createExtract(op, index, bits);
}

ExprRef SymbolicExprBuilder::simplifyExclusiveExpr(ExprRef l, ExprRef r) {
  // From z3
  // (bvor (concat x #x00) (concat #x00 y)) --> (concat x y)
  // (bvadd (concat x #x00) (concat #x00 y)) --> (concat x y)

  for (uint32_t i = 0; i < l->bits(); i++)
    if (!isZeroBit(l, i) && !isZeroBit(r, i))
      return NULL;

  std::list<ExprRef> exprs;
  uint32_t i = 0;
  while (i < l->bits()) {
    uint32_t prev = i;
    while (i < l->bits() && isZeroBit(l, i))
      i++;
    if (i != prev)
      exprs.push_front(createExtract(r, prev, i - prev));
    prev = i;
    while (i < r->bits() && isZeroBit(r, i))
      i++;
    if (i != prev)
      exprs.push_front(createExtract(l, prev, i - prev));
  }

  return ExprBuilder::createConcat(exprs);
}

ExprRef SymbolicExprBuilder::createAdd(ExprRef l, ExprRef r) {
  if (ExprRef e = simplifyExclusiveExpr(l, r))
    return e;

  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createAdd(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      RGDPROXY_ASSERT(nce_l != NULL);
      return createAdd(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createAdd(l, r);
}

ExprRef SymbolicExprBuilder::createAdd(ConstantExprRef l, NonConstantExprRef r) {
  switch (r->kind()) {
    case Add: {
      // C_0 + (C_1 + X) ==> (C_0 + C_1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(createAdd(l, CE), r->getSecondChild());
      // C_0 + (X + C_1) ==> (C_0 + C_1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createAdd(l, CE), r->getFirstChild());
      break;
    }

    case Sub: {
      // C_0 + (C_1 - X) ==> (C_0 + C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createSub(createAdd(l, CE), r->getSecondChild());
      // C_0 + (X - C_1) ==> (C_0 - C1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createSub(l, CE), r->getFirstChild());
      break;
    }
    default:
      break;
  }

  return ExprBuilder::createAdd(l, r);
}

ExprRef SymbolicExprBuilder::createAdd(NonConstantExprRef l, NonConstantExprRef r) {
  if (l == r) {
    // l + l ==> 2 * l
    ExprRef two = createConstant(2, l->bits());
    return createMul(two, l);
  }

  switch (l->kind()) {
    default: break;
    case Add:
    case Sub: {
      // (X + Y) + Z ==> Z + (X + Y)
      // Or (X - Y) + Z ==> Z + (X - Y)
      std::swap(l, r);
    }
  }

  switch (r->kind()) {
    case Add: {
      // X + (C_0 + Y) ==> C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(CE, createAdd(l, r->getSecondChild()));
      // X + (Y + C_0) ==> C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(CE, createAdd(l, r->getFirstChild()));
      break;
    }

    case Sub: {
      // X + (C_0 - Y) ==> C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(CE, createSub(l, r->getSecondChild()));
      // X + (Y - C_0) ==> -C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createNeg(CE), createAdd(l, r->getFirstChild()));
      break;
    }
    default:
      break;
  }

  return ExprBuilder::createAdd(l, r);
}

ExprRef SymbolicExprBuilder::createSub(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createSub(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      RGDPROXY_ASSERT(nce_l != NULL);
      return createSub(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createSub(l, r);
}

ExprRef SymbolicExprBuilder::createSub(ConstantExprRef l, NonConstantExprRef r) {
  switch (r->kind()) {
    case Add: {
      // C_0 - (C_1 + X) ==> (C_0 - C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createSub(createSub(l, CE), r->getSecondChild());
      // C_0 - (X + C_1) ==> (C_0 - C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createSub(createSub(l, CE), r->getFirstChild());
      break;
    }

    case Sub: {
      // C_0 - (C_1 - X) ==> (C_0 - C1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild())) {
        return createAdd(createSub(l, CE), r->getSecondChild());
      }
      // C_0 - (X - C_1) ==> (C_0 + C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild())) {
        return createSub(createAdd(l, CE), r->getFirstChild());
      }
      break;
    }
    default:
      break;
  }

  return ExprBuilder::createSub(l, r);
}

ExprRef SymbolicExprBuilder::createSub(
    NonConstantExprRef l,
    NonConstantExprRef r) {
  // X - X ==> 0
  if (l == r)
    return createConstant(0, l->bits());

  switch (l->kind()) {
    default: break;
    case Add:
      if (l->getChild(0)->isConstant()) {
        // (C + Y) - Z ==> C + (Y - Z)
        return createAdd(l->getChild(0),
            createSub(l->getChild(1), r));
      }
    case Sub: {
      if (l->getChild(0)->isConstant()) {
        // (C - Y) - Z ==> C - (Y + Z)
        return createSub(l->getChild(0),
            createAdd(l->getChild(1), r));
      }
    }
  }

  switch (r->kind()) {
    case Add: {
      // X - (C_0 + Y) ==> -C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(createNeg(CE), createSub(l, r->getSecondChild()));
      // X - (Y + C_0) ==> -C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createNeg(CE), createSub(l, r->getFirstChild()));
      break;
    }

    case Sub: {
      // X - (C_0 - Y) ==> -C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(createNeg(CE), createAdd(l, r->getSecondChild()));
      // X - (Y - C_0) ==> C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(CE, createSub(l, r->getFirstChild()));
      break;
    }
    default:
      break;
  }
  return ExprBuilder::createSub(l, r);
}

ExprRef SymbolicExprBuilder::createMul(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createMul(ce_l, nce_r);
  }

  return ExprBuilder::createMul(l, r);
}

ExprRef SymbolicExprBuilder::createMul(ConstantExprRef l, NonConstantExprRef r) {
  // C_0 * (C_1 * x) ==> (C_0 * C_1) * x
  if (auto me = castAs<MulExpr>(r)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(r->getLeft())) {
      return createMul(createMul(l, ce), r->getRight());
    }
  }

  // C_0 * (C_1 + x) ==> C_0 * C_1 + C_0 * x
  if (auto ae = castAs<AddExpr>(r)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(r->getLeft())) {
      return createAdd(createMul(l, ce), createMul(l, r->getRight()));
    }
  }

  return ExprBuilder::createMul(l, r);
}

ExprRef SymbolicExprBuilder::createSDiv(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_l = castAs<NonConstantExpr>(l)) {
    if (ConstantExprRef ce_r = castAs<ConstantExpr>(r))
      return createSDiv(nce_l, ce_r);
  }

  return ExprBuilder::createSDiv(l, r);
}

ExprRef SymbolicExprBuilder::createSDiv(NonConstantExprRef l, ConstantExprRef r) {
  // x /s -1 = -x
  if (r->isAllOnes())
    return createNeg(l);

  // SExt(x) /s y && x->bits() >= y->getActiveBits() ==> SExt(x /s y)
  // Only works when y != -1, but already handled by the above statement
  if (auto sext_l = castAs<SExtExpr>(l)) {
    ExprRef x = sext_l->expr();
    if (x->bits() >= r->getActiveBits()) {
      return createSExt(
              createSDiv(x,
                createExtract(r, 0, x->bits())),
              l->bits());
    }
  }

  // TODO: add overflow check
  // (x / C_0) / C_1 = (x / (C_0 * C_1))
  if (auto se = castAs<SDivExpr>(l)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(l->getRight())) {
      return createSDiv(l->getLeft(), createMul(ce, r));
    }
  }
  return ExprBuilder::createSDiv(l, r);
}

ExprRef SymbolicExprBuilder::createUDiv(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_l = castAs<NonConstantExpr>(l)) {
    if (ConstantExprRef ce_r = castAs<ConstantExpr>(r))
      return createUDiv(nce_l, ce_r);
  }

  return ExprBuilder::createUDiv(l, r);
}

ExprRef SymbolicExprBuilder::createUDiv(NonConstantExprRef l, ConstantExprRef r) {
  // C(0, x) / y && y->getActiveBits() <= x->bits()
  // == C(0, x/E(y, 0, x->bits()))
  if (auto ce = castAs<ConcatExpr>(l)) {
    ExprRef ce_l = ce->getLeft();
    ExprRef ce_r = ce->getRight();
    if (ce_l->isZero()) {
      if (r->getActiveBits() <= ce_r->bits()) {
        ExprRef e = createConcat(
            ce_l,
            createUDiv(
              ce_r,
              createExtract(r, 0, ce_r->bits())));
        return e;
      }
    }
  }

  // TODO: add overflow check
  // (x / C_0) / C_1 = (x / (C_0 * C_1))
  if (auto se = castAs<UDivExpr>(l)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(l->getRight())) {
      return createUDiv(l->getLeft(), createMul(ce, r));
    }
  }
  return ExprBuilder::createUDiv(l, r);
}

ExprRef SymbolicExprBuilder::createAnd(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createAnd(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      RGDPROXY_ASSERT(nce_l != NULL);
      return createAnd(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createAnd(l, r);
}

ExprRef SymbolicExprBuilder::createAnd(ConstantExprRef l, NonConstantExprRef r) {
  return ExprBuilder::createAnd(l, r);
}

ExprRef SymbolicExprBuilder::createAnd(NonConstantExprRef l, NonConstantExprRef r) {
  // A & A  ==> A
  if (l == r)
    return l;

  // C(x, y) & C(w, v) ==> C(x & w, y & v)
  if (auto ce_l = castAs<ConcatExpr>(l)) {
    if (auto ce_r = castAs<ConcatExpr>(r)) {
      if (ce_l->getLeft()->bits() == ce_r->getLeft()->bits()) {
        // right bits are same, because it is binary operation
        return createConcat(
            createAnd(l->getLeft(), r->getLeft()),
            createAnd(l->getRight(), r->getRight()));
      }
    }
  }
  return ExprBuilder::createAnd(l, r);
}

ExprRef SymbolicExprBuilder::createOr(ExprRef l, ExprRef r) {
 if (ExprRef e = simplifyExclusiveExpr(l, r))
    return e;

  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createOr(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      RGDPROXY_ASSERT(nce_l != NULL);
      return createOr(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createOr(l, r);
}

ExprRef SymbolicExprBuilder::createOr(ConstantExprRef l, NonConstantExprRef r) {
  if (auto ce = castAs<ConcatExpr>(r)) {
    // C_0 | C(x, y) ==> C(C_0 | x, C_0 | y)
    // TODO: only for constant case
    return createConcat(
        createOr(
          createExtract(l, ce->getRight()->bits(), ce->getLeft()->bits()),
          ce->getLeft()),
        createOr(
          createExtract(l, 0, ce->getRight()->bits()),
          ce->getRight()));
  }

  return ExprBuilder::createOr(l, r);
}

ExprRef SymbolicExprBuilder::createOr(NonConstantExprRef l, NonConstantExprRef r) {
  // A | A = A
  if (l == r)
    return l;

  // C(x, y) & C(w, v) == C(x | w, y | v)
  if (auto ce_l = castAs<ConcatExpr>(l)) {
    if (auto ce_r = castAs<ConcatExpr>(r)) {
      if (ce_l->getLeft()->bits() == ce_r->getLeft()->bits()) {
        // right bits are same, because it is binary operation
        return createConcat(
            createOr(l->getLeft(), r->getLeft()),
            createOr(l->getRight(), r->getRight()));
      }
    }
  }

  return ExprBuilder::createOr(l, r);
}

ExprRef SymbolicExprBuilder::createXor(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (NonConstantExprRef nce_l = castAs<NonConstantExpr>(l)) {
      return createXor(nce_l, nce_r);
    }
  }

  return ExprBuilder::createXor(l, r);
}

ExprRef SymbolicExprBuilder::createXor(NonConstantExprRef l, NonConstantExprRef r) {
  if (l == r)
    return createConstant(0, l->bits());
  else
    return ExprBuilder::createXor(l, r);
}

ExprRef SymbolicExprBuilder::createEqual(ExprRef l, ExprRef r) {
  if (l == r)
    return createTrue();

  return ExprBuilder::createEqual(l, r);
}

ExprRef SymbolicExprBuilder::createDistinct(ExprRef l, ExprRef r) {
  return createLNot(createEqual(l, r));
}

ExprRef SymbolicExprBuilder::createLOr(ExprRef l, ExprRef r) {
  if (auto BE_L = castAs<BoolExpr>(l))
    return BE_L->value() ? createTrue() : r;

  if (auto BE_R = castAs<BoolExpr>(r))
    return BE_R->value() ? createTrue() : l;

  return ExprBuilder::createLOr(l, r);
}

ExprRef SymbolicExprBuilder::createLAnd(ExprRef l, ExprRef r) {
  if (auto BE_L = castAs<BoolExpr>(l))
    return BE_L->value() ? r : createFalse();

  if (auto BE_R = castAs<BoolExpr>(r))
    return BE_R->value() ? l : createFalse();

  return ExprBuilder::createLAnd(l, r);
}

ExprRef SymbolicExprBuilder::createLNot(ExprRef e) {
  if (auto BE = castAs<BoolExpr>(e))
    return createBool(!BE->value());
  if (auto NE = castAs<LNotExpr>(e))
    return NE->expr();
  return ExprBuilder::createLNot(e);
}

ExprRef SymbolicExprBuilder::createIte(
    ExprRef expr_cond,
    ExprRef expr_true,
    ExprRef expr_false) {
  if (auto BE = castAs<BoolExpr>(expr_cond))
    return BE->value() ? expr_true : expr_false;
  if (auto NE = castAs<LNotExpr>(expr_cond))
    return createIte(NE->expr(), expr_false, expr_true);
  return ExprBuilder::createIte(expr_cond, expr_true, expr_false);
}

/*
ExprBuilder* PruneExprBuilder::create() {
  ExprBuilder* base = new BaseExprBuilder();
  ExprBuilder* commu = new CommutativeExprBuilder();
  ExprBuilder* common = new CommonSimplifyExprBuilder();
  ExprBuilder* const_folding = new ConstantFoldingExprBuilder();
  ExprBuilder* symbolic = new SymbolicExprBuilder();
  ExprBuilder* cache = new CacheExprBuilder();
  ExprBuilder* fuzz = new PruneExprBuilder();

  // commu -> symbolic -> common -> constant folding -> fuzz -> cache -> base
  commu->setNext(symbolic);
  symbolic->setNext(common);
  common->setNext(const_folding);
  const_folding->setNext(fuzz);
  fuzz->setNext(cache);
  cache->setNext(base);
  return commu;
}
*/

ExprRef ExprBuilder::createBool(bool b)
{
	return next_->createBool(b);
}

ExprRef ExprBuilder::createConstant(uint32_t value, uint32_t bits)
{
	return next_->createConstant(value, bits);
}

ExprRef ExprBuilder::createConstant(llvm::APInt value, uint32_t bits)
{
	return next_->createConstant(value, bits);
}

ExprRef ExprBuilder::createRead(uint32_t off)
{
	return next_->createRead(off);
}

ExprRef ExprBuilder::createConcat(ExprRef l, ExprRef r)
{
	return next_->createConcat(l, r);
}

ExprRef ExprBuilder::createExtract(ExprRef e, uint32_t index, uint32_t bits)
{
	return next_->createExtract(e, index, bits);
}

ExprRef ExprBuilder::createZExt(ExprRef e, uint32_t bits)
{
	return next_->createZExt(e, bits);
}

ExprRef ExprBuilder::createSExt(ExprRef e, uint32_t bits)
{
	return next_->createSExt(e, bits);
}

ExprRef ExprBuilder::createAdd(ExprRef l, ExprRef r)
{
	return next_->createAdd(l, r);
}

ExprRef ExprBuilder::createSub(ExprRef l, ExprRef r)
{
	return next_->createSub(l, r);
}

ExprRef ExprBuilder::createMul(ExprRef l, ExprRef r)
{
	return next_->createMul(l, r);
}

ExprRef ExprBuilder::createUDiv(ExprRef l, ExprRef r)
{
	return next_->createUDiv(l, r);
}

ExprRef ExprBuilder::createSDiv(ExprRef l, ExprRef r)
{
	return next_->createSDiv(l, r);
}

ExprRef ExprBuilder::createURem(ExprRef l, ExprRef r)
{
	return next_->createURem(l, r);
}

ExprRef ExprBuilder::createSRem(ExprRef l, ExprRef r)
{
	return next_->createSRem(l, r);
}

ExprRef ExprBuilder::createNeg(ExprRef e)
{
	return next_->createNeg(e);
}

ExprRef ExprBuilder::createNot(ExprRef e)
{
	return next_->createNot(e);
}

ExprRef ExprBuilder::createAnd(ExprRef l, ExprRef r)
{
	return next_->createAnd(l, r);
}

ExprRef ExprBuilder::createOr(ExprRef l, ExprRef r)
{
	return next_->createOr(l, r);
}

ExprRef ExprBuilder::createXor(ExprRef l, ExprRef r)
{
	return next_->createXor(l, r);
}

ExprRef ExprBuilder::createShl(ExprRef l, ExprRef r)
{
	return next_->createShl(l, r);
}

ExprRef ExprBuilder::createLShr(ExprRef l, ExprRef r)
{
	return next_->createLShr(l, r);
}

ExprRef ExprBuilder::createAShr(ExprRef l, ExprRef r)
{
	return next_->createAShr(l, r);
}

ExprRef ExprBuilder::createEqual(ExprRef l, ExprRef r)
{
	return next_->createEqual(l, r);
}

ExprRef ExprBuilder::createDistinct(ExprRef l, ExprRef r)
{
	return next_->createDistinct(l, r);
}

ExprRef ExprBuilder::createUlt(ExprRef l, ExprRef r)
{
	return next_->createUlt(l, r);
}

ExprRef ExprBuilder::createUle(ExprRef l, ExprRef r)
{
	return next_->createUle(l, r);
}

ExprRef ExprBuilder::createUgt(ExprRef l, ExprRef r)
{
	return next_->createUgt(l, r);
}

ExprRef ExprBuilder::createUge(ExprRef l, ExprRef r)
{
	return next_->createUge(l, r);
}

ExprRef ExprBuilder::createSlt(ExprRef l, ExprRef r)
{
	return next_->createSlt(l, r);
}

ExprRef ExprBuilder::createSle(ExprRef l, ExprRef r)
{
	return next_->createSle(l, r);
}

ExprRef ExprBuilder::createSgt(ExprRef l, ExprRef r)
{
	return next_->createSgt(l, r);
}

ExprRef ExprBuilder::createSge(ExprRef l, ExprRef r)
{
	return next_->createSge(l, r);
}

ExprRef ExprBuilder::createLOr(ExprRef l, ExprRef r)
{
	return next_->createLOr(l, r);
}

ExprRef ExprBuilder::createLAnd(ExprRef l, ExprRef r)
{
	return next_->createLAnd(l, r);
}

ExprRef ExprBuilder::createLNot(ExprRef e)
{
	return next_->createLNot(e);
}

ExprRef ExprBuilder::createIte(ExprRef expr_cond, ExprRef expr_true, ExprRef expr_false)
{
	return next_->createIte(expr_cond, expr_true, expr_false);
}

ExprRef ExprBuilder::createBinaryExpr(Kind kind, ExprRef l, ExprRef r) {

	switch (kind) {
		case Add:
			return createAdd(l, r);
		case Sub:
			return createSub(l, r);
		case Mul:
			return createMul(l, r);
		case UDiv:
			return createUDiv(l, r);
		case SDiv:
			return createSDiv(l, r);
		case URem:
			return createURem(l, r);
		case SRem:
			return createSRem(l, r);
		case And:
			return createAnd(l, r);
		case Or:
			return createOr(l, r);
		case Xor:
			return createXor(l, r);
		case Shl:
			return createShl(l, r);
		case LShr:
			return createLShr(l, r);
		case AShr:
			return createAShr(l, r);
		case Equal:
			return createEqual(l, r);
		case Distinct:
			return createDistinct(l, r);
		case Ult:
			return createUlt(l, r);
		case Ule:
			return createUle(l, r);
		case Ugt:
			return createUgt(l, r);
		case Uge:
			return createUge(l, r);
		case Slt:
			return createSlt(l, r);
		case Sle:
			return createSle(l, r);
		case Sgt:
			return createSgt(l, r);
		case Sge:
			return createSge(l, r);
		case LOr:
			return createLOr(l, r);
		case LAnd:
			return createLAnd(l, r);
		default:
			LOG_FATAL("Non-binary expr: " + std::to_string(kind) + "\n");
			return NULL;
	}
}

ExprRef ExprBuilder::createUnaryExpr(Kind kind, ExprRef e) {
	switch (kind) {		case Not:
			return createNot(e);
		case Neg:
			return createNeg(e);
		case LNot:
			return createLNot(e);
		default:
			LOG_FATAL("Non-unary expr: " + std::to_string(kind) + "\n");
			return NULL;
	}
}

ExprRef BaseExprBuilder::createBool(bool b) {
	ExprRef ref = std::make_shared<BoolExpr>(b);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createConstant(uint32_t value, uint32_t bits) {
	ExprRef ref = std::make_shared<ConstantExpr>(value, bits);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createConstant(llvm::APInt value, uint32_t bits) {
	ExprRef ref = std::make_shared<ConstantExpr>(value, bits);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createConcat(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<ConcatExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createZExt(ExprRef e, uint32_t bits) {
	ExprRef ref = std::make_shared<ZExtExpr>(e, bits);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSExt(ExprRef e, uint32_t bits) {
	ExprRef ref = std::make_shared<SExtExpr>(e, bits);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createAdd(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<AddExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSub(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<SubExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createMul(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<MulExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createUDiv(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<UDivExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSDiv(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<SDivExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createURem(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<URemExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSRem(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<SRemExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createNeg(ExprRef e) {
	ExprRef ref = std::make_shared<NegExpr>(e);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createNot(ExprRef e) {
	ExprRef ref = std::make_shared<NotExpr>(e);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createAnd(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<AndExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createOr(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<OrExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createXor(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<XorExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createShl(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<ShlExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createLShr(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<LShrExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createAShr(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<AShrExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createEqual(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<EqualExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createDistinct(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<DistinctExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createUlt(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<UltExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createUle(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<UleExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createUgt(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<UgtExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createUge(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<UgeExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSlt(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<SltExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSle(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<SleExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSgt(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<SgtExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createSge(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<SgeExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createLOr(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<LOrExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createLAnd(ExprRef l, ExprRef r) {
	ExprRef ref = std::make_shared<LAndExpr>(l, r);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createLNot(ExprRef e) {
	ExprRef ref = std::make_shared<LNotExpr>(e);
	addUses(ref);
	return ref;
}

ExprRef BaseExprBuilder::createIte(ExprRef expr_cond, ExprRef expr_true, ExprRef expr_false) {
	ExprRef ref = std::make_shared<IteExpr>(expr_cond, expr_true, expr_false);
	addUses(ref);
	return ref;
}

ExprRef CacheExprBuilder::createConcat(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createConcat(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createExtract(ExprRef e, uint32_t index, uint32_t bits) {
	ExprRef new_expr = ExprBuilder::createExtract(e, index, bits);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createZExt(ExprRef e, uint32_t bits) {
	ExprRef new_expr = ExprBuilder::createZExt(e, bits);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSExt(ExprRef e, uint32_t bits) {
	ExprRef new_expr = ExprBuilder::createSExt(e, bits);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createAdd(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createAdd(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSub(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createSub(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createMul(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createMul(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createUDiv(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createUDiv(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSDiv(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createSDiv(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createURem(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createURem(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSRem(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createSRem(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createNeg(ExprRef e) {
	ExprRef new_expr = ExprBuilder::createNeg(e);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createNot(ExprRef e) {
	ExprRef new_expr = ExprBuilder::createNot(e);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createAnd(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createAnd(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createOr(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createOr(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createXor(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createXor(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createShl(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createShl(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createLShr(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createLShr(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createAShr(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createAShr(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createEqual(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createEqual(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createDistinct(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createDistinct(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createUlt(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createUlt(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createUle(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createUle(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createUgt(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createUgt(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createUge(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createUge(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSlt(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createSlt(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSle(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createSle(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSgt(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createSgt(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createSge(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createSge(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createLOr(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createLOr(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createLAnd(ExprRef l, ExprRef r) {
	ExprRef new_expr = ExprBuilder::createLAnd(l, r);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createLNot(ExprRef e) {
	ExprRef new_expr = ExprBuilder::createLNot(e);
	return findOrInsert(new_expr);
}

ExprRef CacheExprBuilder::createIte(ExprRef expr_cond, ExprRef expr_true, ExprRef expr_false) {
	ExprRef new_expr = ExprBuilder::createIte(expr_cond, expr_true, expr_false);
	return findOrInsert(new_expr);
}

ExprRef CommutativeExprBuilder::createAdd(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createAdd(ce_r, nce_l);

	return ExprBuilder::createAdd(l, r);
}

ExprRef CommutativeExprBuilder::createMul(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createMul(ce_r, nce_l);

	return ExprBuilder::createMul(l, r);
}

ExprRef CommutativeExprBuilder::createAnd(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createAnd(ce_r, nce_l);

	return ExprBuilder::createAnd(l, r);
}

ExprRef CommutativeExprBuilder::createOr(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createOr(ce_r, nce_l);

	return ExprBuilder::createOr(l, r);
}

ExprRef CommutativeExprBuilder::createXor(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createXor(ce_r, nce_l);

	return ExprBuilder::createXor(l, r);
}

ExprRef CommutativeExprBuilder::createEqual(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createEqual(ce_r, nce_l);

	return ExprBuilder::createEqual(l, r);
}

ExprRef CommutativeExprBuilder::createDistinct(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createDistinct(ce_r, nce_l);

	return ExprBuilder::createDistinct(l, r);
}

ExprRef CommutativeExprBuilder::createUlt(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createUgt(ce_r, nce_l);

	return ExprBuilder::createUlt(l, r);
}

ExprRef CommutativeExprBuilder::createUle(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createUge(ce_r, nce_l);

	return ExprBuilder::createUle(l, r);
}

ExprRef CommutativeExprBuilder::createUgt(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createUlt(ce_r, nce_l);

	return ExprBuilder::createUgt(l, r);
}

ExprRef CommutativeExprBuilder::createUge(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createUle(ce_r, nce_l);

	return ExprBuilder::createUge(l, r);
}

ExprRef CommutativeExprBuilder::createSlt(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createSgt(ce_r, nce_l);

	return ExprBuilder::createSlt(l, r);
}

ExprRef CommutativeExprBuilder::createSle(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createSge(ce_r, nce_l);

	return ExprBuilder::createSle(l, r);
}

ExprRef CommutativeExprBuilder::createSgt(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createSlt(ce_r, nce_l);

	return ExprBuilder::createSgt(l, r);
}

ExprRef CommutativeExprBuilder::createSge(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createSle(ce_r, nce_l);

	return ExprBuilder::createSge(l, r);
}

ExprRef CommutativeExprBuilder::createLAnd(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createLAnd(ce_r, nce_l);

	return ExprBuilder::createLAnd(l, r);
}

ExprRef CommutativeExprBuilder::createLOr(ExprRef l, ExprRef r) {
	NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (nce_l != NULL && ce_r != NULL)
		return createLOr(ce_r, nce_l);

	return ExprBuilder::createLOr(l, r);
}

ExprRef ConstantFoldingExprBuilder::createAShr(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value().ashr(ce_r->value()), l->bits());
	}
	else
	return ExprBuilder::createAShr(l, r);
}

ExprRef ConstantFoldingExprBuilder::createAdd(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value() + ce_r->value(), l->bits());
	}
	else
	return ExprBuilder::createAdd(l, r);
}

ExprRef ConstantFoldingExprBuilder::createAnd(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value() & ce_r->value(), l->bits());
	}
	else
	return ExprBuilder::createAnd(l, r);
}

ExprRef ConstantFoldingExprBuilder::createLShr(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value().lshr(ce_r->value()), l->bits());
	}
	else
	return ExprBuilder::createLShr(l, r);
}

ExprRef ConstantFoldingExprBuilder::createMul(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value() * ce_r->value(), l->bits());
	}
	else
	return ExprBuilder::createMul(l, r);
}

ExprRef ConstantFoldingExprBuilder::createOr(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value() | ce_r->value(), l->bits());
	}
	else
	return ExprBuilder::createOr(l, r);
}

ExprRef ConstantFoldingExprBuilder::createSDiv(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value().sdiv(ce_r->value()), l->bits());
	}
	else
	return ExprBuilder::createSDiv(l, r);
}

ExprRef ConstantFoldingExprBuilder::createSRem(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value().srem(ce_r->value()), l->bits());
	}
	else
	return ExprBuilder::createSRem(l, r);
}

ExprRef ConstantFoldingExprBuilder::createSge(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().sge(ce_r->value()));
	}
	else
	return ExprBuilder::createSge(l, r);
}

ExprRef ConstantFoldingExprBuilder::createSgt(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().sgt(ce_r->value()));
	}
	else
	return ExprBuilder::createSgt(l, r);
}

ExprRef ConstantFoldingExprBuilder::createShl(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value() << ce_r->value(), l->bits());
	}
	else
	return ExprBuilder::createShl(l, r);
}

ExprRef ConstantFoldingExprBuilder::createSle(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().sle(ce_r->value()));
	}
	else
	return ExprBuilder::createSle(l, r);
}

ExprRef ConstantFoldingExprBuilder::createSlt(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().slt(ce_r->value()));
	}
	else
	return ExprBuilder::createSlt(l, r);
}

ExprRef ConstantFoldingExprBuilder::createSub(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value() - ce_r->value(), l->bits());
	}
	else
	return ExprBuilder::createSub(l, r);
}

ExprRef ConstantFoldingExprBuilder::createUDiv(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value().udiv(ce_r->value()), l->bits());
	}
	else
	return ExprBuilder::createUDiv(l, r);
}

ExprRef ConstantFoldingExprBuilder::createURem(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value().urem(ce_r->value()), l->bits());
	}
	else
	return ExprBuilder::createURem(l, r);
}

ExprRef ConstantFoldingExprBuilder::createUge(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().uge(ce_r->value()));
	}
	else
	return ExprBuilder::createUge(l, r);
}

ExprRef ConstantFoldingExprBuilder::createUgt(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().ugt(ce_r->value()));
	}
	else
	return ExprBuilder::createUgt(l, r);
}

ExprRef ConstantFoldingExprBuilder::createUle(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().ule(ce_r->value()));
	}
	else
	return ExprBuilder::createUle(l, r);
}

ExprRef ConstantFoldingExprBuilder::createUlt(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createBool(ce_l->value().ult(ce_r->value()));
	}
	else
	return ExprBuilder::createUlt(l, r);
}

ExprRef ConstantFoldingExprBuilder::createXor(ExprRef l, ExprRef r) {
	ConstantExprRef ce_l = castAs<ConstantExpr>(l);
	ConstantExprRef ce_r = castAs<ConstantExpr>(r);

	if (ce_l != NULL && ce_r != NULL) {
		RGDPROXY_ASSERT(l->bits() == r->bits());
		return createConstant(ce_l->value() ^ ce_r->value(), l->bits());
	}
	else
	return ExprBuilder::createXor(l, r);
}

/*
ExprRef PruneExprBuilder::createZExt(ExprRef e, uint32_t bits) {
	ExprRef ref = ExprBuilder::createZExt(e, bits);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createSExt(ExprRef e, uint32_t bits) {
	ExprRef ref = ExprBuilder::createSExt(e, bits);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createAdd(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createAdd(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createSub(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createSub(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createMul(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createMul(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createUDiv(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createUDiv(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createSDiv(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createSDiv(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createURem(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createURem(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createSRem(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createSRem(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createNeg(ExprRef e) {
	ExprRef ref = ExprBuilder::createNeg(e);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createNot(ExprRef e) {
	ExprRef ref = ExprBuilder::createNot(e);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createAnd(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createAnd(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createOr(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createOr(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createXor(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createXor(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createShl(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createShl(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createLShr(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createLShr(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createAShr(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createAShr(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createLOr(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createLOr(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createLAnd(ExprRef l, ExprRef r) {
	ExprRef ref = ExprBuilder::createLAnd(l, r);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createLNot(ExprRef e) {
	ExprRef ref = ExprBuilder::createLNot(e);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}

ExprRef PruneExprBuilder::createIte(ExprRef expr_cond, ExprRef expr_true, ExprRef expr_false) {
	ExprRef ref = ExprBuilder::createIte(expr_cond, expr_true, expr_false);
	g_call_stack_manager.updateBitmap();
	if (g_call_stack_manager.isInteresting())
		return ref;
	else
		return ref->evaluate();
}
*/
}
