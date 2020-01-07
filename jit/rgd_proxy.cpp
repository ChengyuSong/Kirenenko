#include "expr.h"
#include "llvm/ADT/StringRef.h"
#include <grpcpp/grpcpp.h>
#include "rgd.grpc.pb.h"
// Proprocess constraints before sending to RGD,
// including De-duplication, Dep forest, maybe more?
#include "rgd_proxy.h"

extern dfsan_label_info *__dfsan_label_info; //Ju: Make this global
namespace RGDPROXY {

RGDProxy *g_rgdproxy;

void RGDProxy::addConstraints(ExprRef e) {
  // If e is true, then just skip
  if (e->kind() == Bool) {
    RGDPROXY_ASSERT(castAs<BoolExpr>(e)->value());
    return;
  }
  if (e->isConcrete())
    return;
  dep_forest_.addNode(e);
}

void RGDProxy::syncConstraints(ExprRef e, std::vector<ExprRef> *list) {
	std::cout << "syncConstraints" << std::endl;
  std::set<std::shared_ptr<DependencyTree<Expr>>> forest;
  DependencySet* deps = e->getDependencies();

  for (const size_t& index : *deps) {
    forest.insert(dep_forest_.find(index));
  }

  for (std::shared_ptr<DependencyTree<Expr>> tree : forest) {
    std::vector<std::shared_ptr<Expr>> nodes = tree->getNodes();
    for (std::shared_ptr<Expr> node : nodes) { 
			std::cout << node->toString() << std::endl;
			list->push_back(node);
			//sendExpr(node);
/*
      if (isRelational(node.get()))
        addToSolver(node, true);
      else {
        // Process range-based constraints
        bool valid = false;
        for (INT32 i = 0; i < 2; i++) {
          ExprRef expr_range = getRangeConstraint(node, i);
          if (expr_range != NULL) {
            addToSolver(expr_range, true);
            valid = true;
          }
        }

        // One of range expressions should be non-NULL
        if (!valid)
          LOG_INFO(std::string(__func__) + ": Incorrect constraints are inserted\n");
      }
*/
    }
  }
	std::cout << "end of syncConstraints" << std::endl;

 // checkFeasible();
}



ExprRef RGDProxy::do_build(dfsan_label label) {
	dfsan_label_info* info = &__dfsan_label_info[label];
	if (info == nullptr) return nullptr;
	uint8_t size = info->size * 8;
	if (!size) size = 1;
	switch (info->op) {
		case 0: {
			ExprRef ret = expr_builder->createRead(info->op1);
			ret->setTTFuzzLabelAndHash(label,info->hash);
			return ret;
		}
		case __dfsan::Load: {
			uint32_t index = __dfsan_label_info[info->l1].op1;
			ExprRef out = expr_builder->createRead(index);
			for(uint32_t i=1; i<info->l2; i++)
			{
					out = expr_builder->createConcat(expr_builder->createRead(index+i),
																					 out);
			}
			out->setTTFuzzLabelAndHash(label,info->hash);
			return out;
		}
		case __dfsan::ZExt: {
			ExprRef ret = expr_builder->createZExt(do_build(info->l2),size);
			ret->setTTFuzzLabelAndHash(label,info->hash);
			return ret;
		}
		case __dfsan::SExt: {
			ExprRef ret = expr_builder->createSExt(do_build(info->l2),size);
			ret->setTTFuzzLabelAndHash(label,info->hash);
			return ret;
		}
		case __dfsan::Trunc: {
			ExprRef ret = expr_builder->createExtract(do_build(info->l2),info->l1*8,size);
			ret->setTTFuzzLabelAndHash(label,info->hash);
			return ret;
		}
		case __dfsan::Not: {
			if (size!=1) {
				ExprRef ret = expr_builder->createNot(do_build(info->l1));
				ret->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
			}
			else {
				ExprRef ret = expr_builder->createLNot(do_build(info->l1));
				ret->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
			}
		}
		case __dfsan::Neg: {
			ExprRef ret = expr_builder->createNeg(do_build(info->l1));
			ret->setTTFuzzLabelAndHash(label,info->hash);
			return ret;
		}
	}

	ExprRef child0 = nullptr;
	ExprRef child1 = nullptr;

	if (info->l1 >= CONST_OFFSET) {
		child0 = do_build(info->l1);
	} else {
		child0 = expr_builder->createConstant(info->op1,size);
		child0->setTTFuzzLabelAndHash(label,info->hash);
	}

	if (info->l2 >= CONST_OFFSET) {
		child1 = do_build(info->l2);
	} else {
		child1 = expr_builder->createConstant(info->op2,size);
		child1->setTTFuzzLabelAndHash(label,info->hash);
	}

	switch ((info->op & 0xff)) {
		case __dfsan::And: {
			if (size != 1) {
				ExprRef ret = expr_builder->createAnd(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
			} else {
				ExprRef ret = expr_builder->createLAnd(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
			}
		}
		case __dfsan::Or: {
			if (size != 1) {
				ExprRef ret = expr_builder->createOr(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
			} else {
				ExprRef ret = expr_builder->createLOr(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
			}
		}	
		case __dfsan::Xor: {
				ExprRef ret = expr_builder->createXor(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::Shl: {
				ExprRef ret = expr_builder->createShl(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::LShr: {
				ExprRef ret = expr_builder->createLShr(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::AShr: {
				ExprRef ret = expr_builder->createAShr(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::Add: {
				ExprRef ret = expr_builder->createAdd(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::Sub: {
				ExprRef ret = expr_builder->createSub(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::Mul: {
				ExprRef ret = expr_builder->createMul(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::UDiv: {
				ExprRef ret = expr_builder->createUDiv(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::SDiv: {
				ExprRef ret = expr_builder->createSDiv(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::URem: {
				ExprRef ret = expr_builder->createURem(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::SRem: {
				ExprRef ret = expr_builder->createSRem(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::Concat: {
				ExprRef ret = expr_builder->createConcat(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
	}

	switch (info->op>>8) {
		case __dfsan::bveq: {
				ExprRef ret = expr_builder->createEqual(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvneq: {
				ExprRef ret = expr_builder->createDistinct(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvult: {
				ExprRef ret = expr_builder->createUlt(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvule: {
				ExprRef ret = expr_builder->createUle(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvugt: {
				ExprRef ret = expr_builder->createUgt(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvuge: {
				ExprRef ret = expr_builder->createUge(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvslt: {
				ExprRef ret = expr_builder->createSlt(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvsle: {
				ExprRef ret = expr_builder->createSle(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvsgt: {
				ExprRef ret = expr_builder->createSgt(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
		case __dfsan::bvsge: {
				ExprRef ret = expr_builder->createSge(child0,child1);
				ret ->setTTFuzzLabelAndHash(label,info->hash);
				return ret;
		}		
	}

  RGDPROXY_UNREACHABLE();
}

ExprRef RGDProxy::negateExpr(ExprRef expr) {
	return expr_builder->createLNot(expr);
}

ExprRef RGDProxy::buildExpr(dfsan_label label, uint8_t result, bool taken) {
	bool r = (bool)result;
	std::cout << " in build expr result is " << (int)result << " taken is " << taken << std::endl;
	printLabel(label);
	ExprRef ret =  do_build(label);
	if (r != taken)   //if r=0, taken is true or r = 1 taken is false
		ret = negateExpr(ret);
	std::cout << ret->toString() << std::endl;
	return ret;
}

void RGDProxy::do_print(dfsan_label label) {
	dfsan_label_info* info  = &__dfsan_label_info[label];
	if (info == nullptr) return;
	std::string name;
	switch (info->op) {
		case 0: name="read";break;
		case __dfsan::Load: name="load";break;
		case __dfsan::ZExt: name="zext";break;
		case __dfsan::SExt: name="sext";break;
		case __dfsan::Trunc: name="trunc";break;
		case __dfsan::Not: name="not";break;
		case __dfsan::fmemcmp: name="fmemcmp";break;
		default: break;
	}

	switch (info->op & 0xff) {
		
		case __dfsan::And: {if (info->size) name="and"; else name="land";break;}
		case __dfsan::Or: {if (info->size) name="or"; else name="lor";break;}
		case __dfsan::Xor: name="xor";break;
		case __dfsan::Shl: name="shl";break;
		case __dfsan::LShr: name="lshr";break;
		case __dfsan::Add: name="add";break;
		case __dfsan::Sub: name="sub";break;
		case __dfsan::Mul: name="mul";break;
		case __dfsan::UDiv:name="udiv";break;
		case __dfsan::SDiv:name="sdiv";break;
		case __dfsan::URem:name="urem";break;
		case __dfsan::SRem:name="srem";break;
		case __dfsan::ICmp: {
			switch (info->op >> 8) {
				case __dfsan::bveq:  name="bveq";break;
				case __dfsan::bvneq: name="bvneq";break;
				case __dfsan::bvugt: name="bvugt";break;
				case __dfsan::bvuge: name="bvuge";break;
				case __dfsan::bvult: name="bvult";break;
				case __dfsan::bvule: name="bvule";break;
				case __dfsan::bvsgt: name="bvsgt";break;
				case __dfsan::bvsge: name="bvsge";break;
				case __dfsan::bvslt: name="bvslt";break;
				case __dfsan::bvsle: name="bvsle";break;
			}
			break;
		}
		case __dfsan::Concat:name="concat";break;
		default: break;
	}
	std::cerr << name << "(size=" << (int)info->size << ", ";

	if (info->op == 0) {
		std::cerr << info->op1;
	} else if (info->op == __dfsan::Load) {
		std::cerr << __dfsan_label_info[info->l1].op1; //offset
		std::cerr << ", ";
		std::cerr << info->l2;   //length
	} else {
		if (info->l1 >= CONST_OFFSET) {
			do_print(info->l1);
		} else {
			std::cerr << (uint64_t)info->op1;
		}
		std::cerr << ", ";
		if (info->l2 >= CONST_OFFSET) {
			do_print(info->l2);
		} else {
			std::cerr << (uint64_t)info->op2;
		}
	}
	std::cerr << ")";
}

void RGDProxy::printLabel(dfsan_label label) {
	do_print(label);
	std::cerr<<std::endl;
}


void RGDProxy::solveConstraints(ExprRef expr) {
}

void RGDProxy::sendReset() {
	RGDClient rgd(grpc::CreateChannel(
        "localhost:50051", grpc::InsecureChannelCredentials()));
	JitCmdv2 cmd; 
	cmd.set_cmd(0);
	rgd.sendCmdv2(&cmd);
}

void RGDProxy::sendSolve() {
	RGDClient rgd(grpc::CreateChannel(
        "localhost:50051", grpc::InsecureChannelCredentials()));
	JitCmdv2 cmd; 
	cmd.set_cmd(1);
	rgd.sendCmdv2(&cmd);
}

void RGDProxy::sendExpr(ExprRef expr) {
	RGDClient rgd(grpc::CreateChannel(
        "localhost:50051", grpc::InsecureChannelCredentials()));
	JitCmdv2 cmd;
	cmd.set_cmd(2);
	JitRequest* req = cmd.add_expr();
	codegen(expr,req);
	rgd.sendCmdv2(&cmd);
}

void RGDProxy::sendExpr(std::vector<ExprRef> &list) {
	RGDClient rgd(grpc::CreateChannel(
        "localhost:50051", grpc::InsecureChannelCredentials()));
	JitCmdv2 cmd;
	cmd.set_cmd(2);
	for (ExprRef expr : list) {
		JitRequest* req = cmd.add_expr();
		codegen(expr,req);
	}
	rgd.sendCmdv2(&cmd);
}



void RGDProxy::codegen(ExprRef expression, JitRequest* ret) {
	switch (expression->kind()) {
    case Bool:
     //getTrue is actually 1 bit integer 1
     ret->set_kind(0);
     ret->set_name("bool");
     ret->set_bits(expression->bits());
     if (BoolExprRef be = castAs<BoolExpr>(expression)) {
       if(be->value())
         ret -> set_boolvalue(1);
       else
         ret -> set_boolvalue(0);
     }
     break;
    case Constant:
     //std::cerr << "Constant expr codegen" << std::endl;
     ret->set_kind(1);
     ret->set_name("constant");
     ret->set_bits(expression->bits());
     if (ConstantExprRef ce = castAs<ConstantExpr>(expression)) {
       ret->set_value(ce->value().toString(10,true));
     }
     break;
		case Read:
     //std::cerr << "Read expr codegen" << std::endl;
     ret->set_kind(2);
     ret->set_bits(expression->bits());
     ret->set_name("read");
     if (ReadExprRef re = castAs<ReadExpr>(expression)) {
        ret->set_index(re->index());
     }
     break;
		case Concat: {
     ret -> set_kind(3);
     ret->set_name("concat");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     break;
    }
		case Extract: {
     ret->set_kind(4);
     ret->set_name("extract");
     ret->set_bits(expression->bits());
     JitRequest* child = ret->add_children();
     codegen(expression->getChild(0),child);
     if (ExtractExprRef ee = castAs<ExtractExpr>(expression)) {
       ret->set_index(ee->index());
     }
     break;
    }
		case ZExt: {
    // std::cerr << "ZExt the bits is " << expression->bits() << std::endl;
			ret -> set_kind(5);
			ret->set_name("zext");
			ret->set_bits(expression->bits());
			JitRequest* child = ret->add_children();
			codegen(expression->getChild(0),child);
			break;
		}
		case SExt: {
     //std::cerr << "SExt the bits is " << expression->bits() << std::endl;
     ret->set_kind(6);
     ret->set_name("sext");
     ret->set_bits(expression->bits());
     JitRequest* child = ret->add_children();
     codegen(expression->getChild(0),child);
     //ret = Builder->CreateSExt(codegen(expression->getChild(0),mc),llvm::Type::getIntNTy(*mc->TheContext,expression->bits()));
     //std::cerr << "SExt expr code gen done" << std::endl;
     break;
    }
    case Add: {
     ret->set_kind(7);
     ret->set_name("add");
     ret->set_bits(expression->bits());
     //std::cerr <<"Add expr codegen" << std::endl;
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //std::cerr <<"Add expr codegen finished" << std::endl;
     //ret = Builder->CreateAdd(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Add");
     break;
    }
		case Sub: {
     ret->set_kind(8);
     ret->set_name("sub");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateSub(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Sub");
     break;
    }
    case Mul: {
     ret->set_kind(9);
     ret->set_name("mul");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateMul(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Mul");
     break;
    }
		case UDiv: {
     ret->set_kind(10);
     ret->set_name("udiv");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateUDiv(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "UDiv");
     break;
    }
    case SDiv: {
     ret->set_kind(11);
     ret->set_name("sdiv");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret =Builder->CreateSDiv(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "SDiv");
     break;
    }
		case URem: {
     ret->set_kind(12);
     ret->set_name("urem");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateURem(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "URem");
     break;
    }
    case SRem: {
     ret->set_kind(13);
     ret->set_name("srem");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateSRem(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "SRem");
     break;
    }
		case Neg: {
     ret->set_kind(14);
     ret->set_name("neg");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     codegen(expression->getChild(0),child0);
     //ret = Builder->CreateNeg(codegen(expression->getChild(0),mc), "Neg");
     break;
    }
    case Not: {
     ret->set_kind(15);
     ret->set_name("not");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     codegen(expression->getChild(0),child0);
     //ret = Builder->CreateNot(codegen(expression->getChild(0),mc), "Not");
     break;
    }
    case And: {
     ret->set_kind(16);
     ret->set_name("and");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateAnd(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "And");
     break;
    }
		case Or: {
     ret->set_kind(17);
     ret->set_name("or");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateOr(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Or");
     break;
    }
    case Xor: {
     ret->set_kind(18);
     ret->set_name("xor");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateXor(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Xor");
     break;
    }
		case Shl: {
     ret->set_kind(19);
     ret->set_name("shl");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret =Builder->CreateShl(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Shl");
     break;
    }
    case LShr: {
     ret->set_kind(20);
     ret->set_name("lshr");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateLShr(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "LShr");
     break;
    }
    case AShr: {
     ret->set_kind(21);
     ret->set_name("ashr");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateAShr(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "AShr");
     break;
    }
		case Equal: {
     //std::cerr << "Equal expr codegen and kind is" << expression->kind() <<  std::endl;
     ret->set_kind(22);
     ret->set_name("equal");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpEQ(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Equal");
     break;
    }
    case Distinct: {
     ret->set_kind(23);
     ret->set_name("distinct");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpNE(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Distinct");
     break;
    }
		case Ult: {
     ret->set_kind(24);
     ret->set_name("ult");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpULT(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Ult");
     break;
    }
    case Ule: {
     ret->set_kind(25);
     ret->set_name("ule");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpULE(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Ule");
     break;
    }
		case Ugt: {
     ret->set_kind(26);
     ret->set_name("ugt");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpUGT(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Ugt");
     break;
    }
    case Uge: {
     ret->set_kind(27);
     ret->set_name("uge");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpUGE(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Uge");
     break;
    }
		case Slt: {
     ret->set_kind(28);
     ret->set_name("slt");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpSLT(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Slt");
     break;
    }
    case Sle: {
     ret->set_kind(29);
     ret->set_name("sle");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpSLE(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Sle");
     break;
    }
		case Sgt: {
     ret->set_kind(30);
     ret->set_name("sgt");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpSGT(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Sgt");
     break;
    }
    case Sge: {
     ret->set_kind(31);
     ret->set_name("sge");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateICmpSGE(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "Sge");
     break;
    }
		case LOr: {
     ret->set_kind(32);
     ret->set_name("lor");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateOr(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "LOr");
     break;
    }
    case LAnd: {
     ret->set_kind(33);
     ret->set_name("land");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     //ret = Builder->CreateAnd(codegen(expression->getChild(0),mc),  codegen(expression->getChild(1),mc), "LAnd");
     break;
    }
    case LNot: {
     ret->set_kind(34);
     ret->set_name("lnot");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     codegen(expression->getChild(0),child0);
     //ret = Builder->CreateNot(codegen(expression->getChild(0),mc), "LNot");
     break;
    }
		case Ite: {
     ret->set_kind(35);
     ret->set_name("ite");
     ret->set_bits(expression->bits());
     JitRequest* child0 = ret->add_children();
     JitRequest* child1 = ret->add_children();
     JitRequest* child2 = ret->add_children();
     codegen(expression->getChild(0),child0);
     codegen(expression->getChild(1),child1);
     codegen(expression->getChild(2),child2);
			break;
		}
		default:
			break;
		}
		ret->set_label(expression->TTFuzzLabel());
		ret->set_hash(expression->TTFuzzHash());
		return;
}	

bool RGDProxy::rejectBranch(dfsan_label label) {
	if (label<1) return false;
	dfsan_label_info* info  = &__dfsan_label_info[label];
	if (info==NULL || info->op == 0)  //if invalid or read
		return false; 
	if (info->op == __dfsan::fmemcmp)
		return true;
	if (rejectBranch(info->l1))
		return true;
	if (rejectBranch(info->l2))
		return true;
	return false;
}

}

void initRGDProxy() {
	RGDPROXY::g_rgdproxy = new RGDPROXY::RGDProxy();
}

//flip single branch and also add the intended path 
//to the dep forest
void solveSingle(dfsan_label label, uint8_t result) {
	if (RGDPROXY::g_rgdproxy->rejectBranch(label)) return;
	RGDPROXY::ExprRef not_taken = RGDPROXY::g_rgdproxy->buildExpr(label,result,false);
	RGDPROXY::g_rgdproxy->sendReset();
	RGDPROXY::g_rgdproxy->sendExpr(not_taken);
	//RGDPROXY::g_rgdproxy->sendSolve();
	RGDPROXY::ExprRef taken = RGDPROXY::g_rgdproxy->buildExpr(label,result,true);
	//add to dep forest
	RGDPROXY::g_rgdproxy->addConstraints(taken);
}

//solve nested branch and also add the intended branch 
//to the dep forest
void solveNested(dfsan_label label, uint8_t result) {
	if (RGDPROXY::g_rgdproxy->rejectBranch(label)) return;
	RGDPROXY::ExprRef not_taken = RGDPROXY::g_rgdproxy->buildExpr(label,result,false);
	RGDPROXY::g_rgdproxy->sendReset();
	std::vector<RGDPROXY::ExprRef> list;
	RGDPROXY::g_rgdproxy->syncConstraints(not_taken, &list);
	list.push_back(not_taken);
	RGDPROXY::g_rgdproxy->sendExpr(list);
	//RGDPROXY::g_rgdproxy->sendSolve();
	RGDPROXY::ExprRef taken = RGDPROXY::g_rgdproxy->buildExpr(label,result,true);
	RGDPROXY::g_rgdproxy->addConstraints(taken);
}







