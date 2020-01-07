#pragma once
#include "expr.h"
#include "llvm/ADT/StringRef.h"
#include "dfsan.h"
#include "expr_builder.h"
// Proprocess constraints before sending to RGD,
// including De-duplication, Dep forest, maybe more?
using grpc::Channel;
using grpc::ClientContext;
using grpc::Status;
using rgd::JitRequest;
using rgd::JitCmd;
using rgd::JitCmdv2;
using rgd::JitReply;
using rgd::RGD;


namespace RGDPROXY {

class RGDClient {
  public:
    RGDClient(std::shared_ptr<Channel> channel)
      : stub_(RGD::NewStub(channel)) {}

    void sendCmdv2(JitCmdv2* cmd) {
      JitReply reply;

      ClientContext context;

      // The actual RPC.
      Status status = stub_->sendCmdv2(&context, *cmd, &reply);

    }
  private:
    std::unique_ptr<RGD::Stub> stub_;
};


class RGDProxy {
public:
	void addConstraints(ExprRef expr); //add to dep forest
	void solveConstraints(ExprRef expr);
	void syncConstraints(ExprRef expr,std::vector<ExprRef>* list);

	void sendReset();
	void sendExpr(ExprRef expr);
	void sendExpr(std::vector<ExprRef> &list);
	void sendSolve();

	bool rejectBranch(dfsan_label label);
	ExprRef buildExpr(dfsan_label label, uint8_t result, bool taken);

//	RGDProxy():dep_forest_(), greeter(grpc::CreateChannel(
//				"localhost:50051", grpc::InsecureChannelCredentials())) {
		RGDProxy():dep_forest_() {
		expr_builder = SymbolicExprBuilder::create();
	}

	~RGDProxy() {
		delete expr_builder;
	}


private:
	void do_print(dfsan_label label);
	void printLabel(dfsan_label label);
	ExprRef do_build(dfsan_label label);
	void codegen(ExprRef expr, JitRequest* req);
	ExprRef negateExpr(ExprRef expr);

protected:
	DependencyForest<Expr> dep_forest_;	
	ExprBuilder *expr_builder;
//	RGDClient greeter;
};

extern RGDProxy* g_rgdproxy;

}



