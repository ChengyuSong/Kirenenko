#include <iostream>
#include <memory>
#include <string>
#include <grpcpp/grpcpp.h>
#include "helloworld.grpc.pb.h"
#include <fstream>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <google/protobuf/io/zero_copy_stream_impl.h>
#include "dfsan.h"

using grpc::Channel;
using grpc::ClientContext;
using grpc::Status;
using rgd::JitRequest;
using rgd::JitCmd;
using rgd::JitCmdv2;
using rgd::JitReply;
using rgd::RGD;
using namespace google::protobuf::io;
using namespace __dfsan;

#define RECORD_EXPR 0
//TODO: Ite, LNot/LAnd/LOr
//TODO: test Extract

extern dfsan_label_info *__dfsan_label_info; //Ju: Make this global

void initRGDProxy() {}

class RGDClient {
	public:
		RGDClient(std::shared_ptr<Channel> channel)
			: stub_(RGD::NewStub(channel)) {}

		void sendCmdv2(JitCmdv2* cmd) {
			// Data we are sending to the server.
			//JitRequest request;
			//JitRequest *request1 = new JitRequest();
			//request.set_name(user);
			JitReply reply;

			// Container for the data we expect from the server.

			// Context for the client. It could be used to convey extra information to
			// the server and/or tweak certain RPC behaviors.
			ClientContext context;

			// The actual RPC.
			Status status = stub_->sendCmdv2(&context, *cmd, &reply);

		}



	private:
		std::unique_ptr<RGD::Stub> stub_;
};

void codegen(dfsan_label label, JitRequest* ret);

//reference: https://stackoverflow.com/questions/2340730/are-there-c-equivalents-for-the-protocol-buffers-delimited-i-o-functions-in-ja
bool writeDelimitedTo(
		const google::protobuf::MessageLite& message,
		google::protobuf::io::ZeroCopyOutputStream* rawOutput) {
	// We create a new coded stream for each message.  Don't worry, this is fast.
	google::protobuf::io::CodedOutputStream output(rawOutput);

	// Write the size.
	const int size = message.ByteSize();
	output.WriteVarint32(size);

	uint8_t* buffer = output.GetDirectBufferForNBytesAndAdvance(size);
	if (buffer != NULL) {
		// Optimization:  The message fits in one buffer, so use the faster
		// direct-to-array serialization path.
		message.SerializeWithCachedSizesToArray(buffer);
	} else {
		// Slightly-slower path when the message is multiple buffers.
		message.SerializeWithCachedSizes(&output);
		if (output.HadError()) return false;
	}

	return true;
}

bool readDelimitedFrom(
		google::protobuf::io::ZeroCopyInputStream* rawInput,
		google::protobuf::MessageLite* message) {
	// We create a new coded stream for each message.  Don't worry, this is fast,
	// and it makes sure the 64MB total size limit is imposed per-message rather
	// than on the whole stream.  (See the CodedInputStream interface for more
	// info on this limit.)
	google::protobuf::io::CodedInputStream input(rawInput);

	// Read the size.
	uint32_t size;
	if (!input.ReadVarint32(&size)) return false;

	// Tell the stream not to read beyond that size.
	google::protobuf::io::CodedInputStream::Limit limit =
		input.PushLimit(size);

	// Parse the message.
	if (!message->MergeFromCodedStream(&input)) return false;
	if (!input.ConsumedEntireMessage()) return false;

	// Release the limit.
	input.PopLimit(limit);

	return true;
}


void gdReset() {
	std::cout << "reset gd" << std::endl;
}

void gdSolve() {
	std::cout << "gd solve" << std::endl;
}

void do_print(const dfsan_label_info* info) {
	//dfsan_label_info* info = &__dfsan_label_info[label];
	if (info == nullptr) return;
	std::string name;
	switch (info->op) {
		case 0: name="read";break;
		case Load: name="load";break;
		case ZExt: name="zext";break;
		case SExt: name="sext";break;
		case Trunc: name="trunc";break;
		case Not: name="not";break;
		case fmemcmp: name="fmemcmp";break;
		default: break;
	}

	switch (info->op & 0xff) {
		case And: {if (info->size) name="and"; else name="land";break;}
		case Or: {if (info->size) name="or"; else name="lor";break;}
		case Xor: name="xor";break;
		case Shl: name="shl";break;
		case LShr: name="lshr";break;
		case Add: name="add";break;
		case Sub: name="sub";break;
		case Mul: name="mul";break;
		case UDiv:name="udiv";break;
		case SDiv:name="sdiv";break;
		case URem:name="urem";break;
		case SRem:name="srem";break;
		case ICmp: {
			switch (info->op >> 8) {
				case bveq:  name="bveq";break;
				case bvneq: name="bvneq";break;
				case bvugt: name="bvugt";break;
				case bvuge: name="bvuge";break;
				case bvult: name="bvult";break;
				case bvule: name="bvule";break;
				case bvsgt: name="bvsgt";break;
				case bvsge: name="bvsge";break;
				case bvslt: name="bvslt";break;
				case bvsle: name="bvsle";break;
			}
			break;
		}
		case Concat:name="concat";break;
		default: break;
	}

	std::cerr << name << "(size=" << (int)info->size << ", ";
	/*
		 std::cerr << "width=" << req->bits() << ",";
		 if (req->kind() == 1) {
		 std::cerr << req->value();
		 }
		 if (req->kind() == 2) {
		 std::cerr << req->index();
		 }
	 */
	if (info->op == 0) {
		std::cerr << info->op1;
	} else if (info->op == Load) {
		std::cerr << __dfsan_label_info[info->l1].op1; //offset
		std::cerr << ", ";
		std::cerr << info->l2;   //length
	} else {
		if (info->l1 >= CONST_OFFSET) {
			do_print(&__dfsan_label_info[info->l1]);
		} else {
			std::cerr << (uint64_t)info->op1;
		}
		std::cerr << ", ";
		if (info->l2 >= CONST_OFFSET) {
			do_print(&__dfsan_label_info[info->l2]);
		} else {
			std::cerr << (uint64_t)info->op2;
		}
	}
	std::cerr << ")";
}

void printExpression(const dfsan_label_info* label) {
	do_print(label);
	std::cerr<<std::endl;
}

void sendCmd(int command) {
	RGDClient greeter(grpc::CreateChannel(
				"localhost:50051", grpc::InsecureChannelCredentials()));
	JitCmdv2 cmd; 
	cmd.set_cmd(command);
#if RECORD_EXPR
	mode_t mode =  S_IRUSR | S_IWUSR;
	int fd = open("hello.data", O_CREAT | O_WRONLY | O_APPEND, mode);
	ZeroCopyOutputStream* rawOutput = new google::protobuf::io::FileOutputStream(fd);
	bool suc = writeDelimitedTo(cmd,rawOutput);
	delete rawOutput;
	sync();
	close(fd);
#endif
	greeter.sendCmdv2(&cmd);
}

void solveSingle(dfsan_label label, uint8_t result) {
	static int count = 0;
	std::cout  << "sending label result is " << (int)result << " count is " << ++count << std::endl;
	if (label < CONST_OFFSET || label == -1) {
		std::cout << "WARNING: invalid label: " << label << std::endl;
		return;
	}
	RGDClient greeter(grpc::CreateChannel(
				"localhost:50051", grpc::InsecureChannelCredentials()));

	dfsan_label_info *info = &__dfsan_label_info[label];
	printExpression(info);
	printf("%u %u %u %u %u %llu %llu\n", label, info->l1, info->l2,
	info->op, info->size, info->op1, info->op2);


	//JitRequest req;
	JitCmdv2 cmd;
	cmd.set_cmd(2);
	JitRequest* req = cmd.add_expr();
	//req.set_test_value(value);
	codegen(label,req);
#if RECORD_EXPR
	mode_t mode =  S_IRUSR | S_IWUSR;
	int fd = open("hello.data", O_CREAT | O_WRONLY | O_APPEND, mode);
	ZeroCopyOutputStream* rawOutput = new google::protobuf::io::FileOutputStream(fd);
	bool suc = writeDelimitedTo(cmd,rawOutput);
	delete rawOutput;
	sync();
	close(fd);
#endif
	//std::string user("world");
	//cmd.set_expr(req);
	//std::string reply = greeter.sendCmdv2(&cmd);
	greeter.sendCmdv2(&cmd);
	//std::cout << "RGD received: " << reply << std::endl;
}


void codegen(dfsan_label label, JitRequest* ret) {
	dfsan_label_info* info = &__dfsan_label_info[label];
	if (info == nullptr) return;
	uint8_t size = info->size * 8;
	if (!size) size = 1;
	switch (info->op) {
		case 0: {
			ret->set_kind(2);
			ret->set_name("read");
			ret->set_bits(info->size * 8);
			ret->set_index(info->op1);
			return;
		}
		case Load: {
			ret->set_kind(36);
			ret->set_name("load");
			ret->set_bits(info->size * 8);
			ret->set_index(__dfsan_label_info[info->l1].op1);
			return;
		}
		case ZExt: {
			ret->set_kind(5);
			ret->set_name("zext");
			ret->set_bits(info->size * 8);
			JitRequest* child0 = ret->add_children();	
			codegen(info->l2,child0);
			return;
		}
		case SExt: {
			ret->set_kind(6);
			ret->set_name("sext");
			ret->set_bits(info->size * 8);
			JitRequest* child0 = ret->add_children();
			codegen(info->l2,child0);
			return;
		}
		case Trunc: {
			ret->set_kind(4);	
			ret->set_name("extract");
			ret->set_bits(info->size * 8);
			ret->set_index(info->l1 * 8);
			JitRequest* child0 = ret->add_children();
			codegen(info->l2,child0);
		}
		case Not: {
			if (size != 1) {
				ret->set_kind(15);
				ret->set_name("not");
				ret->set_bits(info->size * 8);
				JitRequest* child0 = ret->add_children();
				codegen(info->l1,child0);
			} else {
				ret->set_kind(34);
				ret->set_name("lnot");
				ret->set_bits(info->size * 8);
				JitRequest* child0 = ret->add_children();
				codegen(info->l1,child0);
			}
			return;
		}
		case Neg: {
			ret->set_kind(14);
			ret->set_name("neg");
			ret->set_bits(info->size * 8);
			JitRequest* child0 = ret->add_children();
			codegen(info->l1,child0);
			return;
		}
	}

	JitRequest* child0 = ret->add_children();
	JitRequest* child1 = ret->add_children();
	if (info->l1 >= CONST_OFFSET) {
		codegen(info->l1,child0);
	} else {
		child0->set_kind(1);
		child0->set_name("constant");
		child0->set_bits(size);
		child0->set_value(std::to_string(info->op1));
	}
	if (info->l2 >= CONST_OFFSET) {
		codegen(info->l2,child1);
	} else {
		child1->set_kind(1);
		child1->set_name("constant");
		child1->set_bits(size);
		child1->set_value(std::to_string(info->op2));
	}

	switch ((info->op & 0xff)) {
		case And: {
			if (size != 1) {
				ret->set_kind(16);
				ret->set_name("and");
				ret->set_bits(size);
			} else {
				ret->set_kind(33);
				ret->set_name("land");
				ret->set_bits(size);
			}
			return;
		}
		case Or: {
			if (size != 1) {
				ret->set_kind(17);
				ret->set_name("or");
				ret->set_bits(size);
			} else {
				ret->set_kind(32);
				ret->set_name("lor");
				ret->set_bits(size);
			}
			return;
		}
		case Xor: {
			ret->set_kind(18); ret->set_name("xor");
			ret->set_bits(size);
			return;
		}
		case Shl: {
			ret->set_kind(19);
			ret->set_name("shl");
			ret->set_bits(size);
			return;
		}
		case LShr: {
			ret->set_kind(20);
			ret->set_name("lshr");
			ret->set_bits(size);
			return;
		}
		case AShr: {
			ret->set_kind(21);
			ret->set_name("Ashr");
			ret->set_bits(size);
			return;
		}
		case Add: {
			ret->set_kind(7);
			ret->set_name("add");
			ret->set_bits(size);
			return;
		}
		case Sub: {
			ret->set_kind(8);
			ret->set_name("sub");
			ret->set_bits(size);
			return;
		}
		case Mul: {
			ret->set_kind(9);
			ret->set_name("mul");
			ret->set_bits(size);
			return;
		}
		case UDiv: {
			ret->set_kind(10);
			ret->set_name("udiv");
			ret->set_bits(size);
			return;
		}
		case SDiv: {
			ret->set_kind(11);
			ret->set_name("sdiv");
			ret->set_bits(size);
			return;
		}
		case URem: {
			ret->set_kind(12);
			ret->set_name("urem");
			ret->set_bits(size);
			return;
		}
		case SRem: {
			ret->set_kind(13);
			ret->set_name("srem");
			ret->set_bits(size);
			return;
		}
		case Concat: {
			ret->set_kind(3);
			ret->set_name("concat");
			ret->set_bits(size);
			return;
		}
	}

	switch (info->op >>8) {
		case bveq: {
			ret->set_kind(22);
			ret->set_name("equal");
			ret->set_bits(size);
			return;
		} 
		case bvneq: {
			ret->set_kind(23);
			ret->set_name("distinct");
			ret->set_bits(size);
			return;
		}
		case bvult: {
			ret->set_kind(24);
			ret->set_name("ult");
			ret->set_bits(size);
			return;
		}
		case bvule: {
			ret->set_kind(25);
			ret->set_name("ule");
			ret->set_bits(size);
			return;
		}
		case bvugt: {
			ret->set_kind(26);
			ret->set_name("ugt");
			ret->set_bits(size);
			return;
		}
		case bvuge: {
			ret->set_kind(27);
			ret->set_name("uge");
			ret->set_bits(size);
			return;
		}
		case bvslt: {
			ret->set_kind(28);
			ret->set_name("slt");
			ret->set_bits(size);
			return;
		}
		case bvsle: {
			ret->set_kind(29);
			ret->set_name("sle");
			ret->set_bits(size);
			return;
		}
		case bvsgt: {
			ret->set_kind(30);
			ret->set_name("sgt");
			ret->set_bits(size);
			return;
		}
		case bvsge: {
			ret->set_kind(31);
			ret->set_name("sge");
			ret->set_bits(size);
			return;
		}

	}
}
