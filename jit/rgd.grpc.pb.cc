// Generated by the gRPC C++ plugin.
// If you make any local change, they will be lost.
// source: rgd.proto

#include "rgd.pb.h"
#include "rgd.grpc.pb.h"

#include <functional>
#include <grpcpp/impl/codegen/async_stream.h>
#include <grpcpp/impl/codegen/async_unary_call.h>
#include <grpcpp/impl/codegen/channel_interface.h>
#include <grpcpp/impl/codegen/client_unary_call.h>
#include <grpcpp/impl/codegen/client_callback.h>
#include <grpcpp/impl/codegen/method_handler_impl.h>
#include <grpcpp/impl/codegen/rpc_service_method.h>
#include <grpcpp/impl/codegen/server_callback.h>
#include <grpcpp/impl/codegen/service_type.h>
#include <grpcpp/impl/codegen/sync_stream.h>
namespace rgd {

static const char* RGD_method_names[] = {
  "/rgd.RGD/sendExpression",
  "/rgd.RGD/sendCmd",
  "/rgd.RGD/sendCmdv2",
};

std::unique_ptr< RGD::Stub> RGD::NewStub(const std::shared_ptr< ::grpc::ChannelInterface>& channel, const ::grpc::StubOptions& options) {
  (void)options;
  std::unique_ptr< RGD::Stub> stub(new RGD::Stub(channel));
  return stub;
}

RGD::Stub::Stub(const std::shared_ptr< ::grpc::ChannelInterface>& channel)
  : channel_(channel), rpcmethod_sendExpression_(RGD_method_names[0], ::grpc::internal::RpcMethod::NORMAL_RPC, channel)
  , rpcmethod_sendCmd_(RGD_method_names[1], ::grpc::internal::RpcMethod::NORMAL_RPC, channel)
  , rpcmethod_sendCmdv2_(RGD_method_names[2], ::grpc::internal::RpcMethod::NORMAL_RPC, channel)
  {}

::grpc::Status RGD::Stub::sendExpression(::grpc::ClientContext* context, const ::rgd::JitRequest& request, ::rgd::JitReply* response) {
  return ::grpc::internal::BlockingUnaryCall(channel_.get(), rpcmethod_sendExpression_, context, request, response);
}

void RGD::Stub::experimental_async::sendExpression(::grpc::ClientContext* context, const ::rgd::JitRequest* request, ::rgd::JitReply* response, std::function<void(::grpc::Status)> f) {
  return ::grpc::internal::CallbackUnaryCall(stub_->channel_.get(), stub_->rpcmethod_sendExpression_, context, request, response, std::move(f));
}

void RGD::Stub::experimental_async::sendExpression(::grpc::ClientContext* context, const ::grpc::ByteBuffer* request, ::rgd::JitReply* response, std::function<void(::grpc::Status)> f) {
  return ::grpc::internal::CallbackUnaryCall(stub_->channel_.get(), stub_->rpcmethod_sendExpression_, context, request, response, std::move(f));
}

::grpc::ClientAsyncResponseReader< ::rgd::JitReply>* RGD::Stub::AsyncsendExpressionRaw(::grpc::ClientContext* context, const ::rgd::JitRequest& request, ::grpc::CompletionQueue* cq) {
  return ::grpc::internal::ClientAsyncResponseReaderFactory< ::rgd::JitReply>::Create(channel_.get(), cq, rpcmethod_sendExpression_, context, request, true);
}

::grpc::ClientAsyncResponseReader< ::rgd::JitReply>* RGD::Stub::PrepareAsyncsendExpressionRaw(::grpc::ClientContext* context, const ::rgd::JitRequest& request, ::grpc::CompletionQueue* cq) {
  return ::grpc::internal::ClientAsyncResponseReaderFactory< ::rgd::JitReply>::Create(channel_.get(), cq, rpcmethod_sendExpression_, context, request, false);
}

::grpc::Status RGD::Stub::sendCmd(::grpc::ClientContext* context, const ::rgd::JitCmd& request, ::rgd::JitReply* response) {
  return ::grpc::internal::BlockingUnaryCall(channel_.get(), rpcmethod_sendCmd_, context, request, response);
}

void RGD::Stub::experimental_async::sendCmd(::grpc::ClientContext* context, const ::rgd::JitCmd* request, ::rgd::JitReply* response, std::function<void(::grpc::Status)> f) {
  return ::grpc::internal::CallbackUnaryCall(stub_->channel_.get(), stub_->rpcmethod_sendCmd_, context, request, response, std::move(f));
}

void RGD::Stub::experimental_async::sendCmd(::grpc::ClientContext* context, const ::grpc::ByteBuffer* request, ::rgd::JitReply* response, std::function<void(::grpc::Status)> f) {
  return ::grpc::internal::CallbackUnaryCall(stub_->channel_.get(), stub_->rpcmethod_sendCmd_, context, request, response, std::move(f));
}

::grpc::ClientAsyncResponseReader< ::rgd::JitReply>* RGD::Stub::AsyncsendCmdRaw(::grpc::ClientContext* context, const ::rgd::JitCmd& request, ::grpc::CompletionQueue* cq) {
  return ::grpc::internal::ClientAsyncResponseReaderFactory< ::rgd::JitReply>::Create(channel_.get(), cq, rpcmethod_sendCmd_, context, request, true);
}

::grpc::ClientAsyncResponseReader< ::rgd::JitReply>* RGD::Stub::PrepareAsyncsendCmdRaw(::grpc::ClientContext* context, const ::rgd::JitCmd& request, ::grpc::CompletionQueue* cq) {
  return ::grpc::internal::ClientAsyncResponseReaderFactory< ::rgd::JitReply>::Create(channel_.get(), cq, rpcmethod_sendCmd_, context, request, false);
}

::grpc::Status RGD::Stub::sendCmdv2(::grpc::ClientContext* context, const ::rgd::JitCmdv2& request, ::rgd::JitReply* response) {
  return ::grpc::internal::BlockingUnaryCall(channel_.get(), rpcmethod_sendCmdv2_, context, request, response);
}

void RGD::Stub::experimental_async::sendCmdv2(::grpc::ClientContext* context, const ::rgd::JitCmdv2* request, ::rgd::JitReply* response, std::function<void(::grpc::Status)> f) {
  return ::grpc::internal::CallbackUnaryCall(stub_->channel_.get(), stub_->rpcmethod_sendCmdv2_, context, request, response, std::move(f));
}

void RGD::Stub::experimental_async::sendCmdv2(::grpc::ClientContext* context, const ::grpc::ByteBuffer* request, ::rgd::JitReply* response, std::function<void(::grpc::Status)> f) {
  return ::grpc::internal::CallbackUnaryCall(stub_->channel_.get(), stub_->rpcmethod_sendCmdv2_, context, request, response, std::move(f));
}

::grpc::ClientAsyncResponseReader< ::rgd::JitReply>* RGD::Stub::AsyncsendCmdv2Raw(::grpc::ClientContext* context, const ::rgd::JitCmdv2& request, ::grpc::CompletionQueue* cq) {
  return ::grpc::internal::ClientAsyncResponseReaderFactory< ::rgd::JitReply>::Create(channel_.get(), cq, rpcmethod_sendCmdv2_, context, request, true);
}

::grpc::ClientAsyncResponseReader< ::rgd::JitReply>* RGD::Stub::PrepareAsyncsendCmdv2Raw(::grpc::ClientContext* context, const ::rgd::JitCmdv2& request, ::grpc::CompletionQueue* cq) {
  return ::grpc::internal::ClientAsyncResponseReaderFactory< ::rgd::JitReply>::Create(channel_.get(), cq, rpcmethod_sendCmdv2_, context, request, false);
}

RGD::Service::Service() {
  AddMethod(new ::grpc::internal::RpcServiceMethod(
      RGD_method_names[0],
      ::grpc::internal::RpcMethod::NORMAL_RPC,
      new ::grpc::internal::RpcMethodHandler< RGD::Service, ::rgd::JitRequest, ::rgd::JitReply>(
          std::mem_fn(&RGD::Service::sendExpression), this)));
  AddMethod(new ::grpc::internal::RpcServiceMethod(
      RGD_method_names[1],
      ::grpc::internal::RpcMethod::NORMAL_RPC,
      new ::grpc::internal::RpcMethodHandler< RGD::Service, ::rgd::JitCmd, ::rgd::JitReply>(
          std::mem_fn(&RGD::Service::sendCmd), this)));
  AddMethod(new ::grpc::internal::RpcServiceMethod(
      RGD_method_names[2],
      ::grpc::internal::RpcMethod::NORMAL_RPC,
      new ::grpc::internal::RpcMethodHandler< RGD::Service, ::rgd::JitCmdv2, ::rgd::JitReply>(
          std::mem_fn(&RGD::Service::sendCmdv2), this)));
}

RGD::Service::~Service() {
}

::grpc::Status RGD::Service::sendExpression(::grpc::ServerContext* context, const ::rgd::JitRequest* request, ::rgd::JitReply* response) {
  (void) context;
  (void) request;
  (void) response;
  return ::grpc::Status(::grpc::StatusCode::UNIMPLEMENTED, "");
}

::grpc::Status RGD::Service::sendCmd(::grpc::ServerContext* context, const ::rgd::JitCmd* request, ::rgd::JitReply* response) {
  (void) context;
  (void) request;
  (void) response;
  return ::grpc::Status(::grpc::StatusCode::UNIMPLEMENTED, "");
}

::grpc::Status RGD::Service::sendCmdv2(::grpc::ServerContext* context, const ::rgd::JitCmdv2* request, ::rgd::JitReply* response) {
  (void) context;
  (void) request;
  (void) response;
  return ::grpc::Status(::grpc::StatusCode::UNIMPLEMENTED, "");
}


}  // namespace rgd
