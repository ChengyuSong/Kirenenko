all:
	protoc -I . --cpp_out=. rgd.proto 
	protoc -I . --grpc_out=. --plugin=protoc-gen-grpc=/usr/local/bin/grpc_cpp_plugin rgd.proto
	g++ -I../llvm_mode/dfsan_rt -I../llvm_mode/dfsan_rt/dfsan -I../llvm_mode/include logging.cpp rgd_proxy.cpp xxhash.cpp expr_cache.cpp expr_builder__gen.cpp expr__gen.cpp dependency.cpp  rgd.grpc.pb.cc rgd.pb.cc -L/usr/lib/llvm-3.8/lib -fPIC -shared -std=c++11 -lLLVM -lgrpc++ -lgrpc -lprotobuf -o librgdproxy.so
	sudo cp librgdproxy.so /usr/lib
clean:
	rm -rf *.pb.cc
	rm -rf *.pb.h
	rm -rf librgdproxy.so
