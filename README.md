# TTFuzz

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

**STILL IN DEVELOPMENT**

I'm really bad at naming so we probably will change it.

## Building

### Build Requirements

- Linux-amd64 (Tested on Ubuntu 18.04)
- [LLVM 4.0.0 - 7.1.0](http://llvm.org/docs/index.html) :
  run `sudo apt install clang` or
  `PREFIX=/path-to-install ./build/install_llvm.sh`.

### Environment Variables

If installed from source,
append the following entries in the shell configuration file (`~/.bashrc`, `~/.zshrc`).

```
export PATH=/path-to-clang/bin:$PATH
export LD_LIBRARY_PATH=/path-to-clang/lib:$LD_LIBRARY_PATH
```

### Fuzzer Compilation

The build script will resolve most dependencies and setup the 
runtime environment.

```shell
./build/build.sh
```

### System Configuration

As with AFL, system core dumps must be disabled.

```shell
echo core | sudo tee /proc/sys/kernel/core_pattern
```

## Test
Running test from Angora
```
cd /path-to-angora/tests/mini
../../bin/tsym-clang mini.c -o mini.taint
python -c "print('A'*20)" > i
TAINT_OPTIONS="taint_file=i" ./mini.taint i
./mini.taint id-0-0-0
```

It doesn't support input growth yet so we need to use a large enough
seed input. It also lacks a driver yet, so we need to manually run
the newly generated test case(s).

Currently I've tested with `mini`, `bitflip`, `shift`, and `switch`.
