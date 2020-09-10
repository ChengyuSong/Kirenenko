FROM ubuntu:18.04

RUN apt-get update
RUN apt-get -y upgrade
RUN apt-get install -y git build-essential sudo

RUN mkdir -p kirenenko
COPY . kirenenko
WORKDIR kirenenko

RUN ./build/build.sh

