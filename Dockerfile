FROM satcomp-common-base-image as builder
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y git gcc g++ make
RUN apt-get install unzip
RUN apt-get install build-essential -y
RUN apt-get install zlib1g-dev -y

ADD kissat_mab /pakis/kissat_mab
ADD bin /pakis/bin
ADD painless-src /pakis/painless-src
ADD Makefile /pakis/Makefile
ADD solver /pakis/solver

WORKDIR /pakis
RUN make all
ADD bin /pakis/bin
RUN cp PaKis ./bin/PaKis



###################
FROM satcomp-base:leader AS pakis_liaison
WORKDIR /
# Copy pakis and solver scripts
COPY --from=builder --chown=ecs-user /pakis/bin/ /competition/
USER ecs-user
RUN chmod +x /competition/PaKis
RUN chmod +x /competition/solver

