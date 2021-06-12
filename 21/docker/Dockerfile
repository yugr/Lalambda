FROM ubuntu:20.04

# Switch to bash for brace expansion
RUN ln -sf bash /bin/sh

# Setup source repos and update
ENV DEBIAN_FRONTEND=noninteractive
ENV COMPONENTS='main universe multiverse restricted'
RUN \
  apt-get update \
  && apt-get install -y gpg lsb-release \
  && apt-key adv --keyserver keyserver.ubuntu.com --recv-keys 428D7C01 C8CAB6595FDFF622 \
  && printf "deb http://us.archive.ubuntu.com/ubuntu %s $COMPONENTS\n" $(lsb_release -cs){,-updates,-security,-proposed,-backports} >> /etc/apt/sources.list \
  && printf "deb-src http://us.archive.ubuntu.com/ubuntu %s $COMPONENTS\n" $(lsb_release -cs){,-updates,-security,-proposed,-backports} >> /etc/apt/sources.list \
  && printf "deb http://ddebs.ubuntu.com %s $COMPONENTS\n" $(lsb_release -cs){,-updates,-proposed} | tee -a /etc/apt/sources.list.d/ddebs.list \
  && apt-get update \
  && apt-get upgrade -y

# Install prerequisites
RUN \
  apt-get install -y gcc g++ make gdb git vim bc \
  && apt-get install -y pbuilder cowbuilder

# Create custom pbuilder container config to disable mounts
# which docker does not like
RUN printf "%s=no\n" USEPROC USESHM USEDEVPTS USESYSFS > pbuilderrc

# Create pbuilder container
RUN pbuilder --create --configfile pbuilderrc --distribution $(lsb_release -cs) --components "$COMPONENTS"

# Setup pbuilder container
COPY pbuilder-setup /
RUN cat pbuilder-setup | pbuilder --login --configfile pbuilderrc --distribution $(lsb_release -cs) --save-after-login

ENTRYPOINT /bin/bash
