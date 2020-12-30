FROM yossarianlives/agda-notebook:latest

#banacorn/agda:2.6.0.1

# crosscompass/ihaskell-notebook:62631e7176e8

#RUN cabal update
#RUN cabal install alex happy Agda-2.6.1

USER root

RUN apt-get update
RUN apt-get install --yes python3-pip

USER $NB_UID

RUN python3 -m pip install --upgrade pip && \
    python3 -m pip install notebook
    
# RUN python3 -m pip install agda_kernel
# RUN python3 -m agda_kernel.install

RUN pwd
RUN ls -la

USER root

RUN pwd
RUN ls -la

#tmp/repo2docker* && ls -la && cd agda-kernel && make kernel-install

COPY --chown=$NB_UID:users . /home/$NB_USER/
#COPY ./agda-stdlib /home/$NB_USER/agda-stdlib
COPY --chown=$NB_UID:users ./src /home/$NB_USER/

USER $NB_UID

WORKDIR /home/$NB_USER/
RUN cd agda-kernel && make kernel-install

RUN git stash && git checkout -f store && git pull
RUN git config --global user.email "xxx@mybinder.com" && \
    git config --global user.name "mybinder"

RUN mkdir -p .agda/
RUN touch .agda/libraries
RUN echo "/home/$NB_USER/agda-stdlib/standard-library.agda-lib" > .agda/libraries

# pre-compile the standard library for reduce latency later
RUN cd "/home/$NB_USER/" && agda TypeOf.agda
RUN cd "/home/$NB_USER/" && agda part0/index.lagda.md
RUN cd "/home/$NB_USER/" && agda part1/index.lagda.md
RUN cd "/home/$NB_USER/" && agda part2/index.lagda.md

RUN cd "/home/$NB_USER/src" && agda part0/index.lagda.md
RUN cd "/home/$NB_USER/src" && agda part1/index.lagda.md
RUN cd "/home/$NB_USER/src" && agda part2/index.lagda.md

#ENV JUPYTER_ENABLE_LAB=yes
