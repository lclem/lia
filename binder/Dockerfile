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
    
RUN python3 -m pip install agda_kernel
RUN python3 -m agda_kernel.install

USER root

COPY . /home/$NB_USER/
#COPY ./agda-stdlib /home/$NB_USER/agda-stdlib
COPY ./src /home/$NB_USER/

RUN mkdir -p /home/$NB_USER/.agda/
RUN touch /home/$NB_USER/.agda/libraries
RUN echo "/home/$NB_USER/agda-stdlib/standard-library.agda-lib" > /home/$NB_USER/.agda/libraries

RUN chown --recursive $NB_UID:users /home/$NB_USER/

USER $NB_UID
RUN cd /home/$NB_USER/ && git stash && git checkout gh-pages && git pull
#ENV JUPYTER_ENABLE_LAB=yes
