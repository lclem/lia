FROM yossarianlives/agda-notebook:latest

#banacorn/agda:2.6.0.1

# crosscompass/ihaskell-notebook:62631e7176e8

#RUN cabal update
#RUN cabal install alex happy Agda-2.6.1

USER root

RUN apt-get update
RUN apt-get install --yes python3-pip

USER $NB_UID

RUN python3 -m pip install --no-cache --upgrade pip && \
    python3 -m pip install --no-cache notebook
    
RUN python3 -m pip install agda_kernel
RUN python3 -m agda_kernel.install

USER root

#RUN mkdir /home/$NB_USER/learn_you_a_haskell
#COPY notebook/*.ipynb /home/$NB_USER/learn_you_a_haskell/
#COPY notebook/img /home/$NB_USER/learn_you_a_haskell/img
#RUN chown --recursive $NB_UID:users /home/$NB_USER/learn_you_a_haskell

USER $NB_UID

#ENV JUPYTER_ENABLE_LAB=yes
