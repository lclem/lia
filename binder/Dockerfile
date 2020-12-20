FROM banacorn/agda:2.6.0.1

# crosscompass/ihaskell-notebook:62631e7176e8

#RUN cabal update
#RUN cabal install alex happy Agda-2.6.1

RUN apt-get update
RUN apt-get install --yes python3-pip

RUN pip3 install --no-cache --upgrade pip && \
    pip3 install --no-cache notebook
    
RUN pip3 install agda_kernel
RUN python -m agda_kernel.install

USER root

#RUN mkdir /home/$NB_USER/learn_you_a_haskell
#COPY notebook/*.ipynb /home/$NB_USER/learn_you_a_haskell/
#COPY notebook/img /home/$NB_USER/learn_you_a_haskell/img
#RUN chown --recursive $NB_UID:users /home/$NB_USER/learn_you_a_haskell

USER $NB_UID

ENV JUPYTER_ENABLE_LAB=yes
