#!/bin/bash

cd src
jupyter notebook --port=8888 --NotebookApp.allow_origin='*' --NotebookApp.token=test-secret --no-browser