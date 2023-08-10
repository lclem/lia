#!/bin/sh

gsed -i -ne "$! N; /^.*\s*\n\s*<\/pre>/ { s/\s*\n\s*//; p; b }; $ { p; q }; P; D" $1