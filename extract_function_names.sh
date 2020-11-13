#!/bin/bash

#<a id="653" href="part1.Semantics.html#653" class="Function Operator">Val</a>
#<a id="\1" href="\2#\3" class="\4">\5</a>

# remove the space before operator to avoid issues later in the pipeline
#\4 not currently used

gsed -r "s/<\/a>/<\/a>\n/g" $1/$2 | perl -n -e'/<a id="(\d+)" href="([\w\.]*)\#(\d+)" class="([a-z A-Z]*)">([^<]*)<\/a>/ && print "$2.$3 '$2'.$1 $5\n"' | sed 's/ Operator/Operator/g' > $1/$2.dep
