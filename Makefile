OUTDIR := html
TMPDIR := tmp
SITEDIR := _site
DOCSDIR := docs
SRCDIR := src
BUILDDIR := $(SRCDIR)/_build
INCLUDES := _includes
SVGS := $(INCLUDES)/svgs
PARTS := part0 part1
#part1 part2 part3 part4
AGDA := agda
PP := ./pp/pp-macos
#~/.local/bin/pp
EPUBCHECK := epubcheck
RUBY := ruby
GEM := $(RUBY) -S gem
BUNDLE := $(RUBY) -S bundle
JEKYLL := $(BUNDLE) exec jekyll
HTMLPROOFER := $(BUNDLE) exec htmlproofer
#FIX_LINKS := $(TMP)/fix-links.sed
ASPELL = aspell

# the citation style
CSL := natbib.csl

# the bibliography file
BIB := bibliography.bib

ifeq ($(shell pandoc --version | head -n1),pandoc 2.11.1.1)
	# more recent pandoc versions embed the citeproc library
	PANDOCEXEC := pandoc --citeproc
else
	PANDOCEXEC := pandoc --filter=pandoc-citeproc
endif

PANDOC := $(PANDOCEXEC) --filter=pandoc-numbering --bibliography=$(BIB) --csl=$(CSL) --metadata link-citations=true --from markdown --to markdown_phpextra
#--metadata numbersections=true --metadata number-sections=true --number-sections 
$(info PANDOC: $(PANDOC))

#$(info PARTS:$(PARTS))

AGDA_SOURCES := $(shell find $(SRCDIR) -name '*.lagda.md' -and -not -name '.\#*')
#$(info AGDA_SOURCES:$(AGDA_SOURCES))

AGDA_MODULES := $(patsubst %.lagda.md,%,$(notdir $(AGDA_SOURCES)))
#$(info AGDA_MODULES:$(AGDA_MODULES))

#AGDA_TMPS := $(foreach PART,$(PARTS),$(foreach AGDA_MODULE,$(AGDA_MODULES),$(TMPDIR)/$(PART).$(AGDA_MODULE).md))
#$(info AGDA_TMPS:$(AGDA_TMPS))

#AGDA_DEPS := $(patsubst %,%.dep,$(AGDA_TMPS))
#$(info AGDA_DEPS:$(AGDA_DEPS))

#AGDA_MD := $(patsubst $(SRCDIR)/%.lagda.md,$(OUTDIR)/%.md,$(AGDA_SOURCES))
#$(info AGDA_MD:$(AGDA_MD))

MARKDOWN_SOURCES := $(shell find $(SRCDIR) -name '*.md' -and -not -name '*.lagda.md' -and -not -name '*\#*')
#$(info MARKDOWN_SOURCES:$(MARKDOWN_SOURCES))

MARKDOWN_MD := $(patsubst $(SRCDIR)/%.md,$(OUTDIR)/%.md,$(MARKDOWN_SOURCES))
#$(info MARKDOWN_MD:$(MARKDOWN_MD))

PART_DIRS := $(patsubst %,$(OUTDIR)/%,$(PARTS))
#$(info PART_DIRS:$(PART_DIRS))

#agda: $(AGDA_MD)

.PHONY: all build agda markdown serve server-start server-stop clean keys refs spellcheck
#html/part1/NormalForms.md tmp/part1.NormalForms.md html/part1/Interpolation.md tmp/part1.Interpolation.md

#$(TMPDIR)/all.dep.txt $(TMPDIR)/keys.dep.txt $(TMPDIR)/all_keys.dep.txt

all: build

docs: build
	rm -fr $(DOCSDIR)/ && rsync -aP $(SITEDIR)/ $(DOCSDIR)/

clean:
	@rm -fr keys.make $(OUTDIR)/ $(TMPDIR)/ $(SITEDIR)/ $(BUILDDIR)/ $(SVGS)/ $(DOCSDIR)/

markdown: agda refs $(MARKDOWN_MD)

spellcheck:
	@echo " [DONE]"

$(OUTDIR):
	@mkdir -p $(OUTDIR)

# $(TMPDIR):
# 	@mkdir -p $(TMPDIR)

# $(PART_DIRS): $(OUTDIR)/%:
# 	@mkdir -p $@

check: build
	$(HTMLPROOFER) ./_site

build: markdown
	$(JEKYLL) build --incremental --trace

# Start Jekyll server with --incremental
serve: markdown
	$(JEKYLL) serve --incremental
#pkill -f fswatch

watch:
	fswatch -o ./src | xargs -n1 -I{} make agda2

# Start detached Jekyll server
server-start:
	$(JEKYLL) serve --incremental --no-watch --detach

# Stop detached Jekyll server
server-stop:
	pkill -f jekyll

# special treatment for the index
agda: $(OUTDIR) $(OUTDIR)/index.md

$(OUTDIR)/index.md: $(SRCDIR)/index.md
	@echo "$(SRCDIR)/index.md --> $(OUTDIR)/index.md\c"

	@$(PANDOC) $(SRCDIR)/index.md -o $(OUTDIR)/index.md

	$(eval LAST_MODIFIED := $(shell stat -f "%Sm" $(SRCDIR)/index.md))

	@gsed -i "1i---" $(OUTDIR)/index.md
	@gsed -i "2ititle : Table of Contents" $(OUTDIR)/index.md
	@gsed -i "3ilayout : home" $(OUTDIR)/index.md
	@gsed -i "4ilast-modified: $(LAST_MODIFIED)" $(OUTDIR)/index.md
	@gsed -i "5ipermalink: /" $(OUTDIR)/index.md
	@gsed -i "6i---" $(OUTDIR)/index.md
#	@gsed -i "6i " $(OUTDIR)/index.md

	@echo " [DONE]"

# don't process refs for now
# define process_refs

# $(OUTDIR)/refs/$1/$2/index.md: $(OUTDIR)/refs/$1/$2/$4.dep

# $(OUTDIR)/refs/$1/$2/$4.dep:
# 	@mkdir -p $(OUTDIR)/refs/$1/$2/
# 	@echo "making $(OUTDIR)/refs/$1/$2/$4.dep...\c"

# # @echo "---" > $(OUTDIR)/refs/$1/$2/$4.md
# # @echo "title: References to \`"'$5'"\`" >> $(OUTDIR)/refs/$1/$2/$4.md
# # @echo "permalink: /refs/$1/$2/$4" >> $(OUTDIR)/refs/$1/$2/$4.md
# # @echo "---" >> $(OUTDIR)/refs/$1/$2/$4.md

# #	@echo "ref to $5"
# 	@echo "References to "'$5'" {#ref-$4}: \n" > $(OUTDIR)/refs/$1/$2/$4.dep

# 	@cat $(TMPDIR)/all.dep.txt | awk -f dep_filter.awk -v mykey=$1.$2.$3.$4 | sed 's|\([a-zA-Z0-9]*\)\.\([a-zA-Z0-9]*\)\.\([a-zA-Z0-9]*\)\.\([0-9]*\)|\* [{% link '$(OUTDIR)'/\1/\2.md %}#\4]({% link '$(OUTDIR)'/\1/\2.md %}#\4)|' >> $(OUTDIR)/refs/$1/$2/$4.dep

# 	@echo "\n" >> $(OUTDIR)/refs/$1/$2/$4.dep

# 	@echo " [DONE]"

# #part0.vector.md.21610

# #refs: $(OUTDIR)/refs/$1/$2/$4.md

# endef

# use keys.dep.txt;
# use all_keys.dep.txt in case you want to create refs also for names not referenced anywhere else...
# each entry in keys.dep.txt is of the format (example) Agda.Primitive.md.636.⊔

keys_exist := $(wildcard $(TMPDIR)/keys.dep.txt)

ifneq ($(strip $(keys_exist)),)

# if keys.dep.txt already exists, then use it to generate refs dependencies;
# it is convenient to have this rule when running "make clean"
# (otherwise it will try to build keys.dep.txt every time...)

# don't do refs now
# REFS := $(shell cat $(TMPDIR)/keys.dep.txt)
# $(foreach REF,$(REFS),$(eval $(call process_refs,$(word 1,$(subst ., ,$(REF))),$(word 2,$(subst ., ,$(REF))),$(word 3,$(subst ., ,$(REF))),$(word 4,$(subst ., ,$(REF))),$(word 5,$(subst ., ,$(REF))))))

else

# generate the code above dynamically if keys.dep.txt does not exists yet
-include keys.make

endif

keys.make: Makefile $(TMPDIR)/keys.dep.txt

	@echo "making $@...\c"

	@printf 'REFS := $$(shell cat $$(TMPDIR)/keys.dep.txt)\n' > $@
	@printf '$$(foreach REF,$$(REFS),$$(eval $$(call process_refs,$$(word 1,$$(subst ., ,$$(REF))),$$(word 2,$$(subst ., ,$$(REF))),$$(word 3,$$(subst ., ,$$(REF))),$$(word 4,$$(subst ., ,$$(REF))),$$(word 5,$$(subst ., ,$$(REF))))))' >> $@

	@echo " [DONE]"

define add_dependency

$(TMPDIR)/$1.$2.md: $(SRCDIR)/$1/$2.lagda.md
	@echo "$(SRCDIR)/$1/$2.lagda.md --> $(TMPDIR)/$1.$2.md\c"
	@cd $(SRCDIR) && $(AGDA) --library-file=../.agda/libraries --html --html-highlight=code --html-dir=../$(TMPDIR) "$1/$2.lagda.md" | \
		sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /.*Checking.*/d' | \
		tr -d '\n'
	@echo " [DONE]"

# don't do dependency graph
# $(TMPDIR)/$1.$2.dot: $(SRCDIR)/$1/$2.lagda.md
# 	@echo "$(SRCDIR)/$1/$2.lagda.md --> $(TMPDIR)/$1.$2.dot\c"
# 	@cd $(SRCDIR) && $(AGDA) --dependency-graph="../$(TMPDIR)/$1.$2.dot" "$1/$2.lagda.md"

# # improve the dot file

# 	@gsed -i '2i\
# 	layout=dot;\
# 	rankdir=TB;\
# 	overlap=false;\
# 	concentrate=true;\
# 	ranksep=0.35;\
# 	splines=ortho;\
# 	nodesep=0.25;\
# 	fixedsize=true;\
# 	ratio=0.6;\
# 	compound=true;\
# 	size="7.5";\
# 	node [shape=record, style=rounded, fixedsize=true, width=2, height=0.45, bgcolor=aliceblue, fillcolor=lightsteelblue3, fontsize=14];\
# 	' $(TMPDIR)/$1.$2.dot

# #	size="8,1000";
# #	node [shape=record, style=filled, fixedsize=true, width=2, height=0.45, fillcolor=lightsteelblue3, fontsize=14];\

# # add clickable links
# # example: [label="part0.Booleans"] becomes [label="part0.Booleans", URL="{% link '$(OUTDIR)/$1/$2.md %}"]

# 	@sed -i "" 's|\[label="\([a-zA-Z0-9]*\)\.\([a-zA-Z0-9]*\)"\]|\[label="\1\.\2", URL="{% link '$(OUTDIR)'/\1/\2.md %}"\]|g' $(TMPDIR)/$1.$2.dot

# # remove links to html/Agda/Primitive.md because it does not exist
# 	@sed -i "" 's|, URL="{% link html/Agda/Primitive.md %}"||g' $(TMPDIR)/$1.$2.dot

# 	@echo " [DONE]"

# $(SVGS)/$1/$2.svg: $(TMPDIR)/$1.$2.dot
# 	@echo "$(TMPDIR)/$1.$2.dot --> $(SVGS)/$1/$2.svg\c"
# 	@mkdir -p $(SVGS)/$1/
# 	@dot $(TMPDIR)/$1.$2.dot -Tsvg -o $(SVGS)/$1/$2.svg

# # remove the first five lines from the svg
# 	@sed -i "" '1,5d' $(SVGS)/$1/$2.svg

# 	@echo " [DONE]"

# dummy output
$(TMPDIR)/$1.$2.lagda.md.spellcheckme: $(SRCDIR)/$1/$2.lagda.md
#	@cat $(SRCDIR)/$1/$2.lagda.md | sed "s|@[^@]*||g" > $(TMPDIR)/$1.$2.lagda.md.spellcheckme
	@$(ASPELL) --home-dir=spell-checker/ --lang=en_GB --mode=markdown --add-filter url --add-filter url --add-filter tex -c $(SRCDIR)/$1/$2.lagda.md
	@printf .

spellcheck: $(TMPDIR)/$1.$2.lagda.md.spellcheckme
.PHONY: $(TMPDIR)/$1.$2.lagda.md.spellcheckme

# don't do deps
$(TMPDIR)/$1.$2.md.dep: $(TMPDIR)/$1.$2.md
	@echo "$(TMPDIR)/$1.$2.md --> $(TMPDIR)/$1.$2.md.dep\c"

# prepare the source by adding #'s to module names, as follows:
# <a id="37" class="Keyword">module</a> <a id="44" href="part0.Booleans.html" class="Module"> becomes
# <a id="37" class="Keyword">module</a> <a id="44" href="part0.Booleans.html#44" class="Module">
# this is necessary to have also module names appear in the dep file
	@sed -i "" 's|<a id="\([0-9]*\)" class="Keyword">module</a> <a id="\([^"]*\)" href="\([a-zA-Z0-9\.]*\)" class="Module">|<a id="\1" class="Keyword">module</a> <a id="\2" href="\3#\2" class="Module">|g' $(TMPDIR)/$1.$2.md

	@./extract_function_names.sh $(TMPDIR) $1.$2.md

# sanitise a bit
# &lt; becomes <
# &gt; becomes >
# &#39; becomes '

#	@sed -i "" 's|&lt;|<|g' $(TMPDIR)/$1.$2.md.dep
#	@sed -i "" 's|&gt;|>|g' $(TMPDIR)/$1.$2.md.dep
#	@sed -i "" "s|&\#39;|'|g" $(TMPDIR)/$1.$2.md.dep
#	@./escape_dollar.sh $(TMPDIR)/$1.$2.md.dep

	@echo " [DONE]"

# MAIN WORKHORSE
$(OUTDIR)/$1/$2.md: $(TMPDIR)/$1.$2.md
	@echo "$(TMPDIR)/$1.$2.md --> $(OUTDIR)/$1/$2.md\c"

	$(eval LAST_MODIFIED := $(shell stat -f "%Sm" $(SRCDIR)/$1/$2.lagda.md))

	@mkdir -p $(OUTDIR)/$1

	@cat $(TMPDIR)/$1.$2.md > $(TMPDIR)/$1.$2.headers.md

	@gsed -i "3isrc: $(SRCDIR)/$1/$2.lagda.md" $(TMPDIR)/$1.$2.headers.md
	@gsed -i "4ilayout: page" $(TMPDIR)/$1.$2.headers.md
	@gsed -i "5ipermalink: /$(1)/$(2)/" $(TMPDIR)/$1.$2.headers.md
	@gsed -i "6ilast-modified: $(LAST_MODIFIED)" $(TMPDIR)/$1.$2.headers.md
	@gsed -i "7ipart: /$(1)/index/" $(TMPDIR)/$1.$2.headers.md
	@gsed -i "8itoc: true" $(TMPDIR)/$1.$2.headers.md
	@gsed -i "9inumbersections: true" $(TMPDIR)/$1.$2.headers.md
#	@gsed -i "10ipandoc-numbering:" $(TMPDIR)/$1.$2.headers.md
#	@gsed -i "11i\    exercise:" $(TMPDIR)/$1.$2.headers.md
#	@gsed -i "12i\        general:" $(TMPDIR)/$1.$2.headers.md
#	@gsed -i "13i\            listing-title: List of exercises" $(TMPDIR)/$1.$2.headers.md
#	@gsed -i "14i\            listing-identifier: False" $(TMPDIR)/$1.$2.headers.md

# WARNING: the number of added lines will affect the following!

# STEP 0: expand solution entries

	@$(PP) -import pp-macros.txt $(TMPDIR)/$1.$2.headers.md > $(TMPDIR)/$1.$2.pp.md

# 2>/dev/null || true

# STEP 1: process citations
# Table of contents shows up only with options "--from markdown --to markdown_phpextra"
	@$(PANDOC) $(TMPDIR)/$1.$2.pp.md -o $(TMPDIR)/$1.$2.pandoc.md
# 

# sometimes pandoc transforms <pre class="Agda"> to <pre markdown="1" class="Agda">, we need to undo this 
	@sed -i "" 's|<pre markdown="1" class="Agda">|<pre class="Agda">|g' $(TMPDIR)/$1.$2.pandoc.md

# sometimes pandoc adds section references such as {#an-unreferenced-section .unnumbered}, but we need to remove .unnumbered
	@sed -i "" 's| .unnumbered||g' $(TMPDIR)/$1.$2.pandoc.md

# re-copy the headers
	@head -n11 $(TMPDIR)/$1.$2.headers.md > $(OUTDIR)/$1/$2.md

# add an horizontal separator
#	@echo "\n\n---\n\n" >> $(OUTDIR)/$1/$2.md

	@cat $(TMPDIR)/$1.$2.pandoc.md >> $(OUTDIR)/$1/$2.md

#	@cp -f $(TMPDIR)/$1.$2.md $(OUTDIR)/$1/$2.md

	@sed -i "" 's|<pre class="Agda">|{% raw %}<pre class="Agda">|g' $(OUTDIR)/$1/$2.md
	@sed -i "" 's|</pre>|</pre>{% endraw %}|g' $(OUTDIR)/$1/$2.md

#{% include markdown_file.md %}

# change the href link in those positions where names are first declared;
# this is achieved by matching on positions as below
# <a id="𝔹"></a><a id="200" href="part0.Booleans.html#200"

#IGNORE FOR NOW
#	@sed -i "" 's|<a id="\([^"]*\)"></a><a id="\([0-9]*\)" href="\([a-zA-Z0-9\.]*\)\#[0-9]*"|<a id="\1"></a><a id="\2" href="{% endraw %}{% link '$(OUTDIR)/refs/$1/$2/'index.md %}#ref-\2{% raw %}"|g' $(OUTDIR)/$1/$2.md

# do the same for modules, we now match on things like
# <a id="37" class="Keyword">module</a> <a id="44" href="part0.Booleans.html" class="Module"> or
# <a id="113" class="Keyword">module</a> <a id="120" href="part1.Hilbert.html#120" class="Module">part1.Hilbert</a>

#IGNORE FOR NOW
#	@sed -i "" 's|<a id="\([^"]*\)" class="Keyword">module</a> <a id="\([^"]*\)" href="[^"]*" class="Module">|<a id="\1" class="Keyword">module</a> <a id="\2" href="{% endraw %}{% link '$(OUTDIR)/refs/$1/$2/'index.md %}{% raw %}" class="Module">|g' $(OUTDIR)/$1/$2.md

# this is just for debugging to see the intermediate result
#	@cp $(OUTDIR)/$1/$2.md $(OUTDIR)/$1/$2.md.txt

#	@gsed -i "3isrc: $(SRCDIR)/$1/$2.lagda.md" $(OUTDIR)/$1/$2.md
#	@gsed -i "4ilayout: page" $(OUTDIR)/$1/$2.md
#	@gsed -i "5ipermalink: /$(1)/$(2)/" $(OUTDIR)/$1/$2.md
#	@gsed -i "6ilast-modified: $(LAST_MODIFIED)" $(OUTDIR)/$1/$2.md
#	@gsed -i "7ipart: /$(1)/index/" $(OUTDIR)/$1/$2.md
#	@gsed -i "8itoc: true" $(OUTDIR)/$1/$2.md
#	@gsed -i "9inumbersections: true" $(OUTDIR)/$1/$2.md
#	@gsed -i "10ipandoc-numbering:" $(OUTDIR)/$1/$2.md
#	@gsed -i "11i\    exercise:" $(OUTDIR)/$1/$2.md
#	@gsed -i "12i\        general:" $(OUTDIR)/$1/$2.md
#	@gsed -i "13i\            listing-title: List of exercises" $(OUTDIR)/$1/$2.md

#{{ site.baseurl }}

# fix the links in place: $(PART).$(AGDA_MODULE).html --> $(OUTDIR)/$(PART)/$(AGDA_MODULE).md
	@$(foreach PART,$(PARTS),$(foreach AGDA_MODULE,$(AGDA_MODULES),sed -i "" 's+$(PART).$(AGDA_MODULE).html+{% endraw %}{{ site.baseurl }}{% link $(OUTDIR)/$(PART)/$(AGDA_MODULE).md %}{% raw %}+g;' $(OUTDIR)/$1/$2.md;))

	@echo " [DONE]"

# don't do refs
# $(OUTDIR)/refs/$1/$2/index.md: $(SVGS)/$1/$2.svg

# 	@echo "making $(OUTDIR)/refs/$1/$2/index.md...\c"

# 	@mkdir -p $(OUTDIR)/refs/$1/$2/
# 	@echo "\c" > $(OUTDIR)/refs/$1/$2/index.md

# 	@echo "---" > $(OUTDIR)/refs/$1/$2/index.md
# 	@echo "title: References to $1/$2" >> $(OUTDIR)/refs/$1/$2/index.md
# 	@echo "permalink: /refs/$1/$2/" >> $(OUTDIR)/refs/$1/$2/index.md
# 	@echo "---\n" >> $(OUTDIR)/refs/$1/$2/index.md

# # start with the graphviz dependency map

# 	@echo "{% include svgs/$1/$2.svg %}\n" >> $(OUTDIR)/refs/$1/$2/index.md

# # make sure there is at least one .dep file
# 	@touch $(OUTDIR)/refs/$1/$2/dummy.dep
# 	@cat $(OUTDIR)/refs/$1/$2/*.dep >> $(OUTDIR)/refs/$1/$2/index.md

# 	@echo " [DONE]"

# don't add these dependencies for a moment

#refs: $(OUTDIR)/refs/$1/$2/index.md
#$(TMPDIR)/all.dep.txt: $(TMPDIR)/$1.$2.md.dep

agda: $(OUTDIR)/$1/$2.md

endef

# don't do these
# $(TMPDIR)/all.dep.txt:

# 	@echo "making $(TMPDIR)/all.dep.txt...\c"

# #	@rm -f $(TMPDIR)/all.dep.txt $(TMPDIR)/keys.dep.txt $(TMPDIR)/all_keys.dep.txt

# # concatenate together all the dependency files
# 	@cat $(TMPDIR)/*.dep > $(TMPDIR)/all.dep.txt

# # for uniformity, replace all .html extensions to .md
# 	@sed -i "" 's/\.html/\.md/g' $(TMPDIR)/all.dep.txt

# 	@echo " [DONE]"

# $(TMPDIR)/keys.dep.txt: $(TMPDIR)/all.dep.txt

# 	@echo "making $(TMPDIR)/keys.dep.txt...\c"

# # extract all the destinations + symbol
# 	@cat $(TMPDIR)/all.dep.txt | awk 'BEGIN { FS=" ";} /^.*/ {print $$3" "$$1; next;}' > $(TMPDIR)/keys.dep.txt.1

# # remove duplicates, according to the id only (not considering the symbol)
# 	@cat $(TMPDIR)/keys.dep.txt.1 | sort -k 2 -u > $(TMPDIR)/keys.dep.txt.2

# # flip the order and convert newlines to single spaces
# 	@cat $(TMPDIR)/keys.dep.txt.2 | awk 'BEGIN { FS=" ";} /^.*/ {print $$2"."$$1; next;}' | paste -s -d ' ' - > $(TMPDIR)/keys.dep.txt

# # remove temporary files
# 	@rm -f $(TMPDIR)/keys.dep.txt.1 $(TMPDIR)/keys.dep.txt.2

# #$(TMPDIR)/all_keys.dep.txt: $(TMPDIR)/all.dep.txt
# #	@cat $(TMPDIR)/all.dep.txt | awk 'BEGIN { FS=" ";} /^.*/ {print $$1"."$$3; print $$2"."$$3; next;}' | sort | uniq | paste -s -d ' ' - > $(TMPDIR)/all_keys.dep.txt

# 	@echo " [DONE]"

# keys: $(TMPDIR)/keys.dep.txt 
# #$(TMPDIR)/all_keys.dep.txt

# refs: keys

$(foreach SOURCE,$(AGDA_SOURCES),$(eval $(call add_dependency,$(word 2,$(subst /, ,$(SOURCE))),$(word 1,$(subst ., ,$(word 3,$(subst /, ,$(SOURCE))))))))

agda2:
	make agda
	make agda
