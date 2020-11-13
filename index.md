---
title : Table of Contents
layout : home
link-citations: true
bibliography: bibliography.bib
csl: chicago.csl
notes-after-punctuation: false
---

<script type="text/x-thebe-config">
      {
        bootstrap: true,
	requestKernel: true,
        selector: "pre",
        binderOptions: {
          repo: "lclem/logic_course",
	  ref: "master",
	  binderUrl: "https://mybinder.org",
	  repoProvider: "github",
        },
        kernelOptions: {
          name: "agda",
	  kernelName: "agda",
	  path: ".",
    // notebook server configuration; not needed with binder
    // serverSettings: {
    //      "baseUrl": "http://127.0.0.1:8888",
    //      "token": "test-secret"
    //    }
        },

      }
</script>

<script type="text/javascript" src="https://unpkg.com/thebelab@latest"></script>

This book is an introduction to propositional and first-order logic.
The material is developed using the proof assistant Agda.

<pre>

module test where

id : ∀ {A : Set} → A → A
id x = x

</pre>
    
An example citation to [@Craig:JSL:1957]
and another to the same [@Craig:JSL:1957],
then @Craig:JSL:1957,
or even just (@Craig:JSL:1957),
finally another one [@Langford:AM:1926:B],
and then Craig again [@Craig:JSL:1957].

A nice quote about the spirit of formalisation:
Simon (1956) wrote to Russell in late 1956 and described the work of the LT (Logic Theorist).
Russell (1956) replied, "I am delighted to know that Principia Mathematica can now be done by machinery. I wish Whitehead and I had known of this possibility before we wasted ten years doing it by hand. I am quite willing to believe that everything in deductive logic can be done by machinery."

## Part 0: Programming in Agda

- [Natural numbers]({{ site.baseurl }}/part0/nat/).

## Part 1: Propositional logic

- [Syntax]({{ site.baseurl }}/part1/Syntax/): Syntax of propositional logic.
- [Semantics]({{ site.baseurl }}/part1/Semantics/): Semantics of propositional logic.
- [NormalForms]({{ site.baseurl }}/part1/NormalForms/): Negation, conjunctive, and disjunctive normal forms.

## Part 2: First-order logic

- [Syntax]({{ site.baseurl }}/part2/Syntax/): Syntax of first-order logic.
- [Semantics]({{ site.baseurl }}/part2/Semantics/): Semantics of first-order logic.

# References

<div id="refs" class="references hanging-indent">

Put refs here

</div>

### Footnotes