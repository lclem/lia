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
        codeMirrorConfig: {
            //theme: "abcdef",
            language: "agda",
            readOnly: false,
            lineNumbers: true,
            keyMap: "default",
        },
        kernelOptions: {
            name: "agda",
            kernelName: "agda",
            path: "src/",
            // notebook server configuration; not needed with binder
            serverSettings: {
                  baseUrl: "http://127.0.0.1:8888",
                  token: "test-secret",
                },
        },
//        binderOptions: {
//            repo: "lclem/lia",
//            ref: "main",
//            binderUrl: "https://mybinder.org",
//            repoProvider: "github",
//            savedSession: {
//                enabled: true,
//                maxAge: 86400, // the max age in seconds to consider re-using a session
//                storagePrefix: "thebe-binder-"
//            },
//      },
      }
</script>

<!-- <script type="text/javascript" src="https://unpkg.com/thebelab@latest"></script> -->

<!-- own version of thebe library: -->
<script type="text/javascript" src="thebe/lib/index.js"></script>

<!-- proper highlighting for Agda -->
<script src="codemirror-agda/lib/index.js"></script>

<pre data-executable="true" data-language="agda">

module test where

open import part0.Naturals

variable
    ℓ m : Level
    A : Set ℓ
    B : Set m

proj1 : A → B → A
proj1 x y = x

proj2 : A → B → B
proj2 x y = ?

data Two : Set where
    one : Two
    two : Two

select : Two → A → A → A
select x a₀ a₁ = {! x !}
</pre>


This book is an introduction to propositional and first-order logic.
The material is developed using the proof assistant Agda.

Inspirations:

* [@plfa20.07] for showing that beautiful books can be written in Agda. A lot of the layout is inspired from [@plfa20.07].
* The [Software Foundations](https://softwarefoundations.cis.upenn.edu/) book (in [Coq](https://coq.inria.fr/)).
* The [Xena project](https://xenaproject.wordpress.com/) lead by Kevin Buzzard on teaching undergraduate mathematics with the [Lean](https://leanprover.github.io/) proof assistant.

A nice quote about the spirit of formalisation:
Simon (1956) wrote to Russell in late 1956 and described the work of the LT (Logic Theorist).
Russell (1956) replied, "I am delighted to know that Principia Mathematica can now be done by machinery. I wish Whitehead and I had known of this possibility before we wasted ten years doing it by hand. I am quite willing to believe that everything in deductive logic can be done by machinery."

Agda resources:

* [@Stump:ACM:2016]
* [@McBride:2013]
* [@Norell:AFP:2008]
* [@agda-dybjer:2018]
* [@BoveDybjer:LerNet:2008]

Other dependent types resources

* [@Chlipala:MIT:2013]

Logic resources:

* [@Harrison:CUP:2009]

## Part 0: Programming in Agda 🚧

- [Natural numbers](/part0/Naturals.md) 🚧 .
- [Lists](/part0/List.md) 🚧 .

## Part 1: Classical propositional logic 🚧

- [Syntax and semantics](/part1/Semantics.md): Syntax and semantics of propositional logic 🚧.

<!--
- [Normal forms]({{ site.baseurl }}/part1/NormalForms/): Negation, conjunctive, and disjunctive normal forms 🚧.
-->

::: {#refs}

# References

:::
