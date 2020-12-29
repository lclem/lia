!define(ref)
~~~~~~~~~~~~
[`` !ifne(!2)()(!2)(!1) ``](#!ifne(!2)()(!1.!2)(!1))
~~~~~~~~~~~~

!define(remoteRef)
~~~~~~~~~~~~
[`` !ifne(!4)()(!4)(!3) ``](../../!1/!2#!ifne(!4)()(!3.!4)(!3))
~~~~~~~~~~~~

!define(chapterRef)
~~~~~~~~~~~~
[Ch. !1/!2](../../!1/!2)
~~~~~~~~~~~~

!define(flexRef)
~~~~~~~~~~~~
[!4](../../!1/!2#!3)
~~~~~~~~~~~~

!define(refExercise)
~~~~~~~~~~~~~
[Exercise %g](!1 "Exercise %g")
~~~~~~~~~~~~~

!define(refSection)
~~~~~~~~~~~~~
[this section](!1 "Section %g")
~~~~~~~~~~~~~

!define(preamble)
~~~~~~~~~~~~~~~~~
module !part().!chapter().!1 where  
open !part().!chapter() as !chapter()
~~~~~~~~~~~~~~~~~

!define(codemirror)
~~~~~~~~~~~~~~~~~~~~

<pre data-executable="true" data-language="agda" id="!part().!chapter().!1">
!preamble(!1)
!1 : typeOf !chapter().!1
-- BEGIN SOLUTION
!1 = ?
</pre>

~~~~~~~~~~~~~~~~~~~~


!define(exercise)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::::: {.exercisebox}

!ifne(!4)()(Exercise (!2) !1)(Exercise !1)
: !ifne(!4)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>

<!--
::::::: {.solutionlink}
[solution](!1-solution)
:::::::
-->

:::::

!append(solutions)
``````````````````

::::: {.solutionbox}

###### Solution to [Exercise %g](!1 "Exercise %g") {!1-solution}

!ifne(!4)()(!4)(!3)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
``````````````````
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(example)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.examplebox}
Example !1
: !2 <span class="hidden">∎</span><span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(theorem)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.theorembox}

!ifne(!3)()(Theorem (!2))(Theorem) !1
: !ifne(!3)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(lemma)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.lemmabox}

!ifne(!3)()(Lemma (!2))(Lemma) !1
: !ifne(!3)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(remark)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.remarkbox}

!ifne(!3)()(Remark (!2))(Remark) !1
: !ifne(!3)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(hide)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::::: {.introbox}

!1 <button type="button" class="hidden">[show]</button> <button type="button" class="collapsible">[show]</button>

:::::

::::: {.hidebox}

!2

:::::

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~