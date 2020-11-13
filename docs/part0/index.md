---
title: "Part 0: Basic programming in Agda"
src: src/part0/index.lagda.md
layout: page
permalink: /part0/index/
last-modified: Nov  9 10:46:09 2020
part: /part0/index/
toc: true
numbersections: true
---

{% raw %}<pre class="Agda"><a id="57" class="Keyword">module</a> <a id="64" href="{% endraw %}{% link docs/refs/part0/index/index.md %}{% raw %}" class="Module">part0.index</a> <a id="76" class="Keyword">where</a>
<a id="82" class="Keyword">open</a> <a id="87" class="Keyword">import</a> <a id="94" href="{% endraw %}{% link docs/part0/utils.md %}{% raw %}" class="Module">part0.utils</a> <a id="106" class="Keyword">public</a>
<a id="113" class="Keyword">open</a> <a id="118" class="Keyword">import</a> <a id="125" href="{% endraw %}{% link docs/part0/eq.md %}{% raw %}" class="Module">part0.eq</a> <a id="134" class="Keyword">public</a>
<a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="{% endraw %}{% link docs/part0/decidable.md %}{% raw %}" class="Module">part0.decidable</a> <a id="169" class="Keyword">public</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="{% endraw %}{% link docs/part0/Booleans.md %}{% raw %}" class="Module">part0.Booleans</a> <a id="203" class="Keyword">public</a>
<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="{% endraw %}{% link docs/part0/nat.md %}{% raw %}" class="Module">part0.nat</a> <a id="232" class="Keyword">public</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="{% endraw %}{% link docs/part0/fun.md %}{% raw %}" class="Module">part0.fun</a> <a id="261" class="Keyword">public</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="{% endraw %}{% link docs/part0/vector.md %}{% raw %}" class="Module">part0.vector</a> <a id="293" class="Keyword">public</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="{% endraw %}{% link docs/part0/wf.md %}{% raw %}" class="Module">part0.wf</a> <a id="321" class="Keyword">public</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="{% endraw %}{% link docs/part0/list.md %}{% raw %}" class="Module">part0.list</a> <a id="351" class="Keyword">public</a>
<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="{% endraw %}{% link docs/part0/Fin.md %}{% raw %}" class="Module">part0.Fin</a> <a id="380" class="Keyword">public</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="{% endraw %}{% link docs/part0/decidable.md %}{% raw %}" class="Module">part0.decidable</a> <a id="415" class="Keyword">public</a>
<a id="422" class="Keyword">open</a> <a id="427" class="Keyword">import</a> <a id="434" href="{% endraw %}{% link docs/part0/Enum.md %}{% raw %}" class="Module">part0.Enum</a> <a id="445" class="Keyword">public</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="{% endraw %}{% link docs/part0/Context.md %}{% raw %}" class="Module">part0.Context</a> <a id="478" class="Keyword">public</a>
<a id="485" class="Keyword">open</a> <a id="490" class="Keyword">import</a> <a id="497" href="{% endraw %}{% link docs/part0/Tree.md %}{% raw %}" class="Module">part0.Tree</a> <a id="508" class="Keyword">public</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}" class="Module">part0.logic</a> <a id="539" class="Keyword">using</a> <a id="545" class="Symbol">(</a><a id="546" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#316" class="Record">Σ</a><a id="547" class="Symbol">;</a> <a id="549" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#129" class="Function">Π</a><a id="550" class="Symbol">;</a> <a id="552" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#208" class="Function">forAll</a><a id="558" class="Symbol">;</a> <a id="560" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#453" class="Function">thereExists</a><a id="571" class="Symbol">;</a> <a id="573" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#388" class="InductiveConstructor Operator">_,_</a><a id="576" class="Symbol">;</a> <a id="578" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#408" class="Field">dfst</a><a id="582" class="Symbol">;</a> <a id="584" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#423" class="Field">dsnd</a><a id="588" class="Symbol">;</a> <a id="590" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1240" class="Field">fst</a><a id="593" class="Symbol">;</a> <a id="595" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1252" class="Field">snd</a><a id="598" class="Symbol">;</a> <a id="600" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1663" class="Function">⊥-elim</a><a id="606" class="Symbol">;</a> <a id="608" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1900" class="InductiveConstructor">left</a><a id="612" class="Symbol">;</a> <a id="614" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1921" class="InductiveConstructor">right</a><a id="619" class="Symbol">;</a> <a id="621" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#2528" class="Function Operator">_↔_</a><a id="624" class="Symbol">)</a> <a id="626" class="Keyword">renaming</a> <a id="635" class="Symbol">(</a><a id="636" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1156" class="Record Operator">_∧_</a> <a id="640" class="Symbol">to</a> <a id="_∧_"></a><a id="643" href="{% endraw %}{% link docs/refs/part0/index/index.md %}#ref-643{% raw %}" class="Record Operator">_×_</a><a id="646" class="Symbol">;</a> <a id="648" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1842" class="Datatype Operator">_∨_</a> <a id="652" class="Symbol">to</a> <a id="_∨_"></a><a id="655" href="{% endraw %}{% link docs/refs/part0/index/index.md %}#ref-655{% raw %}" class="Datatype Operator">_⊎_</a><a id="658" class="Symbol">;</a> <a id="660" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1648" class="Datatype">⊥</a> <a id="662" class="Symbol">to</a> <a id="⊥"></a><a id="665" href="{% endraw %}{% link docs/refs/part0/index/index.md %}#ref-665{% raw %}" class="Datatype">F</a><a id="666" class="Symbol">;</a> <a id="668" href="{% endraw %}{% link docs/part0/logic.md %}{% raw %}#1722" class="Function Operator">¬_</a> <a id="671" class="Symbol">to</a> <a id="¬_"></a><a id="674" href="{% endraw %}{% link docs/refs/part0/index/index.md %}#ref-674{% raw %}" class="Function Operator">~_</a><a id="676" class="Symbol">)</a> <a id="678" class="Keyword">public</a>
</pre>{% endraw %}

Literature on learning Agda

-   [Norell](#ref-Norell:AFP:2009) \[[(2009)](#ref-Norell:AFP:2009)\].
-   [Oury and Swierstra](#ref-OurySwierstra:ICFP:2008)
    \[[(2008)](#ref-OurySwierstra:ICFP:2008)\].
-   [Bove and Dybjer](#ref-BoveDybjer:LerNet:2008)
    \[[(2008)](#ref-BoveDybjer:LerNet:2008)\].

<div id="refs" class="references csl-bib-body hanging-indent"
markdown="1">

<div id="ref-BoveDybjer:LerNet:2008" class="csl-entry" markdown="1">

\[Bove and Dybjer(2008)\] A Bove and P Dybjer. Dependent types at work.
In A Bove et al., editors., *Language engineering and rigorous software
development*, pages 57–99. Springer-Verlag, Berlin, Heidelberg, 2008.

</div>

<div id="ref-Norell:AFP:2009" class="csl-entry" markdown="1">

\[Norell(2009)\] U Norell. Dependently typed programming in agda.
*Proceedings of the 6th international conference on advanced functional
programming* (Berlin, Heidelberg, 2009), 230–266.

</div>

<div id="ref-OurySwierstra:ICFP:2008" class="csl-entry" markdown="1">

\[Oury and Swierstra(2008)\] N Oury and W Swierstra. The power of pi.
*Proc. Of ICFP’08* (2008), 39–50.

</div>

</div>
