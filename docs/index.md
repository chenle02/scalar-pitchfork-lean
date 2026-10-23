---
title: "Scalar Pitchfork"
permalink: /
description: "Scalar pitchfork bifurcation with a jet-bounded remainder and the topology of global branches, formalized in Lean 4 with Mathlib."
---

<section class="hero">
<p class="eyebrow">Lean 4 / Mathlib library · release v0.1.0 · Apache-2.0</p>
<h1>Scalar Pitchfork</h1>
<img class="banner" src="{{ '/assets/banner.svg' | relative_url }}" alt="The trivial branch splitting at the critical parameter into two branches of nontrivial zeros">
</section>

The scalar pitchfork $`f(\tau,z)=\alpha\tau z-\beta z^3+R(\tau,z)`$ with a remainder bounded by explicit weights or by jets at the origin: two continuous branches $`z\approx\pm\sqrt{\alpha\tau/\beta}`$ with an $`O(|\tau|)`$ amplitude error and the stability sign, the classification of small zeros, and the topological skeleton of global branches. Formalized in Lean 4 with Mathlib.

<p class="actions"><a class="button" href="{{ '/what-is-proved.html' | relative_url }}">What is proved</a> <a class="button secondary" href="{{ '/verification.html' | relative_url }}">All Lean statements</a> <a class="button secondary" href="{{ '/getting-started.html' | relative_url }}">Get started</a></p>

<div class="boundary" markdown="1">
**Not proved here.**
- No Crandall–Rabinowitz theorem and no center-manifold reduction: the scalar normal form $`\alpha\tau z-\beta z^3+R`$ is the starting point, not derived from an operator equation.
- No Lyapunov–Schmidt reduction.
- No degree theory: no Leray–Schauder degree and no Rabinowitz global alternative. The global part is the topological skeleton only; the alternatives are hypotheses, not derived from degree theory.
- No certified-root tools: no interval arithmetic or root isolation for specific polynomials.
- No PDE: no existence, uniqueness or regularity theorem for any differential equation.
</div>

## Find your way

### Results

<div class="cards">
<div class="card"><h4><a href="{{ '/what-is-proved.html' | relative_url }}">What is proved</a></h4><p>Each result with its exact compared Lean statement.</p></div>
<div class="card"><h4><a href="{{ '/verification.html' | relative_url }}">All Lean statements</a></h4><p>Generated page: every result, its hypotheses, receipts and the checks that ran.</p></div>
<div class="card"><h4><a href="{{ '/coverage.html' | relative_url }}">Coverage table</a></h4><p>Every coverage row, its claims, inputs and notes.</p></div>
<div class="card"><h4><a href="{{ '/modules.html' | relative_url }}">Modules</a></h4><p>What each Lean module contains.</p></div>
</div>

### Use and trust

<div class="cards">
<div class="card"><h4><a href="{{ '/getting-started.html' | relative_url }}">Get started</a></h4><p>Build, verify, and depend on the library from your own Lake project.</p></div>
<div class="card"><h4><a href="{{ '/getting-started.html#trust-and-axioms' | relative_url }}">Trust and axioms</a></h4><p>Permitted axioms and what the comparator checks.</p></div>
<div class="card"><h4><a href="{{ '/acknowledgments.html' | relative_url }}">Acknowledgments and citation</a></h4><p>Authors and AI disclosure, lean-pkg, the Auburn University Easley Cluster, what it builds on, related work, and how to cite.</p></div>
</div>

## Related

This library was first developed for the [Chemotaxis III Lean companion](https://chenle02.github.io/chemotaxis-paper-iii-lean/). Its sibling library is [neumann-cosine-lean](https://chenle02.github.io/neumann-cosine-lean/). The two libraries are independent.
