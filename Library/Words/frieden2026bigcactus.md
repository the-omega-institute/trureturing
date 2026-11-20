---
bibkey: frieden2026bigcactus
authors: Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov
year: 2026
title: The big cactus group, invariant tensors, and rectangular tableaux
doi: 10.48550/arXiv.2610.24842
url: https://arxiv.org/html/2610.24842v1
claim: "Section 4.4 defines chronological sorting subnetworks, Theorem 4.9 proves avoidance for knitting words, and Conjecture 4.10 asks whether avoidance characterizes adapted reduced words."
strata_touched:
  - D5/S1/Words/Permutations/FriedenSortingNetwork
  - D5/S1/Words/Permutations/FriedenAdaptedWords
license: CC-BY-4.0
triage: anchor
---

# The big cactus group, invariant tensors, and rectangular tableaux

In §4.1 a flip at a source reverses all incident arrows. Section 4.3
defines adaptedness by testing for a source before each reflection.
Lemma 4.5 identifies the adapted reduced reversal words for a fixed
orientation with the knitting words for a path inducing that orientation.
Remark 4.6 specifies the source convention.

Section 4.4 defines an induced subnetwork by selecting wires and recording
the crossings among them. The subnetwork records these crossings in their
original time order with each generator numbered by position within the
selected order. Its forbidden set is
$X=\{123212,321232,212321,232123\}$.

Theorem 4.9 gives avoidance for knitting words. The first sentence of
Conjecture 4.10 (p. 15) states:

> A reduced word for $w_0 \in \mathfrak{S}_n$ is $X$-avoiding if and only if it is adapted to an orientation of $A_{n-1}$.

The Lean result proves this avoidance formulation using a four-wire
obstruction for sufficiency and the direction changes of individual
wires for necessity. The paper also gives a numerical formulation via
Meng's identity.

[Pinned source](https://arxiv.org/html/2610.24842v1#S4.Thmtheorem10)
