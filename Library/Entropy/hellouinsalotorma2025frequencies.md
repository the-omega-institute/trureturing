---
bibkey: hellouinsalotorma2025frequencies
authors: Benjamin Hellouin de Menibus, Ville Salo, and Ilkka Törmä
year: 2025
title: Symbol Frequencies in Surjective Cellular Automata
doi: 10.48550/arXiv.2504.06058
url: https://arxiv.org/html/2504.06058v2
claim: Section 2 states that every finite word w has exactly card(Sigma)^r preimages under a surjective cellular automaton with forward neighborhood [0,r].
strata_touched:
  - D5/S1/Dynamics/Symbolic/SurjectiveWordBalance
license: citation-only
triage: anchor
---

# Finite-word balance

Section 2, under “Surjectivity and probability measures”, states the
balance property of a surjective cellular automaton:

$$
  |F^{-1}(w)|=|\Sigma|^r.
$$

The local rule reads a forward window of length `r+1`. A source word
for an output word of length `n` consequently has length `n+r`.
The native specialization takes `r=k+1`, so the local-rule domain is
`Fin(k+2) → A` and the source-word domain is `Fin(n+k+1) → A`.
Surjectivity is on all integer configurations, without endpoint
permutativity or restrictions on support or periodicity.

The formal statement includes the empty alphabet and output length
zero. These cases are explicit finite-cardinality obligations; no
probability measure on an empty alphabet is asserted. For a nonempty
alphabet, balance gives preservation of the uniform product law on
cylinders. The finite-word theorem itself is a counting statement and
does not require a probability-space construction.

The proof uses the classical preinjectivity consequence of
surjectivity. Concatenating independently chosen members of a fixed
word fiber and recording only the gaps between their fixed output
blocks gives an injective encoding. Its cardinality bound for every
number of blocks forces the fiber size to be at most `card(A)^(k+1)`.
Partitioning all source words by their outputs then forces equality
for every fiber. No claim of literature novelty is made.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2504.06058.
Primary version: https://arxiv.org/html/2504.06058v2.
Section 2, “Definitions”, paragraph “Surjectivity and probability
measures”, the displayed balance property immediately after the
definition of weak-* limit points.
