---
bibkey: shao2026italiandomination
authors: Pingping Shao; Chengye Zhao
year: 2026
title: Counting Weight-k Italian Dominating Sets on Trees and Cycles
doi: 10.48550/arXiv.2610.00108
url: https://arxiv.org/abs/2610.00108v1
claim: "Definition 2.1 defines Italian dominating functions, Definition 1.1 defines their weight-count polynomial, Corollary 3.2 gives the cycle deficit constraint, and Section 9 asks for a total-count recurrence and explicit general-deficit coefficient formulas on cycles."
strata_touched:
  - D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence
  - D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords
  - D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps
  - D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit
license: citation-only
triage: anchor
---

# Counting Weight-k Italian Dominating Sets on Trees and Cycles

Pingping Shao and Chengye Zhao, arXiv:2610.00108v1.

Section 2.1 (p. 5):

> A cycle graph C_n (n ≥ 3) has vertices v_1, v_2, …, v_n and edges v_i v_{i+1} for i = 1, …, n − 1 plus the edge v_n v_1.

Definition 2.1 (p. 5):

> An Italian dominating function (IDF) on G = (V, E) is a function f : V → {0, 1, 2} such that for every v ∈ V with f(v) = 0, Σ_{u∈N(v)} f(u) ≥ 2. The weight of f is ω(f) = Σ_{v∈V} f(v).

Definition 1.1 (p. 3):

> where d_I(G, k) counts the Italian dominating functions of weight k.

Section 9 starts on p. 28; the recurrence bullet is on p. 29:

> Several directions remain open for future work: … • Deriving a complete linear recurrence for the total count Σ_k d_I(C_n, k) using the transfer matrix formulation (the observed limiting ratio ≈ 2.7843 is the dominant eigenvalue of the corresponding transfer matrix).

The ellipsis omits a separate direction about broader graph classes. The total
counts labelled functions; it does not quotient them by rotation or reflection.
The cycle encoding uses `Fin n`, cyclic successor `finRotate n`, and its inverse
as predecessor. For `n ≥ 3` these are the two distinct neighbours, and the local
inequality is exactly Definition 2.1. Partitioning functions by their weight
gives the total sum of the weight counts.

The recurrence with coefficients `(2, 2, 1, −1, −1)` and initial values
`(23, 60, 167, 467, 1297)` is proved in
`D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.result`.
Minimal order, the dominant root, the weighted polynomial recurrence,
unimodality and general near-maximum-weight closed forms are outside that
statement.

## Cycle coefficient formula

Corollary 3.2 (p. 7):

> For the cycle C_n (n ≥ 3), a vector y ∈ {0,1,2}^n corresponds to an IDF of weight 2n−j if and only if ∑_{i=1}^n y_i=j and
>
> y_i = 2 ⟹ y_{i−1} + y_{i+1} ≤ 2 (indices modulo n).

Section 9, fourth future-work bullet (p. 29):

> Deriving explicit closed forms for d_I(C_n,2n−j) for general j via the exclusion-counting method of Theorem 7.1 (the polynomiality of these coefficients in n is already established in Lemma 3.4).

The coefficient count uses the same labelled functions. It separates zero-free
deficit words, words whose zero gaps are all `[2,2]`, and words with at least
one ordinary gap. Marking a zero or a one counts labelled vertices, including
those of periodic words. The same finite subtype at weight zero extends the
coefficient count to the endpoint of the deficit range.

## Verified locator

DOI: 10.48550/arXiv.2610.00108

Source: https://arxiv.org/abs/2610.00108v1

- DOI: https://doi.org/10.48550/arXiv.2610.00108
- URL: https://arxiv.org/abs/2610.00108v1
- Definitions 1.1 and 2.1, §2.1, and §9 of the v1 PDF.
