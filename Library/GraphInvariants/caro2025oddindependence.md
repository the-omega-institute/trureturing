---
bibkey: caro2025oddindependence
authors: Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza
year: 2025
title: "The odd independence number of graphs, I: Foundations and classical classes"
doi: 10.48550/arXiv.2509.20763
url: https://arxiv.org/abs/2509.20763v2
claim: "Problem 40, final question, asks whether alpha_od(Q_d)/2^d tends to one half as d tends to infinity through even integers. Odd independence permits zero or an odd number of neighbours in the independent set at every external vertex."
strata_touched:
  - D5/S3/Combinatorics/Graph/HypercubeOddIndependence
license: citation-only
triage: anchor
---

# Odd independence of Boolean hypercubes

The source is arXiv:2509.20763v2, Section 8, Problem 40. The final question is:

> In particular, is it true that if d is even, then
> lim_{d→∞} alpha_od(Q_d)/2^d = 1/2?

Here Q_d has all binary words of length d as vertices and an edge exactly at
Hamming distance one. An odd independent set S is independent and every vertex
outside S has either zero or an odd number of neighbours in S. The invariant
alpha_od is the maximum cardinality of such a set. Corollary 27 and Proposition
28 provide partial bounds; the final asymptotic question is distinct from the
preceding request for exact values in every even dimension.

The Lean statement uses the real epsilon definition of the limit: for every
positive real epsilon there is a natural D such that the absolute difference
from one half is below epsilon for every even d at least D. The maximum is
bounded by the actual number of vertices and is attained, including dimension
zero. The proof of the limit only uses positive dimensions.

The binary syndrome map and its one-coordinate update rule use the classical
parity-check construction described in Daniel J. Kleitman's MIT 18.310 notes,
[Matrix Hamming Codes, Sections 9.1–9.3](https://math.mit.edu/~djk/18.310/Lecture-Notes/matrix_hamming_codes_2007.html).
They are coding-theoretic ingredients. The hypercube argument indexes coordinates
by every binary check label once, including zero, and repeats zero an even number
of additional times. No perfect-code property on the whole extended cube is
assumed. Every external-neighbour count is proved directly from the check labels.

The all-even-tail construction deletes a smallest syndrome class from the even
parity class. For every positive k and every even d at least 2^k it yields an odd
independent set of size at least

    2^d * (1/2 - 1/(2 * 2^k)).

This is a sufficient lower bound for the asymptotic question. It supplies neither
an exact formula for the finite maximum nor a classification of maximizers.
