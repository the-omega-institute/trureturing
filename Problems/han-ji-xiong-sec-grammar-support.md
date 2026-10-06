---
slug: han-ji-xiong-sec-grammar-support
bibkey: han2026qgrammar
doi: 10.48550/arXiv.2604.23959
url: https://arxiv.org/abs/2604.23959v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/QGrammar/SecGrammar.result
---

# The Number of Distinct Terms of the q-Derivatives of y₀ in the Grammar G_Sec

## Problem

Guo-Niu Han, Kathy Q. Ji and Huan Xiong, *q-Derivative Grammar*, arXiv:2604.23959v2, Appendix III, Conjecture III.7.
The grammar G_Sec has rules x_j ↦ q^j(1 + x_j x_{j+1}) and y_j ↦ q^j y_j x_{j+1}, and its order sorts the variables
of a word by descending index, x before y at equal index. The q-derivative is
D(w₁⋯wₙ) = Σ_j ρ(w₁⋯w_{j−1} R(w_j) ↑(w_{j+1}⋯wₙ)), where ↑ raises every index by one, extended linearly. With Ω(E) the
number of distinct words of E with nonzero coefficient, the conjecture states Ω(Dⁿ(y₀)) = 1 for n = 1, 3 for n = 2,
(20k³ + 33k² + k − 6)/6 for n = 2k + 1 with k ≥ 1, and (20k − 17)(k + 1)k/6 for n = 2k with k ≥ 2.

## Motivation

The theorem `D5/S3/Combinatorics/QGrammar/SecGrammar.result` establishes the formula for every n ≥ 1.

## Gap

Pre-registration issue 12835 records the literature screen: the paper lists the initial values and states the
formula as a conjecture, and its citing paper arXiv:2607.17130 does not treat the grammar G_Sec. This is a bounded
negative finding.

## Route

1. Every coefficient of Dⁿ(y₀) is a nonzero polynomial in q with nonnegative coefficients, so no cancellation occurs
   and the support of the next derivative is the set of normalized successors of the support.
2. Every word of Dⁿ(y₀) contains exactly one y, and its indices lie in a strip of width at most one; such words are
   encoded by small integer tuples in two families.
3. The derivative acts on these tuples by explicit transitions; the set of tuples reachable at step n is an explicit
   region, established by an invariant for inclusion and explicit predecessors for every tuple of the region.
4. Counting the region gives the stated quasipolynomial.

## Falsifier

The statement would fail if two different derivative histories cancelled a word, or if some tuple of the region had
no predecessor at the previous step.

## Evidence

An independent referee implementation computed the supports from the definitions for every n ≤ 26 and checked the
region in both directions and every transition on the computed data; the counts at n = 25, 26 are 6553 and 7371.

## Triage

`theorem`; the statement is Conjecture III.7 of arXiv:2604.23959v2, quantified over every n ≥ 1.

- Proved (formalized): the support of Dⁿ(y₀) is exactly the region described above, and its size is the stated
  quasipolynomial.
- Open: the companion sequence for the grammar G_Sec′ of the same appendix, which the paper records as data without a
  conjectured formula.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, its citing paper arXiv:2607.17130, web and GitHub searches and
the repository checks.
