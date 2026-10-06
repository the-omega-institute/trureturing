---
slug: sobolewski-ulas-binary-hankel-minus-two
bibkey: sobolewski2026hankel
doi: 10.48550/arXiv.2607.09376
url: https://arxiv.org/abs/2607.09376v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel.result
---

# Nonvanishing Indices of the Binary Digit Hankel Determinants at t = −2

## Problem

Bartosz Sobolewski and Maciej Ulas, *Hankel determinants of weighted binary sums of digits*, arXiv:2607.09376v1,
Section 5.1, the case d = 2 of Conjecture 5.7, stated in the sentence following it. For u = Σ_j ε_j 2^j with binary
digits ε_j put S(u,t) = Σ_j ε_j t^j and H(n,t) = det[S(i+j,t)]_{0≤i,j<n}; let n_k = ⌈2^{k+2}/3⌉, so that
n_k = 2, 3, 6, 11, 22, 43, …. The statement is that for every n ≥ 2, H(n,−2) ≠ 0 if and only if
n ∈ {n_k − 1, n_k, n_k + 1} for some k ≥ 0.

## Motivation

The theorem `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel.result` establishes the equivalence for every n ≥ 2.

## Gap

Pre-registration issue 12663 records the literature screen. The paper proves the vanishing on a structured set
(Theorem 5.4) and a family of nonzero indices (Theorem 5.10), and states that the difficulty lies in the
nonvanishing outside that set. The arXiv record has a single version; web and GitHub searches found no proof. This is
a bounded negative finding.

## Route

1. Sparse kernel vectors with a binary carry pattern show that H(n,−2) = 0 at every index strictly between the
   triples.
2. A binary-carry conjugation of determinant one reduces the Hankel matrix to a sparse block form; paired
   elimination gives reflection recurrences that relate H at the triple around n_k to the triple around n_{k−1},
   through an auxiliary bordered determinant.
3. A simultaneous induction shows that the auxiliary determinants at the two ends vanish, so no cancellation occurs
   in the recurrences, and evaluates H at all three members of every triple as explicit signed powers of two.

## Falsifier

The statement would fail if some recurrence coefficient vanished, or if an auxiliary determinant at an endpoint
were nonzero for some k so that cancellation became possible.

## Evidence

An independent referee implementation computed H(n,−2) by exact integer determinants for n ≤ 200 and checked every
intermediate lemma of the proof.

## Triage

`theorem`; the statement is the case d = 2 of Conjecture 5.7 of arXiv:2607.09376v1, quantified over every n ≥ 2.

- Proved (formalized): H(n,−2) ≠ 0 exactly at the indices n_k − 1, n_k, n_k + 1, with the values at these indices
  given as explicit signed powers of two.
- Open: the general case d ≥ 2 of Conjecture 5.7, that H(n,2ζ) = 0 exactly on A_d for every primitive d-th root of
  unity ζ.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, web and GitHub searches and the repository checks.
