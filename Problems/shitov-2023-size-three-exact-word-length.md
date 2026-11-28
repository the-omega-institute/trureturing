---
slug: shitov-2023-size-three-exact-word-length
bibkey: shitov2023growthmatrixalgebras
doi: 10.1007/s00023-026-01728-6
url: https://vixra.org/pdf/2308.0028v1.pdf
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.iterate_posDef_of_wordSpan_eq_top
---

# Shitov, Question 2 in size three

## Problem

> Question 2. For any positive integer \(n\), what is the smallest value \(w(n)\) such that, if \(S^k\,\mathbb C=\operatorname{Mat}_n(\mathbb C)\) for some \(S\) and \(k\), then also \(S^{w(n)}\,\mathbb C=\operatorname{Mat}_n(\mathbb C)\)?

For \(n=3\), determine the least positive \(k\) such that every subset \(S\) of \(M_3(\mathbb C)\) with full complex span at some positive exact word length also has full span at exact length \(k\). [Remark 1 and Question 2, p. 1](https://vixra.org/pdf/2308.0028v1.pdf#page=1)

## Motivation

Fullness of an exact word span measures the injectivity length of a generating family. For a finite Kraus family it also implies strict positivity of the corresponding iterate, as expressed by the cited motivation theorem.

## Gap

Yu's pair gives a lower bound of seven at size three. The universal upper bound must cover arbitrary generator sets, including sets whose entire linear span consists of singular matrices. [Yu v1, Theorem 1.2 and Remark 6.2](https://zenodo.org/records/24562446/files/wielandt_lower_bound.pdf)

## Route

Pass from the exact words over the set to powers of its complex span. If the span contains an invertible generator, use strict dimension growth and the rank-one return analysis. Otherwise use the alternating or compression form of a reduced singular space of size three. Use persistence to exclude all lengths below seven from Yu's proper sixth span and full seventh span.

## Falsifier

An eventually full set with a proper seventh span would refute universality. A universal positive length below seven would force Yu's sixth span to be full.

## Evidence

The proof of `ShitovSizeThree.result` combines the universal upper bound with Yu's published sharpness witness. The six-letter obstruction and seven-letter basis are certified by integer matrix identities. The statement uses ordered products indexed by `Fin k` and quantifies over `Set (Matrix (Fin 3) (Fin 3) ℂ)`. [Preregistered statement and literature screen](https://github.com/the-omega-institute/trureturing/issues/35111)

## Triage

The complex size-three value is seven. The invertible and singular branches also establish the same upper bound over infinite fields of characteristic different from two. Yu's size-three witness works over every field. The general value of \(w(n)\) for \(n\ge 4\) is outside this result.

## ASSUMED-UNVERIFIED

The journal full-text wording of Question 2 and literature priority beyond the sources checked in the preregistration remain unverified. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/35111)
