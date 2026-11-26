---
slug: gonzalez-dleon-wachs-question-7-1
bibkey: gonzalezdeleonwachs2026weighted
doi: 10.48550/arXiv.2608.08692
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization
---

# Gonzalez D'Leon–Wachs Question 7.1

## Problem

[Question 7.1, arXiv:2608.08692v2](https://arxiv.org/html/2608.08692v2#S7.Thmtheorem1)

For positive n and finite r greater than two, evaluate equation (7.1) on
the complete graph K_n when the first r color variables equal t and every
other variable is zero. Each connected partition block B has a weak
composition of |B|−1 among the colors. Refinement requires every upper
weight to dominate the sum of the finer weights coordinatewise. The sum
uses the incidence Möbius value from the singleton-zero bottom. A k-block
term has degree n−k in the literal specialization.

## Motivation

The equal-color specialization keeps the lower-interval Möbius data and
forgets the distribution of weight among surviving colors. Equations
(7.3) and (7.4) print a rank-reversed polynomial, which assigns degree
k−1 to those same terms.

## Gap

Earlier work supplies the one-block inverse and a coefficient expression
using Lie symmetric functions (arXiv:1408.5415) and the two-color
evaluation (arXiv:1309.5527). The question asks for an evaluation uniform
in the number of vertices and colors. [Preregistration #33603](https://github.com/the-omega-institute/trureturing/issues/33603)

## Route

Write `P_r(z) = sum_{i=0}^{r-2} binom(r-2,i) z^i/(i+1)!`. Let
`F_{n,r}(t)` denote the literal specialization of (7.1) and `C_{n,r}(s)`
the polynomial in the printed rank-reversed convention. For all n≥1 and
r≥2 the formulas are

```text
F_{n,r}(t) = (n-1)! [z^(n-1)] exp((1-nt)z) / P_r(tz)^n
C_{n,r}(s) = (n-1)! [z^(n-1)] exp((s-n)z) / P_r(z)^n.
```

Both coefficient extractions use formal series over the rational
polynomial ring in the corresponding marker. The denominators have unit
constant term. Coefficient reflection of degree n−1 takes `F` to `C`,
so `C_{n,r}(0) = [t^(n-1)] F_{n,r}(t)`.

Padding with zeros identifies the actual lower intervals of precisely
the countable-color terms that survive specialization. The restriction
to the upper blocks factors each literal lower interval as a dependent
product and factors the bottom incidence Möbius coefficient accordingly.
Summing over the block weights gives a product of one-block sums on
labeled partitions. A k-block element has `binom(k+r-2,k-1)` one-block
extensions. Summing the bottom Möbius recurrence yields the compositional
inverse of the one-block exponential generating function. Vandermonde
factors this inverse as `z exp(z) P_r(z)`. Formal Lagrange–Bürmann
extraction gives both formulas.

## Falsifier

A disagreement with the bottom incidence Möbius value or either
coefficient convention for any admissible n and r falsifies the
corresponding equality. The proof uses literal intervals and polynomial
reflection across degree n−1, including a zero marker.

## Evidence

- Countable-color support and source equality
  `D5/S3/Combinatorics/WeightedBond/CountableColors.sourceSpecialization_eq`.
- Labeled expansion and inverse recurrence
  `D5/S3/Combinatorics/WeightedBond/PartitionExpansion.psiComplete_partition`
  and `D5/S3/Combinatorics/WeightedBond/PartitionExpansion.partition_inverse_recurrence`.
- Factorization
  `D5/S3/Combinatorics/WeightedBond/ExponentialSeries.inverseEGF_factor`.
- Both formulas, reflection and the zero value
  `D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.result`.

## Triage

### What the settlement shows

The result proves Question 7.1 and covers the boundary r=2, where
`P_2=1`. In that case the reversed expression is `(s-n)^(n-1)` and the
literal expression is `(1-nt)^(n-1)`. The reflection identity makes the
rank convention explicit when comparing the formula to (7.3) or (7.4).
The evaluation concerns complete graphs.

## ASSUMED-UNVERIFIED

The bounded literature search leaves publication priority unverified.
The thesis and the work described as in preparation were unavailable
in the preregistration search.
