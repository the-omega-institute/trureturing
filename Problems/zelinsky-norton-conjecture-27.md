---
slug: zelinsky-norton-conjecture-27
bibkey: zelinsky2023nondeficient
doi: null
url: https://math.colgate.edu/~integers/x13/x13.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27.result
---

# Eventual growth of every Norton threshold first difference

## Problem

Zelinsky, Integers 23 (2023), article A13, page 13:

> Conjecture 27. For any α > 1, and C > 0, for sufficiently large n
> one has a_α(n+1) > a_α(n) + C.

Let p_n denote the n-th prime, p_1=2, and let a_α(n) be the least k≥1
for which the product of p_r/(p_r−1), over n≤r≤n+k−1, strictly exceeds α.
The target quantifiers are

$$
\forall\alpha>1\ \forall C>0\ \exists N\ge1\ \forall n\ge N,
\quad a_\alpha(n+1)>a_\alpha(n)+C.
$$

Here α and C are real, and the natural threshold values are cast to the
reals in this displayed inequality. The bound N may depend on both.

## Motivation

The threshold length removes one initial prime factor when n advances.
Replacing its lost logarithmic mass requires an increasing number of much
smaller increments near the terminal prime.

## Gap

An endpoint estimate with a fixed power error does not control the local
difference for all α>1. The endpoint must be localized up to multiplicative
constants, and first-crossing errors must be negligible beside 1/p_n.

## Route

The following is a paper derivation for each fixed α>1. Put P=p_n,
s_n=n+a_α(n)−1 and Q_n=p_{s_n}. With w(q)=log(q/(q−1)),

$$
\sum_{j=n}^{s_n}w(p_j)=\log\alpha+\varepsilon_n,\qquad
0<\varepsilon_n\le w(Q_n).
$$

The exact Mertens E_3 prefix identity and E_3(x)=O(1/log x) give

$$
\log Q_n=\alpha\log P+O(1),\qquad Q_n\asymp P^\alpha.
$$

The constants may depend on α. For sufficiently large n, the old excess
is smaller than half the removed initial weight. The difference of the
two terminal prefix masses is therefore positive, so the next endpoint
is later. Subtraction of the two crossing sums yields

$$
\sum_{j=s_n+1}^{s_{n+1}}w(p_j)
 =w(P)+\varepsilon_{n+1}-\varepsilon_n.
$$

Since α>1, the excess bound O(P⁻α)=o(1/P) makes the right side comparable
to 1/P. Consecutive starting primes are comparable by Bertrand's bound.
Both endpoints, and every prime in the added interval, are therefore
comparable to P^α; each new summand is comparable to P⁻α. It follows that

$$
1+a_\alpha(n+1)-a_\alpha(n)\asymp P^{\alpha-1}.
$$

The positive power P^{α−1} tends to infinity. Given any real C>0, the
eventual lower comparison exceeds C+1 and gives the required strict
inequality with the original threshold values.

## Falsifier

The condition α>1 is essential to the negligible-excess comparison and
to divergence of P^{α−1}. The argument fixes α before choosing constants;
it does not assert a uniform threshold as α decreases to 1. A bound for
a_α(n) alone cannot be subtracted as if its unrelated errors cancelled.

## Evidence

Preregistration #32081 and the source quotations are attributed to the
dispatcher. The dispatcher's bounded literature check covered the following
sources and results; no independent PDF or network verification was performed
in this repair:

- arXiv:2505.08160 has only v2 in the checked record; Question 6 remains
  stated there.
- Zelinsky (2021), Propositions 2 and 3, proves a(n+1)≥a(n)+1 and divergence
  of the first difference. These propositions give neither a leading
  asymptotic term nor a count of the attained values.
- Zelinsky (2023) poses the general threshold problem again and lists
  Conjecture 27.
- Norton (1961), *Acta Arithmetica* 6, 365–374, Theorem 4, gives asymptotics
  for a(n) and its terminal prime, but no adjacent-difference theorem.
- The repository search found no pre-existing dossier for these questions.

This bounded check reported no prior settlement of the three exact targets.
Independent verification of the issue and source PDFs, exhaustive literature
coverage and worldwide priority remain unverified.

`ZelinskyNortonConjecture27.result` proves in Lean that for every real
α>1 and every real C>0, eventually
`(aAlpha α n : ℝ) + C < (aAlpha α (n + 1) : ℝ)`.
The threshold may depend on both α and C.

`norton_endpoint_bounds` proves Q_n≍p_n^α using `Mertens.E₃.abs_le`
and the exact prime-log prefix identity.
`norton_adjacent_cancellation` proves the lower comparison
1+a_α(n+1)−a_α(n)≥c p_n^{α−1} eventually for some c>0.
Its proof cancels the common prefix and bounds the mass of the added
interval above by its number of terms times 2/Q_n. Positive-power
divergence then gives the stated strict inequality for every C>0.
The result and both public helpers have axiom closure contained in
`propext`, `Classical.choice` and `Quot.sound`.

## Triage

- **Proved in Lean:** `ZelinskyNortonConjecture27.result` proves the
  conjecture with its full real α>1 and C>0 quantifiers.
- **Proved in Lean:** endpoint localization Q_n≍p_n^α and exact adjacent
  cancellation give the lower bound
  1+a_α(n+1)−a_α(n)≥c p_n^{α−1} eventually, which is sufficient for
  the conclusion for every fixed α>1.
- **Paper derivation, not separately formalized:** the stronger two-sided
  order is 1+a_α(n+1)−a_α(n)≍p_n^{α−1}. Its upper bound is unnecessary
  for the proved eventual growth.
- **Paper derivation, not formalized:** for α=2 the sharper prediction is
  a(n+1)−a(n)∼p_n. The order estimate alone does not establish this constant.
- **Computed, floating point:** the α=2 readings of Δ(n)/p_n are
  1.387,1.124,1.055,1.056,1.048,1.024 at n=11,51,101,201,401,801.
  The [threshold-separation dossier](norton-threshold-differences.md)
  specifies the sieve and strict-prefix method. No numerical test of a
  varying α or uniformity as α approaches one is asserted.
- **Paper derivation:** at α=1 every a_1(n)=1, so the corresponding
  positive-difference conclusion fails. No uniform extension through α=1
  is claimed.
- **Unresolved:** uniform estimates with a varying α=α(n) approaching 1
  need quantitative control beyond constants depending on fixed α.
- **Unverified:** no independently checked source dependency scan is
  available, so no other source theorem is claimed to change.

## ASSUMED-UNVERIFIED

The fixed source statement and bounded literature findings are attributed
to the dispatcher. Independent source verification and worldwide priority
remain unverified. Two-sided and leading-constant asymptotics remain paper
conclusions, distinct from the proved Lean growth statement.
