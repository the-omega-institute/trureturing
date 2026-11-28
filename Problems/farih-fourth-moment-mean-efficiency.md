---
slug: farih-fourth-moment-mean-efficiency
bibkey: farih2026meanefficiency
doi: 10.48550/arXiv.2609.15443
url: https://arxiv.org/abs/2609.15443v3
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Stieltjes/FarihFourthMoment.result
---

# Farih’s fourth-moment question at an exact instance

## Problem

Section 10.6 of Badr Farih’s *Sharp Bounds on the Mean Efficiency of a
Fluctuating Machine* asks “whether a fourth moment tightens (30) usefully at
intermediate m₃, and whether the extremal laws remain two-point as the
hierarchy is continued.” In the normalized model, X is nonnegative with mean
one, and the mean efficiency is the expectation of (1 + αX)⁻¹ for α > 0.
[Versioned primary source](https://arxiv.org/html/2609.15443v3)

The registered event asks for a feasible first-four-moment vector at α = 1
with an attained exact maximum, no two-point maximizer, and a strictly
larger achievable mean when the fourth-moment constraint is dropped. An
instance suffices to refute persistence of two-point optimality in general.
[Preregistered issue](https://github.com/the-omega-institute/trureturing/issues/34960) · [Exact event](https://github.com/the-omega-institute/trureturing/issues/34960#issuecomment-7227145477)

### Statement echo

| Registered clause | Lean counterpart |
| --- | --- |
| Normalized nonnegative probability law | `FirstThreeMoments` requires probability and nonnegative support almost everywhere on the real line, plus first raw moment one. |
| Feasible vector at α = 1 | `FirstFourMoments uniform012` gives the exact vector (1, 5/3, 3, 17/3). Each raw moment includes integrability of its power. |
| Exact attained maximum | The uniform law on {0, 1, 2} has mean efficiency 11/18, and every feasible Borel measure on ℝ has mean efficiency at most 11/18. |
| No two-point maximizer | For every full-class feasible measure and every pair of real points, their union fails to carry the law almost everywhere. This excludes feasibility itself. |
| Strict improvement with three moments | `threeMomentWitness` on {0, 3/2, 3} with weights (10/27, 16/27, 1/27) satisfies the first three constraints and gives 37/60, strictly greater than the efficiency of every four-moment feasible law. |

## Motivation

At variance 2/3 the least admissible third moment in the paper’s model is
25/9. The chosen third moment is 3. The paper’s upper endpoint at this
variance is 5/8, which exceeds 11/18 by 1/72. The explicit relaxed witness
establishes a separate comparison with the attainable values under the
first three moments, with gap 37/60 − 11/18 = 1/180. [Eqs. (13), (28), and (30)](https://arxiv.org/html/2609.15443v3)

## Gap

The exact instance resolves the registered existential event. The general
fourth-moment hierarchy, the exact three-moment optimum, and optimizer
uniqueness are outside the Lean statement. The substitution evaluating the
paper’s endpoint at 5/8 is a rational calculation accompanying the theorem.

## Route

For x ≥ 0 the quartic
Q(x) = (x⁴ − 7x³ + 20x² − 32x + 36)/36
has gap x(x−1)²(x−2)²/[36(1+x)] over the efficiency function. This
identity, the nonnegative gap, and integrability of the efficiency and
quartic give the bound on every feasible law by integral monotonicity.
The quartic integral is fixed at 11/18 by the prescribed moments. The
uniform witness has these moments and its atoms are zeros of the gap.

On an almost-everywhere pair {a,b}, the relation x² = (a+b)x − ab
induces the raw-moment recurrence. With m₀ = m₁ = 1, m₂ = 5/3 and m₃ = 3,
the recurrence forces a+b = 2 and ab = 1/3, so m₄ = 49/9. The required
fourth moment is 17/3. Direct integrals under the relaxed witness give the
first three moments and mean efficiency 37/60.

## Falsifier

A feasible measure exceeding 11/18, a feasible measure concentrated
almost everywhere on a pair of real points, or an incorrect moment or
mean-efficiency value for either stated atomic law would invalidate the
corresponding clause of the settlement.

## Evidence

The settling declaration is
`D5.S3.Analytic.Stieltjes.FarihFourthMoment.result`. Its live private
proofs use the quartic integral estimate, two-point recurrence, and weighted
Dirac integrals. The theorem has generality `I`, utility `none`, and
`proof_shape: content`. Its intended admission basis is
`open-problem-resolution` for the registered exact instance. The quartic
majorant and the pair-moment obstruction are live proof steps over arbitrary
feasible Borel measures. Exact atom calculations construct the two witnesses.
[Confirmed public result](https://github.com/the-omega-institute/trureturing/issues/34960#issuecomment-7227674513)

## Triage

Theorem. The result proves the registered exact instance at α = 1 and
shows that preserving a two-point maximizer is impossible there.

## ASSUMED-UNVERIFIED

The Tier 1 preregistration records a bounded check of arXiv:2609.15443v3,
the citing arXiv:2609.37940v2, the author’s arXiv:2609.24748v1, indexed
MathDB, formal-conjectures, and repository records. That screen found no
settlement in the checked scope. Direct MathDB and some citation-index
requests were unavailable. [Preregistration and search limits](https://github.com/the-omega-institute/trureturing/issues/34960)
