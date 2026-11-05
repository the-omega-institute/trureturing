---
slug: baricz-ponnusamy-2013-bessel-product-order-log-convexity
bibkey: bariczponnusamy2013turan
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Analytic/BesselProductOrderLogConvexity/Result.result
url: https://arxiv.org/abs/1010.3346
---

# Refutation of order log-convexity for the modified Bessel product

## Problem

Á. Baricz and S. Ponnusamy, *On Turán type inequalities for modified
Bessel functions*, Proc. Amer. Math. Soc. 141(2) (2013), 523–532,
arXiv:1010.3346v1, final Conjecture in §3, printed p. 7:

> Motivated by Theorems 1 and 2 we conjecture the following.
>
> Conjecture. The function ν ↦ I_ν(u)K_ν(u) is log-convex on (−1, ∞) for all u > 0 fixed.

### Formal reading

Lean names below have prefix
`D5.S3.Analytic.BesselProductOrderLogConvexity.Result`, except the reused
first-kind function.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| First-kind modified Bessel function | `D5.S3.Analytic.BesselRatioLogConcavity.Result.besselI` | Existing standard Gamma-denominator power series. |
| Second-kind function at noninteger orders | `besselK` | Standard connection formula DLMF 10.27.4 using the reused first-kind function. |
| Product at fixed positive argument | `P` | The first-kind function times the second-kind function. |
| Necessary three-point inequality | `claim` | Every u>0, ν>−1 and h>0 with ν, ν+h and ν+2h noninteger satisfies P(u,ν)P(u,ν+2h)≥P(u,ν+h)². |
| Refutation | `result` | Exactly ¬ claim. |

For a positive function, convexity of its logarithm implies the midpoint
inequality after exponentiation. Restricting the three orders to
nonintegers gives a weaker assertion than the conjecture, where the
connection formula defines the standard second-kind function. Refuting
this weaker assertion therefore refutes the conjecture.

## Motivation

The settling declaration is
`D5/S3/Analytic/BesselProductOrderLogConvexity/Result.result`.
The source note is `D5/L/Asymptotics/bariczponnusamy2013turan`.
The paper distinguishes order ν from its square-root parametrization.
The latter's log-convexity does not imply log-convexity in ν itself.

## Gap

The universal order log-convexity assertion is false. The witness is
u=1, ν=−1/2, h=1, so all three orders −1/2, 1/2 and 3/2 are noninteger
and lie in (−1,∞). The obstruction is already a strict reversal of the
necessary midpoint product inequality.

## Route

Writing $c=\sqrt{2/\pi}$, the standard first-kind series gives at u=1

$$I_{-1/2}(1)=c\cosh 1,\qquad I_{1/2}(1)=c\sinh 1,$$
$$I_{3/2}(1)=c(\cosh 1-\sinh 1),\qquad
I_{-3/2}(1)=c(\sinh 1-\cosh 1).$$

The connection formula and the half-integer sine values then give

$$P(1,-1/2)=\frac{1+t}{2},\qquad
P(1,1/2)=\frac{1-t}{2},\qquad P(1,3/2)=2t,\qquad t=e^{-2}.$$

Thus the desired product difference is

$$D(t)=(1+t)t-\frac{(1-t)^2}{4}
=\frac{3t^2+6t-1}{4}.$$

On [0,1] this polynomial is increasing. A rational lower bound on e
gives a rational upper bound on t at which D is strictly negative.

## Falsifier

One positive argument and one admissible noninteger three-point triple
with a strict reversal contradict `claim`. An error in the first-kind
series correspondence, the second-kind connection formula, the
half-integer evaluations or the exponential estimate would invalidate
the refutation.

## Evidence

**PROVED.** `D5.S3.Analytic.BesselProductOrderLogConvexity.Result.result`
states `¬ claim` without additional hypotheses, with the witness u=1,
ν=−1/2 and h=1.

The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/1a480495e8de4f8a2a96d22500bc5d3ee4cb9d7a/experiments/baricz-ponnusamy-bessel-product)
contains the following two independent numerical artifacts.

- **COMPUTED.** `python3 bp-cert.py`, exit code 0; script `bp-cert.py`,
  SHA-256 `e550af958da7502fb7aed5356ca5880b4863f6a3ed312ee166e35f6fba0ebf40`.
  Exact rational arithmetic, starting from the lower bound
  e>2718281828/10⁹, gives t<0.13533528328232172 and
  D(t)≤D((10⁹/2718281828)²)<0. The displayed upper value of D is
  approximately −0.03326034590068771. The certificate verifies the
  rational sign; the lower bound on e and the function evaluations are
  mathematical inputs to that standalone certificate.
- **COMPUTED.** `python3 bp-scan.py`, exit code 0; script `bp-scan.py`,
  SHA-256 `63f301312fd0c1e1c6215fa604e4a2af3b06f0978743c601b6a96f874f030124`.
  With mpmath dps 40, the half-integer product difference is positive at
  u∈{0.1,0.5} and negative at u∈{1,2,3,5,10}. The corresponding values
  are approximately 2.19859, 0.025717795, −0.033260346,
  −0.0098751548, −0.0027649673, −0.00039800239 and −0.000024999978.
  The closed forms agree with mpmath's besseli·besselk at those seven
  arguments, with summed absolute discrepancies at most 1.33×10⁻³⁹.
  At u=1 the triple (0,1/2,1) also fails midpoint log-convexity: its
  logarithmic gap is approximately −0.03033. This scan additionally
  evaluates endpoint pairs (−0.99,−0.9), (−0.98,−0.8), (−0.95,−0.5),
  (−0.9,0), (−0.5,0.5), (0,1), at
  u∈{0.001,0.01,0.1,0.3,1}; these are finite observations.

The supplied literature scope includes ten Semantic Scholar citing
works, related papers arXiv:1301.5429, 1401.1430 and 1507.01104,
and the supplied repository, Formal Conjectures and conjectures.io
checks. No settlement was found in that scope. The OpenAlex citation
listing was unavailable in the supplied check. This bounded scope does
not establish exhaustive coverage or priority.

## Triage

### What the settlement shows

- **PROVED.** The conjecture fails already at u=1 and orders
  −1/2, 1/2 and 3/2:
  `D5.S3.Analytic.BesselProductOrderLogConvexity.Result.result`.
  The strict midpoint obstruction concerns log-convexity in the order
  itself. Theorem 1(4), printed p. 4, concerns log-convexity of
  ν↦I_{√ν}(u)K_{√ν}(u) on (0,∞); this different assertion is not
  contradicted by the negative-order witness.
- **COMPUTED.** The sign changes across the seven tested arguments and
  the failure at the triple (0,1/2,1) have the commands, exact tested
  scopes and script identities in Evidence. These finite tests do not
  determine an interval of log-convexity or a classification in u.
- **PROVED in prose.**
  Theorem 2's equation (19), printed p. 6, is also contradicted at its
  permitted endpoint ν=1/2, u=1. Its left-minus-right difference is
  $2P(1,1/2)-P(1,-1/2)-P(1,3/2)=(1-7e^{-2})/2>0$.
  Indeed e>2718281828/10⁹>27/10 implies e²>729/100>7.
  This explanatory algebra is not a separate Lean theorem. The
  decreasing-in-order assertion of Theorem 2 is not contradicted by
  this triple, whose three values strictly decrease. No stronger
  conclusion about that monotonicity assertion follows here.
- **OPEN.** The exact set of positive arguments u for which the
  conjectured log-convexity on (−1,∞) holds is not determined.
  Neither the square-root assertion nor monotonicity in order supplies
  the missing midpoint product inequality in the original order.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The supplied bibliographic search is bounded; no new
network search is asserted. The source paper's DOI is not verified from
the supplied text; arXiv:1010.3346 is the verified locator. The finite
mpmath scan is not a uniform proof on any continuous parameter region.
The discussion of Theorem 2's equation (19) is an algebraic consequence
of the displayed evaluations, rather than an additional formal theorem.
