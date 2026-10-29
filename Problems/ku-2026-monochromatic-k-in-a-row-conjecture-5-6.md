---
slug: ku-2026-monochromatic-k-in-a-row-conjecture-5-6
bibkey: ku2026monochromatic
doi: null
url: https://arxiv.org/html/2606.12880v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/KuNearLineRefutation.result
---

# Ku's maximum-density conjecture for ordinary hypercubes

## Problem

Kuo-Han Ku, *Monochromatic k in a row*, arXiv:2606.12880v1,
section 5.1.2, states:

> Conjecture 5.6. For every $k\in\mathbb{N}_{\geq 2}$ and $d\in\mathbb{N}$, $D(k,[k]^d)=1-\frac{2}{k}$.

Definitions 2.2, 2.4 and 2.6 fix the ordinary board
$[k]^d=\{1,\ldots,k\}^d$, all full signed integer lines, near-line
avoidance, inclusion-maximal saturation, and the maximum saturated density.
This universal assertion is refuted at $k=3,d=3$.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| Every integer $k\geq2$ and natural dimension $d$ | `KuGeometry.claim` quantifies over natural `k`, the hypothesis $2\leq k$, and every natural `d`. |
| Ordinary points in $\{1,\ldots,k\}^d$ | `Board k d` is `Fin d → Fin k`; a label is interpreted as its natural value plus one in the integers. |
| Every full line $p+tv$, $0\leq t<k$, $0\ne v\in\{-1,0,1\}^d$, inside the board | `GValid` quantifies over every signed nonzero direction and every parameter and coordinate; `GOn` gives literal integer incidence. |
| No $(k-1)$-subset of a line is selected | `GSourceConfig`; `gsource_config_iff` identifies it with `GConfig` for $k\geq2$. |
| Saturated means maximal under inclusion | `GSaturated`: a containing configuration must equal the original one. |
| $D$ is the attained maximum of $|S|/k^d$ over saturated configurations | `density_maximum_attained` supplies a saturated cardinality maximizer; `density` divides its cardinality by $(k:\mathbb{R})^d$. The denominator is positive for $k\geq2$. |
| The claimed equality is $D=1-2/k$ | `claim` has type `Prop`; `result` has type `Not claim`. |
| Refuting parameter pair $(3,3)$ | `exact_real_event` states `density 3 3 < (1 : Real)/3`. |

The fixed board has 27 points. `source_config_iff` and `gconfig_33_iff`
connect the pairwise geometric predicate used in the bound to the general
source predicate. Natural dimension zero is allowed by the formal universal
quantifier; the refuting positive dimension three also lies in a convention
that starts natural dimensions at one. No conclusion depends on dimension zero.

## Motivation

The paper's upper-density formula is suggested by configurations that attain
the axis bound for certain parameters. The three-dimensional board shows why
axis constraints alone cannot establish attainment: equality forces additional
Latin-square structure that conflicts with genuine face diagonals.

## Gap

The bounded literature reading on 2026-10-29 found the original assertion in
arXiv v1; the arXiv record lists only v1. The primary HTML has 792385 bytes and
SHA-256 `6bc5cb16b8c6a9a71baf44f17e03c7361257aeba9c5c38ff4c3866283998dcb3`.
[MathDB's exact problem entry](https://mathdb.com/p/375265) displays
"Solutions 0" and "No solutions have been posted yet".
[OpenAlex W7164573657](https://openalex.org/W7164573657) reports zero citations.
A Crossref title query returned unrelated titles and supplied no matching DOI.
These readings contain no matching prior resolution; they do not establish
worldwide priority. General Google search returned a JavaScript redirect page,
and the source-cited master's thesis was not read.

## Route

`config_bound` proves that every ordinary $3^3$ configuration has at most eight
points. Projection onto the first two coordinates is injective, since two points
in a projection fiber lie on an axis line. If nine points existed, projection
would be bijective, giving a function assigning the third coordinate to each
pair of first coordinates. The other two axis directions force its rows and
columns to be permutations: a Latin square of order three.

`latin_diagonal` proves that such a square repeats a value on a main or opposite
diagonal. `diag_common` turns this repetition into two selected points on a
full ordinary face-diagonal line, contrary to the configuration condition.
The contradiction rules out nine points. Applying the bound to the saturated
maximizer defining `density` gives `exact_real_event`, and `result` contradicts
the conjectured value $1-2/3=1/3$.

## Falsifier

A configuration of nine points on this exact ordinary board would contradict
`config_bound`. A mismatch between the source and formal line family, the
saturation order, or maximum-density semantics would invalidate the external
interpretation even if the finite combinatorial theorem remained true.
The statement echo retains all of these conditions. A size-eight construction
is not needed to refute the universal equality.

## Evidence

The mathematical source is
`D5/S3/Combinatorics/Geometry/KuNearLineRefutation.lean`.
`KuGeometry.config_bound` states the universal cardinality upper bound;
`KuGeometry.density_maximum_attained` supplies the actual saturated maximum;
`KuGeometry.exact_real_event` states the strict density inequality;
`KuGeometry.result` is the closed negation of `KuGeometry.claim`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
No numerical experiment or unverified search certificate is needed for the proof.

The reused order-three Latin predicate is
`D5.S3.Combinatorics.LatinEulerianMultiples.IsLatin`, owned by
`D5/S3/Combinatorics/LatinEulerianDefs`; the finite diagonal obstruction is
proved in `KuGeometry.latin_diagonal`.

## Triage

- **Proved, kernel-checked:** every ordinary $3^3$ near-three-line-avoiding
  configuration has cardinality at most eight (`KuGeometry.config_bound`, with
  `gconfig_33_iff` and `source_config_iff` giving the source correspondence).
- **Proved, kernel-checked:** the registered strict inequality
  $D(3,[3]^3)<1/3$ (`KuGeometry.exact_real_event`). Consequently the universally
  quantified Conjecture 5.6 is false (`KuGeometry.result`).
- **Proved mechanism, kernel-checked:** equality at nine would force a Latin
  square by axis projection (`config_bound`); the forced equal-symbol diagonal
  (`latin_diagonal`) produces an ordinary full-line collision (`diag_common`).
  This identifies an obstruction to attaining the axis upper bound, rather
  than changing the board or deleting directions.
- **Open:** the exact value of $D(3,[3]^3)$ and a size-eight saturated attainer.
  The source retained here proves an upper bound and strict inequality only;
  it does not prove $D(3,[3]^3)=8/27$.
- **Open:** determine $D(k,[k]^d)$ for every integer $k\geq2$ and $d\geq1$; in
  particular, classify the pairs where the source's upper bound is attained.
  Restrictions to larger $k$ or $d$, or other repaired equalities, are not
  established by this one refuting pair.
- **Proved in the cited paper, not newly kernel-checked here:** section 5.1.2
  gives a separate $X_k$ construction for $d=2$, and invokes the Lemma 4.1
  construction when $k$ is even and $k/2$ is coprime with $d!$. Those restricted
  source statements do not assume Conjecture 5.6. The refuting pair $k=3,d=3$
  does not satisfy either restriction; no new certification of them is claimed.
- **Literature reading; remaining questions open:** the two occurrences of
  "Conjecture 5.6" in v1 are its statement and the subsequent explanation of
  the independent $d=2$ case. No later theorem is presented as conditional on
  Conjecture 5.6. Section 5.1.1's Conjectures 5.1--5.4 and Question 5.5 concern
  infinite or toric grids. Question 5.7 concerns minimum-density configurations,
  and section 5.2's winner discussion cites a separate pairing strategy.
  Their stated arguments do not use Conjecture 5.6; none is resolved or refuted
  by the maximum-density obstruction here. The universal equality itself is
  the claim withdrawn, without an asserted downstream theorem collapse.

## ASSUMED-UNVERIFIED

The literature screen is bounded by the sources listed in Gap. The master's
thesis and an unrestricted citation corpus were not checked; nondetection is
not an exhaustive novelty claim.

The four-slot audit of `KuGeometry.config_bound` has a validated registration
in `Reg/D5/S3/Combinatorics/Geometry/KuNearLineRefutation.lean` with an unknown
continuation. The eleven other public audit targets remain unfinished as
individually specified in the
[linked audit boundary](https://github.com/the-omega-institute/trureturing/issues/23487#issuecomment-6487318842).
The designated negation `KuGeometry.result` is exempt. This audit boundary does
not supply or replace any part of the mathematical counterexample proof.
