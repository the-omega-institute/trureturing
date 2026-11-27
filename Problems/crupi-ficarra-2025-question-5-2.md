---
slug: crupi-ficarra-2025-question-5-2
bibkey: crupificarra2025blockingsemiovals
doi: 10.48550/arXiv.2507.05037
url: https://arxiv.org/abs/2507.05037v2
triage: theorem
motivation_gids:
  - D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.result
---

# Crupi–Ficarra Open Question 5.2

## Problem

Marilena Crupi and Antonino Ficarra ask in *Generalizing blocking semiovals in finite projective planes*, arXiv:2507.05037v2, p. 12:

> Are there blocking sets with the r∞-property of size k > 3(q−1) in PG(2, q) with q ≥ 5?

[Open Question 5.2](https://arxiv.org/pdf/2507.05037v2#page=12)

Definition 2.1 and its minimality clause. [p. 4](https://arxiv.org/pdf/2507.05037v2#page=4)

**Projective blocking sets**

> A blocking set of PG(2, q) is a set of points B which meets every line but does not contain any line.

**Minimality**

> A blocking set B of PG(2, q) (AG(2, q), respectively) is called minimal if no proper subset of B is a blocking set of PG(2, q) (AG(2, q), respectively).

Tangent and secant. [p. 4](https://arxiv.org/pdf/2507.05037v2#page=4)

> A tangent to K is a line which intersects K in only one point. A secant to K is a line which intersects K in more than one point.

Definition 3.1. [p. 5](https://arxiv.org/pdf/2507.05037v2#page=5)

> Let B be a blocking set in PG(2, q). We say that B has the r∞-property with respect to P ∈ B if there exists through P only one tangent to B, called r∞, and the other lines through P are secants to B. If it is not necessary to specify the point P, we say that B has the r∞-property.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| PG(2,q) with q≥5 | A field `F` with `Fintype F` and `5 ≤ Fintype.card F`. Points and line covectors have type `ℙ F (Fin 3 → F)` with Mathlib incidence. |
| Definition 2.1, meets every line | First conjunct of `BlockingSet B`. |
| Definition 2.1, contains no line | Second conjunct of `BlockingSet B`. |
| Definition 3.1, the r∞-property | `RInfinity B` selects `p ∈ B` and a tangent through `p` whose only point in `B` is `p`. Every other line through `p` contains another point of `B`. |
| A set of size k > 3(q−1) | Membership of the maximum in `IsGreatest` supplies a set of that size, and the second conjunct gives the strict inequality. |
| Sharp maximum in the settlement | The upper-bound clause of `IsGreatest` ranges over every set satisfying the two definitions. |

## Motivation

The source note is `D5/L/FiniteGeometry/crupificarra2025blockingsemiovals`.

The settling declaration is `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.result`. The preregistered admission basis is open-problem-resolution for the literal question. [Preregistration #34623](https://github.com/the-omega-institute/trureturing/issues/34623)

## Gap

The source constructs examples up to the threshold and asks for larger sets. The bounded literature screen in the preregistration identified classical unitals above the threshold at square orders and left the all-orders answer unfilled. [Preregistration #34623](https://github.com/the-omega-institute/trureturing/issues/34623)

## Route

In the chart z=1, retain the complement of y=x² and add only the vertical direction P=(0:1:0) at infinity. Vertical lines contain P and q−1 retained affine points. Each nonvertical line y=mx+b contains at least q−2 retained affine points by the root bound for the monic quadratic X²−mX−b, and its point at infinity is omitted. The line at infinity meets the set only at P.

The upper bound uses Mathlib's projective plane counts. The tangent omits q points. Each of the q other lines through the tangency point omits at least one point off the tangent. Those omissions are pairwise distinct because two distinct points determine at most one line. Thus at least 2q of the q²+q+1 points are omitted.

## Falsifier

A qualifying set with more than q²−q+1 points at any finite field order q≥5 would contradict the bound. A failure of either blocking clause, the unique tangent, or the cardinality for the displayed witness would contradict its attainment claim.

## Evidence

The maximum and the strict threshold are proved together in `CrupiFicarra52.result`. The proof reuses the existing affine line incidence, Mathlib projective incidence and counts, and Mathlib's polynomial root bound. [Published settlement for #34623](https://github.com/the-omega-institute/trureturing/issues/34623#issuecomment-7204081150)

## Triage

### What the settlement shows

For every finite field in scope the maximum is q²−q+1, an excess of (q−2)² over the question's threshold. This includes fields of characteristic two and extension fields.

Inclusion-minimality is a separate condition. Deleting any retained affine point leaves a blocking subset of the extremizer because every affine line retains at least two points before deletion and the line at infinity retains P. For the stronger requirement, the Bruen–Thas bound gives at most 12 points at q=5, equal to the threshold there. Hermitian unitals give larger inclusion-minimal examples at square orders q≥9 and have exactly one tangent through each of their points. These are literature consequences outside the Lean endpoint. [Bishnoi–Mattheus–Schillewaert, §1 and Theorem 1.1 at t=1](https://arxiv.org/pdf/1703.07843v3)

## ASSUMED-UNVERIFIED

Exhaustive literature priority and correspondence with the journal text are unverified. The journal body was unavailable. Metadata identifies *Finite Fields and Their Applications* 108 (2025), article 102688, DOI `10.1016/j.ffa.2025.102688`. [Journal DOI](https://doi.org/10.1016/j.ffa.2025.102688) · [Crossref metadata](https://api.crossref.org/works/10.1016/j.ffa.2025.102688)
