---
bibkey: cfmp2026eighttriangle
authors: trureturing contributors
year: 2026
title: Adjacent degree-eight packets for CFMP geometric realization
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/new
claim: A strict hyper-ideal realization theorem for valence-eight or valence-at-least-sixteen triangulations whose local degree-eight edge packets are three-stars, three-cycles, or four-cycles.
license: citation-only
triage: anchor
strata_touched: []
---

This note records the scoped theorem in
docs/develop/theory/CFMP_EIGHT_TRIANGLE_CLUSTERS.md.

The genuinely new incidence class is a tetrahedron with exactly three
degree-eight local edges, each adjacent to the other two. Relative to a chosen
degree-eight target edge, the two low neighbours are adjacent; the possible
three-star and three-cycle endpoint substitutions are

- lower: 73/100 and 8*sqrt(6)/27;
- upper: 121/175 and 13*sqrt(41)/123.

The four-cycle values are 293/400 and 473/700. All lower squares exceed 1/2
and all upper squares are below 1/2. For high edges, the conservative endpoint
is 23/25 < cos(pi/8), so degree at least 16 supplies the strict upper budget.

The proof minimizes the actual shared-edge co-volume on one compact global
length box. It does not assume a zero-curvature metric or use Ricci-flow
convergence as an existence premise. Zhao's six-variable formula,
monotonicity and genuine length-domain criterion, and Luo--Yang's co-volume
gradient are external inputs. Costantino--Frigerio--Martelli--Petronio
Conjecture 0.8 is the original geometric-realization problem:
https://arxiv.org/abs/math/0402339

Scope is intentionally narrow: no arbitrary minimum-eight triangulation, no
minimum-six theorem, no partially truncated boundary case, and no claim that
the cited endpoint theorem alone formalizes manifold links or co-volume.
