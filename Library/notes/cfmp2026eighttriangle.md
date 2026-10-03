---
bibkey: cfmp2026eighttriangle
authors: trureturing contributors
year: 2026
title: Adjacent degree-eight packets for CFMP geometric realization
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/11483
claim: Paper proof of a strict hyper-ideal realization subcase with degree-eight three-star or three-cycle packets and all other global edges of degree at least twelve.
license: citation-only
triage: anchor
strata_touched: []
---

The paper theorem and reproducible topology certificate are in
`docs/develop/theory/CFMP_EIGHT_TRIANGLE_CLUSTERS.md`. This note does not
assert Lean/kernel verification of the geometric theorem. Isolated
closed numerical inequalities are not retained as a substitute for it.

Use common global cosh-length intervals [5/4,2] on degree-eight edges
and [1+delta,10/7] on all remaining edges. For a low edge in a three-star
or three-cycle, the conservative lower cosine bounds are 73/100 and
8*sqrt(6)/27; upper bounds are 709/1003 and 11*sqrt(249)/249.
Their positive squared values lie strictly above and below 1/2,
respectively. A high edge has a low opposite edge and two high neighbours;
the relaxed six-placement bound is 5965/6972, whose square is less than
3/4 by 875363/48608784. Thus high degree at least 12 gives the strict
upper cone-angle budget. The high lower length face is chosen using the
maximum degree of the finite triangulation.

The proof minimizes the actual shared-edge co-volume on a compact global
length box contained in the nondegenerate domain. Inward derivative signs
exclude a boundary minimum and give zero cone curvature at the interior
minimum. It does not assume a zero-curvature solution. Zhao's exact
six-variable formula, monotonicity and length-domain criterion, and
Luo--Yang's co-volume gradient identity are external inputs. Convexity
is not needed for this existence argument.

A 16-tetrahedron orientable example has degrees 8,8,8,8,8,8,12,36,
all low packets three-stars, circular edge links, and vertex-link genera
2 and 8. The full pairing table and a standalone Python checker are in
the theory document. Face signatures prohibit mixing three-stars and
three-cycles in one connected triangulation. In the all-three-star case,
high degrees are necessarily even; an apparent numerical improvement to
11 alone therefore yields no new combinatorial cases.

The repository's existing four-cycle theorem already has high threshold
12 but has four low local edges, unlike these three-edge packets.
Its broader transition budget in Section 26 has high thresholds 16 or 17.
The compact-box method itself is reused, not claimed as new. Zhao's
minimum-nine theorem does not apply to the original triangulation with
its degree-eight edges; a different subdivision would not by itself
settle realization of the prescribed triangulation.

Primary references:
- Costantino--Frigerio--Martelli--Petronio, Conjecture 0.8 in
  https://arxiv.org/abs/math/0402339; Conjecture 1.8 in the published source
  https://ems.press/content/serial-article-files/43143. The conjecture
  assumes all edge valences at least six and concerns the given triangulation.
- Xinrong Zhao, https://arxiv.org/html/2601.15174v2, Lemma 2.2,
  Proposition 2.4, Lemma 3.4, and Theorem 1.1.
- Feng Luo and Tian Yang, https://arxiv.org/abs/1404.5365.

This is a paper-first scoped result, not a resolution of the full CFMP
conjecture, arbitrary minimum-eight triangulations, or partially truncated
boundary cases. Formalization of the geometric chain remains open.
