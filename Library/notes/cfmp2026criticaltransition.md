---
bibkey: cfmp2026criticaltransition
authors: Francesco Costantino; Roberto Frigerio; Bruno Martelli; Carlo Petronio; Xinrong Zhao; Ke Feng; Huabin Ge; Bobo Hua; Feng Luo; Tian Yang
year: 2026
title: Sources for critical six-valent transition stars and cover-stable realization
doi: null
claim: The cited geometric inputs support the explicitly restricted critical-star construction; the formal result proves its continuous six-occurrence angle estimate without claiming unrestricted CFMP.
license: citation-only
triage: anchor
strata_touched: []
---

# Source map for Sections 31-35 of CFMP_GEOMETRIC_REALIZATION

This note is a source map for the existing theory owner, not a claim of a
published paper or an independently established priority result.

## Primary geometric inputs

Francesco Costantino, Roberto Frigerio, Bruno Martelli and Carlo Petronio,
*Triangulations of 3-manifolds, hyperbolic relative handlebodies, and Dehn
filling*, arXiv:math/0402339, Conjecture 0.8.
https://arxiv.org/abs/math/0402339
The external question concerns geometric realization of the given
triangulation. The present theory retains the strictly hyperideal case
with all boundary components closed and of genus at least two.

Xinrong Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class
of Compact 3-Manifolds with Boundary*, arXiv:2601.15174v2, February 5, 2026.
https://arxiv.org/html/2601.15174v2
https://arxiv.org/abs/2601.15174
Lemma 2.2, Proposition 2.4 and Lemma 3.4 supply the actual six-variable
cosine, genuine length domain and neighbour/opposite monotonicity. Theorem
1.1 is the general minimum-nine result. The source was read as HTML;
no new PDF visual-inspection claim is made in this increment.

Ke Feng, Huabin Ge and Bobo Hua, *Combinatorial Ricci flows and the
hyperbolization of a class of compact 3-manifolds*, Geometry & Topology 26
(2022), 1349-1384, DOI 10.2140/gt.2022.26.1349.
https://arxiv.org/abs/2009.03731

Feng Luo and Tian Yang, *Volume and rigidity of hyperbolic polyhedral
3-manifolds*, arXiv:1404.5365.
https://arxiv.org/abs/1404.5365
These are the existing co-volume and true-geometry rigidity inputs already
assigned in the theory. The new work does not reclassify their theorems as
new results, or use an existence-dependent convergence result to assume
existence of the required metric.

## Exact new ordinary theorem and example

Low/high caps remain 2 and 5/4. Critical degree-six low edges have floor
4/3. Each of their occurrences has at least three high neighbours; at least
four have four high neighbours and a critical opposite. No equality of
different global edge lengths is assumed. Other low and high edges obey
the existing seven/eight and eighteen-degree budgets. The critical bounds
are 4/7 on the lower face, 43/99 at favourable upper occurrences, and
49/sqrt(6534) at the other upper occurrences. The strict mixed budget is
4 acos(43/99)+2 acos(49/sqrt(6534))>2pi, proved by the double-angle identity
and a positive rational square gap 3896615/192119202.

A single face-pairing permutation in the existing eight-tetrahedron
packet is replaced: (1,3)<->(1,0) uses 2310 instead of 1230. The resulting
actual edge degrees are (6,17,25), with one genus-six vertex link. There
are two M tetrahedra, five P4 tetrahedra and one C tetrahedron. The six-degree
star has four favourable occurrences and two P4 endpoints adjoining
seventeen-degree low edges. Complete edge classes and normal circles are
written in the theory; independent finite checks also trace oriented-edge
classes and all vertex-link fans. These checks are not kernel certification.

The intrinsic opposite condition uses its degree class. It therefore
persists through unbranched covers even if global edge identities split.
The connected n-fold cyclic covers have 8n tetrahedra and Euler
characteristic -5n. The fixed maximum degree 25 allows a common lower floor
and hence use of the previously credited local Hessian compactness input.
No explicit numerical Hessian eigenvalue bound is claimed.

## Formal source correspondence

`D5/S3/Geometry/Hyperideal/CriticalTransitionStar.lean` has one public
candidate theorem `critical_transition_star`, paired with its authored
Scribe. Its arbitrary finite occurrence carrier has cardinality six; all
five non-target real coordinates vary on continuous faces. A finite good
subset has at least four members. The conditions are actual coordinate
caps and opposite floors, not cosine bounds or the desired total angles.
The proof consumes the derivative-based owner FourCycleEnvelopes, proves
the new endpoint and double-angle estimates, and aggregates actual arccos
values with an explicit positive two-sided margin.

Pinned mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.
The exact inverse-trigonometric APIs were read in
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean`, notably
arccos_cos, arccos_neg, arccos_le_arccos, arccos_lt_arccos and cos_arccos.
The square-root and finite-sum patterns follow the existing candidate
modules. Repository searches did not locate this exact critical transition
owner in the searched scope. That is a bounded dependency search, not an
exhaustive novelty certificate.

The formal theorem covers the continuous six-occurrence angle estimate only.
The manifold construction, co-volume existence step and cover family remain
ordinary proofs. The full CFMP conjecture and unrestricted minimum-eight case
remain outside the proved restricted hypotheses. The original
independent-opposite-one obstruction is retained without alteration.
