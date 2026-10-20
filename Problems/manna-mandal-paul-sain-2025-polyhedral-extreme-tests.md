---
slug: manna-mandal-paul-sain-2025-polyhedral-extreme-tests
bibkey: mannamandalpaulsain2025improvement
doi: null
url: https://arxiv.org/abs/2511.20345v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/BanachGeometry/LinfKNumber.result
---

# Independent extreme-point tests in polyhedral Banach spaces

## Problem

Manna, Mandal, Paul and Sain, *An improvement of the
Blanco-Koldobsky-Turnšek characterization of isometries*, arXiv:2511.20345v1,
final Open Question, S2.p45.1:

> Open Question: In an n-dimensional polyhedral Banach space, does the preservation of Birkhoff-James orthogonality by a bounded linear operator at any n linearly independent extreme points necessarily imply that the operator is a scalar multiple of an isometry?

This dossier anchors only this question. The standing field is real or complex;
local preservation means every direction and every base-field scalar.
The test tuple is chosen independently, rather than requiring preservation
simultaneously at every independent tuple. The conclusion permits any one
common scalar, including zero, and a linear isometry of the same carrier.

## Motivation

The distinction between a spanning test set and the geometry of its normal
cones determines whether local tests force a global isometry. The positive
sup-norm theorem `LinfKNumber.result` shows that independence suffices for
extreme-point bases of cubes. A different polyhedral norm can distinguish
this special case from the universal question.

## Gap

The all-extreme-point and all-k-smooth theorems of arXiv:2504.11161v2 require
larger test sets. Theorem 2.33 of arXiv:2501.02714v1 gives negative examples
on nonpolyhedral $\ell_p$ spaces. Its Corollary 2.29 only gives bijectivity
from the selected tests in a polyhedral plane. The complete bounded
comparisons and source locators are in the
[primary Library note](../Library/Geometry/mannamandalpaulsain2025improvement.md).
They supply no applicable whole resolution in the two inspected full texts,
and make no global absence or priority claim.

## Route

Use the complete real normed plane with

$$
N(a,b)=\max(|a|,|a+b|,|a/2+b|),\qquad
p=(1,0),\quad q=(0,1),\quad r=(-1,3/2),\quad
T(a,b)=(a+b,-3b/2).
$$

The native carrier is the plane $w_2=w_1-w_0/2$ in `Fin 3 → ℝ`, with the
inherited metric and norm. Algebraic coordinates give dimension two;
finite-dimensional completeness and continuity give a Banach space and an
actual bounded endomorphism. This coordinate equivalence does not assert
that the usual product norm is preserved.

The ball is exactly the three slab constraints $|w_i|\le1$. An extreme point
must have at least two active constraints: a nonzero tangent that fixes a
sole active constraint gives a small feasible segment on both sides.
The active pairs put every actual extreme point inside the six-point set
$\{\pm p,\pm q,\pm r\}$, proving finiteness. Two saturated independent
supporting equations prove actual extremality of $p,q$. They are the images
of the standard basis and both have norm one.

For every direction $(a,b)$, input orthogonality at $p$ implies
$a(a+b)\le0$, and at $q$ implies $(a+b)(a/2+b)\le0$.
The output signed products are

$$
(a+b)(a-b/2)=\tfrac32 a(a+b)-\tfrac12(a+b)^2,\qquad
(a+b)(b-a/2)=3(a+b)(a/2+b)-2(a+b)^2.
$$

They remain nonpositive. For each real perturbation scalar, an active signed
facet with nonnegative increment proves the output BJ inequality. Necessity
uses the existing `LinfKNumber.active_not_BJ` finite-coordinate descent proof
at its owning declaration. No direction or scalar is sampled.

If $T=cU$ for a native linear isometry, every norm is multiplied by $|c|$.
But $N(p)=N(r)=N(Tp)=1$ and $N(Tr)=2$, a contradiction.

## Falsifier

The example would fail if the induced carrier or its metric differed from
the specified norm, if the ball's actual extreme set were infinite, if the
selected vectors were dependent or not extreme unit points, if any real
direction violated either full preservation implication, or if some common
scalar and native linear isometry represented $T$. Each of these is an
explicit obligation in the native proof. The claim must retain both source
fields and all dimensions; a norm-ratio statement or a finite-direction
calculation alone would not refute it.

## Evidence

`D5.S3.Analytic.BanachGeometry.PolyhedralBJRefutation.result : ¬ claim`
instantiates the real branch of a literal closed `claim : Prop`, containing
the universal real and complex assertions. It proves the entire native
counterexample without assumed geometry, continuity or preservation premises.
The public data definitions are `fieldClaim`, `claim`, `facetPlane`, `Plane`,
`point`, `coordinates` and `operator`; all other new mathematical lemmas are
private and lie on the resolution's proof path.

The native implementation was prospectively registered in
[issue #19309](https://github.com/the-omega-institute/trureturing/issues/19309).
The earlier ordinary proof was not prospectively registered there.
The admission basis is `open-problem-resolution`; the utility is
`certified-instance` with `refutes` pointing to this claim and result.
The Scribe attaches `OpenProblemResolutionClaim` with `Refuted` to the result.

## Triage

1. **Proved in the native theorem — the original universal assertion is false.**
   The real two-dimensional instance settles this one question. Neither a
   classification of polyhedral norms nor a K-number is asserted.

2. **Explanatory calculation — the omitted facet causes the failure of the
   proposed test rule.** The selected adjacent vertices lie on the facet
   $[p,q]$, and $T$ maps them to the adjacent vertices $p,-r$. The two required
   active-slope products are preserved by subtracting nonnegative squares.
   This does not constrain the remaining vertex $r$. In the stated norm,
   $r\perp_B q$ since its first facet reading stays $-1$ under every real
   perturbation by $q$, whereas
   $N(Tr-\tfrac12 Tq)=N(0,-3/2)=3/2<2=N(Tr)$.
   These last boundary identities explain the scope of the counterexample;
   they are not additional named Lean theorems in the resolution module.

3. **Existing positive results retain their scope.** Requiring preservation
   at every extreme point is the premise of the cited all-extreme theorem;
   the calculation at $r$ shows that premise fails here. The native positive
   sup-norm result still proves that every independent extreme-point basis
   suffices for a cube. Bijectivity alone is too weak: this operator has
   determinant $-3/2$ and still has unequal norm ratios.

4. **Unresolved separate questions.** The K-number of this norm, the existence
   of another two-point K-set for it, and a classification of sufficient
   tuples for other polyhedral norms are not settled by this result. No new
   companion theorem or classification is included.

## ASSUMED-UNVERIFIED

The literature comparison is limited to the authenticated source and the
two named versioned full texts. Later unindexed or unpublished work,
journal-version equivalence and mathematical priority are unverified.
Independent formal review, required CI and final development-branch delivery
are separate from the native theorem and are not asserted by this dossier.
