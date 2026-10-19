---
bibkey: mannamandalpaulsain2025improvement
authors: J. Manna; K. Mandal; K. Paul; D. Sain
year: 2025
title: "An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries"
doi: null
url: https://arxiv.org/abs/2511.20345v1
claim: "The final Open Question asks whether preservation at any chosen n independent extreme points forces a bounded endomorphism of every n-dimensional polyhedral Banach space to be a scalar multiple of an isometry."
strata_touched:
  - D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation
license: citation-only
triage: anchor
---

## Primary statement and conventions

Jayanta Manna, Kalidas Mandal, Kallol Paul and Debmalya Sain,
*An improvement of the Blanco-Koldobsky-Turnšek characterization of isometries*,
arXiv:2511.20345v1, submitted 2025-11-25.
The [versioned author text](https://arxiv.org/html/2511.20345v1#S2.p45.1)
ends with the following question, with rendered mathematical symbols transcribed
and whitespace normalized:

> Open Question: In an n-dimensional polyhedral Banach space, does the preservation of Birkhoff-James orthogonality by a bounded linear operator at any n linearly independent extreme points necessarily imply that the operator is a scalar multiple of an isometry?

The standing field is real or complex (S1.p6.1). Birkhoff–James orthogonality is
the inequality $\|x\|\le\|x+\lambda y\|$ for every base-field scalar
$\lambda$ (S1.p7.1). Local preservation quantifies every direction $y$
(S1.p8.1). The proper-subset discussion immediately before the question
(S2.p44.1) distinguishes a chosen independent tuple from a requirement to
preserve at every extreme point. The final question has no norm-one,
nonzero-operator, regularity or smoothness restriction. The preceding
all-extreme-point theorem does not supply such a restriction to the question.

Polyhedrality is implemented by finiteness of the actual real-convex extreme
points of the closed unit ball. This agrees with the explicit finite-dimensional
definition in the authors' arXiv:2407.08900v1, S1.p9.1, and
arXiv:2504.11161v2, S1.p2. The source conclusion is a single scalar times a
linear isometry, including scalar zero.

## Bounded comparisons

The complete numbered statements and explicit examples of
[arXiv:2504.11161v2](https://arxiv.org/html/2504.11161v2), revised 2026-02-07,
and [arXiv:2501.02714v1](https://arxiv.org/html/2501.02714v1), submitted
2025-01-06, have been compared with this question. The entire proof and both
witness constructions of the latter's Theorem 2.33 are included in that
comparison. These source readings establish the following bounded distinctions:

* Theorems 2.19 and 2.27 and Corollary 2.20 of 2504.11161v2 require every
  extreme point or every point of a specified smoothness order. They do not
  replace this test set by an arbitrary independent tuple.
* Lemma 2.16 and Theorem 2.18 of that paper extend preservation along a tested
  face. In the example below $[p,q]$ is one face and its image $[p,-r]$ is
  another. This extension does not reach the omitted vertex $r$.
* Remark 2.15 gives a Hilbert-space projection example, whose ball is not
  polyhedral. The explicit $\ell_p^n$, $1<p<\infty$, $p\ne2$, examples in
  Theorem 2.33 of 2501.02714v1 likewise have infinitely many extreme points.
  They are the arbitrary-Banach-space negative phenomenon cited after the
  target question, and do not satisfy its polyhedral premise.
* Corollary 2.29 of 2501.02714v1 gives bijectivity for two independent extreme
  tests in a polyhedral plane. Bijectivity does not imply the scalar-isometry
  conclusion. The operator below is invertible.
* The existing [sup-norm result](../../Blueprint/D5/S3/Analytic/BanachGeometry/LinfKNumber.md)
  characterizes extreme-point K-sets only on $\ell_\infty^n$. Norm equivalence
  does not preserve BJ orthogonality; it supplies no bridge to an irregular
  hexagonal norm.

No inspected theorem or explicit example in these two versioned full texts
supplies this whole polyhedral resolution. This is a bounded comparison, not
a global absence, priority or present-openness certificate. No new source
requests are part of the native implementation.

## Native counterexample and correspondence

On $\mathbb R^2$ put

$$
N(a,b)=\max\{|a|,|a+b|,|a/2+b|\},\qquad
T(a,b)=(a+b,-3b/2).
$$

The native carrier is the submodule $w_2=w_1-w_0/2$ in the three-dimensional
sup-norm space, with $(a,b)\mapsto(a,a+b,a/2+b)$. Its inherited norm is
exactly $N$, its real dimension is two, and it is complete. The actual unit
ball has finitely many extreme points, contained in
$\{\pm p,\pm q,\pm r\}$, where
$p=(1,0)$, $q=(0,1)$ and $r=(-1,3/2)$.
The native proof establishes that $p,q$ are extreme unit vectors and an
independent pair, constructs $T$ as a continuous linear endomorphism, and
proves full local BJ preservation at both selected vectors for every real
direction and scalar. Norms $N(Tp)=1$ and $N(Tr)=2$, with $N(p)=N(r)=1$,
contradict every equality $T=cU$ with native linear isometry $U$.

`PolyhedralBJRefutation.claim` is a closed proposition, the conjunction of
the universal real and complex assertions. Its unique designated `result`
is literally `Not claim`. The real instance refutes that conjunction; the
claim has no free counterexample assumption and no missing realization
premise. This settles one universal question, without a classification of
polyhedral spaces or a determination of their K-numbers.

## Scope

The prospective native-implementation registration is
[issue #19309](https://github.com/the-omega-institute/trureturing/issues/19309).
The ordinary counterexample and the bounded comparisons preceded that issue;
they are not retroactively preregistered. Journal-version equivalence and
later unindexed or unpublished work are unverified. The cited source
identities and anchors are the limits of the literature statements here.
