---
bibkey: kellerpinchoverpogorzelski2021rellich
authors: Matthias Keller; Yehuda Pinchover; Felix Pogorzelski
year: 2021
title: From Hardy to Rellich inequalities on graphs
doi: 10.1112/plms.12376
url: https://arxiv.org/abs/1909.02286v1
claim: The positive-function ground-state transform rewrites a graph Schrodinger quadratic form using transformed conductances and a pointwise potential term; positivity of the transforming function does not imply square summability or attainment of a normalized spectral minimum.
strata_touched: []
license: citation-only
triage: anchor
---

# Positive-function graph transform and its normalization boundary

The primary preprint is Keller–Pinchover–Pogorzelski,
*From Hardy to Rellich inequalities on graphs*,
[arXiv:1909.02286v1](https://arxiv.org/pdf/1909.02286v1),
§6, proof of Theorem 6.1, displayed ground-state-transform identity.
The journal article is *Proceedings of the London Mathematical Society*
122(3), 458–477, [DOI:10.1112/plms.12376](https://doi.org/10.1112/plms.12376).
The note cites the source and does not redistribute its text or PDF.

The paper uses a graph with symmetric nonnegative weights $b(x,y)$, a
full-support vertex measure $m$ and a real potential $q$, with
$H=m^{-1}\Delta+q$. For a positive function $u$ in the local operator domain
and a finite-support real test $\varphi$, the identity in that proof reads,
in the corresponding quadratic-form notation,

$$
Q_H(u\varphi)
=\frac12\sum_{x,y}b(x,y)u(x)u(y)
 |\varphi(x)-\varphi(y)|^2
+\sum_xm(x)u(x)(Hu)(x)|\varphi(x)|^2.
$$

Real and imaginary parts give the complex finite-support version. A finite
Dirichlet restriction includes its exterior killing in $\Delta$ and hence
in $Hu$; omitting it changes the operator. The transforming function is a
positive function on vertices, not a normalized eigenvector by definition.
The paper's use of a positive supersolution and a Hardy weight in Theorem
6.1 has additional hypotheses. The algebraic identity alone does not
supply such a Hardy weight for an arbitrary attractive operator.

The FIB boundary geometry volume §51 consumes this identity with actual
occurrence weights and $u=1$. The shifted operator $H+gI=aL$ is
nonnegative; the unshifted pointwise term is $-g$, with the declared
Dirichlet killing added at the outgoing occurrence. Its uniform lower
certificate is therefore explicit. The volume's source-specific
nonattainment argument uses the infinite number of actual occurrences:
$u=1$ is not in their counting-measure $\ell^2$ space. Neither the graph
transform nor the paper's Rellich inequality supplies the missing
normalized compactness, native conductance realization or physical field
law.
