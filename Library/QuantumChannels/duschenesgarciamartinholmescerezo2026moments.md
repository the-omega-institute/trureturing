---
bibkey: duschenesgarciamartinholmescerezo2026moments
authors: Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo
year: 2026
title: "Moments of Quantum Channel Ensembles"
doi: 10.1103/grdp-jph9
url: https://arxiv.org/abs/2511.12700v2
claim: "Appendix B, Conjecture 1 asserts that the cHaar moment-operator Hilbert-Schmidt norm is non-increasing with concatenations; the fourth and fifth powers at d = dE = t = 2 contradict this clause."
strata_touched:
  - D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1103/grdp-jph9

Source: https://arxiv.org/abs/2511.12700v2

Journal: *PRX Quantum* 7, 033050 (2026). Page numbers refer to the arXiv v2 PDF.

## Ensemble, moment operator, and norm

The cHaar ensemble samples a Haar unitary on the system and environment,
with a fixed pure environment state. Section III, page 5, states:

> Thus the action of any quantum channel is

$$\Lambda(X)=\operatorname{Tr}_{E}\left[U_{\Lambda}(X\otimes\nu_E)U_{\Lambda}^{\dagger}\right].$$

Appendix B, Definition 4, page 25, states:

> The $t$-th order twirl over the channel-Haar (cHaar) ensemble $C(d,d_E)$ is defined as a measure over $t$ copies of random channels, and is a uniform, Lebesgue measure when $d_E=d^2$. Using the Stinespring formalism, we can re-write this average as a twirl with respect to the Haar ensemble of unitaries acting on $t$ copies of a composite space, of a system and environment $H\otimes E$ of dimensions $d,d_E$, and a local pure environment state $\nu_E\in B[E]$,

This identifies the ensemble by Haar sampling of the Stinespring unitaries. The environment state may be any fixed pure
state by Haar invariance. The encoding chooses the projector onto coordinate
zero, `Matrix.single 0 0 1`, and reuses the existing `partialTraceRight`.
Its defining sum is exactly the trace over `Fin e`.

Section II, page 3, states:

> We can then define the $t$-th order moment operator as the superoperator of the $t$-th order twirl,

$$\widehat T_{\mathcal C}^{(t)}=\int_{\mathcal C}d\Lambda\;\widehat{\Lambda^{\otimes t}}.$$

The matrix-unit entries of `momentOp d e t` integrate the product of the
$t$ channel entries, all evaluated at the same sampled unitary. The source
composes independent samples; its concatenated moment is the $k$-th power.

Page 3 fixes the norm:

> The choice of norm $\lVert\cdot\rVert$ is task-dependent, and unless noted, we use the Hilbert-Schmidt norm as it is overall the simplest to compute.

For a complex Liouville matrix its square is
$\sum_{r,c}\operatorname{Complex.normSq}(M_{rc})$. The encoding uses the
existing `RHLinalg.frobSq`, defined as the real part of `Matrix.trace (Mᴴ * M)`,
whose equality with this double sum is checked for arbitrary finite indices.

## Large-dimension theorem and finite-dimension conjecture

Theorem “cHaar explicit”, part 3, proves the concatenation hierarchy in the
large-dimension limit $d d_E\to\infty$. Appendix B, Conjecture 1, page 32,
“Hierarchy of Haar, cHaar, Depolarize Ensembles”, states:

> it is conjectured that such a hierarchy holds for all concatenations $k$, orders $t$, and dimensions $d,d_E$. Further, it is conjectured that the cHaar norm is monotonically non-increasing with environment dimension and concatenations,

The concatenation clause is

$$\left\lVert\widehat T_{\mathrm{cHaar}}^{(t)k'}\right\rVert^2
\overset{?}{\leq}
\left\lVert\widehat T_{\mathrm{cHaar}}^{(t)k}\right\rVert^2
\qquad\forall\; k'\geq k.$$

`claim` quantifies positive system dimension, positive moment order, a
nonzero environment dimension, and positive concatenation counts. The
counterexample uses $d=d_E=t=2$, $k=4$, and $k'=5$:

$$N_4=\frac{1213852}{1171875},\qquad
N_5=\frac{30362908}{29296875},\qquad
N_5-N_4=\frac{5536}{9765625}>0.$$

The increasing component is the off-diagonal entry of the lower-triangular
second moment in the identity/swap basis. The limiting projector is not
orthogonal. The finite-dimension concatenation conjecture therefore fails;
the asymptotic theorem has a different quantifier and limit scope. The
environment-dimension display reverses the direction of its verbal clause;
that separate clause is not settled here.
