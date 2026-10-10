---
slug: petz-1994-bkm-scalar-curvature-monotonicity
bibkey: dittmann2000kubomori
doi: 10.1016/S0024-3795(00)00130-0
url: https://arxiv.org/abs/quant-ph/9906009v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Petz/SpectralPetz.result
---

# The Kubo–Mori scalar curvature is Schur-concave in the spectrum (Petz's conjecture)

## Problem

Dittmann, arXiv:quant-ph/9906009v1, Section 6, states Petz's conjecture:

> $\rho\succ\varrho\quad\Longrightarrow\quad\mathcal S^1_\rho\ge\mathcal S^1_\varrho$.

Here the source's $\rho\succ\varrho$ means “$\rho$ more mixed than
$\varrho$”. For their spectra $a,b$ sorted decreasingly, respectively,
this means $\sum_{i=1}^k a_i\le\sum_{i=1}^k b_i$ for $1\le k\le n$,
with both full sums equal to one. Thus, in the usual spectral convention,
$a\prec b$. The ordering symbol in the quotation follows Dittmann's
mixing convention.

Gibilisco–Isola, [arXiv:math-ph/0407007v2](https://arxiv.org/abs/math-ph/0407007v2),
Conjecture 8.2, states:

> The scalar curvature of BKM metric is a Schur-increasing function.

Dittmann's Theorem 2 gives, with eigenvalues counted with multiplicity,

$$
\mathcal S^1_\varrho=
\sum_{i,j,k=1}^n d(\lambda_i,\lambda_j,\lambda_k)
-\sum_{i=1}^n d(\lambda_i,\lambda_i,\lambda_i)
+\frac{(n^2-1)(n^2-2)}4.
$$

His Assertion says that the symmetric kernel $h_s$ is concave on
$\mathbb R_+^3$. Lemma 4 derives from it the following inequalities for
$0<x<y$ and $\alpha,\beta>0$, where $h_1=\partial_1 h_s$:

$$
\begin{aligned}
0&\le 2h_1(x,x,y)-h_1(y,x,x)-2h_1(y,x,y)+h_1(x,y,y), &&(62)\\
0&\le h_1(x,x,\alpha)-h_1(y,y,\alpha), &&(63)\\
0&\le h_1(x,y,\alpha)-h_1(y,x,\alpha), &&(64)\\
0&\le h_1(x,\alpha,\beta)-h_1(y,\alpha,\beta). &&(65)
\end{aligned}
$$

The settled spectral statement is: for every $n\ge1$ and positive spectra
$\lambda,\mu$ with unit sums, both sorted decreasingly, if
$\sum_{i=1}^k\mu_i\le\sum_{i=1}^k\lambda_i$ for every $1\le k\le n$,
then $\operatorname{spectralS}(\lambda)\le\operatorname{spectralS}(\mu)$.
Here `spectralS` is Dittmann's spectral triple sum minus the diagonal sum,
without the dimension-dependent constant. The intended result interface is
`D5/S3/Quantum/Petz/SpectralPetz.result`.
The identification $\mathcal S^1=\operatorname{spectralS}+C_n$ with the
Riemannian scalar curvature of the Kubo–Mori metric is Dittmann's Theorem 2,
a literature premise that is not formalized.

## Motivation

Petz's conjecture has been open since 1994 in the literature described below.
It connects spectral mixing with the local geometry of distinguishability
in quantum information geometry: the scalar curvature is conjectured to
increase toward the maximally mixed state. Andai and Gibilisco–Isola left
the general conjecture open; restricted-dimensional or restricted-manifold
results do not settle the faithful density-matrix case in every dimension.

## Gap

The literature check of 2026-10-11 covers arXiv API queries for “Petz
conjecture”, Kubo–Mori/BKM curvature, monotone metric scalar curvature,
and Dittmann concavity. The later results located in that scope concern
submanifolds, [arXiv:2404.09600](https://arxiv.org/abs/2404.09600) and
[arXiv:2303.12008](https://arxiv.org/abs/2303.12008). Gibilisco's 2020
survey still lists the general conjecture as open. These are the recorded
literature readings, rather than an exhaustive worldwide priority claim.
The preregistration is [#15183](https://github.com/the-omega-institute/trureturing/issues/15183).

## Route

The kernel has a smooth positive-domain realization $h_s=(P-2Q)/6$,
where $P=m^2/[L(x,y)L(x,z)L(y,z)]$, $L$ is the logarithmic resolvent
mean, $m$ is the three-node resolvent integral, and $Q$ is the second
divided difference of the exponential at $-\log x,-\log y,-\log z$.
The master logarithmic integral follows from a strip contour. Its density
representation yields, including coincident positive nodes,

$$
-h_s(x,y,z)=\int_0^\infty\frac{\rho_{y,z}(t)}{x+t}\,dt,
\qquad \rho_{y,z}(t)>0\quad(t>0),
$$

and the swap representation

$$
-h_s(x,y,z)=\int_0^\infty
\left(\frac1{x+s}+\frac1{y+s}\right)\rho_{x+y+s,z}(s)\,ds.
$$

These representations imply the strict versions of (62)–(65), without
joint concavity. The spectral derivative identity expresses
$(\partial_x-\partial_y)\operatorname{spectralS}/3$ as the (62) expression,
twice the residual sum of (63) and (64), and the residual double sum of (65).
Its last negative term is $-h_s'(y,\lambda_i,\lambda_j)$; Dittmann's
Theorem 3 proof prints $-h_s(y,\lambda_i,\lambda_j)$ there, omitting the prime.
Consequently every ordered pair direction has nonnegative derivative.
Integration along positive pair-transfer paths and finite majorization
by pair transfers and permutations give the spectral comparison.

Key declaration GIDs are:

- `D5/S3/Quantum/Petz/KernelSmoothness.hs_contDiffOn`.
- `D5/S3/Quantum/PositiveResolvent/MasterStripPoles.stripPoleKernel_rectangle` and `D5/S3/Quantum/PositiveResolvent/LogarithmicIntegral.master_integral`.
- `D5/S3/Quantum/Petz/DensityPositivity.rho_pos` and `D5/S3/Quantum/Petz/StieltjesRepresentation.stieltjes_representation`.
- `D5/S3/Quantum/Petz/SwapRepresentation.swap_representation` and `D5/S3/Quantum/Petz/SwapRepresentation.hs1_sub_swap_integral`.
- `D5/S3/Quantum/Petz/DittmannLemmaFour.dittmann62`, `D5/S3/Quantum/Petz/DittmannLemmaFour.dittmann63`, `D5/S3/Quantum/Petz/DittmannLemmaFourComplete.dittmann64`, and `D5/S3/Quantum/Petz/DittmannLemmaFour.dittmann65`.
- `D5/S3/Quantum/Petz/DittmannLemmaFourComplete.lemma4`.
- `D5/S3/Quantum/Petz/SpectralSymmetrization.d_symmetrization`, `D5/S3/Quantum/Petz/SpectralKernel.spectralS_eq_spectralHs`, `D5/S3/Quantum/Petz/SpectralKernel.spectralHs_transfer_deriv`, and `D5/S3/Quantum/Petz/SpectralKernel.spectralHs_transfer_monotone`.
- `D5/S3/Quantum/Petz/MixingIteration.pair_transfer_reduction` and `D5/S3/Quantum/Petz/OrderedMixingReduction.derivative_pair_transfer_reduction`.

The finite reduction requires only the target spectrum to be decreasing;
the intermediate spectra need not remain sorted. Each transfer preserves
positivity and the total sum, preserves the required prefix inequalities,
and fixes at least one unequal coordinate, so the construction terminates.

## Falsifier

A pair of positive unit-sum spectra satisfying the stated majorization
conditions with negative margin
$\operatorname{spectralS}(\mu)-\operatorname{spectralS}(\lambda)<0$
would refute the spectral result. An error in Theorem 2's formula would
break the curvature identification, while leaving the theorem about the
defined spectral sum intact. A negative numerical margin requires an
independent check of multiplicities, removable limits, and numerical error.

## Evidence

The kernel-checked ingredients are the positivity, integral, strict
inequality, symmetrization, spectral derivative, and majorization declarations
listed in Route. Their reported axiom closures are contained in
`{propext, Classical.choice, Quot.sound}`. The spectral derivative's
nonnegativity theorem explicitly takes the four Lemma 4 inequalities;
`DittmannLemmaFourComplete.lemma4` supplies them. The final
`SpectralPetz.result` interface is separate from these checked ingredients;
no separate kernel acceptance of that interface is recorded here.

Independent research cross-checks report agreement between Theorem 2 and
direct curvature computations. For $n=2$, the Bloch-coordinate metric
$ds^2=dr^2/(1-r^2)+r\operatorname{atanh}(r)\,d\Omega_2^2$ gives absolute
differences at most $10^{-76}$ on the tested radii. For $n=3$, direct
affine-matrix-coordinate curvature contractions agree at approximately
$10^{-12}$. These comparisons include $C_2=3/2$ and $C_3=14$ and the
sphere-positive curvature convention.

The independent research readings also report 960 random T-transform tests,
240 in each dimension $n=3,4,5,6$, at 50 decimal digits with seed `1518302`.
No negative margin occurs; the smallest margin is approximately
$5.147209215375019\times10^{-6}$. These are attributed computational
readings, not kernel proofs or uniform error certificates.

## Triage

The strict Lemma 4 inequalities prove the derivative criterion needed for
spectral Schur concavity. The BKM-specific mechanism is the positive
Stieltjes structure of $-h_s$ in each variable, together with the
constant-sum swap representation. The spectral result implies the stated
curvature monotonicity under the literature premises in ASSUMED-UNVERIFIED.
Dittmann's full joint-concavity Assertion remains [open]; separate-variable
Stieltjes structure and the four derivative inequalities do not prove it.

The WYD-metric curvature conjectures of Gibilisco–Isola are neighbouring
problems [open]. Analogous positive density and swap representations could
supply their needed derivative inequalities, but the BKM density alone
does not establish such representations for the WYD family.

## ASSUMED-UNVERIFIED

The identification of `spectralS` plus $C_n$ with the Riemannian scalar
curvature is Dittmann's Theorem 2, used as a literature premise and not
formalized. The unitary invariance step reducing faithful density matrices
to their spectra is likewise a literature premise, not a formalized
geometric theorem. Numerical cross-checks do not discharge either premise.
