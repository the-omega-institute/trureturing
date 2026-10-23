---
slug: bilyk-et-al-2022-averaged-kernel-characterization-refutation
bibkey: bilykferizovicglazyrinmatzkeparkvlasiuk2022multivariate
doi: 10.1007/s00209-022-03000-z
url: https://arxiv.org/abs/2104.03410
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MultivariateEnergy/Result.result
---

# The averaged-kernel characterization fails

## Problem

D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park and O. Vlasiuk,
*Potential theory with multivariate kernels*, Math. Z. 301 (2022),
Section 5, paragraph before Theorem 5.3, verbatim:

> We suspect that the property that σ minimizes I_K is equivalent to the fact that U_K^{σ^{n−2}} is conditionally positive definite, i.e. the two-input energy I_{U_K^{σ^{n−2}}} is minimized by σ. This conjecture is supported by all the examples known to us.

The setting is the unit sphere in real Euclidean space, normalized surface
measure σ, and continuous symmetric rotationally invariant kernels with n ≥ 3.
Definitions 2.1–2.2 give the measure and energy conditions; (5.1) gives invariance.

| Source object | Formal reading |
|---|---|
| S^{d−1} | `Defs.S d`, the unit sphere subtype in `EuclideanSpace ℝ (Fin d)` with its Borel structure |
| σ | `Defs.sigma d`, radial spherical measure of volume scaled to mass one |
| K | `(Fin (m+3) → Defs.S d) → ℝ`, where n=m+3 |
| Continuity, symmetry, rotational invariance | `Defs.IsAdmissible`; the counterexample is invariant under the full orthogonal group and hence under the special orthogonal group |
| I_K(μ) | `Defs.energy K μ`, the integral against μ in every input |
| σ minimizes I_K | `Defs.IsMinimizer K (Defs.sigma d)`, over all Borel probability measures |
| U_K^{σ^{n−2}} | `Defs.avgKernel K`, integrating the first n−2 inputs |
| Conditional positive definiteness | `Defs.IsCondPosDef`, the quadratic form on differences of two finite positive measures of equal total mass; Jordan decomposition covers all finite signed measures of mass zero |
| Universal equivalence | `Defs.claim`, for all d≥2 and n≥3; its orthogonally invariant subclass already contains the refuting family |

## Motivation

Averaging detects a quadratic variation at the uniform measure. A global
minimization criterion must also control higher-order terms in the energy.
A cubic centered-moment term separates those two requirements.

## Gap

Conditional positive definiteness of the averaged kernel does not imply that
normalized surface measure globally minimizes the original multivariate energy.
The counterexample has positive quadratic variation and negative energy at a
Dirac probability measure.

## Route

For x on the unit sphere in dimension d, define

$$
A(x)=xx^{\mathsf T}-I/d,\qquad
L(x,y)=\operatorname{tr}(A(x)A(y)),\qquad
T(x,y,z)=\operatorname{tr}(A(x)A(y)A(z)).
$$

The three-input family is

$$
K_{d,\beta}(x,y,z)=\frac\beta3\bigl(L(x,y)+L(x,z)+L(y,z)\bigr)-T(x,y,z).
$$

The pair trace is $(x\cdot y)^2-1/d$. The triple trace is

$$
(x\cdot y)(y\cdot z)(z\cdot x)
-\frac{(x\cdot y)^2+(y\cdot z)^2+(z\cdot x)^2}{d}+\frac2{d^2}.
$$

These formulas prove continuity, symmetry and orthogonal invariance. Coordinate
reflections annihilate off-diagonal second moments of σ; coordinate permutations
make diagonal moments equal, and their sum is one. Thus
$\int xx^{\mathsf T}\,d\sigma=I/d$ and $\int A\,d\sigma=0$.
For any Borel probability measure μ, put $Q=\int A\,d\mu$. Then

$$
I_K(\mu)=\beta\operatorname{tr}(Q^2)-\operatorname{tr}(Q^3),\qquad
U_K^\sigma(x,y)=\frac\beta3 L(x,y).
$$

For finite positive measures μ₁,μ₂ the quadratic difference form of the averaged
kernel is $\frac\beta3\operatorname{tr}((Q_1-Q_2)^2)\ge0$ when β≥0,
since the Q matrices are real symmetric. This holds without a mass constraint.
On the other hand, for any unit vector e,

$$
I_K(\delta_e)=\frac{d-1}{d}\left(\beta-\frac{d-2}{d}\right)
<0=I_K(\sigma)
\quad\left(d\ge3,\quad0<\beta<\frac{d-2}{d}\right).
$$

## Falsifier

The universal equivalence would imply minimization for the admissible kernel
at d=n=3 and β=1/10 because its averaged pair kernel is conditionally positive
definite. The competitor δ_e has energy −7/45, whereas σ has energy zero.

## Evidence

The unconditional theorem `D5/S3/Analytic/MultivariateEnergy/Result.result`
has type `¬ Defs.claim`. Its principal family theorem is
`D5/S3/Analytic/MultivariateEnergy/Result.family_refutes`, for every d≥3 and
0<β<(d−2)/d. All three conjuncts, admissibility, conditional positive
definiteness and failure of minimization, are used in the refutation.

Principal dependencies are
`Moments.integral_coord_mul_coord`, `Moments.integral_A_eq_zero`,
`Moments.L_eq`, `Moments.T_eq`, `Moments.isAdmissible_familyKernel_three`,
`Energy.energy_family_eq`, `Energy.avgKernel_family_eq` and
`Energy.isCondPosDef_family`, all in `D5/S3/Analytic/MultivariateEnergy/`.
The result's axiom closure is exactly `propext`, `Classical.choice`, `Quot.sound`.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source proves necessity and a local converse in Theorem 5.3 and leaves the
global converse as a conjecture. No settlement was found in the examined scope:
the source title and identifier, author names with counterexample and conditional
positive definiteness terms, Matzke's dissertation, two follow-ups from 2023,
arXiv:2410.01489, arXiv:2410.22104, and the formal-conjectures collection.
Citation indexes were not examined exhaustively. This scope does not establish
an exhaustive priority claim.

## Triage

### What the settlement shows

1. **PROVED**. For n=3, every d≥3 and 0<β<(d−2)/d, the kernel K is continuous,
   symmetric and orthogonally invariant, its σ-averaged kernel is
   $(\beta/3)\operatorname{tr}(A(x)A(y))$ and conditionally positive definite,
   and $I_K(\delta_e)=((d-1)/d)(\beta-(d-2)/d)<0=I_K(\sigma)$.
   Thus σ is not a minimizer. These are the conclusions and proof dependencies
   of `Result.family_refutes`, consumed by `Result.result`; the displayed
   energies are the private `Result.energy_sigma` and `Result.energy_dirac`,
   and the averaged formula is `Energy.avgKernel_family_eq`.

2. **PROVED**. The uniform second moment is $\int xx^{\mathsf T}\,d\sigma=I/d$
   (`Moments.integral_coord_mul_coord`), and
   $I_K(\mu)=\beta\operatorname{tr}(Q^2)-\operatorname{tr}(Q^3)$
   (`Energy.energy_family_eq`).

3. **PROVED in prose**. For every n≥3, take

   $$
   K_{d,n,\beta}=\frac\beta{\binom n2}\sum_{i<j}L(x_i,x_j)
   -\frac1{\binom n3}\sum_{i<j<k}T(x_i,x_j,x_k).
   $$

   Independence gives the same energy polynomial for each pair and triple.
   Averaging n−2 inputs kills every term containing an integrated feature,
   leaving $\beta L(x,y)/\binom n2$. Hence the same counterexample holds.
   This extension is mathematical reasoning beyond the three-input Lean family.

   There is also an exact spectral threshold. Let M=$\int xx^{\mathsf T}\,d\mu$,
   let λ₁,…,λ_d≥0 be its eigenvalues, so $\sum_i\lambda_i=1$, and put
   $S_k=\sum_i(\lambda_i-1/d)^k$ and c=(d−2)/d. Expanding and using that sum gives

   $$
   cS_2-S_3=\frac1d\sum_{i<j}(\lambda_i-\lambda_j)^2
   (1-\lambda_i-\lambda_j)\ge0.
   $$

   Each factor is nonnegative. Also $S_2=\sum_i\lambda_i^2-1/d\le(d-1)/d$.
   Therefore $I_K=(\beta-c)S_2+(cS_2-S_3)$ is minimized for β<c by rank-one M,
   and for β>c by M=I/d. Equality $\sum_i\lambda_i^2=1$ means rank one;
   its measure is supported on an antipodal pair. Conversely every measure on
   an antipodal pair gives rank one. For β>c the minimizers are exactly isotropic
   measures. At β=c the energy is nonnegative and σ is a minimizer, giving the
   exact threshold for minimization by σ. Finally
   $|\operatorname{tr}(Q^3)|\le\|Q\|_{\mathrm{op}}\operatorname{tr}(Q^2)$
   implies local minimality of σ for β>0: Q depends continuously on μ in the
   weak topology, and $\|Q\|_{\mathrm{op}}<\beta$ makes the energy nonnegative.
   The spectral certificate, minimizer descriptions and local statement are
   mathematical reasoning, not additional Lean theorems.

4. **COMPUTED**. At d=n=3 and β=1/10 the exact Dirac energy is −7/45 and
   the averaged kernel is $((x\cdot y)^2-1/3)/30$. These rational evaluations
   specialize the displayed formulas.

5. **OPEN**. Whether necessity, proved in the source, admits a converse under
   an additional convexity or uniqueness hypothesis beyond the source's local
   converse remains unresolved here.

## ASSUMED-UNVERIFIED

The all-arity extension, spectral threshold, descriptions of minimizers and weak
local minimality argument are proved in prose and are not additional Lean
conclusions. The literature scope is not exhaustive. The additional-hypothesis
converse question remains open.
