---
slug: ahiable-kothakonda-winter-2026-eq31-absolute-separability
bibkey: ahiablekothakondawinter2026geometry
doi: 10.48550/arXiv.2608.03390
url: https://arxiv.org/abs/2608.03390v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31.result
---

# The linear spectral condition (31) and absolute separability

## Problem

J. Ahiable, N. B. T. Kothakonda and A. Winter, *The geometry of absolute separability and other convex
matrix properties from spectrum*, arXiv:2608.03390v2, Section 7 (page 39):

> Thus, another matter of interest is to resolve Conjecture 6.7 in the positive, and to show that the
> linear condition in Eq. (31) is sufficient for absolute separability: because then the maximum purity
> over all three sets must coincide.

Theorem 6.2 (page 23) proves that a state on $\mathcal M_m\otimes\mathcal M_n$ whose decreasingly ordered
eigenvalues satisfy $2\lambda_{mn}+\sum_{k=1}^{m-1}\lambda_{mn-k}\ge\sum_{k=1}^{m-1}\lambda_k$ (31) is
absolutely PPT. A state is absolutely separable when every $U\rho U^\dagger$, $U\in\mathcal U(mn)$, is
separable. The verbatim texts are in [the literature note](../Library/QuantumStates/ahiablekothakondawinter2026geometry.md).
Issue [#14958](https://github.com/the-omega-institute/trureturing/issues/14958) preregisters the reading
($2\le m\le n$, the repository's finite-sum separable cone) and the route.

## Motivation

Absolute PPT and absolute separability are known to coincide for $2\otimes n$ (Johnston 2013) and are
conjectured to coincide in general. The inscribed polytope $\mathcal P_{m,n}$ cut out by (31) carries the
paper's purity and volume bounds; its containment in the absolutely separable spectra would make the
maximum purity over the polytope, the absolutely separable and the absolutely PPT spectra coincide under
Conjecture 6.7, and would turn the polytope's volume into a lower bound on absolute separability.

## Gap

For $m=2$ the statement follows from Theorem 6.2 and Johnston's theorem; for $m\ge3$ the source leaves it
open, and the literature check in #14958 found no settlement (`not-found-in-searched-scope`).

## Route

With $D=mn$, $t=\lambda_D$, $\delta_k=\lambda_k-\lambda_{k+1}$, $a_k=\min\{k,m-1,D-k-1\}$ and $P_k$ the projection
onto the first $k$ eigenvectors of $U\rho U^\dagger$:

1. Abel summation turns (31) into $\sum_{k=1}^{D-2}a_k\delta_k\le2t$, and
   $U\rho U^\dagger=(t-\tfrac12\sum a_k\delta_k)I+\delta_{D-1}P_{D-1}+\sum_{k=1}^{D-2}\tfrac{\delta_k}{2}(a_kI+2P_k)$ with
   nonnegative coefficients.
2. **High-rank rays and $P_{D-1}=I-|\psi\rangle\langle\psi|$** lie in the Gurvits–Barnum ball
   $\lVert R-cI\rVert_2\le c$; the ball is separable because a Hermitian block-positive $H$ satisfies
   $\mathrm{Tr}H^2\le(\mathrm{Tr}H)^2$, proved by a finite fourth-moment functional over the phases
   $\{\pm1,\pm i\}$ corrected by the basis vectors, together with the frozen separation theorem
   `exists_entanglementWitness`.
3. **Middle rays** $mI+(2P_k-I)$: for a contraction $C$, the square root of $I-C^*C$ supplies an orthonormal
   family whose first coordinates are the columns of $C$; extending it to an orthonormal basis gives a unitary
   dilation $V$ with upper-left block $C$, and diagonalizing the normal matrix $V$ in an orthonormal basis
   (eigenvalues of modulus one) and restricting to the first coordinates gives $C=\sum_rc_rR_{a_r}$ with
   $|c_r|=1$ and $\sum_rR_{a_r}=I$. Hence each $2\times2$ contraction block is separable, and the block identity
   $mI+H=\sum_iE_{ii}\otimes(I+H_{ii})+\sum_{i<j}(\text{blocks})$ finishes.
4. **Low-rank rays** $kI+2P_k=\sum_{i\le k}(I+2|v_i\rangle\langle v_i|)$: with a product pair maximizing the
   overlap (compactness) and an eight-point Gaussian-like average, $I+2|\psi\rangle\langle\psi|$ is an explicit
   sum of product PSD terms, without the Schmidt decomposition.

## Falsifier

A spectrum satisfying (31) whose unitary orbit leaves the separable cone, an error in the Abel summation
($2m-1\le D$ is used), or a reading of the eigenvalue order different from the source.

## Evidence

`D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31.lean` states `claim` over
Mathlib's decreasingly ordered eigenvalues `Matrix.IsHermitian.eigenvalues₀` and every unitary
`U ∈ Matrix.unitaryGroup`, with the repository's `separableCone` (`D5/S3/Resource/CompositeCones.lean`), and
proves `result : claim`. The rays are proved in `GurvitsBarnumMoments`, `GurvitsBarnumBall`,
`ContractionBlocks`, `LowRankRaysAverages` and `LowRankRays` of the same directory. The axiom closure of
`result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.

## Triage

Tier 1 by source (an explicit 2026 question), pursued as a research line in #14958. `theorem`; resolution
`proved`. Admission basis `open-problem-resolution`; utility `none`. There is no digestion atom.

### What the proof shows

- **Proved by `result`:** for every $2\le m\le n$, the polytope $\mathcal P_{m,n}$ of Theorem 6.2 consists of
  absolutely separable spectra; in particular absolute PPT and absolute separability agree on it, and the
  polytope's volume is a lower bound on the volume of absolutely separable spectra.
- **Mechanism:** (31) is exactly the condition that the identity coefficient in the ray decomposition is
  nonnegative, and every ray $a_kI+2P_k$ is separable for the smallest of three thresholds $k$, $m-1$,
  $D-k-1$, each matching a known separability mechanism (local averaging over a rank-one pair, contraction
  blocks across the smaller factor, the Frobenius ball around the identity).
- **Side result:** the inequality $\mathrm{Tr}(M^2)\le(\mathrm{Tr}M)^2$ for Hermitian block-positive $M$, for
  which Szarek, Werner and Życzkowski (J. Math. Phys. 49, 032113 (2008), p. 18) ask for "a simple direct
  proof", follows from the finite fourth-moment identity
  $L_d(\bar z_iz_j\bar z_kz_l)=\delta_{ij}\delta_{kl}+\delta_{il}\delta_{jk}$ for
  $L_d(f)=4^{-d}\sum_{z\in\{\pm1,\pm i\}^d}f(z)+\sum_af(e_a)$ applied to compressions in both factor orders
  (`GurvitsBarnumBall.frobSq_le_trace_sq_of_blockPositive`; the statement is literature-attested, the proof
  is repo-derived).
- **Open:** whether the whole absolutely PPT set is absolutely separable for $m\ge3$ (the general question
  of the source), and Conjecture 6.7 itself.

## ASSUMED-UNVERIFIED

The literature check in #14958 is bounded and does not establish worldwide novelty or priority.
