---
slug: kiem-kye-2026-local-distinguishability
bibkey: kiemkye2026localgeometry
doi: 10.48550/arXiv.2608.14199
url: https://arxiv.org/abs/2608.14199v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.result
---

# Local distinguishability at every boundary projection state

## Problem

Young-Hoon Kiem and Seung-Hyeok Kye, *Local geometry for Schmidt number witnesses*, arXiv:2608.14199v1, Section 5, states:

> Nevertheless, we conjecture that the inclusion BP_ℓ ⊋ BP_{ℓ+1} is locally distinguishable around ϱ_{E⊥} for ℓ ≥ k, whenever ϱ_{E⊥} is on the boundary of the convex set BP_k.

For a nonzero proper complex subspace $E\subset\mathbb C^m\otimes\mathbb C^n$, write $\rho=P_{E^\perp}/\dim E^\perp$. The result says that if $\rho\in\partial_H BP_k$, then every neighbourhood of $\rho$ meets $BP_\ell\setminus BP_{\ell+1}$ whenever $1\le k\le\ell<\min(m,n)$. Here $H$ is the trace-one Hermitian affine space, and $BP_j$ tests nonnegativity against all vectors of Schmidt rank at most $j$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Trace-one Hermitian affine space $H$ | `ambient m n` | Both Hermiticity and complex trace one. |
| $j$-blockpositivity | `BP m n j`; imported `schmidtRank` | The real quadratic form is nonnegative on every vector whose coefficient matrix has rank at most $j$. |
| Normalized projection onto $E^\perp$ | `rhoPerp E` | `Submodule.starProjection` converted by `Matrix.toEuclideanLin.symm` and divided by the complex dimension. |
| Nonzero proper subspace | `E ≠ ⊥`, `E ≠ ⊤` in `claim` | The entire source range is retained. |
| Boundary in $H$ | `OnBoundary` | Membership in the closed set $BP_k$ and in the closure of $H\setminus BP_k$. |
| Adjacent inclusions in the finite chain | `1 ≤ k`, `k ≤ ℓ`, `ℓ < min m n` | The range in Sections 3 and 5; it implies $m,n\ge2$. |
| Every neighbourhood meets the difference | `LocallyDistinguishable` | Ambient and relative neighbourhoods give the same test because the difference lies in $H$. |
| The conjecture for every subspace | `result : claim` | No genericity hypothesis. |

All public definition bodies are the literal conventions of [#17787](https://github.com/the-omega-institute/trureturing/issues/17787), with the matrix abbreviation expanded. The imported Schmidt rank is the rank of the coefficient matrix.

## Motivation

The settling GID is `D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability.result`, with admission basis `open-problem-resolution (#17787; Proved)`. This is an external named problem with no digestion atom. One `OpenProblemResolutionClaim` records `Proved` on the settling declaration. The source is documented in the [Library note](../Library/QuantumContext/kiemkye2026localgeometry.md).

## Gap

Sections 3–4 of the source establish generic cases using principal supporting hyperplanes. Section 5 asks for local distinguishability when that method does not give witnesses. The result covers non-generic kernels by moving the kernel vector and then perturbing the state.

## Route

The following statements are proved in the settling module; the named helpers are private.

1. `boundary_kernel` and `boundary_subspace_vector` obtain a unit vector $v\in E$ with Schmidt rank at most $k$. Compactness of unit low-rank vectors makes the projection of the nonpositive quadratic-form tests closed. A boundary limit therefore has a zero quadratic-form test, which is a kernel vector for a positive semidefinite matrix.
2. `rank_one_raise` constructs a rank-one perturbation of a rectangular coefficient map: pair a dual functional nonzero on its kernel with a vector outside its range. For nonzero perturbation parameter, the new kernel is the intersection with that functional's kernel. Rank–nullity raises the rank by one. `mem_closure_exact_rank` and `unit_schmidtRank_density` iterate this and normalize, approximating $v$ by unit vectors $u$ of rank $\ell+1$.
3. `closure_of_low_rank_kernel` compresses $A$ by $I-uu^\dagger$. The compression is positive semidefinite, annihilates $u$, and equals $A$ at the original unit kernel vector. Its trace is continuous and tends to one, so normalization is defined nearby and tends to $A$.
4. `compact_cone_overlap`, `overlap_schmidtRank` and `overlap_witness` obtain $0\le\alpha<1$ bounding squared overlap with unit vectors of rank at most $\ell$. Thus $Q=\alpha I-uu^\dagger$ is nonnegative on those vectors and has value $\alpha-1<0$ at $u$.
5. `kernel_state_in_closure` adds a sufficiently small positive multiple of $Q$ to the compressed state and normalizes its trace. The resulting matrices lie in $BP_\ell\setminus BP_{\ell+1}$. The two closure steps and `closure_locallyDistinguishable` give `result`.

## Falsifier

A counterexample would consist of dimensions, a nonzero proper subspace, indices in the stated chain, its boundary projection state, and a neighbourhood missing $BP_\ell\setminus BP_{\ell+1}$. `result` rules out this complete configuration under the displayed hypotheses. A finite sampling failure to locate a witness is not such a neighbourhood certificate.

## Evidence

`D5.S3.Quantum.Entanglement.LocalDistinguishability.KiemKyeLocalDistinguishability.result` is the settling theorem. Its public definitions and its proof are compiled with the scoped build and freeze door. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit is unfinished under [#18546](https://github.com/the-omega-institute/trureturing/issues/18546). The targets are the settling `result` and the published owner `D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector`. No Reg mirror is delivered. The dependent telescope for the first target and the universe-polymorphic family for the second still lack complete source reconstruction, occurrence bridges, whole-family variation, sensitivity and observational-dependence evidence. No `declared_validated` registration is asserted.

### Numerical experiment

[Experiment directory at `d771f467de03d12ca5206f1d061e345356b3a5a1`](https://github.com/the-omega-institute/trureturing-experiments/tree/d771f467de03d12ca5206f1d061e345356b3a5a1/docs/reports/kiem-kye-2026-local-schmidt-witnesses). The `check.py` SHA-256 is `785a92069698f8a98003b872c8813e82a385b03fd5a1533327990e276fbccb03`; the source at that commit and the executed file have the same hash.

From the experiments repository, the commands are `OPENBLAS_NUM_THREADS=1 python3 docs/reports/kiem-kye-2026-local-schmidt-witnesses/check.py 20261016 20 300` (exit 1) and `OPENBLAS_NUM_THREADS=1 python3 docs/reports/kiem-kye-2026-local-schmidt-witnesses/check.py 20261016 60 3000` (exit 0). The first misses preregistered criterion (a): the numerical overlap maximum differs from the top-$\ell$ Schmidt formula by more than $10^{-4}$ in some instances. The second meets that tolerance and all witness tests in all twelve instances. This reproduces the miss and pass recorded in #17787.

The exact tested scope is four configurations at $t\in\{0.2,0.05,0.01\}$: a product-vector kernel in $3\times3$ with $k=1$ and $\ell=1,2$; a product-plus-entangled-vector kernel in $3\times3$ with $k=1,\ell=2$; and a Schmidt-rank-two kernel in $3\times4$ with $k=\ell=2$. The checks measure overlap optimization, the negative test at the constructed vector, a sampled low-rank quadratic-form minimum, Hermiticity, and distance from the projection state. These finite numerical checks do not establish universal blockpositivity.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | Proved, kernel-checked: `boundary_kernel`, `unit_schmidtRank_density`, `kernel_state_in_closure`, `closure_of_low_rank_kernel`, `result` | Kernel-moving compression and an overlap witness produce arbitrarily close matrices in $BP_\ell\setminus BP_{\ell+1}$; no principal supporting hyperplane is used. |
| Strength | Proved, kernel-checked: `closure_of_low_rank_kernel` | Every positive semidefinite trace-one matrix with a unit kernel vector of Schmidt rank at most $\ell+1$ satisfies the sufficient closure criterion for $\ell<m,n$. It is not restricted to normalized projections. |
| Consequences | Proved, kernel-checked: `result` | Every boundary projection state has the required local distinguishability, without genericity; every neighbourhood contains an $\ell$-blockpositive matrix with a negative rank-$(\ell+1)$ test, in the source's Schmidt-number-witness sense. |
| Converse and rates | Open | A separate theorem establishing the converse of the sharper density-matrix criterion, and quantitative approximation rates, are not supplied. |
| Experiment | Computed: the two commands, exits and script hash above | Criterion (a) misses at $20\times300$ and passes at $60\times3000$ in exactly the twelve stated instances. |
| Literature | Literature reading recorded in #17787; completeness `ASSUMED-UNVERIFIED` | Sections 3–4 prove generic cases. The source's Section 5 explicitly leaves the non-generic conclusion as a conjecture. |

The source's generic-case theorems keep their stated hypotheses and conclusions. The settling result supplies the unrestricted local-distinguishability conclusion asked for in Section 5; it adds no hypothesis to those earlier theorems. The proof gives a sufficient criterion for arbitrary density matrices, while its converse and effective rates remain separate questions.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source v1, Sections 2, 3 and 5, and the literature screen are recorded in #17787. That screen reports no later author-listed paper and no OpenAlex record, a Semantic Scholar rate-limit response, and seat-reported comparisons with Han–Kye arXiv:2505.10288 and arXiv:2506.03733, Song–Chen arXiv:2508.11308, and Kye 1996/1997. Tomiyama, *Linear Algebra and its Applications* 69 (1985), 169–177, remains unread in that screen. No claim of exhaustive literature coverage is made.

The sufficient density-matrix closure criterion is proved; the converse and quantitative rates are open here. The escape audit remains unfinished under #18546. The module's `generality: I` follows its existing `I` imports, including the current frozen Schmidt-rank owner, despite the dimension-uniform conclusion.
