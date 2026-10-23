---
slug: wang-chen-song-2026-appt-extreme-six-levels
bibkey: wangchensong2026extremeappt
doi: 10.1088/1402-4896/ae9148
url: https://arxiv.org/abs/2603.20717v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.result
---

# The sharp six-level bound for extreme two-qutrit absolutely PPT states

## Problem

N. Wang, L. Chen and Z. Song, *Extreme points of absolutely PPT states with exactly three distinct eigenvalues*, arXiv:2603.20717v1, Physica Scripta 101 (2026), 315210, DOI 10.1088/1402-4896/ae9148, Section VII, Conclusions, page 29, asks:

> Fourth, what is the achievable upper bound of distinct eigenvalues of extreme two-qutrit AP states?

The answer is **six**, including attainment.

### Statement echo

A state is a positive semidefinite trace-one matrix on $\mathbb C^3\otimes\mathbb C^3$. The public definition `apStates` is exactly the set of such matrices satisfying the frozen `QutritPerturbationAttainment.APPT`: every global unitary conjugate has positive semidefinite partial transpose. Extremality is `Set.extremePoints ℝ apStates`; the number of distinct eigenvalues is `(spectrum ℂ rho).ncard`, without multiplicity. `claim` is the conjunction of the universal bound $\le 6$ and existence of an extreme state with exactly six eigenvalues. `result : claim` has no extra hypotheses. The real scalar field is the field of convex coefficients; the complex spectrum belongs to the original complex matrix, rather than a real surrogate. Finite-dimensional Hermitian spectra are finite.

## Motivation

The settling GID is `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.result`, with admission basis `open-problem-resolution (#15732; Proved)`. Preregistration [#15732](https://github.com/the-omega-institute/trureturing/issues/15732) identifies the published question and its literature scope.

The supporting modules establish Hildebrand sufficiency, a feasible spectral perturbation, and six-level extremality. They have admission basis `escape-witness`. The pencil-dependency equations are part of `QutritSpectralFeasiblePerturbation` and feed its positive-radius theorem.

## Gap

The source question concerns the sharp achievable bound, including an attaining extreme state. The proof closes both parts for two qutrits. The source's three-level constructions and other valid results retain their stated scopes; questions in other local dimensions and the full classification remain open.

The four-slot escape audit of `result` and all fourteen other new public theorems is unfinished under [#16011](https://github.com/the-omega-institute/trureturing/issues/16011). The missing evidence consists of faithful complete dependent-family realizations, reconstruction and equivalence bridges, enrolled readouts, whole-family variation and sensitivity, and actual observational dependence for the continuous matrix/eigenvalue families. No Reg source or completed registration is claimed. `QutritSixLevelExtremality.ConvexKernel.K2_linear` is the shared linearity identity used by both the convex-kernel argument and the feasible spectral perturbation, with the same unfinished audit. `QutritSpectralReduction.bell_mem_unitaryGroup` states unitarity of the Bell basis matrix and has an unfinished four-slot registration under that issue.

## Route

The frozen `QutritSpectralReduction.K1`, `K2`, `boundaryValues` and `spectral_reduction` provide the two pencils and necessity. `QutritHildebrandSufficiency.Sufficiency.hildebrand_sufficiency` supplies sufficiency through Schmidt diagonalization and the trace rearrangement estimate; `Criterion.hildebrand_criterion` combines the two directions. The proof uses the frozen finite SVD and doubly stochastic rearrangement results.

For seven or more spectral levels, the active kernel constraints have a dependency. When both pencils are singular, writing $p$ and $q$ for their kernel vectors gives
$ p^\top(K_2-K_1)q=(\lambda_6-\lambda_7)p^\top Jq=0 $.
The case $\lambda_6=\lambda_7$ is handled separately. A block-preserving trace-zero vector survives the constraints, and `FeasiblePerturbation.spectral_radius` gives a positive radius preserving order, positivity, trace and both PSD pencils. Hildebrand sufficiency transports this spectral interval back to states, producing a nontrivial open-segment decomposition. `QutritExtremeSixLevels.universal_bound` excludes such a decomposition at an extreme point.

The attaining diagonal state has spectrum $(318,312,200,169,148,148,130,130,130)/1685$. The explicit supporting functional has weights $(-286,-208,-176,128,176,208,242,286,338)$. Its nonnegative trace on AP states vanishes at this state. Equality forces diagonal alignment and the two active kernels; the resulting linear equations uniquely determine the spectrum. `QutritSixLevelExtremality.Extremality.six_level_attainment` proves the existential half.

## Falsifier

A two-qutrit AP extreme state with seven distinct eigenvalues refutes the universal clause. Failure of AP membership or extremality of the attaining state refutes the construction. A spectrum with seven levels alone does not imply that both pencils are singular: the perturbation proof also covers one or neither singular pencil.

## Evidence

The kernel-checked settling declaration is `D5.S3.Quantum.Entanglement.AbsolutePPT.QutritExtremeSixLevels.result`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The corresponding Scribe has one `OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

The literature notes are `Library/QuantumBounds/wangchensong2026extremeappt.md` and `Library/QuantumStates/hildebrand2007pptspectra.md`.

The independent check is published in [the experiments repository](https://github.com/the-omega-institute/trureturing-experiments/tree/130752b956e5676e4fd865ab5bd7b8e65bf6203a/docs/reports/wang-chen-song-2026-appt-extreme-six-levels), at commit `130752b956e5676e4fd865ab5bd7b8e65bf6203a`, entry `docs/reports/wang-chen-song-2026-appt-extreme-six-levels/check.py`. Command: `python3 check.py`; exit 0; script SHA-256 `4978aca8eaedec526e32042542df860e5558a6a97bc3e4683d7182ca3ae37b09`. The exact checks cover the polynomial family on $h\in[0,1/100]$, its strictly decreasing six levels, kernel identities, PSD rank-two pencils, and $\det M(h)=-512Z(h)$ with no zero on that interval; they also cover the symbolic functional identity for arbitrary $\mu$. The numerical sanity checks use seed $20261012$, the $h=0$ state and the fixed control spectrum. They return least sampled or locally optimized partial-transpose eigenvalues $8.508\times10^{-3}$ and $-1.084\times10^{-1}$ respectively, with final `bad= 0`. These sampled readings do not assert minimization over every global unitary.

## Triage

### What the settlement shows

- **Proved, kernel-checked Hildebrand criterion.** `QutritHildebrandSufficiency.Criterion.hildebrand_criterion` identifies APPT with positivity of both boundary pencils for an ordered two-qutrit spectral diagonalization. `Sufficiency.hildebrand_sufficiency` supplies sufficiency; `SpectralBridge.spectral_reduction_ordered` supplies necessity.
- **Proved in prose, singular-pencil rank.** If $\lambda_9>0$, each Hildebrand pencil has three strictly positive diagonal entries and three nonpositive off-diagonal entries. A rank-one positive semidefinite matrix would be $vv^\top$ with every coordinate of $v$ nonzero, so the product of its three off-diagonal entries would be $v_1^2v_2^2v_3^2>0$. Nonpositive off-diagonal entries instead give a product at most zero. Thus its rank is at least two; if it is singular, its rank is exactly two. This is a prose derivation, not a separately kernel-checked rank theorem.
- **Proved, kernel-checked perturbation mechanism.** `QutritSpectralFeasiblePerturbation.FeasiblePerturbation.spectral_radius` supplies the nonzero perturbation and positive feasible radius for every ordered nonnegative trace-one spectrum with at least seven levels and PSD pencils. Its consumed private `PencilDependency.kernel_difference_identity`, `ActiveKernels.active_dependency` and `Dimension.block_perturbation` establish the kernel-equation dependency and surviving block-preserving trace-zero direction. The two-singular-pencil identity above is one case of this argument; seven levels do not force both pencils singular. `QutritExtremeSixLevels.StateDecomposition.nontrivial_decomposition` transports the interval to a nontrivial state decomposition, and `universal_bound` proves the contradiction with extremality.
- **Proved, kernel-checked attainment mechanism.** `QutritSixLevelExtremality.Extremality.six_level_attainment` proves existence at the rational spectrum above. Its consumed private `SupportingFunctional.trace_support_nonneg`, `trace_support_zero_diagonal`, `trace_support_zero_kernel` and `Extremality.rho0_decomposition_trivial` use the explicit functional $W$ to force every convex component to equal the attaining state.
- **Computed, exact family readings.** The experiment entry proves its symbolic equalities and checks signs on $h\in[0,1/100]$; it checks the determinant, kernel and PSD conditions described in Evidence. Lean attainment is the $h=0$ instance. These family identities do not assert a Lean proof of extremality for every parameter.
- **Computed, numerical sanity.** The experiment returns `bad= 0` and the two eigenvalue readings in Evidence for its sampled and locally optimized unitary searches. They are not universal bounds over unitary matrices.
- **Open, continuous-family formalization.** Extremality for every $h\in[0,1/100]$ is not settled by the delivered Lean instance. The computed pencil and determinant identities are separate evidence.
- **Open.** The analogous sharp bound for qubit–qudit and higher local dimensions, and the full classification of extreme AP spectra, remain open.
- **Effect on source results.** The two-qutrit achievable-bound question is settled with sharp value six. The source's three-level results retain their hypotheses and conclusions; this proof does not classify all extreme spectra or settle its other open questions.

## ASSUMED-UNVERIFIED

The published journal edition's full text was not verified; the question is verified in the arXiv source as recorded in #15732. Exhaustive worldwide priority beyond that bounded literature screen is not established. The general-dimension questions, full classification and unfinished escape audit remain separate boundaries.
