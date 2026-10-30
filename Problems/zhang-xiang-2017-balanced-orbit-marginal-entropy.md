---
slug: zhang-xiang-2017-balanced-orbit-marginal-entropy
bibkey: zhangxiang2017averageentropyorbit
doi: 10.1007/s11128-017-1570-6
url: https://arxiv.org/abs/1509.00211v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.result
---

# The Zhang–Xiang balanced orbit marginal entropy identity

## Problem

Lin Zhang and Hua Xiang, *Average entropy of a subsystem over a global unitary orbit of a mixed bipartite state*, Quantum Information Processing 16(5), 112 (2017), arXiv:1509.00211v3, pose the balanced-case question in the closing remarks of the TeX source `QINP-D-16-00527-revision.tex`, lines 916–920:

> and (ii) proving the following identity for the balanced system, i.e., $d_A=d_B$,
> $\int\rS(\rho'_A)\dif\mu(U)=\int\rS(\rho'_B)\dif\mu(U).$

The settled Lean proposition is `claim`: for every $n : \mathbb N$ and every `DensityState (Fin n × Fin n)`, the `Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin n × Fin n) ℂ))` integrals of `vonNeumannEntropy` of the right and left marginals of `unitaryConjugateState` are equal, with the same global unitary variable and state.

## Motivation

The source studies the von Neumann entropy of either subsystem after conjugating a mixed bipartite state by a Haar-distributed global unitary. It states that, if the balanced identity holds, its Theorems A1 and A2 give two-sided bounds for the individual average subsystem entropy. Establishing the identity therefore supplies the symmetry premise for that consequence while leaving the separate bounds and their hypotheses to their own statements.

## Gap

The source left the balanced identity as an open problem. The bounded literature check recorded in preregistration issue [#24334](https://github.com/the-omega-institute/trureturing/issues/24334) found the source statement, four accessible citing texts without a settlement, and no repository result addressing this identity. L. Zhang, "Marginal spectral distributions on regular bipartite unitary orbits", arXiv:2608.30370, gives the characteristic function of one marginal through the global spectrum with each local test eigenvalue repeated as often as the other factor's dimension, states that "An analogous formula holds for $\rho_B$", and identifies the two marginal eigenvalue densities in the generic two-qubit case. For $d_A=d_B$ the two characteristic functions coincide, so equality of the two marginal laws, and hence this identity, follows from that paper; the paper states the identity for no dimension and does not cite the source. The check is therefore `not-found-in-searched-scope` for an explicit statement or settlement of the source question, and the identity is a consequence of the cited 2026 formulas.

## Route

1. For every $n : \mathbb N$ and every matrix $x : \mathrm{Matrix}(\mathrm{Fin}\,n × \mathrm{Fin}\,n)(\mathrm{Fin}\,n × \mathrm{Fin}\,n)\,\mathbb C$, the private lemma `partial_trace_swap` proves that `partialTraceRight (F * x * star F)` equals `partialTraceLeft x`, where $F$ is `permutationUnitary (Equiv.prodComm (Fin n) (Fin n))`. These are the complete hypotheses of that lemma.
2. For every $n : \mathbb N$, every $\rho : \mathrm{DensityState}(\mathrm{Fin}\,n × \mathrm{Fin}\,n)$, and every $u : \mathrm{Matrix.unitaryGroup (Fin n × Fin n)\,\mathbb C}$, the private lemma `marginal_swap_mul` applies the matrix identity to show that the right marginal of the state conjugated by $F u$ equals the left marginal of the state conjugated by $u$.
3. The proof uses `MeasureTheory.integral_mul_left_eq_self` with $G = \mathrm{Matrix.unitaryGroup (Fin n × Fin n)\,\mathbb C}$, the real-valued entropy integrand, the Haar measure $\mu$, and $F$ as the multiplier. That lemma requires the instances `[MeasurableSpace G]`, `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, `[Group G]`, `[MeasurableMul G]`, and `[μ.IsMulLeftInvariant]`; the imported unitary-group and Haar constructions provide them.
4. The pointwise equality from step 2 is lifted through entropy with `congrArg`, supplied to `MeasureTheory.integral_congr_ae` via `Filter.Eventually.of_forall`, and the two integrals are identified. The congruence lemma is used with its required `[NormedAddCommGroup G]` and `[NormedSpace ℝ G]` codomain instances and an almost-everywhere equality.

## Falsifier

The settlement would not answer the source question if the formal encoding used unequal factors, a restricted class of states, a different conjugation, a non-Haar measure, or partial traces with the opposite or another subsystem convention. The module instead quantifies over `Fin n × Fin n`, uses `DensityState` (a positive semidefinite trace-one state), conjugates by every element of the global unitary group, and integrates the two explicitly named marginal functions against the displayed Haar measure. No purity, rank, or swap-symmetry condition on $\rho$ is present in `claim`.

## Evidence

The canonical source is `D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.lean`.
- **Proof.** It proves `result : claim`.
- **Axioms.** `result` depends only on `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy.lean.json`.

Declaration statements:
- `result`: `sha256:a0e26343c8cef631db60b47a8ac61854f8ca78b57789be4d6a3e819dab44f763`;
- `claim`: `sha256:5a55373789733c4e246cf61801ba5203c8aebb4f9e6d4431007de292f16ca8ea`.

## Triage

Tier 1 open problem from Zhang and Xiang's 2017 paper, preregistered in issue #24334 before any Lean; `theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n : \mathbb N$ and every `DensityState (Fin n × Fin n)`, the integral over $u : \mathrm{Matrix.unitaryGroup (Fin n × Fin n)\,\mathbb C}$ of the von Neumann entropy of the right marginal of `unitaryConjugateState` equals the corresponding integral with the left marginal, both against `Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin n × Fin n) ℂ))).

**Computed, not formalized**. None.

**Argued, not formalized.** The decisive mechanism is the coordinate-swap unitary: `partial_trace_swap` applies for every $n : \mathbb N$ and every matrix $x : \mathrm{Matrix}(\mathrm{Fin}\,n × \mathrm{Fin}\,n)(\mathrm{Fin}\,n × \mathrm{Fin}\,n)\,\mathbb C$, and `marginal_swap_mul` applies for every $n : \mathbb N$, every $\rho : \mathrm{DensityState}(\mathrm{Fin}\,n × \mathrm{Fin}\,n)$, and every $u : \mathrm{Matrix.unitaryGroup (Fin n × Fin n)\,\mathbb C}$. The latter makes the right-marginal entropy at $F u$ equal to the left-marginal entropy at $u$; the left-invariance instance required by `integral_mul_left_eq_self` then preserves the integral, and `integral_congr_ae` transfers the pointwise equality to the integral. Within the formal claim this reaches every natural $n$ and every mixed state of the stated type, without purity, rank, or swap-symmetry assumptions. The proof has no separate numerical sharpness parameter: it is an exact symmetry identity. The corresponding unbalanced-dimensional question is open here because the coordinate swap is not a self-map of a single `Fin n × Fin n` space when the factor dimensions differ. The source's conditional use of this identity with Theorems A1 and A2 now has its identity premise supplied by the formal result, but those bounds, the average-coherence problem, closed forms for either entropy average, and claims for other entropies are not formalized here.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority; the unidentified citing record noted in issue #24334 is not settled here. The source's Theorems A1 and A2, their two-sided bounds, the average-coherence question, unbalanced dimensions, and other entropy statements are outside the compiled declaration. All statements under “Argued, not formalized” remain unformalized.
