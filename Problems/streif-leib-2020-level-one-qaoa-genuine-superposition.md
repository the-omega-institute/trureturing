---
slug: streif-leib-2020-level-one-qaoa-genuine-superposition
bibkey: streifleib2020forbidden
doi: 10.1103/PhysRevA.102.042416
url: https://arxiv.org/abs/2007.13563v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.result
---

# Level-one QAOA reaches a genuine four-state superposition on three qubits

## Problem

M. Streif and M. Leib, *Forbidden subspaces for level-1 QAOA and IQP circuits*, arXiv:2007.13563v1 (Phys. Rev. A 102, 042416 (2020)), study when a level-one QAOA state can have support on a target subspace. In the paper's Section “More than two target states,” `main.tex`, lines 335–341, they write:

> Based on the assumption that the only solution can be found for $\beta = \frac{1}{4} \pi, \frac{3}{4} \pi, \frac{5}{4} \pi, \frac{7}{4} \pi$ we show in the following that level-1 QAOA can not map to a genuine superposition of more than $2$ but less than $2^n$ target states. We consider a genuine superposition of target states a superposition where no amplitude vanishes.

They then state:

> Based on this observation as well as the calculation for the 2 target state case and numerical investigations we conducted we conjecture that the only possible solutions are $\beta = \frac{1}{4} \pi, \frac{3}{4} \pi, \frac{5}{4} \pi, \frac{7}{4} \pi$.

The module formalizes the unrestricted exclusion as $\mathit{claim} := \forall n,e,\beta,\gamma,t,\quad 2 < t.card \mathbin{\to} t.card < 2^n \mathbin{\to} \neg\mathit{IsGenuineSuperposition}(\mathit{qaoaState}\ n\ e\ \beta\ \gamma)\ t$, where `qaoaState` is the one phase-layer and one mixer-layer state and `IsGenuineSuperposition` means nonzero amplitudes exactly on $t$. The settlement is `result : ¬ claim`.

## Motivation

The source's statement would exclude every level-one QAOA output whose nonzero computational-basis support has an intermediate cardinality. A concrete support with four states on three qubits tests both that exclusion and the assumption restricting the mixing angle. The formal counterexample uses the target states with unequal first two bits.

## Gap

Issue [#22737](https://github.com/the-omega-institute/trureturing/issues/22737) records the bounded literature check before any Lean: the arXiv record lists v1, and the search found the source paper and unrelated QAOA work but no erratum, comment, or correction settling this counterexample. The repository had no record of this source.

`not-found-in-searched-scope`.

## Route

The module defines `mixer` as the sum of the single-qubit bit-flip permutation matrices, `qaoaState` as the mixer propagator applied to the phase propagator of `plusState`, `IsGenuineSuperposition` by exact nonvanishing support, and `claim` as the universal exclusion above.

The proof proceeds through the following declarations.

1. `mixer_action {n} (v : (Fin n → Bool) → ℂ) (x : Fin n → Bool)` identifies the mixer action at every $n$, vector $v$, and basis point $x$ with the sum over all single-bit flips.
2. `mixer_uniform` proves that at $n = 3$ the mixer sends the all-ones vector to three times that vector. `mixer_parity` proves that the parity vector sends to its negative.
3. `mixer_evolution (β : ℝ)` applies the eigenvector propagator lemma for every real $β$: the all-ones vector acquires phase $\exp(-3\beta i)$ and the parity vector acquires phase $\exp(\beta i)$.
4. `plus_three (x : Fin 3 → Bool)` gives the uniform three-qubit amplitude $(\sqrt{8})^{-1}$ for every $x$. `phase_layer` evaluates the phase propagator at the fixed `spectrum` and time $1$ as the stated sum of the all-ones and parity vectors.
5. `angle_phase` proves the identity $\exp(-3(\pi/8)i)=-i\exp((\pi/8)i)$. `output_amplitudes (x : Fin 3 → Bool)` then gives, for every $x$, zero amplitude when `x 0 = x 1` and the same coefficient otherwise. `output_coefficient_ne_zero` proves that this coefficient is nonzero.
6. `target_card` proves that the filtered target set has cardinality four, and `genuine_output` proves exact support on that set. `result` applies `claim` at $n=3$, `e = spectrum`, $\beta=\pi/8$, $\gamma=1$, and this target set, using $2<4<2^3$.

## Falsifier

The refutation would not match the source if the state, support predicate, or quantifiers differed. The module's `qaoaState` has the source's uniform `plusState`, diagonal real energy function, phase propagator, and transverse-field mixer. Its `IsGenuineSuperposition` requires exactly the nonzero coordinates in the target set and adds no normalization condition.

The formal `claim` has no hypothesis that the target set consists of ground states of the energy function. The selected `spectrum` assigns $\pi/2$ to the four states with unequal first two bits and $2\pi$ to the other four, but a separate ground-state predicate is not part of the formal declaration. The result therefore refutes the unrestricted `claim`; it does not settle a differently restricted formulation.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.lean.json`.
Declaration statements:
- `result`: `sha256:d8536f0e07a7240d42539a7c08164f49c22cc109b881c005a3a84d72b386301e`;
- `claim`: `sha256:ec48404c6a31436199a65e92802365177fa6c6818d6426ccdd586c6dfbf9b036`.

- **Definitions.** The module defines `mixer`, `qaoaState`, `IsGenuineSuperposition`, and `claim`, and proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2020 paper, preregistered in issue #22737 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: after inlining, the mixer eigenvector, propagator, finite-support, and arithmetic steps use existing declarations; the settlement is admitted as an external open-problem resolution | open-problem-resolution |
| `mixer`, `qaoaState`, `IsGenuineSuperposition`, `claim` | bind-only | none | definitions used by `claim` |
| the mixer, phase, amplitude, cardinality, and support helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. No escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** `result` proves `¬ claim`: the universal assertion that every real energy function and every pair of real angles fails to produce a genuine superposition on every target set with cardinality strictly between $2$ and $2^n$ is false. Its proof instantiates the universal assertion at $n=3$, `spectrum`, $\beta=\pi/8$, $\gamma=1$, and a four-element target set.

**Computed, not formalized:** a numerical matrix-exponential check of the counterexample, recorded by the orchestrator in #22737, agreed with the exact output and also satisfied the source's necessary condition, Eq. (condition2), at $\beta=\pi/8$.

**Argued, not formalized.**
- *Mechanism.* The phase layer separates the first-two-bit parity sectors. The mixer eigenvalues $3$ and $-1$ acquire relative phases at $\beta=\pi/8$ that cancel on the four coordinates with equal first two bits and leave one common nonzero coefficient on the other four. The named Lean lemmas formalize this cancellation for the selected instance; a general physical or algorithmic interpretation remains open.
- *Angle scope.* The source's four-angle restriction is contradicted by the tested $\pi/8$ instance, but the module does not classify all solutions of the source's necessary condition. Whether an exclusion restricted to the four odd multiples of $\pi/4$ holds remains open.
- *Size scope.* The result supplies one counterexample at $n=3$ and does not settle whether analogous counterexamples exist for every $n$, every intermediate cardinality, or other target sets.
- *Effect on source statements.* The unrestricted “more than $2$ but less than $2^n$” conclusion and the conjectured list of mixing angles cannot be retained as stated. The paper's one-target and two-target analyses and its IQP statements are outside `claim`; this settlement gives no formal conclusion about them.

## ASSUMED-UNVERIFIED

The literature check recorded in issue #22737 is bounded and does not establish exhaustive worldwide novelty, priority, or the absence of later corrections. The source's one-target and two-target results, IQP transfer, ground-state admissibility as a separate predicate, and classification of all solutions of Eq. (condition2) are not formalized here. The numerical checks in the issue and the broader scope statements in “What the settlement shows” are not formalized.
