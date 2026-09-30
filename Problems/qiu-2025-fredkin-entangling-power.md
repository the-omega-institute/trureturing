---
slug: qiu-2025-fredkin-entangling-power
bibkey: qiu2025multipartite
doi: 10.1103/PhysRevA.111.022407
url: https://arxiv.org/abs/2410.15253v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.result
---

# The four-qubit Fredkin gate generates more than two ebits across AD:BC

## Problem

X. Qiu, Z. Song and L. Chen (arXiv:2410.15253, quant-ph; Phys. Rev. A 111,
022407 (2025)) define the entanglement generation `K_{L:L^c}(U)` of a
multipartite gate as the supremum, over pure inputs `ψ_i` of each party with a
local auxiliary system `R_i`, of the von Neumann entropy in ebits of the
reduced state on `L` of `U(ψ_1 ⊗ ⋯ ⊗ ψ_n)`. For the four-qubit Fredkin gate
`F_4 = (|00⟩⟨00| + |01⟩⟨01| + |10⟩⟨10|)_{AB} ⊗ I_{CD} + |11⟩⟨11|_{AB} ⊗ (S_2)_{CD}`
they prove `K_{AD:BC}(F_4) ∈ [2, log_2 5]` and state:

> Further we conjecture that $K_{AD:BC}(F_4)\leq 2$ by numerical results and
> thus have the following. The entanglement generation $K_{AD:BC}(F_4)=2$.
> Hence the entangling power of a four-qubit Fredkin gate $F_4$ is equal to
> two ebits.

Issue #11460 fixes the reading. Each auxiliary system has any finite
dimension `d_i ≥ 1`, the inputs are unit vectors, `F_4` acts as the identity on
the auxiliary systems, and the entropy is taken on `A R_A D R_D`. The formal
`claim` is the first sentence, `K_{AD:BC}(F_4) = 2`; the result refutes it.

## Motivation

For the three other cuts the paper determines the entanglement generation
exactly, and the conjecture would fix the entangling power of `F_4` at two
ebits. The frozen declaration
`D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.result` shows that
one product input already generates `2.00034…` ebits across `AD:BC`. Since the
entangling power is the maximum over cuts, it also exceeds two ebits; that
consequence is not formalized.

## Gap

Issue #11460 preregisters the reading, the counterexample and the literature
check. arXiv has only v1, and the published abstract repeats the range
`[2, log_2 5]`. INSPIRE lists 5 citing records; a full-text scan of all five
finds no mention of the Fredkin gate.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Take `ψ_A = (3|0⟩ + 20|1⟩)/√409` and `ψ_B = √(2/75)|0⟩ + √(73/75)|1⟩` with
   one-dimensional auxiliary systems, and `ψ_C = ψ_D = ½(|00⟩ + |01⟩ + |10⟩ − |11⟩)`
   on a qubit and an auxiliary qubit, a maximally entangled state with rational
   amplitudes.
2. The output amplitude matrix across the cut is `M = D_A N D_B`, with `D_A`,
   `D_B` diagonal and `N` rational. So `M M^*` has the characteristic polynomial
   of the rational matrix `N (D_B D_B^*) N^T (D_A^* D_A)`, which equals
   `P diag(μ) P^{−1}` for an explicit rational `P`. Hence the reduced state has
   spectrum `μ = (1752, 1460, 1460, 1460, 3, 0, 0, 0)/6135`.
3. Its entropy, `Σ −μ log μ`, exceeds `2 log 2`. The margin is
   `(4380 log(6135/5840) + 1752 log(6135/7008) + 3 log(6135/12))/6135 > 0`, from
   Taylor bounds with remainder and `e < 2.7182818286`.
4. The set of generated values therefore contains a value above 2. If it is
   bounded above, its supremum exceeds 2; otherwise the supremum is 0.

## Falsifier

The answer would change if the auxiliary systems of `A` and `B` were required
to be qubits: appending `|0⟩` auxiliary qubits to `ψ_A` and `ψ_B`, as in the
paper's own input `|10⟩_{AR_A}`, leaves the reduced spectrum unchanged, but
this remark is not formalized. It would also change if the entropy were taken
without the auxiliary systems. The paper's definition attaches `R_i` to its
party, and its own lower-bound input uses auxiliary qubits for `C` and `D`.

## Evidence

An independent NumPy state-vector computation of the full six-factor output
(issue #11460) gives the spectrum above and `2.000344215` ebits. It gives
exactly 2 ebits for the paper's Case-4 input, a positive control.

The canonical source is
`D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.lean`. Its public
declarations are `Party`, `swapGate`, `fredkin4`, `output`,
`generatedEntanglement`, `entanglementGeneration`, `claim` and `result`. The
frozen module state has statement identity
`sha256:96a43ff10b04209f9a9c91d1f3ef89e1b6691fcc699fdea736fe10b9071db905`.
The result declaration has statement identity
`sha256:8e2cc1a5962a8cec92241e5f98f01f7f66fbd7c87b4a4a457b1e01aedd7db3d2`.
The Freeze event is
`sha256:51b3d0ed2f2a5803accd0bdf668654a1428ed980fd3e1355acaf6ffb83435566`.
Its one project-level frozen prerequisite is the Freeze event
`sha256:76851b264ebdd7658b094fafbdf64c162585924cf680081f9b1e8877815dcbd8` of
`D5/S3/Quantum/Information/InputInformationBalance`, the only project import;
through it the module uses `DensityState`, `vonNeumannEntropy`,
`marginalRight`, `entropy_eq_sum` and `spectral_sum_eq_of_charpoly_prod`. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or
new axiom.

## Triage

Tier 1 conjecture from a 2025 quant-ph paper, preregistered in issue #11460
before any Lean. `theorem`; resolution `refuted`. The public theorem has
`proof_shape: bind-only`: it evaluates the definitions at the explicit input.
Its admission basis is `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

## ASSUMED-UNVERIFIED

The published Phys. Rev. A full text was not read, so it is unverified whether
the conjecture was edited there. The bounded literature check does not
establish exhaustive worldwide novelty, priority, or the absence of an
independent answer. The Lean kernel does not authenticate the external source
or its version history.
