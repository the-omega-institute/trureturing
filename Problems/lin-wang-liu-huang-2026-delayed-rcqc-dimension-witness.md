---
slug: lin-wang-liu-huang-2026-delayed-rcqc-dimension-witness
bibkey: lin2026rcqc
doi: 10.48550/arXiv.2606.31103
url: https://arxiv.org/abs/2606.31103v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.result
---

# Every data qubit of the delayed remote-controlled circuit violates the dimension witness S ≤ 4

## Problem

P. Lin, D. Wang, Y. Liu and A. Huang, *Nonclassicality of a delayed remote-controlled quantum computing model*, arXiv:2606.31103v1, study a delayed 1-U-M remote-controlled quantum computing circuit (§III, Eq. (3), Fig. 3):
- a Bell pair on the program and remote-control qubits;
- a controlled-A and a controlled-B gate on the data qubit, with A = diag(1, e^{i(β+δ)}) and B = [[0, −1], [e^{i(β−δ)}, 0]];
- a Hadamard and a computational-basis measurement on the program qubit;
- the remote measurements onto |P*_U⟩ = a₀*|0⟩ + a₁*|1⟩, with a₀ = e^{−i(β+δ)/2} cos(γ/2) and a₁ = e^{−i(β−δ)/2} sin(γ/2), whose β and δ must equal those of the gates.

Read as a prepare-and-measure scenario with four preparations and two binary measurements, a violation of the dimension witness S = E₀₀ − E₀₁ − E₁₀ + E₁₁ − E₂₀ − E₂₁ + E₃₀ + E₃₁ ≤ 4 (Eq. (2)) rules out every classical causal explanation with preshared correlations. Simulated annealing found violations at all 900 points of a 30 × 30 grid of initial data qubits, and the authors write: "It is reasonable to conjecture that for any arbitrary initial data qubit |d⟩, there exists a measurement on the data qubit and specific parameter values for β, δ, γ₀ and γ₁, such that, under an appropriate labeling strategy, violating the dimension witness S ≤ 4". The verbatim statements are in [the literature note](../Library/QuantumBounds/lin2026rcqc.md).

Issue [#16465](https://github.com/the-omega-institute/trureturing/issues/16465) fixes the reading. For every unit data vector d there are β, δ, γ₀, γ₁ and a unit data-measurement vector b such that, with the source's labeling x = 2m + n:
- every preparation has positive probability;
- S > 4.

It is proved.

## Motivation

A violation for every input lets a client certify the nonclassicality of the delegated computation whatever data qubit it supplies, without trusting the server's devices. The source's evidence was a finite grid search.

## Gap

Issue #16465 records the literature check before any Lean:
- arXiv v1 is the only version;
- Semantic Scholar lists no citing work;
- the Pith review page gives no proof or construction;
- Zenodo and web searches return no settlement;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Write d = (d₀, d₁) and take
- β = 0 and δ = −arg(conj(d₀)·d₁);
- γ₀ = π/2 and γ₁ = π.

Then:
1. **The data branches.** u = A d and w = e^{iδ}·B d form an orthonormal basis of the data qubit; the phase of δ removes the relative phase of d.
2. **The circuit state.** After the gates and the Hadamard, the state is (1/2) Σ_m |m⟩_P ⊗ (A d ⊗ |0⟩_R + (−1)^m B d ⊗ |1⟩_R).
3. **The data measurement.** b = cos(π/8)·u + sin(π/8)·w. Every pair (m, n) then has probability 1/4.
4. **The remote measurements.** With γ₀ = π/2 the remote vector is (1, e^{iφ})/√2 up to phase, and with γ₁ = π it is |1⟩ up to phase. The correlators are E = (√2/2)·[[1, −1], [−1, 1], [−1, −1], [1, 1]].
5. **The witness.** S = 8·(√2/2) = 4√2 > 4.

## Falsifier

The proof would not settle the conjecture if:
- the module's circuit, gates or remote vectors differed from Eq. (3) and Fig. 3;
- its probabilities were not the Born-rule probabilities of the program, data and remote outcomes;
- its S differed from Eq. (2);
- the parameters of the gates and of the remote measurement were not shared.

The module fixes the source's first labeling (m₀,n₀), (m₀,n₁), (m₁,n₀), (m₁,n₁) ↦ 0, 1, 2, 3. A labeling that yields S > 4 is one appropriate labeling in the source's sense.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.lean` (575 lines).
- It defines `gateA`, `gateB`, `circuitState`, `remote`, `dataProjector`, `prepProb`, `jointProb`, `E`, `S` and `claim`, and proves `result : claim`.
- It uses the frozen `bellVector` of `D5/S3/QuantumBounds/CHSHWitness` and `hadamard` of `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence`, and pinned Mathlib for complex exponentials, `Complex.arg` and π/8 trigonometry.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.lean` reads out the data-measurement vector b of `claim`. Its rejected realization, the zero vector, fails the unit-norm condition at the input |0⟩. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.lean.json`, statement `sha256:050f4104a92a092e93371ab04e79527ad658b874957e884ca39183de93626f02`.

Declaration statements:
- `result`: `sha256:5b7e2b0a75fb55982b0dd3925d43fec4f826b46ec30cd69fe8fc6d5cbc96b07f`;
- `claim`: `sha256:98b99d8d41658c3ff4e72d84ca54d94107f3469fa605b167d2cf754aeebbc237`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #16465 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the construction is an instantiation followed by complex-number normalization | open-problem-resolution |
| the phase, frame, rotation, branch, probability and correlator helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every unit data qubit, one explicit choice of β, δ, γ₀, γ₁ and data measurement makes every preparation probability equal to 1/4 and gives S = 4√2.

**Computed, not formalized** (orchestrator, NumPy model of the source's circuit, 14 October 2026):
- over 2000 random data qubits, the construction gives S = 4√2 to within 5 × 10⁻¹⁵, with every preparation probability 1/4;
- with γ₀ = γ₁ the two remote measurements coincide and, over 3000 random settings, S never exceeds 3.957.

**Argued, not formalized.**
- 4√2 is the largest value of S for qubit preparations and binary qubit measurements, so the construction is optimal for every input.
  - Write the two observables as M_y = a_y·I + m_y·σ with |a_y| + |m_y| ≤ 1.
  - Maximizing each preparation separately gives S ≤ 2|m₀ − m₁| + 2|m₀ + m₁|: the identity parts cancel between the rows of opposite sign.
  - Then 2|m₀ − m₁| + 2|m₀ + m₁| ≤ 2·√(2(|m₀ − m₁|² + |m₀ + m₁|²)) = 4·√(|m₀|² + |m₁|²) ≤ 4√2.
- The parameters depend on the input only through the relative phase arg(conj(d₀)·d₁). The amplitudes |d₀| and |d₁| play no role, because A d and B d are always orthonormal.
- The construction does not certify an unknown input: δ and the data measurement must be chosen for the given d, as the source's quantifier order allows.

**Open.**
- Whether one apparatus, with β, δ, γ₀, γ₁ and the data measurement independent of d, violates S ≤ 4 for every input.
- The source's broader conjecture in §IV about other programmable gate arrays.

**Effect on the paper.** The conjecture of §III is a theorem with an explicit construction attaining S = 4√2 at every input, and the grid evidence of Fig. 4(c) is replaced by a proof.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
