---
slug: milekhin-adamska-preskill-2025-spacetime-schatten-subadditivity
bibkey: milekhinadamskapreskill2025observable
doi: null
url: https://arxiv.org/abs/2502.12240v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.result
---

# The spacetime density matrix violates the Audenaert-type Schatten subadditivity

## Problem

A. Milekhin, Z. Adamska and J. Preskill, *Observable and computable entanglement in time*, arXiv:2502.12240v2, define the spacetime density matrix T_AB of a subsystem A at time 0 and a subsystem B at time t.
- **The definition.** Tr(T_AB (O_A ⊗ 1_B)(1_A ⊗ O_B)) = ⟨O_A(0) O_B(t)⟩ = Tr(ρ O_A U† O_B U) (Eqs. (4), (9)); A and B "do not have to be related to each other in any particular way". The Schatten norm is ||M||_p = (Tr (M†M)^{p/2})^{1/p} (footnote a).
- **The conjecture.** After Audenaert's inequality for density matrices (Theorem 1, Eq. (24)), §IV item 9 states: "Conjecture 1 For any T_AB on a finite-dimensional H_A ⊗ H_B and p > 1: 1 + ||T_AB||_p ≥ ||Tr_A T_AB||_p + ||Tr_B T_AB||_p. (25)"

The verbatim statements are in [the literature note](../Library/QuantumBounds/milekhinadamskapreskill2025observable.md).

Issue [#17385](https://github.com/the-omega-institute/trureturing/issues/17385) fixes the reading: for every finite dimension, every density matrix ρ, every unitary U between the factorizations H_A ⊗ H_Ā and H_B ⊗ H_B̄ of the whole system, every T satisfying Eq. (9) for all O_A and O_B, and every real p > 1, inequality (25) holds.

The conjecture is refuted.

## Motivation

The spacetime density matrix extends reduced density matrices to subsystems at different times, and its Rényi-type quantities continue timelike entanglement in field theory. Subadditivity of the p-norms would give it the entropy inequality that density matrices satisfy; the authors report numerical evidence for it.

## Gap

Issue #17385 records the literature check before any Lean:
- arXiv v2 retains Conjecture 1;
- the full texts of twelve of the 32 citing works listed by Semantic Scholar were searched for Audenaert, subadditivity, Conjecture 1 and Schatten norms; none settles (25);
- the subadditivity violations of Fullwood–Parzygnat (arXiv:2306.01831) concern a generalized von Neumann entropy, not Schatten norms;
- no settlement was found on Zenodo, Crossref or in the repository Naixu-Guo/quantum-open-problems;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

1. **The witness.** Three qubits Q, R and S, with A = B = Q, the same qubit at times 0 and t. Put ψ = (63/65, 16/65), V the rotation with entries 4/5 and 3/5, and Z = diag(1, −1).
   - The initial state is |Ψ⟩ = (1/2) Σ_{r,s} Z^r ψ ⊗ |r, s⟩.
   - The evolution is U = Σ_{r,s} Z^s V Z^r ⊗ |r, s⟩⟨r, s|.
2. **Dephasing.** U is block diagonal in the controls, so in Tr(ρ (O_A ⊗ 1) U† (O_B ⊗ 1) U) only matching control blocks contribute. The average over r and s replaces O_A and O_B by their diagonal parts.
3. **The spacetime density matrix.** Hence T = diag(q_ij), where q_ij = ψ_i V_ji (Vψ)_j is the Kirkwood–Dirac quasiprobability of ψ for the two bases: T = diag(3024, 945, 576, −320)/4225.
4. **The violation at p = 2.**
   - ‖T‖₂² = 10471777/17850625 and the partial traces are diag(144, 25)/169 and diag(3969, 256)/4225.
   - Hence 1 + ‖T‖₂ ≤ 177/100 < 180/100 ≤ ‖Tr_A T‖₂ + ‖Tr_B T‖₂.

## Falsifier

The refutation would not settle the conjecture if:
- the module's T were not a spacetime density matrix in the source's sense;
- its norm differed from footnote a's;
- its partial traces were exchanged;
- `claim` assumed something the source does not, such as A and B exhausting the system.

The module quantifies over all finite subsystem factorizations, density matrices, whole-system unitaries and matrices satisfying Eq. (9), and every real p > 1. It uses the frozen `schattenNorm`, which is footnote a's formula, and the frozen partial traces.

## Evidence

The canonical source is `D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.lean` (207 lines, `generality: I`, `utility: kind=certified-instance; basis=refutes`).
- It defines `claim` and the witness `witnessPsi`, `witnessV`, `witnessJointPsi`, `witnessRho`, `witnessBlock`, `witnessU` and `witnessT`, and proves `result : ¬ claim`.
- It reuses:
  - the frozen `schattenNorm`, `PartialTraceMutualInformation.partialTraceLeft` and `partialTraceRight`;
  - `FiniteDimensional.qubitZ` and `PureStateHandshake.rankOneDensity`;
  - three lemmas made public for this settlement: `TwoPositiveTransitionTrace.trace_rank_one`, and `ChenKatoBrandaoCMIRefutation.partialTraceRight_diagonal` and `partialTraceLeft_diagonal`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations:
  - `result` is the designated refutation result and is exempt (CLAUDE.md §3.9).
  - `partialTraceRight_diagonal` and `partialTraceLeft_diagonal` are registered in `Reg/D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.lean`. Both are `declared_unresolved`, with the judge reading `IE-C050 … reason=unclassified_form rule=source.descriptor_actual`.
  - `trace_rank_one` is registered in `Reg/D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.lean`. It is also `declared_unresolved`, with the same judge reading.
  - Their escape audit is incomplete; the gaps are recorded in [#17417](https://github.com/the-omega-institute/trureturing/issues/17417) and [#16937](https://github.com/the-omega-institute/trureturing/issues/16937).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.lean.json`, statement `sha256:f2676ea1fdb8499b6e1e997c9608670c9c38ec8b77213c7ce92a8f34a658d40d`.

Declaration statements:
- `result`: `sha256:d16bcb865dc244525ea931c9cee307658ba20b76dc68b08a57d8c8ab8a91ccea`;
- `claim`: `sha256:a27f14f327aa0d1d09c64e34361765552f0c39bcc61db6672ce132bd566b0a75`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the density hypotheses, the unitarity, Eq. (9), the partial traces and the norm values are instantiations of frozen D5 and pinned Mathlib results followed by normalization and rational arithmetic | open-problem-resolution |
| the density, unitarity, Eq. (9), partial-trace, norm and violation helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 9 private theorems are bind-only helpers consumed on the proof path of `result`, and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

## Triage

### What the settlement shows

**Refuted by `result`:** Conjecture 1 fails for the spacetime density matrix of one qubit at two times, with two control qubits as the rest of the system, at p = 2.

**Computed, not formalized** (orchestrator, SymPy exact arithmetic, recorded in #17385): the irrational example of the search seat (T = diag(3, 3, 3, −1)/8, A = Q at time 0 and B = S at time t) violates (25) at p = 4.

**Argued, not formalized.**
- The mechanism is negativity of the Kirkwood–Dirac quasiprobability. When the rest of the system dephases both insertions, T_AB is diagonal with entries q_ij = ψ_i V_ji (Vψ)_j, which can be negative while their marginals |ψ_i|² and |(Vψ)_j|² are probabilities.
- A density matrix cannot have a negative eigenvalue, so this mechanism is unavailable in Theorem 1. The source's Theorem 2 case, an initial state |ψ_Ā⟩⟨ψ_Ā| ⊗ ρ_A, rules out the correlation between A and its complement that the dephasing at time 0 uses.

**Open.**
- Inequality (25) when A and B are the whole system before and after the evolution, so that T_AB = J(ρ ⊗ 1) as in Eq. (6).
- The infimum of the exponents p > 1 at which (25) fails.

**Effect on the paper.** Conjecture 1 is false in the stated generality. The numerical evidence of the paper is consistent with the whole-system case, which remains open.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
