---
slug: girard-plavala-sikora-2021-jordan-compatibility-refutation
bibkey: girardplavalasikora2021jordan
doi: 10.1038/s41467-021-22275-0
url: https://arxiv.org/abs/2009.03279v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/JordanCompatibilityRefutation.result
---

# Compatible quantum channels need not be Jordan compatible

## Problem

M. Girard, M. Plávala and J. Sikora, *Jordan products of quantum channels and their compatibility*, Nat. Commun. 12, 2129 (2021), arXiv:2009.03279v1, study when two channels can be implemented jointly.
- **Jordan compatibility.** For a Hermitian A on X ⊗ X_1 ⊗ X_2 with Tr_{X_1}(A) = Tr_{X_2}(A) = J(1_{L(X)}), the generalized Jordan product Φ_1 ⊙_A Φ_2 has Choi matrix (1 ⊗ Φ_1 ⊗ Φ_2)(A) (Definition 25). The channels are Jordan compatible if this product is completely positive for some such A (Definition 27). Jordan compatibility implies compatibility (Proposition 26), and for invertible channels the converse holds (Theorem 30).
- **The conjecture.** After Theorem 30: "the question of whether compatibility of channels is equivalent to Jordan compatibility remains open. We conjecture that such a pair of channels does not exists."

The verbatim statements are in [the literature note](../Library/QuantumChannels/girardplavalasikora2021jordan.md).

Issue [#17171](https://github.com/the-omega-institute/trureturing/issues/17171) fixes the reading: for every d, every compatible pair of channels on M_d is Jordan compatible. The conjecture is refuted at d = 4.

## Motivation

For a fixed pair of channels, Jordan compatibility is a semidefinite feasibility condition on A, linear in A. Equivalence with compatibility would turn the compatibility question into a search over the operators A, with the Jordan product as a canonical candidate. The source proves the equivalence for invertible channels and for several special classes (Propositions 21–22, Lemmas 23–24), and leaves the noninvertible case open.

## Gap

Issue #17171 records the literature check before any Lean:
- arXiv v1 is the only version, and the journal version states the same open problem;
- a web search found no counterexample or settlement;
- searches by the search seat of the citing and related works (Duarte–Catani–Drumond, Hsieh–Lostaglio–Acín, Guo–Luo–Zhang, Jokinen et al.) found none;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Let P = [[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]] and Q = diag(1, 1, −1, −1). Then P² = Q² = I and PQ + QP = 0.
1. **The channels.** With (S_1, …, S_4) = (P, −P, Q, −Q), take E_i = (5I + 4S_i)/20 and F_j = (4I + 3S_j)/16. Put Φ(R) = Σ_i tr(E_i R)|i⟩⟨i| and Ψ(R) = Σ_j tr(F_j R)|j⟩⟨j|; both are measure-and-prepare channels.
2. **Compatibility.** With h_ij = 1/64 + (15/16)δ_ij, the channel Γ(R) = Σ_{ij} h_ij tr(E_i R)|i, j⟩⟨i, j| has marginals Φ and Ψ, since Σ_j h_ij = 1 and Σ_i h_ij E_i = F_j.
3. **The blocks.** For any admissible A, (1 ⊗ Φ ⊗ Ψ)(A) is block diagonal with blocks B_ij = (1 ⊗ tr(E_i ·) ⊗ tr(F_j ·))(A). Each block is positive semidefinite as a compression.
4. **The marginals.** Equation (117) and E_1 + E_2 = E_3 + E_4 = F_1 + F_2 = F_3 + F_4 = I/2 make the four matrices G_st = 4B_{i(s), j(t)}, s, t = ±1, a joint measurement: Σ_t G_st = (I + s(4/5)P)/2 and Σ_s G_st = (I + t(3/4)Q)/2.
5. **The contradiction.** H_st = (3/2)I − sP − tQ = (1/4)(2I − sP − tQ)² is positive semidefinite, so Σ_{st} tr(H_st G_st) ≥ 0. The marginals give Σ_{st} tr(H_st G_st) = 6 − 16/5 − 3 = −1/5.

## Falsifier

The refutation would not hold if:
- the module's Jordan compatibility were stronger than Definition 27, for example by requiring A to be positive or the partial traces to be normalized;
- its compatibility were weaker than the source's;
- its channels were not channels.

The module requires A only to be Hermitian. In (117) it uses the Choi matrix of the identity, `MatrixMap.choi_matrix (LinearMap.id)`, which is Σ_{ij} E_{ij} ⊗ E_{ij}, the source's J(1_{L(X)}); for the identity this matrix does not depend on the order of the two factors. It states complete positivity of Φ ⊙_A Ψ as positive semidefiniteness of (1 ⊗ Φ ⊗ Ψ)(A). Its channels satisfy the frozen predicate `IsChannel`, a finite Kraus family with Σ_k K_k^† K_k = 1.

## Evidence

The canonical source is `D5/S3/QuantumChannels/JordanCompatibilityRefutation.lean` (571 lines).
- It defines `Mat`, `Map`, `traceX1`, `traceX2`, `jordanAction`, `Compatible`, `JordanCompatible` and `claim`, and proves `result : ¬ claim`.
- Channels are the frozen `PureProgramQubitObstruction.IsChannel`, and the joint channel's marginals use the frozen `partialTraceLeft` and `partialTraceRight` of `PartialTraceMutualInformation`.
- The Kraus families of the measure-and-prepare channels are built from `rowReset`, with their action given by `row_reset_action`, both in the frozen `KrausCompletion`.
- The Choi matrix `MatrixMap.choi_matrix` lives in `FiniteKrausRepresentation`, which is Closed but not frozen.
- The facts P² = Q² = I and the Hermiticity of P and Q come from `Matrices.obs_herm_sq`, `XITable` and `ZITable` of the frozen `RankOfContextualityNonPowerTwo`. The trace inequality of step 5 is `RHLinalg.trace_mul_nonneg_of_posSemidef` of the frozen `RankTrace`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/JordanCompatibilityRefutation.lean.json`, statement `sha256:a384df930e93a472ad01d1913dc8ff3fa1e8ceb1b1eae5e06789994d79b08433`.

Declaration statements:
- `result`: `sha256:5ed149fa3f530a9c28ad7338ae1ce7a91de4710bf0108cb3cb99c0d6226bf010`;
- `claim`: `sha256:a971ef163466bc839b7404461bef0760cf23243844b3f4adfe05d5096209e83f`.

## Triage

Tier 1 conjecture of a 2021 paper, preregistered in issue #17171 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the channel and Choi facts, the block decomposition, the partial-trace identities, the Gram certificate and the trace sum are instantiations of frozen D5, Closed D5 and pinned Mathlib results followed by normalization | open-problem-resolution |

Every other public declaration is a definition used by a public statement. The module's 37 private theorems are bind-only helpers consumed on the proof path of `result`, and its 23 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the two measure-and-prepare channels Φ and Ψ on M_4 above are compatible but not Jordan compatible.

**Computed, not formalized** (orchestrator, NumPy, 15 October 2026):
- the effects have smallest eigenvalues 1/20 and 1/16;
- the Choi matrix of Γ has smallest eigenvalue 7.8 × 10⁻⁴, so even the exhibited joint channel is interior.

**Argued, not formalized.**
- The mechanism: Jordan compatibility forces the four blocks G_st to form a joint measurement of the unsharp anticommuting observables (4/5)P and (3/4)Q, and step 5 shows that no such joint measurement exists. Here (4/5)² + (3/4)² = 1.2025 > 1.
- The full four-outcome measurements {E_i} and {F_j} are jointly measurable (through h), but the output-range identities of Φ and Ψ, together with (117), fix the coarse-grained blocks. This is why compatibility does not lift to Jordan compatibility.
- Both channel superoperators have rank 3, since the effects span {I, P, Q}. So the counterexample lies in the noninvertible case left open by Theorem 30.

**Open.**
- The smallest dimension d for which compatible but not Jordan compatible pairs exist, which this settlement does not determine; it gives d = 4.

**Effect on the paper.** Compatibility is not equivalent to Jordan compatibility in general. Theorem 30 and the density result of §6 remain as stated.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
