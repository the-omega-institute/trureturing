---
slug: kvashchuk-2026-multicopy-design-refutation
bibkey: kvashchuk2026multicopy
doi: null
url: https://arxiv.org/abs/2604.26927v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.result
---

# A design with the maximally mixed state is not the most discriminable qubit ensemble at N = N′(2,3) + 1

## Problem

M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira and M. T. Quintino, *The most discriminable quantum states in the multicopy regime*, arXiv:2604.26927v3, study N equiprobable states received in k copies.
- The discriminability Discr is the largest average success (1/N) Σ_i Tr(M_i ρ_i^{⊗k}) over POVMs.
- A weighted state k-design (Definition 6) is a probability-weighted family whose weighted k-th tensor moment is Π_sym/Tr Π_sym, with every state of positive weight pure.
- N′(d,k) is the least size of such a design (§3.3).

For mixed states with N = N′(d,k) + 1, §11.2 proposes a design on N′(d,k) states together with the maximally mixed state I/d. §12, question 4, asks whether this construction is optimal in every dimension, citing numerical evidence for qubits. The verbatim statements are in [the literature note](../Library/QuantumBounds/kvashchuk2026multicopy.md).

Issue [#15935](https://github.com/the-omega-institute/trureturing/issues/15935) fixes the reading: for all d, k > 0, every weighted k-design on N′(d,k) states, appended with I/d, has Discr at least that of every ensemble of N′(d,k) + 1 states.

## Motivation

Designs are the optimal pure-state ensembles once N is large enough to contain one (the paper's Corollary 5.1). The question asks whether the same structure, padded by the least informative state, still governs the mixed-state optimum just above a design size. A negative answer means that mixed states contribute discriminability that no padding of a design captures.

## Gap

Issue #15935 records the literature check before any Lean:
- arXiv v3 (5 October 2026) still states the question;
- Figure 10's value Ω^q(2,7,3) = 0.6429 is a gradient-descent lower bound (§9.1), and the paper's upper-bound table stops at N = 6 for d = 2;
- web, Zenodo and citation searches found no settlement;
- the repository had no multicopy discrimination result.

`not-found-in-searched-scope`.

## Route

Take d = 2, k = 3, N = 7.
1. **N′(2,3) = 6.**
   - The six octahedron states with equal weights form a weighted 3-design.
   - No weighted 3-design has fewer than six states: the partial transpose of Π_sym/4 on the third factor has rank 6 (a 6 × 6 principal minor has determinant 1/746496), and each pure state of positive weight contributes rank one.
   - In a six-state design every weight is therefore positive, so every state is pure.
2. **The construction gives at most 9/14.** Let P be the projector onto the symmetric subspace (rank 4) and Y = P + (I − P)/8.
   - For every pure φ, Y ⪰ φ^{⊗3}φ^{⊗3}*, and Y ⪰ I/8.
   - So any six pure states with I/2, measured with any POVM, succeed with average at most Tr Y/7 = 9/14. This covers every design on N′(2,3) states, not only the octahedron.
3. **Better ensemble.**
   - The seven states are:
     - |0⟩⟨0| and |1⟩⟨1|;
     - the three trine states (|0⟩ + ω^j|1⟩)/√2 with ω = e^{2πi/3};
     - diag(2/3, 1/3) and diag(1/3, 2/3).
   - An explicit POVM gives the successes 51/64 (twice), 25/32 (three times) and 8/27 (twice).
   - The average is 1957/3024 > 9/14 = 1944/3024.

## Falsifier

The refutation would fail if the source's construction allowed a non-minimal design or a design whose states need not be pure. Definition 6 and §3.3 fix both, and step 1 shows that every minimal qubit 3-design consists of six pure states. It would also fail if Discr were not the uniform-prior optimum over all POVMs with N outcomes. The source defines it so in §2.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.lean` (742 lines).
- Public declarations:
  - the definitions `tensorPow`, `permOp`, `PiSym`, `IsWeightedDesign`, `DesignExists`, `Nprime`, `maxMixed`, `adjoin` and `Discr`;
  - `claim` and `result`.
- It reuses:
  - `FiniteStateChannel.DensityState` and `FiniteDiamondDistance.IsPure`;
  - `ConcealmentKernelNecessityRefutation.IsPOVM`;
  - `EquiprobablePgmActiveSetRefutation.success`;
  - `KickedIsingNegativityRefutation.partialTranspose`;
  - `StabilizerPairLocalUnitaryInequivalence.tensorOp` and `StabilizerPovmMaximalEntanglementRefutation.tensor_trace`;
  - `GibbsVariationalIdentity.gibbsState` at H = 0 with `gibbs_state_zero` (the maximally mixed state);
  - `RHLinalg.trace_mul_nonneg_of_posSemidef`;
  - Mathlib's `finFunctionFinEquiv`, `Finset.univ_perm_fin_succ`, `Equiv.Perm.decomposeFin`, `IsStarProjection.le_of_mul_eq_right` and PSD order.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.lean.json`, statement `sha256:5b7befcd8b3908c03409e2a5ec85d0202eaf479cc957b5f029a5178ab2da3c5e`.

Declaration statements:
- `result`: `sha256:a9fec4edca4d56d7fd970b99dbfe6919be70320a987bf8a45b9421d019ae5c36`;
- `claim`: `sha256:4ace109c5aed2945ef6d3703d41dab633379e3579987f9eb44b1ec715803e664`.

## Triage

Tier 1 question of a 2026 paper, preregistered in issue #15935 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every other declaration is a definition used by `claim` or a private helper on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `certified-instance` with basis `refutes` of `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the statement is false. At d = 2, k = 3, appending I/2 to a weighted 3-design on N′(2,3) = 6 states is not optimal among seven-state ensembles.

**Established inside the proof.**
- N′(2,3) = 6, and every six-state weighted 3-design consists of pure states with positive weights.
- Every such design with I/2 has Discr ≤ 9/14. So the counterexample also refutes the weaker reading that *some* minimal design with I/2 is optimal.
- The seven-state ensemble reaches at least 1957/3024.

**Argued, not formalized.**
- *Where the gain comes from.* The eight-dimensional three-copy space splits into the symmetric subspace (dimension 4) and its complement (dimension 4).
  - Pure-state cubes live in the symmetric subspace. There the construction's six design states reach the full trace 4, and the witness's five pure states reach 2·51/64 + 3·25/32 = 63/16, losing 1/16.
  - On the complement, I/2^{⊗3} contributes 4 · 1/8 = 1/2. Each biased state diag(2/3, 1/3)^{⊗3} or diag(1/3, 2/3)^{⊗3} puts weight 8/27 on a two-dimensional block (the complements of the symmetric vector in the Hamming-weight-1 and weight-2 sectors), for 16/27 > 1/2 in total.
  - The net gain is 16/27 − 1/2 − 1/16 = 13/432. Divided among seven states, this is the margin 13/3024.
- *The witness is not optimal.* The SDP optimum for these seven states is 0.6490 (#15935), above 1957/3024.

**Open.**
- The exact value of Ω^q(2,7,3).
- Whether the construction fails for other (d,k) with N = N′(d,k) + 1. The mechanism above suggests replacing I/d by biased mixed states concentrated on the non-symmetric sectors.

**Effect on the paper.**
- §12 question 4 has a negative answer already for qubits, where §11.2 reports numerical evidence for the construction.
- Figure 10's value 0.6429 = 9/14 is not Ω^q(2,7,3): the optimum is at least 1957/3024 ≈ 0.6472.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The two citing works named by the search seat in #15935 were not rechecked. The statements in "Argued, not formalized" are not formalized.
