---
slug: salazar-shahbeigi-2025-passive-memory-refutation
bibkey: salazar2025dephasing
doi: 10.1088/1402-4896/adda94
url: https://arxiv.org/abs/2403.19247v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.result
---

# A passive incoherent memory realizes a non-classical dephasing superchannel in dimension 3

## Problem

R. Salazar and F. Shahbeigi, *Dephasing noise simulation for coherence-generating devices*, Phys. Scr. **100** (2025) 085110, arXiv:2403.19247v1, study dephasing superchannels, which multiply the Choi matrix J(E) of every channel E entrywise by a Gram matrix C. Such a superchannel is implemented with a memory state τ and encoding and decoding channels on system ⊗ memory: Ξ(E)(ρ) = Tr_M[N_de((E ⊗ id)(N_en(ρ ⊗ τ)))] (Eq. (9)).
- The memory is *passive* if its marginal after encoding does not depend on the input (Definition 2).
- C is *classical* if C = Σ_i q_i C₁^{(i)} ⊗ C₂^{(i)}, the Gram matrix of dephasing channels applied before and after E under classical randomness.

Proposition 1 shows that for qubit channels a passive memory realizes exactly the classical Gram matrices. §V.C asks "whether a passive memory in any dimension is equivalent to a classical memory". §V.D argues that it is, for incoherent implementations. The verbatim statements are in [the literature note](../Library/QuantumChannels/salazar2025dephasing.md).

Issue [#15829](https://github.com/the-omega-institute/trureturing/issues/15829) fixes the reading:
- every system dimension d and finite memory dimension r;
- every memory state and every Kraus encoder and decoder;
- the source's output-first normalised Choi matrix and Eq. (13)'s equal diagonal blocks;
- passivity for every pair of input density matrices;
- classical Gram matrices as finite convex combinations of Kronecker products of unit-diagonal positive semidefinite matrices.

## Motivation

The question decides whether memory that stores no information about the input can still produce gate noise beyond classically correlated pre- and post-dephasing. In the source's framework, that is noise needing quantum correlations between system and memory rather than input-dependent storage.

## Gap

Issue #15829 records the literature check before any Lean:
- arXiv lists only v1, and the journal version keeps the question and the §V.D argument;
- the only citing work (arXiv:2412.15466) does not treat passive memories;
- Roszak, PRA 98, 052344 (2018), gives a related controlled-dephasing circuit and its system–environment entanglement, but not the classical simulability of the induced Gram matrix;
- Zenodo, Crossref and web searches return no settlement;
- the repository had no dephasing-superchannel result.

`not-found-in-searched-scope`.

## Route

Take d = 3, a qubit memory with τ = I/2, the controls U₀ = I, U₁ = X, U₂ = Z, the controlled unitary W = Σ_i |i⟩⟨i| ⊗ U_i, and N_en = N_de = W(·)W†.
1. **Passive.** The memory marginal of W(ρ ⊗ τ)W† is Σ_i ρ_ii U_i τ U_i† = τ for every density matrix ρ.
2. **Dephasing superchannel.** For every channel E, J(Ξ(E)) = C ⊙ J(E) with C_{(i,j),(k,l)} = Tr(U_i U_j U_l† U_k†)/2. C is a Gram matrix with identity diagonal blocks.
3. **Not classical.** A classical C = Σ q_i P_i ⊗ Q_i has positive semidefinite partial transpose Σ q_i P_i ⊗ Q_iᵀ. Here the partial transpose has, on the coordinates (0,0), (1,1), (2,2), the block [[1,1,1],[1,1,−1],[1,−1,1]], since Tr(ZXZX)/2 = −1. The vector (−1,1,1) gives the value −3.

## Falsifier

The refutation would fail if a classical memory admitted more than the convex combinations of Kronecker products of dephasing Gram matrices; the source defines it by Proposition 1 (ii). Non-commutation of the controls is essential: for the commuting controls I, X, X the partial transpose is positive semidefinite (NumPy control in #15829).

## Evidence

The canonical source is `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.lean` (364 lines).
- Public declarations:
  - the definitions `Mat`, `KrausChannel`, `act`, `stateMatrix`, `appendMemory`, `discardMemory`, `implemented`, `choi`, `Gram`, `DephasingGram`, `Passive`, `ClassicalGram` and `Implements`;
  - `claim` and `result`.
- It reuses:
  - `FiniteStateChannel.DensityState`;
  - `FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus`/`kron`, and `MatrixMap.choi_matrix` (normalised by (d)⁻¹);
  - `PartialTraceMutualInformation.partialTraceLeft`/`partialTraceRight`;
  - `StructuredNegativityCoincidenceRefutation.partialTransposeB`;
  - `FiniteDimensional.qubitX`/`qubitZ`;
  - Mathlib's `Matrix.blockDiagonal`, `Matrix.kronecker`, `Matrix.hadamard` and PSD order.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.lean.json`, statement `sha256:c82e1aa1755f3cb5b19284f4cedcc2fee8c2b62250df90bf049cba8bc9010073`.

Declaration statements:
- `result`: `sha256:4a7473110e09ede3d71726c3e6b75b5566daf4f1aad710fdc9f6827c1ad9f46d`;
- `claim`: `sha256:894eac761c558c1034350fd9b52a009048f934e0efdc50819df690306965e7fe`.

## Triage

Tier 1 question of a 2025 paper, preregistered in issue #15829 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every other declaration is a definition used by `claim` or a private helper on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `certified-instance` with basis `refutes` of `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the statement is false. At d = 3 there is an implementation with a passive memory whose dephasing superchannel has a non-classical Gram matrix.

**Established inside the proof.**
- The implementation is passive for every input.
- It realizes C ⊙ J(E) for every Kraus channel E.
- Every classical Gram matrix has a positive semidefinite partial transpose, while C does not.

**Argued, not formalized.**
- W is a monomial unitary and τ is incoherent, so the implementation is maximally incoherent. It is therefore also a counterexample to the §V.D argument, whose step from an incoherent, input-independent memory marginal to a classical simulation does not hold: the marginal condition allows system–memory correlations.
- For unitary controls with U₀ = I on a memory of dimension r with τ = I/r, the same block of the partial transpose has quadratic form −‖U₁U₂ − U₂U₁‖²_HS / r along (−2, 1, 1). Hence non-commuting U₁, U₂ give a non-classical C for every d ≥ 3 (further controls equal to I leave the block unchanged; NumPy: d = 4 with controls I, X, Z, XZ gives eigenvalue −2). The hypothesis U₀ = I is needed: for (U₀, U₁, U₂) = (X, X, Z) the form along (−2, 1, 1) is +4, and C is classical.

**Open.** Whether separability of C together with fixed diagonal entries of its off-diagonal blocks implies a passive realization in higher dimensions, the source's second question, is not addressed.

**Effect on the paper.** The §V.C question has a negative answer from dimension 3 on. The §V.D reasoning that "the simulation must be equivalent to that of a classical memory" does not hold for incoherent passive memories.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The family statements in "Argued, not formalized" are not formalized.
