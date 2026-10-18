---
slug: girard-2017-binegativity-lower-bound
bibkey: girard2017binegativity
doi: 10.48550/arXiv.1701.02724
url: https://arxiv.org/abs/1701.02724v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.result
---

# The two-qubit binegativity lower bound at fixed negativity

## Problem

M. W. Girard and G. Gour, *The binegativity of two qubits*, arXiv:1701.02724v3 (2017), Eq. (8):

> Based on numerical evidence, we conjecture that the binegativity is bounded below by $\frac{\nu}{2} \left(1+\frac{c_\nu}{\sqrt{(1-c_\nu)^2+c_\nu^2}}\right) \leq N_2(\sigma)$ where we define $c_\nu=\sqrt{2\nu(\nu+1)}-\nu$.

Here $\nu = N(\sigma) = 2\operatorname{Tr}[(\sigma^\Gamma)_-]$ and $N_2(\sigma) = \operatorname{Tr}[(\sigma^\Gamma)_-] + 2\operatorname{Tr}[(((\sigma^\Gamma)_-)^\Gamma)_-]$, with $X_-$ the negative component of a self-adjoint $X$. The verbatim statements are in [the literature note](../Library/QuantumStates/girard2017binegativity.md).

Issue [#18490](https://github.com/the-omega-institute/trureturing/issues/18490) fixes the reading: for every two-qubit density matrix σ, with the partial transpose on the second qubit, the inequality holds. This is proved.

## Motivation

The binegativity is a computable quantity that the paper introduces to study entanglement conversion. Eq. (8) is its conjectured lower boundary at fixed negativity; the source notes that the boundary is the binegativity of the states $\sigma_c = c|\phi^+\rangle\langle\phi^+| + (1-c)|10\rangle\langle 10|$ of Eq. (6) with negativity ν. Two other conjectures of the paper are settled in this repository: the upper inequality of Eq. (9) is refuted ([dossier](girard-2017-binegativity-upper-bound.md)), and so is the LOCC monotonicity ([dossier](girard-2017-binegativity-monotonicity.md)). Eq. (8) fixes ν alone and is a separate statement.

## Gap

Issue #18490 records the literature check before any Lean:
- arXiv v3 is the latest version and keeps Eq. (8) as a conjecture;
- the citing work arXiv:1711.03717 gives N₂ for pure states but no sharp bound at fixed N (reported by the search seat);
- the bounds of Verstraete–Verschelde and Verstraete–Audenaert–Dehaene–De Moor give only the weaker 2αβ ≥ ν/c_ν (reported by the search seat);
- the repository's other two dossiers on the paper do not treat Eq. (8).

`not-found-in-searched-scope`.

## Route

Write Γ for the partial transpose on the second qubit.
1. **One negative eigenvalue.** σ^Γ is nonnegative on product vectors, and every two-dimensional subspace of ℂ² ⊗ ℂ² contains a nonzero product vector. So σ^Γ has at most one negative eigenvalue. If it has none, both sides vanish.
2. **Schmidt coordinates.** Let −λ < 0 be the negative eigenvalue and ψ a unit eigenvector, so that (σ^Γ)₋ = λψψ† and ν = 2λ. Local unitaries put ψ in the form α|00⟩ + β|11⟩ and leave N and N₂ unchanged.
3. **The weight bound.** With x the sum of the |00⟩ and |11⟩ diagonal entries of σ, the eigenvalue equations and the positivity of σ on the 01,10 block give ν(2x + ν) ≤ (1 − x)², so x ≤ 1 − c_ν.
4. **The Schmidt product.** The eigenvalue equations also give s := 2αβ with s²(x + ν)² ≥ ν(2x + ν), and then x ≤ 1 − c_ν forces s ≥ c_ν/√((1 − c_ν)² + c_ν²).
5. **The binegativity.** (ψψ†)^Γ has the single negative eigenvalue −αβ, so N₂(σ) = λ + 2λαβ = (ν/2)(1 + s), which is at least the bound.

## Falsifier

The theorem would not settle the question if the module's quantities differed from the source's. The module takes:
- the negativity ν = 2 Tr[(σ^Γ)₋], the source's normalization;
- the binegativity of `TwoQubitBinegativityUpperBoundRefutation`, Tr[(σ^Γ)₋] + 2 Tr[(((σ^Γ)₋)^Γ)₋], with Mathlib's negative part;
- every 4 × 4 complex density matrix, including those with ν = 0.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.lean` (577 lines).
- **Definitions.** It defines `claim` and proves `result : claim`.
- **Reuse.** It reuses:
  - the binegativity of `TwoQubitBinegativityUpperBoundRefutation`;
  - the partial transpose and the density predicate of `StructuredNegativityCoincidenceRefutation`;
  - the local-unitary covariance `partialTransposeB_kronecker_conj` of `KickedIsingNegativityRefutation`;
  - the zero-determinant factorization `zero_determinant_factorization` of `SeparableNumericalRangeRatio`, extracted there from a local fact of `pure_pair` with the same statement and proof, and re-pinned;
  - the rank-one density of `PureStateHandshake` and the singular value decomposition of `FiniteTraceDistance`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations** (both `declared_validated`):
  - `Reg/D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.lean` (`result`);
  - `Reg/D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.lean` (`zero_determinant_factorization`).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.lean.json`, statement `sha256:dce88dab26683c691813b08070a3e3db19b8470321edd5cda0a8615e5f24fd4b`.

Declaration statements:
- `result`: `sha256:114fe535f8be017c5dd1bf88f5435c63c3b2024ecdd004c83eaab218e54522b5`;
- `claim`: `sha256:3690b00b4f68ca36fcb0edfb0a9e6efe7c69b96a2e43e9d9ab857ed8a45139b8`.

## Triage

Tier 1 conjecture of a 2017 preprint, preregistered in issue #18490 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the product-vector argument, the local-unitary transport, the Schmidt form and the scalar bound are instantiations of existing lemmas, polynomial root existence and finite matrix identities | open-problem-resolution |
| `claim` | bind-only | none | definition used by `result` |
| the product-vector, transport, Schmidt and scalar helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |
| `SeparableNumericalRangeRatio.zero_determinant_factorization` (extracted) | bind-only (consumed by its owner and on the proof path of `result`) | none | consumed helper |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The module is a general theorem over all two-qubit density matrices, so `utility` is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Eq. (8) holds for every two-qubit density matrix.

**Computed, not formalized** (orchestrator, recorded in #18490): over 240 000 random two-qubit density matrices of ranks 1–4, N₂(σ) minus the bound stays at least 4.5·10⁻⁹, and the states σ_c of Eq. (6) attain equality at c = c_ν.

**Argued, not formalized.**
- *Sharpness.* The source's Eq. (7) gives N₂(σ_c) = (ν_c/2)(1 + c/√((1 − c)² + c²)) with ν_c = √((1 − c)² + c²) − (1 − c) = N(σ_c). The map c ↦ ν_c inverts ν ↦ c_ν, since (ν_c + c)² = 2ν_c(ν_c + 1). So σ_{c_ν} has negativity ν and binegativity equal to the bound, and Eq. (8) is the exact minimum of N₂ at fixed negativity.
- *Mechanism.* Positivity of σ itself constrains the negative eigenvector of σ^Γ. The 01,10 block bounds the weight x from above, and a small weight forces a large Schmidt product 2αβ, which is the second-level negativity of the eigenvector.
- *The fixed-concurrence conjecture.* After Eq. (7) the source also conjectures that N₂(σ) ≥ N₂(σ_c) with c = C(σ), the concurrence. Write f(ν) for the bound of Eq. (8). Both ν ↦ c_ν and c ↦ c/√((1 − c)² + c²) are increasing (the derivative of the latter is (1 − c)/((1 − c)² + c²)^{3/2}), so f is increasing. The bound N(σ) ≥ ν_{C(σ)} of Verstraete–Audenaert–Dehaene–De Moor (the source's Eq. (5)) then gives N₂(σ) ≥ f(N(σ)) ≥ f(ν_{C(σ)}) = N₂(σ_{C(σ)}). So that conjecture follows from Eq. (8) and the cited negativity–concurrence bound. It is not formalized here; a formal proof needs the two-qubit concurrence and that bound.
- *Scope.* The lower inequality of Eq. (9), at fixed ν and concurrence together, is not addressed.

**Effect on the paper.** The numerically conjectured lower boundary of the negativity–binegativity plot holds for every two-qubit state, and by the sharpness argument above it is the exact minimum. The fixed-concurrence lower bound conjectured after Eq. (7) reduces to the cited negativity–concurrence bound. The lower inequality of Eq. (9) is not settled here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The literature items marked as reported by the search seat were not rechecked. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
