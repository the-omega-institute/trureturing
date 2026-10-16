---
slug: champagne-johnston-macdonald-pipes-2022-symmetric-witness-spectrum
bibkey: champagnejohnstonmacdonaldpipes2022spectral
doi: 10.1016/j.laa.2022.05.004
url: https://arxiv.org/abs/2108.10405v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.result
---

# The eigenvalues of symmetric two-qubit entanglement witnesses satisfy µ3 ≥ −√(µ1µ2)

## Problem

G. Champagne, N. Johnston, M. MacDonald and L. Pipes, *Spectral properties of symmetric quantum states and symmetric entanglement witnesses*, Linear Algebra Appl. 649, 273–300 (2022), arXiv:2108.10405v1, study the eigenvalues of symmetric entanglement witnesses.
- **Witnesses.** A symmetric entanglement witness is a Hermitian W on C^d ∨ C^d with (v ⊗ v)*W(v ⊗ v) ≥ 0 for all v (§2.3); positive semidefinite W are included (footnote 1).
- **Theorem 3.** For d = 2 and real µ1 ≥ µ2 ≥ µ3, the inequalities (a) µ2 ≥ 0 and (b) µ3 ≥ −√(µ1µ2) are sufficient for the existence of a symmetric witness with these eigenvalues, and necessary for decomposable ones. Every symmetric witness satisfies (a) and a weaker inequality (c).
- **The conjecture.** After Theorem 3 and in §6(c) (page 20): "We conjecture that inequalities (a) and (b) from that theorem provide the correct characterization."

The verbatim statements are in [the literature note](../Library/QuantumBounds/champagnejohnstonmacdonaldpipes2022spectral.md).

Issue [#17536](https://github.com/the-omega-institute/trureturing/issues/17536) fixes the reading:
- C²∨C² is identified with C³ through the orthonormal Dicke basis e₀₀, (e₀₁ + e₁₀)/√2, e₁₁, in which v ⊗ v has coordinates (v₀², √2 v₀v₁, v₁²).
- "Eigenvalues µ1 ≥ µ2 ≥ µ3" means that the characteristic polynomial is (X − µ1)(X − µ2)(X − µ3).
- The conjecture: for all real µ1 ≥ µ2 ≥ µ3, a symmetric witness with these eigenvalues exists if and only if µ2 ≥ 0 and µ3 ≥ −√(µ1µ2).

The conjecture is proved in this reading.

## Motivation

The spectrum of a witness decides which entangled states it can detect from spectral data alone. For ordinary two-qubit witnesses the spectra are known (Johnston–Patterson, arXiv:1708.05901). For symmetric witnesses, which are positive only on the product states v ⊗ v, the source obtained the exact spectral region only for decomposable witnesses, and Figure 2 shows the gap between (b) and (c).

## Gap

Issue #17536 records the literature check before any Lean:
- arXiv v1 is the only version;
- the nine citing works with arXiv records listed by Semantic Scholar were read at every in-text citation of the source, and none states or settles the conjecture;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

1. **The null cone.** With J = [[0, 0, −1], [0, 1, 0], [−1, 0, 0]], xᵀJx = x₁² − 2x₀x₂. A vector x ∈ C³ is a coherent vector (v₀², √2 v₀v₁, v₁²) if and only if xᵀJx = 0.
2. **Transport to the eigenbasis.** The witness and the diagonal matrix of its eigenvalues have the same characteristic polynomial, so W = U D U* with U unitary. G = UᵀJU is symmetric and unitary, and the witness condition becomes: zᵀGz = 0 implies Σᵢ dᵢ|zᵢ|² ≥ 0.
3. **Two roots.** Put the negative eigenvalue −c at index 2 and t = |G₂₂|. Then t > 0, because otherwise e₂ would be a null vector with negative expectation. For each u ∈ C², the cone equation in z₂ has two roots whose product is uᵀAu/G₂₂, where A is the upper-left 2 × 2 corner of G. Positivity at both roots gives c|uᵀAu| ≤ t(µ1|u₀|² + µ2|u₁|²).
4. **A 2 × 2 bound.** If A is complex symmetric and |uᵀAu| ≤ p|u₀|² + q|u₁|² for all u, then p, q ≥ 0 and |det A| ≤ pq. The proof is polarization followed by two test pairs.
5. **The corner.** For a unitary G, adj G = (det G)·G*, so |det A| = |G₂₂| = t.
6. **Conclusion.** Steps 3–5 give c²t ≤ t²µ1µ2, hence c² ≤ tµ1µ2 ≤ µ1µ2, that is, µ3 ≥ −√(µ1µ2). Step 4 also gives µ2 ≥ 0. If µ3 ≥ 0, both inequalities are immediate.
7. **Sufficiency.** W = diag(µ1, µ3, µ2) in the Dicke basis has coherent expectation (√µ1|v₀|² − √µ2|v₁|²)² + 2(µ3 + √(µ1µ2))|v₀|²|v₁|² ≥ 0.

## Falsifier

The proof would not settle the conjecture if:
- the module's witnesses were narrower than all Hermitian W on C²∨C² that are positive on v ⊗ v, for example by excluding positive semidefinite or degenerate W;
- the eigenvalue condition were weaker than the characteristic polynomial;
- one direction of the characterization were missing.

The module quantifies over every Hermitian 3 × 3 complex matrix in the Dicke basis with nonnegative coherent expectation, fixes its characteristic polynomial, and proves both directions.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.lean` (396 lines).
- It defines `coherent`, `IsSymmetricWitness` and `claim`, and proves `result : claim`.
- It uses Mathlib's spectral theorem and the eigenvalue comparison `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`. It also uses two theorems made public for this settlement:
  - `QuadraticRadii.quadratic_factors`, the factorization of a complex quadratic;
  - `diagonal_quadratic_form` of `CanonicalRelativeModularModel`, the real quadratic form of a real diagonal matrix, lifted from two identical local facts of that module.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations:
  - `Reg/D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.lean` reads out the lower bound −√(µ1µ2) on µ3 in `claim`. Its rejected realization, −√(µ1µ2) − 1, fails at µ1 = µ2 = 0 and µ3 = −1, where it would require a witness that `result` excludes. The registration is `declared_validated`.
  - `QuadraticRadii.quadratic_factors` is registered in `Reg/D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.lean`; it reads out the second root w of the factorization. The registration is `declared_validated`.
  - `diagonal_quadratic_form` is registered in `Reg/D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.lean`; it reads out the weighted sum Σᵢ dᵢ‖yᵢ‖². The registration is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.lean.json`, statement `sha256:f1e7ea21bf0528a2415971810622185e9420fc12e36d7fbf25e459e6c7da9455`.

Declaration statements:
- `result`: `sha256:733da05943859dbf1271dfb62293583372e136b762dc5d45a1405fc582338fa0`;
- `claim`: `sha256:0e69a98c72918ad682272bc38fcdac99144cf9e09169957a1804dfbd3e095c98`.

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #17536 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the null cone, the spectral transport, the two-root bound, the 2 × 2 determinant bound, the corner identity and the diagonal witness are instantiations of pinned Mathlib and frozen D5 results followed by normalization | open-problem-resolution |
| the null-cone, root, bilinear, determinant, spectral, corner and diagonal-witness helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 9 private theorems are bind-only helpers consumed on the proof path of `result`, and its 4 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for all real µ1 ≥ µ2 ≥ µ3, a symmetric entanglement witness on C²∨C² with eigenvalues µ1, µ2, µ3 exists if and only if µ2 ≥ 0 and µ3 ≥ −√(µ1µ2). This is the exact characterization asked in §6(c).

**Argued, not formalized.**
- The proof gives more than the bound. Let ν be a unit eigenvector of the negative eigenvalue −c, and let t = |νᵀJν| ∈ (0, 1] be its value on the cone form. Then c² ≤ tµ1µ2. Equality µ3 = −√(µ1µ2) therefore forces t = 1: in coefficient form [[x, y/√2], [y/√2, z]], t = |y² − 2xz| = 2|det|, so the negative eigenvector is a maximally entangled symmetric state. The extremal diagonal witness has ν = (e₀₁ + e₁₀)/√2, for which t = 1.
- With Theorem 3 of the source, the eigenvalue region of all symmetric witnesses on C²∨C² equals that of the decomposable ones.

**Open.**
- The spectra of symmetric witnesses on C^d ∨ C^d for d ≥ 3.
- The source's other open problems: antisymmetric witnesses (§6(a)), Schmidt-number witnesses (§6(b)), and the minimal set of matrices for absolute symmetric PPT (§6(d)).

**Effect on the paper.** The conjecture after Theorem 3 holds. Inequality (c) of Theorem 3 can be replaced by (b) for every symmetric witness, and (a) with (b) characterize the spectra exactly.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal version was not read; its agreement with arXiv v1 is unverified. The statements in "Argued, not formalized" are not formalized.
