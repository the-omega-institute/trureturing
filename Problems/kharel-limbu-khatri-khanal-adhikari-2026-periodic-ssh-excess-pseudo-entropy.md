---
slug: kharel-limbu-khatri-khanal-adhikari-2026-periodic-ssh-excess-pseudo-entropy
bibkey: khareletal2026pseudoentropy
doi: null
url: https://arxiv.org/abs/2606.29311v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result
---

# Same-phase periodic SSH ground states can have positive averaged excess pseudo entropy

## Problem

P. K. Kharel, M. Limbu, N. Khatri, A. Khanal and K. Adhikari, *Pseudo entropy and topological phases of matter*, arXiv:2606.29311v1, test the conjectured sign of the averaged excess pseudo entropy in the Su–Schrieffer–Heeger model.
- **The quantity.** For pure states ψ, φ with ⟨φ|ψ⟩ ≠ 0, T = |ψ⟩⟨φ|/⟨φ|ψ⟩, T_A = Tr_B T and S(T_A) = −Tr(T_A log T_A) (Eqs. (1)–(3)). The averaged excess is ∆S = Re S(T_A) − (S(ρ_A^ψ) + S(ρ_A^φ))/2 (Eq. (21)).
- **The conjecture.** "In [25, 26], it was conjectured that the averaged excess entropy is non-positive, ∆S ≤ 0, when the states |ψ⟩ and |φ⟩ are in the same phase" (§IV, p. 5).
- **The assertion.** "Under periodic boundary conditions, the conjecture is fully satisfied with no exceptions at all system sizes and across all three phases: topological, trivial, and crossing" (§VI, p. 9), for half-filled ground states of the periodic Hamiltonian of Eq. (15) at w = 1.

The verbatim statements are in [the literature note](../Library/QuantumBounds/khareletal2026pseudoentropy.md).

Issue [#17503](https://github.com/the-omega-institute/trureturing/issues/17503) fixes the reading:
- The Fock space of the 2N modes (1,A), (1,B), …, (N,A), (N,B) carries the Jordan–Wigner annihilation operators in this order.
- A half-filled ground state is a nonzero N-particle vector of minimal energy in the N-particle sector.
- A is the first L unit cells, 1 ≤ L < N, and Tr_B is the partial trace over the remaining modes.
- The entropy of a matrix is −Σ λ log λ over its eigenvalues with multiplicity.
- The assertion: for all such N, L, all v₁, v₂ in the same phase, and all such ground states, ∆S ≤ 0.

The assertion is refuted in this reading.

## Motivation

The authors propose the sign of ∆S as a diagnostic of whether two SSH ground states lie in the same topological phase. They report violations only for open chains at small sizes, attributed to edge modes, and present the periodic chain as violation-free.

## Gap

Issue #17503 records the literature check before any Lean:
- arXiv v1 is the only version;
- the citing work Rana–Dahal–Adhikari (arXiv:2608.29810) tests the XXZ chain and states no SSH result;
- the origin of the conjecture, Mollabashi–Shiba–Takayanagi–Tamaoka–Wei (arXiv:2011.09648, 2106.03118), states that the non-positivity can be violated only across different phases;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

1. **Operators.** The frozen Jordan–Wigner annihilators `fullC` give the Hamiltonian H(v) = Σ h_ij c_i† c_j of Eq. (15) at w = 1. Their anticommutation relations follow from the Clifford relations of the frozen Majorana operators, and the frozen number operator is diagonal in the occupation basis.
2. **Ground states.** For N = 3 and v ∈ {3/8, 5/8}, a rational orthogonal eigenbasis l_k of h(v) gives H = E_g + Σ_k α_k B_k† B_k with α_k > 0, where B_k is a(l_k)† for the negative modes and a(l_k) for the positive ones. So E_g is a lower bound for every vector. The integer vectors of the preregistration are annihilated by every B_k and have three particles. They are therefore half-filled ground states, with E_g = −25/8 and −27/8.
3. **Reductions.** The partial trace over the last four modes of ψ₁ψ₂†, ψ₁ψ₁† and ψ₂ψ₂† is computed exactly on integer shadows of the vectors. The three reduced matrices are block diagonal: an outer pair of equal entries and an inner symmetric 2 × 2 block.
4. **Spectra.** A rational similarity diagonalizes each block. The eigenvalues are 2/9, 2/9, 4/9, 1/9 for T_A; 104/441, 104/441, 169/441, 64/441 for ρ₁; and 10/49, 10/49, 25/49, 4/49 for ρ₂.
5. **The sign.** ∆S = (2 log 2 + 21 log 3 + 15 log 5 + 13 log 13 − 42 log 7)/21 > 0, because 7⁴² < 2²·3²¹·5¹⁵·13¹³.

## Falsifier

The refutation would not settle the assertion if:
- the module's Hamiltonian, ground states, partial trace or entropy differed from Eqs. (1)–(3), (15) and (21);
- its witness were not in the same phase;
- its subsystem were not admitted by the source's statement.

The module uses the source's definitions with the Jordan–Wigner order of the modes. Both hoppings 3/8 and 5/8 are in the topological phase |v| < 1. The subsystem is one complete unit cell of a periodic chain of three cells, and the source quantifies over subsystems A.

## Evidence

The canonical source is `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.lean` (990 lines).
- It defines `sshHopping`, `hamiltonian`, `IsHalfFilledGroundState`, `reduce`, `matrixEntropy`, `averagedExcess` and `claim`, and proves `result : ¬ claim`.
- It uses the frozen `JordanWigner.fullC` and `prefixCount`, and the frozen `FockMajoranaCarrier.numberOperator`, `numberOperator_eq_diagonal`, `majorana` and `majorana_clifford_and_parity` (the Clifford relations of the Majorana operators). It also uses `HardCoreCompression.fullC_entry`, the sparse entry formula of `fullC`, made public for this settlement from a local fact of that module.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations:
  - `result` is the designated refutation result of the `utility` header and is exempt.
  - `HardCoreCompression.fullC_entry` is registered in `Reg/D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression.lean`; it reads out the entry fullC j s t. Its rejected realization, the zero entry, fails at one mode with t occupied. The registration is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.lean.json`, statement `sha256:f7a4acb44ba50c7a3992d55917a38dacd8fb157fd63c35f20be8d2b64623c821`.

Declaration statements:
- `result`: `sha256:77ea90e0642da5af880d9fd14efbcd8dfe700c4f3a44f77e1435de6d3c4c6ef9`;
- `claim`: `sha256:5ea23ed1eadc9f018eb3ecdb7763af44bce7f21591bcdb05180324161e87d3a6`.

## Triage

Tier 1 assertion of a 2026 paper, preregistered in issue #17503 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the anticommutation algebra, the sum-of-squares ground-state certificates, the integer reduction certificates, the rational spectra and the integer inequality are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| the mode, sparse-action, certificate, reduction, spectrum and entropy helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 55 private theorems are bind-only helpers consumed on the proof path of `result`, and its 30 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** for the periodic SSH chain of three unit cells at w = 1, the half-filled ground states at v₁ = 3/8 and v₂ = 5/8 (both in the topological phase) and the subsystem of the first unit cell give ∆S = (1/21) log(2²·3²¹·5¹⁵·13¹³/7⁴²) ≈ 0.0102 > 0. So the assertion fails at the system size N = 3.

**Computed, not formalized** (orchestrator, SymPy exact arithmetic on the full 64-dimensional Fock space, recorded in #17503): both ground states are nondegenerate, with energies −25/8 and −27/8, and their overlap is positive.

**Argued, not formalized.**
- The witness needs no edge modes. The positive sign comes from the bulk ground states of the periodic chain at a subsystem of one complete cell.
- The case of the source's figures is not the one refuted here. It is the half-chain subsystem at even N.

**Open.**
- Whether ∆S ≤ 0 holds for the half-chain subsystem of periodic chains of every even size, which is the case of the source's figures.
- The sign of ∆S for a subsystem of fixed size as N → ∞.

**Effect on the paper.** The §VI assertion fails as stated: under periodic boundary conditions the non-positivity does not hold at all system sizes.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
