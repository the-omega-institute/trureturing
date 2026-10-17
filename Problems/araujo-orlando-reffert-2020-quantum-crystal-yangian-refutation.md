---
slug: araujo-orlando-reffert-2020-quantum-crystal-yangian-refutation
bibkey: araujoorlandoreffert2021quantumcrystals
doi: 10.1103/PhysRevD.103.026020
url: https://arxiv.org/abs/2005.09103v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.result
---

# The quantum crystal potential is not a Yangian combination on the bosonic states

## Problem

T. Araujo, D. Orlando and S. Reffert, *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality* (Phys. Rev. D 103, 026020 (2021); arXiv:2005.09103), study the quantum crystal melting Hamiltonian H = −J(Γ + Π) + V(√q O₊ + O₋/√q) on plane-partition states.
- Γ and Π add and remove boxes in all possible ways.
- O₊ and O₋ count the boxes that can be added and removed.
- A fermion-boson correspondence, Eq. (46), defines bosonic states |Λ(N K)⟩⟩ = Σ_Λ χ_Λ[C(K)]|Λ⟩ through characters of symmetric groups; it preserves the number of boxes.

Section VI conjectures: "The growth operators Γ, Π and O±(Γ, Π) are linear combinations of the generators of the algebra Y[gl̂(1)], and the states |N K⟩⟩ fulfill the Y[gl̂(1)] MacMahon representation."
- In that representation e_j adds and f_j removes a box on the bosonic states, Eq. (49), and φ_j acts diagonally on them, Eq. (50).
- The authors conclude that "O±(Π, Γ) ∈ B since they can be written as linear combinations of φ_j".

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/araujoorlandoreffert2021quantumcrystals.md).

Issue [#18238](https://github.com/the-omega-institute/trureturing/issues/18238) fixes the reading: the consequences of the conjecture at the three-box bosonic state of the identity class of S₃. The conjecture is refuted.

## Motivation

An identification of the crystal Hamiltonian with Yangian generators, Eq. (51), would make the quantum crystal an integrable system governed by the affine Yangian of gl̂(1). The conjecture is the step that places the potential terms O± in the Cartan part of the algebra.

## Gap

Issue #18238 records the literature check before any Lean:
- arXiv v1 and v2 both state the conjecture;
- the citing works (arXiv:2009.06812; N. Wang, Nucl. Phys. B 969 (2021) 115461) do not settle it for the operators O± in the bosonic basis;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

1. **The state.** By Eq. (46) and the characters (A13), the identity class of S₃ gives v = |(3)⟩ + 2|(2, 1)⟩ + |(1, 1, 1)⟩, the sum over the row, hook and column with coefficients 1, 2, 1, as written in Appendix C, Eq. (C2b).
2. **The potential.** As single-layer plane partitions, the row, hook and column have 1, 2 and 1 removable boxes. So O₋ v = |(3)⟩ + 4|(2, 1)⟩ + |(1, 1, 1)⟩.
3. **The grading.** If e_j v has four boxes, f_j v two boxes and φ_j v is a multiple of v, then every finite combination of them has, at the hook, twice its coefficient at the row. O₋ v has 4 at the hook and 1 at the row. So O₋ v is not such a combination.

## Falsifier

The refutation would not settle the conjecture if:
- O₋ differed from the count of negative flips of Eq. (2b);
- the bosonic state differed from Eq. (46);
- the conjecture did not imply the hypotheses of `claim`.

The module takes:
- plane partitions as finite lower sets in ℕ³;
- O₋ as diagonal on them with eigenvalue the number of removable boxes;
- v from the coefficients 1, 2, 1 of (A13) and Appendix C.

The conjecture implies `claim`. It gives O₋ as a linear combination of the generators, and Eqs. (49)–(50) at the bosonic state v give the grades of e_j v and f_j v and the eigenvector property of φ_j v. A linear combination is read as finite.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.lean` (144 lines).
- It defines `PlanePartition`, `boxCount`, `removableCount`, `State`, `IsGrade`, `potentialMinus`, `bosonicIdentityThree` and `claim`, and proves `result : ¬ claim`.
- It uses Mathlib's `IsLowerSet`, `Finsupp` and `Finsupp.linearCombination`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.lean.json`, statement `sha256:ad8dc9d8ae57be269f51dc4520d7ea20a358dbfbfcce67f55095979e9b2b4db7`.

Declaration statements:
- `result`: `sha256:08c1ac564d619de338f26e9ac7aa26ddb1d627d8453bf8f6e79fc95faeae7a28`;
- `claim`: `sha256:ed44ab325397ddbf83562ccad41f9fcf6d9550d3f9c702a177d675c71f06b595`.

## Triage

Tier 1 conjecture of a 2020 paper, preregistered in issue #18238 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the removable counts are finite computations and the contradiction compares two coefficients | open-problem-resolution |
| the witness and coefficient helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every public declaration is bind-only; the definitions are used by public statements. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** no linear combination of maps satisfying Eqs. (49)–(50) at the bosonic state v agrees with O₋ on v.

**Argued, not formalized.**
- *Mechanism.* O₋ is diagonal in the plane-partition basis. Its eigenvalue varies among plane partitions with the same number of boxes: 1 for the row and the column, 2 for the hook. A bosonic state mixes such plane partitions, so O₋ is not diagonal on the bosonic states. The conclusion O± ∈ B on page 9 of the source therefore fails, whatever the coefficients of Eq. (51).
- *Scope.* The two-box bosonic states give no obstruction, since the two single-layer two-box plane partitions both have one removable box. Three boxes is the least size where O₋ separates plane partitions mixed by Eq. (46).
- *O₊.* The row, hook and column have 3, 4 and 3 addable boxes, so O₊ v = 3|(3)⟩ + 8|(2, 1)⟩ + 3|(1, 1, 1)⟩ is not a multiple of v either (orchestrator, exact count).

**Effect on the paper.** An identification of the potential terms with the Cartan part of Y[gl̂(1)] must use a basis in which O± are diagonal, such as the plane-partition basis itself. The bosonic basis of Eq. (46) is not such a basis.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
