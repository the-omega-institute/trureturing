---
slug: tavakoli-bengtsson-gisin-renes-2020-hoggar-sic-compound-refutation
bibkey: tavakolibengtssongisinrenes2020siccompounds
doi: 10.1103/PhysRevResearch.2.043122
url: https://arxiv.org/abs/2007.01007v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.result
---

# A SIC-compound in dimension 8 from Hoggar SICs

## Problem

A. Tavakoli, I. Bengtsson, N. Gisin and J. M. Renes, *Compounds of symmetric informationally complete measurements and their application in quantum key distribution* (Phys. Rev. Research 2, 043122 (2020); arXiv:2007.01007), define a SIC-compound: d³ unit vectors ψ_{jk} in ℂ^d, j ∈ [d²], k ∈ [d], such that
- for every k the vectors ψ_{jk} form a SIC, |⟨ψ_{jk}, ψ_{lk}⟩|² = (dδ_{jl} + 1)/(d + 1);
- for every j the vectors ψ_{jk} form an orthonormal basis.

They construct compounds for d = 2 and d = 4 and prove that none exists for d = 3.
- For d = 5, 6, 7, 8 they enumerate the Weyl–Heisenberg fiducials and find no compound. The introduction states: "for d = 5, 6, 7, 8 we give evidence in support of the same conclusion."
- For d = 8 they add: "dimension 8 also houses SICs that are not based on the WH group … Whether a SIC-compound can be formed from these exceptional SICs is left as an open question."

The verbatim statements are in [the literature note](../Library/QuantumContext/tavakolibengtssongisinrenes2020siccompounds.md).

Issue [#18207](https://github.com/the-omega-institute/trureturing/issues/18207) reads the exceptional SICs as the Hoggar SICs: the orbits of a fiducial vector under the three-qubit Pauli group. Its claim is the negative answer to the question. The claim is refuted, which answers the question in the positive: a SIC-compound in dimension 8 is formed from eight Hoggar SICs.

## Motivation

A SIC-compound gives d orthogonal SICs, so that each SIC measurement can be paired with a projective measurement in the bases of the compound. The source uses the d = 4 compound for a quantum key distribution protocol that tolerates larger errors than the six-state generalization. Existence in a further dimension extends this resource beyond d = 2 and d = 4.

## Gap

Issue #18207 records the literature check before any Lean:
- arXiv lists v1 only;
- the full texts of the works citing the source and of the Hoggar SIC papers of Stacey, Szymusiak–Słomczyński and Ohta–Sakurai contain no compound in dimension 8 and no set of mutually orthogonal Hoggar fiducials;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

For x, z ∈ {0, …, 7}, let (D(x, z)u)(b) = (−1)^{z·(b ⊕ x)} u(b ⊕ x) on ℂ⁸, with z·y the parity of the bitwise AND. Let:
- w₀ = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1), the standard Hoggar fiducial;
- w₁ = (1, i, i, i, 1 − i, 0, 0, 0), w₂ = (1, i, 1 − i, 0, i, i, 0, 0), w₃ = (1, 1 − i, i, 0, i, 0, i, 0);
- w₄ = (1, −1, −1, 1, −1, 1, 1, 1 + 2i), w₅ = (0, 0, 0, 1 + i, i, −i, −i, −1);
- w₆ = (0, 0, 1, −1, 0, 1 − i, −1, i), w₇ = (0, 1, 0, −1, 0, −1, 1 − i, i);

and f_k = w_k/√r_k with r = (12, 6, 6, 6, 12, 6, 6, 6).

1. **Orthonormal bases.** The Gram matrix of the w_k is diag(r), so the f_k are orthonormal. Each D(x, z) preserves the Hermitian inner product, so every family {D(x, z)f_k}_k is an orthonormal basis.
2. **SICs.** Since D(x, z)D(x′, z′) = (−1)^{z·x′} D(x ⊕ x′, z ⊕ z′), every overlap within a Pauli orbit equals a self-overlap ⟨f_k, D(x ⊕ x′, z ⊕ z′)f_k⟩ up to sign. For (x, z) ≠ (0, 0) its squared modulus is |⟨w_k, D(x, z)w_k⟩|²/r_k² = 1/9, checked over the Gaussian integers for all 504 cases. So each orbit {D(x, z)f_k} is a SIC.

## Falsifier

The refutation would not answer the question if:
- the module's Pauli action differed from the three-qubit Pauli group of the Hoggar SIC;
- its SIC condition differed from Eq. (1);
- its compound conditions differed from properties I and II.

The module takes:
- the Pauli action as the shift by x followed by the parity sign of z, the action under which the Hoggar SIC is the orbit of w₀;
- the SIC condition for unit vectors with squared overlap 1/9;
- the compound as eight Pauli orbits that are SICs, with the eight images under each Pauli operator orthonormal.

The defining SICs are three-qubit Pauli orbits. The different fiducials of such orbits give SICs equivalent up to unitary or antiunitary transformations (Stacey, arXiv:1609.03075), so these are the exceptional SICs of the question.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.lean` (247 lines).
- It defines `pauli`, `IsSIC` and `claim`, and proves `result : ¬ claim`.
- It reuses the bit-parity sign `bitSign` of `HoggarSicSumNegativity`, Mathlib's `GaussianInt` with the ring homomorphism `GaussianInt.toComplex`, and the Mathlib XOR lemmas on `Fin 8`. The finite checks run by `decide +kernel` over the Gaussian integers.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.lean.json`, statement `sha256:c102ed9e64bd828000422af8ba701b599c23c989a4d13cc734913ac0b59e1c7d`.

Declaration statements:
- `result`: `sha256:9f2a4d7fe48bed6ab5f95552254295688f9beb0bad105838ed0622414de8ad28`;
- `claim`: `sha256:b428d087fca469297a3f15769bdcc8bf519605f34bea440e1d4353b8c22ccbe7`.

## Triage

Tier 1 question of a 2020 paper, preregistered in issue #18207 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the Gram identity and the self-overlaps are finite Gaussian-integer computations, and the Pauli laws are finite sign identities | open-problem-resolution |
| the witness, transfer and Pauli helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every public declaration is bind-only; the definitions are used by public statements. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Established by `result`**, which refutes the non-existence claim: eight vectors f₀, …, f₇ in ℂ⁸ have Pauli orbits that are SICs and images under every Pauli operator that are orthonormal bases. The 512 vectors D(x, z)f_k form a SIC-compound whose eight defining SICs are Hoggar SICs.

**Argued, not formalized** (search seat, recomputed in part by the orchestrator, recorded in #18207).
- *Clifford equivalence.* Explicit words U_k in Hadamard, phase and controlled-NOT gates satisfy U_k f₀ ∝ f_k. Conjugation by each U_k permutes the Pauli operators up to phases, so every orbit is unitarily equivalent to the standard Hoggar SIC.
- *Mechanism.* The Clifford orbit of the Hoggar fiducial has 15 360 rays (Ohta–Sakurai, arXiv:2506.11725). The eight fiducials are mutually orthogonal members of it. Pauli covariance reduces the 8 × 2016 conditions within the SICs to 504 self-overlaps, and unitarity reduces the 64 basis conditions to one Gram matrix.

**Effect on the paper.** The evidence reported in the introduction against SIC-compounds for d = 5, 6, 7, 8 comes from the Weyl–Heisenberg SICs. With the exceptional SICs a compound exists in dimension 8, which joins d = 2 and d = 4 as a dimension with a SIC-compound. The open question of the paper is answered in the positive.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized; the gate words were not recomputed by the orchestrator.
