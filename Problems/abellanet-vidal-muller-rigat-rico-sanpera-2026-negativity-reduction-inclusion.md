---
slug: abellanet-vidal-muller-rigat-rico-sanpera-2026-negativity-reduction-inclusion
bibkey: abellanetvidalmullerrigatricosanpera2026spectrum
doi: null
url: https://arxiv.org/abs/2604.02420v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.result
---

# Negativity at most (χ − 1)/2 does not imply positivity under the χ-reduction map

## Problem

J. Abellanet-Vidal, G. Müller-Rigat, A. Rico and A. Sanpera, *Bounding the entanglement of a state from its spectrum*, arXiv:2604.02420v2, compare supersets of the states of Schmidt number at most χ.
- **Negativity.** N(ρ) = (||ρ^Γ||_1 − 1)/2 (Definition 2, Eq. (7)). Schmidt number at most χ implies N(ρ) ≤ (χ − 1)/2 (Lemma 3).
- **Reduction.** RED_κ(ρ) = Tr(ρ)1 − ρ/κ (Eq. (35)). Schmidt number at most κ implies [1 ⊗ RED_κ](ρ) ≥ 0 (Theorem 7).
- **The question.** §5.4: "the complete inclusions of the considered EFS_γ sets is only pending for the unknown case NEGFS_{(χ−1)/2} ?⊂ PREDFS_χ, which is also unknown for the non-FS case."

The verbatim statements are in [the literature note](../Library/QuantumBounds/abellanetvidalmullerrigatricosanpera2026spectrum.md).

Issue [#17440](https://github.com/the-omega-institute/trureturing/issues/17440) fixes the reading of the non-FS case: for every density matrix ρ on C^N ⊗ C^M and every integer 1 ≤ χ ≤ min(N, M), does N(ρ) = (χ − 1)/2 imply [1 ⊗ RED_χ](ρ) = ρ_A ⊗ 1 − ρ/χ ≥ 0? The attained value is the stronger hypothesis, so a counterexample also refutes the sublevel reading N(ρ) ≤ (χ − 1)/2.

The non-FS inclusion is refuted.

## Motivation

Both criteria are necessary conditions for Schmidt number at most χ, and the paper compares them through their spectral versions (Table 1, Eq. (44)). The inclusion would make the negativity bound the stronger criterion in every case.

## Gap

Issue #17440 records the literature check before any Lean:
- arXiv v1 and v2 both state the question;
- INSPIRE lists two citing works, which do not resolve it (seat-reported);
- no settlement was found on Zenodo, Crossref or in the repository Naixu-Guo/quantum-open-problems;
- the repository had no entry for the question.

The reduction maps are those of Terhal–Horodecki (quant-ph/9911117), which apply them to isotropic states.

`not-found-in-searched-scope`.

## Route

1. **The witness.** On C³ ⊗ C³ take ρ = |v⟩⟨v|/18 with v = 4|00⟩ + |11⟩ + |22⟩, and χ = 2.
2. **The negativity.** ρ^Γ sends |ij⟩ to (b_i b_j/18)|ji⟩ with b = (4, 1, 1). So (ρ^Γ)†ρ^Γ is diagonal with entries (b_i b_j/18)², and its square root is diagonal with entries b_i b_j/18. The trace norm is (Σ b_i)²/18 = 2, and N(ρ) = 1/2 = (χ − 1)/2.
3. **The reduction.** ρ_A = diag(16, 1, 1)/18. With z = |00⟩ + 4|11⟩ + 4|22⟩, z†(ρ_A ⊗ 1)z = 8/3 and z†ρz/2 = 4, so z†[1 ⊗ RED_2](ρ)z = −4/3 < 0.

## Falsifier

The refutation would not settle the question if:
- the module's negativity differed from Definition 2;
- its reduction map differed from Eq. (35) on the second factor;
- the witness were not a density matrix;
- the dimensions excluded χ = 2;
- the statement assumed something the source does not.

The module uses the frozen trace norm Tr √(A†A), the frozen second-factor partial transpose and the frozen partial trace. It quantifies over all finite factors, density matrices and admissible χ.

## Evidence

The canonical source is `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.lean` (152 lines, `generality: I`, `utility: kind=certified-instance; basis=refutes`).
- It defines `negativity` and `claim`, and proves `result : ¬ claim`.
- It reuses:
  - the frozen `FiniteTraceDistance.traceNorm`, `KickedIsingNegativityRefutation.partialTranspose`, `PartialTraceMutualInformation.partialTraceRight` and `PureStateHandshake.rankOneDensity`;
  - three declarations of the frozen `CoherentCopyCorrelationTax`, made public for this settlement: `copyMatrix`, `copyMatrix_entry` and `partialTraceRight_copyMatrix`. The last gives the reduced state.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations:
  - `result` is the designated refutation result and is exempt (CLAUDE.md §3.9).
  - `copyMatrix_entry` and `partialTraceRight_copyMatrix` are registered in `Reg/D5/S3/Quantum/Information/CoherentCopyCorrelationTax.lean`. Both are `declared_unresolved`, with the judge reading `IE-C050 … rule=source.state_binder`.
  - Their escape audit is incomplete; the gap is recorded in [#17475](https://github.com/the-omega-institute/trureturing/issues/17475).

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.lean.json`, statement `sha256:100e696e85067b2a4a7a1088e41bba8e10a42ae720cb5a37264430476f43a9a7`.

Declaration statements:
- `result`: `sha256:bbe5e820c03c6e26c4bc4d8774682d0c0916734cb976d6a3b287f58d904a6d6a`;
- `claim`: `sha256:56860d8eb2d2450a899a26489311318103cc7116d80f33ed8838c1cdb80ae1b0`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the density hypotheses, the Gram identity, the square root, the trace norm, the reduced state and the quadratic form are instantiations of frozen D5 and pinned Mathlib results followed by normalization and rational arithmetic | open-problem-resolution |
| the density, Gram, trace-norm, marginal and quadratic-form helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 10 private theorems are bind-only helpers consumed on the proof path of `result`, and its 8 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

## Triage

### What the settlement shows

**Refuted by `result`:** a pure two-qutrit state has negativity exactly 1/2 and fails the 2-reduction criterion, so the non-FS negativity set NEG_{1/2} is not contained in PRED_2.

**Computed, not formalized** (orchestrator, 15 October 2026; recorded in #17440):
- the partial-transpose spectrum {8/9, ±2/9 (each twice), 1/18 (three times), −1/18} and the smallest eigenvalue (2 − √6)/9 of [1 ⊗ RED_2](ρ) (SymPy, exact);
- on 20,000 random pure states of full Schmidt rank in 3 ⊗ 3 and 4 ⊗ 4, the smallest eigenvalue of [1 ⊗ RED_κ](ψ) was at most 0 in every sample, for κ = 2 in 3 ⊗ 3 and κ = 2, 3 in 4 ⊗ 4 (NumPy).

**Argued, not formalized.**
- For a pure state Σ_{i ≤ r} a_i|ii⟩ of Schmidt rank r, the test vector Σ a_i⁻¹|ii⟩ gives z†(ρ_A ⊗ 1)z = r and z†ρz/κ = r²/κ. So [1 ⊗ RED_κ] fails on every pure state of Schmidt rank greater than κ.
- The negativity of such a state is ((Σ a_i)² − 1)/2. It takes every value in (0, (r − 1)/2] as the Schmidt coefficients vary, by continuity.
- Hence for every χ ≥ 2 with min(N, M) ≥ χ + 1, the non-FS inclusion fails at the attained value and on the whole sublevel set, through pure states of Schmidt rank χ + 1.
- So a negativity at most (χ − 1)/2 does not certify positive χ-reduction.

**Open.**
- The FS inclusion NEGFS_{(χ−1)/2} ⊂ PREDFS_χ, with its quantifier over global unitaries, is not addressed.

**Effect on the paper.** The non-FS inclusion of §5.4 is false. The FS case remains the only pending inclusion among the EFS_γ sets.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
