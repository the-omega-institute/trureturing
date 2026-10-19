---
slug: yang-chen-li-fei-wang-2018-coherence-breaking-amendment
bibkey: yang2018coherencebreaking
doi: 10.1007/s10773-018-3890-4
url: https://arxiv.org/abs/1810.09642v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.result
---

# Every incoherent channel with coherence-breaking index at least two is amended by one unitary

## Problem

L.-M. Yang, B. Chen, T. Li, S.-M. Fei and Z.-X. Wang, *Amending Coherence-Breaking Channels via Unitary Operations* (Int. J. Theor. Phys. 57, 3776 (2018); arXiv:1810.09642), study incoherent channels.
- **Definitions.** An incoherent channel is coherence-breaking if it maps every state to an incoherent state. The coherence-breaking index n(Φ) is the least k with Φ^k coherence-breaking.
- **Results.** For qubit channels with n(Φ) = 1 and 2 they find unitaries Λα that make Λα ◦ Φ and Φ ◦ Λα ◦ Φ not coherence-breaking.
- **The conjecture.** Section 5 states: "for a d-dimensional quantum channel Φ with n(Φ) ≥ 2, one may conjecture that the channel Φ can also be amended by Φ ◦ Λα ◦ Φ ◦ · · · ◦ Φ ◦ Λα ◦ Φ [n Φ] with proper unitary operations Λα."
- **The later preprint.** MiS Preprint 7/2019 asserts the qudit statement in its conclusions without a proof.

The verbatim statements are in [the literature note](../Library/QuantumChannels/yang2018coherencebreaking.md).

Issue [#18385](https://github.com/the-omega-institute/trureturing/issues/18385) fixes the reading: for every incoherent trace-preserving Kraus channel with n(Φ) = n ≥ 2, some unitary U makes Φ ◦ (Λ_U ◦ Φ)^{n−1} not coherence-breaking, with the same U in every slot. The conjecture is proved.

## Motivation

Coherence-breaking channels destroy all coherence; amendment asks whether interleaved unitary control can keep some coherence through repeated uses of a noisy incoherent channel. The qubit cases are solved in the source; the general dimension is the open part.

## Gap

Issue #18385 records the literature check before any Lean:
- arXiv v1, the only version, states the d-dimensional case as a conjecture.
- MiS Preprint 7/2019 asserts it without proof.
- Semantic Scholar lists two citing works. arXiv:1909.00926, read in full, cites the paper only in its references. The other, Xie–Chu–Cui 2026 (Phys. Lett. A, DOI 10.1016/j.physleta.2026.131573, on imaginarity-breaking channels), has no arXiv version or abstract on record and was not reachable, so whether it addresses the conjecture is `ASSUMED-UNVERIFIED`.
- The repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Let O be the projection onto off-diagonal matrices, and D = 1 − O.
1. **Diagonals are preserved.** Every incoherent Kraus operator maps each basis vector to a multiple of a basis vector, so the channel maps diagonal matrices to diagonal matrices. Hence T = O ∘ Φ satisfies T = T ∘ O.
2. **Permutation-phase unitaries.** For a permutation σ and fourth roots of unity ω, the unitary conjugation Λ commutes with O. It sends the matrix unit E_kl to ω_k ω̄_l E_{σ(k)σ(l)}.
3. **The composite.** The off-diagonal part of Φ ∘ (Λ ∘ Φ)^{m} is (TΛ)^{m} T. Density matrices span all matrices, so the composite of length n is coherence-breaking only if (TΛ)^{n−1}T = 0.
4. **Nilpotency.** Then (TΛ)^n = 0, so TΛ is nilpotent and its trace vanishes.
5. **A unitary with nonzero trace.** Φ is not coherence-breaking because n ≥ 2, so T ≠ 0.
   - Choose σ moving a nonzero entry of T onto the diagonal of TΛ.
   - The average of ω̄_k ω_l Tr(TΛ) over all fourth-root phases equals that entry. Here the character sums of the fourth roots of unity are used.
   - So some phases give Tr(TΛ) ≠ 0, a contradiction.

## Falsifier

The theorem would not settle the conjecture if the module's notions differed from the source's:
- an incoherent channel;
- coherence breaking;
- the coherence-breaking index;
- the amended composite.

The module takes:
- Kraus families with Σ K†K = 1 in which each column of each Kraus operator has at most one nonzero entry, the source's condition on basis states;
- coherence breaking as mapping every density matrix to a diagonal one;
- the index hypotheses as Φ^n coherence-breaking and Φ^k not coherence-breaking for 1 ≤ k < n;
- the composite with n copies of Φ and one unitary conjugation between consecutive copies.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.lean` (363 lines).
- **Definitions.** It defines `IsIncoherentKraus`, `IsCoherenceBreaking`, `amended` and `claim`, and proves `result : claim`.
- **Reuse.** It reuses:
  - the Kraus action `krausApply` and `IsKrausChannel` of `OutputMaximalCoherenceTensorizationRefutation`;
  - the monomial matrices of `MonomialDiagonalPreserving`;
  - the fourth-root phases and their fourth-moment identity `moment_four` of `GurvitsBarnumMoments`;
  - the density span `all_density_tomographically_complete` of `ConcealmentKernelNecessityRefutation`.
- **Owner exposures.** The two owners are made public at `phase`, `moment_four` and `all_density_tomographically_complete` by removing `private`, and are re-pinned.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations** (all `declared_validated`):
  - `Reg/D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.lean` (`result`);
  - `Reg/D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.lean` (`moment_four`);
  - `Reg/D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.lean` (`all_density_tomographically_complete`).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.lean.json`, statement `sha256:1b9c3e890b6e50ef09a1f477ecb8a50660fc78b10ad6488b3b244ef8413a23ad`.

Declaration statements:
- `result`: `sha256:539a1786d715ffbd2e213146bf8dc7a6d590d7a34a7a0f3aba854be79af20ad5`;
- `claim`: `sha256:208150fc372b1688ca963e75442a94fc77a3cc40862e6dcf17461649f039c6c1`.

## Triage

Tier 1 conjecture of a 2018 paper, preregistered in issue #18385 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the off-diagonal factorization, the nilpotent-trace step, the density span and the fourth-root character average are instantiations of existing lemmas and finite normalization | open-problem-resolution |
| `IsIncoherentKraus`, `IsCoherenceBreaking`, `amended`, `claim` | bind-only | none | definitions used by `claim` |
| the off-diagonal, composite and character-sum helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The module is a general theorem over all dimensions and Kraus families, so `utility` is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every incoherent trace-preserving Kraus channel with coherence-breaking index n ≥ 2 there is a unitary U such that Φ ∘ (Λ_U ∘ Φ)^{n−1} is not coherence-breaking.

**Computed, not formalized** (orchestrator, recorded in #18385): random trace-preserving incoherent Kraus families with exact index n = 2 or 3 in dimensions 3 and 4 (220 channels) are all amended by a permutation unitary with fourth-root phases.

**Argued, not formalized.**
- *Mechanism.*
  - The only obstruction to amendment is the nilpotency of TΛ.
  - The phases make the trace of TΛ a nonzero character polynomial. One permutation-phase unitary therefore amends Φ at every composition length simultaneously.
  - The proof uses only that Φ itself is not coherence-breaking. The index n enters only through n ≥ 2.
- *Scope.*
  - The same argument applies to every channel that maps diagonal matrices to diagonal matrices, including the maximally incoherent operations.
  - It does not bound the number of unitaries needed when different unitaries are allowed in different slots.

**Effect on the paper.** The qubit Lemmas 4.4–4.5 become special cases. The assertion of MiS Preprint 7/2019 now has a proof.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal version and the 2026 citing paper by Xie, Chu and Cui were not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
