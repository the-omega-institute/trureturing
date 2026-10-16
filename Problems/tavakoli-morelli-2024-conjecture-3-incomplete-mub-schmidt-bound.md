---
slug: tavakoli-morelli-2024-conjecture-3-incomplete-mub-schmidt-bound
bibkey: tavakolimorelli2024schmidttracenorm
doi: 10.1103/PhysRevA.110.062417
url: https://arxiv.org/abs/2402.09972v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.result
---

# Conjecture 3 of Tavakoli–Morelli: the Schmidt-number bound for incomplete sets of MUBs

## Problem

A. Tavakoli and S. Morelli, *Enhanced Schmidt number criteria based on correlation trace norms*, arXiv:2402.09972v2, Phys. Rev. A 110, 062417 (2024), bound the trace norm of the table of joint outcome probabilities of local measurements for states of Schmidt number at most r.
- **Incomplete MUBs.** Each side measures in m mutually unbiased bases of C^d, with m < d + 1; Q_m is the md × md table of the joint probabilities tr[ρ (|g^l_a⟩⟨g^l_a| ⊗ |h^k_b⟩⟨h^k_b|)] of the md local projectors.
- **Conjecture 3** (§V B, p. 7): "For any state of Schmidt number r it holds that ‖Q_m‖_tr ≤ 1 + (m − 1)r/d. (54)" The introduction leaves deciding the conjectures as an open problem.

The verbatim statements are in [the literature note](../Library/QuantumBounds/tavakolimorelli2024schmidttracenorm.md). Issue [#17745](https://github.com/the-omega-institute/trureturing/issues/17745) fixes the reading:
- for all d ≥ 1, 1 ≤ m ≤ d, 1 ≤ r ≤ d, any two families of m mutually unbiased bases of C^d chosen independently, and every state of Schmidt number at most r, the bound (54) holds;
- a state of Schmidt number at most r is a finite convex combination of pure states whose coefficient matrices have rank at most r.

This conjecture is proved.

## Motivation

For r = 1, (54) is the separability bound 1 + (m − 1)/d. The source proves only Eq. (53), ‖Q_m‖_tr ≤ (m − 1)/d + r, which coincides with (54) at r = 1 and is weaker for r ≥ 2 and m < d + 1. Conjecture 3 asks whether the criterion keeps its strength with fewer than d + 1 bases.

## Gap

Issue #17745 records the literature check before any Lean:
- arXiv v1 (15 February 2024) already contains the conjecture, and v2 (17 December 2024) leaves it open;
- the citing works read in full text treat informationally complete measurements, conical 2-designs, partial-family collision bounds or matched-outcome sums, not the trace norm of the incomplete table. Li–Huber–Friis (arXiv:2406.04395) bound a matched-outcome sum with the same coefficient 1 + (m − 1)k/d, not the trace norm of the table;
- Naixu-Guo/quantum-open-problems, Zenodo and the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Shared lemma.** `TavakoliMorelliIncompleteEAM.schmidt_traceNorm_le_of_moment`: two families of nonnegative multiples of pure projectors whose second moments satisfy Σ_a (tr H E_a)² ≤ α tr H² + β (tr H)² for every Hermitian H give ‖table‖_tr ≤ α + βr for every state of Schmidt number at most r. It combines the Gram factorization of pure states, the Hilbert–Schmidt Hölder inequality, Σλ² = 1 with (Σλ)² ≤ r, and convexity over mixtures; see the [Conjecture 2 dossier](tavakoli-morelli-2024-conjecture-2-incomplete-eam-schmidt-bound.md).
2. **Second moment of m MUBs.** For Hermitian H, Σ_{l,a} (tr H G^l_a)² ≤ tr H² + (m − 1)(tr H)²/d.
   - Within one basis, the projectors give the diagonal of H in that basis.
   - The traceless diagonal subspaces of distinct mutually unbiased bases are Hilbert–Schmidt orthogonal (`MutuallyUnbiasedDiagonalPlanes`), so their squared projections of the traceless part of H add up to at most ‖H − (tr H/d)𝟙‖² (the Pythagoras core of `PurityPythagorasDecomposition`).
   - Each basis also carries the trace part (tr H)²/d, which appears m times.

   The case d = 1 is separate.
3. **Conclusion.** With (α, β) = (1, (m − 1)/d), the lemma gives ‖Q_m‖_tr ≤ 1 + (m − 1)r/d. Bob's conjugated bases are again mutually unbiased.

## Falsifier

The proof would not settle Conjecture 3 if:
- the module's bases, table or Schmidt number differed from §V B and §II A;
- it fixed a relation between Alice's and Bob's bases, or gauged the first basis;
- it covered only some d, m or r.

The module quantifies over all d ≥ 1, 1 ≤ m ≤ d, 1 ≤ r ≤ d, all pairs of families of m unitaries whose columns have overlaps of modulus squared 1/d across distinct bases, and every finite convex combination of pure states of Schmidt rank at most r.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.lean` (221 lines).
- It defines `MUBFamily`, `MUBFamily.ket`, `MUBFamily.effect`, `Qm` and `claim`, and proves `result : claim`.
- It reuses `TavakoliMorelliIncompleteEAM.schmidt_traceNorm_le_of_moment`, `MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes`, the trace-zero Pythagoras identities of `PurityPythagorasDecomposition`, `TraceZeroReadoutOrthogonalEquivalence.centered_effect_mem` and `Conditioning.recordWeight_sum`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `Reg/D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.lean` registers `result`, `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.lean.json`, statement `sha256:83213415249d1843a8d898bcd44acb0ec413c615c809ce04fae1b3bf73e8ef41`.

Declaration statements:
- `result`: `sha256:4b01070cf34ad0a256164d906cb9a5868f4c344f84e21aeba8c14234a0e6ade3`;
- `claim`: `sha256:0bec6356b5b53cc31d40ee559f863c765d2f018d3ae9f73782361e5e6a2453d3`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #17745 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the bound is an instantiation of the shared Schmidt-number lemma with the MUB second-moment identity, the orthogonality of mutually unbiased diagonal planes and the trace-zero Pythagoras identity, followed by normalization | open-problem-resolution |
| the private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Conjecture 3, for every d, m ≤ d, r ≤ d and every pair of families of m mutually unbiased bases.

**Computed, not formalized** (orchestrator, NumPy/SciPy, recorded in #17745). Wootters–Fields MUBs were used, with Bob's projectors the conjugates of Alice's, and the maximum of ‖Q_m‖_tr was taken over pure states of Schmidt rank at most r.
- For d = 3 and m = 2, 3, the maximum equals 1 + (m − 1)r/d to 1e-6 for every r.
- For d = 5 and m = 2, 3, it is at most the bound for every r, and reaches it to 3e-3, except two r = 5 runs where the optimizer stopped below the bound.

**Argued, not formalized.**
- *Sharpness* (search seat; not checked in Lean). With Bob's projectors the conjugates of Alice's, the maximally entangled state on r vectors of one basis attains 1 + (m − 1)r/d.
- *Mechanism.* Only the traceless part of the second moment is basis-dependent, and the orthogonality of the traceless diagonal planes of MUBs makes the m bases share one budget tr H² − (tr H)²/d. The Schmidt rank enters only through (tr H)² ≤ r in the m − 1 extra copies of the trace part.

**Open.** Whether the analogous bound holds for families of bases that are not mutually unbiased, with the overlap 1/d replaced by the actual overlaps.

**Effect on the paper.** The incomplete-MUB criterion of §V B holds at the conjectured strength.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. Wu–Tang, Phys. Rev. A 113, 022440 (2026), was assessed from its abstract only. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
