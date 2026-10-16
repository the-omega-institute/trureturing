---
slug: tavakoli-morelli-2024-conjecture-2-incomplete-eam-schmidt-bound
bibkey: tavakolimorelli2024schmidttracenorm
doi: 10.1103/PhysRevA.110.062417
url: https://arxiv.org/abs/2402.09972v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.result
---

# Conjecture 2 of Tavakoli–Morelli: the Schmidt-number bound for equiangular measurements

## Problem

A. Tavakoli and S. Morelli, *Enhanced Schmidt number criteria based on correlation trace norms*, arXiv:2402.09972v2, Phys. Rev. A 110, 062417 (2024), bound the trace norm of the table of joint outcome probabilities of local measurements for states of Schmidt number at most r.
- **Equiangular measurement (EAM).** n > d unit vectors ψ_a in C^d with Σ_a |ψ_a⟩⟨ψ_a| = (n/d)𝟙 (Eq. (49)) and |⟨ψ_a|ψ_a′⟩|² = (n − d)/(d(n − 1)) for a ≠ a′ (Eq. (50)); its effects are E_a = (d/n)|ψ_a⟩⟨ψ_a|.
- **The table.** For Alice's EAM {E^A_a} and Bob's {E^B_b}, (P_n)_ab = tr[ρ (E^A_a ⊗ E^B_b)].
- **Conjecture 2** (§V A, p. 7): "For any state of Schmidt number r it holds that ‖P_n‖_tr ≤ [d(d − 1) + r(n − d)]/[n(n − 1)]. (52)" The introduction leaves deciding the conjectures as an open problem.

The verbatim statements are in [the literature note](../Library/QuantumBounds/tavakolimorelli2024schmidttracenorm.md). Issue [#17745](https://github.com/the-omega-institute/trureturing/issues/17745) fixes the reading:
- for all d ≥ 1, 1 ≤ r ≤ d, n > d, any two n-element EAMs on C^d chosen independently, and every state of Schmidt number at most r, the bound (52) holds;
- a state of Schmidt number at most r is a finite convex combination of pure states whose coefficient matrices have rank at most r.

This conjecture is proved.

## Motivation

For r = 1, (52) is the separability bound, and for larger r it detects states of Schmidt number greater than r with n < d² outcomes per side. The source proves only the weaker Eq. (51), ‖P_n‖_tr ≤ [n − d + d(d − 1)r]/[n(n − 1)], which coincides with (52) at r = 1 and is weaker for r ≥ 2. Conjecture 2 asks whether the criterion keeps its strength with incomplete measurements.

## Gap

Issue #17745 records the literature check before any Lean:
- arXiv v1 (15 February 2024) already contains the conjecture, and v2 (17 December 2024) leaves it open;
- the citing works read in full text treat informationally complete measurements, conical 2-designs, partial-family collision bounds or matched-outcome sums, not the trace norm of the incomplete table (Wang–Fei 2505.02297, Siudzińska 2506.18211, 2607.04555 and 2512.18807, Mu–Wang–Fei 2511.12887, Li–Huber–Friis 2406.04395 and others);
- Naixu-Guo/quantum-open-problems, Zenodo and the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Pure states as a Gram product.** For a unit vector ψ with coefficient matrix Ψ = U D Vᴴ (singular value decomposition, D = diag(λ)), put S = D^{1/2}. Then tr[|ψ⟩⟨ψ| (A_a ⊗ B_b)] = tr(X_a Y_b) with X_a = S Uᴴ A_a U S and Y_b = S Vᴴ B_bᵀ V S, so the table is Fᴴ G for matrices F, G whose columns are vec X_a and vec Y_b.
2. **Hölder.** ‖Fᴴ G‖_tr ≤ ‖F‖_F ‖G‖_F, from the Hilbert–Schmidt Hölder inequality of `TraceClass.IdealNorm`.
3. **Second moments.** For rank-one effects, ‖F‖_F² = Σ_a (tr H E_a)² with H = U D Uᴴ. For an EAM and Hermitian H, the tight-frame identity and the constant overlaps give Σ_a (tr H E_a)² ≤ [d(d − 1) tr H² + (n − d)(tr H)²]/[n(n − 1)]. Bob's transposed effects form an EAM again.
4. **Schmidt rank.** tr H² = Σλ² = 1, and (tr H)² = (Σλ)² ≤ r by Cauchy–Schwarz over the at most r nonzero λ.
5. **Mixtures.** The table is real-linear in ρ and the trace norm is subadditive and positively homogeneous, so the pure-state bound extends to every state of Schmidt number at most r.

Steps 3–5 are the shared lemma `schmidt_traceNorm_le_of_moment`: two families of nonnegative multiples of pure projectors with second moments bounded by α tr H² + β (tr H)² give ‖table‖_tr ≤ α + βr. Conjecture 3 uses the same lemma.

## Falsifier

The proof would not settle Conjecture 2 if:
- the module's EAMs, table or Schmidt number differed from Eqs. (49), (50), (8) and §II A;
- it fixed a relation between Alice's and Bob's measurements;
- it covered only some d, n or r.

The module quantifies over all d ≥ 1, all n > d, all 1 ≤ r ≤ d, all pairs of EAMs given by the two conditions (49) and (50), and every finite convex combination of pure states of Schmidt rank at most r. The table entries are the real parts of tr[ρ (E^A_a ⊗ E^B_b)], which equal the traces themselves for such ρ.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.lean` (754 lines).
- It defines `coeff`, `SchmidtNumberLE`, `correlation`, `moment`, `ScaledPure`, `MomentBound`, `EAM`, `EAM.effect`, `Pn` and `claim`, and proves `result : claim`.
- The public lemmas `ket_dot_self`, `proj_eq_outer`, `scaledPure_hermitian`, `scaledPure_sandwich`, `proj_overlap` and `schmidt_traceNorm_le_of_moment` lie on the proof path of `result`. `schmidt_traceNorm_le_of_moment` is also used by the Conjecture 3 module, and `proj_overlap` by `SeparableStateLocalUnitaryStabilizerObstruction`.
- It reuses the frozen trace norm, triangle inequality and singular value decomposition of `FiniteTraceDistance`, the Hölder inequality of `TraceClass.IdealNorm`, `GerzonEqualityParameterIdentity.gram_pair_sum`, `ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg` and `traceNorm_isometry`, and `BornReduction.rank_one_pure_state_modulus_square_reduction`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `Reg/D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.lean` registers `result` and the six public lemmas, each `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.lean.json`, statement `sha256:76b5999014037e0e51cb975d2cc4b66e8d7a57e6fe5c308985ba47c784bb76ea`.

Declaration statements:
- `result`: `sha256:57885042b94b1c4aecb00db5627a7587914e07a56e1a2eb3120e2ad9467dd448`;
- `claim`: `sha256:4f77bee427a842cbf69cd6c99c6d708fa06806ff457fe5971280225d0a4cb4ad`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #17745 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the bound is an instantiation of the frozen trace-norm, singular-value and Hölder results, the Gram identity and Cauchy–Schwarz, followed by normalization | open-problem-resolution |
| the six public lemmas | bind-only (consumed on the proof path of `result`) | none | consumed helpers |
| the private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Conjecture 2, for every d, n > d, r ≤ d and every pair of EAMs.

**Computed, not formalized** (orchestrator, NumPy/SciPy, recorded in #17745): for simplex EAMs (n = d + 1) with d = 2 and d = 3, the maximum of ‖P_n‖_tr over pure states of Schmidt rank at most r equals [d(d − 1) + r(n − d)]/[n(n − 1)] to 1e-6 for every r, strictly below Eq. (51) for r ≥ 2.

**Argued, not formalized.**
- *Mechanism.* The proof needs only the second moment of the effects: the frame identity (49) fixes the trace part, and the constant overlap (50) makes the traceless parts of the n effects a regular simplex in an (n − 1)-dimensional space. The bound therefore holds for every measurement whose effects have this second-moment structure.
- *Where r enters.* Only through (tr H)² = (Σλ)² ≤ r, multiplied by the trace-part weight (n − d)/[n(n − 1)]; the traceless part contributes d(d − 1)/[n(n − 1)] · tr H² = d(d − 1)/[n(n − 1)] for every pure state.

**Open.** Whether the bound is attained for every n > d and r, and for EAMs that are not simplices.

**Effect on the paper.** The incomplete-EAM criterion of §V A holds at the conjectured strength.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. Wu–Tang, Phys. Rev. A 113, 022440 (2026), was assessed from its abstract only. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
