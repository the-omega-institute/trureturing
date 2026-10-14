---
slug: santalla-singha-roy-sierra-rodriguez-laguna-2026-even-legged-reconstruction
bibkey: santalla2026hyperlink
doi: 10.1103/gmjw-rb13
url: https://arxiv.org/abs/2601.17926v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.result
---

# Even-legged hyperlinks reconstruct the entanglement entropies with N-independent leg-factors

## Problem

S. N. Santalla, S. Singha Roy, G. Sierra and J. Rodríguez-Laguna, *The hyperlink representation of entanglement and the inclusion-exclusion principle*, arXiv:2601.17926v2, Phys. Rev. A **114**, 022431 (2026), define the entanglement hyperlinks J_I = Σ_{A⊆I} (−1)^{|I|−|A|} S_A of the entanglement entropies S_A of a pure state on N parties (Eq. (5)).

Appendix B proposes the even-legged reconstruction S_A = Σ_{|I| even} Λ_{|I|,|I∩A|} J_I (B2), with Λ_{2l,0} = Λ_{2l,2l} = 0 and Λ_{2l,p} = Λ_{2l,2l−p}. It lists the leg-factors for 2l ≤ 8 (B5) and states: "It is still to be proved that the leg-factors Λ_{2l,p} exist and do not depend on N" and "the validity of Eq. (B2), with leg-factors that do not depend on N, has only been checked up to N = 9". The verbatim statements are in [the literature note](../Library/Entropy/santalla2026hyperlink.md).

Issue [#16381](https://github.com/the-omega-institute/trureturing/issues/16381) fixes the reading: there are leg-factors, independent of N, with the zero and symmetry laws, such that (B2) holds for every N. It is proved.

## Motivation

(B2) halves the data needed to describe the entanglement of a pure state: only the 2^{N−1} − 1 even-ranked hyperlinks are needed, as many as the independent bipartitions. Universal leg-factors also make the reconstruction usable at every system size without solving a new linear system.

## Gap

Issue #16381 records the literature check before any Lean:
- arXiv v2 is the latest version and keeps the conjecture;
- the Pith review page calls the leg-factors' existence "plausible but unproven";
- the one citing work (arXiv:2503.17230) does not address the inverse;
- Zenodo and web searches return no settlement;
- the repository had no entry for the paper.

The general set-function basis results of Faigle–Grabisch and Grabisch could not be read, and this is recorded as a priority limitation.

`not-found-in-searched-scope`.

## Route

The theorem is proved for every real set function S on the subsets of N parties with S(∅) = 0 and S(A) = S(Ω ∖ A). The source's closing paragraph places the reconstruction on exactly these "vectors S with a special symmetry".
1. **Möbius inversion.** Σ_{I⊆A} J_I = S_A, and conversely.
2. **The complement transform.** The hyperlinks of A ↦ S(Ω ∖ A) are J'_I = (−1)^{|I|} Σ_{K⊇I} J_K.
3. **Uniqueness.** For complement-symmetric S with S(∅) = 0, the odd hyperlinks are determined by the even ones (descending induction on |I|), so the even nonempty hyperlinks determine S.
4. **A spanning family.** For nonempty K, q_K(A) = (1_{K⊆A} + 1_{K⊆Ω∖A} − 1)/2 is complement-symmetric and vanishes at ∅. Its even hyperlinks are 1 at I = K, 1/2 for even I ⊊ K, and 0 otherwise.
5. **Inversion.** The numbers c₀ = 1, c_r = 0 for odd r, and c_r = −(1/2) Σ_{j<r, j even} C(r, j) c_j for even r > 0 invert this triangular system. Hence S = Σ_K h_K q_K with h_I = Σ_{K⊇I, |K| even} c_{|K∖I|} J_K.
6. **Evaluation.** Counting the k-subsets of I that meet both A and Ω ∖ A gives (B2) with Λ_{m,p} = −(1/2) Σ_{2≤k≤m, k even} c_{m−k} [C(m,k) − C(p,k) − C(m−p,k)]. This expression depends only on m and p, vanishes at p = 0 and p = m, and is symmetric.

## Falsifier

The proof would not settle the conjecture if:
- the module's hyperlinks differed from Eq. (5);
- its sum differed from (B2)'s sum over even-ranked hyperlinks with p = |I ∩ A|;
- the entanglement entropies of a pure state failed S(∅) = 0 or S(A) = S(Ω ∖ A).

Both identities hold: complementary reduced states of a pure state have the same nonzero spectrum, by the singular values of the coefficient matrix across the cut, and the empty block has entropy 0. This identification is mathematical background and is not formalized in the module.

## Evidence

The canonical source is `D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.lean` (659 lines).
- It defines `hyperlink`, `legInverseCoeff`, `legFactor` and `claim`, and proves `result : claim`.
- It uses Mathlib's powerset and cardinality API, `Finset.sum_powerset_neg_one_pow_card`, `Finset.sum_powerset_apply_card` and `Nat.strongRec`; it has no frozen D5 dependency.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.lean` reads out the coefficient family of `claim`. Its rejected realization, the zero family, fails at N = 2 on the complement-symmetric function equal to 1 on singletons. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.lean.json`, statement `sha256:c1a2ee9571bd964047381546931624d50a75a8bdd71a1280b5aa3368aef5a49e`.

Declaration statements:
- `result`: `sha256:d1e2a640995787198bec6081f56dca5d84636148876b21dc8fa4d2fa35d70fbf`;
- `claim`: `sha256:9c006cc99bf50eaf09992cdaa578085d949ed96b9850a8a221498b91570c553b`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #16381 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the route instantiates pinned Mathlib powerset, cardinality and alternating-sum results and normalizes; the uniqueness step also follows from a triangular determinant | open-problem-resolution |
| the Möbius, complement, uniqueness, q-family, interval-inverse, synthesis and counting helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the even-legged reconstruction (B2) holds for every N, with the explicit rational leg-factors above, independent of N. It holds for every real complement-symmetric set function vanishing at ∅, so positivity, subadditivity and realizability by a quantum state are not needed.

**Established inside the proof.**
- For such functions the odd-ranked hyperlinks are determined by the even-ranked ones: J_I = −(1/2) Σ_{K⊋I} J_K for odd |I|. This confirms the source's remark that "odd-ranked EHLs can be obtained from the even-ranked ones".
- The coefficients c_r invert the triangular system J_I = h_I + (1/2) Σ_{K⊋I even} h_K.

**Computed, not formalized** (orchestrator, exact rational arithmetic, 14 October 2026):
- the leg-factors reproduce all ten values of (B5);
- they give Λ_{10,1..5} = −31/2, −31, −355/8, −107/2, −227/4;
- (B2) reconstructs random complement-symmetric functions exactly for N = 2, …, 11 and fails for random non-symmetric ones.
- The source's sign pattern, "Λ_{2l,p} is negative whenever l is odd", and positive when l is even, holds for every 2l ≤ 40 and 1 ≤ p ≤ 2l − 1.

**Argued, not formalized.**
- (B2) gives a closed form for the source's iterative determination of the leg-factors, which solved a new linear equation at each even N.
- Every pure-state entropy vector is complement-symmetric with S(∅) = 0, so (B2) holds for all pure states. For mixed states S(A) ≠ S(Ω ∖ A) in general, and (B2) does not apply. The theorem identifies exactly which property of pure states the reconstruction uses.

**Open.**
- Whether the leg-factors are the unique N-independent choice. For a fixed N, several inverses exist, as the source notes.
- The sign pattern of the leg-factors for 2l > 40.

**Effect on the paper.** Appendix B's conjecture is a theorem, the leg-factors are explicit for every rank, and the restriction "checked up to N = 9" is removed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the general set-function basis literature named in #16381 was not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
