---
slug: chen-klco-2026-hildebrand-negative-index-persistence
bibkey: chenklco2026negativityrank
doi: null
url: https://arxiv.org/abs/2610.10820v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.result
---

# The one-negative-eigenvalue bound for Hildebrand's APPT matrices fails in dimension four

## Problem

M. Chen and N. Klco, *Susceptibility of qudit-qudit entanglement to quantum noise: insights from the negativity rank*, arXiv:2610.10820v1, derive the maximum purity of a qutrit-qutrit APPT state from Hildebrand's spectral criterion.
- **The criterion.** For the ordered eigenvalues λ1 ≥ … ≥ λ9 ≥ 0, ρ is APPT iff the two matrices L1, L2 of Eq. (5) are positive semidefinite (Theorem II.1, citing Hildebrand).
- **The rank bound.** "If λ⃗ is an ordered vector of qutrit-qutrit density matrix eigenvalues, then L1 and L2 of Eq. (5) have at most one negative eigenvalue" (Theorem II.2, p. 5).
- **The question.** "it may be prudent to explore whether components of the proof, e.g., the limited rank available for inequality violation established in Theorem II.2, persists for the increasing number of corresponding inequalities in qudit-qudit systems with d > 3" (§V, p. 16).

The verbatim statements are in [the literature note](../Library/QuantumBounds/chenklco2026negativityrank.md). The corresponding inequalities are Hildebrand's ([note](../Library/QuantumStates/hildebrand2007pptspectra.md)): for a pair of orderings (σ₊, σ₋) in Σ±, Λ(σ₊, σ₋) + Λ(σ₊, σ₋)ᵀ ⪰ 0.

Issue [#17687](https://github.com/the-omega-institute/trureturing/issues/17687) fixes the reading:
- S₊ = {(k, l) : k ≤ l} and S₋ = {(k, l) : k < l}, with orderings as bijections onto ranks.
- Σ± is the set of pairs compatible, in the sense of Hildebrand's Definition 1, with some x₁ > … > x_d > 0.
- L = Λ + Λᵀ has diagonal entries 2λ_{d²+1−σ₊(k,k)} and off-diagonal entries λ_{d²+1−σ₊(k,l)} − λ_{σ₋(k,l)}. For d = 3 the two pairs of Σ± give L1 and L2.
- The property: for every d > 3, every ordered spectrum (λ_k ≥ 0, Σλ_k = 1, no APPT condition, as in Theorem II.2) and every pair in Σ±, L has at most one negative eigenvalue counted with multiplicity.

The property is refuted in this reading.

## Motivation

The source's analytic maximum purity of qutrit-qutrit APPT states (§II C) rests on Theorem II.2. Since the bound of the purity confirms numerics, settles the qutrit case of a conjecture and constrains a putative APPT bound entangled state, the authors ask whether the same rank limitation survives in higher dimension, where the number of Hildebrand inequalities grows.

## Gap

Issue #17687 records the literature check before any Lean:
- arXiv v1 is the only version, and it is the latest entry of Klco's author listing;
- Hildebrand (quant-ph/0502170) states no bound on the number of negative eigenvalues of Λ + Λᵀ;
- the recent APPT papers arXiv:2609.18568, 2608.03390 and 2603.20717 state no such bound;
- the queries "negativity rank", "Hildebrand AND APPT" and "absolutely PPT" on arXiv, Naixu-Guo/quantum-open-problems, Zenodo and Crossref found no answer;
- the Semantic Scholar citation list was not retrieved (HTTP 429).

`not-found-in-searched-scope`.

## Route

1. **Witness.**
   - d = 4, λ = (13, 13, 13, 13, 1, …, 1)/64 (four entries 13/64, twelve entries 1/64).
   - x = (8, 5, 3, 1), whose ten products on S₊ are strictly decreasing in the order (1,1), (1,2), (2,2), (1,3), (2,3), (3,3), (1,4), (2,4), (3,4), (4,4). σ₊ is this order and σ₋ is the inherited order on S₋, so the pair is in Σ±.
2. **The matrix.** L = M/32 with M = [[1, −6, −6, −6], [−6, 1, −6, 0], [−6, −6, 1, 0], [−6, 0, 0, 1]].
3. **Compression.**
   - With B = [[1, 0], [0, 1], [0, 1], [1, −2]], Bᵀ L B = −H, where H = (1/16)[[5, 1], [1, 3]].
   - H = diag(1/4, 1/8) + VᵀV with V = (1/4, 1/4), so H is positive definite.
   - Hence −H has two negative eigenvalues.
4. **Inertia.** A congruence by a rectangular matrix cannot increase the number of negative eigenvalues, so L has at least two.

## Falsifier

The refutation would not settle the question if:
- the module's orderings, Σ±, spectrum indexing or matrix differed from Hildebrand's construction;
- the count were not the number of negative eigenvalues with multiplicity;
- the witness spectrum or orderings were not admissible.

The module follows Hildebrand's Definition 1 and Eq. (2) with zero-based ranks, and reproduces Eq. (5) at d = 3. The count is the number of strictly negative eigenvalues of the matrix, with real entries viewed in ℂ; a real orthogonal diagonalization is a unitary one, so the count is that of the real symmetric matrix. The witness spectrum is ordered, nonnegative and normalized, and x is strictly decreasing and positive.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.lean` (296 lines).
- It defines the orderings, `Compatible`, `Admissible`, `plusIndex`, `minusIndex`, `hildebrandArray`, `hildebrandMatrix`, `OrderedSpectrum` and `claim`, proves `hildebrandMatrix_isHermitian`, and proves `result : ¬ claim`.
- It uses:
  - the frozen index sets `Increments.UT` and `PositiveIndex`;
  - the frozen `RHLinalg.negIndex`, the number of negative eigenvalues;
  - `RHLinalg.negIndex_conj_le`, which says that a congruence does not increase it;
  - `ConfluentNegativeJetBlock.confluent_negative_jet_block`, the exact count for a negative definite congruence.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations:
  - `result` is the designated refutation result of the `utility` header and is exempt.
  - `hildebrandMatrix_isHermitian` is registered in `Reg/D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.lean`; it reads out the matrix L(λ, σ₊, σ₋). Its rejected realization, the matrix with every entry i, fails at d = 1, where Hermitian symmetry would give conj(i) = i. The registration is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.lean.json`, statement `sha256:689c58ff84c4c5169e3ca1eb77a4360d61e7df36e4e26dc5cf160cb7fef73169`.

Declaration statements:
- `result`: `sha256:751f729ff46a69f9ea082a85642aa843e3b18c4947dd4b3e367580771d6f2f26`;
- `claim`: `sha256:42d4979e5ee54324d7902868b5e84706af9dd1a5a598a9f91fe4795945e0f48d`.

## Triage

Tier 1 question of a 2026 paper, preregistered in issue #17687 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the ordering certificates, the entrywise matrix identity, the positivity of H and the inertia bound are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| hildebrandMatrix_isHermitian | bind-only (consumed by `claim`) | none | consumed helper |
| the ordering, spectrum and certificate helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** at d = 4, the ordered spectrum (13, 13, 13, 13, 1, …, 1)/64 and the admissible pair of orderings induced by x = (8, 5, 3, 1) give a Hildebrand matrix with at least two negative eigenvalues. So the rank limitation of Theorem II.2 does not persist to d = 4.

**Computed, not formalized** (orchestrator, exact rational arithmetic and NumPy, recorded in #17687):
- charpoly(M) = (t − 7)(t³ + 3t² − 117t − 103), so L has exactly two negative and two positive eigenvalues (−0.3756, −0.0271, 0.2188, 0.3090).
- Random strictly decreasing x induce 10 distinct pairs of Σ± at d = 4 and 114 at d = 5. Product ties give further pairs (for example two more at d = 4 from x = (8, 4, 2, 1)), so these counts are lower bounds.
- Over random ordered spectra, the largest number of negative eigenvalues found is 1 at d = 3 (in accordance with Theorem II.2), 2 at d = 4 and 3 at d = 5.

**Argued, not formalized.**
- *Every d ≥ 4.* Take x = (8, 5, 3, 1, ε₅, …, ε_d) with 1/8 > ε₅ > … > ε_d > 0. Every product with an index above 4 is below x₄² = 1, so σ₊ ranks the ten pairs of the leading 4 × 4 block first in the order above, and σ₋ ranks its six strict pairs first. With λ = (13, 13, 13, 13, 1, …, 1)/(d² + 48), the leading 4 × 4 block of L is 2M/(d² + 48). Compressing by B on the first four coordinates again gives two negative eigenvalues. So the property fails for every d ≥ 4.
- *Mechanism.* When the diagonal D of L is positive (the source's "Rank 9 (Alternative)" argument in Appendix A), write L = D^{1/2}(I − C)D^{1/2}; then L and I − C have the same number of negative eigenvalues.
  - At d = 3, C is then a traceless nonnegative 3 × 3 matrix with det C ≥ 0, so at most one of its eigenvalues exceeds 1.
  - At d = 4 the witness has D = (1/32)I and C = I − M. The off-diagonal entries of C are 6 on (1,2), (1,3) and (2,3), which form a triangle, and on (1,4), and 0 on (2,4) and (3,4). Its eigenvalues are 13.02, 1.87, −6 and −8.89. Two of them exceed 1, which gives the two negative eigenvalues of L.

**Open.**
- The largest number of negative eigenvalues of a Hildebrand matrix as a function of d. The sampled values 1, 2, 3 for d = 3, 4, 5 are consistent with d − 2.
- Whether the maximum APPT purity of §II C extends to d ≥ 4 by another route.

**Effect on the paper.** The component of the §II C proof that the authors propose to carry to higher dimension, the single negative eigenvalue of every Hildebrand matrix, fails from d = 4 on. The qutrit results of the paper are not affected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
