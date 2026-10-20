---
slug: wilde-2020-coherent-discrimination-triangle-refutation
bibkey: wilde2020coherentdiscrimination
doi: 10.1109/ISIT44484.2020.9174425
url: https://arxiv.org/abs/2001.02668v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result
---

# The coherent discrimination bias is not a metric on quantum channels

## Problem

M. M. Wilde, *Coherent Quantum Channel Discrimination* (IEEE ISIT 2020; arXiv:2001.02668), introduces a coherent version of channel discrimination.
- The verifier controls the two channels by a qubit R₁ in |+⟩.
- The prover supplies an input ψ_RA and processes the channel output with a unitary V_RBE′F, returning B and a flag qubit F.
- The verifier uncomputes the controlled isometric extensions and projects R₁F onto a Bell state.

The success probability p^coh_s(N⁰, N¹) is the supremum of Eq. (17) over the prover's strategies (Eq. (18)), and 1/2 ≤ p^coh_s ≤ 1 (Proposition 2). Section VI asks: "An intriguing open question is to determine if p^coh_s − 1/2 is a metric on quantum channels." The incoherent analogue p^inc_s − 1/2 is a metric: by Eq. (8) it is half the normalized diamond distance (1/2)‖N⁰ − N¹‖_⋄.

The verbatim statements are in [the literature note](../Library/QuantumChannels/wilde2020coherentdiscrimination.md).

Issue [#18289](https://github.com/the-omega-institute/trureturing/issues/18289) fixes the reading: the triangle inequality for d = p^coh_s − 1/2 on qubit channels, which a metric would satisfy. The question is answered in the negative.

## Motivation

A distinguishability measure that is a metric supports triangle-inequality arguments, such as hybrid arguments over sequences of channels. The question asks whether the coherent measure shares this property with the diamond distance.

## Gap

Issue #18289 records the literature check before any Lean:
- arXiv lists v1 only;
- the works citing the source do not settle the metric question or evaluate p^coh_s on replacement channels;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

For a probability vector t, let R_t(X) = Tr(X) diag(t₀, t₁), with Kraus operators √t_j |j⟩⟨k|. Write s_j = √(t_j² + u_j²).

1. **Upper bound.** Fix a strategy. Through the replacement structure, the uncomputed amplitude equals (1/2)Σ_j (t_j Q_{0j} + u_j Q_{1j}) applied to the components of ψ. Here Q_{ij} is the block of the prover's unitary V from (B = j, E′ = 0, F = 0) to (B = j, F = i).
   - Unitarity gives ‖Q_{0j}v‖² + ‖Q_{1j}v‖² ≤ ‖v‖².
   - The triangle and Cauchy–Schwarz inequalities then give p^coh_s(R_t, R_u) ≤ (s₀ + s₁)²/4.
2. **Attainment.** The controlled rotation of F by (1/s_j)[[t_j, −u_j], [u_j, t_j]] on B = j reaches the bound, so p^coh_s(R_t, R_u) = (s₀ + s₁)²/4.
3. **The triangle.** For a = (3/4, 1/4), b = (1/2, 1/2) and c = (1/4, 3/4):
   - d(R_a, R_c) = 1/8;
   - d(R_a, R_b) = d(R_b, R_c) = (√65 − 7)/32, whose sum (√65 − 7)/16 is less than 1/8 because √65 < 9.

## Falsifier

The refutation would not answer the question if:
- the module's success probability differed from Eq. (17);
- the supremum differed from Eq. (18);
- the claim were not implied by the metric property.

The module takes:
- the canonical isometric extension of a Kraus family;
- the prover's unitary on R, B, E′ and F with E untouched;
- the uncomputation and the Bell projection of Eq. (17), with the factor 1/4 from the 1/2 of Eq. (17) and the 1/√2 of the Bell bra;
- the supremum over all finite reference and ancilla types, unit inputs and unitaries, with the zero of the ancilla named explicitly.

The source notes after Eq. (17) that the value does not depend on the isometric extension, so the metric property implies the triangle inequality on these Kraus families.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.lean` (375 lines).
- It defines `extend`, `successProbability`, `coherentValue` and `claim`, and proves `result : ¬ claim`.
- It reuses:
  - the Kraus normalization `IsKrausChannel` of `OutputMaximalCoherenceTensorizationRefutation`;
  - the controlled matrix `controlled` of `PositivePauliClockOrder` with its unitarity `controlled_unitary`, made public by removing only `private`;
  - Mathlib's unitary norm preservation.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The newly public `PositivePauliClockOrder.controlled_unitary` is registered in `Reg/D5/S3/Quantum/Dynamics/PositivePauliClockOrder.lean`, `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.lean.json`, statement `sha256:949b7818c9a6c69bbaa4c4468b03ee0e02073744ea7036a51aaf90c14cb4c17c`.

Declaration statements:
- `result`: `sha256:85de01fa5f4e3fb91e2578a9010304910fc4ce2838fe6d2f303aa0fbf525bed7`;
- `claim`: `sha256:e256919e05fc898409572a34d70548cac79c84ab5c817f5c454df0a3125805fe`.

## Triage

Tier 1 question of a 2020 paper, preregistered in issue #18289 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the block identity, the unitarity bound, the Cauchy–Schwarz step and the attaining rotation are instantiations of existing lemmas and finite identities, and the triangle defect is arithmetic | open-problem-resolution |
| the witness, block and bound helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every public declaration is bind-only; the definitions are used by public statements. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** for the replacement channels R_a, R_b, R_c, d(R_a, R_c) exceeds d(R_a, R_b) + d(R_b, R_c) by (9 − √65)/16.

**Proved in the module, in the generality used:** p^coh_s(R_t, R_u) = (s₀ + s₁)²/4 for the replacement channels with strictly positive t and u.

**Argued, not formalized.**
- *Mechanism.* On replacement channels d(R_t, R_u) = M + M²/2 with M = Σ_j √((t_j² + u_j²)/2) − 1. Near the diagonal d is of quadratic order in t − u, and a quantity of quadratic order cannot satisfy the triangle inequality along a segment. The incoherent bias p^inc_s − 1/2 is of first order: for replacement channels it is half the trace distance of diag(t) and diag(u).
- *Open.* Whether √(p^coh_s − 1/2), or another function of p^coh_s, is a metric on channels is not addressed. The search seat relates M to a classical mean divergence whose square root is a metric (seat-reported, recorded in #18289).

**Effect on the paper.** Unlike p^inc_s − 1/2, the coherent bias p^coh_s − 1/2 is not a metric, already for qubit replacement channels with full-rank Choi matrices.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
