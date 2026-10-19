---
slug: cao-fitzsimmons-mann-pereira-laflamme-2023-semi-nonnegative-backflow-refutation
bibkey: caofitzsimmonsmannpereiralaflamme2023cptphptp
doi: null
url: https://arxiv.org/abs/2308.01894v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.result
---

# A non-semi-positive semi-nonnegative qutrit map can signal information backflow

## Problem

N. Cao, M. Fitzsimmons, Z. Mann, R. Pereira and R. Laflamme, *Quantum Maps Between CPTP and HPTP*, arXiv:2308.01894, classify the Hermiticity-preserving trace-preserving (HPTP) maps that can describe the evolution of an open system.
- A map is semi-nonnegative (SN) if it sends some density matrix to a density matrix (Definition 2), equivalently if Ψ ∘ Φ = Ξ for some CPTP Φ and Ξ (Theorem 2).
- It is semi-positive (SP) if it sends some invertible density matrix to an invertible one (Definition 1). SP maps are the intermediate maps of CP-indivisible, non-Markovian evolutions.
- For qubits, the non-SP SN maps send only one pure state to a state, so they "signal no information backflow".
- The Outlook conjectures: "We conjecture that non-SP SNTP maps still signal no information backflow and are not uniquely defined even for higher dimensional H."

The verbatim statements are in [the literature note](../Library/QuantumChannels/caofitzsimmonsmannpereiralaflamme2023cptphptp.md).

Issue [#18048](https://github.com/the-omega-institute/trureturing/issues/18048) fixes the reading of the first conjunct: in every context Ψ ∘ Φ = Ξ of a non-SP SNTP map, the intermediate map does not increase the trace distance of two states. This conjunct, and with it the conjecture, is refuted.

## Motivation

Information backflow, an increase of distinguishability, is the operational signature of non-Markovian evolution in the trace-distance sense that the source cites. The conjecture would place all non-SP SN maps among the dynamics without such a signature, separating them from the SP maps that describe non-Markovian evolutions.

## Gap

Issue #18048 records the literature check before any Lean:
- arXiv lists v1 only, and Crossref finds no journal version;
- the follow-up arXiv:2503.07745 by a coauthor does not treat SN maps;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

1. **The map.** On 3 × 3 matrices X = [[A, u], [v, c]], with A of size 2 × 2, let Ψ(X) = [[2A − (tr A)1/2 + c·1, u], [v, −c]].
   - Ψ is linear, Hermiticity-preserving and trace-preserving.
   - It is SN, since Ψ(P/2) = P/2 for P = diag(1, 1, 0).
   - It is not SP: every positive-definite X has c > 0, and then Ψ(X) has the negative entry −c on the diagonal.
2. **The context.** Ξ(X) = PXP + x₃₃P/2 and Φ(X) = Ξ(X)/2 + (tr X)P/4 are CPTP, with explicit rational Kraus families, and Ψ ∘ Φ = Ξ.
3. **The backflow.** For σ± = diag(5/8, 1/8, 1/4) and diag(1/8, 5/8, 1/4), the states Φσ± are at trace distance 1/4, and Ξσ± = Ψ(Φσ±) are at trace distance 1/2.

## Falsifier

The refutation would not settle the conjecture if:
- the module's SP or SN differed from Definitions 1–2;
- its context differed from Theorem 2;
- its backflow differed from the trace-distance notion of the source's references [11] and [20].

The module takes:
- SP as a positive-definite density with a positive-definite density image;
- SN as a density with a density image;
- the context as Kraus channels Φ, Ξ with Ψ ∘ Φ = Ξ;
- backflow as an increase of ‖ρ − σ‖₁/2.

Ψ is invertible on 3 × 3 matrices, so the reduction to SPR in Definition 1 does not change it.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.lean` (216 lines).
- It defines `IsHPTP`, `IsSemiPositive`, `IsSemiNonnegative`, `traceDistance` and `claim`, and proves `result : ¬ claim`.
- It reuses the density predicate of `CoPRelativeQuantumnessRefutation`, the Kraus action `krausApply` and the normalization `IsKrausChannel` of `OutputMaximalCoherenceTensorizationRefutation`, and the trace norm of `FiniteTraceDistance`. It also reuses the diagonal trace-norm lemma `diagonal_norm` of `ChenKatoBrandaoTraceNormCMIRefutation`, made public by removing only `private`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The newly public `ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm` is registered in `Reg/D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.lean`, `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.lean.json`, statement `sha256:2f244fc4d5f4910437aa699f7069856fbd672e058b76180929ab5e5289d87bae`.

Declaration statements:
- `result`: `sha256:ecdc3caab3f17d5e83bf6eb017699bdda224072e784c69d138c8753534e515de`;
- `claim`: `sha256:f6953d2de7b2e24bce47a42225dca26e204aa59d343d89f4e7b9b0d8aed9c020`.

## Triage

Tier 1 conjecture of a 2023 paper, preregistered in issue #18048 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the map properties, the Kraus normalizations and the context are 3 × 3 matrix identities, and the distances are diagonal trace norms | open-problem-resolution |
| the witness and distance helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every public declaration is bind-only; the definitions are used by public statements. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** the qutrit map Ψ above is HPTP, SN and not SP, and in the context Ψ ∘ Φ = Ξ it doubles the trace distance of Φσ₊ and Φσ₋.

**Argued, not formalized** (orchestrator, recorded in #18048).
- *Physical domain.* The states with a density image under Ψ form the set {A ⊕ 0 : tr A = 1, A ≥ 1/4}, a portion of the rank-two face {A ⊕ 0 : tr A = 1, A ≥ 0} of the state space. On it Ψ acts as A ↦ 2A − 1/2, which doubles every traceless difference.
- *Mechanism.* The source's qubit argument relies on the physical domain being a single pure state. In dimension 3 the domain can be a set of positive dimension inside a face of the state space, as the source anticipates for its facets, and an expanding map on that facet signals backflow. The expanding block is the qubit repolarization of Dominy and Lidar (search seat, recorded in #18048).

**Open.** The second conjunct, that non-SP SNTP maps are not uniquely defined in higher dimensions, is not addressed.

**Effect on the paper.** Failure of semi-positivity does not rule out information backflow in dimension 3. The qubit statement of the Outlook does not extend.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
