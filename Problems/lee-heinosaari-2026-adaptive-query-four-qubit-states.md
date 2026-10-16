---
slug: lee-heinosaari-2026-adaptive-query-four-qubit-states
bibkey: leeheinosaari2026adaptivequery
doi: null
url: https://arxiv.org/abs/2608.01167v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.result
---

# A four-state qubit ensemble where an adaptive post-measurement query beats a pre-measurement query

## Problem

H. Lee and T. Heinosaari, *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*, arXiv:2608.01167v1, study state discrimination with a one-bit query.
- **Pre-measurement query.** P_pre maximizes, over the binary partitions of the symbols and the measurements of the two subensembles, the success probability after the answer is known (Eq. (3)).
- **Adaptive post-measurement query.** P^adap_post maximizes over a measurement whose outcome selects the partition and the guesses (Eq. (5)).
- **The suggestion.** "A relevant question is whether there exists an ensemble of four qubit states with this property. … These examples suggest that P^adap_post > P_pre may never occur for qubit ensembles with n ≥ 4, though we leave a proof as an open question" (§VI, p. 6).

The verbatim statements are in [the literature note](../Library/QuantumBounds/leeheinosaari2026adaptivequery.md).

Issue [#17780](https://github.com/the-omega-institute/trureturing/issues/17780) fixes the reading: for every n ≥ 4 and every ensemble of n qubit states (priors q_x ≥ 0 with Σ q_x = 1 and 2 × 2 density matrices), P^adap_post ≤ P_pre. This suggestion is refuted, and the §VI question is answered affirmatively, by an ensemble of four qubit states.

## Motivation

For three states the source finds ensembles, such as the trine, where the adaptive query wins, even with perfect discrimination of non-orthogonal states. Its two symmetric four-state candidates, the tetrahedron and the lifted BB84 states, give P^adap_post < P_pre. Whether four qubit states can show the advantage decides whether the effect is confined to three-state qubit ensembles.

## Gap

Issue #17780 records the literature check before any Lean:
- arXiv v1 is the only version;
- the arXiv queries "adaptive post-measurement" and "post-measurement query" return only the source, and the authors' later arXiv records do not treat the question;
- the older works on post-measurement information (quant-ph/0608014, 1003.0716, 1804.09693, 2109.03581) treat outcome-independent information;
- Naixu-Guo/quantum-open-problems and Zenodo have no entry, and the repository had none;
- the Semantic Scholar and Google Scholar citation lists were not retrieved.

`not-found-in-searched-scope`.

## Route

1. **Witness.** Priors (33, 33, 33, 1)/100 and the pure states
   - ϱ₁ = [[1, 0], [0, 0]];
   - ϱ₂ = [[1, 2], [2, 4]]/5;
   - ϱ₃ = [[1, −2], [−2, 4]]/5;
   - ϱ₄ = [[1, 1], [1, 1]]/2.

   They are pairwise non-orthogonal, with overlaps between 1/10 and 9/10.
2. **Adaptive strategy.** The measurement M₁ = [[0, 0], [0, 3/4]], M₂ = [[4, −2], [−2, 1]]/8, M₃ = [[4, 2], [2, 1]]/8 satisfies tr ϱ_z M_z = 0 for z = 1, 2, 3. At outcome z the query separates the other two of the first three symbols. Every occurrence of the symbols 1, 2, 3 is identified, so the value is 99/100.
3. **Pre-measurement bound.** For each of the 8 partitions and each nonempty cell C, a rational matrix Y_C with Y_C ⪰ q_x ϱ_x for all x ∈ C bounds the success on C by tr Y_C. The largest total is 483/500, at the partition {1, 2} | {3, 4}.
4. **Conclusion.** P_pre ≤ 483/500 < 99/100 ≤ P^adap_post.

## Falsifier

The refutation would not settle the suggestion if:
- the module's strategies or values differed from Eqs. (3) and (5);
- its pre-measurement bound missed a partition, a measurement or an empty cell;
- its witness were not an ensemble of four qubit states.

The module admits every partition, with normalization required only on a nonempty cell, every finite measurement on each cell, and every finite adaptive measurement with outcome-dependent partitions and guesses. The witness has strictly positive priors summing to one and four distinct qubit density matrices.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.lean` (262 lines).
- It defines `IsEnsemble`, `IsPOVM`, `IsPreStrategy`, `preValue`, `Ppre`, `IsAdaptiveStrategy`, `adaptiveValue` and `claim`, and proves `result : ¬ claim`.
- `IsPOVM` reuses the existing POVM predicate of `ConcealmentKernelNecessityRefutation`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.lean.json`, statement `sha256:68bd5e384a798f3a1dbf1696c4e469b6220c0c145b85bd05afefbc984a853065`.

Declaration statements:
- `result`: `sha256:bf2ca012361be9ec94978343f5fb821276d74759ee9e6d1cd879a911195f41c4`;
- `claim`: `sha256:bdd682a2c48d82e044cea562a7180ed1be88e8c661b7ed443eb9b54cbc2b0f3d`.

## Triage

Tier 1 question of a 2026 paper, preregistered in issue #17780 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the adaptive value, the positivity of the certificates and the trace inequalities are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| the strategy, certificate and bound helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** for the ensemble above, every pre-measurement strategy succeeds with probability at most 483/500, while an adaptive post-measurement strategy succeeds with probability 99/100. So P^adap_post > P_pre for an ensemble of four qubit states.

**Computed, not formalized** (orchestrator, CVXPY/SciPy, recorded in #17780):
- the exact optimum is P_pre ≈ 0.96419;
- with uniform priors, 40 random ensembles of four pure qubit states give P^adap_post − P_pre ≤ −0.013, and the trine with a fourth state at the pole, on the equator or tilted gives −0.114, −0.136 and −0.078;
- with the fourth prior lowered to 0.05 or 0.02, these three families show an advantage of 0.008 to 0.034.

**Argued, not formalized.**
- *Mechanism.* The first three states are antidistinguishable: each outcome of the three-element measurement excludes one of them, so an adaptive query after the outcome identifies the remaining two. A pre-measurement query must place two of the three heavy states in one cell, where their overlap limits any measurement. The fourth state carries a small prior, which bounds what the adaptive strategy loses on it.
- *Scope.* Keep ϱ₁, ϱ₂, ϱ₃ with priors (1 − q₄)/3 each and take any fourth state with prior q₄.
  - The adaptive strategy above gives P^adap_post ≥ 1 − q₄.
  - Dropping the fourth symbol from a pre-measurement strategy leaves a strategy for the three heavy states, so P_pre ≤ (1 − q₄)P₃ + q₄, where P₃ is the pre-measurement value of ϱ₁, ϱ₂, ϱ₃ with equal priors.
  - Hence the advantage holds whenever (1 − q₄)(1 − P₃) > q₄. P₃ ≈ 0.9648 (computed), so the threshold is q₄ < (1 − P₃)/(2 − P₃) ≈ 0.034, for every fourth state.

**Open.**
- Whether P^adap_post > P_pre can occur for four qubit states with uniform priors, the setting of the source's two tested candidates; the numerical readings above found no instance.
- The largest n for which some qubit ensemble shows the advantage.

**Effect on the paper.** The suggestion that P^adap_post > P_pre may never occur for qubit ensembles with n ≥ 4 fails in the source's framework with general priors, and the §VI question has a positive answer. The uniform-prior form of the suggestion remains open.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
