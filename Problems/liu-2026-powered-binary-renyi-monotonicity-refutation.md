---
slug: liu-2026-powered-binary-renyi-monotonicity-refutation
bibkey: liu2026binaryentropybounds
doi: 10.4230/LIPIcs.STACS.2026.66
url: https://arxiv.org/abs/2601.03734v2
triage: theorem
motivation_gids:
  - D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.result
---

# The powered binary Rényi entropy is not monotone in the order

## Problem

Y. Liu, *Computational hardness of estimating quantum entropies via binary entropy bounds*, arXiv:2601.03734v2, Section 1.4(b):

> Can the inequalities in \Cref{table:Rank2RenyiQEA-hardness} be tightened? For instance, is it possible to prove that $\rbra[\big]{\frac{\Halpha(x)}{\ln(2)}}^{2/\alpha}$ is monotonically non-decreasing in $\alpha$ for all fixed $x\in[0,1]$, as suggested by numerical evidence and as a generalization of \Cref{thm:Renyi-binary-entropy-upper-bound-0leAle2}?

Here H^R_α(x) = ln(x^α + (1−x)^α)/(1−α). The verbatim passages are in [the literature note](../Library/Entropy/liu2026binaryentropybounds.md).

Issue [#19090](https://github.com/the-omega-institute/trureturing/issues/19090) fixes the reading: for every x ∈ [0, 1] and all orders 0 < a < b with a, b ≠ 1, (H_a(x)/ln 2)^{2/a} ≤ (H_b(x)/ln 2)^{2/b}. It is refuted.

## Motivation

The comparison with order 2 (the source's Theorem 3.4) transfers hardness results between Rényi orders for rank-2 states. Monotonicity in the order would tighten all such comparisons at once.

## Gap

The literature check before any Lean is recorded in #19090:
- arXiv v2 is the latest version and keeps the question;
- OpenAlex lists no citing work;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Take x = 1/17. Since √(1/17) + √(16/17) = 5/√17 and (1/17)^{1/4} + (16/17)^{1/4} = 3·17^{−1/4}:
- H_{1/2}(1/17) = ln(25/17);
- H_{1/4}(1/17) = (4/3)(ln 3 − (ln 17)/4).

So the powered values are ((4/3)(ln 3 − ln 17/4)/ln 2)^8 at α = 1/4 and (ln(25/17)/ln 2)^4 at α = 1/2. The proof compares these two numbers through logarithm inequalities, so the value at the larger order is strictly smaller.

## Falsifier

The refutation would fail if the module's quantities differed from the source's. The module:
- uses the frozen `BinaryRenyiCombining.hRenyi alpha p = (1/(1 − alpha)) · log(p^alpha + (1 − p)^alpha)`, the source's definition;
- uses natural logarithms and a real power 2/α;
- excludes α = 1, where the source uses the Shannon limit.

## Evidence

The canonical source is `D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.lean` (112 lines).
- **Proof.** It proves `result : ¬ claim` for the instance above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.lean.json`, statement `sha256:92fe6351144bbcfcd2014a8f23f9b2575156e9fd64c30c100c9c145bad4e8580`.

Declaration statements:
- `result`: `sha256:791f52ccb714fe9d2057a240f4c475283e971276d0d376c9e8b3c0746bb4f689`;
- `claim`: `sha256:2151ee2ee44b5898afa0f28c0985969683018255c567f192940aa7774c5ff9c2`.

## Triage

Tier 1 question of a 2026 paper, preregistered in issue #19090 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |
| `powered`, `claim` | bind-only | none | definitions used by `claim` |
| private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** at x = 1/17 the powered entropy is larger at order 1/4 than at order 1/2.

**Computed, not formalized** (orchestrator, recorded in #19090):
- the values are 0.100966 and 0.095836;
- for 497 of 500 sampled x ∈ (0, 1/2], the powered entropy decreases somewhere in α ∈ (0, 4];
- at x = 1/17 its sampled minimum lies near α = 0.6 (0.0957), and the values rise on both sides;
- on α ∈ [1.01, 4] no decrease was found for the same 500 values of x.

**Argued, not formalized.**
- *Scope.* The proved comparison with order 2 (the source's Theorem 3.4) is unaffected. The failure lies at small orders.
- *Open.* Whether monotonicity holds on α > 1, as the sampling suggests, is not determined here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
