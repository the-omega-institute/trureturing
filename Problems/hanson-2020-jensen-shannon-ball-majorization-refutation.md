---
slug: hanson-2020-jensen-shannon-ball-majorization-refutation
bibkey: hanson2020entropiccontinuity
doi: null
url: https://arxiv.org/abs/2010.02408v1
triage: theorem
motivation_gids:
  - D5/S3/Divergence/JensenShannonBallMajorizationRefutation.result
---

# Square-root Jensen–Shannon balls need not admit majorization-minimizers

## Problem

E. P. Hanson, *Entropic Continuity Bounds & Eventually Entanglement-Breaking Channels* (PhD thesis, Cambridge, 2020; arXiv:2010.02408), derives continuity bounds for Schur-concave functions from the majorization structure of total-variation balls.
- Every total-variation ball in the probability simplex contains a majorization-minimizer r∗, with r∗ ≺ q for every q in the ball (Eq. (3.1)). Every Schur-concave function, such as an entropy, attains its maximum over the ball at r∗.
- For p-norm balls with 1 < p < ∞ no such element exists (Section 3.7).
- Chapter 8, Question 1 asks: "Do balls in Hellinger distance, Bures distance, the (square-root) Shannon-Jensen divergence, Wasserstein distances, or other metrics on P admit majorization-minimizers?"

The verbatim statements are in [the literature note](../Library/Divergence/hanson2020entropiccontinuity.md).

Issue [#18189](https://github.com/the-omega-institute/trureturing/issues/18189) fixes the reading of the Jensen–Shannon clause: for every probability vector p and every positive radius, the square-root Jensen–Shannon ball around p has a majorization-minimizer. This clause is answered in the negative.

## Motivation

A majorization-minimizer of a ball maximizes every Schur-concave function over the ball at once, which gives universal local continuity bounds for entropies. The question asks which distances share this property with the total variation distance. For the Jensen–Shannon distance, a positive answer would transfer the majorization-flow method of the thesis to a smooth information-theoretic metric.

## Gap

Issue #18189 records the literature check before any Lean:
- arXiv lists v1 only;
- the full texts of the works citing the thesis, and of the closest predecessors on ℓ^p balls (arXiv:2001.08766) and smoothed divergences (arXiv:2603.09885), contain no Jensen–Shannon ball result;
- the repository had no record of the thesis.

`not-found-in-searched-scope`.

## Route

Let J(p, q) = (1/2) Σᵢ [pᵢ ln(2pᵢ/(pᵢ + qᵢ)) + qᵢ ln(2qᵢ/(pᵢ + qᵢ))]. The square-root ball of radius ε is the sublevel set {q : J(p, q) ≤ ε² ln 2}. Take d = 3 and:
- p = (2/3, 4/15, 1/15), a = (1/2, 2/5, 1/10) and b = (8/15, 1/3, 2/15);
- the threshold t = J(p, a) > 0.

1. **Supporting line.** For c > 0, x ≥ 0 and y > 0, the term f_c(x) = (1/2)[c ln(2c/(c + x)) + x ln(2x/(c + x))] satisfies f_c(x) ≥ f_c(y) + (1/2) ln(2y/(c + y))(x − y), with equality only at x = y. This follows from ln z ≤ z − 1.
2. **Only a can be a minimizer.** At a the slopes are (1/2)(ln(6/7), ln(6/5), ln(6/5)). Summing over the coordinates, J(p, r) ≥ t + (1/2) ln(5/7)(r₁ − 1/2) for every probability vector r.
   - A majorization-minimizer r satisfies r ≺ a, so its largest entry is at most 1/2.
   - Since ln(5/7) < 0, it follows that J(p, r) ≥ t, with equality only at r = a.
3. **b lies in the ball.** 60(J(p, b) − t) = ln(4·5⁵⁵·7³⁵/3¹⁴⁴), and 4·5⁵⁵·7³⁵ < 3¹⁴⁴.
4. **a is not majorized by b.** The two largest entries of a sum to 9/10 > 13/15, the corresponding sum for b. So the ball has no majorization-minimizer.

## Falsifier

The refutation would not settle the clause if:
- the module's divergence, ball, majorization or minimizer differed from the thesis;
- the claim restricted the quantifiers of the question.

The module takes:
- the Jensen–Shannon divergence with the natural logarithm and the convention 0 · ln(·) = 0;
- the ball as the sublevel set {q : J(p, q) ≤ t}, t > 0, which is the square-root ball after rescaling the radius;
- majorization as the descending partial sums of Eq. (2.3), through the repository predicate `moreMixed`;
- the minimizer as a member majorized by every member, as in Eq. (3.1);
- the claim over every d, every probability vector p and every t > 0.

## Evidence

The canonical source is `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.lean` (306 lines).
- It defines `jensenShannon`, `IsMajorizationMinimizer` and `claim`, and proves `result : ¬ claim`.
- It reuses the probability predicate `Probability` of `CycleSingleCutMinimax`, the majorization predicate `moreMixed` with `desc` and `prefixSum` of `PositiveSimplexGeometryAndMixing`, and the Mathlib logarithm inequalities and identities.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Divergence/JensenShannonBallMajorizationRefutation.lean.json`, statement `sha256:0c5f1bf96657516834fe6c2cd1b20367980ae0acf1578b82f7a4f78690b4a78d`.

Declaration statements:
- `result`: `sha256:0625acaddc356ae107c5b8837b25f20b6016fc71206649eef373593d2ca15bf3`;
- `claim`: `sha256:506d6bae465fd268301e961d62f210c1e04f3a1d9e7c9e569de75d451343a685`.

## Triage

Tier 1 question of a 2020 thesis, preregistered in issue #18189 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the supporting-line bound, the majorization bounds and the logarithm comparison are elementary inequalities and identities | open-problem-resolution |
| the witness and inequality helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every public declaration is bind-only; the definitions are used by public statements. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** the Jensen–Shannon ball around p = (2/3, 4/15, 1/15) with threshold J(p, a) has no majorization-minimizer.

**Argued, not formalized.**
- *Mechanism.* Step 2 shows that every other point of the ball has first entry above 1/2, so a is the unique point of the ball whose largest entry is at most 1/2. This comes from the agreement of the slopes of J(p, ·) at a on the second and third coordinates. The point b raises the smallest entry above 1/10 while staying inside the ball. Minimizing the largest entry and maximizing the smallest entry are incompatible requirements, as for the p-norm balls of Section 3.7.
- *Scope.* The construction uses the smoothness and strict convexity of J(p, ·) at a point of the boundary where two slopes coincide. The answer to the other clauses of Question 1 is not addressed here.

**Effect on the thesis.** The majorization-flow method of the thesis does not extend to Jensen–Shannon balls. Since r ≺ q holds exactly when Σ g(rᵢ) ≤ Σ g(qᵢ) for every convex g, no single point of this ball maximizes every Schur-concave function.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
