---
slug: janssen-2025-annealed-potts-moment-lower-bound-refutation
bibkey: janssen2025annealedpotts
doi: null
url: https://arxiv.org/abs/2508.21409v3
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.result
---

# A weight density below Janssen's moment lower bound for the annealed Potts critical parameter

## Problem

A. J. E. M. Janssen, *Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights*, arXiv:2508.21409v3, Section 6:

> In fact, a limited numerical exploration with some other pdfs (like the exponential $\exp({-}w)\,\cax_{[0,\infty)}(w)$ and $\cax_{[0,1)}(w)$) shows that there may hold more generally
> 2\,\frac{\mu_3}{\mu_4}\,{\rm ln}(q-1)<t_c<2\,\frac{\mu_0}{\mu_1}\,{\rm ln}(q-1)~, ~~~~~~q>2~,

Here 𝓕₀ and 𝒦 are defined in Section 1. Under the standing assumption that 𝓕₀'' is first positive and then negative, t_c is the unique positive zero of 𝒦. The verbatim definitions are in [the literature note](../Library/StatisticalMechanics/janssen2025annealedpotts.md).

Issue [#18836](https://github.com/the-omega-institute/trureturing/issues/18836) fixes the reading: the lower inequality, for every q > 2 and every probability density on (0, ∞) with finite fourth moment satisfying the standing assumption and the uniqueness of the positive zero of 𝒦. It is refuted.

## Motivation

t_c determines the critical inverse temperature of the annealed Potts model on sparse rank-1 random graphs. A bound by low-order moments of the vertex weights would locate the transition without solving for the zero of 𝒦.

## Gap

The literature check before any Lean is recorded in #18836:
- arXiv v3 (2026-07-14) is the latest version and keeps the bounds as a suggestion from numerics;
- OpenAlex `W4415990031` lists no citing work;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Take q = 3 and the density of W = A + U, where P(A = 1) = 1331/1340, P(A = 11) = 9/1340, and U is independent of A and uniform on [−1/1000, 1/1000].
1. **Moments.** The moments are explicit rationals, and 2(μ₃/μ₄) ln 2 exceeds the rational point 6931/50000.
2. **The standing assumption.** With g(x) = (e^x − 1)/(e^x + 2), 𝓕₀'' is a positive multiple of E[W³ g''(tW)]. Since g'' changes sign once, at ln 2, 𝓕₀'' is positive near 0 and negative for large t. Rational exponential enclosures on a grid certify a single sign change on the compact middle range.
3. **Uniqueness.** 𝒦' = ((q−1)/(2q))(𝓕₀ − t𝓕₀') and (𝓕₀ − t𝓕₀')' = −t𝓕₀''. So 𝒦 has exactly one positive zero.
4. **Location.** 𝒦 is negative at a small rational point and positive at 6931/50000. The zero t_c therefore lies below 2(μ₃/μ₄) ln 2.

## Falsifier

The refutation would fail if the module's 𝓕₀, 𝒦 or hypotheses differed from the source's. The module:
- defines 𝓕₀ and 𝒦 by Eq. (1) and Eq. (6) as integrals against the density;
- normalizes by μ₁;
- quantifies over all q > 2 and all densities that are integrable, nonnegative, vanish on (−∞, 0], have mass 1 and an integrable fourth moment, and satisfy the standing assumption and uniqueness.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.lean` (924 lines).
- **Definitions.** It defines `moment`, `F0`, `K`, `claim` and the instance density, and proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.lean.json`, statement `sha256:32414dcb04d0d6336e222dc79231b30eb6b35d46dfe31e48a95527164faf04a8`.

Declaration statements:
- `result`: `sha256:d0f61a558574b6e93f2f82d2f8e8e124244ecc2f5ba9807149f13b2efe54d47e`;
- `claim`: `sha256:49c1fa185dbf3d9c82efc9e3de5d93f51aad916d9c0ac7b3252b00ffb1ed1d89`.

## Triage

A tier 1 suggestion of a 2025 paper, preregistered in issue #18836 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: the sign bounds instantiate Mathlib's exponential bounds and interval-integral identities, followed by rational normalization | open-problem-resolution |
| `moment`, `F0`, `K`, `claim` and the density | bind-only | none | definitions used by `claim` |
| private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only: the certified sign changes instantiate Mathlib's exponential bounds and interval-integral identities, followed by rational normalization. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2.

Utility: `kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the lower inequality fails for the two-block density at q = 3. All of the source's assumptions hold for this density.

**Computed, not formalized** (orchestrator, recorded in #18836):
- t_c ≈ 0.1383954, against 2(μ₃/μ₄) ln 2 ≈ 0.1386294, a 0.17 % deficit;
- the zero of 𝓕₀'' is near 0.0685.

**Argued, not formalized.**
- *Scope.* Whether the lower inequality holds for the Pareto family of the paper or for other restricted classes, such as log-concave densities, is not determined here.
- *Upper inequality.* The upper inequality t_c < 2(μ₀/μ₁) ln(q−1) is not addressed.

**Effect on the paper.** The Pareto-case results of the paper are unaffected. The general-density extension of the lower bound does not hold.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
