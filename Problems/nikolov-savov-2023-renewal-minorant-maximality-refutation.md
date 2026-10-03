---
slug: nikolov-savov-2023-renewal-minorant-maximality-refutation
bibkey: nikolovsavov2024renewal
doi: 10.53656/math2024-2-1-pro
url: https://arxiv.org/abs/2307.00545v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.result
---

# Refutation of Nikolov–Savov Conjecture 3.7 at k = 4

## Problem

N. Nikolov and M. Savov, *Properties and conjectures regarding discrete renewal sequences*, arXiv:2307.00545v2, §3, Conjecture 3.7, states:

> For any k ≥ 3, Q_k is a maximal element in 𝒜_k and it is largest in 𝒜̂_k.

The formal claim settles the first clause:

```text
claim := ∀ k ≥ 3, Q_k ∈ 𝒜_k ∧ ∀ P ∈ 𝒜_k, Q_k ≺ P → P = Q_k.
```

Here `A_k` is the simplex of nonnegative first `k−1` masses with sum at most one, `u` is the renewal sequence of Eq. (2.2), `Q_k` is the product of partial sums in Eq. (2.5), and `𝒜_k` is the degree-bounded class of polynomial lower bounds in Eq. (2.7). The hatted class is not used.

## Motivation

Issue #12306 preregisters the named conjecture, its quantified claim, and the k = 4 witness. The motivation declaration is the frozen Lean result `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.result`.

## Gap

The source proves the k = 3 case in Proposition 3.8 and leaves the universal maximality assertion open. The bounded literature and repository checks recorded for issue #12306 found no prior proof or refutation of Conjecture 3.7 in the searched scope.

## Route

At k = 4 write x = p₁, y = p₂, z = p₃ and w = 1 − x − y − z. Let

```text
P = x²(x + y + z) + xy.
```

Then `P − Q₄ = xyw`, so `Q₄ ≺ P` on `A₄`, while `P` has total degree three and differs from `Q₄`. The renewal masses are `u₁ = x`, `u₂ = x² + y`, and `u₃ = x³ + 2xy + z`. The certificates

```text
u₁ − P = x(z + (1+x)w)
u₂ − P = x²w + y(1−x)
u₃ − P = xy(1−x) + z(1−x²)
```

are nonnegative on `A₄`; `P ≤ u₁ ≤ u₀ = 1`. For n ≥ 4 the renewal recurrence is a convex combination of the preceding four masses, so strong induction gives `P ≤ u_n` for every n ≥ 1. This proves `P ∈ 𝒜₄` and contradicts maximality of `Q₄`.

## Falsifier

A failure of any certificate, of the all-n induction, of the degree bound, of `Q₄ ≺ P`, or of `P ≠ Q₄` would invalidate the refutation. The result does not assert that `𝒜₄` has no maximal element and does not address the largest-in-`𝒜̂_k` clause.

## Evidence

The Lean module is `D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.lean`. Its public settlement is `result : ¬ claim`; the definitions expose the source simplex, step masses, renewal recurrence, polynomial order, minorant class, product `Q`, and claim. The all-n minorant argument is the escape witness. Lean checks the theorem with axiom closure `[propext, Classical.choice, Quot.sound]`. The Scribe result carries an `OpenProblemResolutionClaim` marked `Refuted` for this problem.

## Triage

`theorem`; resolution `Refuted` at k = 4; preregistration #12306. `proof_shape: content` for `result`; `admission_basis: open-problem-resolution`. Information-escape registration is paused under CLAUDE.md section 3.9.

### What the settlement shows

- **Proved in this module:** `Q₄` is not a maximal element of `𝒜₄`; the strict improvement is the polynomial `xyw`, and the all-n renewal minorant bound is supplied by the three certificates and strong induction.
- **Computed:** the improvement `xyw` vanishes on each face `x = 0`, `y = 0`, and `w = 0`, and is positive at the interior point `x = y = z = w = 1/4`; there `P = 7/64` and `Q₄ = 6/64`.
- **Proved:** the k = 3 case in Proposition 3.8 survives this mechanism: at k = 3 the degree bound is two, while the analogous three-coordinate interior factor would require the degree-three term `xy(1−x−y)`. This module does not reprove Proposition 3.8.
- **Open:** whether `𝒜₄` has any maximal element remains unsettled. Refuting maximality of `Q₄` does not settle existence of another maximal minorant.
- **Open:** the separate assertion that `Q_k` is largest in `𝒜̂_k` is not used and remains unsettled.
- **Proved boundary:** source results that rely specifically on the universal maximality of `Q_k` cannot use that clause at k = 4 without an additional hypothesis or replacement minorant. The k = 3 proposition and results independent of Conjecture 3.7 are unaffected by this refutation.

## ASSUMED-UNVERIFIED

The literature search is bounded by the sources and queries recorded in issue #12306; it does not establish exhaustive absence of a later settlement. The identification of the Lean definitions with the source notation is documented in the Library note and the Scribe commentary; the hatted class is intentionally outside this result.
