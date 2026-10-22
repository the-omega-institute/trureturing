---
bibkey: miskaulas2022sigma
authors: Piotr Miska; Maciej Ulas
year: 2022
title: "On the Diophantine equation σ₂(X̄ₙ) = σₙ(X̄ₙ)"
doi: 10.1142/S1793042124500635
url: https://arxiv.org/abs/2203.03942v1
claim: "Conjecture 4.8 proposes simultaneous bounds on the common value of σ₃ and σₙ and on the last coordinate of a nondecreasing positive integer solution."
strata_touched:
  - D5/S0/Certificates/Polynomials/MiskaUlasSigmaThreeBound
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1142/S1793042124500635

Source: https://arxiv.org/abs/2203.03942v1

## Source definitions

Page 1: “Let n ∈ N≥3 and for given k ≤ n consider the k-th symmetric polynomial σ_k(x_1, . . . , x_n) = Σ_{i_1<i_2<...<i_k} x_{i_1} · · · x_{i_k}.”

Page 2: “By a solution of (1) we mean a sequence X_n = (x_1, . . . , x_n) satisfying the condition x_i ≤ x_{i+1} for i = 1, . . . , n − 1”, in positive integers.

## Conjecture 4.8

Page 16: “Let n ∈ N≥4 and suppose that m ∈ N satisfies m = σ_3(X_n) = σ_n(X_n). Then m ≤ (1/12)(3021n⁶ − 77575n⁵ + 920361n⁴ − 6235705n³ + 24764202n² − 53664304n + 48986640) and x_n ≤ (1/12)(27n⁴ − 190n³ + 471n² − 500n + 216).”

The source's preceding sentence is: “For example, based on numerical calculations we formulate the following.”
The solution conditions extend the positive and nondecreasing tuple terminology to the equation with σ₃.
The source's N contains zero. Lean uses ℕ for both n and m, with positivity required separately for tuple entries.
The two polynomial bounds are evaluated in ℚ. Mathlib's elementary symmetric polynomial evaluated at the tuple is the sum in the definition above.

## Scope

The quoted statement is arXiv:2203.03942v1. The publication is
*International Journal of Number Theory* 20(5) (2024), 1287–1306.
The journal PDF was inaccessible in the literature screen, so its wording and any revision of the conjecture are unverified.
The accessible version record, correction/title queries and indexed later works supplied no refutation; completeness of that literature screen is ASSUMED-UNVERIFIED.
The refutation of the first bound leaves the second bound as a universal statement open.
