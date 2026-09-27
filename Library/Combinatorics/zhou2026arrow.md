---
bibkey: zhou2026arrow
authors: Robin D.P. Zhou, Xinyang Yu
year: 2026
title: "Arrow-Wilf equivalences and enumerative results for short arrow patterns"
doi: 10.48550/arXiv.2609.29392
url: https://arxiv.org/abs/2609.29392v1
claim: "This suggests that these two patterns may be arrow-Wilf-equivalent. … We leave this as an open problem."
strata_touched:
  - D5/S3/Combinatorics/ArrowWilfEquivalence
license: citation-only
triage: anchor
---

# Zhou and Yu, arrow-Wilf equivalences for short arrow patterns

The paper continues the study of arrow pattern avoidance, which constrains the one-line notation of a
permutation `π` and the cycle structure of `π̂ = θ⁻¹(π)` at once. It enumerates the avoidance classes of
the arrow patterns `(ν; b → c)` of size three with `ν ∈ {31, 23, 32}`, completes the two cases
`(12; 3 → 3)` and `(21; 3 → 3)`, and records an unexplained numerical coincidence as an open problem.

## Verified locator

DOI: 10.48550/arXiv.2609.29392

URL: https://arxiv.org/abs/2609.29392v1

The arXiv record shows only v1 (24 September 2026), distributed under the arXiv non-exclusive licence.

- Locator: Section 1, the definition of containment of an arrow pattern `α = (ν; H)` of size `k`:
  a set `X = {x_1 < ⋯ < x_k}` and indices `t_1 < ⋯ < t_m` with `π_{t_1} ⋯ π_{t_m} = x_{ν_1} ⋯ x_{ν_m}`,
  and `π̂(x_b) = x_c` for every arrow `b → c` in `H`; `π̂ = θ⁻¹(π)` is read off by cutting `π` before each
  left-to-right maximum. Two patterns are arrow-Wilf-equivalent when `|S_n(α)| = |S_n(β)|` for all `n ≥ 1`.
- Locator: Theorem 3.1, `|S_n(12; 3 → 3)| = d_n + Σ_{m=1}^{n} Σ_{k=0}^{n−m} C(n−m,k) C(m+k−1,n−m) d_k`.
- Locator: Theorem 5.5, `|S_n(23; 1 → 1)| = d_n + d_{n−1} + Σ_{m=1}^{n−1} Σ_{r=0}^{m−1} C(m−1,r) C(n−m+r−1,r) r! d_{m−1−r}`.
- Locator: Section 7, "We have computed the avoidance counts for the arrow patterns (12; 3 → 3) and
  (23; 1 → 1) and found that the resulting sequences agree for all values of n tested. This suggests
  that these two patterns may be arrow-Wilf-equivalent. However, the explicit formulas we obtained for
  the two sequences are quite different in form, and we have not been able to establish the
  equivalence by a direct bijection or by any other method. We leave this as an open problem."

## Reading of the statement

A permutation avoids `(12; 3 → 3)` exactly when, for every fixed point `f` of `π̂`, the entries below `f`
appear in decreasing order; it avoids `(23; 1 → 1)` exactly when, for every fixed point `f`, the entries
above `f` appear in decreasing order. The open problem asks for `|S_n(12; 3 → 3)| = |S_n(23; 1 → 1)|` for
every `n ≥ 1`.

## Scope of the recorded answer

The equivalence holds. After removing the derangements, both counts equal the finite signed sum
`E_n = Σ_{p=0}^{n−1} Σ_{i=0}^{p} (−1)^i (p!/i!) C(n−i−1, p−i)`: the first by a trinomial reindexing and
the negative-binomial expansion of `(1 − z − z²)^{−(k+1)}`, the second by a hockey-stick summation, with
the boundary term `d_{n−1}` equal to the term `p = n − 1` of `E_n`.

## Bounded prior-resolution evidence

Read on 2026-09-25: the arXiv record (v1 only), google-deepmind formal-conjectures and conjectures.io;
searches by title, arXiv number and the two pattern names returned no later proof. The paper was one day
old at the time of reading, so the absence of citing work is weak evidence; this is a bounded negative
finding.
