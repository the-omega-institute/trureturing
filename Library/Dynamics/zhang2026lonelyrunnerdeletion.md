---
bibkey: zhang2026lonelyrunnerdeletion
authors: Yuhan Zhang
year: 2026
title: "Tight instances of the Lonely Runner Conjecture: complete classification of one-entry modifications, a new infinite family, and the growth bound"
doi: 10.48550/arXiv.2608.13599
url: https://arxiv.org/abs/2608.13599v2
claim: "For every N >= 2 and 1 <= r <= N, LR([N] minus {r}) >= 1/N, with equality iff r=N or N=2."
strata_touched:
  - D5/S1/Phase/LonelyRunnerDeletion/OneDeletion
license: citation-only
triage: anchor
---

# One-deletion Lonely Runner bounds and equality cases

Zhang's Question 2.11 asks whether deleting one speed from `[N]` leaves
Lonely Runner value at least `1/N`, and whether equality requires deleting
`N`. The latter wording has an exception at `N=2`: either deletion leaves
a singleton with value `1/2`.

The Lean theorem proves the universal lower bound and the exact corrected
equality classification. This is a formalization of a consequence of
existing literature; it is not counted as a new unique open-problem solution.

## Verified locators and literature consequence

- Zhang: https://arxiv.org/abs/2608.13599v2, Theorem 1.2 and Question 2.11;
  Remark 2.8 and Proposition 2.10 supply the surrounding one-entry cases.
- Terence Tao, *Some remarks on the lonely runner conjecture*,
  https://arxiv.org/abs/1701.02048, Proposition 1.5 (printed page 7;
  proof in Section 5, pages 27–28). With `m=N-1` distinct positive speeds,
  all at most `N`, its hypothesis `max v_i <= 1.2*m` holds for `N >= 6`
  and gives `LR >= 1/(m+1)=1/N`. The remaining sizes are covered by
  the explicit witnesses in the direct proof below.

For `r < N`, write `[N] \ {r}` as `([N-1] \ {r}) ∪ {N}`. Zhang's
Theorem 1.2 applies with its parameter `n=N` and replacement `w=N` whenever
`N >= 4`. Its sporadic cases have replacements `7` and `9` with parameters
`5` and `6`, so neither matches `w=n`. In case (i), the conditions
`2*r > N-1`, `r | N`, and `r < N` force `N=2*r`. Hence `m=2` and
`s=N-r=r`; the required gcd condition includes `r+1`, contradicting
`gcd(r,r+1)=1`. Together with the lower bound this excludes equality for
`r<N, N>=4`. The small cases and the endpoint `r=N` are elementary.

## Direct formal proof

`D5/S1/Phase/LonelyRunnerDeletion/OneDeletion.result` proves, for every
`N >= 2` and `1 <= r <= N`,

\[
\frac1N\le \operatorname{LR}([N]\setminus\{r\}),\qquad
\operatorname{LR}([N]\setminus\{r\})=\frac1N
\Longleftrightarrow r=N\lor N=2.
\]

The implementation supplies its own rational witnesses and does not assume
Tao's or Zhang's classification theorem. For `r>N/2`, time `1/r` gives a
strict surplus over `1/N`. For `2*r<=N`, it constructs a denominator `q`
with `N+r<q<2*N` and an inverse of `r` modulo `q`, placing every retained
residue at least two away from either endpoint. The deleted-endpoint upper
bound follows from Mathlib's Dirichlet approximation theorem; the two
`N=2` singleton cases are handled directly.

The formal definition uses the supremum over all real times of
`|v*t - round(v*t)|`. Independent Lean review proved the general attainment
and finite-minimum bridge for every nonempty finite speed set and checked
that the formal statement faithfully represents the source's maximum.

## Scope

The theorem concerns the exact one-deletion family. Its known literature
consequences preclude a new unique-solution claim. The earlier identifier
and repository screen found no competing local implementation, but that
screen did not examine the broader consequences of published theorems.
