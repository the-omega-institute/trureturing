---
bibkey: krasikov2011turan
authors: Ilia Krasikov
year: 2011
title: Turán inequalities for three-term recurrences with monotonic coefficients
doi: 10.1016/j.jat.2011.04.007
url: https://arxiv.org/html/1101.3204v1
claim: "Theorem 8 gives nonnegativity of the correctly weighted S_2 determinant for monotone recurrence coefficients on t >= b_n - 2a_n."
strata_touched:
  - D5/S1/Recurrence/Turan/StrictlyIncreasingTail
  - D5/S1/Recurrence/Sun/GStrict
  - D5/S1/Recurrence/Sun/VTail
license: citation-only
triage: anchor
---

# Krasikov's weighted right-tail inequality

Ilia Krasikov, *Turán inequalities for three-term recurrences with
monotonic coefficients*, *Journal of Approximation Theory* 163(9)
(2011), 1227-1248. DOI: 10.1016/j.jat.2011.04.007.
Versioned source URL: https://arxiv.org/html/1101.3204v1.

## Verified locator

DOI: 10.1016/j.jat.2011.04.007.
Versioned source URL: https://arxiv.org/html/1101.3204v1.
The checked scope is the displayed three-term recurrence, the weighted
`S_2` definition, and Theorem 8's right-tail conclusion with its
monotonicity hypotheses.

## Exact normalization

The source recurrence, at positive `k`, is

$$
\frac{a_k}{c_k}p_k(t)=(t-b_{k-1})p_{k-1}(t)
 -a_{k-1}c_{k-1}p_{k-2}(t),
$$

with `p_{-1}=0`, `p_0=1`, `a_0=0`, positive `a_k,c_k` for positive
`k`, and positive `c_0`. Its determinant is

$$
S_2(p_n)=p_n(t)^2-
 \frac{c_n}{c_{n+1}}\frac{a_{n+1}}{a_n}p_{n-1}(t)p_{n+1}(t).
$$

Theorem 8 assumes nondecreasing `a_k` and `b_k` and gives
`S_2(p_n) >= 0` for `t >= b_n-2a_n`. It is a non-strict weighted
tail result, not either full strict Sun clause. The local proof specializes
to `c_k=1`, requires strict increase of `a`, and proves its own base,
central, and farther-tail cases. For Sun's `g` transform, `a_n=n^2`,
`b_n=2n(n+1)` and the threshold is `t>=2n`. For the `v` transform,
`a_n=n^3/sqrt(4n^2-1)`, `b_n=n(n+1)` and the threshold is
`t>=n(n+1)-2n^3/sqrt(4n^2-1)`. The positive normalization factor
`d_n=1/sqrt(2n+1)` connects the latter source sequence to the
unit-normalized recurrence; the Lean `VTail` proof establishes that
connection by its initials and recurrence.

Theorem 5 of the same paper cannot be applied unchanged to the `g`
parameters: its needed discriminant condition would compare
`16i^2-4` against `16i^2` in the wrong direction. Theorem 8 covers
only the tail; endpoint parity, local positive quadratics, and the
weighted-to-strict conversion are additional proof content.
