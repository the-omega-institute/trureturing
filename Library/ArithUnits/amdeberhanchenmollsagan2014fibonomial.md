---
bibkey: amdeberhanchenmollsagan2014fibonomial
authors: Tewodros Amdeberhan, Xi Chen, Victor H. Moll, Bruce E. Sagan
year: 2014
title: Generalized Fibonacci polynomials and Fibonomial coefficients
doi: 10.1007/s00026-014-0242-9
url: https://arxiv.org/abs/1306.6511v2
claim: 'Conjecture 4.6, first clause: If s > t ≥ 1 with (s, −t) ≠ (2, −1) and n, r ∈ P then ⌊(∑_{k=n}^∞ 1/{rk}_{s,−t})^{−1}⌋ = {rn}_{s,−t} − {r(n − 1)}_{s,−t} − 1.'
strata_touched:
  - D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s00026-014-0242-9

Source: https://arxiv.org/abs/1306.6511v2

Annals of Combinatorics 18 (2014), 541–562. The arXiv version places
the sequence definition in Section 1, p. 2, and Conjecture 4.6 in Section 4,
p. 13.

## Source statements

“Throughout this work, P will stand for the positive integers.”

“{0}_{s,t} = 0, {1}_{s,t} = 1 and, for n ≥ 2,
{n}_{s,t} = s{n − 1}_{s,t} + t{n − 2}_{s,t}.”

“If s > t ≥ 1 with (s, −t) ≠ (2, −1) and n, r ∈ P then
⌊(∑_{k=n}^∞ 1/{rk}_{s,−t})^{−1}⌋ = {rn}_{s,−t} − {r(n − 1)}_{s,−t} − 1.”

The source explains the excluded pair: “The restriction (s, t) ≠ (2, −1)
in the following conjecture is to ensure that the series converges.”
The squared-reciprocal clause of the conjecture is a separate statement.

## Mathematical scope

The integer recurrence `U` uses the source's three recursive cases. Its tail
is reindexed by natural `k` as `r * (n + k)` and explicitly asserted summable
over the reals. The module proves the first floor identity for all the stated
integer parameters and positive natural indices. Its proof controls the growing
Cassini defect by the difference of terms two indices apart, then compares the
tail with telescoping series. No square-root formula is required.

Literature completeness, including the scope of prior partial results, is
ASSUMED-UNVERIFIED. The preregistration is
https://github.com/the-omega-institute/trureturing/issues/18768.
