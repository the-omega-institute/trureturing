---
bibkey: chuysurichay2026fibdold
authors: Sompong Chuysurichay; Sawian Jaidee; Chatchawan Panraksa; Thomas Ward
year: 2026
title: "The local Dold congruence for Fibonacci and Lucas sequences"
doi: null
url: https://arxiv.org/abs/2609.24544v1
claim: For a prime p other than 2 and 5, the local Fibonacci repair factor is z(p)/gcd(z(p),p-1), where z(p) is the Fibonacci rank of apparition; it equals 1 exactly for p congruent to plus or minus 1 modulo 5.
strata_touched: []
license: citation-only
triage: anchor
---

# Local repair factors for Fibonacci prime support

The source is [arXiv:2609.24544v1](https://arxiv.org/pdf/2609.24544v1), submitted 21 September 2026. The paper's notation uses `varphi(p)` for the Fibonacci rank of apparition; this card writes that rank as `z(p)` to avoid confusion with the golden ratio. The proof and its computational density checks were not independently audited here, and no Lean verification is claimed.

Theorem 2.4 states that the local Fibonacci `p`-part is almost Dold at every prime and, for `p` other than `2` and `5`, its least repair factor is

$$
\operatorname{Fail}_p(F)=\frac{z(p)}{\gcd(z(p),p-1)}.
$$

In particular it is one exactly when $p\equiv\pm1\pmod 5$; for $p\equiv\pm2\pmod 5$ the repair factor is nontrivial. This is a local congruence statement about the Fibonacci sequence, not a divisor-sum estimate and not a Robin criterion.

## Verified locator

https://arxiv.org/abs/2609.24544v1

Theorem 2.4 gives the Fibonacci repair factor. Section 4, PDF page 11,
prints the tribonacci and four-Bonacci good-prime observations.
