---
bibkey: assani2025robinkaneko
authors: Idris Assani; Aiden Chester; Alex Paschal
year: 2025
title: On Robin's Inequality and the Kaneko-Lagarias Inequality
doi: null
url: https://arxiv.org/abs/2503.03159v2
claim: The paper gives elementary proofs of Robin safety for several large arithmetic classes and reduces the Kaneko-Lagarias test to superabundant numbers; its divisibility classes are not FIB additive inclusion classes.
strata_touched: []
license: citation-only
triage: anchor
---

# On Robin's Inequality and the Kaneko--Lagarias Inequality

The source is [arXiv:2503.03159v2](https://arxiv.org/pdf/2503.03159v2), updated 16 August 2025. The results below are attributed to that version; no independent proof audit or Lean verification is claimed.

The paper proves Robin's inequality for every $n>5040$ not divisible by any of $2,3,5$, for primorials above $30$, for sufficiently large $2^k m$ with $m$ odd, and for $21$-free integers. It also proves that the Kaneko--Lagarias inequality

$$
\sigma(n)<e^{H_n}\log H_n
$$

is equivalent to RH when checked on all integers, and that it is enough to check it on superabundant numbers. The paper explicitly leaves the analogous superabundant reduction for the full Lagarias inequality as future work.

## FIB interface and non-identification

The hypotheses here are divisibility and $p$-free conditions. A five-window state records additive inclusion of Fibonacci positions; labels such as $[2]$ or $[2\,5]$ do not assert $2\mid n$, $5\mid n$, or a prescribed $p$-adic valuation. Therefore the class results can be used only after an independent divisibility proof for a concrete FIB-generated integer. They do not supply the missing prime-support or same-price bridge for the general FIB family.
