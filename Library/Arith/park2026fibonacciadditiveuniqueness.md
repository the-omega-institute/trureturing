---
bibkey: park2026fibonacciadditiveuniqueness
authors: Poo-Sung Park
year: 2026
title: "The Fibonacci numbers are not an additive uniqueness set for multiplicative functions"
doi: null
url: https://arxiv.org/abs/2609.08137v1
claim: A positive integer-valued multiplicative function can agree with the identity on all Fibonacci numbers and all sums of two Fibonacci numbers without being the identity; the smallest exhibited prime switch is 557 <-> 2417 from F_31.
strata_touched: []
license: citation-only
triage: anchor
---

# A negative uniqueness result for Fibonacci additive tests

The source is [arXiv:2609.08137v1](https://arxiv.org/pdf/2609.08137v1), submitted 8 September 2026. This card records the stated construction and criterion from that version. It is a preprint; the proof and certificate checker were not independently audited here, and no Lean verification is claimed.

The paper answers a question of Spiro by constructing a positive integer-valued multiplicative function $f\ne\operatorname{id}$ such that

$$
f(F_n+F_m)=f(F_n)+f(F_m)\qquad(n,m\ge1).
$$

The displayed example uses

$$
F_{31}=557\cdot2417,
$$

and exchanges the two prime contributions:

$$
f(N)=N\left(\frac{2417}{557}\right)^{\mathbf 1_{557\mid N}-\mathbf 1_{2417\mid N}}.
$$

The source proves that $557$ and $2417$ divide exactly the same Fibonacci numbers and the same sums of two Fibonacci numbers. It also gives a finite rank and fourth-power-residue criterion producing further prime pairs.

This is a negative identifiability result for sparse Fibonacci tests. It does not say that the specific function $Z(n)=\sigma(n)/n$ cannot be controlled on a FIB family, and it does not construct a Robin counterexample. It does show that an argument using only values on Fibonacci numbers or pairwise Fibonacci sums cannot recover an arbitrary multiplicative function without an additional source relation. A Robin bridge must therefore retain the actual prime-power valuation data or prove a property specific to $\sigma(n)/n$.
