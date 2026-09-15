---
bibkey: grellpeng2015pellheight
authors: George Grell; Wayne Peng
year: 2015
title: Wall's Conjecture and the ABC Conjecture
doi: null
url: https://arxiv.org/abs/1511.01210
claim: Number-field abc implies infinitely many non-Fibonacci-Wieferich primes; the Pell-block argument gives an explicit conditional budget for the original initial depths.
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed-golden Pell heights and original WSS depth mass

## Verified locator

1. George Grell and Wayne Peng, *Wall's Conjecture and the ABC Conjecture*,
   arXiv:1511.01210v1, https://arxiv.org/abs/1511.01210 .
   Section 4, Theorem 3 and its proof use abc over Q(sqrt(5)),
   the simple-prime-divisor part of F_n and a radical bound to prove
   conditional infinitude of non-WSS primes. This is the classical
   height/radical mechanism. The paper's product-style claim about Pisano
   periods is not used here.

2. Wayne Peng, Journal of Number Theory 212 (2020), 354-375,
   DOI 10.1016/j.jnt.2019.11.010,
   https://www.sciencedirect.com/science/article/pii/S0022314X1930410X .
   The publisher abstract states a generalization of conditional
   non-Wieferich infinitude to a finite algebraic base set. The complete
   proof is outside this note's source scope. The related preprint is
   arXiv:1511.05645.

3. Luis A. Medina and Eric Rowland, *p-regularity of the p-adic valuation of
   the Fibonacci sequence*, Fibonacci Quarterly 53 (2015), 265-271,
   https://arxiv.org/abs/0910.2907 . Theorems 1.2 and 1.4 of v4 describe
   valuations with the initial valuation arbitrary. The historic computation
   bound is not an up-to-date WSS search bound.

4. OEIS A113650, https://oeis.org/A113650/internal . The July 2026 entry
   states that no WSS prime is known; this is the source's status statement.

## Correspondence to the theory

PH.1-PH.7 of `Problems/wall-sun-sun-golden-unit-lift.md` give the
fixed-golden Pell-block argument.

At a prime INDEX ell>=7, use the actual original values
A=F_ell, B=L_ell, M=F_(2ell)=AB, C=5A^2=B^2+4. Every factor has exact rank
ell or 2ell, and its exponent in M is the original initial WSS depth h_p.
These are not generalized recurrences or a variable quadratic field.

Let U contain only exponent-one primes, W the full factors p^h_p with
h_p>=2, E the excess factors p^(h_p-2) for h_p>=3, and R=10 rad(M).
The identities M=UW and WE=100 M^2/R^2 are unconditional.
The depth-d budget W_(>=d)^(d-1) <= (M/rad(M))^d is also unconditional.

The uniform height inequality C<=H R^kappa is an EXPLICIT EXTRA HYPOTHESIS,
required only for these prime-index Pell triples. Rational abc would imply
it for every kappa>1. It has not been proved here. Under it, W is bounded by
100(H/sqrt(5))^(2/kappa) M^(2-2/kappa)/E. Kappa<2 forces a non-WSS factor
in every sufficiently large paired block; kappa<4/3 forces one in EACH of
the exact-rank ell and 2ell channels. The quantified exponents, particularly
4/kappa-3 in the separate-channel lower bounds, are derived in full.

The limiting logarithmic WSS-factor mass under all these height hypotheses
is zero. This is not the natural density of WSS primes. The argument is
consistent with an empty WSS set and cannot establish WSS existence.
Its classical height/radical mechanism is credited above; no first-discovery
claim is made for this prime-rank packaging or its corollaries.

## Boundaries

The norm identity doubles the return-trace depth; that observation alone
cannot force or exclude initial depth two. At index 91, thirteen has a
square factor while its initial depth remains one. Pointwise height checks
do not prove a uniform H.

The remaining arithmetic obligation is an unconditional height/radical or
other depth constraint on the original fixed-golden blocks that yields a
new restriction without assuming the displayed height hypothesis. A proof
of WSS existence would additionally have to force a positive exceptional
contribution; none of the upper bounds does so.
