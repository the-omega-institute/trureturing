---
bibkey: nowicki2013strongdivisibility
authors: Andrzej Nowicki
year: 2013
title: Strong divisibility and lcm-sequences
doi: null
url: https://arxiv.org/abs/1310.2416v1
claim: Theorem 2.1 characterizes nonzero positive-index strong divisibility sequences in a gcd-domain by divisor products of their successive prefix-lcm quotients, up to units; logarithms and Moebius inversion give the retained Mertens dilation as a classical consequence.
strata_touched:
  - D5/S3/Arith/StrongDivisibilityLcmMertens
license: citation-only
triage: anchor
---

# Classical prefix-lcm reconstruction

## Verified locator

The primary source is Andrzej Nowicki, *Strong divisibility and
lcm-sequences*, arXiv:1310.2416v1, submitted 9 October 2013.
The version record is https://arxiv.org/abs/1310.2416v1.
The title, author, abstract, introduction and Theorem 2.1 were directly
read from https://arxiv.org/pdf/1310.2416v1, PDF pp. 1 and 4.
The saved primary PDF has SHA-256
`020ceb705522920c25be19a8fb01c771a5be9039d16eb18d9d4a20b73ba5a248`.

The `v1` locator fixes the arXiv version. The directly verified result is
Theorem 2.1, PDF p. 4; PDF p. 1 independently confirms the title, author,
version date and the reconstruction statement in the abstract. The note
uses the declared `Factorization` domain in `Meta/domains.yaml`.

## Verified mathematical statement and Lean consequence

Theorem 2.1, PDF p. 4, states that a sequence `(a_n)_{n>=1}` of nonzero
elements in a gcd-domain is a strong divisibility sequence if and only if

$$
a_n=\prod_{d\mid n}c_d\quad(n\ge1),
$$

where `c_1=a_1` and, for `n>=2`,

$$
c_n=\frac{\operatorname{lcm}(a_1,\ldots,a_n)}
{\operatorname{lcm}(a_1,\ldots,a_{n-1})}.
$$

The paper explicitly treats gcd/lcm equalities up to units. For positive
natural values there is no unit ambiguity. The Lean module only needs
the forward reconstruction implication. It uses the empty prefix lcm
`L(0)=1`, so the uniform quotient `A(n)=L(n)/L(n-1)` also gives
`A(1)=u(1)`. It does not assume `u(1)=1` or impose a value at `u(0)`.

The retained theorem is

$$
\log L(N)=\sum_{1\le d\le N}\log u(d)
    \sum_{1\le m\le\lfloor N/d\rfloor}\mu(m)
\qquad(N\ge0).
$$

This logarithmic Mertens dilation is a classical consequence of
Nowicki's reconstruction and ordinary additive Moebius inversion.
Nowicki does not literally print this log/Mertens formula. The module
honestly uses `literature-attested` provenance for this known consequence
and makes no research novelty claim. No theory chapter is added.

The missing certified supplier in the project pin is the reconstruction
for positive natural strong divisibility sequences. The live Lean proof
constructs the prefix quotients and proves the more informative projection

$$
\gcd(u(n),L(K))=\prod_{\substack{1\le d\le K\\d\mid n}}A(d),
\qquad n\ge1,\quad K\ge0.
$$

In the next-index branch `d|n`, cancellation in the positive natural
gcd-times-lcm identities shows that the gcd gains exactly `A(d)`.
In the other branch, `0<gcd(n,d)<d`, and strong divisibility places the
overlap value in the previous prefix, so the gcd does not grow.
At `K=n` this yields divisor reconstruction. The prefix product
telescope, positive finite logarithms, additive Moebius inversion and
finite summatory convolution then give the retained formula, including
`N=0`. The internal real arithmetic function is zero-normalized at
index zero, preserving arbitrary `u(0)`.

The projection is independently implemented in Lean. No paper proof
or external Lean source is copied. The existing natural gcd/lcm
distributor is reused from its original repository source,
`D5.S3.Factorization.PrimePowers.FiniteCompatibleCrt.gcd_lcm_distrib`.
The pinned Mathlib supplies `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`
and `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum` for the remaining
inversion and grouping. A search of the pinned Mathlib and Lean core
found no public distributor matching the needed natural equality.

Downstream applications to `u(n)=n`, Fibonacci numbers, primitive
rational factors and the centered Fibonacci defect are bindings of this
supplier and other existing results. They earn no separate public
theorem in this delivery. The exact Robin signed integral tail and
the Riemann hypothesis remain open in the broader research task.
