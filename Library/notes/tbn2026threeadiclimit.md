---
bibkey: tbn2026threeadiclimit
authors: trureturing research continuation
year: 2026
title: The sharp 3-adic limit and growing depth modulus in the split Lucas tower
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/WSS_TBN_MOD27_BALANCE.md
claim: Exact 3-adic convergence order for normalized split Lucas recurrence and weighted-depth congruence modulo 3^(j+1).
license: repository-original
triage: anchor
strata_touched: []
---

Let u_j=(B_j-1)/(2*3^(j+1)) for B_j=L_(2*3^j)+1 and set
c_j=(-1)^(j+1)u_j. The exact recurrence is
c_(j+1)=c_j(1-4*3^(2j+1)c_j^2), with 3 not dividing c_j. Hence
v_3(c_(j+1)-c_j)=2j+1 exactly, and c_j converges to a unique C in Z_3 with
v_3(C-c_j)=2j+1. Therefore u_j=(-1)^(j+1)C modulo 3^K exactly when
K<=2j+1; the maximal stabilization modulus is 3^(2j+1).

TBN.3 gives p=1+m_j b_(p,j), m_j=2*3^(j+1), and
B_j=product p^(h_p) with actual depths h_p. First-order expansion modulo m_j^2
yields the growing weighted congruence
sum h_p b_(p,j) = u_j modulo 3^(j+1) for every j>=1. A stronger S-only
modulus needs new control of the second-order coefficient.

OEIS A268924 and A271223 record Lucas(3^j) as successive 3-adic
approximants to a root of x^2+2, with Nagell/Lang provenance. The checked
sources do not state this normalized limit together with actual WSS depth
weights. This result is paper-first; there is no block-depth Lean API.
