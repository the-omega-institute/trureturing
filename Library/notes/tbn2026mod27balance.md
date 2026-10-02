---
bibkey: tbn2026mod27balance
authors: trureturing research continuation
year: 2026
title: A mod-27 depth balance in the split Lucas tower
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/WSS_TBN_MOD27_BALANCE.md
claim: Unconditional mod-27 weighted congruence for the actual Fibonacci depths in the fixed Lucas blocks B_j=L_(2*3^j)+1.
license: repository-original
triage: anchor
strata_touched: []
---

This note records the paper-first theorem in
docs/develop/theory/WSS_TBN_MOD27_BALANCE.md. It uses the existing TBN.2
and TBN.3 identities for
B_j=L_(2*3^j)+1=L_(3^j)^2+3, r_j=3^(j+1), and
v_p(B_j)=h_p, where h_p is the original Fibonacci depth.

Set u_j=(B_j-1)/(2r_j) and b_(p,j)=(p-1)/(2r_j). The block recurrence
B_(j+1)=B_j^3-3B_j^2+3 gives
u_(j+1)=u_j(-1+4*3^(2j+1)u_j^2), with u_1=1. Hence
u_j=(-1)^(j+1) modulo 27. For j>=2, (2r_j)^2 is divisible by 54r_j;
expanding the exact factorization B_j=product p^(h_p) modulo 54r_j gives
sum_(p|B_j) h_p b_(p,j)=(-1)^(j+1) modulo 27. The j=1 case is the direct
block B_1=19.

The theorem sharpens the prior mod-3 balance by retaining a mod-27
weighted residue of the actual depth vector. It gives no h_p=1 witness and
does not decide WSS existence. The only arithmetic input beyond TBN.2--3
is the binomial expansion; no abc, Pell-height, Chebotarev, or
equidistribution assumption is used.

The rank/depth baseline is classical: Lengyel's valuation theorem as
recorded in L. A. Medina and Eric Rowland, "p-regularity of the p-adic
valuation of the Fibonacci sequence", Fibonacci Quarterly 53 (2015),
Theorem 1.4, arXiv:0910.2907. The displayed mod-27 balance itself is
not attributed to that source.

Exact checks for j=1,...,4, including factorizations and residues, are
included in the theory document.
