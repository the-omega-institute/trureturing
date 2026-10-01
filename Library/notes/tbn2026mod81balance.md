---
bibkey: tbn2026mod81balance
authors: trureturing research continuation
year: 2026
title: An unconditional mod-81 depth balance in the split Lucas tower
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/WSS_TBN_MOD27_BALANCE.md
claim: Unconditional mod-81 weighted congruence for the actual Fibonacci depths in the fixed Lucas blocks B_j=L_(2*3^j)+1.
license: repository-original
triage: anchor
strata_touched: []
---

This note records the M81 strengthening appended to
docs/develop/theory/WSS_TBN_MOD27_BALANCE.md. It uses the existing TBN.2 and
TBN.3 identities for B_j=L_(2*3^j)+1=L_(3^j)^2+3, r_j=3^(j+1), and
v_p(B_j)=h_p, where h_p is the original Fibonacci depth.

Set m_j=2r_j, u_j=(B_j-1)/m_j, and b_(p,j)=(p-1)/m_j. The exact recurrence
u_(j+1)=u_j(-1+4*3^(2j+1)u_j^2), with u_2=107, gives
u_j=26*(-1)^j modulo 81 for j>=2. For j>=3, 81 divides m_j, so expanding
B_j=product p^(h_p) modulo 81*m_j gives
sum_(p|B_j) h_p b_(p,j)=26*(-1)^j modulo 81. The direct bases are
S_1=1 and S_2=26, with B_2=5779 prime.

The theorem is elementary once TBN.2--TBN.3 are admitted and is paper-first;
the repository has no block-factorization/depth-vector Lean API, so no
bind-only formal wrapper is claimed. The rank/depth baseline is classical
Lengyel valuation input as recorded in Medina--Rowland, Fibonacci Quarterly
53 (2015), Theorem 1.4, arXiv:0910.2907. The closest checked residue source is
Bundschuh--Bundschuh, Distribution of Fibonacci and Lucas Numbers Modulo 3^k,
Fibonacci Quarterly 49 (2011), 201--210; it does not state this weighted
actual-depth congruence. No matching M81 theorem was found in the checked
repository or recent WSS PR history.
