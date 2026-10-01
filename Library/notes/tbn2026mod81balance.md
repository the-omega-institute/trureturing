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



The exact coefficient hierarchy behind the first-order balance is as follows.
Let
Phi_j(X)=product_(p|B_j)(1+b_(p,j)X)^(h_p)=sum_q E_(q,j) X^q.
Then E_(0,j)=1, E_(1,j)=S_j, and
E_(2,j)=T_j=sum_p binom(h_p,2)b_(p,j)^2+
sum_(p<q)h_p h_qb_(p,j)b_(q,j). Evaluating at m_j gives
u_j=sum_(q>=1) m_j^(q-1) E_(q,j). Hence the truncation
U_(j,Q)=sum_(q<=Q)m_j^(q-1)E_(q,j) satisfies
u_j=U_(j,Q) modulo m_j^Q. In particular
S_hat_j=S_j+m_j T_j equals u_j modulo m_j^2.

This correction does not improve the sharp 3-adic limit C from the merged
3-adic theorem: v_3(C-(-1)^(j+1)S_hat_j)=2j+1, because the correction error
has valuation at least 2j+2 while v_3(C-(-1)^(j+1)u_j)=2j+1. TBN.3 is
block-local and imposes no relation between consecutive multisets of
(b_(p,j),h_p), so it gives no stable E_(2,j) modulo 3 or E2 recurrence.
At coefficient level, multisets (a,1) and (1,1),(a-1,1) have the same E1
but E2 values 0 and a-1.

Exact checks for j=3,4,5 give
j=3: b mod 27=(19,9), T mod 27=9, v3(u-S)=6;
j=4: b mod 27=(15,11), T mod 27=3, v3(u-S)=6;
j=5: b mod 27=(1,13,3,11), T mod 27=26, v3(u-S)=6, and
v3(u-S_hat)=12. The j=5 squarefree factorization has four prime factors
1459, 58321, 67234945243909760461, and
64642456533364216165903625998192510598323380531684784427098565775883411861,
all with h_p=1. Thus T_5 is 2 modulo 3 and S_5 is not congruent to u_5
modulo 3^7, proving the current 3^(j+1) weighted modulus cannot be lifted
uniformly by one digit. This is a paper-first obstruction, not a claim that
the actual E2 sequence has no deeper law.

