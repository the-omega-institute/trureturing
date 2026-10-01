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

The recurrence has a full 3-adic limit. Set
v_j=(-1)^(j+1)u_j. Then v_(j+1)=v_j-4*3^(2j+1)*v_j^3, v_1=1, and there is a unique A in Z_3 with
v_3(A-v_j)=2j+1. Therefore
u_j=(-1)^(j+1)A modulo 3^(2j+1), sharply (the congruence fails
modulo 3^(2j+2)). For K>=1, A modulo 3^K is represented by v_(J_K),
where J_K=max(1,ceil((K-1)/2)); the first residues are
1,1,1,55,136,379,1108,3295 for K=1,...,8.

Writing S_j=sum h_p b_(p,j), the full binomial product gives
B_j=1+m_j S_j+m_j^2 Q_j, hence S_j=(-1)^(j+1)A modulo 3^(j+1).
The exponent j+1 is the maximal modulus forced by the TBN.2--TBN.3
hypotheses: (u_j-S_j)/3^(j+1)=2Q_j modulo 3, so a lift requires the
extra condition Q_j=0 modulo 3. Accidental lifts occur in small blocks and
do not make a uniform theorem.

OEIS A268924 and A271223 concern Hensel/Lucas approximants to the
3-adic square root of -2 and their base-3 digits. A is the normalized
residual limit for (L_(3^j)^2+2)/(2*3^(j+1)); the weighted actual-depth
congruence is additional and is not asserted by those entries. See
https://oeis.org/A268924 and https://oeis.org/A271223. This remains
paper-first and does not resolve WSS existence.
