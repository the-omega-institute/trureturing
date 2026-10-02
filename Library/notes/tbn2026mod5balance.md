---
bibkey: tbn2026mod5balance
authors: trureturing research continuation
year: 2026
title: A mod-5 Fermat-quotient balance in the split Lucas tower
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/WSS_TBN_MOD27_BALANCE.md
claim: Every fixed-golden Lucas block B_j=L_(2*3^j)+1 has a nonzero weighted Fermat-quotient depth sum modulo 5, forcing a factor with 5-nondivisible original depth outside the Fermat-quotient kernel modulo 25.
license: repository-original
triage: anchor
strata_touched: []
---

This note records Theorem FQ5 in
`docs/develop/theory/WSS_TBN_MOD27_BALANCE.md`. Keep the existing TBN.2--TBN.3
identities

    B_j=L_(2*3^j)+1=product_(p|B_j) p^(h_p),
    B_(j+1)=B_j^3-3B_j^2+3, B_1=19,

where h_p is the original Fibonacci initial depth and every p|B_j has exact
rank 2*3^(j+1) in the fixed golden field. For 5-coprime x define

    lambda_5(x)=(x^4-1)/5 mod 5.

The elementary identities lambda_5(xy)=lambda_5(x)+lambda_5(y) and
lambda_5(x^a)=a lambda_5(x) follow from x^4=1 mod 5 and multiplication
modulo 25. The block recurrence gives B_j=19 mod 25 for odd j and 4 mod 25
for even j. Therefore

    sum_(p|B_j) h_p lambda_5(p) = 4 mod 5 (j odd),
    sum_(p|B_j) h_p lambda_5(p) = 1 mod 5 (j even).

Since the kernel of lambda_5 on the units modulo 25 is
{1,7,18,24}, every block has a factor with 5 not dividing h_p and with
p mod 25 outside that kernel. This is a direct restriction on the actual
initial-depth vector in the fixed golden field. If h_p=1 the witness is
non-WSS; if h_p>=2 it is WSS. The result deliberately does not choose either
case and does not resolve Wall--Sun--Sun.

The first exact rows are:

    j=1: B=19, sum=4;
    j=2: B=5779, sum=1;
    j=3: B=3079*62650261, sum=4;
    j=4: B=59779*120074026624398979403194983601, sum=1;
    j=5: factors 1459, 58321, 67234945243909760461,
         64642456533364216165903625998192510598323380531684784427098565775883411861,
         sum=4.

The proof does not use these factorizations. The existing RP.3 theorem gives a
mod-5 weighted identity for odd-index primitive Fibonacci blocks; it does not
cover these even-rank fixed Lucas blocks as stated. A targeted search of the
dev tree and WSS PR history found no prior lambda_5(B_j) balance. This source is
paper-first and has no Lean/Scribe declaration.

Inputs are TBN.2--TBN.3, the elementary Fermat-quotient calculation recorded
as RP.1 in PERIODIC_TREE.md, and the classical Fibonacci valuation baseline
recorded in Medina--Rowland, Fibonacci Quarterly 53 (2015), Theorem 1.4,
arXiv:0910.2907.
