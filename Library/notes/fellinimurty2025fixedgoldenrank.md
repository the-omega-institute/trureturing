---
bibkey: fellinimurty2025fixedgoldenrank
authors: Nic Fellini and M. Ram Murty
year: 2026
title: Wieferich primes in number fields and the conjectures of Ankeny--Artin--Chowla and Mordell
doi: null
url: https://arxiv.org/html/2508.08472v2
claim: Conditional fixed-golden rank-by-rank non-Wall witness corollary under Masser's number-field abc.
license: citation-only
triage: anchor
strata_touched: []
---

This note records the fixed-golden specialization in
docs/develop/theory/WSS_FM_RANK_COROLLARY.md. For
(K=Q(sqrt(5))), (phi=(1+sqrt(5))/2), and (v=phi^2), define
(U_n) as the product of prime ideals having valuation exactly one in
(v^n-1). Fellini--Murty's number-field abc argument implies
(N(U_n)	oinfty): an infinite bounded-norm subsequence would bound the
powerful complementary factor and contradict their norm-growth proposition.
Their cyclotomic extraction then gives, for every sufficiently large prime
index ell, a non-Wieferich ideal of exact residue order ell.

An inert prime is impossible for odd ell because
(v^{(p+1)/2}=phi^{p+1}=-1). Every witness therefore splits and satisfies
(p=1 mod 2ell); ord(-v)=2ell, and the fixed golden identity
(v^{p-(5/p)}-1=p(5/p)q_p sqrt(5) mod p^2) gives (q_p != 0) and
Fibonacci rank rho(p)=2ell. Distinct indices give distinct rational primes.
The exact norm
(|N(v^ell-1)|=v^ell+v^{-ell}-2<v^ell) gives the lower count
(gg log X/log log X).

This is conditional and scoped. It is a literature-derived alternative
route, not an unconditional WSS result and not a comparison of the abc
hypothesis with the project's separate PH(kappa) hypothesis.

Primary source: Fellini--Murty,
https://arxiv.org/html/2508.08472v2, Theorems 1.2, 1.4 and
Lemmas 5.4--5.6.
