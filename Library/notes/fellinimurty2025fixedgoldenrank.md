---
bibkey: fellini-murty2025fixedgoldenrank
authors: Nic Fellini and M. Ram Murty
year: 2026
title: Wieferich primes in number fields and the conjectures of Ankeny--Artin--Chowla and Mordell
doi: null
url: https://arxiv.org/html/2508.08472v2
claim: Under Masser's number-field abc conjecture, the published square-free cyclotomic extraction specializes to one non-Wall prime in every sufficiently large prime Fibonacci-rank channel.
license: citation-only
triage: anchor
strata_touched: []
---

# Fixed-golden rank corollary

Fellini--Murty v2, Theorems 1.2 and 1.4 and Lemmas 5.4--5.6, proves under
number-field abc that for an admissible base alpha in a number field, the
square-free part U_n of alpha^n-1 has norm tending to infinity, and extracts a
non-Wieferich prime ideal from U_q for each sufficiently large rational prime
index q (their proof, lines 543--548). Distinct prime indices give distinct
prime ideals by their Lemma 5.5.

Specialize to K=Q(sqrt(5)), O=Z[phi], phi=(1+sqrt(5))/2, and v=phi^2.
Since v-1=phi is a unit, the finite A_1 exception is empty. Remove only primes
above 2 and 5 and finitely many initial indices. For each remaining prime index
ell, a divisor pfrak of U_ell has residue order exactly ell (Lemma 5.4; its
residue characteristic cannot equal ell because v-1 is a unit), and is
non-Wieferich for v (Lemma 5.6).

For p=pfrak cap Z >5, split p gives residue degree one and ell | p-1;
inert p gives degree two, v has norm one, and ell | p+1. In both cases
ord_p(-v)=2 ell because ell is odd. The standard identity phi/bar(phi)=-v
identifies this with the Fibonacci rank rho(p), so rho(p)=2 ell.

The fixed-golden first-lift identity (CG.1/SJC.6 in the WSS dossier) is
v^(p-(5/p))-1 = p (5/p) q_p sqrt(5) mod p^2 O, where
q_p=F_(p-(5/p))/p mod p. For split p the Fellini--Murty exponent is p-1;
for inert p it is p^2-1=(p-1)(p+1), and
(1+pt)^(p-1)=1+p(p-1)t mod p^2. Therefore the extracted non-W condition is
exactly q_p != 0, i.e. p is non-Wall-Sun-Sun.

Conclusion (conditional): there is ell_0 such that every prime ell >= ell_0
has a rational p with q_p != 0, rho(p)=2 ell, and ell | p-(5/p).
The p are distinct for distinct ell. Counting prime ell <= c log X gives
at least a constant multiple of log X/log log X such p <= X. The split/inert
sign need not be fixed in advance. This is an application to the fixed golden
WSS zero set; it is not claimed as a new theorem in the cited literature, nor
as an unconditional WSS result.

Primary sources:
- Fellini--Murty, https://arxiv.org/html/2508.08472v2 (Theorems 1.2, 1.4; Lemmas 5.4--5.6; extraction at lines 543--548).
- Grell--Peng, https://arxiv.org/html/1511.01210 (Theorem 3, older conditional square-free Fibonacci argument).
- WSS dossier, `Problems/wall-sun-sun-golden-unit-lift.md`, CG.1/SJC.6 for the fixed-golden lift identity.

Literature boundary checked: Grell--Peng (arXiv:1511.01210, Theorem 3)
obtains only unbounded square-free Fibonacci parts under abc, while
Fellini--Murty's later norm-to-infinity statement is what gives every large
prime index. Ding (C. R. Acad. Sci. Paris 357 (2019), Theorem 1.1) and
Graves--Murty treat non-Wieferich primes in fixed arithmetic progressions for
integer bases; their modulus is fixed and does not encode the varying exact
Fibonacci rank. No checked source states the above fixed-golden contraction
with rho(p)=2 ell.
