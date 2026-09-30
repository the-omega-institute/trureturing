### FMR. Conditional rank-by-rank non-Wall witnesses in the fixed golden field

#### FMR.1 Statement

Let (K=mathbb Q(sqrt5)), (mathcal O_K=mathbb Z[phi]),
(phi=(1+sqrt5)/2), and (v=phi^2). For (p>5), put
(chi_p=(5/p)), (N_p=p-chi_p),
(q_p=F_{N_p}/ppmod p), and let (ho(p)) be the first positive
Fibonacci zero rank. Assume Masser's number-field abc conjecture for (K).
Then there is (ell_0) such that every prime (ellgeell_0) has a
rational prime (p>5) with
[
q_p
e0,qquad ho(p)=2ell,qquad ellmid p-chi_p.
]
The (p)'s for different (ell)'s are distinct. Every witness is split,
so in fact (pequiv1pmod{2ell}). Consequently
[
#{ple X:p>5, q_p
e0, ho(p)/2 {m prime}}
gg_{K,v}{log Xoverloglog X}.
]
This is conditional on abc and is a fixed-golden specialization of the
number-field extraction theorem; it is not an unconditional WSS result.

#### FMR.2 Exact square-free extraction

For a non-root-of-unity (alphainmathcal O_K), write the principal ideal
[
(alpha^n-1)=U_nV_n,qquad
U_n=prod_{mathfrak q:,v_{mathfrak q}(alpha^n-1)=1}mathfrak q,quad
V_n=prod_{mathfrak q:,v_{mathfrak q}(alpha^n-1)ge2}
       mathfrak q^{v_{mathfrak q}(alpha^n-1)}.
]
Thus (U_n) is the exact valuation-one factor and (V_n) is powerful; the
two ideals are coprime. Fellini--Murty, arXiv:2508.08472v2, Theorems 1.2,
1.4 and Lemmas 5.4--5.6, prove under Masser's number-field abc that
(N(U_n)) cannot remain bounded. The needed quantifier is all sufficiently
large (n), not merely a selected subsequence: if an infinite subsequence
had bounded (N(U_n)), the number-field abc inequality applied to
(1+(alpha^n-1)=alpha^n), together with
(operatorname{rad}(V_n)le N(V_n)^{1/2}), would bound (N(V_n)) on that
subsequence. This contradicts their norm-growth proposition
(N(alpha^n-1)	oinfty). Hence (N(U_n)	oinfty).

Their extraction argument then applies to each sufficiently large rational
prime index (ell). Since (N(U_ell)>1), choose
(mathfrak pmid U_ell). A valuation-one factor is non-Wieferich:
[
v_{mathfrak p}(alpha^{Nmathfrak p-1}-1)=1.
]
For an unramified prime with residue characteristic (p), their cyclotomic
valuation lemma gives
[
ell=p^i f_alpha(mathfrak p),qquad
f_alpha(mathfrak p)=operatorname{ord}_{mathfrak p}(alphamodmathfrak p).
]
The finite exceptional characteristics are removed below. Once (p
eell),
this forces (i=0), so the residue order is exactly (ell). Their
coprime-index lemma shows that prime ideals extracted from distinct prime
indices cannot repeat.

Apply this with (alpha=v). Since (v-1=phi) is a unit of norm (-1),
no prime ideal divides (A_1=(v-1)). Remove the finite primes above (2,3,5)
and finitely many initial indices. Also (p=ell) cannot occur: if a
valuation-one divisor above (p=ell) had residue order (1), then it would
divide (v-1), while an order-(ell) divisor is impossible because the
residue-field unit group has order prime to (ell). Thus every sufficiently
large prime (ell) supplies a prime (mathfrak pmid U_ell) above a
rational (p>5) with (operatorname{ord}_{mathfrak p}(v)=ell).

#### FMR.3 Inert primes are impossible

For (p>5), (p) is unramified in (K). If (p) were inert, Frobenius
sends (phi) to (arphi=1-phi), hence
(phi^{p+1}=N_{K/mathbb Q}(phi)=-1) in the residue field. Therefore
[
v^{(p+1)/2}=phi^{p+1}=-1
]
and the order of (v) is even. This contradicts its odd order (ell).
Thus every extracted (mathfrak p) lies over a split rational prime (p),
with residue degree one. Since (v) has order (ell) in
(mathbb F_p^	imes), (ellmid p-1). Moreover (-1
otinlangle vangle)
because (ell) is odd, so (operatorname{ord}_p(-v)=2ell). The Binet
identity (phi/arphi=-v) identifies this order with the Fibonacci
rank:
[
ho(p)=2ell,qquad pequiv1pmod{2ell}.
]
If the same rational (p) arose from two different indices, its reduction
would give two different orders for (v); conjugation only replaces (v) by
(v^{-1}), preserving order. Hence the contracted rational witnesses are
distinct.

#### FMR.4 Translation to the fixed Fibonacci quotient

The fixed-golden first-lift identity from CG.1/SJC.6 in the WSS dossier is
[
v^{N_p}-1equiv p,chi_p q_psqrt5
       pmod {p^2mathcal O_K}.
]
For the split (mathfrak p) above (p), (Nmathfrak p=p), so the
Fellini--Murty non-Wieferich condition is
(v^{p-1}
otequiv1pmod{mathfrak p^2}). Since (p) splits, this is
equivalent to (v^{N_p}
otequiv1pmod{p^2mathcal O_K}), and the displayed
identity is equivalent to (q_p
e0). Thus each extracted ideal contracts to
a rational non-Wall-Sun-Sun prime of exact rank (2ell).

#### FMR.5 Counting and logical scope

The exact absolute norm is
[
|N_{K/mathbb Q}(v^ell-1)|
 =v^ell+v^{-ell}-2 <v^ell .
]
Any rational prime below (U_ell) is therefore (<v^ell). Taking
(ellle(log X)/log v+O(1)) produces (ple X). The prime number theorem
gives (gglog X/loglog X) prime indices in this range, proving the count.

The Grell--Peng paper (arXiv:1511.01210, Theorem 3) gives a related
conditional infinitude argument through square-free Fibonacci parts, while
Ding and Graves--Murty give fixed-modulus arithmetic-progression estimates
for non-Wieferich bases. None of those checked statements phrases the
split-only contraction with (ho(p)=2ell). The present result is therefore
best recorded as a literature-derived fixed-golden corollary and alternative
conditional route. The project already contains the separate PH6 result under
the rational Pell-height hypothesis (mathrm{PH}(kappa)), (kappa<4/3);
no comparison of abc with that hypothesis is asserted here. No unconditional
WSS exclusion, WSS existence, or claim that the WSS zero set is empty follows.
