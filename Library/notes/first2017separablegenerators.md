---
bibkey: first2017separablegenerators
authors: Uriya First; Zinovy Reichstein; Santiago Salazar
year: 2017
title: On the number of generators of a separable algebra over a finite field
doi: 10.48550/arXiv.1709.06982
url: https://arxiv.org/abs/1709.06982
claim: Theorem 1.1 and Proposition 2.3 count generators of finite etale algebras by Frobenius orbits; the golden-tower calculations below are separate ordinary proofs.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite-field generators and the actual golden tower

## Primary source and attribution

First-Reichstein-Salazar, arXiv:1709.06982v1 (20 September 2017),
Theorem 1.1, Proposition 2.3 and Lemma 3.3, printed pages 2, 4 and 5:
https://arxiv.org/pdf/1709.06982 .
For a product of r copies of F_(q^n), the least generator count is the
least g for which r <= (1/n)*sum_(d|n) mu(d)*q^(gn/d). Distinct degree
parts take the maximum of their counts. The source proves this by
counting full Frobenius orbits of tuples. Those are classical inputs to
GTC2 below, not new general generator theorems. The indicated PDF text
was read; the requested page-2 and page-5 screenshots failed.

The existing Problems owner remains
`Problems/wall-sun-sun-golden-unit-lift.md`. Its companion
`Library/notes/dunn2024cubicreciprocity.md`, GIR and GMI, supplies the
actual golden tower and the distinction between normalization and
power-generator indices. GTC is the continuation of those objects.
It does not create a different WSS problem or attribute its proofs to
the authors of the source above. The older companion is retained intact.

## GTC.1 Actual dyadic splitting of the common golden fields

For j>=1 retain B_j=L_(3^j)^2+3 and its positive real cube root theta_j.
Set

$$F_J=\mathbb Q(\theta_1,\ldots,\theta_J),\qquad
N_J=F_J(\omega),\quad \omega^2+\omega+1=0,$$

and let L=Q_2(omega), R=Z_2[omega]. This local quadratic extension is
unramified, with residue field F4. It is unrelated to the notation for
the global Lucas numbers L_n. Write m_J=(3^J-1)/2.

**Theorem GTC1.** For every J>=1,

$$\boxed{\mathcal O_{F_J}\otimes\mathbb Z_2
\simeq\mathbb Z_2\times R^{m_J},\qquad
\mathcal O_{N_J}\otimes\mathbb Z_2\simeq R^{3^J}.}\tag{GTC1}$$

In particular two is unramified in both fields and divides neither
field discriminant. These formulas require no h_p=1 assumption.

**Proof.** GIR proves [F_J:Q]=3^J and
Gal(N_J/Q)=(Z/3)^J semidirect C2, where the involution inverts the
translation group. Briefly, disjoint block supports and GCR's noncube
balance give a prime of depth nonzero modulo three in each block.
Taking valuations there proves the independence of all J cube classes.
Kummer theory gives the group and degree. The involution fixing the
positive cube roots fixes exactly F_J.

Every odd integer B has a unique cube root r in Z_2^times: the residue
root is one and the derivative of t^3-B is odd there, so Hensel lifting
applies. Choose a place of N_J with theta_j mapped to that rational
2-adic root r_j and omega to omega. The completion is exactly L,
since all roots r_j*omega^a lie there and omega is already in N_J.
Its Frobenius fixes all r_j and sends omega to omega^2. Thus its action
is the specified involution. On the 3^J embeddings of F_J, labelled
by vectors a in (Z/3)^J, it acts by a -> -a. There is one fixed vector
and m_J two-element orbits. This proves the first decomposition.
The normal field has 3^J primes of residue degree two, proving the
second. Taking maximal integral rings gives GTC1. All factors are
unramified; this also agrees with GIR's explicit discriminant formulas.

## GTC.2 Exact local generator counts, including lower and upper constructions

Here gen_2(K) is the least number of elements generating
O_K tensor Z_2 as a unital Z_2-algebra. It is a LOCAL algebra generator
count, not the dimension of K and not the least number of global
integral generators.

**Theorem GTC2.** One has

$$\boxed{\operatorname{gen}_2(F_J)
=\min\{g\ge0:4^g-2^g\ge3^J-1\},}\tag{GTC2}$$

$$\boxed{\operatorname{gen}_2(N_J)
=\min\{g\ge0:4^g-2^g\ge2\cdot3^J\}.}\tag{GTC3}$$

Consequently O_(F_J) is nonmonogenic for J>=2, and O_(N_J) is
nonmonogenic for every J>=1, already by obstruction at two.

**Proof.** An F4 component requires a tuple in F4^g not fixed by
Frobenius; different components require different Frobenius orbits,
otherwise polynomial evaluation cannot separate them. Exactly 2^g
tuples are fixed, so there are (4^g-2^g)/2 eligible orbits. Conversely
choose that many distinct orbits. Their evaluation kernels in
F2[X_1,...,X_g] are distinct maximal ideals. CRT proves surjectivity
onto the product of the corresponding F4 factors. A single F2 component
can use any fixed tuple and has a different kernel automatically.
This proves necessity AND attainment of the displayed finite-field
bounds, the n=2 case of the cited general theorem.

Lift the tuple coordinates to the indicated finite free Z_2-algebra.
The subalgebra they generate is a finite Z_2-module because the elements
are integral. Surjectivity after reduction modulo two and Nakayama's
lemma imply equality with the full algebra. Conversely every generating
set reduces to a generating set. This proves GTC2-GTC3 over Z_2.
Any global generating set is also a local one, proving the exclusions.
Both counts grow as (J log(3))/log(4)+O(1); no fixed number of integral
coordinates can generate all levels, even locally at two.

## GTC.3 The exact common-index valuation as a terminating minimization

For a number field K define

$$\nu_2(K)=\min_{\alpha\in\mathcal O_K,\,\mathbb Q(\alpha)=K}
 v_2([\mathcal O_K:\mathbb Z[\alpha]]).$$

Equivalently this is the two-valuation of the gcd of all integral
primitive-element indices. It is different from both GMI's
[A_j:Z[alpha]] and GIR's normalization index [O_(k_j):A_j].
Only the two-part of the common index is computed below.

Put C(n)=n(n-1)/2. Define

$$W(n)=\sum_{s\ge1}\left(r_s C(q_s+1)+(4^s-r_s)C(q_s)\right),
\quad n=4^s q_s+r_s,\quad0\le r_s<4^s.\tag{GTC4}$$

Only finitely many summands are nonzero. Let U(0)=V(0)=0. For n>=1,
compute U(n) before V(n), using

$$\boxed{U(n)=\min_{\substack{a+b+c=n\\a<n,\ b<n}}
 \{C(2a)+U(a)+C(2b)+U(b)+2C(c)+2W(c)\},}\tag{GTC5}$$

$$\boxed{V(n)=\min_{\substack{a+b+c=n\\a<n}}
 \{C(2a+1)+V(a)+C(2b)+U(b)+2C(c)+2W(c)\}.}\tag{GTC6}$$

All minimization variables are nonnegative integers. Every entry on
the right is already available, so these are finite exact recurrences.

**Theorem GTC3.** For the actual golden fields,

$$\boxed{\nu_2(F_J)=V(m_J),\qquad \nu_2(N_J)=U(3^J).}\tag{GTC7}$$

Every lower bound is attained by an integral primitive element of the
corresponding global field. Attainment here concerns the TWO-VALUATION;
the total integer index may have additional odd factors.

**Proof, step 1: the discriminant energy.** An integral primitive element
of L^n is a tuple (z_1,...,z_n) with z_i in R, each z_i nonrational and
no two pairs {z_i,bar(z_i)} equal. A primitive element of Q_2 times L^n
has additionally one rational integral coordinate. Thus the complete
root set consists of n nontrivial conjugate pairs, with zero or one
rational root. Since the maximal algebra is unramified, its discriminant
is a unit. The Vandermonde formula and the index/discriminant relation give

$$v_2([T:\mathbb Z_2[\alpha]])
=\sum_{x<y\text{ in the root set}}v_2(x-y).\tag{GTC8}$$

This is a sum over unordered distinct roots, independent of their ordering.
For x=A+B omega in R, v_2(x)=min(v_2(A),v_2(B)). No factor of two from
the quadratic residue degree is inserted in the root-distance sum.

**Step 2: unconstrained branches.** For n arbitrary distinct elements
of R, the minimum of the same pair-distance sum is W(n). Indeed
v_2(x-y)=sum_(s>=1) 1_(x=y modulo 2^s). Among 4^s residue classes the
collision count is minimized by populations differing by at most one,
which gives the s-th summand of GTC4. These minima can be achieved
simultaneously: write i=0,...,n-1 in base four and replace each digit
0,1,2,3 by 0,1,omega,1+omega, with successive weights 1,2,4,... .
The resulting elements have balanced low-digit populations at every
precision. Thus W is both a lower bound and an explicit attainable cost.

**Step 3: conjugate pairs.** Modulo two, Frobenius fixes the classes zero
and one and exchanges omega and omega^2. Suppose a pairs reduce to zero,
b pairs to one, and c pairs have one root in each nonfixed class.
The first-level collisions contribute C(2a)+C(2b)+2C(c).
After subtracting the scalar residue and dividing by two, the first
two clusters are again problems of the same paired type. The other
cluster consists of c arbitrary roots in one nonfixed residue, with its
conjugate cluster determined, contributing 2W(c) at the finer levels.
This proves GTC5. A minimum cannot have all pairs in one fixed residue:
subtracting that residue and dividing by two would strictly decrease
the energy. This justifies excluding the two circular choices.

With a rational root present, translate by zero or one so that its
residue is zero. The zero cluster has 2a+1 roots and cost V(a), the one
cluster has 2b roots and cost U(b), and the nonfixed clusters are unchanged.
The same exclusion of a circular choice gives GTC6. These arguments
supply lower bounds for every primitive tuple.

**Step 4: attainment and globalization.** Choose a minimizing triple
(a,b,c). Lift the zero-cluster witnesses by z -> 2z, the one-cluster
witnesses by z -> 1+2z, and the free witnesses by z -> omega+2z together
with their conjugates. Induction yields finitely many distinct elements
of Z[omega] with exactly the required conjugation pattern and cost.
The rational coordinate stays rational. Hence U and V are attained
by actual integral local tuples, not by multiplicity profiles alone.

Choose an integer M strictly larger than every pairwise valuation in
such a tuple. The map O_K -> (O_K tensor Z_2)/2^M is surjective.
Lift the attaining tuple to an element alpha in O_K. Its local roots
remain distinct and retain exactly the same pairwise valuations.
Distinctness proves Q(alpha)=K, and GTC8 gives the same index valuation.
This proves GTC7 and global attainment. This last argument is the standard
local-to-global interpretation of the common index; the specific optimal
cost and witnesses are calculated above.

## GTC.4 Sharp growth and explicit global attaining elements

**Theorem GTC4.** If D is the degree of either F_J or N_J, then

$$\boxed{W(D)\le\nu_2(K)\le D^2/6,}\tag{GTC9}$$

and consequently

$$\boxed{\nu_2(K)=D^2/6+O(D\log D)\quad(J\longrightarrow\infty).}\tag{GTC10}$$

This describes quadratic growth of an unavoidable polynomial-model
index at a prime which remains unramified in the maximal integer ring.

**Proof.** Dropping the conjugation constraints proves the lower bound.
For the upper bound use induction in GTC5-GTC6, with
U(n)<=2n^2/3 and V(n)<=(2n+1)^2/6. The cases n=0,1,2,3 follow directly
from the recurrences. For n>=4 write n=4a+r, 0<=r<=3, and choose
(a,b,c)=(a,a,2a+r). Since W(c)<=c^2/6, the excess over 2n^2/3 in
GTC5 is at most 2r^2/3-n, which is nonpositive. The excess over
(2n+1)^2/6 in GTC6 is at most 2r^2/3-4a-5r/3, also nonpositive.
This proves the upper bounds. For k=floor(log_4 D), Cauchy's inequality
at each of the first k residue levels gives

$$W(D)\ge D^2/6-(D/2)\lfloor\log_4D\rfloor-2D/3.$$

The omitted geometric-series tail is at most 2D/3. Together these
bounds prove GTC10; no independence or equidistribution heuristic occurs.

The first five exact stages of GTC5-GTC7 are:

| J | [F_J:Q] | nu_2(F_J) | nu_2(N_J) | gen_2(F_J) | gen_2(N_J) |
|---|---:|---:|---:|---:|---:|
| 1 | 3 | 0 | 2 | 1 | 2 |
| 2 | 9 | 6 | 36 | 2 | 3 |
| 3 | 27 | 89 | 408 | 3 | 3 |
| 4 | 81 | 964 | 4072 | 4 | 4 |
| 5 | 243 | 9338 | 38262 | 5 | 5 |

These finite values are evaluated exact recurrences whose unrestricted
proof is GTC3. The field degree of N_J is twice the displayed F_J degree.

**Explicit witnesses.** Put theta=cuberoot(19), zeta=cuberoot(5779).
In F_2 and N_1 respectively take

$$\alpha_F=\theta+\zeta+2\theta^2\zeta,\qquad
\alpha_N=\theta+\omega+2\theta\omega.\tag{GTC11}$$

They are global integral primitive elements and attain nu_2(F_2)=6
and nu_2(N_1)=2. A direct finite certificate is as follows. Both rational
2-adic cube roots of 19 and 5779 are three modulo four. Evaluate alpha_F
at all nine pairs 3omega^i,3omega^j, and alpha_N at all six choices
3omega^i,omega^e with e=1,2. In coefficient pairs (A,B) for A+Bomega,
their residues modulo four are respectively

$$(0,0),(3,1),(2,3),(1,1),(2,2),(1,2),(0,3),(3,2),(0,2),$$

$$(3,3),(0,1),(2,2),(1,2),(3,2),(0,2).$$

Each list is pairwise distinct, so these elements are primitive. All
root distances have valuation zero or one; their sums are six and two.
As a second certificate, the N_1 witness has minimal polynomial

$$X^6+3X^5+6X^4+7X^3-507X^2-510X+9748,$$

whose discriminant has two-valuation four. The F_2 witness polynomial
is the monic resultant of t^3-19 and
(X-t)^3-5779*(1+2t^2)^3 with respect to t; its degree is nine and its
discriminant has two-valuation twelve. These agree with GTC8 and the
unit maximal-order discriminants at two. They do not claim total
indices four or sixty-four, only those exact two-primary parts.

## GTC.5 Arithmetic-geometric consequence and WSS boundary

Every maximal local algebra in GTC1 is finite etale over Z_2 and hence
has a regular total space. Nevertheless for J>=2 every global primitive
polynomial model Z[alpha] of F_J has a nontrivial normalization defect
above two; the same holds for N_J at every J>=1. Its two-primary size
is at least 2^nu_2(K), with the exact attainable exponent above.
A nonnormal point of this one-dimensional finite arithmetic order is
not regular. Thus singularities in primitive polynomial models can be
forced entirely by residue-orbit collisions while the normalized scheme
remains unramified. Two divides no actual B_j and is not part of the
original WSS factor set.

For the first J=2 stages the actual blocks are 19 and 5779, both prime
and of original depth one. GIR's block normalization indices are both
one. Yet the combined F_2 already has nu_2(F_2)=6. This is a concrete
counterexample to identifying an arbitrary tower-generator index or
its polynomial-model singularities with the block WSS index.
It does not refute the SPECIFIC GIR/GNT equivalence for A_j subset O_(k_j).
GMI's implication from monogenic O_(k_j) to a WSS factor also remains
unchanged; GTC treats the different fields F_J and N_J.

The tower fields and the independent elliptic points on them were
already constructed in GIR. GTC computes the additional unavoidable
integral-presentation cost of that same tower. The rank lower bounds
are not recounted as new. No new WSS prime, new decided WSS prime family,
new nonmaximal golden block, P^2Q^3 exclusion or external open-problem
solution follows. Global priority of these prescribed-family calculations
has not been established.

## Additional primary literature and reproducibility scope

Enric Nart, *On the index of a number field*, Transactions AMS 289
(1985), 171-183, DOI 10.1090/S0002-9947-1985-0779058-2:
https://portalrecerca.uab.cat/en/publications/on-the-index-of-a-number-field/ .
The author's institutional record confirms the scope and classical
index problem. No unread numbered formula of that paper is used here.

Ilaria Del Corso and Roberto Dvornicich, *On Ore's conjecture and its
developments* (2005), institutional record:
https://arpi.unipi.it/handle/11568/184256 .
Its abstract explicitly records localization of the common index and
an effective procedure for powers of normal tame local extensions.
Thus an effective common-index procedure for normal local products is
prior work. GTC supplies the displayed direct paired/singleton recurrences
and their concrete golden application; it does not claim the first
algorithm for this general problem. Only the institutional abstract was
read, so no stronger comparison or attribution of a numbered theorem
is asserted.

N. K. Godara, A. Jakhar and R. Joshi, *Number fields with prescribed
p-adic index*, Ramanujan Journal 70, article 41 (8 June 2026),
DOI 10.1007/s11139-026-01418-1:
https://link.springer.com/article/10.1007/s11139-026-01418-1 .
The publisher preview reports explicit index valuations in families.
Only the abstract and bibliography were available, not the full proof;
no theorem of that paper is a premise of GTC or a verified novelty
comparison. The growing degrees in GTC are explicitly retained.

The companion verifier computes the finite recurrence, constructs attaining
Z[omega] tuples, checks pairwise valuations and independent power-basis
determinants, exhausts the small residue-orbit cases modulo four, and
checks the two global witness discriminants. Its larger product-algebra
fixtures instantiate the PROVED local splitting of the actual tower;
they are not separately computed global maximal-order bases. Neither
finite checks nor source attribution substitute for the general proofs.
No Lean elaboration, Scribe compilation or high-degree global maximal-order
calculation is claimed. The source count theorem is classical; the
recurrence, attainment, growth and golden applications are ordinary
mathematical deductions with their exact assumptions displayed.
