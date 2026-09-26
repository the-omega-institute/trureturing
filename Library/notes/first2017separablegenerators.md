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


## GGL. Ramified residue labels and exact global integral generator counts

### GGL.0 Reconcile the existing boundaries before adding a new one

Retain the actual golden integers and fields of GIR/GTC:

$$B_j=L_{3^j}^2+3,\quad \theta_j=\sqrt[3]{B_j}>0,\quad
F_J=\mathbb Q(\theta_1,\ldots,\theta_J),\quad N_J=F_J(\omega),$$

where J>=1 and omega^2+omega+1=0. The original WSS depth remains
h_p=v_p(B_j) at a factor p of B_j. None of the following arguments
assumes h_p=1. Put m_J=(3^J-1)/2. Write g_R(A) for the least number of
UNITAL R-algebra generators, and g_q(K)=g_(Z_q)(O_K tensor Z_q).
This counts algebra generators, not module rank or primitive-element index.

At inspected PR head e51b14884c40f2d31865c69707d54e08a4440ff6 the repository
already contains these parallel source endpoints:

* GoldenMatrixPeriodBridge.golden_matrix_faithful: a faithful golden
  multiplication matrix and equality of its order with that of phi.
* GoldenPrimePeriodBounds.golden_prime_period_bounds: at primes p>5,
  the Fibonacci matrix order divides p-1 in the split case and 2(p+1)
  in the inert case; it is prime to p. The source's legendreSym 5 p is
  the character modulo five, equal to (5/p) here by reciprocity.
* GoldenPrimePowerOrder.golden_prime_power_order: an element
  1+p^m(a+b phi) of exact coefficient depth m has order p^n modulo
  p^(m+n), under m>0, m+2<=pm and at least one coefficient a,b prime to p.
  For p>5 the numerical inequality holds for every m>=1. The exact
  starting depth is an input, not proved to be one by this endpoint.

These existing sources must no longer be listed as missing local-order
machinery. Their general mathematical statements are classical. This
pass reads their statements and proofs but does not recompile, certify,
modify, or claim authorship of them. Applying the last endpoint to the
original Fibonacci return still uses PCL's equality of its coefficient
depth with h_p; it does not independently decide h_p. GGL below uses the
already-proved GIR field and GTC dyadic data, not a new WSS consequence
of the parallel source files.

A different gap is explicitly present in GTC.2: its dyadic generator
counts are global LOWER bounds, without a matching global upper bound.
GGL closes that gap by retaining the prime three and constructing one
common tuple of integer generators, rather than choosing unrelated
local tuples and declaring that they glue.

### GGL.1 Lifting residue labels also handles ramified local factors

**Lemma GGL1.** Let q be prime and K a degree-D number field. For g>=1,
if the reduced algebra of O_K/qO_K can be generated by g elements over
F_q, then O_K/qO_K can also be generated by g elements. The same count
applies to O_K tensor Z_q. In particular,

$$\boxed{q^g\ge D,\ g\ge1\quad\Longrightarrow\quad g_q(K)\le g.}\tag{GGL1}$$

**Proof.** Factor qO_K into powers of distinct prime ideals. Each factor
of O_K/qO_K is an Artinian principal local ring of characteristic q,
with residue field F_(q^f) and length e. It has a coefficient field:
unique lifting of the roots of X^(q^f)-X across the nilpotent maximal
ideal gives a copy of F_(q^f). The derivative is -1, so these lifts exist
and are unique, and they are closed under the field operations.
A generator epsilon of the maximal ideal then gives an isomorphism
with F_(q^f)[epsilon]/(epsilon^e), by successive reduction and length.

A generating g-tuple in the reduced product gives, at each factor, a
field-generating residue tuple (a_1,...,a_g), with distinct Frobenius
orbits at distinct factors. Lift it locally to
(a_1+epsilon,a_2,...,a_g), omitting epsilon for e=1. A sufficiently large
q^(fM)-th power kills epsilon and fixes every a_i, so the generated
subalgebra contains the coefficient field, then epsilon. It is the
whole local factor. Evaluation kernels for distinct factors have
different maximal radicals, hence are comaximal; CRT proves generation
of their product. Conversely, generators reduce to generators.

The reduced algebra is finite etale of F_q-dimension at most D.
First-Reichstein-Salazar, Corollary 4.2, gives at most ceil(log_q D)
generators, so q^g>=D suffices. Their theorem is used only for this
reduced algebra; the nilpotent lifting has just been proved separately.
To pass to Z_q, lift any generating residue tuple to O_K tensor Z_q.
Its subalgebra is finite as a Z_q-module because all generators are
integral. The finite quotient vanishes modulo q, hence vanishes by
Nakayama. The converse follows by reduction. This proves GGL1.
The hypothesis g>=1 excludes the exceptional zero-generator case of
F_q itself versus a nontrivial nilpotent thickening of it.

### GGL.2 The prime three gives an exact, stronger local lower bound

Let R_3=Z_3[omega]. Here R_3 is RAMIFIED quadratic, with
R_3/3R_3=F_3[epsilon]/(epsilon^2). It must not be confused with the
unramified quadratic ring R at two used in GTC.

**Theorem GGL2.** For every J>=1,

$$\boxed{O_{F_J}\otimes\mathbb Z_3
\simeq\mathbb Z_3\times R_3^{m_J},\qquad
O_{N_J}\otimes\mathbb Z_3\simeq R_3^{3^J}.}\tag{GGL2}$$

Consequently

$$\boxed{g_3(F_J)=g_3(N_J)=J.}\tag{GGL3}$$

**Proof.** GIR1 proves that every B_j is a cube in Q_3. Explicitly,
B_j=1+9a_j and the equation z+3z^2+3z^3=a_j has derivative one modulo
three. Hensel lifting gives (1+3z)^3=B_j. Thus a completion of N_J is
exactly Q_3(omega). Its decomposition group is the involution fixing
these chosen rational cube roots and inverting omega. On the embeddings
of F_J, indexed by (Z/3)^J, it acts by a -> -a. There is one fixed point
and m_J pairs. This proves the field decompositions; taking maximal
integer rings gives GGL2. The polynomial of omega-1 is
X^2+3X+3, Eisenstein at three, and its reduction is X^2.

For F_J the reduced special fiber has m_J+1=(3^J+1)/2 copies of F_3;
for N_J it has 3^J copies. A g-tuple labels each component by a point of
F_3^g. Distinct components require distinct labels. Conversely choose
distinct labels and, on each length-two component, add epsilon to the
first coordinate. Lemma GGL1 proves generation. Thus the exact counts
are the least positive g with 3^g>=(3^J+1)/2 or 3^g>=3^J, respectively.
Since 3^(J-1)<(3^J+1)/2<=3^J, both counts equal J.

This is a bound on the FULL three-adic algebra, not only its number of
nilpotent directions. At each component there is only one nilpotent
direction. The growing cost comes from distinguishing all components
by one shared tuple over the finite residue field.

### GGL.3 One common tuple over the integers: a constructive gluing lemma

**Lemma GGL3.** Let K be a degree-D number field and g>=2. If
O_K/qO_K is generated by g elements over F_q for every rational prime
q<=D, then there are g elements of O_K which generate it over Z.
The same assertion holds over Z[S^(-1)] for any finite set S of primes,
with the conditions imposed only at primes outside S.

**Proof.** At each prime q<=D outside S, choose a generating g-tuple
and prescribe its first coordinate. CRT in the free Z-module O_K
produces a common lift alpha_0. Put M equal to the product of these
finitely many primes, with empty product one. Choose an integral
primitive element beta of K and consider alpha_0+Mt beta for integers t.
For any pair of distinct embeddings sigma,tau of K, their values on
beta differ. Hence equality of their values on alpha_0+Mt beta excludes
at most one t. Avoiding the finitely many forbidden t gives an integral
primitive alpha_1 with all prescribed first coordinates unchanged.

The index [O_K:Z[alpha_1]] is finite. Let T be its prime support outside
S. At primes q in T with q>D, Lemma GGL1 with g=1 applies since q>D:
O_K/qO_K is monogenic. Choose such a local generator as coordinate two
and set the unused coordinates to zero. At the originally prescribed
small primes use the already chosen remaining g-1 coordinates.
A second application of CRT, now over their finite union with T,
constructs global alpha_2,...,alpha_g with all these values.

The ring C=Z[alpha_1,...,alpha_g] has finite index in O_K because it
contains Z[alpha_1]. At each small prime the complete prescribed tuple
generates; at each new prime in T, coordinate two suffices; outside T,
alpha_1 already generates after localization. Hence no prime outside S
divides [O_K:C]. Therefore C[S^(-1)]=O_K[S^(-1)]. Taking S empty proves
the integer assertion. Each CRT step uses a single common tuple.
This proof does not infer global generation from unrelated local choices.

This is a direct arithmetic gluing argument using classical primitive
elements, CRT and finite-index localization. First-Reichstein's general
algebraic Forster bound supplies broader context, but its n+d upper
bound alone is not substituted for this sharp lemma. No first general
local-to-global generator theorem is claimed here. Given an integral
basis and the finite residue data, this is a terminating construction;
it does not bound the heights of the chosen integers or make the
required integral-basis computation free.

### GGL.4 Exact GLOBAL generator counts of the actual golden towers

**Theorem GGL4.** Let g_Z(O_K) count generators as a unital Z-algebra.
Then

$$\boxed{g_{\mathbb Z}(O_{F_J})=\max(2,J),}\tag{GGL4}$$

$$\boxed{g_{\mathbb Z}(O_{N_J})=
\begin{cases}2,&J=1,\\3,&J=2,\\J,&J\ge3.\end{cases}}\tag{GGL5}$$

These are both lower bounds and attainable counts. They make no
assumption about the original h_p at any golden block factor.

**Proof.** For F_J with J>=2 the prime-three lower bound is J.
For J=1 the actual B_1=19 is squarefree, so GIR gives O_(F_1)=A_1.
GMI proves A_1 nonmonogenic, giving the lower bound two. This last
argument is the previously proved specific block result.

For N_J, GTC's dyadic counts are two at J=1 and three at J=2.
For J>=3 the prime-three lower bound is J.

For the upper bounds put g equal to the claimed answer. At three,
equation (GGL3) gives local generation by J<=g elements. At two, GTC gives the
counts from 4^g-2^g. For F_J, 4^J-2^J>=3^J-1: expand (3+1)^J-(1+1)^J
and retain its last nonnegative term. For N_J and J>=3,
4^J-2^J>=2*3^J, starting with 56>=54; if A_J denotes the difference,
A_(J+1)=3A_J+4^J+2^J>=0. The two small normal stages use g=2 and g=3.
At every prime q>=5, q^g>=D for the relevant degree D=3^J or 2*3^J.
For the normal tower this uses 5^J>=2*3^J for J>=2; the small cases
are immediate. Lemma GGL1 gives local generation at every such prime.
Finally Lemma GGL3 constructs one global tuple of exactly g generators.


### GGL.5 Exact effect of inverting the common ramified prime

Let g_2(F_J),g_2(N_J) retain GTC's exact dyadic formulas.

**Theorem GGL5.** For every J>=1,

$$\boxed{g_{\mathbb Z[1/3]}(O_{F_J}[1/3])=g_2(F_J),\qquad
 g_{\mathbb Z[1/3]}(O_{N_J}[1/3])=g_2(N_J).}\tag{GGL6}$$

**Proof.** The dyadic counts are necessary since two was not inverted.
They are at least two except for F_1. If g equals the relevant dyadic
count, the inequality defining that count implies 5^g>=D. All primes
q>=5 therefore satisfy the local upper bound GGL1. Apply the localized
version of Lemma GGL3 with S={3}. For F_1, GIR gives O_(F_1)=A_1 and
A_1[1/3]=Z[1/3][theta_1]; its degree excludes zero generators.
This proves the exceptional case and both equalities.

Thus for sufficiently large J the unlocalized cost is J, whereas after
inverting three it is (J log 3)/log 4+O(1). Their difference is
(1-log(3)/log(4))*J+O(1). This is a proved change in the required
integral coordinates, not an estimate obtained by dropping a local
condition without constructing global generators.

| J | g_2(F_J) | g_3(F_J) | g_Z(O_FJ) | g_2(N_J) | g_3(N_J) | g_Z(O_NJ) |
|---|---:|---:|---:|---:|---:|---:|
|1|1|1|2|2|1|2|
|2|2|2|2|3|2|3|
|3|3|3|3|3|3|3|
|4|4|4|4|4|4|4|
|5|5|5|5|5|5|5|
|6|5|6|6|6|6|6|
|8|7|8|8|7|8|8|
|10|8|10|10|9|10|10|

### GGL.6 What is now closed, and what this does not decide

The previously explicit gap between GTC's local lower counts and global
integer generation is closed by GGL4. In geometric language these are
the least numbers of affine coordinates for a closed immersion of the
specified Spec(O_K) into affine space over Z. Passing to Z[1/3] has the
exact effect GGL6. The normalized rings stay regular; the obstruction
comes from finite residue labels, rather than a new singular WSS block.

The dyadic bound alone is not generally the global answer: for example
J=6 gives g_2(F_6)=5 but g_Z(O_(F_6))=6. The prime three supplies the
missing lower bound. For F_1 the different phenomenon of GMI remains:
every local algebra is monogenic, but two global generators are needed.
No contradiction to GTC, which expressly asserted only local counts,
or to the parallel prime-period bounds is involved.

Neither an algebra generator count nor a tower primitive-element index
is the block normalization index I_j of GIR/GNT. The new equalities do
not decide whether an untested actual B_j has a WSS factor, do not
eliminate P^2Q^3, and do not identify an h_p=1 theorem in the inspected
parallel sources. The next WSS obligation still concerns the ORIGINAL
h_p. The generator problem itself now has a complete global answer in
both displayed towers and over the displayed localization.

### GGL.7 Literature, attribution and verification scope

The extension from residue fields to truncated DVR factors, the local
three-adic decomposition, and the common-integer CRT construction are
proved above. General finite-etale counts remain attributed to
First-Reichstein-Salazar, arXiv:1709.06982v1, Theorem 1.1,
Proposition 2.3 and Corollary 4.2 (printed page 7). The corollary is used
only after passing to the reduced finite algebra. The nonreduced
special fiber at three is not called etale.

For the general local-to-global context: Uriya A. First and Zinovy
Reichstein, *On the number of generators of an algebra*, Comptes Rendus
Mathematique 355 (2017), 5-9, DOI 10.1016/j.crma.2016.11.015;
arXiv:1610.08156v3, Theorem 1.2, its unital variant (i), and Lemmas
2.1-2.3. The stated general upper bound is n+d. GGL's sharp result uses
the separate finite-prime construction above, not an unmentioned
stronger statement from that paper. Primary locators:
https://arxiv.org/pdf/1610.08156v3 ;
https://arxiv.org/pdf/1709.06982 .
The first paper's page-one image and the relevant parsed passages of
both papers were inspected. Requested images of the other selected
pages failed; no visual inspection of those pages is claimed.

No first-ever general generator theorem or established global priority
for this prescribed family is asserted. The finite checks accompany
the general proofs, and do not constitute construction of explicit
high-degree global integral bases or height-bounded optimal tuples.
This pass supplies ordinary mathematics, with no new Lean source,
Lean/Scribe compilation, kernel certification, independent-model
review, new WSS witness or independently solved external open problem.
