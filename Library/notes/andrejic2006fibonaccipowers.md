---
bibkey: andrejic2006fibonaccipowers
authors: V. Andrejić
year: 2006
title: On Fibonacci Powers
doi: 10.2298/PETF0617038A
url: https://doiserbia.nb.rs/Article.aspx?ID=0353-88930617038A
claim: A nonclassical Fibonacci perfect power would imply a Wall–Sun–Sun prime, by prime-index reduction and equality of the entry points at a prime and its square.
strata_touched: []
license: citation-only
triage: anchor
---

# Perfect powers and the Wall–Sun–Sun obstruction

## Verified locator

V. Andrejić, *On Fibonacci Powers*, Univ. Beograd. Publ. Elektrotehn. Fak.
Ser. Mat. 17 (2006), 38–44,
https://doi.org/10.2298/PETF0617038A .
Crossref and the DOI Serbia article record identify this publication.
The publisher PDF https://doiserbia.nb.rs/ft.aspx?id=0353-88930617038A
contains Lemma 4 on page 39 and Theorem 1, its proof and Lemma 5 on page 40.

## Claim and scope

Lemma 4 reduces a perfect q-th power F_n with n>12 to a perfect q-th power
F_ell at some prime ell>5. Theorem 1 states that the absence of WSS primes
would imply that the only Fibonacci perfect powers are 1, 8 and 144.
Contrapositively, a further perfect power would yield a WSS prime.

In the proof, every prime factor r of the prime-index block satisfies
r^2 dividing F_ell, hence Z(r^2)=Z(r)=ell. Lemma 5 identifies this entry-point
equality with the WSS square condition at the signed index r-(r/5).

This supplies a method precedent for FPD.4–FPD.5 of
`Problems/wall-sun-sun-golden-unit-lift.md`. A WSS prime alone does not
force all other factors of its rank block to have exponent at least two.
The cited implication neither gives its converse nor classifies all
powerful Fibonacci values.

## OSE. Finite original odd-depth support and a quantitative escape theorem

### OSE.0 Fixed object and already-proved prerequisites

This is an ordinary research continuation for the existing owner
`Problems/wall-sun-sun-golden-unit-lift.md`. The deductions below are not
attributed to Andrejic's paper. Retain the ORIGINAL Fibonacci and Lucas
sequences, F_0=0, F_1=1, L_0=2, L_1=1. For a prime p>5 put

$$\rho(p)=\min\{n\ge1:p\mid F_n\},\qquad
h_p=v_p(F_{\rho(p)})=v_p(F_{p-(5/p)}).$$

WSS means h_p>=2. In this section an odd super-depth prime means
h_p is odd and h_p>=3; depths two, four, six, etc. are not in that set.
Every use of this condition refers to h_p, not to v_p(F_n) at an
arbitrarily multiplied index. Put E_0={1,2,6,12}. Positive one is powerful.

The inspected `PERIODIC_TREE.md`, ZBD.1 and PBC.1-PBC.4, already proves:
(1) powerful Fibonacci values at five-smooth indices occur exactly at E_0;
(2) the largest index-prime ell>=7 of a powerful F_n has a powerful F_ell;
(3) such a block contains a prime of rank ell and odd h_p>=3;
(4) the analogous witnesses at successive largest-prime power layers;
(5) the partition of prime ranks into simple-factor and fully exceptional
blocks. These are prior repository results, not new OSE theorems.
The read snapshot was 9d48e0f0626ad25a583e2453bdda4ad23c70dee9,
ZBD/PBC around lines 4180-4375. FPD in the current owner supplies the same
largest-prime mechanism. Their square-class input is classical.

At PR head 3dcf7c4b1c1a54cb26bb4ac12787283626ffb28e the parallel local
formalization also contains GoldenCubicIndexForm, in addition to the
matrix bridge and exact prime-power order source. Its new public endpoint
constructs the actual cubic coordinate ring and proves the trace
and power-basis determinants. That source was read; it is preserved and
not recompiled or claimed as authored here. OSE returns to original
prime-depth support, rather than proving another generator-count bound.

We use the following classical inputs with their scopes unchanged:

* If p>5 and rho(p)|n, v_p(F_n)=h_p+v_p(n); otherwise the valuation is
  zero. Also rho(p)|p-(5/p). The small ranks are rho(2)=3, rho(3)=4,
  rho(5)=5. See the existing Medina-Rowland note, Theorem 1.4.
* F_n is square at positive indices exactly {1,2,12}. Its positive-index
  square classes have only two nonsingleton classes, {1,2,12} and {3,6}.
  Thus a specified squarefree d>2 occurs in F_n=d*y^2 for at most one n.
  Ribenboim, FFF (2005), (3.4), states this full classification; (3.7)
  states an effective fixed-d index bound, and (3.8) its rank-closure
  algorithm. These are stronger inputs than merely the absence of new
  perfect powers. They are credited rather than reproved here.

### OSE.1 A finite, computable closure of a finite prime set

Let S be ANY finite set of primes greater than five. It need not consist
of actual exceptional primes. Let H(S) be the least set containing
{2,3,5} union S and closed under taking prime divisors of rho(p):

$$H_0=\{2,3,5\}\cup S,\qquad
H_{r+1}=H_r\cup\bigcup_{p\in H_r}\operatorname{Supp}(\rho(p)),\qquad
H(S)=\bigcup_{r\ge0}H_r.\tag{OSE1}$$

Here Supp(a) is the prime support of a positive integer, with Supp(1)
empty. Write t(S)=|H(S)| and M(S)=product_(p in H(S)) p.

**Lemma OSE1.** This procedure terminates, and every member of H(S) is
at most max({5} union S). For p>5 every prime divisor of rho(p) is
STRICTLY smaller than p. H(S) is effectively computable from S using
integer factorization and the original recurrence.

**Proof.** The rank divides one of the even numbers p-1,p+1. An odd
prime divisor of either number is at most (p+1)/2<p; the possible prime
two is smaller too. At two, three and five, the displayed small ranks
add only primes already in {2,3,5}. Thus no new prime exceeds the initial
maximum, and a strictly increasing chain of these finite subsets must
terminate. At termination it is closed, and induction shows it is
contained in every closed set containing H_0. Ranks can be computed by
iterating the invertible Fibonacci pair recurrence modulo p, or by
removing prime factors from p-(5/p) and testing actual Fibonacci zeros.
The same rank-closure operation occurs in Ribenboim (3.8). Its use below
is to control original odd-depth support of powerful values.

### OSE.2 The original odd-depth support controls both index and square class

For every n>=1 define the finite set of external odd-depth divisors

$$U(n)=\{p>5\text{ prime}:p\mid F_n,\ p\nmid n,\ h_p\text{ odd}\}.$$

The word external means only the explicit condition p not dividing n.
Let d(n)=product_(p|F_n, v_p(F_n) odd) p be the positive squarefree
kernel; F_n=d(n)*y^2 for a positive integer y.

**Theorem OSE2.** If U(n) is contained in S, then

$$\boxed{\operatorname{Supp}(n)\subseteq H(S),\qquad
             d(n)\mid M(S).}\tag{OSE2}$$

**Proof.** Suppose n has a prime divisor outside H(S), and choose the
largest such divisor ell. It is at least seven. Every prime p|F_ell
has rho(p)=ell and p>ell, by the prior prime-index argument FPD3/ZBD1.
If p divided n, maximality of ell among the OUTSIDE primes would give
p in H(S). Closure would then imply ell in H(S), a contradiction.
Thus every prime p|F_ell is prime to n. The valuation formula gives
v_p(F_n)=h_p=v_p(F_ell), since ell divides n.

The nonsquare F_ell has some prime divisor p with odd valuation. For
this p the preceding equalities show p in U(n), hence p in S and H(S).
Closure again implies ell=rho(p) in H(S), the required contradiction.
This proves the first inclusion. Notice that ell need not be the largest
prime of n; it is the largest one OUTSIDE the specified closed set.
This is the additional descent step not supplied by merely taking P+(n).

If q divides d(n) but q is outside H(S), then q>5 and, by the first
inclusion, q does not divide n. Since q|F_n, its odd value exponent is
h_q+v_q(n)=h_q. Therefore q in U(n) subset S subset H(S), another
contradiction. The kernel is squarefree, so its support inclusion is
exactly the asserted divisibility. No power-basis index is used.

### OSE.3 A cardinality bound for all powerful values supported by S

For n>=1 put

$$T(n)=\{p>5\text{ prime}:p\mid F_n,\ h_p\ge3\text{ odd}\},$$

$$\mathcal P(S)=\{n\ge1:F_n\text{ powerful and }T(n)\subseteq S\}.$$

T(n) may include primes dividing n; this only strengthens its containing
U(n) in the powerful case. S may be an arbitrary finite prime set, so
membership in P(S) does not assume a classification of all WSS primes.

**Theorem OSE3.** For every finite S as above,

$$\boxed{n\in\mathcal P(S)\Longrightarrow
\operatorname{Supp}(n)\subseteq H(S),\quad d(n)\mid M(S),}\tag{OSE3}$$

$$\boxed{\#\mathcal P(S)\le 2^{t(S)}-4.}\tag{OSE4}$$

In particular P(S) is finite, without abc, a density premise, or an
assumption about the number of depth-two WSS primes.

**Proof.** If p in U(n) and F_n is powerful, then p does not divide n,
so v_p(F_n)=h_p is odd and at least two. Hence h_p>=3 and p in T(n).
Thus U(n) subset T(n) subset S, and OSE2 proves OSE3.

There are exactly 2^t squarefree divisors of M(S). Eight divide 30,
since {2,3,5} subset H(S). A powerful F_n with d(n)|30 must have a
five-smooth index: otherwise take its largest index-prime ell>=7.
A prime divisor p of odd exponent in F_ell exists by nonsquareness;
p>ell and p does not divide n, so its same odd exponent in F_n puts
p>5 in d(n), a contradiction. The prior five-smooth classification
therefore forces n in E_0. Conversely these four indices are powerful
and have T(n) empty, so all four belong to P(S).

For every remaining squarefree divisor d of M(S), d does not divide 30
and in particular d>2. The classical full square-class theorem gives at
most one positive n with d(n)=d, before even imposing powerfulness or
T(n) subset S. Thus there are at most 2^t-8 further indices. Adding the
four classical ones proves OSE4. The collisions {1,2,12} and {3,6} are
handled by the explicit E_0 count; they are not silently treated as
singleton square classes.

**Finite-escape corollary.** Among more than 2^t(S)-4 distinct powerful
Fibonacci INDICES, at least one value has a prime p outside S with odd
original h_p>=3. In particular infinitely many powerful Fibonacci values
would force infinitely many such odd-depth super-WSS primes.

**Proof.** Otherwise all those indices would be in P(S), contradicting
OSE4. If the global odd-super-depth set were finite, take it for S.
The number of indices is then bounded by OSE4. Distinct positive values
and indices differ only at F_1=F_2, so infinitude is equivalent.

**Conditional consequence, with the hypothesis displayed.** If
S_odd={p>5:h_p>=3 odd} is finite, then the TOTAL set of powerful Fibonacci
indices has size at most 2^|H(S_odd)|-4. This permits any number of WSS
primes with even depth, including h=2 or h=4. It does not prove that
S_odd is finite or that any WSS prime exists. When S_odd is empty the
classification reduces to E_0, the already-known ZBD/FPD consequence.

### OSE.4 Effective finite reduction and a fixed family of elliptic curves

For a specified finite S, OSE3 reduces ALL candidates for P(S) to

$$F_n=d y^2,\qquad d\mid M(S),\quad d\text{ squarefree},\quad n,y\ge1.$$

Ribenboim's cited (3.7) gives an effectively computable N(d) for this
fixed-d equation. Consequently

$$N_S=\max_{d\mid M(S)}N(d)$$

is a valid finite search bound. Factoring the finitely many F_n up to
N_S and checking the original h_p computes P(S). The existence of these
classical effective bounds is used; no numerical N_S or complete search
is reported in this continuation. A scan with a chosen cutoff is not a
substitute for N_S. The kernel uniqueness bound OSE4 does not itself
provide a height bound.

There is also an exact geometric realization of the candidate equations.
Put epsilon=(-1)^n. The ORIGINAL golden Pell relation gives
L_n^2=5d^2 y^4+4epsilon, so

$$\boxed{(X,Y)=(5d^2y^2,\ 5d^2yL_n)
\in E_{d,\epsilon}:Y^2=X^3+20\epsilon d^2X.}\tag{OSE5}$$

The discriminant is -64*(20epsilon*d^2)^3, nonzero for d>0.
The map follows from the exact polynomial identity

$$(5d^2yz)^2-(5d^2y^2)^3-20\epsilon d^2(5d^2y^2)
=25d^4y^2(z^2-5d^2y^4-4\epsilon).$$

There are only 2^(t+1) specified curves. For recovering P(S), retain
X/(5d)=F_n, X/(5d^2)=y^2 with y positive, Y/(5d^2y)=L_n positive,
epsilon=(-1)^n, powerfulness, and the original-depth support test.
Arbitrary rational or integral points without these filters are not
WSS witnesses. Siegel's classical theorem independently gives finiteness
of the integral points on each curve, but the sharper OSE4 uses the
full square-class uniqueness theorem and no numerical rank calculation.

### OSE.5 Two disjoint exact-rank channels and their odd-depth budget

For a prime ell>=7 keep the two ACTUAL integers F_ell and L_ell.
Their prime supports are disjoint. For p|F_ell and q|L_ell respectively,

$$\rho(p)=\ell,\quad\pi(p)=4\ell,\quad p\equiv1\pmod4,$$

$$\rho(q)=\pi(q)=2\ell,\quad(5/q)=1,$$

and the factor exponents are their original h_p,h_q. Supports for
all different ell, including between the two channels, are disjoint.

**Proof.** Exact ranks and prime-to-index valuations are the prior
FPD/PH block results. At an odd zero rank ell, the Fibonacci matrix
Q^ell is scalar aI with a^2=-1 modulo p. Hence its scalar order is four,
p=1 modulo four, and its pair period is 4ell. For q|L_ell, the norm
identity L_ell^2-5F_ell^2=-4 gives (5/q)=1, and the matrix trace-zero
identity gives Q^(2ell)=I; its zero rank is already 2ell. Finally the
products F_ell*L_ell=F_(2ell) are pairwise coprime for distinct prime ell,
because gcd(F_(2ell),F_(2ell'))=F_2=1.

The classical Fibonacci and Lucas square classifications ensure an
odd-exponent prime in EACH channel. Each witness therefore has either
h=1 or odd h>=3. Let N_1(X) and N_o(X) count rational primes p<=X with
rho(p) equal to ell or 2ell for some prime ell>=7, and respectively
h_p=1 or odd h_p>=3. Let Pi(Y) count ordinary rational primes <=Y and
phi=(1+sqrt(5))/2. For real Y>=7,

$$\boxed{N_1(\phi^Y)+N_o(\phi^Y)\ge2(\operatorname{Pi}(Y)-3).}\tag{OSE6}$$

**Proof.** Choose an odd-exponent factor from each of the two channels
at every prime ell<=Y. All chosen primes are distinct and smaller than
phi^ell, by the original Binet formulas. Their original depths put each
in exactly one of the two displayed counts. There are Pi(Y)-3 indices.
No comparison prime outside the actual Fibonacci/Lucas supports is used.

Thus, by the classical prime number theorem,

$$\liminf_{X\to\infty}
\frac{(N_1(X)+N_o(X))\log\log X}{\log X}\ge\frac2{\log\phi}.\tag{OSE7}$$

If N_o(X)=o(log(X)/log(log(X))), the same lower bound holds for N_1
alone. This is a CONDITIONAL non-WSS conclusion. Applied separately,
each channel has constant 1/log(phi): one locates pair period 4ell and
p=1 modulo four, the other split primes with period 2ell. The older
PBC.4 already proves the Fibonacci-channel partition and a conditional
order-of-growth bound; those statements are credited, not recounted.
OSE6 records both disjoint channels, their original odd-depth alternative,
and the explicit exponential scale together.

For a residue refinement requiring only the elementary mod-eight and
mod-four recurrences: if ell=5 or7 modulo12, F_ell=5 modulo8, so one
odd-depth factor p is five modulo eight (all its factors are one modulo
four). If ell=5 or11 modulo12, L_ell=3 modulo4, so one odd-depth factor
q is three modulo four. Neither observation distinguishes depth one
from odd depth at least three by itself.

### OSE.6 Formalization targets and remaining arithmetic obligation

The local proof work is kept separate from the user's concurrent Lean
files. The proposed theorem order for later formalization is:

1. Finite rank closure: strict descent above the fixed small-prime set,
   stabilization, leastness and support closure.
2. Largest-prime-OUTSIDE-closure descent OSE2, using the actual Fibonacci
   rank, valuation and prime-index nonsquare inputs.
3. Powerful U(n) subset T(n), squarefree-kernel support, then the finite
   set injection proving the exact bound OSE4 with its eight base classes.
4. OSE5 as a coordinate polynomial identity plus explicit arithmetic
   filters. For OSE6 use finite disjoint supports before any asymptotics.

The full square-class theorem is a genuine classical prerequisite for
OSE4, stronger than a determinant identity or the prime-power order
lemma. It has been used in prior repository written theory; no claim
that it is already Lean-certified follows. Without that prerequisite,
OSE2/OSE3's support conclusions and the explicit curve reduction remain,
and Siegel still supplies qualitative finiteness. No formal axiom or
new Lean wrapper is inserted in this pass.

The independent WSS question still requires deciding an original h_p
or excluding an actual unbounded exceptional family. OSE does not prove
N_o is small, construct a nonclassical powerful Fibonacci value, supply
a WSS prime, or exclude the unrestricted P^2 Q^3 ternary-block pattern.
It gives a finite-support obstruction and a cardinality theorem on the
original odd-super-depth set. Finiteness of that set remains a displayed
hypothesis only where explicitly stated.

### OSE.7 Primary literature and scope of the verification

* P. Ribenboim, *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly
  43(1) (2005), 3-14. Sections (3.4)-(3.5), printed page 8, give the
  square classes; (3.7)-(3.8), page 9, give fixed-square-class effectiveness
  and the earlier rank-closure algorithm. The square-class result is
  attributed there to *Square classes of Fibonacci and Lucas numbers*,
  Portugaliae Mathematica 46(2) (1989), 159-175.
  https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf
  The parsed passages were read. Web screenshot requests for pages 8-9
  failed, as did the container download, so no visual-page check is claimed.
* Y. Bugeaud, M. Mignotte and S. Siksek, *Classical and modular approaches
  to exponential Diophantine equations I. Fibonacci and Lucas perfect
  powers*, Annals of Mathematics 163 (2006), 969-1018,
  DOI 10.4007/annals.2006.163.969.
  https://annals.math.princeton.edu/2006/163-3/p05
  The publisher abstract corroborates the square exceptions. It is not
  substituted for the stronger fixed-square-class uniqueness theorem.
* N. Fellini and M. Ram Murty, *Wieferich primes in number fields and the
  conjectures of Ankeny-Artin-Chowla and Mordell*, arXiv:2508.08472v2,
  Theorems 1.3-1.4 and 4.3:
  https://arxiv.org/html/2508.08472v2
  The paper already proves non-Wieferich infinitude and a log X/log log X
  lower bound under finiteness of ALL base-alpha super-Wieferich primes,
  and recalls Siegel's theorem. OSE does not claim that general mechanism
  as new. Its hypothesis selects original odd Fibonacci depths and its
  finite-support cardinality statement concerns powerful Fibonacci indices.
  No abc hypothesis, random quotient model or unrestricted Chebotarev
  prime is inserted into the displayed proofs.

The rank-closure operation, square-class theorem, primitive-prime facts,
valuation theory and fixed-d effectiveness are classical. ZBD/PBC's
odd-super witness and Fibonacci-channel count were already in the
repository. The additional finite-support descent and explicit counting
bound are proved here with those prerequisites, without claiming global
priority or an externally stated open problem solved.

`verify_ose.py` is an exact finite diagnostic, not a proof of a finite
super-depth hypothesis. It checks actual F_n for 1<=n<=60, rank closures,
original versus multiplier depth, and both prescribed prime-index channels
through ell=43. Integer factorizations are proposed by SymPy and every
factor is independently certified by trial division. It also checks the
elliptic map as a polynomial identity and the exceptional square classes
in the tested range. No new WSS sample or complete integral-point solver
is reported. No Lean/Scribe compilation or independent-model review is
claimed; the unrestricted arguments are the ordinary proofs above.
