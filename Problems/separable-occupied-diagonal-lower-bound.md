---
slug: separable-occupied-diagonal-lower-bound
bibkey: doughertyblissgalvanpolleyshuster2026enumerating
doi: null
url: https://arxiv.org/abs/2608.27583v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/Separable/OccupiedComparison.actual_occupation_subsolution_comparison
---

# Actual separable occupied-diagonal lower bound

## Problem

For each positive length n, let M_n(e) count actual permutations avoiding
2413 and 3142, with no proper direct cut, and having at least one position
j with j-sigma(j)=e. Count each permutation once. Put b=sqrt(2)-1,
rho=b squared, a=1-b and O(e)=(2/a)sum_(n>=1)rho^n M_n(e).
The target is a uniform positive constant c_* such that, for every integer e,

$$
O(e)\ge\frac{c_*}{\sqrt{2+|e|}\log(2+|e|)}.
$$

The empty permutation is excluded and the singleton is retained. The raw
mass C=(a/2)O is distinct from the normalized occupation. This is an
occupation obligation motivated by Dougherty-Bliss, Galvan, Polley and
Shuster, *Enumerating separable derangements*, arXiv:2608.27583v1,
Definitions 2, 5, 6 and equations (2)-(4), rather than a settlement of the
paper's full Conjecture 15.
[Issue 15063](https://github.com/the-omega-institute/trureturing/issues/15063)
registers the exact target.

## Motivation

The actual comparison theorem proves summability of the literal shape
weights, their total b, and critical kernel mass one half without extra
premises. It also proves convergence of every actual occupied-count series
and the box 0<=C(e)<=a/2. It proves reflection and the literal actual
fixed-point equation, then bounds every vanishing nonnegative subsolution
in that box by the actual occupied mass. The strict maximum argument uses
the singleton loss weight. No recurrence-defined replacement class is used.

The critical convergence proof applies the native Schroder recurrence to
the actual cardinalities. Nonnegative partial sums are bounded by b using
a triangular convolution contained in the corresponding square. The Cauchy
product then gives T=rho+rho*T+T squared. At rho=1-2*b this is
(T-b) squared=0, so T=b; retaining the singleton correction gives kernel
mass b+rho/2=1/2.

## Gap

The literal actual occupation equation and its finite minimum-cut event
bridge are proved for both orientations, all natural lengths
and every integer displacement. Write A(n,e) for the full occupied count,
J(s,n,e) for the orientation-s indecomposable occupied count, and D(s,n,e)
for the count with a proper orientation-s cut. Write U(n) and I(s,n) for
whole-class cardinalities. For 0<i<n, the direct recurrence summand is

$$
J(0,i,e)\bigl(U(n-i)-A(n-i,e)\bigr)+I(0,i)A(n-i,e),
$$

while the skew recurrence summand is

$$
J(1,i,e+n-i)U(n-i)+I(1,i)A(n-i,e-i).
$$

The sum of these respective summands over proper cuts is D(s,n,e). The
actual minimum-cut equivalence transports the literal position/value hit
predicate. Direct occupation is partitioned into left-hit/right-no-hit and
right-hit, retaining the intersection correction. Skew occupation is a union
of disjoint shifted events; the Fin bounds give a gap of two between their
possible displacement ranges. Every actual shape is counted once.

The actual hit fibers also satisfy A(n,e)=J(s,n,e)+D(s,n,e) for every
orientation, length and displacement. For n>=2 the native opposite-sign law
gives D(s,n,e)=J(1-s,n,e). At length one J(s,1,e) is one at e=0 and zero
elsewhere, with the genuine singleton retained in both orientations.

Inversion preserves avoidance and both proper-cut classes: a direct cut
keeps its size, while a skew cut of size i becomes a skew cut of size n-i.
It sends each hit displacement e to -e, so the actual indecomposable
occupied counts and C are even. Every weighted finite-recurrence summand
is nonnegative and bounded by twice the product of the corresponding shape
weights. Their convergent joint sum permits the positive-length
antidiagonal transport and interchange of the factor sums.

Let T be full occupied mass, P direct-decomposable occupied mass and
V(x)=x squared/(h+x). The transported direct recurrence and partition give
P=C(b-T)+(a/2)T and T=C+P. Hence T=2C-2V(C) and P=C-2V(C).
The skew indecomposable occupied mass is delta+P, where delta is rho at
zero and zero elsewhere. Substituting these identities into the transported
skew recurrence, reflecting e to -e and averaging yields the literal
occupation map. The delta terms select exactly length abs(e) for nonzero
e and vanish at zero; the retained singleton gives forcing(0)=rho.
Thus forall e, C(e)=occupationMap(C,e), with no extra equation premise.

The uniform power-kernel residual, integrated negative logarithmic residual,
quadratic convolution bound and symbolic finite-region forcing bound remain
needed to construct the positive global subsolution. Their Lean proofs and
the uniform lower bound remain open.

The actual convergence, finite events, reflection and fixed-point equation
are closed clauses of the comparison theorem. A closed production
registration still needs faithful reconstruction and audit of its complete
statement, including the unrestricted subsolution function and every
conclusion clause. No production Reg source or validated registration is
supplied. This unfinished audit is linked to issue 15063.

The singleton gives C(0)>=rho>0. The finite-support function w(0)=rho/2
and w(e)=0 for nonzero e lies in the comparison box, has finite positive
superlevel sets and satisfies w<=occupationMap(w). The closed comparison
therefore gives w<=C without an actual-equation premise. This positive
finite-support application supplies no uniform all-integer lower bound.

## Route

Construct a positive global subsolution for the literal occupation map in
the same mass box, with finite positive superlevel sets. Uniform exterior
residual estimates must dominate the quadratic loss; positive forcing on a
finite core then permits a single positive scale. The closed actual
fixed-point and comparison theorem supplies the final comparison. The
required global logarithmic subsolution remains open.

## Falsifier

Refuting the original bound requires showing that every positive proposed
constant has an integer displacement violating that bound. Failure of a
particular subsolution or residual estimate rejects that route alone.
A finite positive-support example does not establish the uniform target.
No refutation of the original target is supplied.

## Evidence

The mathematical source is
`D5/S1/Words/Patterns/Separable/OccupiedComparison.lean`, whose theorem
`actual_occupation_subsolution_comparison` has the twelve closed clauses
described above. Its axiom closure is propext, Classical.choice and
Quot.sound. The finite recurrence clauses use the actual minimum-cut
equivalence and preserve the singleton, intersection correction and skew
displacement shifts. The actual equation is proved before the arbitrary
subsolution comparison, with no equation antecedent.

## Triage

The retained theorem supplies unconditional actual critical-series facts,
the literal occupation fixed point and comparison for all subsolutions
satisfying the stated box and vanishing conditions. It establishes neither
the requested uniform lower bound nor Conjecture 15.

## ASSUMED-UNVERIFIED

The bounded source search does not establish worldwide originality or
first-publication priority. Ordinary analytic estimates using the paper's
cardinality asymptotic are not additional compiled suppliers in this unit.
The complete source-selection and dependent-family escape audit remains
unfinished, with its concrete missing evidence linked to issue 15063.
