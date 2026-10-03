# A marked same-source boundary for higher-core continuation

This note gives an exact conditional interface for arbitrary SHALLOW
singleton-outside originals, a finite convex weighting problem, and the
additional joint data required by multiple-outside deletions. The
[clipped-source construction](751-clipped-common-sources-release-core-and-outside-heights.md)
supplies a feasible weighting on a canonical supported subset for every
shallow singleton-outside family; arbitrary chosen smaller supports need
not share that property.
All arguments are ordinary finite mathematics, not Lean verification.

## 1. Exact same-source probabilities and the higher-core coefficient

Fix L0=315=3^2*5*7 and outside primes P={11,13,17,19,23}. Let X be an
actual supported subset of old315 survivors. Every actual shallow
outside-bearing original in the current source uses exactly one outside
prime, to exponent1, with an old divisor d|315. Original phases are fixed
once globally, and numerical moduli are distinct.

After the actual or auxiliary pure p-root exclusion, put

    A_p(x)={live p-roots avoiding every actual p*d original over x},
    r_p(x)=|A_p(x)|, R(x)=product_p r_p(x),
    Omega={x in X:R(x)>0}.

Assume Omega is nonempty. If it is empty, this chosen supported source
cannot be used; that does not imply that the original arithmetic family
covers the full carrier.

For any probability u on Omega choose one actual source

    mu_u(x,y)=u(x)/R(x), y in product_p A_p(x).

Thus u is the old315 marginal and the source is conditionally uniform on
its ACTUAL remaining outside fibre. It avoids every existing original.
Its exact Haar domination on the shallow carrier is

    mu_u<=D(u) Haar, D(u)=315 product_p p * max_x u(x)/R(x).       (M1)

The original uniform actual source is the special choice u(x)=R(x)/sum R.
This reweighting ansatz allows the actual data to select u once, before all
queries and higher-core originals; no query-specific source is substituted.

For old d|315, queried outside subset J, old phase a and roots t, define

    f_(d,J,a,t)(x)
      =1_(x=a mod d) product_(p in J) 1_(t_p in A_p(x))/r_p(x),
    m_(d,J)(u)=max_(a,t) sum_x u(x) f_(d,J,a,t)(x).              (M2)

This is the exact maximum probability of that numerical query cylinder.
For a nonempty core-prime subset S, let beta_S(u) be the sum of m_(d,J)
over all J and all d saturated at9,5,7 for the primes3,5,7 in S.
Each slot has its own free query phase, so these maxima are simultaneously
attainable as one marked query on this SAME source. This does not assert
that a union of higher-core original events attains the sum of their masses.

Write Sat(d)={3:9|d} union {5:5|d} union {7:7|d} and

    kappa(d)=product_(p in Sat(d))(1+1/(p-1))-1.

Then exactly

    lambda(u)=sum_(nonempty S) beta_S(u) product_(p in S)1/(p-1)
             =sum_(d|315,J subset P) kappa(d)m_(d,J)(u).         (M3)

Only d=1 and3 have kappa(d)=0. Equation(M3) follows by expanding the finite
product and interchanging finite nonnegative sums; it does not multiply
separately chosen source extrema.

For any additional finite distinct-modulus family with at least one
3/5/7 exponent above(2,1,1), outside exponents at most1 and no other primes,
uniformly extend the selected source in its higher core digits. For a fixed
positive excess-exponent vector on S, every original projects to a distinct
shallow numerical slot saturated on S. Its probability is the projected
cylinder probability times product p^(-excess). Sum the actual original
masses and then the geometric tails. This gives debit at most lambda(u).
Consequently

    lambda(u)<1 ==> Haar(actual final survivors)>=(1-lambda(u))/D(u)>0. (M4)

The new high-core originals may involve MULTIPLE outside primes. The
singleton-outside assumption concerns the shallow source before this lift.
Every new phase is arbitrary and globally fixed. The [71-original example](../700-749/747-an-actual-marked-boundary-restores-a-core-height-continuation.md)
is one verified case of(M4), with its uniform conditional u and lambda
101900963/147044288. The general implication(M4) separates source
construction from the subsequent high-core deletion estimate.

## 2. Four outside phase optimizations disappear for every singleton source

For p>=13 there are at most eleven nonpure shallow labels p*d, d|315,d>1.
They use at most eleven live roots globally. There are p-1>=12 live roots.
Therefore some root t_p^* is untouched over EVERY old point x, regardless
of the original phases, missing labels, or old source weights.

In(M2), choose t_p=t_p^* for all queried p>=13. These choices simultaneously
replace their membership indicators by1 at every x, and no other choice
can increase a nonnegative sum. Thus

    m_(d,J)(u)=max_(a,t11 if11 in J)
       sum_(x=a mod d) [u(x)/product_(p in J)r_p(x)]
            *1_(t11 in A_11(x)) if11 in J,                     (M5)

with the last indicator omitted otherwise. This is an equality. It is not
specific to the special root12 used in the 71-original example.

Accordingly the row counts r_p(x), the weights u(x), and the common-root
membership masks for11 suffice for these free marked mean queries. At11
the eleven original labels can use all ten live roots; its masks cannot
be dropped. The declared output is m_(d,J), beta_S and lambda: SUPREMA
over free query phases. It does NOT recover the individual numerator or
probability for a specified phase t at p>=13, and it does not support
adding arbitrary fixed-phase original deletions without restoring their
membership data. Thus the full-root-mask interface used for concrete C
responses remains necessary even where the maximization interface can
omit four masks. Arbitrary convex tests of whole marked loads also require
a separate sufficiency argument.

The shallow exponent assumption is essential. With higher outside powers,
there may be eleven mixed labels per depth, so this pigeonhole argument
does not leave a common first root. One must then retain the actual nested
prefix-cylinder memberships and masses. Similarly it does not apply to
an already unrestricted357 old carrier with arbitrarily many old cofactors.

## 3. Source weighting is a finite convex feasibility problem

For the fixed actual root incidence data, every f in(M2) is a known
nonnegative rational vector. Thus lambda(u) is convex and piecewise linear.
A certificate of a higher-core bridge consists of rational u and v_(d,J)
such that

    u>=0, sum u=1,
    v_(d,J)>=sum_x u(x)f_(d,J,a,t)(x) for EVERY relevant(a,t),
    sum_(d,J)kappa(d)v_(d,J)<1.                               (M6)

Numerical optimization can propose u, but an exact evaluation of(M5)
certifies all inequalities and computes the actual domination(M1). No
optimality claim is needed. There are320 nonzero-coefficient(d,J) slots;
effective old cylinders and the at-most-ten queried11 roots supply finite
constraints, without enumerating independent roots at13,17,19,23.

There is also an exact obstruction to THIS weighting/first-moment method.
Choose nonnegative numbers gamma_(d,J,a,t), with

    sum_(a,t) gamma_(d,J,a,t)=kappa(d) for each(d,J),
    sum_(d,J,a,t) gamma_(d,J,a,t) f_(d,J,a,t)(x)>=1
                                                    for every x in Omega. (M7)

For any u, a weighted average of tests is below the corresponding maximum;
integrating(M7) gives lambda(u)>=1. Conversely, finite minimax or linear
programming duality gives

    min_u lambda(u)
      =max_gamma min_x sum gamma_(d,J,a,t)f_(d,J,a,t)(x),

where gamma has the stated per-slot masses. The finite simplices are
compact and the payoff is bilinear. Consequently absence of a strict
certificate(M6) has a dual certificate(M7), with the usual equality case
included. This is an application of finite minimax, not a new minimax claim.

Such a dual certificate rules out only row reweighting with the declared
uniform conditional fibres and the first-moment higher-core debit. It
does not construct a covering, rule out other conditional source laws,
or rule out an argument using overlaps between original deletion events.
The existence of a primal certificate on the 71-family does not supply
the quantifier 'for every actual shallow family, there exists such a u'.
That uniform statement remains unresolved here.

## 4. An actual singleton pair shows why the11 mask matters

Use the canonical first-shape old315 head with all five mixed7 originals
redundant with pure7=0; its old survivor support has102 points. At outside11
exclude pure root0. For d=(3,5,9,15,45), use old phase2 mod d and outside
root1,2,3,4,5 respectively. The other six labels are

|Old d|Old phase|Family A11 root|Family B11 root|
|---|---:|---:|---:|
|7|2|6|6|
|21|2|7|7|
|35|2|8|8|
|63|47|6|8|
|105|47|7|9|
|315|47|8|10|

Each line specifies one CRT phase for numerical modulus11*d. These and
the eleven old head originals and pure11 give23 distinct odd nonunit
moduli in each family. The first three private old cylinders have7 root2,
the last three have7 root5, so they never overlap. Within a group their
outside roots are distinct and disjoint from1,...,5. It follows, and the
literal CRT checker verifies, that r_11(x) is IDENTICAL in both families
at all102 old points.

Take the same allowed prior weighting in both families: old45 marginal
concentrated at2, with equal mass on all six live7 roots, and a uniform
live11 root. After the actual singleton deletions, both sources have24
equally weighted cells. Four old7 roots retain five11 roots each; old7
roots2 and5 retain two each. Thus the entire old marginal also agrees.

Family A has common untouched11 roots9 and10. Family B does not: its best
common query root occurs on five of the six old7 rows. Hence the numerical
9*11 query maximum is6/24 in A and5/24 in B. Including every saturated3
old slot9,45,63,315 and both outside subsets gives

    beta_3(A)=3, beta_3(B)=35/12.

Counts and the current source weighting agree, but a later marked-query
response differs. This is a failure of that coarse representation, not a
covering example or evidence that(M6) must fail on every source. Adding
the independent unused outside primes13,17,19,23 preserves the difference,
scaling both full marked means by product p/(p-1).

## 5. Multiple-outside originals require joint cylinder data

For a general actual finite source, retain unnormalized joint marginals

    F_x(J,t)=sum_(y:y_J=t) mu(x,y).

The singleton factorization is one special representation of this table.
For an actual deletion with old condition x=a mod d and outside cylinder
y_J=t, a requested K-marginal has the exact update

    F'_x(K,s)=F_x(K,s)
       -1_(x=a mod d)*1_(s,t compatible on K intersect J)
                       *F_x(K union J,s union t).              (M8)

Total mass is sum_x F_x(empty); normalization follows only afterwards.
This is a linear unnormalized boundary update. It shows exactly which
additional relation is needed: the joint scope K union J. A declared
collection of scopes supports all these updates if it is closed under
the required unions and retains consistent joint assignments. Arbitrary
future scopes may force the full joint table; selected interfaces can
need much less. For higher powers, assignments are compatible prefixes
and union means the common refinement at the larger requested depth.

Even all conditional SINGLE-coordinate marginals need not suffice.
A literal distinct-modulus example uses old315 rows2 and47, and a common
auxiliary supported prior with each11 and13 root in{1,2}. At old row2,
remove off-diagonal outside pairs with old labels7 and21. At old row47,
use labels35 and63 to remove off-diagonal pairs in family A, diagonal pairs
in family B. Every mixed modulus is its listed old label times11*13;
all four moduli are distinct and have globally fixed CRT phases.

Both conditional survivor sources have four cells, equal old marginals,
and the same full single-coordinate marginal table at each old point.
But the maximal9*11*13 query contains two cells in A and one in B. The
full saturated3 means on this declared source are15/2 and7. This example
uses the explicitly pruned two-root prior; it is not asserted to be the
unpruned full-live-root source of a prior theorem. It proves that the
general process interface needs joint marginals such as(M8), even after
row masses and all singleton marginals have been retained.

## 6. Verification and the uniform obligation

The [literal CRT consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_marked_boundary.py)
reconstructs both pairs from their actual numerical originals, checks all
query-slot maxima and compares the single-coordinate marginal tables.
It also checks(M8) after each of the four actual joint deletions in both
variants: every old row, every outside scope and every retained assignment
is compared with direct survivor enumeration. The
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_marked_boundary.json)
is checked against a complete replay; no inherited finite table is assumed.

For all eleven-slot singleton-outside shallow families, the
[clipped-source theorem](751-clipped-common-sources-release-core-and-outside-heights.md)
proves that one canonical supported subset admits(M6). This does not
guarantee feasibility on every arbitrarily chosen smaller support X.
A failed source ansatz or its dual on a fixed support is not an odd covering.
Higher outside powers require nested prefix memberships, as used in the
clipped-source proof. Already present core-shallow multiple-outside
originals require joint data such as(M8) and remain unresolved here.
The shallow untouched-root shortcut is not used beyond its domain.

All conclusions here are ordinary mathematics and exact finite arithmetic,
not new Lean verification. No unrestricted Erdős#7 result is claimed.
