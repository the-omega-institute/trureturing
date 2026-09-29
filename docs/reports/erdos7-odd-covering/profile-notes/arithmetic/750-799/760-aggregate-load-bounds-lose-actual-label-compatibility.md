# Aggregate load bounds do not suffice for the row envelope

The [all-colour certificate](758-one-row-mass-law-handles-all-outside-colours.md)
uses old-phase incidence information. The [thin-fibre bounds](759-one-actual-label-dictionary-localizes-thin-fibres.md)
control its largest local loads. The following exact obstruction shows
why retaining only total loads and those layer counts is insufficient.

There is a literal75-by5 integer load table satisfying both

```
sum_x h_j(x)=146 for every axis j,
0<=h_j(x)<=6 for every row and axis,
```

for which **every nonzero nonnegative row-mass vector fails the372-slot envelope**. A439-term rational dual proves the strict cost lower bound

```
44408103273659/44352000000000 > 1.
```

The table satisfies all the high-layer bounds `#{h>=10}<=1`, `#{h>=9}<=2`, `#{h>=8}<=3`, and `#{h>=7}<=4` with the stronger count zero. It nevertheless violates a necessary actual-label relation. Thus it is a counterexample to an **aggregate-load relaxation**, not to the actual phase problem and not to Erdős #7.

## 1. Fixed actual core and relaxed loads

Use the actual core originals

```
(3,0), (5,0), (7,0), (9,4), (15,11), (21,8),
(35,9), (45,1), (63,1), (105,59), (315,179).
```

Their full actual survivor set `X` in `Z/315Z` has75 points. At the five outside axes use minimum primes

```
P=(11,13,17,19,23).
```

The [literal input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_aggregate_load_obstruction_input.json) records every pair `(x,[h_0,...,h_4])`. This table is considered only as an abstract load assignment. Put

```
ell_j(x)=P_j-1-h_j(x)>0.
```

Let `D` be the eleven nonunit divisors of315. For the actual core rows,

```
sum_(d in D) max_(a mod d) #{x in X:x=a mod d}=146.
```

Every actual singleton old-phase assignment must therefore satisfy `sum_x h_j(x)<=146`. The relaxed table uses equality at all five axes and has no load above6.

## 2. The same372-slot envelope

For a nonnegative row-mass vector `u`, write

```
C_(d,J)(u)=max_(a mod d)
 sum_(x=a mod d) u_x / product_(j in J) ell_j(x),
c_(d,J)=kappa(d)+1_(|J|>=2),
kappa(d)=product_(p in Sat(d)) p/(p-1)-1,
Sat(d)={3:9|d} union {5:5|d} union {7:7|d}.
```

The robust cost is `R_*(u)=sum_(d,J)c_(d,J)C_(d,J)(u)`. There are372 nonzero coefficients. A successful envelope certificate would require

```
R_*(u)<sum_x u_x.
```

For the literal relaxed load table, the rational dual below excludes this inequality for every nonzero `u>=0`.

## 3. Exact finite dual certificate

For every slot and old query phase, choose nonnegative rational `gamma_(d,J,a)` such that

```
sum_a gamma_(d,J,a)=c_(d,J).
```

Since each maximum dominates a convex average of its phase values,

```
R_*(u)
 >=sum_x u_x score(x),
score(x)=sum_(d,J)
 gamma_(d,J,x mod d)/product_(j in J) ell_j(x).       (D1)
```

The literal file contains439 positive integer numerators `v_(d,J,a)`, with common convention

```
gamma_(d,J,a)=v_(d,J,a)/(48*10^9).
```

Every one of the372 slot budgets is exactly equal to `c_(d,J)`; no budget excess or numerical tolerance is used. Exact rational evaluation on all75 rows gives

```
min_x score(x)=44408103273659/44352000000000 > 1.     (D2)
```

Hence for every nonzero `u>=0`,

```
R_*(u)>=44408103273659/44352000000000 * sum_x u_x
       >sum_x u_x.
```

This is a complete finite Farkas-style obstruction to the envelope on the declared relaxed table. Solver optimality is not a premise: the literal rational budget and row inequalities suffice.

## 4. The relaxed table is not an actual singleton phase assignment

For each actual label `d`, one old phase is chosen, so its contribution to `sum_x h_j(x)` is at most its maximal cylinder size on `X`. Since those eleven maxima sum to146, actual equality146 forces **every** label to attain its own maximum.

At label9, the unique maximizing old phase is7; its cylinder has23 points. Thus any actual axis with total load146 must hit row16 through this label, because `16=7 mod9`. The relaxed table instead has

```
h_0(16)=0.
```

This is already an exact contradiction.

The same obstruction has a direct integer support-cut form. For any actual old singleton phase assignment,

```
sum_(x in X, x!=16) h_0(x)
 <=sum_(d in D) max_(a mod d)
      #{x in X, x!=16 : x=a mod d}
 =145.                                               (D3)
```

The literal table gives146 on the left. The checker independently computes every maximization in (D3); its conclusion does not rely on the preceding equality argument.

Thus the counterexample is expressly **outside** the actual-label feasible set. It proves that the aggregate146 budget together with all four high-layer bounds cannot by themselves imply universal envelope feasibility. Even without any thin high-load row, the missing relation can be the requirement that all row loads come from the same eleven fixed congruence labels.

## 5. Exact verification and remaining boundary

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_aggregate_load_obstruction.py)
reads only the pinned literal loads and dual. It reconstructs all75 core
rows, verifies every load total and range, derives the372 coefficients
from saturation, checks all439 positive rational entries and372 exact
budget equalities, and computes every row score and the145 support cut.
No solver, solver optimum, or numerical tolerance is a premise. The
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_aggregate_load_obstruction.json)
includes all75 scores and the nonrealizability witness, and must equal
fresh full recomputation.

An independent checker uses one integer denominator per old row, with
complementary outside products in its numerator. All75 scores and372
budgets agree. Separate old-cylinder histograms give label maxima

    (38,26,16,23,15,9,5,6,4,3,1)

in increasing nonunit-divisor order; deleting row16 changes only the
fourth maximum,23 to22. This independently verifies both146 and145.

The exact dual excludes every nonzero row-mass law only on the declared
RELAXED load table. The support cut proves that table cannot arise from
actual old singleton phases. No actual old-phase dictionary with an
infeasible372-slot envelope is supplied here, and no actual final
survivor set excluding every old-row law is supplied. These are separate
stronger questions. All finite checks are ordinary exact computation,
not Lean verification; unrestricted Erdős #7 remains unresolved.
