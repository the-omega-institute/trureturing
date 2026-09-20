[Index](../../marked_head_profile.md) · [Adopted original mean costs](../065-128/109-the-mean-and-all-hinges-share-one-original-test.md) · [Complete AP11 blocks](../065-128/111-each-ap11-block-shares-its-mean-and-curvature.md) · [Single residual supports](../065-128/127-complete-tail-supports-restore-one-shared-convex-budget.md) · [Uniform first consumer](134-one-complete-cost-is-uniform-on-a-nonzero-k-neighborhood.md)

# Eleven original costs share one uniform K neighborhood

All eleven adopted mean-cost improvements from109 now have one
source-uniform weighted bound on134's actual K neighborhood:

    sum_(i in I) weight_i*Cost_i
       <=190508750298605283803831047688144136298511681
          /20583099791960494073490467262000000000000000
        =9.255590859692362... ,                    (PC1)

where

    I=(1,2,7,10,17,18,23,26,32,33,36),
    qK>=1-sigma, 0<=sigma<=1/10000,
    0<=rho<=1/100000, 0<=r<=1/520.                 (PC2)

The corresponding sum of the adopted face bounds is

    63433628286367055844084552403
      /6861147616447105476254760000
      =9.245337927769985... .                     (PC3)

Thus the complete uniform excess is0.010252931922375615.... Each
cost retains its own original test, but all costs use the same actual
source, the same q pair and the same seven-coordinate residual budget.
Both K orientations, every feasible beta distribution and every
infinite exponent tail remain included.

This is an ordinary continuum result with exact rational certificates.
It is a partial numerator consumer: the other30 linear costs, the11
quadratic costs, signed mass, square complement and full AP11/AP13
survival denominator are not replaced by(PC1). No new global K, Lean
verification or unrestricted Erdos #7 result is asserted.

## 1. The eleven targets agree with the adopted face consumer

Each selected index is an original109 cost, with its original positive
coefficient vector, original test identity and outside weight. In109's
certificate, these and only these eleven rows have status `enumerate`.
For each one, all three values agree exactly:

    uniform_cost_upper=accepted_cost_upper=improved_cost_bounds[i].

Consequently(PC3) is the actual adopted face contribution, not the
value of a weaker unadopted objective. All eleven original costs have
f_i(1)=0, so none requires a surviving-mass constant.

The original weights are1 for indices1,2,7,10;15/17 for17,18,23,26;
and13299/1360 for32,33,36. The certified individual bounds are:

| Index | Original cost | Uniform bound, decimal display |
| --- | --- | ---: |
|1|R17(0,1)|1.560083742559701|
|2|R17(0,2)|0.1643324105262483|
|7|R17(1,0)|1.7780056136771047|
|10|R17(2,0)|0.22176263511080846|
|17|R19(0,1)|1.2471888815444794|
|18|R19(0,2)|0.13139569040349128|
|23|R19(1,0)|1.4213924660355755|
|26|R19(2,0)|0.1773136979617285|
|32|R5(0,0)|0.2014207082920677|
|33|R5(0,1)|0.044588988782885745|
|36|R5(1,0)|0.05100240154139578|

Every authoritative value in the certificate is an exact rational.
The displays above are not substituted into any inequality.

## 2. Maximize one shared coordinate, after each cost's own head

Use134's source-uniform enlarged finite LP, corrected133 mean price,
uniform tail coefficients, fixed affine supports and common polygon.
For cost i, let F_(i,B,j)(q) be the right side of134(UN17), before
maximizing over its original head B, residual coordinate j and q.
Every component is evaluated using the same fixed rectangle radii.

For each cost choose a fixed support vector N_i before optimizing q.
Its complete coefficient in residual coordinate j is denoted
lambda_(i,B,j). If y is the actual shifted residual vector,

    sum_j y_j<=e(q)=rho0-g*(q5+q15).

For fixed heads, nonnegativity gives

    sum_j y_j*sum_i weight_i*lambda_(i,B_i,j)
       <=e(q)*max_j sum_i weight_i*lambda_(i,B_i,j).

At fixed q,j the heads are independent test choices, so

    max_(B_i)_i sum_i weight_i*F_(i,B_i,j)(q)
       =sum_i weight_i*max_B F_(i,B,j)(q).         (PC4)

This step does not identify different original tests. It also does not
give each cost its own coordinate j or its own residual allowance.
The source-uniform weighted upper is therefore

    max_(q in vertices(P)) max_(j=1..7)
                    sum_i weight_i*max_B F_(i,B,j)(q). (PC5)

Each fixed-head/fixed-coordinate expression is convex in q by134;
finite maxima and positive sums preserve convexity. Thus the same
vertex argument proves(PC5). No convexity in the continuous source
parameters is assumed.

The support candidates are(8,6,6,5),(10,10,10,10),(12,12,12,12).
For each cost each candidate is first maximized over its full original
head inventory, all seven coordinates and the whole polygon. The
candidate with least complete upper is then fixed for that cost.
Only afterwards are the selected fixed supports combined in(PC5).
This is a legal choice of fixed majorants; it is not claimed optimal
over every possible joint support vector.

All eleven selected vectors are(8,6,6,5). Their complete geometric
intercepts remain present. Every omitted original depth is deleted
from its own family exactly as in125/127, and the remainder after each
cut is summed as an infinite geometric series.

## 3. Exhaustive common-source result

The polygon vertices are

    (0,0), (0,9/19954), (9/19954,0).

At each vertex and for every cost, the checker includes all12500
base-head layouts and all10 independent positive-seven projection
choices. The total is

    11*3*12500*10=4125000

original branch evaluations, plus132 independent rational/integer
capacity-LP comparisons. One shared cache of the unweighted mean
reference and head prices serves all eleven coefficients. The other
head coefficients and all selected operators are evaluated separately
for each actual original cost.

The three complete weighted vertex maxima are respectively

    9.255590859692362...,
    9.251566172423700...,
    9.250181669446636... .

The first vertex attains the maximum in the omega coordinate. For this
particular rectangle the shared maximum equals the sum of the separate
cost maxima, so the numerical gain from sharing is exactly zero.
This equality is recorded; sharing the budget is still required for a
valid general combined interface. The maximizing outer-relaxation
allocation is not asserted realizable by an original congruence family.

The first cost is rechecked against134's complete certificate: every
vertex, head maximum, witness, rational check and fixed-support result
agrees exactly. All eleven face targets are checked against109 before
any off-face result is accepted.

## 4. Surviving mass has both a useful upper and lower direction

The selected eleven constants vanish, but subsequent consumers cannot
silently use face mass for a nonzero f(1). For a general cost, preserve
its exact term f(1)*S.106 supplies

    S<=53/360+5delta/9+rho0.                       (PC6)

This gives the correct upper payment for f(1)>=0. A negative signed
mass coefficient, or a survival denominator with positive S, needs a
lower bound instead. The same source data give

    S>=53/360-101delta/180+rho
      >=53/360-101delta/180.                      (PC7)

Here rho is the actual residual, not a newly allocated budget.

To prove(PC7), write the carrier retained density as
w_l=1-t_l/5, with face values w*=(1,4/5,4/5,4/5,4/5). From106,

    ||n-n*||1<=delta/2,
    n0*=1/36, sum_(l!=0)n_l*=2/9,
    w0>=1-2delta/5,
    w_l>=4/5-delta/5 for l!=0,
    0<=w_l<=1.

It follows that

    sum_l w_l*n_l-sum_l w_l* *n_l*
       >=-delta/2-(2delta/5)/36-(delta/5)*(2/9)
       =-5delta/9.

The complete cap quantity in106 is

    R=Dmax/18+h/4+max(h0,h1)/4+max_l eta_l/4+1/72.

Throughout delta<=2/27, h1>h0, h1<=1/3 and max eta_l<=1/9, so
those last two varying terms do not exceed their face values.
Dmax<=3/4+delta/4 and h<=1/2+delta/18 each increase R by at most
delta/72. Hence R-R*<=delta/36. Finally

    S0=sum_l w_l*n_l-R/5,
    S=S0+rho

prove(PC7). This is a continuum source inequality using106, not an
inference from the finite cost enumeration. It includes the entire
beta face because only n0* and the complementary total were used.

## 5. What remains for the complete AP consumer

111's four original AP11 blocks have positive hinge vectors, so134's
same-head source-uniform operator applies to them with zero f(1).
They are separate original tests and require their own complete
bounds; none is silently replaced by a numerator cost in(PC1).

Off the face,111's exact infinite-count regrouping retains the form

    R_tail<=H1/7986+S/87846,

where H1 uniformly bounds the complete threshold-one cost of every
remaining original block. The full lower denominator requires

    d>=S-U4/6-(sum_(e=0..3)B_e+R_tail)/7.         (PC8)

Thus the four block bounds B_e, the independent AP13 h4 bound U4,
the complete remaining-block H1 bound and correctly directed actual
mass must still be supplied together. Equations(PC6)--(PC7) provide
the mass directions; this result does not claim the remaining
numerical substitutions in(PC8).

For the numerator, the other30 linear-cost bounds must retain their
adopted controlling arguments. The41 linear-growth inventory contains
39 primitive vectors, but blindly extending every mean-LP vector does
not preserve the best face comparison:109 already records fixed-head
obstructions for30 rows. In particular indices0 and16 use other
adopted bounds. The11 quadratic objectives and complete square
complement also remain independent obligations. The local contribution
(PC1) can be substituted only alongside valid bounds for those terms.

[uniform_mean_cost_portfolio.py](../../frontier/comparison-bounds/uniform_mean_cost_portfolio.py)
and its
[certificate](../../certificates/source_norms/comparison-bounds/uniform_mean_cost_portfolio.json)
retain the full per-cost and shared-coordinate results.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/uniform_mean_cost_portfolio.py --check
```
