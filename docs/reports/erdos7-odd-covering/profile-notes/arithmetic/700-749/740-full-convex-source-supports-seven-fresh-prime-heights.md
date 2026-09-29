# Seven arbitrary-height fresh directions using pair and triple convex penalties

Let L0=315*11*13*17*19*23. Every finite family of pairwise distinct
odd numerical moduli greater than1 dividing

    L0*product_(i=1..7)q_i^E_i

leaves uncovered Haar density at least

    129998639766928635509/54872873440166678177736000 > 1/500000, (T1)

provided the fresh primes are distinct, outside L0, and ordered with

    (q1,...,q7)>=(29,31,37,41,43,47,53)

coordinatewise. Each E_i is arbitrary but finite and nonnegative.
Original phases are arbitrary but fixed once for the entire family.
The old exponent limits v3<=2 and all other old exponents<=1 persist.
This is an ordinary mathematical proof with an exact full-domain finite
enclosure, not a new Lean verification or unrestricted Erdos #7.

## 1. One actual source and127 finite-height fields

Use the existing actual uniform old survivor source mu with

    Haar(E23)>=104726/6084351.

The [conditioned convex-source result](736-a-common-conditioned-convex-law-sharpens-the-same-source.md) supplies the single17-atom law Y
such that every complete old divisor query L obeys

    E_mu h(L)<=E h(Y)

for every increasing convex h. Its support is

    {8,10,12,16,20,24,32,40,48,64,80,96,128,160,192,256,384}.

For each nonempty fresh support J, retain the actual full exponent tuple
and old cofactor and form the finite geometric average of complete old
queries with constant-one padding:

    C_J=sum_e alpha_(J,e)L_(J,e)+(1-sum_e alpha_(J,e)),
    alpha_(J,e)=product_(j in J)(q_j-1)/q_j^e_j.

The total weight of the finite exponent rectangle is at most1.
Jensen on the SAME source and h(1)<=E h(Y) show simultaneously that

    C_J>=1, E_mu h(C_J)<=E h(Y).                         (T2)

Taking h(t)=(t-384)_+ gives C_J<=384 almost surely. In the finite actual
uniform source this holds at every source point. The original complete
old divisor dictionary also gives the same cap directly. No separate
source maximization or phase reassignment occurs between the127 fields.
If a fresh height is zero, supports using that coordinate have an empty
exponent rectangle and C_J=1. Thus zero heights and unused padding
coordinates cause no extra actual deletion.

## 2. Weighted conjugates retain the triple interactions

The [normalized fibre-carving response](728-one-common-shallow-source-supports-three-arbitrary-fresh-prime-heights.md) is nondecreasing in every fresh
capacity. At the reference capacities set

    r=(28,30,36,40,42,46,52), m=r-1=(27,29,35,39,41,45,51),
    A_i=C_{i}, u_i=(r_i-A_i)_+,
    P=product_i u_i, b_J=product_(i outside J)u_i,
    Q2=sum_(|J|=2)b_J C_J, Q3=sum_(|J|=3)b_J C_J,
    H=sum_(|J|>=4)b_J C_J,
    Hbar=sum_(|J|>=4)C_J product_(i outside J)m_i,
    W=(P-Q2-Q3-H)_+.

The actual Haar-dominated conditional survivor submeasure has mass at
least W/product(r_i). Also Hbar>=H and H+W>=(P-Q2-Q3)_+.

Let T={1} union support(Y), and let g interpolate x^2 linearly at its18
nodes. It is increasing convex on[1,384], and

    E g(Y)=E Y^2,
    g*(s)=max_(1<=c<=384)[s c-g(c)]
         =max_(v in T)(s v-v^2).                        (T3)

An endpoint-slope extension may be used when applying the global convex
source theorem; the established range of C_J makes its outside values
irrelevant to(T2).

Give each of the21 pair fields penalty g and each of the35 triple fields
penalty g/24. Fix kappa=1/100000. For every0<=lambda<=kappa,

    kappa W+sum_(|J|=2)g(C_J)
             +(1/24)sum_(|J|=3)g(C_J)+kappa Hbar
      >=lambda P-sum_(|J|=2)g*(lambda b_J)
                     -(1/24)sum_(|J|=3)g*(24lambda b_J).

This is the same elementary conjugate inequality applied to the actual
fields, plus kappa(H+W)>=lambda(P-Q2-Q3). Define the maximum of the right
side over lambda in[0,1/100000] as Psi(u). At lambda0,

    Psi(u)>=21+35/24=539/24.

Thus all zero-coordinate boundaries are retained. The construction has
not replaced a positive part by a single quadratic branch.

## 3. A fixed unary hinge certificate

Use the increasing convex unary penalties

    f_i(a)=(1/100)sum_t c_(i,t)(a-t)_+, f(A)=sum_i f_i(A_i),

with the following nonzero coefficient table:

| i / threshold t | 8 | 12 | 16 | 20 | 24 | 32 |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 17433 | 60373 | 42972 | 0 | 0 | 0 |
| 2 | 12486 | 48905 | 43923 | 0 | 0 | 0 |
| 3 | 13379 | 23152 | 1976 | 22346 | 36800 | 0 |
| 4 | 7808 | 6200 | 25538 | 0 | 43974 | 0 |
| 5 | 5254 | 2173 | 20259 | 0 | 52573 | 0 |
| 6 | 6900 | 0 | 6653 | 10259 | 23239 | 38770 |
| 7 | 0 | 4597 | 0 | 3250 | 19992 | 42974 |

Their total expected cost under the SAME Y is

    sum_i E f_i(Y)=2817942055817788/288377958375.          (T4)

The finite enclosure establishes the full pointwise inequality

    f(A)+Psi(u)>=15050 for ALL real A_i>=1.              (T5)

If any A_i>=r_i, nonnegativity and monotonicity give

    f(A)>=min_i f_i(r_i)=426784/25>15050.

This covers the entire exterior of the box product[1,r_i].

## 4. Continuous-domain proof from rational boxes

On a closed box inside product[1,r_i], choose a supporting affine
function ell_i for each f_i and any rational0<=lambda<=1/100000.
Then f+Psi bounds below the function

    sum_i ell_i(A_i)+lambda P
       -sum_(|J|=2)g*(lambda b_J)
       -(1/24)sum_(|J|=3)g*(24lambda b_J).               (T6)

This function is concave in each coordinate separately: the product
P is affine in each coordinate, each b_J is affine or constant, and
the negative of a convex conjugate composed with an affine function is
concave. Successively taking endpoints shows that its minimum on the
box occurs at one of128 corners. All128 corner inequalities are checked
exactly for every box accepted this way; joint concavity is unnecessary.

There is also a monotone-profile bound. Fix u1=u>0 and substitute
v=lambda*u in Psi. For supports not containing1, b_J=u*c_J, so the
conjugate argument is independent of u at fixed v. For supports
containing1, the argument is proportional to v/u. Every weighted
conjugate here is nondecreasing, being a maximum of affine functions
with positive slopes. Increasing u increases the expression at fixed v
and enlarges its admissible interval[0,kappa*u]. Thus Psi is
coordinatewise nondecreasing. At u=0, P=0; each conjugate term is at
least its value at0, and lambda0 attains539/24, so Psi=539/24 there.
The monotonicity therefore includes the zero boundary. Consequently
f(low)+Psi(r-high), or any lower fixed-lambda evaluation of that profile,
is a valid whole-box lower bound.

The primary enclosure uses spatial denominator256, an8192-step lambda
grid, supporting lines at box centers, and longest-side splitting with
priority for active hinge locations. Every split retains both children.
It checks348,225 nodes and174,113 accepted leaves, with maximum depth31.
The leaf counts by method are

    unary plus zero-lambda baseline:7977,
    monotone profile:932,
    affine support plus128 corners:165204.

Their exact volumes sum to

    7246707250298993588463206400 / 256^7
      =100568265525,

the full seven-dimensional box volume. The identity
nodes=2*leaves-1 checks that no child was omitted. Together with the
valid leaf bounds, this covers every real point of the closed box.

The final native verifier performs all acceptance computations as exact
signed128-bit integer operations. A separate arbitrary-precision Python
bound covers all products, sums, subtraction magnitudes, conjugate
arguments, center evaluations, corner gate products, volume and counters
in their actual execution contexts. The largest corner-context bound is
less than1.024% of2^127; the center-only bound is less than1.252%.
The center context does not execute the corner gate's further factor100.
The build also uses undefined-behavior/signed-overflow checking with
immediate abort on failure; the full run exited0 without such a failure.
Diagnostic decimal volume ratios never decide acceptance.

The earlier arbitrary-precision Python implementation and the native
implementation agree on the node and accepted-leaf counts through the
first100,000 nodes; the complete native run separately verifies the
exact final volume; a separate Fraction check verified4,480 conjugate
vertex choices and cleared-formula evaluations, including all seven
zero-coordinate cases. These finite cross-checks support the
implementation; the complete native enclosure supplies the full-domain
certificate. No new Lean verification is asserted.

A separately derived verifier uses spatial denominator512, a16384-step
lambda mesh, direct complementary products, left-endpoint unary supports,
and normalized-width splitting with active hinge cuts. It checks259,861
nodes and129,931 leaves, maximum depth31:4,844 monotone-profile leaves
and125,087 affine/corner leaves. Its exact accepted volume is

    927578528038271179323290419200 / 512^7 =100568265525.

Every large addition, subtraction and multiplication in this independent
implementation has an explicit checked128-bit overflow operation, and
UBSan is also enabled. Its full run exited0; a separate exact budget and
exterior calculation gives the same final density. Its tree and numeric
mesh differ from the primary verifier, so it does not merely recheck the
same saved list of boxes.

The canonical [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_seven_fresh_heights.py)
replays the pinned comparator arithmetic, reconstructs the static integer
range envelope, recompiles the [native verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_seven_fresh_heights.cpp)
with overflow diagnostics, executes the entire primary enclosure and
checks its emitted coefficients against the fixed dual. The [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_seven_fresh_heights.json)
contains exact parameters, full-tree counters, range bounds and budget.
It inherits the actual-source and carving proofs as ordinary mathematics.

## 5. Actual finite-period survival

There are64 supports of size at least4. Their complementary capacity
coefficients sum to

    sum_(|K|<=3)product_(i in K)m_i=1931112.

Taking ONE expectation in(T2),(T5), and the weighted conjugate inequality
bounds the total cost by

    sum_i E f_i(Y)+(539/24)E Y^2+(1931112/100000)E Y
      =3755372306935950419/252330713578125<15050.

Therefore

    E_mu W>=1350557837274586592/80745828345>0.            (T7)

For each actual old source point, the unary carving and subsequent
actual mixed deletions give a fresh-Haar-dominated submeasure of mass
at least W/product(r_i). Finite summation against the uniform source
mu, multiplied by Haar(E23)>=104726/6084351, yields(T1). A positive
measure on this finite CRT carrier has an actual avoiding point.
Neither live mass nor a separately normalized conditional law is
silently substituted for Haar density.

For larger actual fresh primes, apply monotonicity to the NORMALIZED
carving response with l_i=(1-A_i/r_i)_+. Its dependence on a particular
l_i is(h*l_i-k)_+ with k>=0, and increasing capacities also decreases
the relevant negative charge coefficients. The actual numerical fields
satisfy(T2) regardless of their own finite geometric weights. Hence the
reference-capacity inequality proves the stated bound uniformly for all
seven allowed fresh primes and all their finite heights. Every actual
original numerical label is grouped and charged once; completion is an
upper-bound device and does not add forbidden originals.

## 6. A conditional interface beyond the old384-query cap

As in the [six-direction aggregate-budget interface](739-an-aggregate-hinge-budget-removes-the-old-query-hard-cap.md), the pointwise gate also has an explicit unbounded-field formulation.
Keep g unchanged on[1,384], and extend it linearly to the right with
slope1285. This slope exceeds the previous terminal slope640, so the
extension remains increasing convex. In the reference box,

    max_(pairs)lambda b_J<=5137587/4000=1284.39675,
    max_(triples)24lambda b_J<=2201823/2500=880.7292.

Both are below1285. The terminal ray of s*c-g(c) is therefore
nonincreasing, so its maximum over ALL c>=1 still occurs at the same18
nodes. The pointwise conjugate proof and exact gate remain valid for
all mixed fields C_J>=1 with this extended penalty; no new domain
search is needed.

This does not remove the old-height restriction from(T1). For a larger
actual old carrier one must first construct a positive common source
and prove that the sum of its actual unary, pair, weighted-triple and
higher-support penalty expectations is strictly below15050. The old Y
law gives that budget only in the source regime already established.
Different fields may compensate in the total cost, but separately
attainable budgets cannot be treated as one jointly attainable source.
