# All shallow outside supports without11, on at most five outside axes

Let P be a set of at most five primes, all at least13. Fix arbitrary finite
core heights E3,E5,E7 and put

    Q=3^E3 5^E5 7^E7 product_(p in P) p.

For every finite family of pairwise DISTINCT odd numerical moduli m>1
dividing Q, with one globally fixed arbitrary residue for each modulus,
the Haar density of integers avoiding every class is at least

    24842/294076965 > 1/12000.                                  (N1)

In particular the family does not cover. All outside supports are allowed,
including every shallow multioutside original; the restriction is that
each outside exponent is at most1. The3/5/7 heights are arbitrary and
finite. This does not cover outside11, six or more outside axes, arbitrary
outside heights, or the unrestricted odd-covering problem.

The result uses the complete six-shape actual core catalogue already
certified in the [actual-source catalogue](753-six-shape-actual-source-joint-query-catalogue.md)
and the116 [fixed old source laws](754-last-three-shallow-supports-with-arbitrary-core-heights.md). The additional
work is a32-source repair and a new joint budget for all26 shallow
multioutside supports. It is ordinary mathematics plus exact finite
certification, not new Lean verification.

The noncoverage range itself is already contained in the attributed
eight-prime result recorded in the [Schroeder source record](../../../../../../Library/Arith/schroeder2026nine.md):
Michael Schroeder, *Nine Prime Divisors in Odd Distinct Covering Systems*,
edition1.0.1, DOI10.5281/zenodo.22759614, states noncoverage with at most
eight prime divisors and unrestricted exponents, together with uncovered
density at least1/1002375. The project's source record preserves the
boundary that the whole arbitrary-height theorem has not been locally
kernel-replayed. Here there are at most three core primes plus five
outside primes, so no new prime-support noncoverage frontier is claimed.
Nor is(N1) a record for pure-head density in this project: the [existing no11 source](../../../problem-details/68-eight-prime-core-omitting-eleven.md) gives, under its
explicitly inherited ordinary source premises, the stronger no11
eight-prime head source bound

    (10237584019/168750000000)/(297/20)

before paying its attachment costs. The present contribution is the
315-window clipped source with all26 shallow outside supports in one
budget, the32 explicit repairs using weights0,...,6, and the accompanying
cylinder-query bounds that can be used in later common-source composition.
The quantitative margin(N1) certifies this particular construction; no
best-density or new prime-support frontier claim is made.

## 1. One actual old source and its task quantities

First choose one effective-padded actual core source by the existing
six-shape reduction. Missing or inactive slots may receive auxiliary
supported restrictions; active original phases are retained. This step
does not identify every raw source with one common75-row set. The
complete catalogue contains112893 selected sources in six shapes.

Within one selected source, let x range over its old45 points, and let
r_x=6-b_x count its actual surviving7 roots after the pure7 root and the
five nonpure7 slots. Choose nonnegative integer weights v_x, and give
every surviving old315 point over x the same weight v_x. Set

    D=sum_x r_x v_x, t=max_x v_x.

For the eleven nonunit old divisors in the order

    (3,5,9,15,45,7,21,35,63,105,315),

write C_d for the actual maximum weighted cylinder mass. The five caps
without7 are max_a sum_(x=a mod d) r_x v_x. The pure7 cap is sum_x v_x,
and the remaining five7 caps are max_a sum_(x=a mod d) v_x. These are
exact: five nonpure7 labels use at most five of the six live roots, so
there is a common untouched root attaining every corresponding free query.
Thus the caps depend on this source's actual b and this SAME v, even when
different actual color patterns realize the same b.

Define

    M=sum_d C_d,
    K=sum_d k_d C_d,
    k=(0,12,24,12,42,8,8,22,36,22,57).

The normalized old law has nonunit complete-query bound M/D, higher-core
coefficient K/(48D), and raw Haar cap315t/D.

Let J4 and J6 be upper bounds on the unnormalized weighted hinge
numerators of this same source. A uniform law uses its catalogue values.
For each weighted source used below, its uniform source has hinge
numerators29 and10. Pointwise v_x<=t gives

    J4<=29t, J6<=10t.                                         (N2)

This domination is applied before the query maximum and uses the same
actual source throughout. It neither imports a uniform normalized hinge
after reweighting nor requires an independently attaining query for each
term.

## 2. Singleton clipping and all26 multioutside supports

At the minimal five-prime tuple

    (13,17,19,23,29),

use the SAME thresholds(4,4,4,6,6) for every source. The singleton clipping
construction from754 gives one unnormalized measure supported on the
actual core and actual singleton survivors. Its parameters are

    rho=(1/9,1/13,1/15,1/17,1/23).

The raw mass lost to the clipped singleton fibres is at most

    (149/585) J4/D+(40/391) J6/D.

Every old cylinder C with queried outside set J has mass at most the old
mass of C times product_(i in J) rho_i. The same measure has raw Haar cap

    D0=(315t/D) product_i p_i/(p_i-a_i)
      =(315t/D)(551/135).                                   (N3)

Uniformly extend this measure through all extra core digits. Summing the
complete higher-core geometric tails gives total higher-original debit
at most

    F K/(48D), F=product_i(1+rho_i)=7168/5083.

For the shallow multioutside originals, every subset J with |J|>=2 is
allowed. There are26 such supports and12 possible old divisors d|315,
including the unit divisor. Distinct numerical original labels give
total debit at most

    B(1+M/D),
    B=product_i(1+rho_i)-1-sum_i rho_i=12166/228735.

These are separate numerical originals from the singleton and
higher-core classes. Their actual phases remain globally fixed; their
overlaps only improve the union bound. Every debit is evaluated under
the SAME unnormalized measure. The complete sufficient cost is

    cost=(7168/5083) K/(48D)
         +(12166/228735)(1+M/D)
         +(149/585)J4/D+(40/391)J6/D.                        (N4)

Equivalently define the integer reserve

    G=216569D-12166M-6720K-58259J4-23400J6.                  (N5)

Then 1-cost=G/(228735D). Dividing by the SAME density cap(N3) gives

    Haar(survivors)>=G/(294076965t).                         (N6)

## 3. Exactly32 additional source laws close the minimal tuple

Keep754's116 fixed weighted source laws, using the conservative bounds
(N2). Use uniform weights on the other sources except the following two
uniform catalogue groups, both in shape3:

| Group | N | M | K | Uniform J4 | Uniform J6 | Actual source count |
|---|---:|---:|---:|---:|---:|---:|
|20|75|148|1865|29|10|12|
|22|75|149|1865|29|10|20|

Their uniform costs under(N4) are17169329/17155125 and381811/381225,
respectively. They are the ONLY remaining failures among the previously
assigned parameter rows.

All32 actual b vectors can be extracted without re-enumerating the full
catalogue. Shape3 has16 old45 points. For the five7-slot masks at old
moduli3,5,9,15,45, the largest sizes are8,5,4,3,1. If N=75, then

    sum_x b_x=6*16-75=21=8+5+4+3+1.

Let q_x count the five numerical masks hitting x, before merging equal
root colors. Then b_x<=q_x pointwise and sum q_x<=21. Equality forces
each chosen mask to have maximum size and b_x=q_x for every x. Hence all
N75 vectors are sums of maximum masks, even if disjoint masks happened to
share a color.

There are only2*2*2*2*16=256 choices of these maximum masks. Conversely
every such choice is actual: use pure7 root0 and assign the five labels
distinct live colors1,...,5. CRT produces one literal numerical phase for
each7*d, and root6 remains common. The256 sums are distinct. Filtering by
the displayed M,K values returns exactly12+20=32 actual vectors, matching
the COMPLETE catalogue group counts. Every source at either triple has
the same already certified uniform J4=29 and J6=10.

The new literal input assigns one old45 vector v with entries between0
and6 to each of these32 sources. The consumer verifies all256 maximum
mask choices, exact32 coverage, each supplied actual phase witness, all
weighted caps, and the reserve using(N2). It also reconstructs all315
residues of each literal witness, independently confirming the fibre
counts6-b_x. No arbitrary old315 reweighting or transport between unrelated
source masks is used.

For the32 new laws:

    max cost =87888344/89892855 <1,
    min paired Haar =2004511/1764461790.

LP search only proposed the small integer vectors. The final consumer
has no optimizer, proposed cost, or optimality premise among its inputs.

## 4. Complete source accounting and the uniform margin

The final source assignment is:

| Source type | Actual sources | Checked parameter rows |
|---|---:|---:|
| Remaining uniform laws |112745|3187|
| Retained754 weighted laws |116|116|
| New shape3 weighted laws |32|32|
| Total |112893|3335|

The exact consumer recomputes every selected source's own D,M,K,t and
uses that source's uniform hinge or its justified weighted upper bound.
It verifies

    G>=24842t

for all3335 parameter rows. The least reserve per maximum weight occurs
at a remaining uniform group in shape4:

    (D,M,K,J4,J6,t)=(75,147,1861,29,10,1).

Its cost is17130283/17155125 and its Haar bound is precisely(N1). The
new weighted laws have larger margins, so they do not control the final
uniform bound.

## 5. Larger primes, missing coordinates, and finite heights

Every five ordered outside primes without11 are componentwise at least
13,17,19,23,29. Keep the thresholds4,4,4,6,6 by position. As a prime
increases, both rho_i=1/(p_i-a_i) and p_i/(p_i-a_i) decrease. All cost
coefficients and the Haar-cap factors are nonnegative, so the entire
same-source cost and density cap can only improve. This transports(N1)
to every such five-prime tuple.

If fewer than five outside coordinates, or some core coordinates, are
present, pad with free coordinates and apply the same supported-source
construction. Haar survivor density of the actual family is unchanged
under this free lift; auxiliary source restrictions may discard mass but
cannot create survivors outside the original family. The complete core
geometric majorants apply uniformly to every finite core height.

## Exact verification and remaining boundary

The [literal input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_no11_all_supports_weights.json)
contains only32 actual b vectors, integer old45 weights and maximum-mask
phase witnesses. The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_no11_all_supports.py)
pins that input and the existing753/754 catalogue and source laws by
content hashes. It verifies the complete3335-row assignment, all256
maximum-mask layouts, all32 actual315 witnesses, and(N2)--(N6) using exact
rational arithmetic. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_no11_all_supports.json)
must equal fresh complete recomputation.

Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_no11_all_supports.py
```

A separate implementation reconstructs all32 actual315 carriers and their
eleven query caps directly from numerical residues, checks the maximum-mask
completeness argument, and reproduces the same all-source reserve and
Haar minimum. Both calculations inherit the pinned catalogue's earlier
complete native enumeration and uniform hinge bounds; neither represents
a fresh native catalogue reconstruction or new Lean verification.

The outside11 case, arbitrary outside exponents within this clipped-source
method, and a number of outside coordinates not bounded by five remain
outside this result. Unrestricted Erdős #7 remains unresolved.
