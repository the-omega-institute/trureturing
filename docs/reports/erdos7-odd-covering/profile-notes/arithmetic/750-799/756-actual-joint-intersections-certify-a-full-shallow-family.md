# A compact joint certificate for the actual full383 family

For one fixed383-original family, a certificate can be checked from
its [literal numerical originals and193-edge forest](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_joint_input.json) alone. It does
not need the57,024,000-cell live tensor, the334,639,305-point numerical
sieve, the final survivor count, or any final query maximum as premises.
The resulting actual higher-core Haar lower bound is

    92922359/16062686640 > 1/173.                     (C1)

The direct numerical CRT calculation below gives the stronger lower
bound2368253/314954640>1/133. Its role here is an independent
comparison, not an input to this compact proof. No Lean claim is made.

## Literal source construction and initial debit

The input contains all383 pairs(modulus,phase), the outside primes
11,13,17,19,23 and the common carrier

    Q=315*11*13*17*19*23=334639305.

Each label is decoded as d times an outside squarefree cofactor, d|315.
The checker verifies the complete numerical slot inventory and every
literal residue range. There are11 core,60 singleton-outside (including
five pure), and312 multioutside originals, with no repeated modulus.

Let X be the actual old315 survivors of the11 core originals. For every
x in X, let A_p(x) be the roots avoiding every ACTUAL singleton-outside
original over x, and put r_p(x)=|A_p(x)|. The initial measure F0 assigns
unit mass to every point

    (x,y), x in X, y_p in A_p(x).

This is the whole actual core-and-singleton survivor set. Its row masses
and total mass are computed directly as

    R_x=product_p r_p(x),  mass(F0)=sum_x R_x=31702156.

There are75 actual core rows. No old row or outside cell is selected using
a prospective query.

For a query(d,J,a,t), its mass is exactly

    sum_(x=a mod d) product_(p notin J)r_p(x)
                        product_(p in J)1_(t_p in A_p(x)).    (C2)

At each p>=13, the pure root and at most eleven nonpure singleton labels
use at most twelve roots globally. Therefore a common untouched root
exists for that axis. Selecting it attains the phase maximum in(C2)
for every old row simultaneously. The checker reconstructs and verifies
those common-root intersections from the actual originals. It then
exhausts all old phases and, when queried, all11 possible roots at11.
This gives EVERY initial marked-query maximum exactly, using [Report750](750-marked-boundaries-and-joint-deletion-updates.md)'s
same-source equality, not any final-source query data.

With kappa(d) as in the previous marked interface, the320 exact initial
maxima give

    48R(F0)=1330280423,
    48J(F0)=48mass(F0)-48R(F0)=191423065.              (C3)

The untouched-root shortcut is used only before the312 multioutside
originals are imposed. Their final actual family uses every live root;
no final-source product factorization or untouched root is assumed.

## Actual original intersections give a mass bound

For each of the312 multioutside events E_i, compute its fibre counts
e_i(x). A fixed old row either fails its old congruence, contains a
forbidden selected root, or contributes product_(unqueried p)r_p(x).
These alternatives are checked from the literal phase.

For each pair, CRT incompatibility makes the intersection zero; otherwise
it is the same calculation on the union of the queried coordinates and
the combined old condition. All48516 pairs are checked. Exactly1464
have positive mass. Define

    S1_x=sum_i F0(E_i in row x),
    S2_x=sum_(i<j)F0(E_i intersect E_j in row x).

The exact global sums are

    sum_x S1_x=4064229,
    sum_x S2_x=323196.

The input also specifies193 forest edges by their ACTUAL numerical labels.
The checker verifies acyclicity and recomputes every edge intersection.
Their total weight is201002. For any forest, the number of active edges
at a point is at most the number of active vertices minus one, whenever
an event is active. Thus the actual removed union G satisfies

    mass(G)<=4064229-201002=3863227.                  (C4)

This is a genuine repair on this actual family: charging the bare sum
would give48J lower bound-3659927, while(C4) alone raises that bound to
5988169>0. Optimality of the forest is not claimed or required.

## Ten old-coordinate credits supply most of the remaining gain

Bonferroni gives a lower bound for the removed mass at every old row:

    L_x=max(0,S1_x-S2_x)<=G(row x).

Therefore the final old marginal is at most R_x-L_x. For each nonzero
core slot d with NO queried outside coordinate, recompute across ALL
old phases

    M_d=max_a sum_(x=a mod d)R_x,
    B_d=max_a sum_(x=a mod d)(R_x-L_x),
    eta_d=M_d-B_d>=0.                               (C5)

The new maximizing phase is free to change. In particular(C5) is not a
subtraction at a previously selected maximizer. Its certified credits are

|d|certified eta_d|
|---:|---:|
|5|1286469|
|7|827989|
|9|1157172|
|15|764370|
|21|473116|
|35|249330|
|45|201584|
|63|126986|
|105|158730|
|315|37330|

The output retains every occupied old phase's initial mass, removed-mass
lower bound and final-mass upper bound, so both maxima in(C5) can be
checked independently. Empty old phases have value zero.

All other query maxima can only decrease when the source is restricted.
Consequently, with no final320-query oracle,

    48 sum_d kappa(d)eta_d=86934190,
    48R(F0-G)<=1330280423-86934190=1243346233.         (C6)

Mass and debit refer to the same actual restricted measure F0-G. Combining
(C4),(C6),

    mass(F0-G)>=27838929,
    48J(F0-G)>=48*27838929-1243346233=92922359>0.      (C7)

No separate extrema are treated as simultaneously attained. The mass
upper/lower statements, query credits and original incidences are all
computed on one fixed F0 and its one actual removed union.

## Higher-core continuation and the exact evidence boundary

The source F0-G is unit mass on every actual shallow survivor. Its Haar
density is at most Q. Extend it uniformly in every additional3/5/7 digit.
Numerical distinctness and the saturated geometric tail sum bound the
mass of any further finite higher-core original family by R(F0-G).
Their outside exponents remain at most one, and all actual new phases
may be arbitrary. Dividing(C7) by48Q proves(C1).

The [compact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_joint_saving.py)
reads only the literal input linked above. It reconstructs the75 actual
core rows, all initial320 maxima, every pair intersection and forest edge,
and the ten complete old-phase credit bounds. The [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_joint_saving.json)
is compared with a fresh exact replay. It reads no final survivor count,
final cap, phase-generation seed, tensor result, or numerical optimizer.

Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_joint_saving.py
```

An independent reconstruction combines numerical congruences using
generalized CRT and forms separate old-phase histograms. It checks all
48,516 event pairs,193 selected edges,320 initial caps and10 phase-credit
slots, and reproduces(C1). This is finite exact arithmetic, not Lean.

## Full numerical survivor certificate

The same literal family has the following core originals:

    (3,0),(5,0),(7,0),(9,4),(15,11),(21,8),
    (35,9),(45,1),(63,1),(105,59),(315,179).

All383 nonunit shallow divisor slots appear exactly once. Across their
fixed outside phases, every live root at each of11/13/17/19/23 is used.
A direct numerical sieve on Z/QZ leaves exactly27,939,653 points. Let F
be unit mass on this ENTIRE actual survivor set. Its exact query debit is:

| Outside-support size | 48 times sum of corresponding maximum debits |
|---:|---:|
|0|841425317|
|1|325687406|
|2|49408113|
|3|3666748|
|4|132984|
|5|1873|

Thus48R(F)=1220322441 and48J(F)=120780903, yielding the stronger bound

    Haar(survivors)>=J(F)/Q=2368253/314954640>1/133.

This also holds for every finite higher-core extension in the same five
shallow outside axes, with all383 shallow phases kept fixed. Source Haar
domination is Q and the saturated core-tail estimate is the same as above.

The [numerical consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_actual_source.py)
checks the shared literal classes and a [final-query certificate](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_actual_certificate.json).
Its [native sieve](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_actual_sieve.cpp)
applies each numerical arithmetic progression to all334,639,305 residues,
then folds counts through all384 divisors and checks all320 nonzero query
maxima. It runs with undefined-behavior checks and compares the
[retained exact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_actual_source.json).
A separate old-row tensor calculation gives the same counts and all maxima.
The compact proof above does not depend on these final data.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullmulti_actual_source.py
```

Both certificates establish this fixed full383 family. Neither is uniform
over shallow phase assignments. In fact, a different actual full family
can have negative J for its uniform surviving measure; improving a lower
bound for that same negative J cannot repair it. One must select a different
supported law or strengthen the higher-core estimate. The compact criterion
exposes actual source information that the coarse scalar envelope omits,
and can be reused with explicit nonnegative row weights.
