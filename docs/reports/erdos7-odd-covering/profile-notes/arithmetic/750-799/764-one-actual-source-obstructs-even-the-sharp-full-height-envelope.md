# An actual source blocks the full-height budget even with sharp weighted hinges

For the actual75-point core source below, every nonnegative real old45
weight vector and every threshold vector in{4,6}^5 has the specified
all-height common-source cost strictly greater than51/50. The hinges
in this statement are the TRUE complete-query maxima on that same
weighted source. The obstruction does not result merely from using the
coarser pointwise bounds29t and10t.

This is a limitation of one source ansatz and one sufficient budget. It
does not assert that the actual family covers, that arbitrary outside
heights are impossible, or that every source law fails. It is ordinary
mathematics with a standalone exact finite certificate, not a Lean result.

## One actual source and its weighted boundary

Fix the actual core family with numerical moduli and respective phases

    (3,5,9,15,45,7,21,35,63,105,315),
    (0,0,4,11,1,0,8,9,59,74,269).

Its surviving old45 points and numbers of surviving7 roots are

    x=(2,7,8,14,16,17,19,23,28,29,32,34,37,38,43,44),
    r=(5,6,5,2,6,5,5,4,6,3,4,5,6,5,6,2).

The total is75. This is shape4, group25 in the [complete actual-source catalogue](753-six-shape-actual-source-joint-query-catalogue.md).
The five nonpure7 labels have old phases(2,4,5,14,44) at
(3,5,9,15,45) and live7 colors(1,2,3,4,3); pure7 uses color0.
The displayed numerical phases are their CRT realization. The consumer
reconstructs every residue mod315 and verifies the actual75 cells.

Give every surviving315 point over x the same nonnegative real weight
v_x, with v not identically zero. Set D=sum r_x v_x. In the displayed
nonunit divisor order, let C_d be the exact maximum weighted cylinder
mass and define

    M=sum C_d,
    K=sum k_d C_d,
    k=(0,12,24,12,42,8,8,22,36,22,57).

The five caps without7 are max_a sum_(x=a mod d) r_x v_x;
the7 cap is sum v_x; the remaining five are max_a sum_(x=a mod d) v_x.
The common untouched root5 attains the positive7 caps. The consumer
independently checks all623 literal nonunit numerical cylinders: each
is dominated by an included cap row, and every included row is attained.

A complete query Q has one independently chosen phase for every
divisor of315, including the unit divisor. Its phases are fixed globally
on the actual source. Define the true weighted hinge numerators

    J_t(v)=max_Q sum_(z survives) v_(z mod45) (Q(z)-t)_+,
    t=4,6.

Every quantity D,M,K,J4,J6 belongs to this ONE weighted source. Under
uniform v, they are75,147,1861,29,10 respectively.

## The all-height cost that is obstructed

For outside primes P=(13,17,19,23,29), release every outside height to an
arbitrary finite value. The [all-height pure-avoiding law](751-clipped-common-sources-release-core-and-outside-heights.md) has complete
positive-depth cap sum1/(p-2). After singleton clipping at threshold a,
the corresponding sum is rho=1/(p-a-1), and the raw Haar density factor
is(p-1)/(p-a-1). For a=(a_1,...,a_5) in{4,6}^5, write

    rho_i=1/(p_i-a_i-1),
    F=product(1+rho_i), B=F-1-sum rho_i.

Paying higher-core originals and every multioutside support under the
same pre-multioutside clipped source gives the saturated sufficient cost

    C_a(v)=F K/(48D)+B(1+M/D)
           +(sum_(a_i=4)rho_i)J4(v)/D
           +(sum_(a_i=6)rho_i)J6(v)/D.                     (O1)

All phases remain globally fixed; every numerical modulus is paid once
in its designated support/depth category. The coefficients sum geometric
cylinder caps over every possible positive finite depth. They are the
height-independent saturated budget, not a claim that every finite
height realizes these infinite sums or exhausts their union bound.

The exact certificate proves, simultaneously for all32 a and all v>=0
with D>0,

    C_a(v)>=12922647501637/12615680000000>51/50>1.           (O2)

Thus even sharp weighted hinge information cannot turn(O1) into a
positive-reserve certificate using this conditional-uniform7 ansatz.
This is a statement about(O1); overlaps or a different transport bound
can still improve the actual survival estimate.

## Fourteen literal queries and a rational dual proof

Normalize D=1 by homogeneity. Use29 nonnegative variables

    z=(v_1,...,v_16,C_1,...,C_11,J4,J6).

The cap epigraphs give69 integer inequalities. For a complete numerical
query Q and threshold t, form its16-vector

    h_(Q,t)(x)=sum_(z survives,z mod45=x) (Q(z)-t)_+.

Then J_t>=sum_x h_(Q,t)(x)v_x. The literal input contains14 such query
witnesses, each with all12 numerical labels and all12 residue phases.
The consumer reads the actual75 cells and directly recomputes each
coefficient. It checks label completeness, distinctness and residue
ranges. It does not trust an oracle's coefficient vector, a claimed
maximizer, or an inferred A/B decomposition. The14 lower hinge cuts
together with the cap rows give83 integer inequalities Az<=0.

The normalization is e.z=1, with e=(r,0,...,0). The11 cap coefficients
in the linear part of(O1) are F k_d/48+B; the two hinge coefficients are
the corresponding sums of rho. Denote this rational vector by c, so
C_a=B+c.z.

For each threshold tuple, the literal supplies a positive integer scale
L and nonnegative integer multipliers lambda on the83 rows. The checker
reconstructs A,c and sets

    nu=min_(1<=i<=16) (Lc+A^T lambda)_i/r_i.

It verifies all29 exact rational inequalities

    Lc+A^T lambda-nu e>=0.

Multiplying by z>=0 and using Az<=0 gives

    L c.z >= nu-lambda.Az >= nu,

and therefore C_a>=B+nu/L. The minimum of the32 reconstructed bounds is
the number in(O2), at a=(4,4,4,6,6). This minimum describes the supplied
certificates; no LP optimality is claimed. Fourteen actual query lower
cuts suffice, so an exhaustive maximum enumeration is unnecessary for
the obstruction proof. The separate query witnesses bound separate
supremum terms; they do not assert simultaneous attainment by one actual
outside phase family or turn this upper budget into actual deletion mass.

Numerical separation and LP search proposed the witnesses. The final
consumer uses only the Python standard library. No optimizer, native
oracle, tolerance, or claimed optimality is among its premises.

## Scope and next gap

The obstruction quantifies over all nonnegative real old45 weights and
all32 stated threshold vectors for this actual source, using true sharp
hinges. It does not quantify over root-dependent315 weights, another
supported source, other thresholds or clipping rules, direct overlap
credits, or a different treatment of higher-core and multioutside
originals. It does not refute finite-height noncoverage or the original
odd-covering conjecture. Enlarging the same sharp hinge query search
cannot defeat the14 valid cuts already used in this certificate.

## Exact verification and remaining boundary

The [literal input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullheight_envelope_dual_input.json)
contains the actual source,14 complete numerical queries and32 integer dual
certificates. The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullheight_envelope_dual.py)
pins the input and catalogue, reconstructs the actual cells, every query
coefficient and every dual inequality. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullheight_envelope_dual.json)
must equal a fresh full recomputation.

A separate implementation reconstructs the same carrier, counts the full
query load at every actual cell, and sums the literal multipliers as rational
polynomials in named variables. All894 positive multipliers and32 certified
bounds agree, including(O2). No optimizer or claim of attained optimality is
used by either check.

Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullheight_envelope_dual.py
```

Only the stated sufficient-budget route is closed. The unrestricted
odd-covering question and a uniform source construction for its remaining
families are not proved here. These are ordinary proof and exact finite
certification, not new Lean verification.
