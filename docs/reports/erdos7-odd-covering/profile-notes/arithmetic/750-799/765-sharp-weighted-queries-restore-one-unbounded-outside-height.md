# Sharp weighted queries restore a positive29-height reserve on one actual source

Fix the eleven core classes with numerical moduli and phases

    (3,5,9,15,45,7,21,35,63,105,315),
    (0,0,4,11,1,0,8,9,59,74,269).

Let a finite family of pairwise distinct odd nonunit numerical moduli
contain these classes. Every other modulus may be ANY divisor of

    Q=3^H3 5^H5 7^H7 13^E13 17^E17 19^E19 23^E23 29^E29,

where H3>=2, H5,H7>=1 and E29>=0 are arbitrary finite integers, while
E13,E17,E19,E23 are0 or1. Every remaining class has one arbitrary globally
fixed phase. In particular all26 possible multioutside supports are
allowed, with arbitrary permitted29 depth and arbitrary core heights.
Then the Haar density of survivors is at least

    99938/212952285>0.                                    (P1)

This statement is restricted to the displayed actual core phases; it
is not uniform over all112893 old source vectors. It is a concrete
same-source sharp-query repair, not a new prime-support noncoverage
frontier: the family has at most eight prime divisors and lies within
the already attributed eight-prime noncoverage range. No new Lean
verification or optimal-density claim is made.

## A fixed small integer source law

The75 old315 survivors project onto the16 old45 points

    x=(2,7,8,14,16,17,19,23,28,29,32,34,37,38,43,44),

with surviving7 multiplicities

    r=(5,6,5,2,6,5,5,4,6,3,4,5,6,5,6,2).

This is exactly the actual source used in [764](764-one-actual-source-obstructs-even-the-sharp-full-height-envelope.md). Assign every surviving
cell over x its corresponding integer weight

    v=(8,5,4,12,10,12,12,12,10,12,7,12,10,12,5,4).

Normalize by D=sum r_x v_x=684. Every cell has probability v_x/D;
t=max v=12, so the old source has Haar density cap315t/D.

For the eleven divisors in the original displayed order, the exact
weighted cylinder numerators are

    C=(360,218,180,128,60,147,83,52,32,28,12).

Thus

    M=sum C_d=1300,
    K=sum k_d C_d=16428,
    k=(0,12,24,12,42,8,8,22,36,22,57).

All values use the SAME v and actual source. The consumer reconstructs
all75 cells directly from the eleven numerical congruences and checks
every623 nonunit numerical cylinder; no catalogue representative or
phase profile is substituted for this realization.

## Complete sharp weighted hinge envelopes

The actual core leaves live7 root5 untouched above every x. Let A and B
be genuine complete old45 query layouts, each including its unit slot.
The weighted version of [745's convex concentration argument](../700-749/745-actual-source-catalogues-and-sharp-convex-query-laws.md) gives

    J_t(v)=max_(A,B) sum_x v_x[(r_x-1)(A(x)-t)_+
                                      +(A(x)+B(x)-t)_+],
    t=4,6.                                                (P2)

The positive7 query slots are all placed at the SAME untouched root5.
Superadditivity of the convex increments proves the upper bound; that
legitimate globally fixed query placement attains it. The weight v_x
is common to the surviving cells at x, so it preserves the pointwise
argument. No actual deletion phases are changed and no source is
selected after a query.

For this16-point old45 set, the numbers of nonempty restricted phase
masks at3,5,9,15,45 are2,4,5,7,16. Their complete products give4480
old45 layouts. Empty query masks may be replaced by any nonempty mask
because both hinges are increasing. Deduplicating the complete layouts
retains exactly4480 vectors.

The integer native enumerator visits ALL4480^2=20070400 ordered(A,B)
pairs, using their same-point weighted load histograms. The exact maxima
are

    J4(v)=296, J6(v)=104.                                 (P3)

The consumer separately reconstructs numerical phases for both reported
maximizing queries, then directly reads them on the actual75 cells to
check attainment. An independently implemented mask-based unordered-pair
oracle returns the same two maxima. The complete upper bound comes from
the full query enumeration and(P2), not from the fourteen lower cuts in764.

## One source for every allowed remaining original

Use [751's actual pure-avoiding laws](751-clipped-common-sources-release-core-and-outside-heights.md), conditional singleton clipping, and
geometric depth bounds. Assign thresholds(4,4,4,6,6) to13,17,19,23,29.
Only29 is given arbitrary finite height, so

    epsilon=(0,0,0,0,1),
    rho_i=1/(p_i-a_i-epsilon_i),
    rho=(1/9,1/13,1/15,1/17,1/22).

The raw conditional product source is formed AFTER removing all actual
pure and nonpure singleton originals and BEFORE charging multioutside
originals. Zero conditional fibres get zero mass. This uses the actual
remaining phases without treating later multioutside survivors as an
independent product law.

Its singleton clipping loss is at most

    (1/9+1/13+1/15)J4/D+(1/17+1/22)J6/D.

Let

    F=product(1+rho_i)=10304/7293,
    B=F-1-sum rho_i=11789/218790.

The higher-core debit is at most F K/(48D), after summing every excess
core depth and every allowed outside cofactor. Every core-shallow
multioutside original is paid by B(1+M/D): the B expansion includes every
outside support of size at least two; each selected29 factor includes
its complete positive-depth geometric majorant. Numerical distinctness
ensures one original per actual modulus. These classes are disjoint as
labels from the pure, singleton and higher-core categories.

Consequently the total sufficient cost on this same source is

    cost=F K/(48D)+B(1+M/D)
         +(1/9+1/13+1/15)J4/D+(1/17+1/22)J6/D
        =18506669/18706545<1.                            (P4)

The raw Haar cap, including the SAME maximum old weight, is

    D0=(315t/D) product_i (p_i-epsilon_i)/(p_i-a_i-epsilon_i)
      =2254/99.

Dividing the positive remaining unnormalized mass by D0 gives

    (1-cost)/D0=99938/212952285,

which proves(P1) for all the stated finite heights and globally fixed
remaining phases. Missing outside axes can be padded with independent
coordinates; all phases of actual originals are retained.

## What this positive example establishes

For these identical weights, replacing the sharp values(P3) by the
valid conservative bounds29t and10t gives

    cost_conservative=18914518/18706545>1.

Thus retaining actual weighted hinge geometry, instead of only t and
the uniform hinge envelope, changes this construction from an
uncertified reserve to a strictly positive one. It does not alter the
original family or transport a hinge value from another measure.

By contrast,764 shows that letting ALL five outside axes have arbitrary
heights defeats the specified saturated budget even with sharp hinges
for every old45 weight vector on this source. The present theorem
changes the height scope explicitly; it does not overturn that result.
The remaining all-source and stronger-height extensions are open here.

## Exact reproduction

The [literal actual source](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_sharp_last29_input.json),
[complete generic weighted enumerator](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_weighted_hinges.cpp),
[exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_sharp_last29.py) and
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_sharp_last29.json)
reproduce all source values and query maxima.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_sharp_last29.py
```

The consumer pins the literal and native source, compiles an isolated
temporary executable with undefined-behavior checks, and compares the
recomputed result with the retained data. It replays all20070400 ordered
query pairs twice, once with the stated weights and once with uniform
weights, checking the comparison values29 and10 on this same source.
The independent mask-based unordered-pair computation agrees with the
weighted maxima. All enumeration and rational arithmetic are solver-free.
These are exact finite checks and an ordinary transport argument, not a
new Lean/kernel result.
