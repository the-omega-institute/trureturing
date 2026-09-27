# Adaptive triple gain without a uniform mixed-inventory rebate

For the same three-point interface as report501, every actual family satisfies

    616(17s1+16s2+13s3)>=41.                              (A1)

This improves the earlier survivor lower bound32, while the original fixed
objective min g_(17,16,13) remains32 on the axis-budget relaxation. The gain
uses two different mixed-budget weights on two exhaustive axis regions and
the nonnegativity of survivors.

It cannot be interpreted as subtracting a uniform rebate from the independent
mixed budget892. For the fixed pure family F of
[report504](504-equal-axis-totals-have-different-mixed-continuations.md), an
explicit actual extension attains the entire finite mixed budget at every
rectangular exponent cutoff. There is no uniform positive multiplicative
rebate, even with this F and all51 old labels fixed.

Both statements are ordinary mathematics, supported by exact rational and
literal CRT checks. They concern the declared three-point interface, not
unrestricted Erdős#7 or a completed-source mass bound. No new Lean verification
is asserted.

## Common interface and the stronger survivor inequality

Keep the old primes3,5,7,11,13,17,19, new primes23,29, the51 numerical old
labels D and the simultaneous old centres and points in
[report503](503-integer-selectors-strengthen-capped-budgets-but-axis-limits-survive.md).
The ordered profiles are

    (4,2,-4,1,2,1,1),
    (5,-2,4,1,1,1,1),
    (-5,-3,-2,1,1,1,1).

For label d, A_d and B_d are its three old-point activation bits. Put
N(v)=sum_d max(v dot A_d,v dot B_d). Each complete original numerical
modulus d*23^j*29^k is distinct and has one fixed old selector and one common
new phase tuple, shared by all tested points. Missing labels are allowed
in the bounds. Other old residues and other prime directions are not included.

Let t,u be22 and28 times actual pure-axis deletion fractions, and s the
remaining later-fibre survivor fractions on full uniform new-coordinate
fibres. With the same actual family throughout, for any v>=0,

    616 v dot s>=g_v(t,u)
       :=sum_i v_i(22-t_i)(28-u_i)-N(v).                  (A2)

This subtracts the mixed union upper bound from the exact pure survivor
product. For full-family survival, the old points must separately avoid
all old-only classes.

Both axis vectors lie in their capped complete weighted polytopes P_22 and
P_28. In the direction order

    100,010,110,001,101,011,111,112,121,211,

the capacities are

    22,21,39,30,45,42,58,85,78,79.

Split P_22 at t1=20. Exact vertex-pair minimization gives

| Axis region | Mixed weight v | N(v) | Minimum g_v | Vertex pairs |
| --- | --- | ---: | ---: | ---: |
| t1<=20 | (17,9,8) | 671 | 41 | 15*22=330 |
| t1>=20 | (9,16,9) | 662 | 92 | 12*22=264 |

The minima occur respectively at

    t=(18,21,18), u=(22,12,23),
    t=(21,18,19), u=(15,21,21).

All vertices are obtained by enumerating triples of independent active
constraint normals and checking all inequalities with rational arithmetic.
The objective is linear in t for fixed u and linear in u for fixed t, so a
minimum over the compact product occurs at a vertex pair. The594 checks
therefore prove the two stated minima, not just sampled upper estimates.

Each branch weight is coordinatewise at most w=(17,16,13). Since s>=0,
A2 implies A1 in both exhaustive regions. Each branch weight also sums to34,
so its own inequality yields

    max_i s_i>=41/(616*34)=41/20944.                      (A3)

A3 uses the branch weight sum34; it does not follow by treating the sum of
w as34. These are certified lower bounds, with no actual-family sharpness
claim. The stronger value does not create a new Boolean triple edge at the
existing threshold1/3696, and cannot replace the global threshold while
keeping weaker pair constraints unchanged.

## Actual simultaneous saturation with F fixed

Now fix every class and residue of the102-class pure family F in report504.
Its pure survivors in the three first-phase fibres have sizes(40,32,25) out
of667. The phase cells surviving simultaneously at all three old points are

    C={0,22} times {0,25,26,27,28}.                       (A4)

Choose a w-maximizing old selector for each d and use that selector at all
mixed powers. The active-label counts are n=(21,18,19), with w dot n=892.
The selected-mask multiplicities are

| Active old points | Number of labels |
| --- | ---: |
| {1} | 16 |
| {2} | 13 |
| {3} | 16 |
| {1,2} | 3 |
| {2,3} | 1 |
| {1,3} | 1 |
| {1,2,3} | 1 |

The six nonsingleton labels are1,3,5,7,9,27. Assign them, in this order, the
first six lexicographic cells of C. Reserve three other common cells

    P=(22,26), Q=(22,27), B=(22,28).                     (A5)

For each singleton label choose a surviving cell in its one active fibre,
avoiding these reserved cells and the cells of labels already active there.
After the shared assignments and reservation, the available counts are at
least32,24,19, versus singleton requirements16,13,16. Thus all first-layer
assignments exist and no two labels active at the same old point share a cell.
Write these assignments as(r_d,s_d).

Properly color the intersection graph of selected active masks using colors
c_d in{1,...,21}: give the six shared labels different colors1,...,6; the
singleton groups avoid respectively5,5,3 of those colors and use distinct
remaining colors within each group. There are enough colors for16,13,16
singletons. Different singleton groups have disjoint masks and can reuse
colors. The consumer checks the complete resulting coloring and assignments.

For every finite J,K>=1, include exactly one mixed class for each

    d*23^j*29^k, d in D, 1<=j<=J, 1<=k<=K.

Its new-coordinate residues, interpreted modulo23^j and29^k, are

    (r_d,s_d)                           if j=k=1,
    (22+c_d*23^(j-1),26)                 if j>=2,k=1,
    (22,27+c_d*29^(k-1))                 if j=1,k>=2,
    (22+c_d*23^(j-1),28+29^(k-1))        if j>=2,k>=2.     (A6)

Combine A6 by CRT with the selected old-centre residue modulo d. This gives
one static residue per complete original modulus. Unique prime factorization
ensures that mixed labels are distinct from each other and from the pure
labels; all moduli are odd and greater than one.

On each tested old fibre, every higher-level cylinder lies in one of the
three reserved common cells, so it avoids every pure class there. First-layer mixed cylinders avoid the reserved
cells. In P, exact valuation v23(x-22)=j-1 separates different j; the nonzero
color separates labels with intersecting masks at the same j. In Q the
corresponding29-adic statement uses k-1 and c_d. In B the pair of valuations
is(j-1,k-1), and the23-color separates intersecting masks at a common height
pair. Colors1,...,21 are nonzero modulo both primes. The three reserved
first-phase cells are different, so cylinders in different cases of A6
cannot meet.

Thus, at each old point, all active mixed classes are pairwise disjoint and
lie inside its unchanged pure survivor set. Their measures add exactly,
giving the sharp finite mixed deletion

    sum_i w_i * mixed_deletion_i
      =892/616 * (1-23^(-J))*(1-29^(-K)).                 (A7)

The ordinary weighted union bound gives the same quantity as an upper bound,
so this is simultaneous attainment by original residues, not merely separate
per-label maximization. It handles every finite rectangle without treating an
infinite family as a covering system.

## Finite counterexample to a uniform rebate and its boundary

At J=K=1, the combined family has153 classes and mixed deletion892/667.
The three remaining fibre counts are(19,14,6) out of667.

At J=K=2, the combined family has306 classes and mixed deletion

    642240/444889
      =(443520/444889)*(892/616)
      >(99/100)*(892/616).                               (A8)

This already contradicts a one-percent uniform discount of the closed mixed
budget for this fixed F. As J,K grow through finite integers, the factor in
A7 tends to one. Hence no epsilon>0 works uniformly for every finite mixed
extension of F.

This construction keeps F at its first pure layer. It does not saturate the
mixed budget along the limiting pure-axis configuration used to attain the
old relaxed objective32. A bound conditioned on stronger actual pure losses
or their joint phase arrangement remains possible. Nor does the construction
assert positive occupancy of these CRT points under a completed old source.

A1 and A7 are compatible: a stronger survivor bound can follow from joint
constraints even when an unconditional reduction of one budget is false.
The next useful obligation is a deficit conditioned on the actual joint
pure boundary, followed by a global source-support bound. The larger triple
constant alone does not meet that obligation.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_region_triple_survival.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_inventory_saturation.py

The first consumer regenerates the clipped axis vertices and all594 rational
objective values. The second retains F unchanged, constructs the shared
label selectors, first phases and colors, and verifies original CRT residues
at J=K=1 and2. It checks every relevant mixed/pure and mixed/mixed congruence
compatibility and directly enumerates the first-level CRT survivors. The
all-height proof is the valuation argument for A6, not an extrapolation from
these finite examples. Both consumers use only the standard library and
compare the derived result with their adjacent JSON by default.
