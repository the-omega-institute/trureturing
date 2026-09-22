[Index](../../marked_head_profile.md) · [Global mass-floor bridge](146-a-global-mass-floor-and-coupled-costs-expand-the-k-radius.md) · [Original vector marker](../../frontier/endpoint-bounds/vector_marked_source.py)

# The optimized heavy margin fails late-factor Jensen

The original implemented index0 heavy margin is not separately
concave in the late-source factor. A rational segment between the
original product vertices398 and404 already violates the required
Jensen inequality. Thus146's vertex argument for the carrier mass
cannot be transferred to this optimized heavy margin without
changing the bound or subdividing its active regions.

This refutes the proposed componentwise concavity argument on the
implemented source relaxation. It does not assert that the three
source points arise from finite covering families, or that the
complete52-cost signed sum fails concavity: other summands can
compensate for a component's defect. It supplies no new global K.

## 1. One original factor moves, with all source guards retained

Use original index0, named R17 with tuple(0,0), r=0, first_beta=2,
and the point carrier(root,cell)=(1,1). For0<=t<=1 set

    deficit=(1/2,0,0,0,0), alpha=(0,1/4),
    beta=(0,0,1/4,0,0), z=3/4,
    late=((1-t)/72,0,0,t/72,0).                 (VJ1)

Only the late simplex factor changes. In particular Delta=0,
the actual first-beta condition remains satisfied, and the caps,
pure masses, availabilities, carrier scores and positive geometry
gap are constant. The source masses are

    n=(1/36+t/72,1/12,1/36,1/18-t/72,1/18),
    s=1/4.                                     (VJ2)

The original geometry and every necessary slot/group condition
hold at both endpoints. Their remaining dependence on late is
affine, so they hold on the entire segment. The helper additionally
checks each evaluated point through the original API. No guard,
first-beta constraint or original cost branch is disabled.

Let M(t) be vector_marked_source.cost_bound's new_layout_min, the
minimum of all100 original retained-deep branches. It is a margin
lower bound, so the proposed vertex reduction requires concavity.
The same branch controls at every point used below:

    baseline b=(2,3,1,1,1), positive5=(1,1,3,2,2).

The two other root1 permutations of positive5 tie. The active
marker uses slot2 and selected-deep cell0 throughout. Write its
root1 derivative as

    v=298469622484874903/2311075142665519230>0.   (VJ3)

For the following symmetric triple, the exact original API gives:

| t | M(t) |
| --- | --- |
| 3/4 | 156912662969586614381525286466507/2143925176994895672413135100000000 |
| 4/5 | 12020944534654472152979115907039/154609988725593437914408781250000 |
| 17/20 | 2649330337030817817917844054580619/32158877654923435086197026500000000 |

Consequently

    M(4/5)-(M(3/4)+M(17/20))/2
      =-v/3600
      =-298469622484874903/8319870513595869228000<0. (VJ4)

The old_common_layout_min has Jensen difference exactly0 on this
triple. The violation is in the new marker improvement.

There is also a direct failure of interpolation from the two
original product vertices:

    M(0)=1193878489939499612/259995953549870913375,
    M(1)=1083673895520386723490708479815549
                    /11255607179223202280168959275000000,

    M(3/4)-M(0)/4-3M(1)/4
      =-3903263580003370702541/23305343953667629019166000<0. (VJ5)

This does not mean M has an interior value below both endpoints;
the failed assertion is the stronger Jensen inequality used by the
proposed proof, not every possible vertex bound.

## 2. The exact obstruction is an adaptive capacity dual

In cell3 of slot2, the cap stays1/45 and the non-H budget is

    B3(t)=n3-eta3/5=1/30-t/72.                 (VJ6)

The column coefficient in that cell is4v/5. The three-group
capacity bound keeps gamma=0. In the five-row partition, the
optimal cell3 dual changes when B3(t) crosses1/45, namely at t=4/5.
The five-row upper bound then becomes smaller by

    (4v/5)*(1/45-B3(t))_+
      =(v/90)*(t-4/5)_+.                       (VJ7)

The marker subtracts this upper bound. At the retained points its
credit is exactly

    credit(t)=4v/225+(v/90)*(t-4/5)_+.          (VJ8)

The helper checks(VJ8) against every retained point and compares
both original duals, with the same selected-deep cell and original
layout. There is no layout change responsible for(VJ4). Replacing
the concave capacity optimum by its negative creates a convex
piece, and the old margin does not cancel this corner.

## 3. A fixed feasible dual repairs this late factor

For each original column and each original selected-deep choice,
use the feasible gamma=0 dual

    column upper<=sum_c coefficient_c*cap_c.    (VJ9)

This is an upper bound for every feasible allocation, irrespective
of its row/group budget. It is constant as late varies while all
other source data, carrier, r and first-beta remain fixed. The
helper implements this as a separate explicit formula; it does
not replace or modify the original optimized capacity API.

Every original branch then receives a constant marker correction.
Its old margin is concave in late. Indeed n and s are affine, d and
eta are fixed, and raw35 is a maximum of affine functions of n.
In the complete raw357-minus-raw35 term, the identical zero-seven
block cancels. What remains is an affine mass term and nonnegative
complete sums of convex raw35 blocks. This term is subtracted in
the margin; all other late-dependent branch terms are affine.
Adding a constant correction preserves concavity, and taking the
minimum over the100 concave branches preserves it too.

Thus the fixed-zero-dual margin is concave in this late factor on
the domain where the original source bound applies. At all five
retained points it equals

    M_fixed(t)=old_common_layout_min(t)+4v/225. (VJ10)

The helper checks every fixed correction is no greater than its
original optimized correction and that all100 fixed corrections
are identical across the five points. In(VJ4), M_fixed has Jensen
difference0. At t=1, it gives up exactly v/450 of the optimized
marker improvement.

This repairs the particular late-factor obstruction. Concavity in
the other source factors, a usable bound on the complete signed
sum, and extension beyond the existing source slab are separate
unproved obligations. The optimized API itself is defined on its
broad slab Delta<=1/18, not on the unrestricted1296-vertex product.

The [helper](../../frontier/source-budgets/heavy_margin_vertex_obstruction.py) and
[certificate](../../certificates/source_norms/source-budgets/heavy_margin_vertex_obstruction.json)
retain the original source pins, exact values, geometry guards,
active duals, and both Jensen differences. The result is an
ordinary counterexample and a fixed-dual lemma, not Lean verification.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/heavy_margin_vertex_obstruction.py --check
```
