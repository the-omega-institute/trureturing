[Index](../marked_head_profile.md) · [Original source bridge](195-the-complete-source-comparison-extends-beyond-the-old-radius-domain.md) · [Global affine comparison](213-the-affine-j-reserve-enters-the-complete-global-comparison.md)

# The source bridge covers a larger complete residual strip

The complete K-source rectangle can be enlarged to

    sigma<=1/12, rho<=1/2300, r<=5rho.

On this entire rectangle, in both K orientations, the original52-cost
comparison gives

    K<=14958107545487190422212589049902660267009489941902726569
        /29504547108544861722422979070633612621270046473200000
      =506.97634810178624...<507.

This preserves all original independent labels, every numerator cost,
the five survival objectives, the signed actual mass and all infinite
tails. It enlarges195's residual radius1/3000 without invoking that
result outside its domain. It is a full rectangle bound; it is not an
estimate at one favorable boundary point. A complete global join is a
separate obligation. Unrestricted Erdos7 remains unresolved.

## 1. Prove the enlarged source and packing guards

Put d=1/12, R=1/2300 and rbar=5R=1/460. The source concentration and
availability bounds are unchanged:

    loss=d/(1-d)=1/11, Delta=loss/4=1/44,
    availability=3/136<=Delta, z<=37/48<4/5.

The five lower bounds for the actual packing gaps are

    9/92, 1579/24840, 95/4968, 71861/3378240, 91/3105.

Thus G=95/4968>0 and R/G<1/5. They apply throughout the rectangle:
the source envelopes are taken at sigma=d and the actual residual
losses at r=rbar. The positive source-polynomial conditions from the
general134/152/157/158 proofs remain valid throughout[0,1/12].
The helper checks their endpoint values and the required signs,
both first-label forcing conditions and both enlarged pre-cap tables.

The source ratios remain

    tbar=13/4, Cbar=370/81, kbar=71/34.

The larger wrong-slot range still satisfies

    max((1/2+d/18)/(5G),65/9)=65/9.

Consequently the original169 one-residual heavy prices pay both the
marker and every actual slot movement. The same actual rho is used
throughout, with no independent artificial r cutoff.

## 2. Transport every old original head, with complete tails

The source radius is unchanged. The finite source LP keeps its three
budgets and only enlarges capacities. At the three corresponding
defect vertices, write c_i for old capacities, dc_i>=0 for their
increments, a_i for the old objective coefficients and a'_i for the
new coefficients. The all-layout transport inequality is

    LP_new-LP_old
      <=sum_i dc_i*max_layout(a'_i)
        +sum_i c_i*max_layout(a'_i-a_i).

To see the capacity part, clip a new feasible vector coordinatewise
to the old capacities. It remains feasible for the old budgets;
the removed mass in coordinate i is at most dc_i. The second term
bounds coefficient change on this clipped vector. Coefficients and
the retained coefficient increments are checked nonnegative.

Every selected-cylinder correction is transported with its same
original operator weights. Each operator's increment is bounded
before taking its maximum. All original layouts and labels remain
independent. The factorial head increases by at most

    10199/3047500,

as checked across all12500 original factorial layouts. Mean references
are unchanged, and their seven coordinate prices pay the change of
the same residual at each corresponding vertex.

These uniform inequalities transport all26 original objectives from
the pinned195 certificate, which contains9750000 original-head
evaluations and312 independent rational comparisons. The new helper
also checks3120 complete finite branches against the general transport
inequality. These3120 checks are arithmetic cross-checks; the uniform
inequality supplies the unenumerated-layout proof.

Complete factorial, selected, exponent and mean tails are then
recomputed on the new rectangle. Shared residual support is maximized
over all three defect vertices. Any competing complete support bounds
are minimized only after they cover the entire common domain.

## 3. Rebuild the complete signed comparison

The pure-five common residual bound, full square, shallow H1, both
heavy tests, all11 mean costs,28 simple costs,9 quadratic costs and
both retained raw81 tests are reassembled. The independent cost
indices are exactly0 through51, once each.

With A=53/360 and cE=1-1/614922, the full denominator at the actual
mass floor is

    D=cE*A-shared_survival_loss-H1/55902
     =21522064217545954190353/285478265840170677120000
     >0.

The surviving actual-mass coefficient is positive. Hence the quoted
bound applies for every actual S>=A, not only S=A. The old full count
tail and all source exponent tails are retained. No original test
has been replaced by a repeated congruence label or an independently
sampled source.

The bound is an ordinary mathematical comparison supported by an
exact rational certificate, not a Lean or frozen-state claim.

## 4. Reproduce the exact certificate

From the repository root:

```sh
python3 docs/reports/erdos7-odd-covering/frontier/expanded_bridge_residual_comparison.py --check
```

The helper verifies the complete pinned input closure, all new guards,
all26 transported objectives, the3120 independent branch comparisons,
all52 numerator labels, both signs needed for the actual-mass reduction,
and exact equality with the stored certificate. Split certificate bytes
are read and written through the existing certificate IO interface.
