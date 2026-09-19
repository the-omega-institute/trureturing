[Index](../marked_head_profile.md) · [Actual source deficits](39-source-deficits-through-one-actual-survivor-mass.md)

# Source-barrier saturation leaves a structural gap

Keep all comparison formulas, source parameters, original-label inventories
and complete exponent tails of profile39 fixed. Allow its47 comparison
constants to increase independently from their current values:41 linear
costs, five exceptional quadratic costs, and the square-source barrier45.
At each of the six controlling parameters398,410,422,616,628,640, the maximum
further decrease in the joint row J and combined row K=J+T13(81) is exactly

    epsilon=68782571167036370194555899862835
            /202252668310750704832347357225888
           =0.3400823917010357... .

A single globally fixed vector of47 constants attains all six limits. The
square barrier45 is already saturated. The gain and required coefficient
budget in the remaining directions are:

| Cost group | Already saturated | Maximum additional J/K gain | Extra coefficient budget |
| --- | ---: | ---: | ---: |
| 41 linear costs | 15 | 0.04290300263942107 | deltaH41=0.5576248695016868 |
| Five quadratic costs | 1 | 0.2971793890616146 | deltaH16=4.691741391947358 |
| Square-source barrier45 | 1 | 0 | 0 |

Both coefficient costs are charged in these gains: the joint numerator
uses `H=AC*H16+H41`, with `AC=2371/2880`. They are not gains in bare source
margins. The exact budgets are

    deltaH41=6376577573755210678594429
              /11435246027411842460424600,
    deltaH16=189030337939057/40290016466700.

The resulting control-row limits are

    J_infinity=9540172912107709073250238188651705087161011
               /22090697499491985454000143343406864568000
              =431.8638156322181...,
    K_infinity=108338334924419323519151218642321457614524149
               /205127905352425579215715616760206599560000
              =528.1501545988377... .

These are lower limits of this fixed certificate's upper-bound expressions,
not lower bounds for actual covering families. No claim is made that an
original congruence family attains the relaxation. They are also not new
complete-domain upper bounds: this experiment verifies the six controls,
not every other vertex and fallback at the proposed constants.

Even before adding the complete finite-core error, the relaxation retains

    K_infinity-403
      =25671789067391815095217825087958197991844149
        /205127905352425579215715616760206599560000
      =125.15015459883773... .

Increasing these same47 constants cannot cross the required inequality.
This conclusion excludes only constant increases in the fixed comparison
formulas. Stronger source/deletion inequalities, common carrier information,
changed source parameters, other cost functions or a different proof model
are outside its scope. It is not an Erdos7 counterexample or a negative-Q
proof. Constants below the current values with differently clipped floors
are also outside the stated optimization domain.

## Exact finite saturation mechanism

Fix a parameter theta and one original test. Its signed raw margin is

    m_C(theta,b,c)=C*s-U(theta,b,c)-W(C,theta,b,c)/5,
    m_C(theta)=min_(b,c) m_C(theta,b,c).

The original zero5 layout b and first positive5 layout c remain independent
of all other tests. The source term U is independent of C. It retains the
complete positive5 tail, and for the quadratic and square costs also the
existing original-layout Jensen correction.

The cofactor cap W is a sum of eight positive multiples of finite maxima
of affine functions of C. Include the empty-root and empty-cell alternatives0
in its first two maxima. For `k_j=C-f(b_j)`, the final deep weights are
13/243 and1/486 for the five-cofactor linear comparison, or40/729 and1/1458
for the six-cofactor quadratic and square comparisons. Both pairs sum1/18.
The eventual total slope is therefore exactly

    cap0=R(n)+max(n)+max(d)/18
         +(sum(w)+R(w)+max(w))/36+1/72
        =5(s-D),
    w=9*eta, R(v)=max(sum(v[0:2]),sum(v[2:5])).

For each finite maximum, its eventual line has the largest slope; among
lines with that slope choose the largest intercept. Let beta_(b,c) be the
sum of these eventual intercepts with the cap's original weights. Then

    F_(b,c)(C)=U+W(C)/5-C(s-D)

is continuous, piecewise affine, nonincreasing, and eventually constant at

    L_(b,c)=U+beta_(b,c)/5.

The independent-layout envelope is

    C*D-m_C(theta)=max_(b,c) F_(b,c)(C).

There are100 allowed layout pairs. Its exact limit is consequently

    L(theta)=max_(b,c) L_(b,c).

A finite maximum of eventually constant functions becomes constant after a
finite increase. Its least saturation point at or above the current C0 is

    Cstar=max_(b,c) inf{C>=C0 : F_(b,c)(C)<=L(theta)}.

Each first crossing is found by solving a linear equation on the exact
upper hulls' finitely many rational intervals. At their maximum every
branch is at most L, while a branch with eventual value L establishes
equality. Below that maximum an uncrossed branch exceeds L, proving
minimality. This is an exact finite calculation, not large-C extrapolation.

The construction applies independently to all47 costs. Every consumer
weight is positive, so its weighted sum has the sum of these costwise
limits as its exact infimum. The same vector of least saturation constants
works at all six controls. There is no choice of constants depending on
the actual forbidden family or parameter theta.

## Complete cost and normalization accounting

For a linear direction, U is the existing zero7 remainder, original zero5
source contribution, its deep bound and the retained positive5 source.
The eventually affine tail is evaluated by exact geometric sums. The
weighted raw improvement of all41 directions is

    deltaM_linear=6376577573755210678594429
                   /2058344284934131642876428000.

For each exceptional quadratic direction, U is the same original source
formula from `shared_source_deficits.aggregate`, including its complete
quadratic tail and `-(4/25)*curvature*distance(eta,b,c)` correction. The five
unweighted raw gains sum to

    deltaM_quadratic=189030337939057/7252202964006000.

At all six controls the source-square100-branch envelope at45 already equals
its exact limit. Thus increasing that barrier cannot improve either its
quadratic complement in J or its contribution to T13(81). This is verified
by the six-cofactor upper hulls, not inferred from two large sampled values.

All six controls have `Delta=15447272417/213929100000`. Therefore

    epsilon=(deltaM_linear+AC*deltaM_quadratic)/Delta.

The square barrier has zero remaining gain, so T13(81) is unchanged when
these limits are attained, and J and K have the same total improvement.
The extra five-quadratic budget is charged to H16, the extra linear budget
to H41, and the corresponding raw margins are retained before division.
The four fixed-target endpoint coefficients remain positive at the candidate
limits. This sign check does not substitute for a new complete-domain check.

The actual-S interval certificate controls the retained possibilities
`D<=S<=s`. Its maximum is at least its expression at D. Allowing coefficient
budgets that require using the s endpoint cannot lower this necessary
D-row expression. Thus the computed limit remains an obstruction inside
this interval relaxation even if positive-D-coefficient budgets are ignored.
This argument does not assert that an actual family attains S=D.

## Reproducible exact experiment

Run from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/frontier/source_barrier_saturation.py

The default computes and verifies the result and prints exact fractions.
An optional `--output PATH` writes full JSON with all47 least constants and
all six independent direction tables. It uses current repository scripts
and inputs, checks the published certificate's direct source pins, and
reconstructs each linear starting margin, the square starting margin, the
five quadratic source formulas, and their complete published Mquad sum.
It does not replay all mathematical ancestors.

The experiment checks28200 original layout caps, exact eventual slopes,
rational hull crossings, the unchanged full exponent tails and one common
saturation vector at all six controls. The retained program and this
boundary do not replace profile39's complete certified constants. The
result identifies a limit of constant tuning and a concrete reason to
change the comparison information. Unrestricted Erdos7 remains open.
