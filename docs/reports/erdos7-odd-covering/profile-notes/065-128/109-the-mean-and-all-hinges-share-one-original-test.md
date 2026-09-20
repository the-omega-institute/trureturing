[Index](../../marked_head_profile.md) · [Complete deletion geometry](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Complete hinge generator](98-a-complete-stop-loss-profile-strengthens-the-whole-face-comparison.md) · [Common cost layout](104-one-test-layout-couples-the-hinges-of-each-complete-cost.md) · [Complete quadratic tail](108-a-complete-second-factorial-tail-improves-four-quadratic-costs.md)

# The mean and all hinges share one original test

Combining the first-difference term with every curvature term before
taking the common head and selected-cylinder maxima improves11 original
linear-growth cost bounds. Keeping108's complete quadratic bounds gives

    N<=35.147145027755249208617911054604...,
    C0+N/d<=463.623378713598603010037641655167... .   (MH0)

The complete numerator decreases by

    6077664218170899372619/352939692204069211741500
      =0.017220121036023352246548943498... .

The comparison improves108 by0.216569430729013488215357274758....
The full101 denominator d is unchanged. The threshold-one source bound
must
retain the complete deletion information of72 and75. Its numerical
bound is not obtained by inserting the previously optimized first
moment as a coefficient in a different source LP.

The ordinary theorem here applies on both complete actual K-control
beta faces, with r=rho=0 and mass D=53/360. Every cost keeps its own
original test. All original exponent tails are retained. The exact
arithmetic checker is
[whole_cost_mean_stop_loss.py](../../frontier/comparison-bounds/whole_cost_mean_stop_loss.py),
with [certificate](../../certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json).
These are ordinary source inequalities and exact LP certificates, not
Lean verification or an off-face global comparison.

## 1. Threshold one has a valid common source bridge

For the same original complete357 test A used by104, write

    A=B+Y+R+Z,
    B=1+I3+I9+I5+I15+I45.

Here Y contains every old zero-seven label outside this six-label
head. The retained positive-seven family R contains all unit7^e
labels and the original21 and35 labels. The remaining positive-seven
labels form Z. The complete surviving tail bounds of98 are

    integral_mu Y <= R0=163/1800,
    integral_mu Z <= Zplus=779/12600.               (MH1)

Because B>=1, the first hinge h1(v)=(v-1)_+ has the exact identity

    h1(A)=(B-1)+Y+R+Z.

The original raw seven bridge gives

    integral_mu R <= integral_Lambda g_(1,m),
    g_(1,m)=1/5+6*m/35,
    m(c,s)=1_(ROOT(c)=T)+1_(s=F),                  (MH2)

with the same original21/35 root and first-five projection T,F as in
every other hinge. This is98's bridge at t=1. It is constant in the
old load v>=1, so the selected old prefix has length k1=0. All four
labels25,27,75,81 are paid in R0 for this threshold.

The established U1=L-D=443/900 follows from75's separate cylinder
caps. It is not the maximum of(MH2) plus the uncorrected head LP.
The following retained deletion supplies a stronger, compatible
threshold-one head before it is combined with other thresholds.

## 2. Complete extra deletion on each original head event

Use the canonical orientation with thinned root0 cell0 and unthinned
root0 cell1. As in75, the pure5 complement in the source slots
(P,A,B,Q,H) is

    q=(0,1/5,1/5,3/20,1/5),
    eta=(1/18,1/9,1/9,1/9,1/9).

The symbol B in the slot list denotes the first beta slot; the head
load B above is a function. The source tables use these same five
slot indices throughout.

The density w used by98 includes exactly the four complete forbidden
cofactor families3,9,5,15. Saturation gives equality of actual and
virtual deletion measures. Hence, after these four families, any
additional collection of distinct original cofactor families may
still be subtracted from w*Lambda when integrating a nonnegative
head function.

The complete forbidden pure3 family3^a,a>=3 is such a collection.
By75 its support is on root0; its whole mass is1/120, and its
five-coordinate marginal on any measurable F is q(F)/90. In
addition, all forbidden27 labels lie in cell1. The saturated27
cylinder has full ternary Haar mass1/27 and the exact pure5
complement section. Summing its complete seven depths gives

    deletion27(cell1)=1/180,
    deletion27(cell1 x F)=q(F)/135.                (MH3)

Therefore, for the original head layout

    layout=(r3,c9,s5,r15,s15,c45,s45),

the pure3 family contributes at least

    C3(layout)=1_(r3=0)/120 + 1_(c9=1)/180
                +q[s5]/90 + 1_(r15=0)*q[s15]/90
                              +1_(c45=1)*q[s45]/135             (MH4)

to the integral of B-1 against its deletion measure. Each term
concerns a different head indicator. Their supports may overlap:
linearity of the integral counts a point once for each indicator
present in B-1. No disjointness among these test events is assumed.

There is a second collection of extra forbidden families,5^b and
3*5^b with b>=2. These are distinct from the pure3 collection and
from the four shallow families already used in w. The saturation
argument of72, applied to each original depth-b cofactor, gives
source-free cylinders, globally for5^b and on root1 for3*5^b.
Consequently their complete deletion on a ternary event T is

    [eta(T)+eta(T intersect root1)]/100,
    1/100=(1/5)*sum_(b>=2)5^-b.                   (MH5)

The factor1/5 sums all original positive seven depths. In particular
the b=1 families are excluded from(MH5), as required by the definition
of w. Apply(MH5) only to the head's pure ternary events I3 and I9;
discard its nonnegative action on the other head events. It supplies

    C5(layout)=[(1+r3)*eta(root r3)
                          +(1+ROOT(c9))*eta[c9]]/100.           (MH6)

Let C=C3+C5. From the two collections of original forbidden families
and the unchanged four-family density w we obtain

    integral_mu(B-1)
       <= integral_Lambda w*(B-1)-C(layout).       (MH7)

This inequality concerns only the threshold-one head. The other
hinges continue to use their original valid source bounds; the
peeled tail terms in(MH1) continue to use their existing surviving
caps. Those tails contain different original test labels from B.
The extra deletion in(MH7) is not deducted again from either tail.

Combining(MH1),(MH2),(MH7) proves the common threshold-one bound

    H1 <= R0+Zplus
           +U_L(w*(B-1)+g_(1,m))-C(layout).       (MH8)

Here U_L is the same three-group source LP as98. The correction is
a bound for every actual source on the stated face, for this fixed
original head. It can be subtracted after taking that source LP
upper bound. Its value must remain inside the maximum over layouts.

## 3. One positive combination covers the entire original cost

Write the exact affine-tail expansion of one original cost as

    f(v)=f(1)+sum_(t=1..8)a_t*h_t(v),
    a1=f(2)-f(1)>=0,
    a_t=f(t+1)-2*f(t)+f(t-1)>=0, t>=2.             (MH9)

The function h1(v) is v-1 on this positive integer domain. All
finite values and the entire affine tail in(MH9) are the original
ones verified in98.

Set k1=0 and k_t=min(t-1,4) for t>=2. With98's bridge functions f_t,
form the positive head and selected-cylinder objectives

    H_f(B)=sum_t a_t*f_t(B),
    Z_(f,i)(B)=sum_(t:k_t>=i)a_t*[f_t(B+i)-f_t(B+i-1)].

For t=1, f1(v)=w*(v-1)+g_(1,m). For t>=2 the functions are exactly
those of104. Combining the bounds on the same original test before
integrating gives

    integral_mu f(A)
      <= f(1)*D + sum_t a_t*(Zplus+R_(k_t))
           +max_(layout,T,F) [ U_L(H_f(B))
                       +sum_i P_(M_i)(Z_(f,i)(B))
                                      -a1*C(layout) ].          (MH10)

The four selected old labels keep the order25,27,75,81. Each
threshold either pays one label in its selected operator or in its
peeled cap remainder, exactly as in104. Threshold one pays all four
in R0 and contributes nothing to the selected operators. All head
and selected objectives remain nonnegative; the fixed correction is
applied once to their combined upper bound.

Unlike104, a cost with only a2 as nonzero curvature generally has
both a1 and a2 in its combined objective. The mean and curvature
need not admit the same maximizing original head or source mass
allocation. Formula(MH10) retains that constraint. The calculation
takes its minimum with the previously proved bound for each cost;
no uniform superiority of(MH10) over the old first-moment estimate
is assumed.

The source LP keeps the entire root1 beta mass in its original
group constraint. The correction C depends only on the fixed eta,
the complete pure5 complement and the original head choices. All
three first-beta cell permutations preserve it. The root0-cell
exchange transports the same argument to the other actual K face.
No separately optimized beta vertices are interpolated.

The complete geometric sums in(MH1)--(MH5) and98 justify passage
from finite prefixes to infinite original label families. All
coefficients in(MH9) are nonnegative, and their number is finite.
Different AP costs may have independent original test residues.

## 4. Exact source maxima and the complete consumer

The checker verifies each original cost expansion. Explicit original
head/projection choices exclude the proposed objectives for30 costs:
their fixed values already equal or exceed the retained upper bounds,
so the full maxima cannot improve those bounds. This includes costs0
and16, all27 previously single-curvature costs, and the affine cost.
The new two-threshold representation does not improve those27 costs
within the stated generator. This is an exact obstruction for this
generator, not a claim that their true cost bounds are optimal.

In particular the single choice

    layout=(0,1,2,1,2,3,2), T=1, F=4

excludes all27 single-curvature costs. For the affine cost, the choice
layout=(1,1,2,1,2,3,2),T=1,F=4 already gives897/1400, which exceeds
the retained first moment1151/1800. The old first moment is therefore
retained throughout this consumer.

The remaining11 indices are

    1,2,7,10,17,18,23,26,32,33,36.

Each primitive positive hinge vector is checked over all12500 original
heads and all10 original21/35 projections, for1,375,000 new LP
evaluations. The source LP has a feasible primal and matching dual
at each evaluation. All11 complete maxima improve their retained
cost bounds.

The consumer retains108's five quadratic and six raw81 bounds. It
takes the per-cost minimum with the new linear-growth bounds, then
makes one simultaneous substitution into the existing52 all-load
majorants. The complete signed numerator remains

    N=r_mass*D+sum_(i=1..52)weight_i*cost_i
                                      +c_square*(374/75),
    r_mass<0, weight_i>0, c_square>0.

The complete101 AP11 denominator, including its original probability
law, first moment and full affine tail, is retained. The resulting
numerator and comparison upper bound are exactly

    N=138926206317862779142362029175860155778966279743
        /3952702451597549034231858077472656250000000000,

    C0+N/d=715888291617021475640539484626464822301802543314859
              /1544116031429162385179130957682216048828125000000.

The all-load majorant substitution gives zero additional gain here.
Thus every improvement in(MH0) is the direct gain from the11 costs,
counted once relative to108. The scope remains the saturated faces
and does not supply a new global K bound or a proof of unrestricted
Erdos7. The comparison remains above403.

The helper's MeanHead.prepare accepts any nonzero nonnegative
rational combination of thresholds1 through8. MeanHead.objective
retains one layout and its correction throughout the calculation.
With coefficient a1=0 it is exactly104's original common operator.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/whole_cost_mean_stop_loss.py --check
```
