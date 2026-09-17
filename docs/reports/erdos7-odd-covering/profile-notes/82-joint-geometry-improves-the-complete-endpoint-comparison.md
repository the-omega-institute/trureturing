[Index](../marked_head_profile.md) · [Previous complete comparison](79-complete-deletion-improves-the-endpoint-comparison.md) · [Fifth hinge](78-a-common-seven-head-uniformly-improves-the-endpoint-fifth-hinge.md) · [Joint mean](80-joint15-25-75-forces-another-uniform-linear-gap.md) · [Common square](81-complete-pure3-deletion-sharpens-the-common-square.md)

# Joint geometry improves the complete endpoint comparison

For actual families approaching source404, carrier(0,1) and surviving
mass S=D=3/20, the complete AP comparison satisfies

    N<=35.7365346421544...,
    d>=12487883191877/160166043056250
      =0.07796835679764705...,
    C0+N/d<=479.9407720451339... .                    (JG1)

The comparison retains every numerator cost, independent original
test residue, signed mass term and infinite auxiliary tail. These
are uniform endpoint bounds on one actual source. They do not
update the whole-source-domain global K bound, reach threshold403,
or resolve unrestricted Erdos #7. No Lean verification is claimed.

| Uniform endpoint comparison | Upper bound |
| --- | ---: |
| Profile70: original mean, common square and scalar survival | 487.3421133369318... |
| Profile79: complete pure3 deletion in the mean | 486.7678681333996... |
| This result: joint mean, common square and fifth hinge | 479.9407720451339... |

Each row retains its own stated hypotheses and source inputs. The
new comparison strengthens the earlier bounds; it does not assert
that any of them is attained by an actual family.

## 1. Three uniform constraints apply to each original test

For any complete original357 load A, use

    L=238/375,                 integral A dmu<=L,
    Q=508716559089313/111663855622800,
                               integral A^2 dmu<=Q,
    U5=30941653/194481000,      integral(A-5)_+ dmu<=U5.

The first is profile80's joint15/25/75 theorem. The second is
profile81's disjoint pure5 square-pair correction and conversion
of the retained rational layout slack. The third is profile78's
common zero-seven and positive-seven head theorem. Keep

    U4=2701424/12403125

from profile53. All four estimates are uniform in A, so each
independently labelled numerator or survival test can use them.
The proofs do not require the different tests to have a common
maximizing residue choice.

## 2. The numerator keeps all52 old majorants and their min branches

Retain the54 scalar costs and all52 all-load rational majorants
of profiles65 and79. Set b0=L and b1=Q while keeping the other
52 original upper bounds. For each target cost f_i use

    cost_i=min(b_i,alpha_i*D+sum_j w_ij*b_j),
    f_i(v)<=alpha_i+sum_j w_ij*f_j(v), w_ij>=0,

for every positive integer v. The existing verifier checks each
majorant through its full eventual polynomial tail. This step
does not assume that a finite load window captures all values.

The complete positive-cost expansion stays

    N=r*D+sum_i beta_i*cost_i+c_square*Q.              (JG2)

Here r<0 and is retained at the fixed actual mass D; every beta_i
and c_square is positive. The coefficient c_square includes the
complete transformed-square complement and the raw81 square tail.
Thus the gain from profile79 is exactly the sum of the weighted
cost decreases plus c_square times its square decrease. The
checker evaluates both expressions and obtains the numerator
in(JG1). No old min branch is discarded.

The fifth-hinge estimate is used in survival below. This consumer
does not claim to have optimized new numerator dual coefficients
using U5 as an additional input. The52 existing majorants remain
valid and supply the stated guarantee.

## 3. Mean and fifth-hinge gains enter different terms of one denominator

Use the complete AP11 expression of profile67:

    d>=D-U4/6-(1/7)*sum_(n>=1)pn*n*U(5/n),
    p1=28/33, pn=50/(3*11^n) for n>=2.

For n=1 use the new U5. For n=2,3,4 use the same all-load
interpolation

    U(t)=(4-t)*(L-D)/3+(t-1)*U4/3, 1<=t<=4.

For every n>=5 the full tail is affine, because loads are at
least1: n*h_(5/n)(v)=n*v-5. Summing it exactly gives

    d=(945008/922383)*D-(45253/1844766)*L
                         -(346061/1844766)*U4-(4/33)*U5.
                                                               (JG3)

This is the positive denominator in(JG1). Relative to profile79,
its increase is exactly

    (45253/1844766)*(16/25-L)
        +(4/33)*(2028798479/12155062500-U5).           (JG4)

The first change comes from the mean constraints on the n>=2
terms; the second comes from the independent n=1 fifth hinge.
They are different terms of the same physical comparison, so
their gains can be added. No deletion measure is subtracted
again from either already bounded cost.

The exact count-tail expansion and coefficient expression(JG3)
agree. Since d>0, applying(JG2) and(JG3) with the unchanged C0
gives the quotient in(JG1). A denominator belonging only to one
chosen witness is never substituted here.

## 4. Revised abstract laws delimit the remaining scalar information

Let W be profile67's law supported on{1,4,7}. Move mass

    (1157/1800-L)/3=73/27000

from load4 to load1. The resulting W'' has positive masses,
total mass D, mean L and fourth-hinge integral U4. Define V'' by

    V''(9)=U5/4, V''(1)=D-U5/4.

It has fifth-hinge integral U5 and mean D+2*U5<L. The checker
verifies all57 revised scalar inequalities for both laws: the
54 cost bounds with new L,Q, and the native5/2,4,5 hinge bounds
with new U5. All114 slacks are nonnegative. In particular the
new fifth-hinge constraint does not invalidate W'' and the
stronger square constraint holds for both laws.

W'' attains the interpolation at every threshold5/n, n=2,3,4,
and the affine n>=5 tails. V'' attains the n=1 fifth hinge.
Give an abstract pair of load coordinates mass W''(i)*V''(j)/D;
its two marginals are the required raw mass-D laws. Use the
W'' coordinate for the fourth hinge and every n>=2 AP11 test,
and V'' for the n=1 test. This attains(JG3) in precisely this
57-constraint scalar relaxation.

Thus the old W and V are excluded by actual geometry, but the
new scalar relaxation still has an exact boundary. No actual
congruence realization of W'' or V'' is claimed. Additional
common-source constraints, stronger numerator inequalities or
a different complete comparison remain possible. Scalar
survival sharpness is not an optimality claim for the actual
quotient in(JG1).

## 5. Reproduction and scope

The [checker](../frontier/endpoint_joint_geometry_ratio.py) pins
the three new geometric inputs and the existing all-load cost
library. It verifies52 majorants, both full AP11 expansions,
the signed complete numerator, and114 revised feasibility slacks.
The [certificate](../certificates/source_norms/endpoint_joint_geometry_ratio.json)
retains all rational costs, coefficients, tails and scalar laws.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_joint_geometry_ratio.py --check
```

The endpoint limit uses the complete tail controls in78,80,81
and the existing comparison passage in79. The finitely many
cost coefficients pass to limsup, while the AP11 affine remainder
is controlled by the same uniform first moment. This retains
arbitrary finite original exponent heights and changing residues.
