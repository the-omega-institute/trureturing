[Index](../marked_head_profile.md) · [Complete numerator](84-a-complete-comparison-on-both-k-control-faces.md) · [Surviving-tail denominator](86-peeling-surviving-tails-improves-the-k-face-comparison.md) · [Whole-face linear vectors](95-vector-marked-gains-hold-on-the-entire-actual-k-faces.md) · [Whole-face quadratic vectors](96-quadratic-cell-vectors-retain-deep-deletion-on-the-k-faces.md)

# Vector source margins improve the complete face comparison

On both complete actual K-control beta faces with r=rho=0 and saturated
mass D=53/360, the linear and quadratic vector source estimates improve
the complete comparison to

    N<=36.28760220780042157219483072305...,
    d>=40455251803/517708422000
       =0.078142927725058334090612881704...,
    C0+N/d<=485.9688744047118926390309286704... .       (VC1)

The preceding complete face bound from86 was
486.4485574625582786076633520952..., so the decrease is
0.47968305784638596863242342477.... The denominator is retained exactly.
The numerator retains all52 original cost terms, its negative mass
coefficient, both complete square complements, and all exponent tails.

This is a uniform result on the actual saturated faces, including every
allowed beta distribution and both root0 orientations. It supplies no
off-face neighborhood or new global K bound, remains above403, and does
not settle unrestricted Erdős7. The proof is ordinary mathematics with
exact rational checks, not a Lean result or a sharpness claim.

## 1. Consume absolute whole-face margins once

The survivor mass is exactly D=53/360. An absolute margin lower bound
M_i for cost f_i with its original barrier C_i therefore gives

    integral_survivor f_i(A)<=C_i*D-M_i.              (VC2)

For the41 linear costs,95 proves M_i=m_i+g_i uniformly on all actual
first-beta triangles, with the fixed carrier and r=0. Setting rho=0
removes its shared residual penalty. The five quadratic costs use96's
uniform absolute margin lower bounds. Their proof applies directly to
the same triangles and symmetry images. No claim that the old quadratic
minimum is constant in beta is needed for(VC2).

All these bounds concern the same original cost functions and surviving
measure used by84 and86, with independent original test labels and
complete tails. Let B_i be the52 cost upper bounds already retained by
86. For each of the46 transformed costs form

    B_i^direct=min(B_i,C_i*D-M_i).                    (VC3)

The six raw81 cost bounds are retained at this step. The new vector
bounds improve only seven of the already strengthened linear bounds:
indices0,1,7,16,17,23,32 in the original41-cost inventory. Their net
weighted numerator improvement is

    8627577205613326039286845075631489
    /720420499726946075006749800000000000
    =0.0119757519516495603809585288476... .           (VC4)

The41-cost gain0.04074584252... in95 was measured against its specified
old carrier margins; that full number cannot be deducted again from84's
already improved numerator. Formula(VC3) prevents that duplicate credit.

Among the five quadratic costs, only00,01,10 improve the current bounds.
The bounds from84 remain stronger for02,20. Their combined weighted
numerator improvement is

    10407081038453971/483480197600400000
    =0.0215253511728219763173416706022... .           (VC5)

The complete square cap Q=374/75, its comparison coefficient and the six
raw81 bounds have not been replaced by a truncated quadratic estimate.

## 2. One simultaneous substitution propagates the valid improvement

The52 existing all-load majorants have the form

    f_i(v)<=alpha_i+sum_j lambda_ij*f_j(v),
    lambda_ij>=0, v in the positive integers.        (VC6)

The constraint inventory includes the first and second moments as well
as all52 costs. The total load A is at least1 because the original
unit label is included. The verifier checks(VC6) on its finite prefix
and exact complete affine or quadratic tail; no numerical solver or
finite-height approximation supplies the inequality.

After integration, use the exact mass D for the possibly negative
alpha_i and the proven upper bounds(VC3) for all nonnegative multipliers.
This yields the single substitution

    B_i^final=min(B_i^direct,
                  alpha_i*D+sum_j lambda_ij*B_j^direct). (VC7)

The moment entries in B^direct are the unchanged L=1151/1800 and
Q=374/75. Every right side uses the same already proved vector B^direct;
no newly computed target is fed into another target in this step.
There is no cyclic fixed-point assumption or iteration. Applying this
same substitution to the preceding B_i alone returns B_i exactly, as
the rational check confirms.

The additional weighted numerator improvement from(VC7), beyond(VC4)
and(VC5), is

    14346221120444945311257727225730747
    /3602102498634730375033749000000000000
    =0.00398273539575357807595925657891... .          (VC8)

In total43 of the52 cost bounds become smaller:40 linear costs and the
three quadratic costs just identified. All52 terms remain in the final
numerator, including those whose upper bound did not improve.

## 3. Retain the complete signed numerator and survival denominator

Let r_mass<0 denote the original signed mass coefficient, let w_i>0
be all52 original comparison weights, and let c_square>0 be the complete
square-complement coefficient. Then

    N_new=r_mass*D+sum_(i=1..52)w_i*B_i^final
                         +c_square*(374/75).         (VC9)

No signed term is omitted or assigned a new sign. The exact difference
from86's numerator is the sum of the three disjoint improvements
(VC4),(VC5),(VC8):

    N_old-N_new
       =774990851740505588642278700390621
        /20675333219204447305678406250000000
       =0.0374838385202251147742594560287... .        (VC10)

The resulting exact upper bound is

    N_new=9179782029399638996550960877298472801218799254177
           /252972956902243138190838916958250000000000000000.

Use86's complete surviving-tail hinge estimates

    U4=938213/4630500, U5=1523903/9724050.

The full AP11 survival inequality is unchanged:

    d>=(945008/922383)*D-(45253/1844766)*L
                       -(346061/1844766)*U4-(4/33)*U5. (VC11)

The checker reconstructs(VC11) from both its coefficients and the
complete AP11 expansion, including the tail moments5/43923 and17/29282.
It reuses the certified250000-layout result behind86 without rerunning
those layouts. This is reuse of an existing complete bound, not a new
claim about an attaining source configuration.

Both N_new and the displayed denominator lower bound are positive.
Therefore decreasing N and retaining that positive lower denominator
proves(VC1), with the same offset

    C0=185694867601/8599322160.

The exact resulting comparison upper bound is

    47197499880208999734343547153150683794373898235771601
    /97120417306609665359541226329029902125000000000000.

This argument combines simultaneous uniform upper bounds for the same
cost integrals; their maximizing residue configurations need not agree
or be attainable. It does not extend the stated r=rho=0 domain.

## Reproduction

[vector_face_complete_ratio.py](../frontier/vector_face_complete_ratio.py)
pins the whole-face vector certificates,84's complete52-cost inventory
and86's complete denominator. Its
[certificate](../certificates/source_norms/vector_face_complete_ratio.json)
retains all52 bounds, every all-load majorant and complete tail check,
the signed coefficients, and the separate direct and propagated gains.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/vector_face_complete_ratio.py --check
```
