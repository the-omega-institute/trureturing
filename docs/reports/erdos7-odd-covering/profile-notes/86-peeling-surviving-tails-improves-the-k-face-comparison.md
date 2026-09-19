[Index](../marked_head_profile.md) · [Actual surviving cylinder caps](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Common seven bridge](83-common-seven-hinges-on-both-complete-k-control-faces.md) · [Complete face comparison](84-a-complete-comparison-on-both-k-control-faces.md)

# Peeling surviving tails improves the K-face comparison

On both entire actual K-control beta faces, with the same saturated
mass D=53/360 as profiles75,83 and84, every independently labelled
complete357 test A satisfies

    integral_survivor(A-4)_+<=938213/4630500
                             =0.2026159162077529...,
    integral_survivor(A-5)_+<=1523903/9724050
                             =0.156714846180346666... .       (ST1)

The first face has vertices398,410,422 and carrier(1,1); the
second has vertices616,628,640 and carrier(1,0). These inequalities
hold for arbitrary source beta distributions on the actual faces,
independent original test residues and all exponent tails. They
also hold as limsup inequalities for the approaching actual
families considered in the preceding face results.

Keeping the entire numerator and first moment of profile84 yields

    N<=36.325086046320646686969...,
    d>=40455251803/517708422000
       =0.07814292772505833...,
    C0+N/d<=486.448557462558278607663... .                         (ST2)

The previous whole-face comparison was486.90427923605119... .
The improvement uses actual surviving tail caps before the raw
seven-prefix estimate. It does not change the global bound
509.4606868254497..., provide an off-face neighborhood, reach403,
or resolve unrestricted Erdos #7. These are ordinary proofs
with exact rational checks, not Lean results or sharpness claims.

## 1. Separate the remaining old load on the actual survivor first

Write h_t(v)=(v-t)_+. Retain the six-label zero-seven head

    B=I_1+I_3+I_9+I_5+I_15+I_45.

Let X be the selected additional zero-seven load, Y all other
zero-seven labels, R all positive-seven unit labels together with
the independently labelled tests21 and35, and Z every other
positive-seven label. Thus A=B+X+Y+R+Z, and all four added loads
are nonnegative. Choose

    X=I_25+I_27+I_75               for t=4,
    X=I_25+I_27+I_75+I_81         for t=5.                (ST3)

The hinge is1-Lipschitz and increasing, so pointwise

    h_t(A)<=h_t(B+X+R)+Y+Z.                              (ST4)

Integrate(ST4) on the actual surviving measure. The Y term is
now exactly a sum of actual surviving cylinder masses. Profile75
bounds these directly. The Z term retains profile83's complete
raw linear budget

    integral_survivor Z<=779/12600.                       (ST5)

Only after this separation apply the existing common seven bridge
to h_t(B+X+R). In the notation of profile83, with Lambda the raw35
source, mu its actual surviving marginal, w the selected-deletion
upper density, and m=I_T+I_F for the independent old projections
of21 and35,

    integral_survivor h_t(B+X+R)
       <=integral_mu h_t(B+X)+integral_Lambda g_(t,m)(B+X)
       <=integral_Lambda f_(t,w,m)(B+X),                 (ST6)

where

    g_(t,m)(v)=7^(-max((t-v)_+-m,0))/5
                          +(6/35)*max(m-(t-v)_+,0),
    f_(t,w,m)(v)=w*h_t(v)+g_(t,m)(v).

Here mu<=w*Lambda and w>=2/5. The same finite source table,
entire beta group budget, source-head LP and independent layout
choices from83 still apply. The actual density dmu/dLambda is
not substituted for w in f. In particular(ST6) never puts Y
inside the raw function g; its complete contribution was already
separated in(ST4).

## 2. Sum every remaining zero-seven cylinder on the survivor

Outside B, profile75 supplies the complete tail budgets

| Category | Actual surviving upper bound |
| --- | ---: |
| Pure3, a>=3 | 7/180 |
| Pure5, b>=2 | 1/50 |
| 3 times5^b, b>=2 | 1/75 |
| 9 times5^b, b>=2 | 1/225 |
| 3^a times5^b, a>=3,b>=1 | 1/72 |

The sum is163/1800. The corresponding individual cylinder caps
of the selected labels, valid for arbitrary residues, are

    cap25=2/125, cap27=7/270,
    cap75=4/375, cap81=7/810.                            (ST7)

Remove these labels exactly once from the complete series. The
linear bounds for Y are therefore

    R4=163/1800-2/125-7/270-4/375=41/1080,
    R5=R4-7/810=19/648.                                (ST8)

This subtraction removes assigned terms from an explicit sum of
individual upper bounds. It does not subtract an upper bound
from the unknown actual total. No label is charged both here and
among the selected finite increments.

## 3. Each old certified layout decreases by one fixed constant

For an increasing integer-convex f and ordered indicators I_i,

    f(B+sum_(i=1)^k I_i)
       <=f(B)+sum_(i=1)^k I_i*(f(B+i)-f(B+i-1)).         (ST9)

Whenever I_i=1, the earlier selected indicators have total at
most i-1, and convexity bounds its actual increment by the ith
displayed increment. Apply(ST9) to the three or four selected
labels in(ST3). These are precisely the first three or four
increment terms already certified in83. The same B,T,F must be
used in the head and every selected term.

For t=4, the old fourth increment, assigned to81, is identically
w for every common layout: B>=1 gives B+3>=4, where h_4 is affine
and g_(4,m) is constant. Its old raw cost is consequently the
layout-independent number

    P81(w)=3^-4*max_c sum_s p(c,s)*w(c,s)=71/8100.       (ST10)

The old remaining tail cost of83 was2389/81000. For t=4, remove
(ST10) from the selected terms and replace the remaining tail by
R4. For t=5 all four selected terms stay, and replace only the
remaining tail by R5. Thus every old common-layout objective
decreases by the constant

    delta4=2389/81000+71/8100-41/1080=1/3375,
    delta5=2389/81000-19/648=7/40500.                   (ST11)

These changes are independent of the head layout, the21/35
projections, and the first-beta choice. The existing exact maximum
over250000 threshold/layout choices can therefore be reused:

    U4=62639/308700-delta4=938213/4630500,
    U5=565031/3601500-delta5=1523903/9724050.            (ST12)

The certificate reconstructs the maximizing bound from the old
head LP value, the retained finite increments, and both complete
remainders. Reusing the old maximizing layout concerns this
upper-bound optimization only; actual source/test attainment is
not asserted. The exact source-cell exchanges from83 transport
the same argument to every first-beta location and to the second
complete K-control face.

## 4. Improve the denominator while retaining the entire numerator

Profile84 gives the same actual mass D, the uniform mean
L=1151/1800, the complete square bound Q=374/75, and all52
transformed-cost bounds. Retain its numerator exactly:

    N=r*D+sum_i beta_i*cost_i+c_square*Q,
    r<0, beta_i>0, c_square>0.                          (ST13)

Both complete square tails and every original signed term remain
in(ST13); no numerator deletion credit is added.

The whole AP11 denominator has the coefficient form

    d>=(945008/922383)*D-(45253/1844766)*L
                     -(346061/1844766)*U4-(4/33)*U5.   (ST14)

The AP11 probabilities are p_1=28/33 and p_n=50/(3*11^n)
for n>=2. For n=2,3,4 retain the preceding interpolation between
L-D and U4. For n>=5 retain the exact complete affine tail,
whose zeroth and first moments are

    sum_(n>=5)p_n=5/43923,
    sum_(n>=5)n*p_n=17/29282.                          (ST15)

Substitution of(ST12) in(ST14) gives the denominator in(ST2).
Relative to84 its positive gain is exactly

    (346061/1844766)*(1/3375)+(4/33)*(7/40500).         (ST16)

The checker verifies(ST14) both from these coefficients and from
the complete AP11 expansion. N and the new denominator lower
bound are positive; raising the denominator while keeping N and
C0 fixed proves(ST2).

## 5. Completeness and exact reproduction

Apply the pointwise argument to finite label families and pass to
the increasing complete loads. Every separated infinite sum is
dominated by its displayed complete geometric budget. The
uniform tail controls in75 and83 give the same limiting argument
for families approaching the saturated faces. No finite-height
test or common maximizing residue is assumed.

The [checker](../frontier/k_face_surviving_tail_ratio.py) pins the
75,83 and84 helpers and certificates, verifies all inherited
artifact hashes, the complete surviving tail arithmetic, every
possible fourth-increment entrance, the two layout-independent
shifts, the unchanged full numerator and both AP11 expansions.
It consumes83's already certified complete layout maximum and
dual digest without repeating that enumeration. The
[certificate](../certificates/source_norms/k_face_surviving_tail_ratio.json)
contains the exact rational bounds and retained coefficients.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/k_face_surviving_tail_ratio.py --check
```

The outstanding global obligation remains control of actual
sources off the saturated faces. The present estimate cannot be
inserted into a relaxed vertex table without a valid extension
argument.
