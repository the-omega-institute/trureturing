[Index](../../marked_head_profile.md) · [Previous complete comparison](273-joint-factorial-crosses-improve-the-complete-j-comparison.md) · [Actual raw and survivor crosses](272-joint-raw-and-survivor-crosses-strengthen-three-original-j-costs.md) · [Complete factorial pruning](270-shifted-factorial-heads-strengthen-three-original-j-quadratic-costs.md)

# Generalized factorial thresholds strengthen two original J costs

On both entire actual saturated J faces, each unchanged original cost
satisfies integral cost_i(A)dmu<=U_i, with the complete bounds

| Original index | Factorial threshold k | Exact complete upper U_i | Decimal prefix |
| --- | ---: | ---: | ---: |
|48|3|14458716500149327837/3969000000000000000|3.6429116906397903343411438...|
|49|2|207467385335349113/52920000000000000|3.9203965482870202758881330...|

The improvements over the corresponding complete target envelopes in273
are

    cost48: 0.0837237591695223955656336... ,
    cost49: 0.1290472348192713447676524... ,

Every target retains62,500,000 original containing choices, both entire
actual saturated J faces, the whole common late interval and all omitted
prime/cofactor depths. The source model remains3306 variables,6354
inequalities and18 equalities. This source result is not a new complete
52-cost comparison.

## The same original costs admit lower factorial thresholds

For integer n>=1 and integer k>=1, write

    H_t(n)=(n-t)_+,
    Phi_k(n)=(n-k)_+*(n-k+1)_+/2.

The two exact original identities are

    cost48(n)=(n^2-9)_+=5*H_3(n)+2*Phi_3(n),
    cost49(n)=(n^2-81/16)_+
             =(31/16)*H_2(n)+(17/16)*H_3(n)+2*Phi_2(n).   (GF1)

These hold at every positive integer load, not at arbitrary real loads.
The helper obtains them from the unchanged original Phi_5 expansions.
For a general original expansion a+sum_t old_t*H_t+f*Phi_5, use

    c_t=old_t+f*(I(t>=5)-I(t>=k)).                       (GF2)

This is the integer identity Phi_k-Phi_5=sum_(t=k..4) H_t
when k<=5, with the corresponding signed identity when k>5. The retained
expansions have a>=0, f>0 and positive nonzero c_t. The helper checks all
finite transitions through the common polynomial entrance. Beyond it,
the exact constant, linear and quadratic coefficients are

    a-sum_t t*c_t+f*k*(k-1)/2,
    sum_t c_t+f*(1-2*k)/2,
    f/2,                                                (GF3)

and agree with the original complete polynomial. Thus no finite cutoff
stands in for the infinite load range.

## One head-tail inequality covers every omitted depth

Keep the independently chosen original head

    B=1+I3+I9+I5+I15+I45, 1<=B<=6,
    A=B+T, T=O+Z, h=(B-k+1)_+.

Here O contains every omitted zero-seven label and Z every positive-seven
label. For every integer T>=0,

    Phi_k(B+T)<=Phi_k(B)+h*T+binom(T,2).                 (GF4)

If B>=k-1, set d=B-k>=-1. For every T>=0 the two sides equal
(d+T)*(d+T+1)/2, including the boundary d=-1,T=0 where both sides vanish.
Indeed the right-hand side is

    d*(d+1)/2+(d+1)*T+T*(T-1)/2.

If B<k-1, then Phi_k(B)=h=0. Put s=(B+T-k+1)_+.
Since s is an integer with0<=s<=T,
Phi_k(B+T)=binom(s,2)<=binom(T,2). This proves(GF4) for the
entire nonnegative integer tail in all six head cases.

For k=2, every possible head has equality in(GF4). For k=3, only B=1
uses the monotonicity case. The complete distinct-pair bound remains

    integral binom(O+Z,2)dmu<=4879/7200.                 (GF5)

No pair payment is subtracted or assigned a new conditional meaning.
The generalized split changes which low-load information remains in
the explicit head and cross terms while preserving the original cost.

## The actual source carries both complete cross terms

Apply272's full cross construction with h=(B-k+1)_+. Its source
coefficients and prime/cofactor partitions do not depend on k.

The actual raw source Lambda has mass1/4. Retain the first-depth
projections21,35,63,105 and the second-depth projections147,245, with
cell multiplicities m1 and m2. The retained positive-seven bound is

    integral h*(1/5+(6/35)*m1+(6/245)*m2)dLambda.          (GF6)

The complete weight across all positive-seven depths is1/5. The five remaining
raw mask-family weights, for cofactors3,9,5,15,45, are

    beta=(1/245,1/35,1/245,1/35,1/5),                    (GF7)

and the omitted old-cofactor contribution is still OldTail(h)/5.
Thus(GF6) and(GF7) retain every positive-seven term. They use actual raw
mass, without multiplying(GF6) by the survivor cap w.

For h*O retain the actual survivor events25,27,75,81,135,125.
With z=w*h, the complete old-tail weights are

    (1/18,1/20,1/20,1/20,1/72)

on C3,C5,C15,C45,Cstar. Removing just the assigned payments of the six
retained labels leaves

    gamma=(1/162,1/500,1/100,1/20,7/1080).               (GF8)

The removed weights are(4/81,6/125,1/25,0,1/135), all from their own
complete geometric series. The75 coefficient is1/25 because C15
already contains its root geometry. The retained survivor part is

    integral h*(I25+I27+I75+I81+I135+I125)dmu.            (GF9)

For each cell i and original four-bit mask, the objective adds

    f*h_i*(1/5+(6/35)*m1_i+(6/245)*m2_i) to X_(i,mask),
    f*(Phi_k(B_i)+h_i*popcount(mask)) to Y_(i,mask),
    f*h_i*(1,1,2)_state to V_(i,mask,state).             (GF10)

The three V states are135-only,125-only,both. All events keep their
actual multiplicities. The same X,Y,V columns also carry the original
hinge objective, including all selected labels and both seven depths.
The complete hinge tail37/1225 remains.

Let M_d(h,theta) be the existing raw cap maximum over each remaining
mask family. The unretained cross bound is

    R_(B,k)(theta)=sum_j gamma_j*C_j(w*h)+OldTail(h)/5
                  +sum_d beta_d*M_d(h,theta).           (GF11)

Every beta_d is nonnegative and each M_d is a maximum of affine cap
bounds. Consequently R_(B,k) is convex, and its endpoint secant bounds
it throughout the same actual interval[1/135,1/90]. With
x=(theta-LO)/(HI-LO), the common coordinate column875 has coefficient

    f*(R_(B,k)(HI)-R_(B,k)(LO)),                         (GF12)

and the outside factorial constant is f*(R_(B,k)(LO)+4879/7200).
The two retained targets have a=0; the generic objective also supports
the exact mass term a*(3/20). Only column875 may have a signed price.
All3306 columns are checked with exact rational dual witnesses on the
unchanged source polytope.

## Complete pruning is recomputed at the same threshold

Each target receives a fresh problem instance. Its k is set before any
factorial-head, cross or objective cache is populated and cannot be
changed by the retained calculation. The old complete two-, four- and
six-projection affine bounds are recomputed using this k and the exact
coefficients(GF1), including the full head, both full crosses and(GF5).
They remain valid upper bounds for the same original cost. No Phi_4
cached value or hinge-only pruning bound is reused.

The original choice inventory is12,500 head layouts times10 first
projections times50 next projections times10 second-depth projections.
The exact branch ledger checks500*n2+10*n4+n6=62,500,000 per target.

| Original index | n2 | n4 | n6 | Joint-dual branches |
| --- | ---: | ---: | ---: | ---: |
|48|124989|410|1400|1116|
|49|124985|339|4110|3734|

The maximizing certificate branches are

| Original index | Head layout |21/35/63/105/147/245 projections|
| --- | --- | --- |
|48|(1, 4, 2, 1, 2, 4, 2)|(1, 2, 4, 1, 2, 1, 2)|
|49|(1, 4, 2, 1, 2, 4, 2)|(1, 2, 4, 1, 2, 1, 2)|

These maximize certified upper bounds. They do not assert simultaneous
attainment by an actual covering family or a common optimizer for the
two original costs.

## Exact artifact and boundary

The [helper](../../frontier/j-geometry/j_face_generalized_factorial_heads.py) and
[certificate](../../certificates/source_norms/j-geometry/j_face_generalized_factorial_heads.json)
retain131 mathematical source pins and4850 distinct exact rational duals.
They check16034100 domination columns across125,000,000 original choices,
25000 threshold-specific head/cross records,50000 cross endpoints,
and38 independent original-affine compiler checks. Both complete identities,
all six head cases at each threshold, full geometric partitions, branch
decisions and source closure are retained. The dual bank uses the
existing canonical codec and contains only consumed witnesses.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_generalized_factorial_heads.py --check
```

The result covers both entire saturated actual J faces. It does not by
itself update the full52-cost comparison, cross403, extend off the faces,
close the global join, establish unrestricted Erdos7 or supply Lean
verification.
