[Index](../marked_head_profile.md) · [Shifted factorial identity and complete pruning](270-shifted-factorial-heads-strengthen-three-original-j-quadratic-costs.md) · [Previous complete comparison](271-three-shifted-factorial-costs-improve-the-complete-j-comparison.md) · [Actual retained source model](256-a-second-seven-depth-sharpens-the-complete-retained-j-heads.md)

# Joint raw and survivor crosses strengthen three original J costs

On both entire actual saturated J faces, each unchanged original cost
satisfies integral cost_i(A)dmu<=U_i, with the following complete bounds:

| Original index | Complete exact upper | Decimal prefix |
| --- | ---: | ---: |
|41|258197238719666557094805653/52227799123500000000000000|4.943674500032497182980892...|
|47|17329379471720830159/5556600000000000000|3.118701988935829492675377...|
|48|591640644011726489/158760000000000000|3.726635449809312729906777...|

Their improvements over the adopted original-cost bounds in271 are

    cost41: 0.065689085603817505431829... ,
    cost47: 0.048515118698352438181621... ,
    cost48: 0.041599999980372146636432... ,

All three costs retain their positive-seven factorial cross on the same
actual raw source. Costs41 and48 additionally retain six zero-seven cross
events on the same actual survivor. Cost47 uses the complete original
zero-seven cross bound. Every target covers62,500,000 original choices,
the whole late interval and every omitted prime/cofactor depth.

This is a change to the complete cost objective on the original source
model:3306 variables,6354 inequalities and18 equalities. No source row,
marked state or original function is removed. A new full52-cost comparison
requires a separate consumer.

## The exact original factorial split

Keep270's exact all-load expansions

    cost(n)=a+sum_t c_t*H_t(n)+f*Phi4(n),
    H_t(n)=(n-t)_+, Phi4(n)=(n-4)_+*(n-3)_+/2,
    c_t>=0, f>0.                                          (JC1)

All finite transitions and the entire original quadratic continuations
are unchanged and checked. For the same independent old head

    B=1+I3+I9+I5+I15+I45,    h=(B-3)_+,
    A=B+O+Z,

O contains all omitted old labels and Z all positive-seven labels. The
complete inequality is

    Phi4(A)<=Phi4(B)+h*O+h*Z+binom(O+Z,2).                 (JC2)

The proof and all six possible B values are270's. Its original complete
pair bound4879/7200 is retained in full. The new bounds concern precisely
the two linear cross terms h*O and h*Z; they do not subtract anything
from an unknown actual pair moment.

## The positive-seven cross shares the actual raw source

Let Lambda be the common raw source, of mass1/4. For each cofactor d in
1,3,9,5,15,45, let M_d(h,theta) denote the maximum raw cap integral of h
over the corresponding projection masks. The six mask-family sizes are
1,2,5,5,10,25. The old complete bound in270 is

    integral h*Z dmu
        <=(sum_d M_d(h,theta)+OldTail(h))/5.               (JC3)

The complete weight across positive-seven depths is1/5. The first two
depths have weights

    u1=6/35,    u2=6/245,
    sum_(e>=1) 6/(5*7^e)=1/5.                            (JC4)

Retain the actual projections of21,35,63,105 in the first depth and
147,245 in the second depth. Their multiplicities at raw cell i are

    m1_i=I21_i+I35_i+I63_i+I105_i,
    m2_i=I147_i+I245_i.

The cofactor1 projection is the whole old source at every positive depth.
The retained part therefore has the linear bound

    integral h*(1/5+u1*m1+u2*m2) dLambda.                 (JC5)

All unretained cofactor depths remain. The exact residual mask weights
for d=3,9,5,15,45 are

    (1/245,1/35,1/245,1/35,1/5),                         (JC6)

because1/5-u1-u2=1/245 and1/5-u1=1/35. The complete omitted old-cofactor
part is still OldTail(h)/5. Thus(JC5) together with(JC6) partitions every
term of(JC3), replacing selected maxima by their integrals on the actual
same raw source. No factor w is inserted in(JC5).

Inside the LP, X_(i,mask) is the actual raw cell mass, so(JC5) contributes

    f*h_i*(1/5+u1*m1_i+u2*m2_i)

to every X column over i. The six projections retain independently chosen
original residues; they are not forced to align with B or with one
another.

## Six zero-seven events share the actual survivor

For costs41 and48, retain the actual events

    25,27,75,81,135,125                                  (JC7)

inside h*O. Write z=w*h. The complete old-tail operator has the form

    OldTail(z)=C3(z)/18+C5(z)/20+C15(z)/20
               +C45(z)/20+Cstar(z)/72,                  (JC8)

where C3 is the maximum normalized deep-three cell sum, C5 the maximum
descendant-five slot sum, C15 the maximum root/slot sum, C45 the maximum
descendant-weighted cell value and Cstar=max z. These are the complete
source operators used in241 and270.

The exact assigned series weights of(JC7) are

| Old-tail family | Retained labels | Removed weight | Complete remaining weight |
| --- | --- | ---: | ---: |
|C3|27,81|1/27+1/81=4/81|1/162|
|C5|25,125|1/25+1/125=6/125|1/500|
|C15|75|1/25|1/100|
|C45|none|0|1/20|
|Cstar|135|1/135|7/1080|

The75 weight is1/25 because C15 already contains the root geometry; it
is not C15/75. The135 label has exponents(3,1) and belongs to the mixed
old-tail series. Its assigned payment is Cstar/135. All five remaining
weights are strictly positive and keep their entire exponent series.
The helper verifies the exact geometric totals and this partition for
every original head.

Replace only these six assigned payments by

    integral h*(I25+I27+I75+I81+I135+I125) dmu.            (JC9)

The original four-bit mask records25,27,75,81; its population count gives
their multiplicity. Y_(i,mask) is actual survivor mass. The retained
states V_(i,mask,state) distinguish135-only,125-only,both, with
multiplicities1,1,2. Hence(JC9) is exactly represented by adding

    f*h_i*popcount(mask) to Y_(i,mask),
    f*h_i*(1,1,2)_state to V_(i,mask,state).              (JC10)

The complement retains multiplicity0. Overlaps are counted with their
actual multiplicity, not identified as one event. Both the original
hinge part and(JC10) use these same Y and V variables.

For cost47 no(JC9) replacement is made; its entire(JC8) is retained.
This is a different valid objective for that original cost, not a sum
of gains from two independently optimized sources.

## One residual secant and the unchanged complete pair tail

After(JC5) and the optional(JC9), the remaining cross bound is

    R_B(theta)=remaining_OldTail(w*h)+OldTail(h)/5
               +sum_(d=3,9,5,15,45) beta_d*M_d(h,theta), (JC11)

where beta is(JC6). Its old-tail term uses the complete remaining weights
above for41/48 and all original weights for47. Every beta is nonnegative.
For fixed coefficients, the raw cap integral is affine in theta, so each
maximum over masks is convex. Therefore R_B is convex and

    R_B(theta)<=(1-x)*R_B(LO)+x*R_B(HI),
    theta=LO+(HI-LO)*x, 0<=x<=1.                         (JC12)

Only the one actual common x is used. The objective adds
f*(R_B(HI)-R_B(LO)) to column875, and its outside constant includes

    f*(R_B(LO)+4879/7200)+a*(3/20).                       (JC13)

The actual factorial head f*Phi4(B) remains on the same Y columns. The
hinge part retains256's full selected135/125 load, both positive-seven
depths and complete hinge tail37/1225. Only the common-x objective can
be signed. All3306 columns are checked against exact duals on the same
original polytope; inequality multipliers are nonnegative and equality
multipliers are unrestricted.

All270 two-, four- and six-projection affine pruning bounds remain
unchanged. Each already bounds the whole original cost, including its
full factorial head, both crosses and complete pair tail. The minimum
of any such bound and the new complete joint dual is therefore valid.
No hinge-only bound is used for quadratic pruning.

## Complete original-choice coverage and exact artifact

Each target retains12,500 old-head layouts,10 first-projection choices,
50 next-projection choices and10 second-depth choices. If n2,n4 are the
first two pruning counts and n6 reaches the final stage, the checker
verifies500*n2+10*n4+n6=62,500,000 exactly.

| Cost | n2 | n4 | n6 | Joint-dual branches |
| --- | ---: | ---: | ---: | ---: |
|41|124990|381|1190|834|
|47|124990|475|250|115|
|48|124990|414|860|666|

The complete artifact contains1615 distinct rational duals and checks
5339190 domination columns across187,500,000 original choices. It
reconstructs both cross modes on all12,500 heads before pruning,
covering50,000 endpoint records. All57 independent original-affine compiler
checks remain. The branch decisions, cross components and complete
source closure are hashed; only the consumed dual bank is retained.

The maximizing certificate branches are

| Cost | Old-head layout |21/35/63/105/147/245 projection tuple|
| --- | --- | --- |
|41|(1, 4, 2, 1, 2, 4, 2)|(1, 4, 4, 1, 4, 1, 4)|
|47|(1, 4, 2, 1, 2, 4, 2)|(1, 2, 4, 1, 2, 1, 2)|
|48|(1, 4, 2, 1, 2, 4, 2)|(1, 2, 4, 1, 4, 1, 4)|

These identify maxima of certified upper bounds, not simultaneous
attainment by an actual covering family. The three targets need not
share an optimizing source.

The [helper](../frontier/j_face_joint_factorial_cross_heads.py) and
[certificate](../certificates/source_norms/j_face_joint_factorial_cross_heads.json)
retain125 mathematical source pins, all exact original expansions, both complete
cross partitions, the per-target objective mode and the entire pair tail.
Canonical replay uses standard-library rational arithmetic.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j_face_joint_factorial_cross_heads.py --check
```

The result applies to both entire saturated actual J faces. It does not
by itself give a full52-cost comparison, a crossing of403, an off-face
extension, a global join, Lean verification or unrestricted Erdos7.
