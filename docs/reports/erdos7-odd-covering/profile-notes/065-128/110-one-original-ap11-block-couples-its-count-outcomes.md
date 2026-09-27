[Index](../../marked_head_profile.md) · [Complete AP11 law](101-neighboring-hinges-strengthen-complete-ap11-survival.md) · [Same-test cost operator](104-one-test-layout-couples-the-hinges-of-each-complete-cost.md) · [Complete quadratic tail](108-a-complete-second-factorial-tail-improves-four-quadratic-costs.md)

# One original AP11 block couples its count outcomes

One original AP11 block uses the same independently labelled357 test
at every auxiliary count outcome in which that block occurs. Combining
its positive costs before maximizing strengthens the complete survival
denominator on both entire actual saturated K faces:

    d >= 1363468279799/17084377926000
       = 0.07980789734954262917070522313614... .     (AB1)

The gain over101 is exactly159851/542361204. Keeping108's entire
numerator gives

    C0+N108/d <= 462.2067284476727005763985937306... . (AB2)

The decrease from108 is1.6332196966549159218544.... Every original
block keeps its own test and arbitrary residues; no tests belonging
to different blocks are identified. All count and exponent tails,
the separate AP13 survival loss, and all52 signed numerator costs
remain included. The scope is r=rho=0 and D=53/360 on the two whole
K-control beta triangles. This is an ordinary exact-arithmetic proof,
with no off-face extension, global K improvement, Lean verification
or unrestricted Erdos7 resolution. The comparison still exceeds403.

## 1. Regroup the original count law by its fixed test

Let h_t(v)=(v-t)_+. In101's original AP11 law,

    p1=28/33, p_n=50/(3*11^n) for n>=2,

the loss before the outside factor1/7 is bounded by

    L11=sum_(n>=1)p_n*sum_(e=0..n-1)
                                  integral h_(5/n)(A_e)dmu. (AB3)

Here A_e is the original block-e test, fixed for every n>e.
Different A_e may have completely different residue configurations.
All summands are nonnegative, so Tonelli permits regrouping by e.
The old bound used a separate uniform hinge estimate at each n;
we preserve the common test in each regrouped block.

For n=1,2,3,4, the exact integer-load identities of101 are

    h5(v),
    h_(5/2)(v)=(h2(v)+h3(v))/2,
    h_(5/3)(v)=(h1(v)+2*h2(v))/3,
    h_(5/4)(v)=(3*h1(v)+h2(v))/4.                 (AB4)

The factors1/n in(AB4) are retained because(AB3) sums block costs,
not the n-fold aggregate dilated cost.

## 2. The infinite affine count tail also regroups exactly

For every integer v>=1 and every n>=5,

    h_(5/n)(v)=h1(v)+1-5/n.

Define the complete count sums

    T0=sum_(n>=5)p_n=5/43923,
    T1=sum_(n>=5)n*p_n=17/29282.

For a fixed original block e, its h1 coefficient is

    w_e=sum_(n>=max(5,e+1))p_n.

These are complete geometric sums. In particular w_e=T0 for
e=0,1,2,3, while

    sum_(e>=4)w_e=T1-4*T0=1/7986.

The total constant term in the entire count tail is

    D*sum_(n>=5)(n-5)*p_n=(T1-5*T0)*D=D/87846.

Thus every infinite block and count remains present. There is no
uncomputed reciprocal-count series: summing the n block constants
first cancels its1/n factor exactly.

For e=0,1,2,3 define the finite positive hinge objective

    F_e(v)=sum_(n=e+1..4)p_n*h_(5/n)(v)+T0*h1(v).

With U1 bounding each original integral h1(A_e), equations(AB3)--(AB4)
and the complete tail imply

    L11 <= sum_(e=0..3)integral F_e(A_e)dmu
                         +(T1-4*T0)*U1+(T1-5*T0)*D. (AB5)

Only the last uniform inequality forgets the identity of each
remaining e>=4 test. It is valid for every such independently labelled
test. The first four tests remain fixed inside their respective F_e.

## 3. Combine each block's source objective before its maximum

Write F_e(v)=a_e*h1(v)+sum_(t>=2)k_(e,t)*h_t(v).
All coefficients are nonnegative, with exact values:

| e | a_e | k2 | k3 | k5 |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1355/263538 | 20425/263538 | 25/363 | 28/33 |
| 1 | 1355/263538 | 20425/263538 | 25/363 | 0 |
| 2 | 1355/263538 | 2275/263538 | 0 | 0 |
| 3 | 85/87846 | 25/87846 | 0 | 0 |

Use a_e*U1 for the first term, retaining75's stronger whole-face
first-moment bound. For the remaining terms, apply104's common-test
operator with curvature vector k_(e,t). It combines the98 head
objectives and each selected original cylinder's positive increments
before the respective maximum. All original complementary label
tails carry the same curvature coefficients as the head. The test
layout is common across thresholds of one F_e, with no constraint
between e and any other block.

The e=2,3 objectives have only one curvature hinge; positive
homogeneity makes their existing one-hinge bounds unchanged. The
other two require12500 original head layouts times10 original
positive-seven projections each. All250000 exact LP evaluations
and selected-cylinder values give

| Original block | Uniform integral F_e bound | Gain in denominator |
| --- | ---: | ---: |
| 0 | 2007027259/11093751900 | 3268/19370043 |
| 1 | 667489/13835745 | 68347/542361204 |
| 2 | 33868/5929605 | 0 |
| 3 | 16081/27671490 | 0 |

The gains include the outside factor1/7 from survival. Their sum
is159851/542361204=0.0002947316268587677226.... As in104, feasible
head LP primal/dual pairs have matching rational values. The two
block maxima need not be simultaneously attained; independent uniform
upper bounds are sufficient, and no actual-family attainment is claimed.

The source tables, grouped beta constraints and first-beta symmetries
are the same as98 and104. Consequently the argument holds on both
entire actual saturated faces; no separately optimized vertex values
are interpolated.

## 4. Preserve the separate AP13 term and the full numerator

The remaining affine term in(AB5) is exactly

    R_tail=(1/7986)*U1+(1/87846)*D=3337/52707600.

Let B_e be the four block upper bounds in the table. The complete
survival lower bound is

    d >= D-U4/6-(sum_e B_e+R_tail)/7.             (AB6)

The standalone U4/6 comes from the separate AP13 comparison. It is
not attached to one of the AP11 original tests and is not combined
with their source maxima. Substituting the old separate bounds into
(AB6) reconstructs101's denominator exactly. The two accepted block
gains therefore give(AB1).

Keep108's complete numerator

    N108=35.164365148791272560864459998102...,

including the negative mass coefficient, all52 positive cost terms,
the full374/75 square complement and its weight. Both numerator and
denominator concern the same actual survivor. Since N108>0 and the
new denominator is positive, with C0=185694867601/8599322160 one gets

    C0+N108/d <=
      716346295632156935511464502635117131958540824564859
      /1549839609730510136501378201256902572265625000000,

which is(AB2).

## Reproduction

[whole_block_ap11_survival.py](../../frontier/moments-survival/whole_block_ap11_survival.py)
reconstructs the original probability law and integer identities,
checks the complete tail regrouping, evaluates the250000 new joint
objectives, and retains108's complete signed numerator. The
[certificate](../../certificates/source_norms/moments-survival/whole_block_ap11_survival.json)
stores the exact block coefficients, maxima, tail sums and final ratio.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/moments-survival/whole_block_ap11_survival.py --check
```
