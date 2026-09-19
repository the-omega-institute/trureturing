[Index](../marked_head_profile.md) · [Whole beta face](72-a-linear-gap-on-the-entire-controlling-beta-face.md) · [Common seven head](78-a-common-seven-head-uniformly-improves-the-endpoint-fifth-hinge.md) · [Previous survival comparison](53-allocated-seven-thresholds-sharpen-actual-survival.md)

# Common seven hinges on both complete K-control faces

For actual original families approaching any point of the source
beta face398,410,422, with saturated mass S=D=53/360 and
carrier(root1,cell1), every independently labelled complete357
test A satisfies the uniform endpoint bounds

    limsup integral_survivor (A-4)_+<=62639/308700
                                    =0.20291221250404926...,
    limsup integral_survivor (A-5)_+<=565031/3601500
                                    =0.1568876856865195... . (KF1)

The source-cell exchange of profile72 transports both inequalities
to the entire second face616,628,640 with carrier(root1,cell0).
The bounds retain arbitrary beta distributions, all original test
residues and every exponent tail. No test first moment or unit
tail is assumed saturated.

Relative to the actual profile53 comparison at every point of these
faces, the fourth and fifth hinge upper bounds improve by at least

    gain4=650333/69457500,
    gain5=185792021/45581484375.                       (KF2)

Consequently their contribution to the common three-hinge survival
denominator improves uniformly by at least

    gain4/6+(4/33)*gain5
       =24723710047/12033511875000
       =0.002054571458757961... .                      (KF3)

These are ordinary endpoint theorems with exact rational
verification. They supply data on both full controlling faces;
they do not supply a quantitative finite neighborhood, update
global K, resolve unrestricted Erdos #7 or claim Lean verification.

## 1. A source relaxation retains the entire beta budget

Use profile72's five ternary cells with ROOT=(0,0,1,1,1) and

    eta=(1/18,1/9,1/9,1/9,1/9),
    beta2+beta3+beta4=1/4, beta_i>=0,
    n=(1/36,1/12,(1/2-beta2)/9,
                       (1/2-beta3)/9,(1/2-beta4)/9).

Actual source labels have one first beta cell L in{2,3,4}, with
beta_L>=1/5. The first source slots are P,A,Beta, and the unique
source-free slot is H; Q is the remaining first slot. Profile72
proves this using the first beta label. Beta labels in different
ternary cells are not assumed to have disjoint five projections.

Let X(c,s)=Lambda(cell_c times slot_s). Discarding deeper beta and
late35 source deletions gives the entrywise upper table

    X(c,s)<=R(c,s)=eta_c*p(c,s),

| Cell | P | A | Beta | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0,1 | 0 | 1/5 | 1/5 | 3/20 | 1/5 |
| L | 0 | 0 | 0 | 1/10 | 1/5 |
| Other root1 cells | 0 | 0 | 1/5 | 1/10 | 1/5 |

The exact source masses also give three disjoint group constraints:

    sum_s X(0,s)=1/36,
    sum_s X(1,s)=1/12,
    sum_(c>=2,s)X(c,s)=5/36.                           (KF4)

The sum of the raw upper table on root1 is13/90. Thus the last
constraint retains a compulsory deficit1/180, exactly the mass
of the remaining beta budget(1/4-1/5)/9. It allows that deficit
to be distributed arbitrarily among the root1 cells and slots.
The first-beta restriction is retained through the zero Beta
entry in cell L.

For a nonnegative rectangle cost z define U_L(z) as the maximum
of sum z(c,s)*X(c,s), with0<=X<=R and the three equalities in(KF4)
relaxed to upper bounds. Every actual source is feasible. This is
one LP whose variables include all remaining source masses; beta
has been eliminated by its exact group sum. In particular the
bound does not interpolate separately optimized fixed-beta LPs.

For one group G of mass bound b, nonnegative dual multipliers
gamma,alpha_i with gamma+alpha_i>=z_i give

    sum_(i in G)z_i*X_i<=gamma*b+sum_(i in G)alpha_i*R_i. (KF5)

The checker supplies a feasible primal and a feasible dual with
equal values for every common layout. The groups are disjoint,
so their three certified values add to U_L(z).

## 2. The ordered-seven bridge works at both thresholds

Fix t in{4,5}. Let A0 include all zero-seven test labels and the
unit. Keep every positive-seven unit label7^e and the original
test labels21 and35. If their independent old projections are
the ternary root T and first-five slot F, put

    m=1_T+1_F in{0,1,2},
    g_(t,m)(v)=7^(-max((t-v)_+-m,0))/5
                               +(6/35)*max(m-(t-v)_+,0).

At each old point the retained positive-seven list contains m+1
depth1 indicators followed by one indicator at every depth>=2.
For any ordered indicators J_i and integer k>=0,

    (sum_i J_i-k)_+<=sum_(i>k)J_i.

The complete normalized seven caps are6/(5*7^e), so deleting the
first k indicators yields the formula for g_(t,m). No relation
between their seven residues is imposed.

The complete raw35 nonunit cap sum on these faces is37/72.
The old caps of the selected labels21 and35 are respectively
5/36 and1/10, multiplied by6/35. All other positive-seven labels
therefore have total linear budget

    Zrest=37/360-(6/35)*(5/36+1/10)=779/12600.          (KF6)

The same nonnegative-increment argument as in78 gives

    integral_survivor(A-t)_+
        <=Zrest+integral_mu(A0-t)_+
                             +integral_Lambda g_(t,m)(A0).

The selected complete forbidden families3,9,5,15 of72 yield

    mu<=w*Lambda,
    w(c,s)=1-[1_(c>=2)+1_(c=1)+1_(s=H)
                                      +1_(c>=2,s=H)]/5.

Because the hinge is nonnegative, the surviving term is bounded
above by its integral against w*Lambda. Therefore, with

    f_(t,w,m)(v)=w*(v-t)_++g_(t,m)(v),

we obtain the single common-source estimate

    integral_survivor(A-t)_+<=Zrest+integral_Lambda f_(t,w,m)(A0). (KF7)

This is a measure inequality, not an identification of the actual
surviving measure with the selected-deletion upper measure.

## 3. Keep one layout through the head and complete old tails

Use the six-label head B of{1,3,9,5,15,45}, with layout
(r3,c9,s5,r15,s15,c45,s45), exactly as in78. There are12500
layouts and10 choices of(T,F). The function f_(t,w,m) is
increasing and integer-convex: below t its forward increments
increase to6/35, and from t onward they equal w>=2/5.

Order the first four old-tail labels as25,27,75,81. For
A0=B+sum_i I_i, the complete pointwise bound is

    f(A0)<=f(B)+sum_(i=1)^4 I_i*[f(B+i)-f(B+i-1)]
                                         +w*sum_(i>4)I_i. (KF8)

For i>=5, B+i-1>=5>=t, so the remaining forward increment is
exactly w. Thus(KF8) is valid for both t=4 and t=5.

For nonnegative rectangle functions z, deep pure3 cylinders have
the raw cost bound

    P_(a,0)(z)=3^-a*max_c sum_s p(c,s)*z(c,s), a>=3.   (KF9)

Here p is the table in section1; it excludes the first source
slots and keeps the complete pure5/alpha tails in Q. Dropping
remaining pure3 and late source deletions gives an upper bound.

For descendant-five cylinders of depth b>=2, start with the raw
coefficient eta_c on each entry. Set to zero every P entry, each
root1 A entry, and cell L's Beta entry. Call this matrix E.
Only full first-slot exclusions are used, so arbitrary distributed
deeper beta deletion is allowed. The cylinder bounds are

    P_(0,b)(z)=5^-b*max_s sum_c E(c,s)*z(c,s),
    P_(1,b)(z)=5^-b*max_(r,s) sum_(ROOT(c)=r)E(c,s)*z(c,s),
    P_(2,b)(z)=5^-b*max_(c,s)E(c,s)*z(c,s).           (KF10)

Deep mixed labels a>=3,b>=1 retain their product Haar caps.
Using(KF9)--(KF10) with z=w gives the complete old-tail budgets

| Category | Complete upper bound |
| --- | ---: |
| Pure3, a>=3 | 71/1800 |
| Pure5, b>=2 | 37/1800 |
| 3 times5^b, b>=2 | 1/75 |
| 9 times5^b, b>=2 | 1/225 |
| 3^a times5^b, a>=3,b>=1 | 1/72 |

Their sum is11/120. Removing the four assigned linear caps for
25,27,75,81, each exactly once, leaves

    Rrest=11/120-sum_(ORDER)P_(a,b)(w)=2389/81000.     (KF11)

The selected labels are then charged only the common-layout
increments in(KF8). All other labels remain in Rrest.

## 4. Exact finite certification covers the entire source face

For each common layout define z_i(c,s)=f(B(c,s)+i)-f(B(c,s)+i-1).
Combining the common-source LP with(KF6)--(KF11) gives

    integral_survivor(A-t)_+
       <=779/12600+U_L(f(B))+2389/81000
                              +sum_(i=1)^4P_(ORDER_i)(z_i). (KF12)

The same B,T,F enter every term. The checker certifies the maximum
of(KF12) over all250000 choices of head, additional projections
and threshold. The canonical first-beta cell is L=2. Swapping
cell2 with cell3 or cell4 preserves ROOT, eta, all group masses,
the head layout inventory and both tail operators; it transports
the three source tables exactly. Hence the same bounds cover all
three first-beta choices without a new assumption on beta.

For both thresholds, the unique maximizing common layout in
canonical coordinates is

    (r3,c9,s5,r15,s15,c45,s45)=(0,1,Beta,0,Beta,1,Beta),
    T=root0, F=Beta.

The values of its two nonconstant contributions are

| Threshold | Common source-head LP | Four selected old tails |
| --- | ---: | ---: |
| 4 | 20891/308700 | 12451/283500 |
| 5 | 77731/2160900 | 11747/396900 |

Adding779/12600+2389/81000 gives exactly(KF1).
The computed maxima belong to this upper-bound relaxation; no
actual family attaining them is asserted.

## 5. A uniform comparison with the previous face bounds

For fixed threshold t and carrier(1,1), let V_t(beta) be the
profile53 upper bound S-m_t(beta) for the surviving t-hinge.
In the notation of53, it is

    V_t=D-s+Trest+h_carrier+P_t+F_beta(g_t)-credit_t. (KF13)

The quantities D,s,Trest,h_carrier are constant on this beta
simplex. Each source operator in P_t and F_beta(g_t) is convex
in beta: its old-coordinate masses n and available densities d
are affine in beta; its finite layout/deep maxima are maxima of
affine functions; its pure3 positive-five remainder depends only
on the fixed eta. The positive-block coefficients are nonnegative.
For the affine complete tail this conclusion also follows directly
from the existing source operator for v-1.

Furthermore V_t is invariant under every permutation of the
three root1 cells. Their eta values and forbidden weights agree,
and the ternary layout set is invariant. Averaging these six
permutations sends every beta to the barycenter(1/12,1/12,1/12).
Jensen's inequality therefore gives

    V_t(barycenter)<=V_t(beta).

Conversely convexity bounds V_t(beta) by its equal values at the
three vertices. Exact evaluation of(KF13) gives

| Threshold | Minimum on the full relaxed simplex | Maximum |
| --- | ---: | ---: |
| 4 | 3686027/17364375 | 3686027/17364375 |
| 5 | 29347862459/182325937500 | 435388099/2701125000 |

The barycenter need not be an actual source with a first-beta
label. Its role is to give a lower bound for the old numerical
expression throughout the larger relaxed simplex, and therefore
on every actual subregion beta_L>=1/5. Subtracting(KF1) from
these lower bounds proves(KF2), and the positive denominator
weights1/6 and4/33 give(KF3). Convexity here concerns the explicit
old source expression(KF13), not fixed-beta optima of the new LP.

## 6. Endpoint passage and reproduction

The proof of72 supplies labelwise compactness for varying actual
families approaching either full beta face. After taking a
subsequence, the first-beta cell and the finite head stabilize.
Every omitted source or test tail is uniformly bounded by the
complete geometric sums used above. The hinge is1-Lipschitz in
the nonnegative load, so removing sufficiently deep labels has
a uniformly vanishing integral cost. Apply(KF12) at the limiting
source and pass back to limsup. The proof covers changing test
residues and unbounded exponent heights.

The [checker](../frontier/k_face_common_seven_hinges.py) uses integer
cost scale12005 and source-mass scale360. It independently checks
primal feasibility, dual feasibility and equality for every LP,
the two convex-increment tables, all complete tails, first-beta
symmetry, and the exact old face comparisons. Its
[certificate](../certificates/source_norms/k_face_common_seven_hinges.json)
stores the two bounds, maximizing witnesses, aggregate enumeration
hash, complete budgets and guaranteed gains.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/k_face_common_seven_hinges.py --check
```
