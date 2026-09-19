[Index](../marked_head_profile.md) · [Exposed prices](156-exposing-each-loss-gives-exact-rational-joint-price-bounds.md) · [Complete wide rectangle](157-a-signed-tail-comparison-covers-the-one-over-twenty-seven-neighborhood.md)

# The seven-containing pair tails have one exposed source price

For the original actual source with qK>=1-sigma and
0<=sigma<=delta<=2/27, the complete positive-seven complement Zplus
and the two seven-containing factorial pair subseries satisfy

    Zplus<=779/12600+3delta/280,
    O+P<=103/180+13delta/180.                    (SP1)

Here O is the original old_positive7 subseries and P is the original
positive7_positive7_distinct subseries from128/138. Their full
infinite geometric sums are retained. The old-old pair subseries,
including all of its defect-dependent minima and exact crossings,
is unchanged.

Consuming(SP1) in157's complete rectangle gives

    qK>=26/27, rho<=1/100000, r<=1/520
       ==> K<=484.1680980992159... .             (SP2)

All52 original tests, five denominator objectives, every retained
finite head and infinite tail, and the one original residual budget
remain included. No head is rescanned. With the older139/143 H1/Q
interfaces the same consumer gives488.8868998452084; with152 it gives
(SP2). These remain ordinary continuous-source results with exact
rational checks, not a global K bound, Lean theorem or unrestricted
Erdos7 resolution.

## 1. Scalar source bounds retain the whole beta face

Use the canonical orientation and six losses of153/156, in order

    (ua,uz,ub,ud,ul,up).

The loss ub controls the total root1 beta mass:
sum_(j>=2)beta_j=(1-ub)/4. It does not require one beta cell to carry
that whole mass. This distinction retains the full admissible
first-beta face.

Write s=sum n_j, N3=max(n0+n1,n2+n3+n4), N9=max n_j,
D=max d_j, h=sum eta_j, h1=sum_(j>=2)eta_j and em=max eta_j.
As in157, every root1 width is at least1-ud/2. Thus

    sum_(j>=2)beta_j*w_j >=(1-ub)*(1-ud/2)/4.

The same lower width bound gives
sum_(j>=2)w_j>=3-ud/2. Since alpha1=(1-ua)/4, the raw mass has the
upper bound

    s<=[(3+uz)*(9+ud)
           -(1-ua)*(6-ud)-(1-ub)*(2-ud)-(1-ul)]/72
      =1/4+[9uz+6ua+2ub+5ud+ul
                            +ud*(uz-ua-ub)]/72
      <=1/4+ua/12+uz/8+ub/36
                            +(5+delta)*ud/72+ul/72.           (SP3)

The first step upper-bounds z*sum w, lower-bounds the root1 alpha
and beta subtractions, drops the other nonnegative subtractions,
and retains the selected late mass. In the final step uz<=delta,
and the two negative products are discarded. Every inequality holds
pointwise on the original source simplex domain.

For the root1 mass, the argument of157 before maximizing any price
gives

    R1<=5/36+ua/12+uz/12+ub/36+ud/72.           (SP4)

For root0, keep the selected deficit and late mass:

    R0<=1/9+(3uz+3ud+ul+uz*ud)/72
       <=1/9+(7delta+delta^2)/72<=5/36.

The last step holds throughout delta<=2/27. Consequently the same
upper bound(SP4) holds for N3=max(R0,R1). The other scalar bounds are

    N9<=z/9=1/12+uz/36, D<=z=3/4+uz/4,
    h<=1/2+ud/18, h1<=1/3, em<=1/9.           (SP5)

These formulas provide one six-coordinate price vector for each
scalar source quantity. They do not maximize the six losses
independently.

## 2. Reconstruct both complete factorial subseries

Use the original exact geometric series convention
G(p,b;s,t)=sum_(n>=b)(s*n+t)*p^(-n). The values needed by128 are

    a0=G(3,3;0,1)=1/18, aw=G(3,3;2,1)=4/9,
    b1=G(5,1;0,1)=1/4, bw1=G(5,1;2,1)=7/8,
    b2=G(5,2;0,1)=1/20, bw2=G(5,2;2,1)=11/40,
    G(3,3;2,-2)=5/18, G(5,2;2,-1)=7/40.

Substituting these into the original old_positive7 definition yields

    O=D/18+7(h+3h1+5em)/200+49/900.             (SP6)

For the other subseries, retain the complete raw linear and square
caps L and Q:

    L=s+N3+N9+a0*D+b1*(h+h1+em)+a0*b1,
    Q=s+3N3+5N9+aw*D+bw1*(h+3h1+5em)+aw*bw1,
    P=[(4/15)*Q-L/5]/2.

Combine the source coefficients before substituting any upper bound:

    P=s/30+3N3/10+17N9/30+29D/540
                      +11h/120+13h1/40+67em/120+109/2160.    (SP7)

All coefficients in(SP6),(SP7) are nonnegative. In particular,
the negative linear term in the original definition is combined
exactly; no upper bound is substituted into a negative coefficient.
At the whole K face these give

    O*=121/720, P*=97/240, O*+P*=103/180.        (SP8)

The helper derives(SP6),(SP7) from the original geometric-series
function and reconstructs both157 pair terms from their original
raw source caps. It does not use a copied decimal or a truncated
sum as evidence for an infinite series.

## 3. Apply the exposed budget after combining all source coefficients

First,157's exact positive-seven identity is

    Zplus=N3/35+N9/5+D/90+11h/700
                                  +h1/20+em/20+1/360.

Insert(SP3)--(SP5) in this expression and in F=O+P. Their resulting
six-loss price vectors are

    pZ=(1/420,3/280,1/1260,4/3150,0,0),
    pF=(1/36,13/180,1/108,(146+5delta)/10800,1/2160,0).

Thus

    Zplus<=779/12600+pZ.u,
    F<=103/180+pF.u.                            (SP9)

In both vectors the z coordinate is largest. Their second-largest
prices are1/420 and1/36. On the whole interval delta<=2/27 each is
at most(1-delta) times its largest price. Apply156's exposed
inequality for that same coordinate, or its exact rational support
formula, to obtain

    pZ.u<=3delta/280,
    pF.u<=13delta/180.

This proves(SP1). The sharpness statement inherited from156 concerns
the specified loss relaxation; it does not establish attainment by
an original covering family.

The same observation applies to every nonnegative combination
A*pZ+B*pF. Its largest coordinate is still z, and its exposed price
is exactly A*(3delta/280)+B*(13delta/180). Thus the full consumer can
pay one combined source price, after putting together its numerator
and denominator coefficients.

## 4. Preserve the entire old-old defect tail

Write Qoo for157's old_old_distinct bound. Replace only its two
seven-containing companion subseries:

    tail_distinct_pairs<=Qoo+103/180+13delta/180.              (SP10)

Every old-old family keeps its original min branch, shared defect,
selected-label omission, exact crossing and complete geometric tail.
The finite factorial head, including its positive7_cross terms,
also remains unchanged. Equation(SP10) affects only the
layout-independent pair-tail constant used by each original
quadratic cost.

At delta=1/27, the old-old bound stays exactly
6819361848539/50380606800000. The complete pair tail changes from
0.7255180616748547 to0.7102540013182017; the exact improvement is

    DeltaF=4451/291600.

The positive-seven complement improves157 by

    DeltaZ=79/2211300.

Both savings leave the face constants unchanged at delta=0. No
additional rho allowance enters(SP9) or(SP10).

## 5. One full signed consumer, without a head rescan

All157 support coordinates depend affinely on these two constants.
For each mean or quadratic hinge combination, decreasing Zplus by
DeltaZ subtracts(sum_t a_t)*DeltaZ from every coordinate at every
common q vertex. The single-H2 rows inherit the same improvement
with their original positive H2 coefficients. For a quadratic
factorial coefficient theta, (SP10) subtracts theta*DeltaF.

Let gammaD be the weighted Z coefficient in the five denominator
objectives, gammaN its coefficient in mean11, single-H2 and
quadratic9, and gammaF the weighted sum of the nine factorial
coefficients. The original weights give

    gammaD=6211/18634,
    gammaF=396401658301258447/86193944714797920.

No other original cost is changed. The new signed endpoint and
denominator are therefore

    Nnew=N157-gammaN*DeltaZ-gammaF*DeltaF,
    dnew=d157+gammaD*DeltaZ.                     (SP11)

For the target T=C0+Nnew/dnew, the code additionally combines the
actual source price before optimizing:

    [(T-C0)*gammaD+gammaN]*pZ+gammaF*pF.         (SP12)

The exact156 support of(SP12) equals the sum used in(SP11), because
both vectors share the same exposed maximizing coordinate. The
original full signed margin is checked to be exactly zero at T in
both forms. The two remaining actual mass coefficients from151/157
stay positive. The square's actual S unit and both global mass
floors are retained exactly as in157.

| Complete comparison | Retained139/143 H1/Q | Independent152 H1/Q |
| --- | ---: | ---: |
| Previous K upper | 489.8804182271787 | 485.1608401342302 |
| New denominator lower | 0.07848307098402725 | 0.07848783543433809 |
| New signed endpoint | 36.67457174504033 | 36.30642960334337 |
| New K upper | 488.8868998452084 | 484.1680980992159 |

The [helper](../frontier/seven_pair_source_prices.py) binds156 and157
and their complete source closure, reconstructs all geometric and
source coefficients, checks the raw-mass polynomial, evaluates the
exact exposed support, and checks one combined signed target price.
It reuses all9,750,000 original head evaluations and performs zero
new head evaluations. The [certificate](../certificates/source_norms/seven_pair_source_prices.json)
records exact rational coefficients, supports, savings, retained
old-old mass and both complete comparisons.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/seven_pair_source_prices.py --check
```
