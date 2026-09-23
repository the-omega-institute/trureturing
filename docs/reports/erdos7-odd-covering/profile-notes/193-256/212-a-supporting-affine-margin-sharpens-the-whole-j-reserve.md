[Index](../../marked_head_profile.md) · [Original identity formula](../065-128/66-explicit-linear-endpoint-neighborhood.md) · [Whole J face](../129-192/130-the-whole-j-face-forces-source-anti-alignment.md) · [Complete family errors](197-the-whole-j-reserve-keeps-each-original-family-error.md)

# A supporting affine margin sharpens the whole J reserve

On either whole actual J neighborhood of136,

    qJ>=1-delta, rho>=0, delta+rho<=1/1000,

the actual carrier average of the original old49 identity margin has
the upper bound

    sum_c pi_c*m40(theta;c)<=10661/48600+2*delta.     (JA1)

The previous136 bound used50*delta. Keeping197's entire family error
E(delta,rho), including both infinite pure-axis tails, gives the
replacement reserve

    reserve>=79/1944-6*delta-E(delta,rho).           (JA2)

This improves197's bound by48*delta throughout the same domain. The
actual source, carrier law, independent original labels and single
residual are unchanged. Only old49 direction40 is replaced. This
does not assert a new complete global K bound, Lean verification,
or a resolution of unrestricted Erdos7.

## 1. The same fixed layout has an affine upper support

Use130's actual layouts and distinguished carrier

    b=(2,3,1,1,1), c=(1,2,2,2,2), k=6-b,
    A=(root0,cell1), ROOT=(0,0,1,1,1).

Write d,n,eta for the original availability, raw mass and width
vectors, s=sum n, and h1=eta2+eta3+eta4. For this fixed layout the
original66 formula is

    m_fixed(theta;A)=6s-U(theta;b,c)-(a0+2a1+T)/5,
    a_l=k_l*n_l-c_l*eta_l/5.                         (JA3)

All maxima in U and T occur with negative coefficients in(JA3).
The following lower supports may therefore replace those maxima
to obtain an upper bound; no assumption that their branches remain
maximizing off the face is needed:

| Original maximum | Chosen lower support |
| --- | --- |
|max(root0 mass,root1 mass)|s/2|
|max_l n_l|n1|
|max_l d_l|d0|
|max(root0 width,root1 width)|h1|
|max_l eta_l|eta1|
|max_(t in BASES) eta.t|eta.c|
|max_l(k_l*d_l-c_l/5)|4*d0-1/5|
|max_l k_l*d_l|4*d0|
|max(root0 w,root1 w), w_l=9*eta_l*k_l|w2+w3+w4|
|max_l w_l|w2|

The root-mass support is the average of its two arguments. All other
rows select an argument of the original maximum. Both b and c are
members of the original independent BASES inventory. The exact
cofactor formula uses coefficients13/243 and1/486 for its two deep
ternary maxima, and(sum w+max_root w+max w)/36+5/72 for its remaining
complete contribution. Thus none of its infinite tails is truncated.

Substitution and collection give

    m_fixed(theta;A)<=L(theta),

    L=-1381/48600-d0/9
        +(29*n0+13*n1+47*(n2+n3+n4))/10
        -23*eta0/50-59*eta1/100-27*eta2/20
        -11*(eta3+eta4)/10.                         (JA4)

On the whole J face, n0=1/24, n1=1/12 and n2+n3+n4=1/8,
d0=3/4 and eta=(1/18,1/9,1/9,1/9,1/9). All chosen supports are
exact there, independently of the beta and late allocations, and

    L=10661/48600.                                 (JA5)

The helper reconstructs every coefficient of this affine identity
from(JA3), including its constant. Affine-basis comparison here is
an algebraic coefficient check, not a nonlinear interpolation claim.

## 2. Signed source bounds retain the favorable quadratic term

136's concentration gives

    deficit0>=(1-delta)/2,
    alpha1>= (1-delta)/4,
    sum_(l>=2) beta_l >=(1-delta)/4,
    sum_(l>=2) late_l >=(1-delta)/72,
    3/4<=z<=3/4+delta/4.

All original total simplex capacities remain in force. In particular
alpha0,beta0<=delta/4 and d0=z-alpha0-beta0>=3/4-delta/2.
The raw source formula n_l=eta_l*d_l-late_l gives

    n0<=1/24+delta/18+delta^2/72,
    n1<=1/12+delta/36.                             (JA6)

Indeed eta0<=1/18+delta/18 and n0<=eta0*z, whereas eta1<=1/9.
For the other root, eta_l>=1/9-delta/18 and h1<=1/3, so

    n2+n3+n4
      =(z-alpha1)*h1-sum_(l>=2)eta_l*beta_l
                                      -sum_(l>=2)late_l
      <=(1/2+delta/2)/3
         -(1/9-delta/18)*(1-delta)/4-(1-delta)/72
      =1/8+2*delta/9-delta^2/72.                    (JA7)

All multiplied quantities are nonnegative throughout the stated
domain. The three positive mass coefficients in(JA4) therefore
contribute an increase of at most

    (149/120)*delta-delta^2/40.                    (JA8)

The availability term costs at most delta/18. The width term has
negative coefficients: eta0>=1/18 is favorable and may be discarded.
The other widths are at most1/9; their total downward movement is
at most delta/18, because the total deficit outside cell0 is at most
delta/2. The largest negative coefficient magnitude is27/20, so
the entire width contribution costs at most3*delta/40. This proves

    L-Lface<=149*delta/120-delta^2/40
                              +delta/18+3*delta/40.       (JA9)

No independent lower mass is substituted into a positive coefficient,
and no upper mass is substituted into a negative one.

## 3. Average the actual carriers after choosing the same layout

The original m40(theta;carr) is the minimum of its layout margins.
Consequently, for every carrier separately,

    m40(theta;carr)<=m_fixed(theta;carr).          (JA10)

This inequality is averaged using the actual pi. It does not exchange
a layout minimum with an average. The fixed-layout difference from A
depends only on the cofactor carrier sum of a_l in(JA3).

On the original source domain, 0<=n_l<=eta_l<=1/9. Thus
a0+2*a1<=10/9, while any carrier sum, including an empty root or
cell, is at least-8/45. A carrier uses at most four cell occurrences,
and each a_l>=-2/45. Therefore

    m_fixed(theta;carr)-m_fixed(theta;A)
        <=(10/9+8/45)/5=58/225<1/2.              (JA11)

The actual carrier defect kappa=1-pi_A is at most delta by136.
Using(JA4),(JA9)--(JA11) gives

    sum pi*m40
      <=10661/48600+(337/180)*delta-delta^2/40
      <=10661/48600+2*delta.                      (JA12)

The compatible exchange of cells0 and1 transports the full argument,
including the actual carrier law and all original labels, to the
other J orientation. No particular beta vertex or late allocation
was chosen.

## 4. Keep every original family error in the replacement

197's complete actual identity margin is

    6S-integral A dmu
       >=13/50+5*rho-(239/60)*delta-E(delta,rho).  (JA13)

Its E retains the four separate shallow errors, both clipped infinite
pure-axis tails, the actual budget rho+7*delta/36, and all unchanged
mixed families. Subtract(JA12), discard the favorable5*rho and use
239/60+2<6. This gives(JA2). The change is exactly the source price
54 to6 in197's conservative reserve; it is not another deletion
credit or an independent use of the residual.

E is nondecreasing in delta and rho by197's whole-series argument.
Thus(JA2) is uniform on each complete rectangle whose corner obeys
delta+rho<=1/1000. Some positive corners are

| delta | rho | Complete replacement reserve lower bound |
| --- | --- | --- |
|1/1250|1/100000|307383341/25312500000 =0.012143539397530864...|
|1/1100|1/100000|9389279/1113750000 =0.008430329068462401...|
|1/1020|1/100000|18631897/3098250000 =0.006013684176551279...|
|1/1000|0|9430081/1518750000 =0.006209106831275720...|

A complete global consumer must replace only the original old49
direction40 term, with its original positive weight, and check every
complementary source region at the new target. These local reserves
alone do not supply such a consumer.

The [helper](../../frontier/j-geometry/j_affine_margin_reserve.py) and
[certificate](../../certificates/source_norms/j-geometry/j_affine_margin_reserve.json)
retain the exact affine coefficients, continuous-domain prices and
full197 errors. The helper also checks the support and carrier bound
at all23328 original source/carrier endpoints and the nine product
face vertices. Those are diagnostic checks; the inequalities above
prove the continuous-source and arbitrary-height assertions.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_affine_margin_reserve.py --check
```
