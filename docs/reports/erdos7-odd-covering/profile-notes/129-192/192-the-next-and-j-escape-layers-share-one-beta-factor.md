[Index](../../marked_head_profile.md) · [Original three layers](../065-128/92-the-next-k-escape-layers-and-product-exclusion.md) · [Paired denominator](186-the-original-survival-margin-pays-its-own-target-change.md) · [Square-root exclusion](190-the-square-root-product-exclusion-sharpens-the-complete-source-union.md)

# The next and J escape layers share one beta factor

The original J layer and the next two source controls cannot receive
independent worst-case masses. Retaining their common beta factor
reduces the joint bound to the minimum of two explicit alternatives.
This is an ordinary source theorem on the original full domain,
with one actual residual and all independent labels and tails.
It does not by itself supply a complete global comparison or solve
unrestricted Erdos7.

Use186's target decrement0<=h<=H=gamma1/eJ and set

    fK=-h*eK,
    fJ=gamma1-h*eJ,
    fB=gamma2-h*eB,
    fC=gamma3-h*eC.                                  (BL1)

The first three pairs are exactly those of186. The next values are

    gamma3=131097134374357952846687928903046514235992135314423
             /162297686428943722579100173933265785675218000000000,
    eC=11635969547/152806500000.                       (BL2)

Write sigma=1-qK and t=sqrt(1-sigma). Then

    Phi(K0-h)>=min(F_B(sigma),F_J(t))+(A-q*h)*rho,
    F_B(sigma)=fK*(1-sigma)+fB*sigma,
    F_J(t)=fK*t^2+fJ*(1-t)^2+2*fC*t*(1-t),
    q=23/42.                                        (BL3)

Both alternatives are concave in t. Thus a complete comparison on
any closed source interval and residual lower bound reduces to
checking both alternatives at its two endpoints. No independent
upper bound on the actual denominator is inferred from(BL3).

## 1. The next joint layer uses the original paired rows

Let K be the original six zero controls, J the eighteen first-gap
controls, and B the two next controls386/(1,1),592/(1,0).
They are the sets enumerated in92. At each original source vertex
and carrier,186 retains the original gap g and its associated
allocated-denominator value e=q*D_c+M_lower.

The exact certificate reconstructs every original allocated margin
using53's original routine and checks its complete original digest.
It then verifies, for every row outside K union J union B,

    g-h*e>=gamma3-h*eC, 0<=h<=H.                     (BL4)

It checks h=0 and h=H; the difference is affine in h, so these two
checks cover the entire interval. At both endpoints, equality occurs
exactly at sources386 and592 with carriers(1,2),(1,3),(1,4).
Each of these six rows has the same gap gamma3 and payment eC.
Every upper mass endpoint retains its additional nonnegative term
(A-q*h)*(s-D_c), so no source or carrier endpoint is omitted.

Together with186, this gives the four lower levels fK,fJ,fB,fC,
with

    fC>fB>fJ>=0>=fK.                                (BL5)

All inequalities are checked at h=0,H and are affine in h.
The original positive coefficients A-q*h and K0-offset-h remain
positive. Consequently the genuine-function Jensen bridge of186
continues to apply; this is not interpolation of a patched table.
For qB the product-barycentric mass of B, it gives

    Phi(K0-h)>=fK*qK+fJ*qJ+fB*qB
                  +fC*(1-qK-qJ-qB)+(A-q*h)*rho.     (BL6)

## 2. Extract the common beta factor without changing any source

Use92's original simplex coordinates. Put b=beta3+beta4+beta5,
a=alpha2*z0, L=late3+late4+late5, and define

    k=a*(deficit1*late1*pi11+deficit2*late2*pi10),
    j=a*L*(deficit1*pi01+deficit2*pi00).              (BL7)

The exact Cartesian descriptions in92 give

    qK=b*k, qJ=b*j,
    qB=a*(deficit1*beta2*late1*pi11
                        +deficit2*beta1*late2*pi10)
       <=(1-b)*k.                                  (BL8)

All weights are nonnegative simplex weights. Let LK=late1+late2
and PK=pi11+pi10. Then k<=LK*PK and j<=(1-LK)*(1-PK).
Cauchy--Schwarz yields

    sqrt(k)+sqrt(j)<=1.                             (BL9)

This reasoning includes both K orientations simultaneously. It
uses the same actual carrier distribution as the original proof.
Product-barycentric source factors do not assert independence
of the actual forbidden labels or of the actual survivor measure.

## 3. A convex auxiliary problem has only two extremal alternatives

Fix qK=x>0. Since x=b*k, one has x<=k<=1, b=x/k. Equations(BL8)
and(BL9) imply

    qB<=k-x,
    qJ<=x*(1/sqrt(k)-1)^2.                          (BL10)

Let u=fC-fB>0 and v=fC-fJ>0. The part subtracted from
fC+(fK-fC)*x in(BL6) is u*qB+v*qJ. Its upper bound is

    u*(k-x)+v*x*(1/sqrt(k)-1)^2.

Set z=sqrt(k), so sqrt(x)<=z<=1. Apart from the constant-u*x,
the function to maximize is

    D(z)=u*z^2+v*x*(1/z-1)^2.

Its second derivative is

    D''(z)=2u+v*x*(6/z^4-4/z^3)>0,                 (BL11)

because0<z<=1. It is convex on the whole interval, so its maximum
occurs at one of the two endpoints. Returning to(BL6):

- At k=1, the bound uses qB=1-x,qJ=0 and gives F_B(1-x).
- At k=x, it uses qB=0,qJ=(1-sqrt(x))^2 and gives F_J(sqrt(x)).

Taking the smaller lower bound proves(BL3). When x=0, the original
four-level mixture is at least fJ by(BL5), and the formula reduces
to min(fB,fJ)=fJ. Thus division by x or k is never used at a zero
endpoint. The other endpoint x=1 is included directly.

The auxiliary endpoint configurations can be attained as product
weights in one orientation: set the unused source factors to their
required basis values, take the late and carrier K probabilities
both sqrt(k), and put beta mass b=x/k on the K beta region and
1-b on its matching B index. This describes only the interpolation
relaxation. It does not construct an actual covering family or
claim simultaneous equality in the underlying source inequalities.

## 4. The resulting interval check remains finite

In t=sqrt(1-sigma), F_B=fB+(fK-fB)*t^2 is concave because fK<fB.
The quadratic coefficient of F_J is fK+fJ-2*fC<0. Hence both
alternatives are concave on every t interval; their minimum is
concave as well. It is sufficient to bound each at the two ends.
The residual remains monotone because A-q*h>0.

The [helper](../../frontier/cover-geometry/three_layer_product_escape.py) and
[certificate](../../certificates/source_norms/cover-geometry/three_layer_product_escape.json)
retain the original gap/payment data, all four exact layer checks,
the coefficient ordering and the auxiliary formulas. The product
reduction and convexity argument above supply the continuous bridge.
A complete global join must additionally retain its full local
comparisons, original fallbacks and terminal errors. No Lean or
frozen-truth claim is made here.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/three_layer_product_escape.py --check
```
