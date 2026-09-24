[Index](../../marked_head_profile.md) · [Actual six-loss budget](153-the-six-source-losses-share-one-actual-concentration-budget.md) · [Signed source polynomial](150-signed-source-monotonicity-strengthens-the-product-mass-bound.md)

# Exposing each loss gives exact rational joint price bounds

For the selected concentrated K orientation, write the six losses as
u=(a,z,b,d,l,p), each in[0,sigma], with0<=sigma<1/2. Their original
concentration satisfies the necessary relaxation

    (1-a)*(1-z)*(1-b)*T3(d,l,p)>=1-sigma,
    T3=(1-d)*(1-l)*(1-p)+d*l*p.                 (EP1)

Then every coordinate satisfies its own stronger budget:

    u_j+(1-sigma)*sum_(i!=j)u_i<=sigma.         (EP2)

For six nonnegative prices, sort them c1>=...>=c6, retaining their
original factor labels. The resulting exact rational upper bound is

    sum_i c_i*u_i
      <=max_(1<=k<=6) sigma*(c1+...+ck)
                                  /[k-(k-1)*sigma].           (EP3)

The expression is the exact support of the outer polytope(EP2).
It is not in general the exact support of the nonlinear set(EP1).
Under the price-gap condition below it is sharp for that nonlinear
relaxation as well. Neither assertion implies actual-family attainment.

The small-coordinate domain is essential: q>=1-sigma alone does not
select the orientation. For example a=z=b=0 and d=l=p=1 give q=1
but violate(EP2). Actual applications use the orientation lemma already
established in148 and153.

## 1. A residual lemma for two or three coupled losses

Suppose0<=r<1/2, every common and late loss lies in[0,r], and

    P*T>=1-r,
    P=product_i(1-x_i),
    T=T3(y1,y2,y3) or T2(y1,y2),
    T2=(1-y1)*(1-y2)+y1*y2.

Put Y=1-P. The common factors give

    sum_i x_i<=Y/(1-Y).

For T3, its loss is sum y minus the three pair products, and each
pair satisfies yi*yj<=r*(yi+yj)/2. For T2, its loss is y1+y2-2y1y2.
In either case

    1-T>=(1-r)*sum_j y_j,
    1-T<=(r-Y)/(1-Y).

Consequently

    sum_i x_i+sum_j y_j
       <=Y/(1-Y)+(r-Y)/[(1-Y)*(1-r)]
        =r/(1-r).                              (EP4)

This bound is strict if r>0. When Y>0 the common-factor inequality
is strict. If Y=0, equality in the late loss estimate would require
either all late losses zero or all equal r. The former has total0,
below r/(1-r); the latter has T<1-r for0<r<1/2. Neither realizes
equality in the claimed total.

## 2. Expose one coordinate before applying the lemma

Expose a common coordinate, say a, and set

    r=(sigma-a)/(1-a)<=sigma<1/2.

Dividing(EP1) by1-a gives(1-z)*(1-b)*T3>=1-r.
Every remaining common loss is at most r. For a late loss, first use
the original small-coordinate domain to obtain, for example,

    1-d-T3=l*(1-d-p)+p*(1-d)>=0.

Thus the residual product is at most1-d, and d<=r. The same holds
for l,p. All hypotheses of(EP4) now hold, giving

    sum_(i!=a)u_i<=r/(1-r)=(sigma-a)/(1-sigma).

This is(EP2) for a; the other common coordinates are identical.

For a late coordinate, say d, the exact identity is

    (1-d)*T2(l,p)-T3(d,l,p)=(1-2d)*l*p>=0.

With r=(sigma-d)/(1-d), this implies

    (1-a)*(1-z)*(1-b)*T2(l,p)>=1-r.

Before asserting l,p<=r, use their original bounds l,p<1/2:

    1-l-T2=p*(1-2l)>=0,
    1-p-T2=l*(1-2p)>=0.

The residual product is therefore at most each1-l,1-p and every
common factor. All five residual losses are at most r, with no
circular assumption. Apply(EP4) again to prove(EP2). For sigma>0,
equality in the j-th exposed inequality occurs only at the corner
u_j=sigma and all other coordinates zero. Sigma=0 has only the zero
tuple and is handled directly.

## 3. Optimize the six linear inequalities exactly

For sigma>0 and total loss S, the six inequalities(EP2) are equivalent
to the common upper cap

    0<=u_i<=m(S):=[sigma-(1-sigma)*S]/sigma.

For fixed S, a nonnegative weighted sum is maximized by filling the
highest-priced coordinates first. Its dependence on S is affine
between breakpoints S=k*m(S), namely

    S=k*sigma/[k-(k-1)*sigma].

At that breakpoint the first k coordinates all equal
sigma/[k-(k-1)*sigma] and the rest are zero. These are feasible
vertices of(EP2), and their objective values are exactly the terms
in(EP3). The zero endpoint adds no larger value for nonnegative
prices. This proves(EP3) and its polyhedral sharpness. At sigma=0
both sides are zero.

For positive sigma and c1>0, the exact nonlinear support equals
sigma*c1 if and only if

    c2<=(1-sigma)*c1.                           (EP5)

Sufficiency follows immediately from(EP2) for the highest-priced
coordinate. Its corner realizes sigma*c1 in(EP1), and strictness
from section2 excludes other nonlinear optimizers. Conversely, if
c2>(1-sigma)*c1, assign the two highest-priced coordinates

    u1=(sigma-epsilon)/(1-epsilon), u2=epsilon,

and set the other four to zero. Every two-coordinate slice of(EP1)
is the product constraint(1-u1)*(1-u2)=1-sigma. The gain over the
corner is exactly

    epsilon*[c2-c1*(1-sigma)/(1-epsilon)]>0

for sufficiently small positive rational epsilon. This proves
necessity without a differentiability assumption. All-zero prices
have zero support on the entire feasible set, not a unique optimizer.

## 4. Consequences for the original source norm prices

Use153's original factorwise estimates and their same valid first-beta
projection. The mass, pure and availability prices are

    N:(1/6,5/36,1/18,1/9,1/36,0),
    E:(0,0,0,1/9,0,0),
    D:(1/4,1/4,1/4,0,0,0).

Thus

    N<=sigma/6                         (sigma<=1/6),
    E<=sigma/9,
    D<=3sigma/[4*(3-2sigma)]           (sigma<1/2). (EP6)

The last is the exact outer-polytope price, not a claim of nonlinear
sharpness. The signed mass-difference prices in153 have maximum2/45
and second-largest13/360. By(EP5), through sigma<=3/16,

    S-s<=53/360-1/4+2sigma/45+rho.               (EP7)

For several simultaneous source errors, add their six price vectors
first, then apply(EP3) once. In particular153's vector for
L_N*N+L_E*E+L_D*D remains

    (L_N/6+L_D/4, 5L_N/36+L_D/4, L_N/18+L_D/4,
     (L_N+L_E)/9, L_N/36, 0).

The [helper](../../frontier/comparison-bounds/exposed_concentration_prices.py) exports this
joint calculation and the separate norm bounds. Its rational examples
check that pricing the combined vector can be strictly cheaper than
adding separately optimized norm bounds. The common bound sigma can
be replaced by a uniform delta<1/2, because an actual source with
sigma<=delta also satisfies(EP1) and its small-coordinate assumptions
at delta. The original infinite-tail coefficients are not altered.

The ordinary proof supplies the continuum claim. The program checks
the algebra, exact outer vertices and specified price corollaries.
This result alone is not a new complete numerator/denominator bound,
Lean verification or unrestricted Erdos7 resolution.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/exposed_concentration_prices.py --check
```
