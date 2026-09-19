[Index](../../marked_head_profile.md) · [Original product exclusion](../92-the-next-k-escape-layers-and-product-exclusion.md) · [Same-source denominator layers](../186-the-original-survival-margin-pays-its-own-target-change.md) · [Complete source union](../187-the-original-denominator-payment-strengthens-the-complete-source-union.md)

# The square-root product exclusion sharpens the complete source union

Retaining the stronger product inequality already proved in92 gives

    K <= 509.035651775507430129927742351... .                      (SP1)

This improves187 by 0.016339667439152338306637602.... The two
complete local source domains, all52 numerator costs, full denominator,
eight fallback bounds and both terminal errors are unchanged.
The smaller complete sufficient gap above403 is
106.036226775825572028752576179....
Unrestricted Erdos7 remains unresolved.

The result is an ordinary proof with rational endpoint certificates.
The displayed K is a certified rational value obtained using rigorous
square-root enclosures, not the asserted exact algebraic optimum.
No actual-family attainment, Lean verification or frozen-state claim
is made.

## 1. Retain the full separation of the two product regions

Use the original product-barycentric masses qK and qJ. Their late
and carrier factors give92's exact inequality

    sqrt(qK)+sqrt(qJ)<=1.                             (SP2)

These factors describe the original source interpolation. Their
product structure imposes no independence on the actual forbidden
residue labels or the survivor measure.

Write sigma=1-qK and t=sqrt(1-sigma). Then(SP2) implies

    qJ<=(1-t)^2.                                     (SP3)

The earlier consequence qJ<=sigma^2 discards some of this relation.
Keep186's full paired gap/denominator layers before making that
last relaxation. With q=23/42 and u=sigma-qJ, they give

    Phi(K0-h)>=-h*eK*qK+(gamma1-h*eJ)*qJ
                       +(gamma2-h*eB)*u+(A-q*h)*rho,
    0<=h<=H=gamma1/eJ.                               (SP4)

The coefficient of qJ after substituting u is

gamma1-gamma2-h*(eJ-eB)<0. Hence(SP3) gives the lower bound

    Phi(K0-h)>=P_h(t)+(A-q*h)*rho,
    P_h(t)=-h*eK*t^2+(gamma1-h*eJ)*(1-t)^2
                         +2*(gamma2-h*eB)*t*(1-t).   (SP5)

The coefficient of t^2 is

    gamma1-2*gamma2-h*(eK+eJ-2*eB).                   (SP6)

It is negative at the chosen h. Thus P_h is concave in t.
This proves endpoint control on the image of each closed sigma
interval under t=sqrt(1-sigma). No concavity in sigma is needed.
The residual coefficient A-q*h remains strictly positive.

## 2. Exact rational enclosures suffice at the six endpoints

The source complement remains187's three regions:

    0<=sigma<=1/20, rho>=1/1000;
    1/20<=sigma<=1/18, rho>=1/13000;
    1/18<=sigma<=1, rho>=0.                          (SP7)

At each endpoint let M=10^30 and define n as the integer floor
of M*sqrt(1-sigma). The helper computes n with integer square root
and verifies the exact rational inequalities

    (n/M)^2<=1-sigma<((n+1)/M)^2,
    0<=n/M<=1.                                     (SP8)

Consequently jbar=(1-n/M)^2 bounds the true qJ from above. The
safe endpoint margin from(SP4) is

    gamma2*sigma-(gamma2-gamma1)*jbar+A*R
       -h*[eK+(eB-eK)*sigma+(eJ-eB)*jbar+q*R].      (SP9)

Its capacity is the ratio of the constant reserve to the positive
h coefficient. All arithmetic following(SP8) is rational.

|Branch|sigma|R|Certified decrement capacity|
|---|---:|---:|---:|
|low_zero|0|1/1000|0.718671919556859689725243137|
|low_low_radius|1/20|1/1000|1.098573964247007612886157830|
|bridge_low_radius|1/20|1/13000|0.438488126799954793759976200|
|bridge_wide_radius|1/18|1/13000|0.480418437803537704631077381|
|outer_wide_radius|1/18|0|0.425036740175942574441476642|
|outer_one|1|0|0.618581269720449377004926977|

The minimum is

    h=0.425036740175942574441476642...,
    K=K0-h.                                       (SP10)

The unique controlling rational enclosure is sigma=1/18,R=0.
Because its square root is enclosed, this does not assert that the
true algebraic endpoint has exactly zero margin. Every true endpoint
has a nonnegative margin by(SP9), and concavity in t extends these
bounds over(SP7). The checker verifies0<h<H and both positive
coefficients required by186's genuine-source Jensen proof.

## 3. Keep the complete local and terminal interfaces

The exact local domains181 and170 still include every actual slot
loss allowed by r<=5rho. Their complete52-cost bounds are both
below(SP1); each retains a positive full denominator and remaining
mass coefficient. All eight inherited fallback comparisons also
lie below(SP1). The original positive division factor is unchanged.
The full effective-source union and all original branches therefore
satisfy(SP1).

Both terminal error fractions are retained without alteration.
The sufficient gaps above403 become

    all20: 106.036226775825572028752576179...;
    nonuniform: 106.256172183720098155901727364... .

All infinite exponent and count tails remain in the inherited
complete source theorems. The sharper product observation neither
removes a cost nor invents a new actual source witness.

## 4. The maximal-decrement transition is rational in this coordinate

For future domain work, set eta=gamma2-H*eB>0. At h=H,

    P_H(t)=t*[2eta-(2eta+H*eK)*t].                  (SP11)

Its source-side transition is therefore exactly

    t_star=2eta/(2eta+H*eK),
    sigma_star=1-t_star^2
              =0.081402726616236368575217492... .

Unlike the intermediate square-root parametrization, sigma_star
is rational. It is smaller than186's previous transition. This is
only the zero-residual threshold of the outer inequality. To join
at H, complete local estimates must also cover every excluded
residual region; extending a source radius alone does not suffice.

The [helper](../../frontier/transport/square_root_product_escape_comparison.py)
and [certificate](../../certificates/source_norms/square_root_product_escape_comparison.json)
retain the original source closure, six exact square-root enclosures,
concavity and sign conditions, both complete local bounds, all
fallbacks and terminal terms, and the rational maximal-capacity
transition.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/square_root_product_escape_comparison.py --check
```
