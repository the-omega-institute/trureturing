[Index](../../marked_head_profile.md) · [Complete source credits](147-source-dependent-credits-cross-the-old-middle-bottleneck.md) · [Previous global consumer](149-product-mass-and-source-credits-improve-the-complete-comparison.md) · [Actual signed mass](154-the-actual-orientation-sum-extends-the-signed-mass-bound.md)

# The signed mass bound reaches the current source credit ceiling

Keeping147's complete source-cost credits and replacing the upper mass
bound by154 gives the full ordinary comparison

    K<=K0-h*,
    h*=B0/(53/360)=0.1531243936601362...,
    K<=509.3075641220232... .                    (JC1)

Here B0 is147's exact rational zero-escape credit, not a fitted decimal.
This improves149 by0.0031243936601362... and118 by0.0291243936601362....
All nine endpoints, eight original fallback branches and both full
terminal errors remain. The smaller complete sufficient gap above403
is still106.3081391223414.... Unrestricted Erdos7 is unresolved.

The same calculation identifies the exact capacity of this fixed
credit assignment. Changing only its denominator slope or cutoffs
cannot improve past(JC1), because its sigma=rho=0 endpoint is unchanged.
No optimality for actual covering families or other proof methods is
asserted. The gain uses the1/10 slope already proved in150; extending
that slope's domain to1/3 in154 is valid but not necessary for this gain.

## 1. Preserve the complete original source reserve

Use147's notation and exact constants, with

    delta=21/500, r*=3/1000, a=53/360,
    B(sigma)=B0-B1*sigma+B2*sigma^2,
    e(sigma)=gamma2*sigma-(gamma2-gamma1)*sigma^2.

The unchanged46 original fixed cost alternatives, their full tails,
and actual slot transport give the target reserve before changing K0:

    R>=B(sigma)-Q*sigma+e(sigma)+(A-P)*rho-L*r.  (JC2)

This is the same source and residual as the actual denominator E.
Its original slot identity gives r<=5rho. On sigma<=1/3,154 gives

    E<=a+sigma/10+rho.                          (JC3)

For sigma<=delta and r<=r*, substitute(JC3) in R-h*E and then use
r<=5rho. The lower bound becomes

    F(sigma)+(A-P-h*-5L)*rho,
    F(sigma)=B(sigma)-Q*sigma+e(sigma)
                                      -h*(a+sigma/10).         (JC4)

The residual coefficient is positive. The quadratic coefficient in
F is negative, since gamma2-gamma1-B2>0. Thus F is concave and its
two interval endpoints suffice. By definition F(0)=B0-h*a=0 exactly;
F(delta)>0. A zero endpoint is sufficient for the claimed non-strict
bound K<=K0-h*: no strict comparison at that source is claimed.

For sigma<=delta but r>=r*, discard the marked credits entirely.
The original unmarked reserve then gives

    R-h*E>=e(sigma)+(A-h*)rho-h*(a+sigma/10)
           >=(A-h*)r*/5-h*(a+delta/10)>0.       (JC5)

The cost penalties P and L are not paid after the associated credits
are discarded. This retains one residual, without duplicating its use.

## 2. Check both sides of every mass-bound switch

For delta<=sigma<=1/3 use e(sigma)-h*(a+sigma/10).
For1/3<sigma<1/2 use the unchanged upper mass a+(5/9)*sigma.
For1/2<=sigma<=1 use the original raw-mass upper bound

    1/4+(11/36)*sigma*(1-sigma).

All three target functions are concave with the inherited constants.
Thus the full source partition has the following endpoint capacities.
Each number is an exact rational in the certificate, shown rounded here.

| Branch endpoint | Maximum decrement allowed by that endpoint |
| --- | ---: |
| Concentrated small r, sigma=0 |0.1531243936601362...|
| Concentrated small r, sigma=delta |0.1545337514352853...|
| Concentrated large r |0.2142120244690261...|
| Strong middle, sigma=delta |0.1550888657618723...|
| Strong middle, sigma=1/3 |0.7447028124933494...|
| Old middle, right limit at1/3 |0.4045043131927664...|
| Old middle, left limit at1/2 |0.3697332370738243...|
| Far, sigma=1/2 |0.4814398746578308...|
| Far, sigma=1 |0.1878037429972404...|

Only the first endpoint has zero margin at h*. Every other margin is
strictly positive. The old middle value at1/3 is checked as a right
limit, so the switch does not lose a source region. The exact original
positive denominator factor and positive target coefficient remain.
All eight complete fallback bounds lie strictly below K0-h*; both
terminal errors are retained when comparing against403.

## 3. What now has to change

For this assignment, the zero-escape endpoint demands B0-h*a>=0.
It therefore forbids h>h*, regardless of improvements to the sigma
coefficient in(JC3). Even removing this one endpoint would leave the
nearby delta endpoint and then other complete source regions.

Consequently further numerical tuning of these unchanged constants
cannot provide a substantial advance toward403. A stronger complete
cost curve, a wider applicable local theorem with its residual domain,
or a new complete branch is required. Local reserves cannot be
transferred between different actual source configurations.

The [helper](../../frontier/comparison-bounds/joint_mass_outer_comparison.py) reconstructs
149 and154 before evaluating the complete new partition. It uses h*
as its exact rational expression; it does not choose an arbitrary
rounded decrement or claim a strict inequality at the limiting
endpoint. Ordinary proofs establish the source-uniform comparison;
the exact program checks its inputs and all finite algebraic conditions.
No canonical118 certificate is mutated, and no Lean or frozen-truth
claim is made.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/joint_mass_outer_comparison.py --check
```
