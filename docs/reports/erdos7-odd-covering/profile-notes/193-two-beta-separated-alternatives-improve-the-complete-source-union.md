[Index](../marked_head_profile.md) · [Shared beta theorem](192-the-next-and-j-escape-layers-share-one-beta-factor.md) · [Previous complete union](190-the-square-root-product-exclusion-sharpens-the-complete-source-union.md)

# Two beta-separated alternatives improve the complete source union

Retaining the shared beta factor from192 improves the complete global
comparison to

    K<=3417245151673515148092745937052755142808744261
         /6713249102926614010511352413785632128472000
      =509.029994162406521665721458068084... .       (BG1)

The improvement over190 is0.0056576131009084642.... This bound
retains every original source case, all52 local numerator costs,
the full denominator, eight fallback comparisons and both terminal
errors. It remains above the sufficient403 threshold, and does
not resolve unrestricted Erdos7. No Lean or freeze claim is made.

## 1. The original complete domains leave three outer regions

Keep181's complete domain

    sigma<=1/20, rho<=1/1000,

and170's complete domain

    sigma<=1/18, rho<=1/13000.

Their complete bounds are505.701239618792632674... and
506.975514690183036952..., both below(BG1). Each uses the actual
implication r<=5rho, with no independent slot cutoff. Their
complement is covered by the following closed regions:

    sigma in[0,1/20],       rho>=1/1000;
    sigma in[1/20,1/18],    rho>=1/13000;
    sigma in[1/18,1],       rho>=0.                 (BG2)

Overlapping boundaries cause no omission. The signed comparison
Phi, baseK0, coefficientA and survival coefficientq=23/42 are
exactly those in186/192.

## 2. Both auxiliary alternatives must pass at every endpoint

For0<=h<=H=gamma1/eJ,192 proves

    Phi(K0-h)>=min(F_B(sigma),F_J(sqrt(1-sigma)))
                            +(A-qh)*rho.

Both alternatives are concave in t=sqrt(1-sigma), and A-qh>0.
Thus each region in(BG2) requires both alternatives at both ends,
giving twelve inequalities. For an endpoint(sigma,R), the first
has reserve and payment

    reserve_B=gamma2*sigma+A*R,
    payment_B=eK+(eB-eK)*sigma+q*R.               (BG3)

For the second, let jbar be an upper bound on
(1-sqrt(1-sigma))^2. Then

    reserve_J=gamma3*sigma-(gamma3-gamma1)*jbar+A*R,
    payment_J=eK+(eC-eK)*sigma+(eJ-eC)*jbar+q*R.  (BG4)

The helper encloses each square root between adjacent multiples
of10^-30 by integer-square arithmetic. Taking the lower root
bound gives jbar. The coefficient of jbar in
reserve_J-h*payment_J is negative throughout the selected range,
so this gives a rigorous lower margin for the actual endpoint.
All payments are positive.

Choose h as the smallest of the twelve reserve/payment ratios.
Its unique controller is the B alternative at sigma=1/18,R=0:

    h=14158742250938240063000691811817435200717494240697
        /32874223084687105840152186783317860376636005773600
     =0.430694353276851038647760924774... .        (BG5)

This controller is exactly rational; no square-root enclosure is
used in its value. The other eleven certified margins are positive.
The result satisfies0<h<H. Hence all complete outer regions and
both inner domains satisfy(BG1).

## 3. The remaining full-capacity transition is explicit

At h=H the J coefficient vanishes. Set eta=gamma3-H*eC. The J
alternative at zero residual is nonnegative precisely through
the threshold obtained from

    t*=2*eta/(2*eta+H*eK),
    sigma_J=1-t*^2=0.0582914338822622696....

The B alternative requires

    sigma>=sigma_B=H*eK/[gamma2-H*(eB-eK)]
                 =0.0798129511760183648.... .     (BG6)

Consequently the larger threshold sigma_B controls the range
sigma>=sigma_B where both alternatives are nonnegative. These
thresholds are exact rational values in the certificate. They
describe this auxiliary bound, not an actual-family extremizer
or an optimal comparison over all possible methods.

The [helper](../frontier/three_layer_global_comparison.py) and
[certificate](../certificates/source_norms/three_layer_global_comparison.json)
retain both complete local comparisons, check all twelve
endpoint margins and their signs, and retain all eight original
fallbacks and both full terminal errors. Arbitrary labels and
infinite tails are covered by the inherited ordinary proofs.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/three_layer_global_comparison.py --check
```
