[Index](../marked_head_profile.md) · [Complete cost choices](103-a-smaller-deep-capacity-charge-improves-global-k.md) · [Carrier mass bound](106-the-actual-denominator-shares-the-carrier-mass-residual.md)

# Carrier mass and the shared residual improve global K

Using the actual mass identity in the denominator improves the complete
global comparison to

    K <= 108482466605093312704498169765165569198939589
           /212986060315016386011231666281461556328000
       = 509.340688515683372704369218992858... .       (CG1)

The target is K0-3/25, improving103 by21/500. The46 cost choices and
source parameters are exactly those of103. The improvement comes from
using the carrier-averaged lower mass and the actual residual together
when bounding the denominator. All eight fallback branches, both full
terminal errors and every infinite exponent tail remain included.
The box20/current8 complete sufficient gap is still
106.3412635160015146031940...>0. Unrestricted Erdos7 and arbitrary
later-prime continuation remain open. These are ordinary proofs and
exact rational checks, with no Lean or optimality claim.

## 1. Pay the denominator from the same mass budget

Keep103's actual residual rho=S-S0, source escape sigma=1-qK, and
the original positive complete denominator E. Write B_escape for the
original product-interpolated signed reserve. Its two positive layers
gamma1,gamma2 satisfy

    B_escape >= gamma2*sigma-(gamma2-gamma1)*sigma². (CG2)

Indeed94 gives B_escape>=gamma1*qJ+gamma2*u, where
qJ+u=sigma and u>=sigma*(1-sigma). Substitution proves(CG2).
The actual signed comparison at K0 also retains the nonnegative
residual term Acur*rho and all marked-cost gains. Here Acur is103's
conservative coefficient54.27497997750398....

For0<=sigma<1/2,106 proves the actual denominator inequality

    E <= 53/360+5*sigma/9+rho.                     (CG3)

Consequently a target decrement h>0 gives

    Acur*rho-hE
      >= (Acur-h)*rho-h*(53/360+5*sigma/9).         (CG4)

The rho in(CG3) is the same rho as in(CG4) and in every cost loss.
It cannot be dropped from the denominator. The combined coefficient
must be checked after subtracting h.

Set

    W_h(sigma)=gamma2*sigma-(gamma2-gamma1)*sigma²
                                      -h*(53/360+5*sigma/9).

This is concave because gamma2>gamma1. Without any extra marked gain,
the signed comparison at K0-h is at least W_h(sigma), provided
Acur-h>=0. The proof of(CG3) holds on the whole stated half-neighborhood;
it does not require sigma<=1/18 or preservation of a maximizing carrier.

## 2. The46 existing cost choices still fit after this charge

Retain103's fixed constants and all four first-slot packing guards:

    delta=1/27, r_star=1/520, G_star=7499/379080.

The27 old marked alternatives and19 retained-deep alternatives remain
unchanged. Each original cost selects one valid inequality, retaining
its own independently labelled test. Their weighted sum is

    sum_i weight_i*(d_i-m_i) >= B-P*rho-Q*sigma,

where B,P,Q are exactly103(SG4):

    B=0.0196637253965320908...,
    P=37.1739197737606136663...,
    Q=0.515666653007543... .                       (CG5)

These are rational sums over all46 rows; the certificate retains the
exact fractions and reconstructs each row from the original source
interfaces. Nothing from105 or the separate saturated-face comparisons
is added to these costs.

Take h=3/25. The available residual coefficient and its reserve are

    Acur-h = 54.1549799775039805079445...,
    Acur-h-P = 16.9810602037433668416444... > 0.    (CG6)

For sigma<=delta and r<r_star, combining(CG2)--(CG6) gives

    Phi_(K0-h) >= B-Q*sigma+W_h(sigma).

Its minimum on[0,delta] is at an endpoint. The positive part in each
individual cost inequality only makes this fixed affine sum stronger.
The stronger original budget rho-r/5 may be weakened to rho as in103;
no second residual or second source credit is introduced.

If sigma<=delta and r>=r_star, the actual defect satisfies
rho>=r_star/5. Drop the nonnegative escape reserve and marked gains,
then(CG4) gives the separate lower bound

    Phi_(K0-h) >= (Acur-h)*r_star/5
                                  -h*(53/360+5*delta/9). (CG7)

## 3. Two complementary escape ranges cover every other source

For delta<=sigma<1/2, apply W_h directly. Concavity bounds it below
by the smaller of W_h(delta) and its polynomial value W_h(1/2).
The latter is a limiting endpoint bound;106's denominator theorem
is not applied at sigma=1/2.

For1/2<=sigma<=1, use94's original complete raw-mass estimate and
product exclusion instead. They give

    Phi_(K0-h) >= R_h(sigma),
    R_h(sigma)=-h/4+(gamma2-11*h/36)*sigma
                        -(gamma2-gamma1-11*h/36)*sigma². (CG8)

The subtracted quadratic coefficient remains positive. Its two
endpoint values therefore suffice on[1/2,1]. This branch uses(CG8)
alone; it does not add two denominator estimates or reuse the residual
already charged in(CG4).

The complete seven rational margins are strictly positive:

| Branch endpoint or case | Signed lower bound |
| --- | ---: |
| Small r, sigma=0 | 0.0019970587298654241453... |
| Small r, sigma=delta | 0.0012363400106975521077... |
| Large r, sigma<=delta | 0.0006930359837503438800... |
| Middle, sigma=delta | 0.0006713795403707587672... |
| Middle, limit sigma=1/2 | 0.1061366257563753449004... |
| Far, sigma=1/2 | 0.1179699590897086782337... |
| Far, sigma=1 | 0.0169509357493101091336... |

Thus the new target holds throughout the effective source branch.
The original positive survival lower bound justifies division. All
eight complete fallback bounds are below the new target; both full
terminal errors are carried unchanged. This proves(CG1). The decrease
3/25 is subtracted once from K0, rather than added to any preceding
decrease.

## Reproduction and scope

[carrier_mass_global.py](../frontier/carrier_mass_global.py) pins106's
complete mass interface and103's complete consumer. It reconstructs
the46 cost choices, checks their original guards and common residual
budget after the h*rho payment, and verifies all seven endpoints,
eight fallbacks and two full errors. Its
[certificate](../certificates/source_norms/carrier_mass_global.json)
retains the exact fractions and source bindings.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/carrier_mass_global.py --check
```

The new input is the actual relation S=S0+rho in the denominator.
Neither the cost choices nor the local saturated-face numerator is
retuned or extrapolated. The resulting global comparison still exceeds
the sufficient threshold403; it is not a proof of unrestricted Erdos7.
