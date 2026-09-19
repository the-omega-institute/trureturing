[Index](../marked_head_profile.md) · [Original marked bounds](94-quadratic-marked-events-and-a-common-residual-improve-global-k.md) · [Shared-residual comparison](100-fractional-deep-payments-improve-the-global-comparison.md) · [Reduced deep-capacity charge](102-one-root-imbalance-charge-reduces-the-deep-capacity-penalty.md)

# A smaller deep-capacity charge improves global K

The reduced capacity penalty of102 allows a fixed positive gain from
all46 original transformed costs within the same residual budget.
Keeping the existing source-escape comparison gives

    K<=21698282403925308678542128299029878116861073
          /42597212063003277202246333256292311265600
      =509.38268851568337270436921899285... .         (SG0)

The target is K0-39/500. It improves100 by13/1000, counted once from
the same K0. All eight fallback branches, both complete terminal
errors, independent original test residues and infinite exponent tails
are retained. The box20/current8 complete sufficient gap remains
106.3832635160015146031940...>0. Unrestricted Erdos7 and arbitrary
later-prime continuation remain open. These are ordinary proofs and
exact rational checks, with no Lean verification or optimality claim.

## 1. Keep the source credit and reduce its residual charge

Use100's notation for the actual margin d_i, its old carrier-averaged
bound m_i, the shared residual rho and source escape sigma=1-qK. Let
s_i=13/1215 for the41 linear costs and s_i=40/3645 for the five
quadratic costs. These are complete selected-deep coefficients, not
cutoffs for the remaining tails.

Profile102 proves, uniformly for each original independently labelled
test on the source slab,

    Q_D-P_D>=-kappa_i*E_D-s_i*C_i*chi,
    kappa_i=max(36*vmax_i/125,36*(vmax_i-vmin_i)/25).

Both root0 subsets share the same total selected-family mass s_i.
The charge for their common imbalance chi therefore remains s_i*C_i,
while the capacity defect is paid with kappa_i. The union error uses
vmax_i, which already dominates36*vmax_i/125. After the exact source
cancellation and first-slot packing argument, the fixed concentrated
bound becomes

    d_i-m_i>=b_i-t_i*rho-q_i*sigma,
    b_i=vmin_i*min((1-delta)*g/5,b_star),
    t_i=max(vmax_i,36*(vmax_i-vmin_i)/25,vmin_i/(9*g)),
    q_i=s_i*C_i/4.                                 (SG1)

As in100, replacing rho-r/5 by rho weakens the result, and
chi<=sigma/4 uses the source-escape coordinate. No additional residual
is introduced. The g, b_star and q_i meanings are unchanged.

The original94 alternative also remains valid:

    d_i-m_i>=a_i-p_i*rho,
    a_i=vmin_i*min((alpha_i-(1+delta)/5)*g,b_star)
                                         -(s_i/5)*vmax_i,
    p_i=max(vmax_i,vmin_i/(9*g)),                    (SG2)

with alpha_i=1 or6/5. Both alternatives bound the same marked credit;
use their maximum with zero, without adding their gains.

## 2. A fixed choice uses all46 costs

Fix the source-independent constants

    delta=1/27, r_star=1/520, h=39/500.

The general85 packing formulas give

    Delta<=3*delta/4=1/36<1/18,
    h1>=h_star=1/3-delta/6,
    eta_min>=eta_star=1/9-delta/18,
    g=min(1/10-r_star,h_star/5-r_star,eta_star/5-r_star,
                             h_star*(1/10-3*delta/4)-2*r_star)
      =7499/379080>0,
    b_star=1/50-r_star/5=51/2600>0.                 (SG3)

Every first-label and denominator guard holds. Choose the old
alternative(SG2) at the following27 indices:

    3,4,5,6,9,11,13,14,15,19,20,21,22,25,27,
    29,30,31,34,35,37,38,39,40,42,43,45.

Choose(SG1) at the remaining19 indices. The exact checker verifies
that this fixed choice takes the larger zero-error credit for each
cost. Every selected credit is positive. There are no fractional
coefficients in this consumer; the general convex-choice argument
from100 applies with weights0 or1.

After multiplying by the original positive comparison weights, the
credit and penalty sums are

    B=292250583636758860113407141069
        /14862421933958678536792310976000
      =0.0196637253965320908...,

    P=1349321394795027825970086351367
        /36297528025211177401364688000
      =37.1739197737606136663...,

    Q=1626740964132810385459985700332127421489
        /3154636730230866529407028478057850000000
      =0.515666653007543... .                        (SG4)

Here Q includes chi<=sigma/4. The same conservative coefficient
Acur=54.27497997750398... satisfies P<Acur. Thus all46 inequalities
share the one actual residual:

    Acur*rho+sum_i beta_i*(d_i-m_i)
                         >=B-Q*sigma+(Acur-P)*rho
                         >=B-Q*sigma.              (SG5)

The sum P concerns the actual capacity and union losses. It does not
pay source imbalance again; that charge is Q*sigma.

## 3. The existing escape polynomial covers every source branch

Retain100's joint source-mass and product-exclusion polynomial

    R_h(sigma)=-h/4+(gamma2-11*h/36)*sigma
                      -(gamma2-gamma1-11*h/36)*sigma^2.

The coefficient of the subtracted square is positive at the chosen h.
For sigma<=delta and r<r_star, (SG5) gives the signed sufficient
comparison B-Q*sigma+R_h(sigma). It is concave, so its lower bound
on[0,delta] is the minimum of its two endpoint values.

If sigma<=delta and r>=r_star, the actual defect gives rho>=r_star/5.
Using E<=1/4+11*delta/36 gives the large-r margin below. Outside
concentration, use R_h and its endpoints delta,1. The exact five
strict margins are:

| Case | Signed margin lower bound |
| --- | ---: |
| Small r, sigma=0 | 0.0001637253965320908... |
| Small r, sigma=delta | 0.0010221196174648132... |
| Large r | 0.0004922762496572764... |
| Outside, sigma=delta | 0.0004571591471380198... |
| Outside, sigma=1 | 0.0274509357493101091... |

The target decrement is the entire term-hE applied once to the old
comparison at K0. The coefficient Acur remains a conservative bound
for the original residual before that term is subtracted, as in100.
No old target decrement is added to the present one.

The inherited positive survival lower bound permits division; the
checker retains all eight complete fallback comparisons and verifies
they lie below the target. Both full core errors remain positive
obstructions to reaching403. This proves(SG0) on the entire inherited
source split, without using the separate saturated-face comparison
as though it were a neighborhood theorem.

## Reproduction

The [checker](../frontier/shared_root_global.py) pins102's stronger
bridge,94's exact46-cost inventory and100's complete predecessor. It
reconstructs both alternative coefficient vectors, checks agreement
with102's exported general interface, verifies the fixed selections,
all source guards, the single residual budget, five signed margins,
eight fallbacks and two full terminal errors. Its
[certificate](../certificates/source_norms/shared_root_global.json)
retains the complete exact comparison.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/shared_root_global.py --check
```

The reusable new input is the smaller deep-capacity charge of102.
The rational constants here provide one valid consumer. They do not
assert a maximal decrement, a truncation of infinite labels, or a
resolution of unrestricted Erdos7.
