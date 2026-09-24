[Index](../../marked_head_profile.md) · [Shared slot-defect geometry](117-the-actual-slot-defects-share-a-stronger-packing-polytope.md) · [Previous complete comparison](107-carrier-mass-and-the-shared-residual-improve-global-k.md)

# The shared slot gap enters the complete global comparison

The stronger source gap from117 increases the summed marked credit and
reduces its shared residual penalty for the same46 cost choices used
in103 and107. With the fixed source rectangle and target decrement
31/250, the complete seven-branch comparison gives

    K<=108481614660852052638954124838500443352714277
          /212986060315016386011231666281461556328000
      =509.33668851568337270436921899285858... .     (GG1)

This is1/250 below107. All eight fallback branches, two complete terminal
errors and every original exponent tail remain. The box20/current8
complete sufficient gap remains106.3372635160015146...>0. Unrestricted
Erdos #7 and arbitrary later-prime continuation remain open.

The numerical improvement must be attributed precisely. The same fixed
target decrement31/250 also passes all seven branches with107's old
packing gap. Thus the1/250 target change uses previously available
numerical margin; it does not require the new geometric gap. The new
geometry separately and strictly improves the complete credit and
residual coefficients displayed below. The certificate verifies both
statements with exact rational arithmetic.

These are ordinary proofs and exact arithmetic checks, not Lean
verification or an optimality claim.

## 1. The new gap is valid on the entire original rectangle

Keep the actual source escape sigma=1-qK and exactly the old rectangle

    delta=1/27, r_star=1/520,
    0<=sigma<=delta, 0<=r<=r_star.

By117, the common source deficit budget yields

    h1>=1/3-delta/18=161/486,
    eta_L>=1/9-delta/18=53/486,
    Delta<=3*delta/4=1/36.

All first-label forcing and distinct-slot conditions hold. The four
packing guards are positive, and their minimum is

    G=2513/126360=7499/379080+1/9477.              (GG2)

In particular the fourth guard is4567/227448, greater than(GG2).
The inclusive r cutoff is covered by117's general proof. There is no
use of85's numerical r<1/12000 branch at r=1/520.

The existing best-slot mass credit and carrier bounds remain

    b_star=1/50-r_star/5=51/2600,
    q_star=(1+delta)/5, w_deep=(1-delta)/5.

The stronger joint5/15 defect polygon is not added as a second gain
in this consumer. Only its proved packing consequence(GG2) is
substituted into the existing cost interfaces.

## 2. Substitute the gap in both existing alternatives

For each original cost i, retain its exact weight, barrier C_i, low
increments vmin_i,vmax_i, and full selected-deep coefficient s_i.
Here s_i=13/1215 for linear costs and40/3645 for quadratic costs.
The unselected complement still makes the total pure3 coefficient1/90.

The old marked alternative from94 and the retained-deep alternative
from102 become

    old_credit_i=vmin_i*min((alpha_i-q_star)*G,b_star)
                                              -vmax_i*s_i/5,
    old_penalty_i=max(vmax_i,vmin_i/(9*G)),

    deep_credit_i=vmin_i*min(w_deep*G,b_star),
    deep_penalty_i=max(vmax_i,36*(vmax_i-vmin_i)/25,
                                              vmin_i/(9*G)),
    escape_penalty_i=s_i*C_i/4.                    (GG3)

The coefficient alpha_i is1 or6/5 according as the cost is linear
or quadratic. The source cancellation, surviving curvature, full
cofactor tails and common residual meanings are unchanged. Replacing
a valid lower packing gap by the stronger valid(GG2) increases both
credits and decreases or preserves both residual penalties. It does
not change the root-imbalance charge.

Use precisely107's27 old and19 retained-deep choices, with no new
selection or fractional interpolation. Each is a valid lower bound
for the same original cost. After multiplying by the original
positive weights, the complete inequality is

    sum_i weight_i*(d_i-m_i)>=B-P*rho-Q*sigma,      (GG4)

where

    B=13984949245536176840531588729
                /707734377807556120799633856000
      =0.019760166644524508265796815...,

    P=451896694199085314479664772229
                /12163713552121041313459056000
      =37.1512114505759682369320510...,

    Q=1626740964132810385459985700332127421489
                /3154636730230866529407028478057850000000.

Compared with107, the changes due to the new gap alone are exactly

    B-B_old=8958440746880334610976389
                    /92890137087241740854951943600>0,

    P_old-P=2212986454021531388697515
                    /97452658042046676078663954>0,
    Q-Q_old=0.                                    (GG5)

The underlying rho-r/5 may be weakened to rho, as before. Each cost
keeps its independent original test. No gains for alternative proofs
of the same cost are added together.

## 3. The complete shared-residual comparison

Take the fixed decrement

    h=31/250.

Retain107's conservative actual residual coefficient Acur and106's
complete denominator bound

    E<=a+b*sigma+rho,
    a=53/360, b=5/9, 0<=sigma<1/2.

Thus the available residual coefficient is Acur-h, and the checker
verifies Acur-h>P. With the same two source-escape layers gamma1,gamma2,
put

    W_h(sigma)=gamma2*sigma-(gamma2-gamma1)*sigma²
                                             -h*(a+b*sigma),

    R_h(sigma)=-h/4+(gamma2-11*h/36)*sigma
                     -(gamma2-gamma1-11*h/36)*sigma². (GG6)

Both are concave on their required intervals. For concentrated small r,
(GG4) and the single residual budget give B-Q*sigma+W_h(sigma).
For concentrated large r, the actual bound rho>=r_star/5 gives

    (Acur-h)*r_star/5-h*(a+b*delta).               (GG7)

For delta<=sigma<1/2, use W_h alone. Its value at1/2 is a limiting
polynomial endpoint; the strict-domain denominator theorem is not
applied there. For1/2<=sigma<=1, use R_h alone and the original global
raw-mass bound. There is no addition of two denominator reserves.

The seven exact rational margins are positive:

| Complete branch | Margin lower bound |
| --- | ---: |
| Small r, sigma=0 | 0.00150461108896895271024... |
| Small r, sigma=delta | 0.000661587843052109479256... |
| Large r, sigma<=delta | 0.0000203041065740222593076... |
| Middle, sigma=delta | 0.000000186124732898684919370... |
| Middle, limit sigma=1/2 | 0.104436625756375344900... |
| Far, sigma=1/2 | 0.116664403534153122678... |
| Far, sigma=1 | 0.0159509357493101091337... |

The minimum is the exact positive fraction

    132128101609358147424843724860684819563366963273
      /709890080440199842560984160784104546543403532000000000.

Concavity reduces each entire sigma interval to its listed endpoints.
The original positive survival lower bound justifies division. All
eight complete fallbacks remain below the new target, and both full
terminal errors are unchanged. This proves(GG1), subtracting h once
from K0.

## 4. Attribution control and verification

The checker also substitutes B_old,P_old,Q_old from107 while keeping
exactly the same h and all other data. All seven margins remain
positive and Acur-h>P_old. Therefore the stated target was already
available inside the old complete comparison. Claiming that(GG1)
requires117's geometry would be false.

The strict coefficient improvements(GG5) are the additional mathematical
benefit of117 in this consumer. The middle escape branch does not use
those cost coefficients; it supplies the smallest margin at the chosen
target. No parameter sweep or optimal decrement is asserted.

`frontier/source-budgets/shared_slot_gap_global.py` reconstructs107 and117, recomputes
all46 rows, retains their original fixed choices, verifies the shared
residual after the denominator payment, and checks all seven margins,
eight fallbacks and two complete errors. Its certificate records exact
fractions and the old-gap attribution control.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/shared_slot_gap_global.py --check
```

No saturated-face comparison has been extrapolated to this neighborhood.
The global sufficient threshold403 remains out of reach of this bound.
