[Index](../../marked_head_profile.md) · [Weighted marked events](90-weighted-marked-events-improve-the-global-comparison.md) · [Product exclusion and mass](92-the-next-k-escape-layers-and-product-exclusion.md) · [Complete global comparison](74-a-strict-global-k-gain-from-the-controlling-faces.md)

# Product escape and source mass improve global K

Using the same product weights to control the two low-gap regions
and the actual comparison denominator gives the complete global bound

    K<=108500925396987280791285809842909962533821349
          /212986060315016386011231666281461556328000
      =509.4273551823500393710358... .                 (PE1)

The improvement over90 is0.0302032709500459927244... . It comes
from the original target K0 minus1/30, with no preceding increment
added again. It uses90's general linear marked-event theorem and
92's product exclusion, without assuming any new quadratic or
deep-event improvement. All original test residues remain independent,
all exponent tails remain complete, and the eight fallback branches
and two terminal errors are retained. The box20/current8 gap above
403 is106.4279301826681812698607... . Unrestricted Erdos #7 remains
open. This is ordinary mathematics with exact rational checking,
not Lean verification or a sharpness claim.

## 1. Escape and comparison mass share one product representation

Let qK and qJ be the product-barycentric masses of the original
K and J zero-control sets, using the same actual carrier mixture pi.
Put sigma=1-qK. Write gamma1=gamma_K and gamma2 for92's next gap.
The already proved old comparison at K0 obeys

    Phi_K0_old>=B_K+A0*rho,
    B_K>=gamma1*qJ+gamma2*(1-qK-qJ),                (PE2)

where rho=S-sum_c pi_c*D_c>=0 is the one actual mass residual.
The K and J sets use complementary regions of both the late
source factor and the carrier factor. Profile92 proves

    qJ<=sigma^2,
    B_K>=Q(sigma)
       :=gamma2*sigma-(gamma2-gamma1)*sigma^2.       (PE3)

The denominator E appearing when the target changes satisfies
0<E<=S<=s. The source mass s is separately affine in each of the
five source factors: each cell mass is

    (1-deficit_l)*(z-alpha_ROOT(l)-beta_l)/9-late_l.

Its product interpolation is therefore an equality. All K controls
have s=1/4; all source vertices have s<=5/9. Including the same
normalized pi leaves s unchanged, and gives

    E<=e(sigma):=1/4+11*sigma/36.                   (PE4)

No independence of the actual source and its forbidden labels is
assumed. The product distribution is the barycentric representation
of the source parameters used by the old separately concave proof.
It has the actual pi as its carrier factor throughout.

For any target decrement h>0,

    Phi_(K0-h)=Phi_K0-hE.

The function Q(sigma)-h*e(sigma) is concave. On any closed interval
its minimum is at one of the two endpoints. Thus the escape region
does not require replacing its whole mass by the old small gap
gamma1, or replacing its denominator independently by5/9.

## 2. Fixed concentration and packing constants

Choose constants independently of the actual source and test labels:

    delta=2/125, r_star=1/1250, h=1/30.             (PE5)

If sigma<=delta, the concentration argument of71/90 gives a
distinguished carrier of weight at least1-delta whose root1 and
root0 cell are disjoint. In the notation of90,

    1-v3-v9>=w=1-(1+delta)/5,
    eta_star>=1/9-delta/18,
    h1>=1/3-delta/6,
    Delta<=3*delta/4=3/250<1/18.                    (PE6)

Consequently the first original source labels5,15,45 are present
and have distinct first-five slots, by85. For r<r_star the general
packing lemma of85 gives

    G>=min(1/10-r_star,
           (1/3-delta/6)/5-r_star,
           (1/9-delta/18)/5-r_star,
           (1/3-delta/6)*(1/10-3*delta/4)-2*r_star)
      =239/11250>0.

    c=max(1,(1/9)/Gstar)=1250/239,
    min(w*Gstar,1/50-r_star/5)=19837/1171875.        (PE7)

All required bounds r<h/5,r<h1/5,r<eta_star/5 hold. Here h/5
in those packing hypotheses denotes the raw ternary mass divided
by5, as in85; the target decrement in(PE5) is a separate scalar.
The general packing lemma, rather than85's illustrative numerical
cutoff, justifies the chosen r_star.

For each of the41 complete linear costs let vmin_i and vmax_i
be90's exact first and third discrete increments. Its old source
and deletion floors, complete affine tail and comparison weight
beta_i are unchanged. The uniform theorem90(WM12) gives

    d_i_actual>=m_i_old+[a_i-c*vmax_i*rho]_+,
    a_i=(19837/1171875)*vmin_i-(13/6075)*vmax_i.     (PE8)

Keep the28 positive a_i, at fixed inventory indices

    3,4,5,6,9,11,12,13,14,15,19,20,21,22,
    25,27,28,29,30,31,33,34,35,36,37,38,39,40.

Their weighted gain and total penalty are exactly

    Bmark=4420337790413827756721045171
             /510502054795171538411812500000
         =0.0086588050898000743257...,
    Pmark=21225037375/1073704632
         =19.76804117484705048753... .               (PE9)

The conservative old signed mass coefficient Acur from74 satisfies
A0>=Acur>Pmark. All costs share rho, so

    Acur*rho+sum_i beta_i*[a_i-c*vmax_i*rho]_+
       >=Bmark+(Acur-Pmark)*rho>=Bmark.             (PE10)

The13 remaining linear costs, all five quadratic costs and the
source square retain their full old inequalities. Different costs
retain their own independent original test events; none of the28
selected gains assumes their residues or layouts coincide.

## 3. Four endpoint checks cover the full actual branch

If sigma>=delta, discard the nonnegative new gains and retain
(PE3). Concavity reduces positivity after decreasing the target
to the two numbers Q(delta)-h*e(delta) and Q(1)-h*e(1).

If sigma<=delta but r>=r_star, the always-valid cofactor5 capacity
deficiency gives rho>=r_star/5. The reserve is at least
Acur*r_star/5-h*e(delta), after discarding B_K>=0.

In the remaining case apply(PE10) and e(sigma)<=e(delta). Its
reserve is at least Bmark-h*e(delta). The exact checks give:

| Branch | Signed margin lower bound, decimal prefix |
| --- | ---: |
| Concentrated, small r | 0.0001625087935037780294... |
| Concentrated, large r | 0.0001877005001043405849... |
| Outside, sigma=delta | 0.0006723637544518824538... |
| Outside, sigma=1 | 0.0284324172307915906151... |

All are strictly positive. In particular the complete signed
comparison holds at K0-1/30 throughout the effective9 source
branch. The unchanged positive-survival bound ensures division
by the actual denominator remains valid. The exact checker also
compares every one of74's eight complete fallback bounds with
the new target and carries both complete terminal errors forward.

## 4. Reproducible result and remaining boundary

The [checker](../../frontier/source-budgets/product_escape_global.py) pins90's
complete cost inventory and92's full signed-table classification,
recomputes every new source guard and all41 gains, accumulates
the28 penalties against the same mass term, and checks all four
signed margins, eight fallbacks and two core errors. Its
[certificate](../../certificates/source_norms/source-budgets/product_escape_global.json)
stores exact rational results. The ordinary proof establishes
the all-parameter and all-residue statements; the arithmetic
checker is not an enumeration of actual covering families.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/product_escape_global.py --check
```

The useful structural fact is that concentration, escape and the
mass denominator depend on the same source coordinates. Their
extremal bounds cannot be treated as unrelated worst cases without
losing information. This improvement still leaves a positive gap
to403 and does not settle the arbitrary later-prime continuation.
