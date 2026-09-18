[Index](../marked_head_profile.md) · [Quadratic source and carrier payments](49-full-linear-and-quadratic-carriers-refine-the-frontier.md) · [Weighted marked events](90-weighted-marked-events-improve-the-global-comparison.md) · [Product escape and denominator](93-product-escape-and-source-mass-improve-global-k.md)

# Quadratic marked events and a common residual improve global K

The marked-event argument extends to all five quadratic costs with
their full six-cofactor source payment. Bounding its common residual
more closely, and retaining the shared mass of the K and J control
sets, gives the complete global bound

    K<=108497375629315363851518955981805271507882549
          /212986060315016386011231666281461556328000
      =509.4106885156833727043692... .               (QM0)

This is K0-1/20 and improves93 by exactly1/60. The construction
combines28 linear and four quadratic gains at fixed parameters;
it does not add a gain to an already-consumed target decrement.
The original curvature corrections, independent test labels,
complete tails, eight fallback branches and both full terminal
errors are retained. The box20/current8 gap remains positive at
106.4112635160015146031940... . Unrestricted Erdos #7 and arbitrary
later-prime continuation remain open. These are ordinary proofs
with exact rational checks, not Lean verification or sharpness.

## 1. Retain the quadratic source payment and its original curvature

Fix one of the five original quadratic costs f_i of49, its fixed
barrier C_i and its independent original layouts b,c5. Write

    v_l=f_i(b_l+1)-f_i(b_l),
    vmin=f_i(2)-f_i(1), vmax=f_i(4)-f_i(3),
    k_l=C_i-f_i(b_l), t_l=c5_l*v_l, alpha=6/5.

These costs are increasing and discretely convex. Profile49(Q2)
proves that the complete selected source cost psi_i has increments
at least alpha times those of f_i. Its outside source coefficient
remains1. Let M=eta tensor Haar5, W=M-Lambda>=0, and let F_J be
the original modulus5 test slot. Put

    x_v=integral_(F_J) v dW, x_J=W(F_J).

Before deletion is combined with the source, the source estimate
retains alpha*x_v as the payment for this event. The other original
test events15 and45 retain their own payments. The fixed-layout
source envelope U_i is precisely49(Q8)'s source, including

    -(4/25)*mu_i*d_eta(b,c5).

This curvature term is the loss in the final restored-cap Jensen
estimate. The marked payment is retained in the preceding source
enlargement and cap restoration, as in49(Q4); it is not a second
use of that Jensen loss. Neither psi_i nor U_i is multiplied by
alpha a second time.

Convexity and the fixed barrier give the nonnegative floors

    (C_i-f_i(A_i))_+<=k-v*(I5+I15+I45),
    (C_i-f_i(A_i)+v*I5)_+<=k-v*(I15+I45).

Use the second floor on the actual deleted measure. It retains
the exact term integral_(F_J) v ddelta and changes the selected
cap correction from t to t-v. The other two events still obey
49(Q5), using six cofactors and their own source payments. Thus
the improvement relative to the old fixed-layout comparison is
at least

    alpha*x_v+integral_(F_J) v ddelta-Pshift.       (QM1)

No identity f_i(A_i-I5)=f_i(A_i)-v*I5 is assumed. Absent selected
test labels may first be padded by arbitrary independent residues:
this raises the test cost without adding any forbidden deletion
or changing Lambda, delta, mu or the actual carrier mixture pi.

## 2. Cancel the shallow shift and keep every deep cofactor

Let q=v3+v9 be the actual ternary densities of the two shallow
virtual deletion families, and suppose q<=qstar<=alpha pointwise.
The same pi used in the old conditional comparison gives

    Psh=(1/5)*integral v*q deta.

For the six-cofactor quadratic operator, the remaining selected
depths are3,...,6. Their full coefficient is40/729. Replacing
t by t-v changes each deep entry z_l to z_l+v_l/5, so

    0<=max(z+v/5)-max(z)<=vmax/5,
    Pshift<=Psh+(8/3645)*vmax.                     (QM2)

The unselected pure3 tail remains1/1458. Its sum with40/729 is
1/18. All positive5 cofactor terms, all original7 depths, the
source square complement and the curvature term remain unchanged.

Write omega=(V-delta)(1)>=0. Since v<=vmax, bounded transfer through
this one positive measure gives

    integral_(F_J) v ddelta
       >=integral_(F_J) v*q dLambda
                         +V5(v*I_J)-vmax*omega.

The product identity integral_(F_J) v*q dM=Psh cancels the shallow
shift exactly. Consequently

    alpha*x_v+integral_(F_J) v ddelta-Psh
       >=integral_(F_J) v*(alpha-q) dW
                         +V5(v*I_J)-vmax*omega
       >=vmin*(alpha-qstar)*x_J
                         +V5(v*I_J)-vmax*omega.    (QM3)

The same proof applies to each of90's41 linear costs with alpha=1
and deep coefficient13/6075. In that case the selected depths are
3,...,5 and the unselected pure3 tail remains1/486.

## 3. A smaller cost-dependent charge against the same residual

Use85's general packing hypotheses. Let H be the best first-five
slot, r=min_J x_J, m=Lambda(F_H), and G>0 the gap from every other
slot. Its complete virtual cofactor5 family satisfies

    0<=q5<=1/5, E5>=r/5+G*q5,
    V5(v*I_H)=(1/5-q5)*integral_(F_H) v dLambda.

The factor1/5-q5 is nonnegative. Bound the entire weighted
integral below before estimating q5; this yields

    V5(v*I_H)>=vmin*m*(1/5-q5)
              >=vmin*m/5-(vmin*m/G)*(E5-r/5).      (QM4)

Thus the penalty for the missing H labels uses vmin. The separate
union error still uses vmax. These are different errors, and
85's single budget E5+omega<=rho controls their sum. Set

    p_i=max(vmax,vmin*m/G).

For J=H, (QM3)--(QM4), E5-r/5>=0 and omega>=0 give a lower bound
vmin*m/5-p_i*rho after dropping nonnegative r terms. For J!=H,
use x_J>=r+G and discard V5 to obtain
vmin*(alpha-qstar)*G-p_i*rho. Both cases therefore imply

    d_i_actual>=m_i_old+[a_i-p_i*rho]_+,
    a_i=vmin*min((alpha-qstar)*G,m/5)-D_i*vmax,     (QM5)

where D_i=8/3645 for quadratic costs and13/6075 for linear costs.
Here m_i_old is the actual pi-average of the true49 conditional
function. The retained old bound justifies the positive part.
Each bound is uniform before maximizing independently over the
original layouts and averaging with pi.

Since m<=1/9, a fixed lower bound G>=g>0 permits

    p_i<=max(vmax,vmin/(9*g)).                      (QM6)

Equivalently, for vmax>0 this is vmax*c_i with
c_i=max(1,(vmin/vmax)/(9*g)). This replaces90's coarser use of
vmax for both losses. There is still one actual rho: summing
selected inequalities with their positive old comparison weights
requires paying the sum of all their weighted p_i from the old
signed mass coefficient once.

## 4. Both low-gap control sets have the same small source mass

Let qK and qJ be the product-barycentric masses of the original K
and J zero-control sets, using the actual carrier factor pi. Their
disjointness and92's product exclusion give

    sigma=1-qK, u=1-qK-qJ=sigma-qJ,
    0<=qJ<=sigma^2, u>=sigma-sigma^2.              (QM7)

Each of the six K controls and eighteen J controls has raw source
mass1/4. The same complete1296-vertex domain has mass at most5/9.
The source mass is separately affine in the original five source
factors, so its product interpolation is exact. Using the same
normalized pi in the mass and signed-gap averages therefore gives

    0<E<=S<=s<=1/4+(11/36)*u,
    B_K>=gamma1*qJ+gamma2*u.                       (QM8)

The first inequality sharpens93 by keeping J's mass as well as
K's. These product weights describe interpolation of the actual
source parameters; they do not assume probabilistic independence
of the source from its forbidden residue labels.

For a target decrement h>0 satisfying

    gamma2-gamma1-11*h/36>=0,

combine the two estimates before eliminating qJ. Equations(QM7)
and(QM8) give

    B_K-hE>=-h/4+gamma1*sigma
                          +(gamma2-gamma1-11*h/36)*u
       >=R_h(sigma)
        :=-h/4+(gamma2-11*h/36)*sigma
                    -(gamma2-gamma1-11*h/36)*sigma^2. (QM9)

This polynomial is concave. Its minimum on[delta,1] is attained
at an endpoint. At sigma=1 its value is gamma1-h/4. No signed
escape term is added a second time. Inside the concentrated region
the weaker bound E<=1/4+11*delta/36 remains sufficient.

## 5. One fixed consumer for all46 costs

Choose the source-independent rational constants

    delta=1/44, r_star=1/840, h=1/20.               (QM10)

When sigma<=delta,71's concentration argument gives

    qstar=(1+delta)/5=9/44,
    eta_star>=1/9-delta/18, h1>=1/3-delta/6,
    Delta<=3*delta/4=3/176<1/18.

Thus85's first original source labels5,15,45 are present with
distinct first-five slots. For r<r_star the four general packing
guards, in their original order, are

    83/840, 299/4620, 8/385, 8117/325248.

Their minimum is g=8/385>0. Also

    m/5>=1/50-r_star/5=83/4200,
    e(delta)=1/4+11*delta/36=37/144.                (QM11)

Every division and first-slot guard of85's general lemma holds.
This uses its general formulas, not its smaller illustrative
cutoff1/12000. Apply(QM5)--(QM6) with

    a_i=vmin_i*min((alpha_i-9/44)*(8/385),83/4200)
                                      -D_i*vmax_i,
    p_i=max(vmax_i,(385/72)*vmin_i).                (QM12)

The five original quadratic increments and resulting gains are:

| Original tuple | vmin | vmax | a_i |
| --- | ---: | ---: | ---: |
| (0,0) | 75376570/184225041 | 1792/429 | -6783077333/6267335894820 |
| (0,1) | 15627/48334 | 175/78 | 216814889/147989041200 |
| (0,2) | 4395/48334 | 259/1014 | 36593077/29597808240 |
| (1,0) | 379438/1090089 | 28/11 | 79855319/61808046300 |
| (2,0) | 131938/1090089 | 124/363 | 304490707/185424138900 |

Keep the four positive quadratic entries, each with the original
complete comparison coefficient AC=2371/2880. Keep also the28
positive linear entries at indices

    3,4,5,6,9,11,12,13,14,15,19,20,21,22,
    25,27,28,29,30,31,33,34,35,36,37,38,39,40.

All selections depend only on the fixed original inventory and
the displayed constants. They do not depend on the actual source,
test layout or residue. The remaining13 linear costs, quadratic
tuple(0,0), and source-square complement retain their old bounds.

With exactly the old positive weights beta_i, the sums are

    Bmark=sum_selected beta_i*a_i
      =22037845256986549574060722303
          /1707837658128205225975184832000
      =0.0129039461989262425759...,

    Pmark=sum_selected beta_i*p_i
      =845440521863452293058853/77588735303934049029120
      =10.8964338515334092324657... .               (QM13)

The quadratic contribution to Bmark is
837432691474741/180499273770816000>0. All32 improvements use one
actual rho. The old mass coefficient satisfies

    A0>=Acur>Pmark,
    Acur-Pmark=43.3785461259705712754788...>0.

Consequently

    Acur*rho+sum_selected beta_i*[a_i-p_i*rho]_+
       >=Bmark+(Acur-Pmark)*rho>=Bmark.             (QM14)

In the concentrated small-r branch this gives Bmark-h*e(delta).
In the concentrated large-r branch, E5>=r/5 gives the reserve
Acur*r_star/5-h*e(delta). Outside, use the concave polynomial(QM9).
The exact four comparisons are:

| Branch | Signed margin lower bound, decimal prefix |
| --- | ---: |
| Concentrated, small r | 0.0000567239767040203537... |
| Concentrated, large r | 0.0000753920581358683749... |
| Outside, sigma=delta | 0.0001025908492670920944... |
| Outside, sigma=1 | 0.0344509357493101091336... |

All are positive. The signed sufficient comparison therefore holds
at K0-1/20 throughout the actual effective9 branch. The inherited
positive survival denominator permits division; all eight complete
fallback bounds remain below this target. This proves(QM0) on the
complete inherited source split, without patching a vertex table
or asserting its concavity.

## 6. Exact verification and remaining boundary

The [checker](../frontier/quadratic_marked_global.py) reconstructs
all46 original costs and their selected source functions. It checks
365 finite-prefix increments through their exact affine or quadratic
tail entrances, the complete source multiplier, all23000 original
layout-cell floors, the five original curvature records, the
unchanged49 barriers and weights, and the full six-cofactor shift.
It checks source mass at all1296 vertices, including all24 J/K
zero controls, and recomputes the32 gains, their common penalty,
four margins, eight fallbacks and both complete terminal errors.
The [certificate](../certificates/source_norms/quadratic_marked_global.json)
stores exact rational results and inherited source hashes.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/quadratic_marked_global.py --check
```

The all-parameter source/deletion and interpolation statements are
the ordinary proofs above and their cited predecessors; the finite
arithmetic checker does not enumerate actual covering families.
No finite-height truncation, shared choice of original test residue,
new independent measure or duplicate curvature payment is used.
The two full terminal gaps remain
106.4112635160015146031940... and106.6312089238960407303432... .
They are not negative, so this comparison does not close the
terminal threshold403 or the unrestricted covering problem.

The capacity of this particular scalar template is also explicit.
For any nonnegative concentration and slot-loss parameters in the
same formulas, g<=1/45 and qstar>=1/5. The linear source credit is
therefore at most4/225, while the quadratic credit is at most the
template's best-slot lower estimate1/50. Summing every positive
ideal cost gain, with the same deep payments and weights, gives

    Bideal=10115878772922446403539237
               /705718040548845134700489600
          =0.0143341649096219925636... .

Every fixed subset has at most this sum. The small-loss branch
requires Bmark-h*e(delta)>0 and e(delta)>=1/4, so this template
cannot certify a decrement exceeding

    4*Bideal=0.0573366596384879702545... .

Thus parameter tuning within this criterion can improve the present
decrement by at most0.0073366596384879702545... . Dropping its
other guards and residual-penalty limits only makes this capacity
bound more permissive. It is a boundary of the stated sufficient
criterion, not a lower bound on actual K;91's cell-vector method
and other changes to the comparison are outside its scope.
