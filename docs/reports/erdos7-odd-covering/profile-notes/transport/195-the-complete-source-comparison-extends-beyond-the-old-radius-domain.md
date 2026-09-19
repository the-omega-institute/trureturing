[Index](../../marked_head_profile.md) · [Original concentration domain](../106-the-actual-denominator-shares-the-carrier-mass-residual.md) · [Joint loss budget](../153-the-six-source-losses-share-one-actual-concentration-budget.md) · [Exposed prices](../156-exposing-each-loss-gives-exact-rational-joint-price-bounds.md) · [Full-slot heavy extension](../169-the-complete-source-bound-needs-no-independent-slot-loss-cutoff.md)

# The complete source comparison extends beyond the old radius domain

The original complete source construction is valid on the larger
actual-source rectangle

    sigma<=1/12, rho<=1/3000, r<=5rho.             (ED1)

On this whole rectangle its complete bound is

    K<=499.194491675541964774309023313...<500.

Both K orientations, every admissible first-beta distribution and
all original independent residue labels remain. The extension uses
the original pointwise cap, mean and tail derivations with their
domain conditions proved below. It does not apply a predecessor's
radius-limited theorem beyond its stated interval.

## 1. Concentration supplies a smaller actual geometric loss

Put delta=1/12 and R=1/3000. The orientation theorem106 applies
whenever sigma<1/2. It gives one orientation in which each of the
six supported source factors is at least1-sigma. No2/27 condition
occurs in that theorem.

Write ua,uz,ub,ud,ul,up for the same six losses as153/156, and
Delta=(ua+uz+ub)/4. Their established general bounds imply

    sum u<=delta/(1-delta)=1/11,
    Delta<=1/44<1/18,
    Delta<=3delta/[4(3-2delta)]=3/136,
    z<=3/4+delta/4=37/48<4/5.                    (ED2)

The second Delta bound uses156's support for the three equal
availability prices. The first suffices for the cap increments
and162's zero-slot-loss slab. This replaces the old sufficient
condition3delta/4<=1/18; that coarse condition is not required
of the actual source once(ED2) is retained.

The same deficit concentration gives

    h>=1/2, h1>=71/216, eta_L>=23/216,
    h1-h0>=17/108, h<=109/216.                   (ED3)

The first-label source floor1/4-3delta/4=3/16 exceeds1/20.
Together with Delta<1/18, the general85/117 packing argument forces
the original labels5,15,45 and their three distinct slots P,A,B.
The usual relabeling puts the first-beta cell at2.

There is no circular use of a small slot cutoff. Since H maximizes
the actual modulus5 slot mass, every5*7^e cofactor contributes at
most that mass. Their full weights sum to1/5, so E5>=r/5 even
before a positive wrong-slot gap is chosen. The original defect
identity E5<=rho therefore gives r<=5rho<=1/600.

## 2. The whole slot range has positive packing gaps

At rbar=1/600, the five general117 gap guards are

| Guard | Uniform lower bound |
| --- | ---: |
|h/5-r|59/600|
|h1/5-r|173/2700|
|eta_L/5-r|53/2700|
|h1(1/10-Delta)-2r|16367/734400|
|(h1-h0)/5-r|161/5400|

In the fourth row use Delta<=3/136. Every row decreases as the
source or residual radius increases: the source lower masses
decrease, while the positive availability loss increases. Hence
these endpoint lower bounds hold on all of(ED1). They include
wrong-root and absent-label cases and ensure that H is distinct
from P,A,B.

Choose

    G=53/2700, R/G=9/530<1/5.                    (ED4)

The seven actual shifted defects are nonnegative and share the
single residual R-G(q5+q15). The common polygon therefore has
vertices(0,0),(9/530,0),(0,9/530), with remaining residuals(R,0,0).
No separate allocation of R to different objectives is introduced.

## 3. Reconstruct the actual finite head and source ratios

Let U=delta/(1-delta)=1/11. The original134 cap derivation uses
only the exact source exclusions, the component bounds in(ED3)
and the slot ratios r/h<=2r and r/h1<=r/(71/216). Thus it gives

    v0=U/4+2rbar=43/1650,
    v1=U/4+rbar/(71/216)=2171/78100.             (ED5)

These are below1/20 and1/10, respectively. In particular the
factorial pre-cap bounds3/20+v0 and1/10+v1 remain below1/5.
The finite LP uses the same25 entries and three disjoint groups.
Its cap increments are delta/90 in nonexcluded cell0 entries,
with an additional v0/18 in that cell's Q entry, v0/9 in cell1's
Q entry, and v1/9 in root1 Q entries. All other increments are
zero. The product bound charges the cell0 eta change at the full
slot cap1/5, so no delta*r product is omitted.

157's group-budget proof before any radius restriction gives

    dN=((3+delta)U/72,delta/36,U/12)
      =(37/9504,1/432,1/132).                   (ED6)

Each actual source has the same exact zero entries as the face.
Its nonzero carrier score is at least1-delta=11/12. Thus134's
coefficient domination Z<=Zface+(delta/5)V applies on every entry.
The actual feasible head is contained in this new finite LP.
Its coefficients remain affine in the common q variables, so its
maximum remains convex in q. These statements do not use an old
numerical head maximum.

The original actual ratios have the valid bounds

    tbar=2(1+delta)/(1-4delta)=13/4,
    Cbar=(3/4+delta/4)/(1/5-3delta/8)=370/81,
    kbar=(6-delta)/(3-2delta)=71/34.             (ED7)

Their derivation uses R3<=1/2+delta/2, D-R3>=1/4-delta,
the forced27 gap, and the root deficit bounds of134. Here
D=max_l d_l and R3=max_(l>=2)d_l are availability densities;
R is the separate residual radius. All denominators are positive.

The complete interval conditions needed by134,152,157 and158 are

| Expression | Lower bound on[0,1/12] |
| --- | ---: |
|1-4delta|2/3|
|6-49delta-70delta^2|103/72|
|42-35delta^2|6013/144|
|3delta^2-23delta+3|53/48|
|2-7delta-delta^2|203/144|
|4-5delta-3delta^2|57/16|
|1-delta-delta^2|131/144|

They are decreasing on this interval; the fourth has derivative
6delta-23<0. Also8-15delta>=27/4 and3-2delta>=17/6. The second
row proves Cbar>=1+tbar. The third is a conservative lower bound
for the numerator42+68delta-35delta^2 of Cbar-kbar. The fourth
retains the maximizing pure3 reference cell. The last three prove
the root and cell dominance comparisons used in157/158. Hence no
comparison is inferred solely from its value at the former radius.

## 4. The source mean, shallow indicators and all tails extend

134's selected-operator error bound follows from the cap and score
bounds just proved. Its signed mean correction comes from133 SM13,
which is valid for an arbitrary actual source in the packing domain:

    Aface-A+X<=299sigma/10800+4u/135,
    u<=r/h, E5-Gq5>=r/5.

Since h>=1/2, the last term is paid by(8/27)(E5-Gq5).
This uses the same residual coordinate and keeps the H/Q slot
migration. It does not require the former2/27 wrapper.

152's individual shallow-cylinder proof now applies with(ED7).
Its fixed capacity duals retain all source/residual product terms;
its modulus3 calculation retains both actual H-column identities.
The141 original cases are evaluated independently, rather than
assuming their former maximizing residues persist.

The complete reference and raw-minus-reference envelopes are

    cbar=(7/10+delta/4,2/5+13delta/90,
                         4/15+delta/15,4/45+delta/45),
    Hbar=(1/20+21delta/20-delta^2/5,
          1/10+(19delta+2delta^2)/90,
          1/15+delta/9,1/45+delta/30-delta^2/360). (ED8)

134 derives these directly from the source lower references and
carrier scores. Its only maximizing-cell condition is the positive
fourth polynomial above. The other lower references follow from
h>=1/2, t0<=2delta, t_c<=1+delta and the nonselected deficit budget.
All four cbar and Hbar values are positive on the new interval.

The complete family errors remain(kbar*R,R+delta/240,R,R), using
0<=z-D<=3delta/8. Every fixed support retains its entire geometric
or polynomial tail. The factorial construction138 uses these same
caps, its actual forced27 error and lower/upper density envelopes;
their25 pre-cap/density entries satisfy their original inequalities.
Its nonnegative old/old pair multiplicities are unchanged. The
original raw81 continuity bounds use106's general source norms,
which already hold for sigma<1/2.

The joint pure-five bound has positive reference densities

    (0,2003/12960,4259/12960,89/216,89/216),

all below hbar=109/216. Its original complete error estimate and
the shallow indicator share the same E3+omega+delta/240 term.
Thus both available pure-five bounds can be evaluated and their
minimum used in the complete square.

## 5. Reprove both complete seven-containing price bounds

158's raw-mass expansion and its pointwise scalar source bounds
remain valid here. The only extra root comparison is

    R0<=1/9+(7delta+delta^2)/72<=5/36,

which follows from2-7delta-delta^2>0. It allows the root1 upper
price to bound N3=max(R0,R1). The bounds on N9,D,h,h1,max eta
are direct source inequalities. Thus the same raw coefficient
expansion gives the six-loss price vectors

    pZ=(1/420,3/280,1/1260,4/3150,0,0),
    pF=(1/36,13/180,1/108,(146+5delta)/10800,1/2160,0).

Their largest coordinate is z, and their second-largest prices
are1/420 and1/36 throughout this interval. At its endpoint the
two156 price-gap margins are

    (1-1/12)*(3/280)-1/420=5/672>0,
    (1-1/12)*(13/180)-1/36=83/2160>0.

The other prices are smaller, including
(146+5/12)/10800<1/36. Therefore156's general exposed-price
theorem applies to the same actual loss vector and proves

    Zplus<=779/12600+3delta/280=3161/50400,
    Fseven<=103/180+13delta/180=1249/2160.        (ED9)

The complete geometric pair coefficients are reconstructed from
the original definitions before applying these prices. No negative
moment is bounded separately, and no source-price wrapper whose
stated domain ends at2/27 is called.

## 6. The full heavy slot range uses one actual residual

At r=0, (ED2) and the forced first-beta condition place the whole
source in162's fixed-support slab. Both absolute heavy margins
therefore hold with every deficit/late factor and all original
carriers still present.

169's pointwise movement proof uses only h>=1/2 and h0<=2/9:
its price is at most vmax*r*(h0/h+1)<=(13/9)vmax*r. Here the
general marker price has coefficient

    max(1,hbar/(5G))=545/106<65/9.

For epsilon=rho-(r+r1)/5>=0, the same actual residual pays

    (13/9)vmax*r+(65/9)vmax*epsilon
        <=(65/9)vmax*rho.                       (ED10)

The two heavy floors and one-residual prices12491905/792792 and
18197065/1459458 are consequently valid throughout(ED1).
The older positive-r cutoff1/2500 is not assumed at rbar=1/600;
the extension follows from(ED10) and the newly proved gap guards.

## 7. A complete new original-head calculation supplies the consumer

With the new caps, group budgets, source scores and the three
vertices in(ED4), the calculation evaluates all26 original
objectives: five denominator costs, H2, eleven mean costs and
nine quadratic costs. Each uses12500 original layouts and ten
independent positive-seven projections at each vertex. All
9,750,000 original heads are evaluated afresh, and312 independent
rational LP comparisons agree with the integer computation.

The mean and factorial contributions are combined on each original
layout before maximizing. Complete tail supports keep their full
geometric and polynomial continuations. The complete square uses
the smaller of its original pure-five contribution and the joint
pure-five estimate; the original contribution is smaller on this
rectangle, so no pure-five saving is claimed.

All original indices0,...,51 occur exactly once. At A=53/360,
the complete signed numerator endpoint and denominator bound are

    N=36.385739889110578545144427598...,
    d=0.076184489571967815186968539...>0.         (ED11)

For the original offset C0 and cE=1-1/614922, the target is

    K=C0+N/d
     =11353028672181746035778282729858256414067818124216579
      /22742696206593554647442710232848603094640810000000
     =499.194491675541964774309023313... .         (ED12)

The complete remaining actual-mass coefficient is positive:

    (K-C0)cE-M=408.751717720781824437517446217...,
    M=68.847868785989060471933474022... .         (ED13)

Consequently the comparison holds for every actual S>=A, with
all five original survival objectives and the remaining count
tail retained. The numerical result consumes the enlarged-domain
proof above; it is not inferred from a narrower source scan.

The [helper](../../frontier/transport/extended_source_bridge_comparison.py),
[complete certificate](../../certificates/source_norms/extended_source_bridge_comparison.json)
and [fresh original heads](../../certificates/source_norms/extended_source_bridge_heads.json)
retain the exact source closure and all domain, inventory and
complete-tail data. Reconstruct the canonical comparison with

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/extended_source_bridge_comparison.py --check
```

Adding `--scan` independently reevaluates all original heads.
This is an ordinary continuous-source theorem with exact rational
certificates, not Lean kernel verification or an actual-family
attainment statement. A global consumer must separately cover
the complement of(ED1). Unrestricted Erdos7 remains unresolved.
