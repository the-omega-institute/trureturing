[Index](../../marked_head_profile.md) · [Complete survival comparison](203-the-expanded-seven-head-improves-the-complete-survival-denominator.md) · [First-depth bridge and selected intersections](201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md)

# A second seven depth strengthens both complete heavy costs

The complete arbitrary-residue bridge can retain147=3*7² and245=5*7²
alongside201's first-depth labels21,35,63,105. The additional two old
projections keep distinct original test labels at the second seven depth.
Every omitted label remains in a complete nonnegative cap series.

The new bounds apply on both entire actual saturated K faces, with
r=rho=0 and common survivor mass D=53/360. They strengthen the two
original heavy costs0 and16 in203's complete52-cost comparison. The
complete199 square,202's integer identities,203's denominator and
its quadratic41 improvement remain in place.

The resulting full comparison is

    K<=2339779825623119932873783867480513340400113
        /5403859595209570937396996220316137000000
      =432.9830900301878... .

Its improvement over203 is exactly

    76395662488632300/28570475937986437
      =2.6739373419768... .

The bound remains above the sufficient threshold403.

## 1. Two seven depths retain a complete ordered-cap remainder

Keep the original old-coordinate head

    B=1+I3+I9+I5+I15+I45,

the selected zero-seven labels(25,27,75,81), and201's four shallow
seven projections. At an old point(c,s), their count is

    m=I_(ROOT(c)=r21)+I_(s=s35)+I_(c=c63)
                      +I_(ROOT(c)=r105,s=s105), 0<=m<=4.

Retain the independent projections of147 and245 and put

    ell=I_(ROOT(c)=r147)+I_(s=s245), 0<=ell<=2.       (SD1)

The retained seven list contains M1=1+m indicators at depth one,
M2=1+ell at depth two, and one unit indicator at every depth e>=3.
The one at each depth includes the original unit7^e label. Every
depth-e indicator has the same complete normalized raw cap

    6/(5*7^e).

List the depth-one indicators first, then depth two, then the
remaining unit powers. For q>=0, the first q indicators contribute
at most q pointwise. Thus the positive part of the full retained
count minus q is bounded by the remaining indicators' sum, for
arbitrary original seven residues. Summing their complete caps gives

    G_(m,ell)(q)
      =(6/35)*(M1-q)_+
        +(6/245)*(M2-(q-M1)_+)_+
        +1/[5*7^(2+(q-M1-M2)_+)].                  (SD2)

The last term is the entire geometric tail starting after whichever
unit powers were removed. In particular, no large-exponent cutoff
appears. Define

    g_(t,m,ell)(v)=G_(m,ell)((t-v)_+).

When ell=0, grouping the single depth-two unit with all higher unit
powers recovers exactly201's function:

    g_(t,m,0)(v)
       =1/[5*7^max((t-v)_+-m,0)]
                        +(6/35)*(m-(t-v)_+)_+.    (SD3)

The new labels have assigned original old caps5/36 and1/10. They
already occur in201's complete omitted cap series, at depth two.
Removing those precise summands gives

    cap147=(6/245)*(5/36)=1/294,
    cap245=(6/245)*(1/10)=3/1225,
    cap147+cap245=43/7350,

    Znew=13/360-43/7350=2669/88200>0.              (SD4)

This subtracts known summands from a proved nonnegative upper-cap
series. It does not subtract an upper bound from an unknown actual
mass. Each original label belongs to one part of the new partition.

## 2. The same selected-cylinder estimates apply to the new bridge

For the same raw old source Lambda and actual survivor mu of201,
let w be the original retained density and define

    f_t(v;c,s)=w(c,s)*(v-t)_++g_(t,m(c,s),ell(c,s))(v). (SD5)

The original surviving hinge uses mu<=w*Lambda; the nonnegative
seven increment uses Lambda. All arbitrary source and seven residues
remain allowed.

The bridge is increasing and integer-convex. Before v reaches t,
its forward increments read the ordered cap list in reverse, so
they are nonnegative and nondecreasing. Beyond t the increment is
exactly w>=2/5, which exceeds the largest seven cap6/35. The checker
verifies every finite transition and the exact affine continuation
for t=1,...,8, every original source weight,0<=m<=4 and0<=ell<=2.

For a nonnegative combination sum_t a_t*(A-t)_+, use k1=0 and
kt=min(t-1,4) for t>=2. For the i-th selected label define

    D_i^k(c,s)=sum_(t:kt>=i)a_t
                    [f_t(B+k+1;c,s)-f_t(B+k;c,s)]. (SD6)

These coefficients are nonnegative and ordered in k. The same
pointwise selected-indicator telescoping as201 applies. In particular,
the actual raw intersections27∩25 and27∩75 have cap1/675;
81∩25 and81∩75 have cap1/2025. The resulting selected bounds are
exactly201's minimum of its independent-cylinder bound and its
intersection bounds, now evaluated with(SD6).

No product factorization of the surviving measure is assumed.
The intersection caps use the original raw source dominated by
the complete3-by5 Haar product, as in201. Each cylinder carries
the combined coefficients of its one original test before taking
the source maximum.

Write P_i for these selected bounds and L for the same25-cell
source capacity LP. The complete six-projection objective is

    V6=sum_t a_t*(R_kt+Znew)
        +L(sum_t a_t*f_t(B))
        -a1*C109(layout)+sum_i P_i.               (SD7)

The old zero-seven remainders R_kt are unchanged complete tails.
The threshold-one correction C109 keeps its original forced
pure-three and deep-five deletions on this same head. Changing
the seven bridge does not change that correction to the surviving
old mean.

For each source configuration the complete two-projection bound V2
and four-projection bound V4 from201 are still valid. Therefore

    integral_mu sum_t a_t*(A-t)_+ <=min(V2,V4,V6).  (SD8)

Each is a whole bound with its own full complementary cap sum.
Taking their minimum does not add gains belonging to different
partitions.

## 3. Exact pruning retains all62,500,000 original choices per cost

There are12500 independent old heads. Each has10 original21/35
projection choices,50 choices for63/105, and10 choices for147/245.
Their product is62,500,000 complete source branches per cost.

Seed evaluations at201's controlling head give a lower bound b
for the maximum of(SD8). For each original21/35 branch, evaluate V2.
If V2<=b, all500 containing choices already satisfy(SD8)<=b.
Otherwise evaluate V4 separately for all50 choices. When
min(V2,V4)<=b, all10 containing second-depth choices satisfy the same
bound. Only the remaining branches require their ten V6 values.

The current b can only increase. Every branch bounded earlier
therefore remains below the final maximum. This is an exhaustive
upper-bound calculation; no original choice or infinite tail is
omitted. Every invoked source LP checks a feasible primal and a
matching feasible dual with exact integer arithmetic. Exact scale
conversion returns rational bounds for the original coefficients.

The checker records both levels of expanded and bounded branches,
their largest discarded upper values, every maximizing witness,
and a digest of all branch decisions. It checks the full identity

    500*(two-projection branches bounded)
       +10*(four-projection branches bounded)
       +(six-projection evaluations excluding seed)=62,500,000.

The exact counts for the two original heavy costs are:

| Cost | Two-projection branches bounded | Two-projection branches expanded | Four-projection branches bounded | Four-projection branches expanded | Six-projection evaluations, including5000 seed choices | Exact LPs |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
|0|116164|8836|441776|24|5240|572550|
|16|116046|8954|447676|24|5240|578450|

Both complete maxima have the witness

    layout=(1,3,2,1,2,3,2),
    (r21,s35,c63,r105,s105,r147,s245)=(1,2,3,1,2,1,2).

These are maximizing choices in the valid upper-bound program;
no actual family attaining all source inequalities is asserted.

## 4. One complete comparison consumes the new heavy bounds

The original heavy functions0 and16 have exact nonnegative hinge
expansions on all positive integer loads. The checker reconstructs
their finite transitions and full affine tails, and applies(SD8)
to each complete combination separately. Their original labels
and maximizing source configurations remain independent.

The complete original cost bounds are

    Cost0<=1728345508164669466610462689
              /299640136547155230246420000
          =5.768070753407478...,

    Cost16<=1196500222137264428493588992761
               /259563268283973218200961325000
           =4.609666961152001... .                 (SD9)

Replace their203 bounds by the new complete maxima, then apply
the existing whole-integer majorant propagation to the original
52-function inventory. All previous cost bounds remain available.
The signed mass term uses exact D, and the complete square stays
Q=8201/1800 with its original positive coefficient.

Only costs0 and16 improve in this full propagation. The resulting
numerator and its exact decrease are

    N<=7692346668557100176741694846143297889317
         /224864850579771678391856815074000000000
      =34.20875538673044...,

    N203-N=2104563704921/9465121886220
          =0.2223493506179750... .                 (SD10)

The denominator is exactly203's complete positive lower bound

    d>=1420639249067/17084377926000.

It retains the four independent AP11 blocks, the separate AP13
loss, and the full count tail3337/52707600. No gain from a new AP
application of(SD8) is included here. The original offset remains
185694867601/8599322160. Thus one complete new numerator N gives
the comparison C0+N/d.

The [helper](../../frontier/comparison-bounds/second_depth_seven_comparison.py) and
[certificate](../../certificates/source_norms/comparison-bounds/second_depth_seven_comparison.json)
contain the exact full maxima, complete cost vector, denominator,
source pins and branch accounting.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/second_depth_seven_comparison.py --check
```

These are ordinary source inequalities and rational certificates.
They do not assert simultaneous attainment, an off-face neighborhood,
a new global K bound, Lean verification or unrestricted Erdos7 resolution.
