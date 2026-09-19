[Index](../../marked_head_profile.md) · [Previous complete comparison](199-one-six-label-head-controls-the-square-and-both-complete-crosses.md) · [Original complete hinge bridge](../98-a-complete-stop-loss-profile-strengthens-the-whole-face-comparison.md) · [Same mean and hinges](../109-the-mean-and-all-hinges-share-one-original-test.md)

# Two more seven labels and selected intersections control both heavy costs

On both complete saturated actual K faces, the original heavy costs
of indices0 and16 have the uniform upper bounds

    Cost0 <=1767382419284066416882094809
              /299640136547155230246420000
           =5.898350066350101...,
    Cost16<=1223584622012646577327283593201
              /259563268283973218200961325000
           =4.714013003850734... .                     (EP1)

The preceding bounds were5.928953257640718... and4.736106750810962....
Keeping199's full square, all52 costs and complete denominator gives

    K<=300262746236495996567844728508827341127777603196305477
        /661429767923471771517732963287361097500000000000000
      =453.9601342394326... .                         (EP2)

This improves199 by0.6275718097557763.... The new structure has two
parts: original63 and105 stay inside the same positive-seven bridge,
and the four selected old-label increments retain intersections between
the ternary and five coordinates. The bounds use the actual common
source and all original independent residues and exponent tails.

The domain is r=rho=0 and mass53/360 on the two complete actual K
faces. This is an ordinary source theorem with exact rational LP
checks, without an actual-attainment claim, Lean verification,
off-face or global extension, or unrestricted Erdos7 resolution.

## 1. The complete positive-seven partition has four shallow projections

Retain109's original six-label head

    B=1+I3+I9+I5+I15+I45,

and the ordered selected zero-seven labels

    (M1,M2,M3,M4)=(25,27,75,81).

For threshold t the selected prefix still has length k1=0 and
kt=min(t-1,4) for t>=2. Every unselected zero-seven label retains98's
complete survivor-cap remainder R_kt. The same original test is used
for all thresholds of a cost.

For the enlarged bridge retain every unit7^e and the original
positive-seven labels21,35,63,105. Their independent old projections
are a root r21, a slot s35, a cell c63, and a root/slot pair(r105,s105).
At an old point(c,s), let

    m=I_(ROOT(c)=r21)+I_(s=s35)+I_(c=c63)
                         +I_(ROOT(c)=r105,s=s105), 0<=m<=4. (EP3)

The original complete omitted positive-seven cap was779/12600.
Its assigned63 and105 terms are exactly

    (6/35)*(1/12)=1/70,
    (6/35)*(1/15)=2/175.

Remove these two terms from that known complete cap sum. The remaining
positive-seven labels have total upper

    Znew=779/12600-1/70-2/175=13/360.               (EP4)

This removes terms from a proved nonnegative cap series, not an upper
bound from an unknown actual mass. The labels occur in exactly one
part of the enlarged test partition.

At a fixed old point, the retained seven list has m+1 depth-one
indicators and one unit indicator at every depth e>=2. Each has its
original normalized raw cap6/(5*7^e). The pointwise deletion-of-the-
first-q-indicators argument of98 therefore gives, for every integer
t>=1 and v>=1,

    g_(t,m)(v)=1/[5*7^max((t-v)_+-m,0)]
                        +(6/35)*max(m-(t-v)_+,0).   (EP5)

The proof uses the count m, not the former restriction m<=2; it applies
unchanged through m=4. Arbitrary seven residues are allowed. The old
survivor hinge is bounded using mu<=w*Lambda, whereas g is integrated
against the raw source. Thus the source bridge is

    f_t(v;c,s)=w(c,s)*(v-t)_++g_(t,m(c,s))(v).        (EP6)

It is increasing and integer-convex. Before its affine continuation,
the forward increments grow geometrically to6/35; thereafter they
equal w>=2/5. The checker reconstructs the entire finite transition
and the exact affine continuation for every used t,w,m.

## 2. A selected increment asks whether an earlier label is present

Take any finite nonnegative combination sum_t a_t*(A-t)_+ with
1<=t<=8. Keep the same B and all four seven projections fixed. Define

    D_i^k(c,s)=sum_(t:kt>=i) a_t
                       [f_t(B+k+1;c,s)-f_t(B+k;c,s)],
    0<=k<=i-1.                                    (EP7)

These arrays are nonnegative and increasing in k. Every active
threshold containing Mi contains all earlier Mj as well. Telescoping
the selected indicators gives an exact contribution at step i of

    I_Mi * D_i^(I_M1+...+I_M(i-1)).                (EP8)

The old bound replaced the superscript by i-1 everywhere. The new
bound keeps one or two of those actual binary observations.

For i=2,3, respectively, pointwise monotonicity gives

    I27*D_2^I25
      <=I27*D_2^0+I27*I25*(D_2^1-D_2^0),
    I75*D_3^(I25+I27)
      <=I75*D_3^1+I75*I27*(D_3^2-D_3^1).          (EP9)

The second inequality uses I25<=1. It does not assert that25 and75
are independent or nested. Each displayed product is an actual
intersection of two test events from the original test.

For i=4 put l=D_4^1, u=D_4^2, h=D_4^3, and

    kappa=max(u-l,(h-l)/2)>=0

pointwise on the25 rectangles. For q=0,1,2, the affine function
l+kappa*q majorizes the three values l,u,h. Since I27<=1,

    I81*D_4^(I25+I27+I75)
      <=I81*l+I81*(I25+I75)*kappa.                (EP10)

There is also the valid one-observation bound

    I81*D_4^(I25+I27+I75)
      <=I81*D_4^2+I81*I25*(D_4^3-D_4^2).        (EP11)

Both bounds will be available; their upper values may be minimized
after integration. No subtraction of an unknown marginal is involved.

## 3. Original mixed intersections give the smaller capacities

Let P_M(z) be the existing raw source-cylinder operator of98/109,
applied to the nonnegative rectangle array z. It upper-bounds
integral I_M*z dLambda for every independently chosen original residue.
For the added intersections the common raw source satisfies
Lambda<=Haar3 times Haar5. The generalized CRT intersection therefore
has cap

    Lambda(test27 intersect test25)<=1/675,
    Lambda(test27 intersect test75)<=1/675,
    Lambda(test81 intersect test25)<=1/2025,
    Lambda(test81 intersect test75)<=1/2025.       (EP12)

For75 its root must also be compatible; an incompatible intersection
is empty and still satisfies the same cap. For a nonnegative rectangle
array z, multiply these caps by max z. These are bounds on the same
actual Lambda, without a product assumption about the survivor mu.

Equations(EP9)--(EP12) give the step upper bounds

    V2<=P27(D_2^0)+max(D_2^1-D_2^0)/675,
    V3<=P75(D_3^1)+max(D_3^2-D_3^1)/675,
    V4<=P81(l)+2*max(kappa)/2025,
    V4<=P81(D_4^2)+max(D_4^3-D_4^2)/2025.        (EP13)

For each i retain its original upper P_Mi(D_i^(i-1)) as another
option and take the minimum of the valid upper values. V1 is unchanged.
Different step inequalities may use the same original source facts,
since they bound different summands of the exact telescoping identity.
Every selected summand is added exactly once.

The complete bound for this fixed head and projections is

    sum_t a_t*(R_kt+Znew)
       +L(sum_t a_t*f_t(B))
       -a1*C(ell)+sum_i Vi.                       (EP14)

L is the original three-group raw-source capacity LP. The complete
mean-head deletion C(ell) is precisely109's correction, with its
pure3 and deep-five families and the same layout ell. It is applied
only to the threshold-one old-head contribution. Adding63/105 to the
seven bridge changes none of those forbidden-family identities.

The two-projection version, retaining only21/35 and the old omitted
tail779/12600, admits the same selected-intersection improvements.
It supplies another valid upper for the same original test. The
minimum of the two complete fixed-head upper values is used below.

## 4. Finite evaluation covers every projection and every infinite tail

The head has12500 original choices. Together with the independent
21/35 projections this gives125000 branches; every branch has50
additional independent63/105 projections. Thus the enlarged containing
inventory has6,250,000 choices per cost.

The exact scan first computes a valid two-projection upper at each
of the125000 branches. If it is no larger than the maximum candidate
already found, all50 additional projections are bounded by that same
upper and require no evaluation. Otherwise all50 are evaluated and
the two complete upper values are minimized. The maximum can only
increase during the scan, so every skipped value remains below the
final maximum. No actual source branch or original label is removed.
The certificate records the branch-decision digest and verifies the
largest unexpanded upper is below the final result.

For cost0 the scan expands3187 branches, and for cost16 it expands3270.
Including the initial complete500-projection head evaluation, the
new projection counts are159850 and164000. The respective total
numbers of independently checked rational LPs are284860 and289010.
A maximizing head/projection tuple is

    ell=(1,3,2,1,2,3,2),
    (r21,s35,c63,r105,s105)=(1,2,3,1,2).          (EP15)

Cell4 supplies its source symmetry image. No assertion that an actual
family simultaneously attains these upper operators is made.

Every old omitted label still appears in its original complete R_kt
series. Every positive-seven label appears either in(EP4) or in the
complete geometric bridge(EP5). The four selected labels keep their
independent residues, and(EP12) holds at their actual intersections.
All inequalities hold for finite original prefixes with nonnegative
complete cap remainders. Monotone convergence handles a fixed source;
the original uniform geometric first-moment tails justify the
labelwise diagonal limit of varying finite source families. The
finite head scan therefore evaluates a complete infinite-label theorem,
not a bounded-height surrogate.

Both source orientations and every actual first-beta choice use the
same permutations of the source tables, forbidden-family correction
and original test projections as109. The full containing inventory is
preserved, giving the stated uniform bound on both whole K faces.

## 5. The original costs and full comparison remain intact

The original cost functions are read from the pinned inventory.
For each heavy function f the checker reconstructs

    f(v)=f(1)+sum_(t=1..8)a_t*(v-t)_+, v>=1,

including every finite transition, its eventual slope and its constant
term. Here f(1)=0 and all a_t>=0. Thus(EP14), maximized as above,
proves(EP1) for the complete original functions.

The consumer starts from199's full52 vector and keeps Q=8201/1800.
Only indices0 and16 improve; the existing majorant propagation adds
no further change in this substitution. The exact numerator decrease is

    24371839809732202720609289602472299
      /486486455581236804213151763381250000
      =0.05009767390258294... .

The resulting numerator is34.514824958934746.... The complete denominator
remains50511415637/632754738000>0, with all AP11 blocks, the independent
AP13 loss and the infinite count tail. Together they give(EP2).

The [helper](../../frontier/transport/expanded_seven_pair_comparison.py) exposes
CoupledSevenHead.prepare and CoupledSevenHead.scan for arbitrary
nonzero nonnegative rational coefficients at thresholds1 through8.
Its scan output bounds the hinge combination; a separate constant
f(1)*53/360 is added by a consumer when needed. The same-layout
mean deletion is retained whenever a1 is positive.

The [certificate](../../certificates/source_norms/expanded_seven_pair_comparison.json)
stores both complete scans, the exact source pins and the full consumer.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/expanded_seven_pair_comparison.py --check
```
