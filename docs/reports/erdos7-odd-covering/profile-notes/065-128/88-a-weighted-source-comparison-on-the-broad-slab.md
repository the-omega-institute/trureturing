[Index](../../marked_head_profile.md) · [Broad source geometry](85-a-broad-five-slot-source-deletion-tradeoff.md) · [Clipped identity interface](87-a-clipped-full-load-interface-on-the-broad-slab.md) · [Old identity formula](66-explicit-linear-endpoint-neighborhood.md)

# A weighted source comparison on the broad slab

There is an explicit pointwise source upper for the whole actual slab

    Delta=(z-3/4)+(1/4-alpha1)+(1/4-beta2-beta3-beta4)<=1/18,
    0<=r<1/12000.

It retains the actual source parameters, the actual common carrier mixture,
the best five slot and all original test residues. It uses finite capacity
duals at the actual parameter point, not interpolation of optimized vertex
values. Every exponent tail remains complete.

On both entire K beta faces with r=0 and their controlling carrier, its
source upper is154/225. The old fixed-layout comparison is33673/48600,
so the source gain is at least409/48600 before the complete clipped tail
T40 of87 is deducted. The fixed three-group argument below proves this
uniformity across each beta simplex.

Profile72's dedicated face estimate133/200 is sharper at that endpoint.
The present formula retains every actual parameter throughout the broad
small-r slab, providing an explicit source comparison away from the faces.

The same pointwise bound is not everywhere smaller than the old source
comparison. Exact parameter probes give negative differences in some
deficit and carrier directions. These are retained below. The theorem
supplies a source interface for a joint mass/escape comparison; this note
does not establish a global K improvement or Lean verification.

## 1. Actual weighted source and the missing fifth-slot observation

Use85's measures Lambda,mu, the five ternary cells and ROOT=(0,0,1,1,1).
Write the actual common carrier mixture as pi_(u,v), with

    u in{-1,0,1}, v in{-1,0,1,2,3,4}, sum pi=1.

The value -1 denotes a missing shallow carrier. Put

    t_l=sum_(u,v)pi_(u,v)*(1_(ROOT(l)=u)+1_(l=v)),
    a_l=1-t_l/5, b_l=1+1_(l>=2).

Thus t_l/5 is the sum of the two actual virtual shallow densities v3,v9
of87. The weight there is

    w_(l,j)=a_l-(b_l/5)*1_(j=H), 1/5<=w_(l,j)<=1.    (W1)

Relabel the distinct first source slots as P=0,A=1,B=2, and the remaining
slots as Q=3,H=4. Let L in{2,3,4} be the actual first-beta source cell.
For the raw source matrix

    X_(l,j)=Lambda(cell_l intersect F_j),

the row sum is n_l, and all entries are nonnegative. The source exclusions
force X_(l,0)=0, X_(l,1)=0 for l>=2, and X_(L,2)=0. Elsewhere the first
cap is eta_l/5.

Profile85's root-wide packing already gives the stronger Q cap in root1:

    X_(l,3)<=eta_l*(1/10+Delta+r/h1), l>=2.           (W2)

There is also a root0 cap. Let R5 be the complete pure5 deletion outside
P. Its five-coordinate measure is1/20-p. Its intersection with A is at
most a=1/4-alpha1: otherwise the first alpha label plus the complete
remaining alpha tail1/20 could not attain alpha1. Its intersection with
B is at most b=1/4-sum_(l>=2)beta_l, by the first-beta argument of85.
Since pure5 removes all ternary mass above its five-coordinate support,
its intersection with H has measure at most r/h. Therefore

    |R5 intersect Q|>=1/20-Delta-r/h,
    X_(l,3)<=eta_l*(3/20+Delta+r/h), l<2.             (W3)

Let U_(l,j) be the minimum of the relevant bound(W2) or(W3) and eta_l/5,
with the three sets of exact zero entries imposed. These are caps on the
same actual matrix X; they are not independently chosen source measures.

One more observation is needed. The actual best-slot deficit is

    sum_l(eta_l/5-X_(l,4))=r.                        (W4)

Consequently any cell group G has non-H source mass at most

    sum_(l in G)n_l-sum_(l in G)eta_l/5+r.           (W5)

Giving r to each disjoint group weakens this bound but does not reverse
it. In particular actual inputs obey

    eta_l/5-r<=n_l<=sum_j U_(l,j),
    s>=h/5-r.                                      (W6)

A relaxed parameter point that violates(W6), for the stipulated first-beta
cell and r, cannot represent this actual branch.

## 2. A finite capacity dual for every original head

Let B be the load of the six original test labels{1,3,9,5,15,45}.
Its12500 possible surviving shallow layouts are indexed by

    (u3,v9,j5,u15,j15,v45,j45)
        in{0,1}x{0,...,4}x{0,...,4}x{0,1}x{0,...,4}^3.

The first entry of the load is the unit. Missing or source-disjoint test
labels can be replaced by a surviving choice to obtain an upper bound;
all coefficients below are nonnegative. Different test labels remain
independently chosen.

For a fixed head layout let c_(l,j)=w_(l,j)*B_(l,j). For a finite index
set I with capacities U_i and mass budget N>=0 define

    D(c,U,N,I)=min_(gamma in{0} union{c_i:i in I})
             [gamma*N+sum_(i in I)U_i*(c_i-gamma)_+]. (D1)

Every gamma>=0 in(D1) gives an upper bound on sum_i c_i X_i when
0<=X_i<=U_i and sum_i X_i<=N. Filling capacities in decreasing order
of c_i attains a dual breakpoint and proves(D1) is the exact capacity
optimum. The checker independently verifies the primal allocation and
its dual value; the ordinary inequality does not rely on sampled optima.

For each of the partitions

    {{0},{1},{2,3,4}} or {{0},{1},{2},{3},{4}},

write N_G=sum_(l in G)n_l. There are two valid head bounds per group:

    Plain_G=D(c,U,N_G,G times{0,...,4}),

    KeptH_G=sum_(l in G)c_(l,4)*eta_l/5
       +D(c,U,N_G-sum_(l in G)eta_l/5+r,
                                  G times{0,1,2,3}). (D2)

The second uses(W5) and replaces the H contribution by its raw cap.
Its residual budget is nonnegative for every actual input. Sum each
method over its groups, take the minimum of the four bounds, and finally
maximize over the12500 original layouts. Call the result H(theta,pi,r,L).
Then

    integral w_H*B dLambda<=H(theta,pi,r,L).          (D3)

This is a finite maximum of explicit finite-dual formulas at the actual
parameters. No regularity or convexity of optimized values is assumed.

## 3. Complete tails use the same weight and first source exclusions

For deep pure3 tests, first remove the late mixed35 source restrictions.
The retained weight is nonnegative, so this increases the integral. The
remaining shallow35 source has, within each ternary cell, one common
five-coordinate survivor set of measure d_l. Let its loss on H relative
to1/5 be epsilon_l. The actual raw source only removes additional points,
so

    eta_l*epsilon_l<=r, eta_l>=1/18.                 (T1)

Every deep3 test cylinder in this cell has weighted shallow-source
coefficient at most

    a_l*d_l-b_l/25+(b_l/5)*epsilon_l.

Its ternary measure is at most3^-a. Sum all a>=3, using1/18 and b_l<=2:

    Tail3<=max_l(a_l*d_l-b_l/25)/18+(2/5)*r.         (T2)

The base coefficient is nonnegative throughout the domain. This proof
uses shallow-source homogeneity before summing. It does not charge an
independent r at each of infinitely many deep cylinders.

For descendant-five tests set

    Z_(l,j)=eta_l*w_(l,j)

except Z is zero in P, root1 times A and cell L times B. A depth-b test
five cylinder has weighted cap Z times5^-b. Since sum_(b>=2)5^-b=1/20,
the complete tails at ternary depths0,1,2 satisfy

    Tail5<=[max_j sum_l Z_(l,j)
       +max_(u,j)sum_(ROOT(l)=u)Z_(l,j)
       +max_(l,j)Z_(l,j)]/20.                       (T3)

The remaining tests have both ternary depth>=3 and five depth>=1;
their complete weighted cap is at most1/72 because w<=1. Finally the
positive-seven tests contribute at most(s+C)/5 as in87, where C is the
complete old raw35 cap sum.

Thus the explicit source upper is

    Q(theta,pi,r,L)=H+Tail3+Tail5+1/72+(s+C)/5.       (T4)

Combining with87 gives, for the complete original357 identity test A,

    integral A dmu357
       <=Q+c*[rho-(r+r1)/5]+T40,
    c=17100/397, rho=S-S0.                          (T5)

All terms come from the same source, carrier mixture and original test.

## 4. Compare with the old margin using the same carrier mixture

For any fixed old pair of ternary layouts beta,gamma in BASES, define

    k_l=6-beta_l, A_l=k_l*n_l-gamma_l*eta_l/5,
    z_l=k_l*d_l-gamma_l/5, v_l=9*eta_l*k_l,

    T=(13/243)*max z+(1/486)*max(k_l*d_l)
       +[sum v+max_root sum_root v+max v]/36+max k/72.

Let U_old be the existing exact_old_U for this pair and source. The old
conditional margin is a minimum over old layout pairs. Consequently its
actual pi average satisfies

    m40<=6*s-U_old-[sum_l t_l*A_l+T]/5.             (M1)

Every pair separately gives a valid bound; using the same pair across
the pi average is a relaxation in the required direction. Define

    O=max_(beta,gamma)[6*S0-6*s+U_old
                                  +(sum_l t_l*A_l+T)/5],
    g=O-Q.                                         (M2)

There are100 fixed old pairs. Hence6*S0-m40>=O, and(T5) gives an
available margin satisfying

    new_margin-m40
       >=g-T40+(6-c)*rho+c*(r+r1)/5.                (M3)

Combining with the still-valid old bound permits taking the positive
part of the right-hand side. Neither g nor the whole right-hand side
is asserted positive throughout the slab. The residual coefficient is
linear and shared once; any global absorption must separately retain
the existing actual-mass and escape terms.

## 5. A uniform anchor on both complete K beta faces

On the canonical face the deficit is in cell0, the late mass is1/72
in cell0, alpha1=1/4, z=3/4, sum_(l>=2)beta_l=1/4, and pi is concentrated
on carrier(1,1). At r=0, the weighted table depends on the first-beta
cell L but not on the distribution of the remaining beta budget.
The three group source masses are exactly

    1/36,1/12,5/36.

After(W5), their non-H mass budgets are1/60,11/180,13/180. Thus the
three-group KeptH method in(D2) is constant across the entire face.
Every L in{2,3,4} gives the same maximum by a permutation of the root1
cells, which preserves the layout set and the three source groups.
Exact enumeration with rational duals gives

    H<=11/25.

The original plain three-group method instead gives67/150. The complete
tails and positive-seven complement are

    Tail3=71/1800, Tail5=23/600,
    Tail3+Tail5+1/72=11/120, (s+C)/5=11/72.

All these max branches remain fixed across the beta simplex. Therefore

    Q<=154/225.

The old fixed pair beta=(2,3,1,1,1), gamma=(1,2,2,2,2) supplies
O>=33673/48600 throughout the same face, so

    g>=409/48600.                                   (F1)

For completeness the required fixed branches can be checked directly.
The face densities are d0=d1=3/4 and d_l=1/2-beta_l for l>=2, so

    1/4<=d_l<=1/2, sum_(l>=2)d_l=5/4,
    max d=3/4, max n=n1=1/12,
    sum_root0 n=1/9<sum_root1 n=5/36.

These give C=37/72 and U_old=8/9. In the displayed old pair,
k=(4,3,5,5,5); hence z0=14/5, z1=37/20 and z_l<=21/10 in
root1, while(k*d)0=3,(k*d)1=9/4 and(k*d)_l<=5/2. Thus cell0
controls both old deep maxima. Also9*eta*k=(2,3,5,5,5),
sum_l t_l*A_l=23/30, and T=12991/9720, proving the stated O.
For the new pure3 tail the cell0 coefficient is71/100, the cell1
coefficient is14/25, and every root1 coefficient is at most8/25.
The three descendant-five maxima are37/90,4/15,4/45. They depend
only on eta, the carrier and source exclusions, which are fixed here.
These inequalities prove the whole-face branches used above.

Exchanging the two root0 cells proves the same result on the other
control face, with carrier(1,0). At saturated actual mass rho=0,
profile85 forces r=r1=0, and(M3) gives the strictly positive gain
409/48600-T40. The continuation uses fixed group masses and fixed old
branches; it does not interpolate newly optimized vertex numbers.

## 6. Direction probes preserve both improvements and failures

The checker evaluates41 exact parameter/carrier cases. Each admissible
record enumerates12500 heads with checked capacity duals and100 old
layout pairs. The baseline is canonical source vertex398, first-beta
cell2, carrier(1,1), r=0. These are pointwise comparisons of the proven
upper-bound formulas, not assertions that every parameter is realized
by an original covering family.

| Change from that baseline | Exact g before T40 |
| --- | --- |
| Baseline | 409/48600 |
| p=1/20 | 137/24300 |
| a=1/18 | 157/48600 |
| b=1/18 | 187/48600 |
| Deficit moved to cell2 | -779/48600 |
| Deficit moved to cell3 or4 | -347/48600 |
| Carrier changed to(-1,2) or(1,2) | -23/48600 |

The certificate also retains intermediate p,a,b values, all deficit
and late coordinates, all18 single carriers, a mixed carrier and a
positive-r input. Moving the full late budget to cell2 fails(W6): its
row mass is below eta2/5 while r=0. That record is explicitly excluded
from this actual branch; it is not silently dropped or called a
counterexample. The relaxed p=1/18 input also fails the row-cap bound:
the forced original source label5 implies z<=4/5, equivalently p<=1/20.
Thus that relaxed point is retained as excluded, and p=1/20 supplies
the actual necessary boundary used in the table.

The negative differences mean this particular source upper and old
lower comparison do not give an everywhere-positive improvement.
They do not refute an actual-source improvement, and do not settle
whether the old global escape surplus absorbs the deficits.

The [checker](../../frontier/endpoint-bounds/broad_weighted_identity_source.py) and its
[certificate](../../certificates/source_norms/endpoint-bounds/broad_weighted_identity_source.json)
retain the pointwise formula, caps, witnesses, exact dual digests, complete
tail values and remaining comparison obligation.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/broad_weighted_identity_source.py --check
```
