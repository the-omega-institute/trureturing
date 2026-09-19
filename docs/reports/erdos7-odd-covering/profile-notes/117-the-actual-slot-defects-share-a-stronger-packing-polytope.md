[Index](../marked_head_profile.md) · [Actual slot and deletion budgets](85-a-broad-five-slot-source-deletion-tradeoff.md) · [Actual source matrix](88-a-weighted-source-comparison-on-the-broad-slab.md) · [Concentrated mass geometry](106-the-actual-denominator-shares-the-carrier-mass-residual.md)

# The actual slot defects share a stronger packing polytope

The actual cofactor5 and15 defects admit the shared necessary constraint

    G5*q5+G15*q15+omega<=rho-(r+r1)/5,
    0<=q5,q15<=1/5, omega>=0.                       (DP1)

The quantities are from one source, one family and one projected
deletion measure. They are not independently chosen probabilities.
For a concentrated K-face orientation the certified gaps can be taken as

    Gbar=min(eta_L/5-r,h1*(1/10-Delta)-r-r1)>0,
    G5=Gbar, G15=Gbar+r-r1.                        (DP2)

Thus the extra nonnegative term(r-r1)*q15 is retained in(DP1).
The bound uses the actual first-beta cell L, rather than replacing
its mass by a minimum over all root1 cells.

The same shared-deficit argument gives a stronger uniform gap on the
entire rectangle used in103 and107:

    qK>=1-1/27, 0<=r<=1/520
        =>G5,G15>=2513/126360
                  =7499/379080+1/9477.             (DP3)

The proof of(DP3) uses general packing guards. It does not apply85's
smaller cutoff r<1/12000 outside that cutoff. A complete global consumer
must separately substitute this gap into all costs and branches.

These are ordinary source and measure inequalities. The polytope is an
outer constraint on actual data, with no assertion that every feasible
point is realized by a congruence family. This interface alone does not
claim a new global K, Lean verification or unrestricted Erdos #7 result.

## 1. Exact actual quantities and one budget

Use85's effective9 raw source Lambda, survivor mu, virtual mixed-seven
deletion V and actual projected deletion delta. Let

    eta_c=(1-deficit_c)/9,
    h0=eta0+eta1, h1=eta2+eta3+eta4, h=h0+h1,
    x_j=h/5-Lambda(F_j), r=min_j x_j,
    H in argmin_j x_j,
    r1=h1/5-Lambda(root1 times F_H).

Then0<=r1<=r. The root0 loss on the same best slot is r-r1. Also

    r<=h/5, r1<=h1/5, r-r1<=h0/5.                 (DP4)

With the actual normalized shallow carrier mixture pi, put

    S0=sum_c pi_c*D_c(theta), T=Lambda(1)-S0,
    rho=mu(1)-S0, omega=(V-delta)(1).

The exact identity is

    rho=(T-V(1))+omega.                            (DP5)

Both terms are nonnegative. In particular0<=rho<=T because
mu(1)<=Lambda(1). The complete cap formula106(M4) also gives
R<=23/72. Since n_c<=1/9, every shallow carrier has c.n<=4/9.
Consequently T=(c_bar.n+R)/5<=11/72, so

    0<=omega<=rho<=T<=11/72.

In particular the actual omega lies in115's required unit mass domain.
Let V5 and V15 be the two distinct original
cofactor families5*7^e and15*7^e, with complete weights
u_e=6/(5*7^e), sum_(e>=1)u_e=1/5. Their unused capacities are

    E5=h/25-V5(1), E15=h1/25-V15(1).

As shown in85, these are separate nonnegative summands of T-V(1).
If additional distinct complete cofactor defects are retained as Erest,
then

    E5+E15+Erest+omega<=rho.                       (DP6)

In particular a deep-family defect from102 can coexist with these
terms when its original cofactors are distinct; it is not a second
copy of rho.

Define q5 as the sum of u_e over wrong5 slots and absent labels,
and q15 similarly for carriers other than root1 times H and absent
labels. These quantities lie in[0,1/5]. If every wrong5 slot has
Lambda mass at most Lambda(F_H)-G5, and every wrong15 carrier has
mass at most Lambda(root1 times F_H)-G15, then, label by label,

    E5>=r/5+G5*q5,
    E15>=r1/5+G15*q15.                             (DP7)

Absent labels also satisfy these bounds since their entire capacity
is missing and G5<=h/5-r, G15<=h1/5-r1. Summing every original seven
depth proves(DP7). Combining with(DP6) gives(DP1), or the stronger
version with Erest on its left side. In particular
rho-(r+r1)/5>=0 in this separated-carrier domain.

## 2. The root1 loss sharpens the packing guard

Assume Delta=p+a+b<=1/18, with p,a,b as in85. Its complete tail
budget forces the first source labels5,15,45, with15 on root1 and45
in root1 cell L, and their first-five slots P,A,B are distinct.
The complete root-wide pure5/alpha packing set U satisfies

    |U minus(P union A)|_5=1/10-p-a,
    |U intersect B|_5<=b.

Let R=U minus(P union A). It is deleted throughout root1. Therefore
its intersection with the best slot obeys the stronger bound

    h1*|R intersect H|_5<=r1.                      (DP8)

Using r1 here preserves information that85 discarded by replacing
it with r. Since R is confined to B,H,Q, it follows that

    h1*|R intersect Q|_5>=h1*(1/10-Delta)-r1.       (DP9)

For each non-H modulus5 slot, compare its loss with r. The four
valid gap guards are

    h/5-r, h1/5-r, eta_L/5-r,
                            h1*(1/10-Delta)-r-r1. (DP10)

For modulus15, compare wrong carriers with root1 times H. Root0
carriers have mass at most h0/5. Root1 P,A are empty; root1 B loses
at least eta_L/5; root1 Q obeys(DP9). Thus its four guards are

    h1/5-r1, (h1-h0)/5-r1, eta_L/5-r1,
                              h1*(1/10-Delta)-2*r1. (DP11)

Cylinders in removed ternary roots have zero mass and satisfy the
first guard. If all displayed guards are positive, the minima in
(DP10),(DP11) are valid G5,G15. Positivity also ensures H differs
from P,A,B, so the packing argument is consistent.

If h1-h0>=eta_L, the first two guards of each list are redundant.
Their minima reduce exactly to(DP2). This proves the strengthened
shared budget on its full stated domain.

## 3. One concentrated deficit budget controls the whole root

Suppose qK>=1-sigma with0<=sigma<1/2. By106's product-concentration
argument, one K orientation has its selected root0 deficit coordinate
at least(1-sigma)/2. The total deficit over all five cells is at
most1/2. Consequently the entire remaining deficit, including the
whole root1, is at most sigma/2. Hence

    h1>=1/3-sigma/18,
    eta_L>=1/9-sigma/18,
    h0<=1/6+sigma/18,
    h1-h0>=1/6-sigma/9>1/9>=eta_L.                (DP12)

The first bound retains the total deficit budget. Bounding each of
three root1 cells independently would only give1/3-sigma/6, the
weaker bound used in103. Both K orientations satisfy(DP12).

Concentration also gives Delta<=3*sigma/4. For a fixed rectangle
0<=sigma<=delta<=2/27 and0<=r<=r_star, use r1<=r and define

    h_star=1/3-delta/18,
    eta_star=1/9-delta/18,
    G_star=min(1/10-r_star,h_star/5-r_star,
               eta_star/5-r_star,
               h_star*(1/10-3*delta/4)-2*r_star). (DP13)

When G_star>0 all general first-slot and division guards hold.
The source budgets are at least1/4-3*delta/4, exceeding the
post-first-depth capacity1/20, so the forcing argument for the
three distinct first labels also remains valid. Thus(DP13) is a
uniform gap for the whole rectangle, including its r endpoint.
It is not confined to85's original numerical small-r branch.

For delta=1/27, r_star=1/520,

    h_star=161/486, eta_star=53/486,
    eta_star/5-r_star=2513/126360,
    h_star*(1/10-1/36)-2*r_star=4567/227448.

The beta guard is smaller. This proves(DP3), with every other
guard positive. The original lower best-slot credit1/50-r_star/5
remains51/2600. The original source-carrier and root-imbalance
bounds of102 remain unchanged.

## 4. Actual source caps can retain the same split loss

For the raw source matrix X_(c,j)=Lambda(cell_c intersect F_j),
88's row sums, exact zero entries and cell caps remain. In addition
retain both actual equalities

    sum_c X_(c,H)=h/5-r,
    sum_(c>=2)X_(c,H)=h1/5-r1.                    (DP14)

By(DP9), the root1 Q cap improves to

    X_(c,Q)<=eta_c*min(1/5,1/10+Delta+r1/h1), c>=2. (DP15)

For the root0 Q cap, let R5 be the complete pure5 deletion outside P.
It is deleted over both ternary roots. Therefore

    |R5 intersect H|_5
       <=min(r/h,r1/h1,(r-r1)/h0)=u.              (DP16)

The original source budgets give|R5|=1/20-p, with its intersections
with A and B at most a and b. Hence

    X_(c,Q)<=eta_c*min(1/5,3/20+Delta+u), c<2.      (DP17)

Every denominator is positive in the effective source domain.
These caps apply to the same actual X; they do not license separate
source allocations for the two observed losses.

## 5. What the finite defect polygon does and does not assert

For fixed actual source parameters,r,r1,rho and positive certified
gaps, put e=rho-(r+r1)/5. The necessary defect polygon is

    P_e={(q5,q15) in[0,1/5]^2:
                              G5*q5+G15*q15<=e}.  (DP18)

For each point,0<=omega<=e-G5*q5-G15*q15. A nonnegative charge
M*omega may therefore be bounded by its upper endpoint. If the
remaining objective is convex in q5,q15, its maximum after this
substitution occurs at a vertex of P_e. For source LPs with a fixed
feasible source set and an affine q-dependent objective, convexity
follows by taking a supremum of affine functions. Finite maxima
and positive sums preserve it; merely writing an arbitrary minimum
of dual bounds does not establish it.

The vertices of(DP18) are intersections of its four rectangle
boundaries and its budget line. The helper exports their exact
rational enumeration. These are outer relaxation vertices, not
asserted actual congruence-family realizations. If a consumer makes
source capacities, gaps or feasible sets depend on q, it must
re-establish the required convexity. When r,r1 also vary, products
such as(r-r1)*q15 are not a jointly affine polytope constraint;
(DP18) is explicitly conditional on those parameters.

The complete dominated-error tails of115 are concave functions of omega.
Adding those tails does not preserve the convexity just used;115 gives
an exact interior-maximum counterexample. A consumer must first use a
uniform tail bound, or fix omega and separately optimize its remaining
one-dimensional dependence.

The original g0=397/36000 remains valid on Delta<=1/18 and
r<1/12000. Its least broad guard is

    1/90-1/12000=397/36000,

while the Q guard is1973/162000, greater by373/324000. It must
not be used unconditionally. For example, take the actual raw source
with eta_c=1/9 and no5/15/45 source restrictions. All five columns
are equal, so r=0 and an arbitrary H is a best slot. Put the two
present forbidden cofactor5 labels at seven depths1,2 in a different
slot; all other such labels are absent. Then

    Delta=3/4, q5=1/5,
    E5=h/25-(6/35+6/245)*(h/5)=1/2205
                                     <g0*q5.     (DP19)

Thus even the individual g0 defect inequality fails outside its
packing branch. This is a source/cofactor counterexample to an
unguarded inference, not a covering of the integers.

Finally106's denominator bound remains

    E<=53/360+5*sigma/9+rho, 0<=sigma<1/2.

The same rho must pay both the defect losses and any target decrement
in the denominator, as107 explicitly does. Neither(DP1) nor the
stronger gap removes that residual term.

`frontier/shared_slot_defect_polytope.py` checks the exact guards,
shared-deficit constants, stronger rectangle, polygon vertices and
counterexample. Its certificate records the interface and source
bindings. The ordinary proofs above carry the arbitrary-family
quantifiers and every complete exponent tail.
