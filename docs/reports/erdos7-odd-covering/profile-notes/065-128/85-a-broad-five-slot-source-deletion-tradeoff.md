[Index](../../marked_head_profile.md) · [Actual source budgets](../001-064/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Common deletion measure](../001-064/57-common-deleted-measure-coupling.md) · [K zero faces](71-global-j-k-control-faces-and-exact-escape-gaps.md)

# A broad five-slot source/deletion tradeoff

The actual source geometry gives a uniform tradeoff on the whole slab

    Delta=(z-3/4)+(1/4-alpha1)
                         +(1/4-beta2-beta3-beta4)<=1/18.

Let r be the smallest raw-source loss among the five first-five
slots, and rho=S-sum_c pi_c*D_c the actual common-carrier mass
residual. Then either

    r>=1/12000 and rho>=1/60000,                       (S1)

or every independently chosen modulus-5 test slot F_J satisfies

    mu(F_J)<=h/5-r-Gamma,
    Gamma=[min(397/36000,
          1199/60000-(4000/397)*(rho-r/5))]_+.         (S2)

The second branch has r<1/12000. All quantities use one actual
source and deletion measure. The theorem permits arbitrary
deficit and late-source coordinates, changing original residues,
absent labels and complete exponent tails. It does not assume
S=D or concentration on one particular forbidden carrier.

The product-barycentric region with mass at least25/27 on the
union of the two K zero boxes lies in this slab. There is also
a joint modulus-5/modulus-15 interface for bounded fourth and
fifth hinges of a six-label head, proved in section7.

These are ordinary mathematical constraints with exact rational
checks. They have not been converted into an additional increment
of the old direction-40 margin or a new global K bound. No actual
covering construction or Lean verification is claimed.

## 1. Actual measures and their budget deficits

Use the effective-source branch of48. The five surviving ternary
cells have ROOT=(0,0,1,1,1). With the actual assigned source budgets,

    eta_c=(1-deficit_c)/9,
    d_c=z-alpha_ROOT(c)-beta_c,
    n_c=eta_c*d_c-late_c,
    h=sum_c eta_c, h0=eta0+eta1, h1=eta2+eta3+eta4.

The nonnegative deficit, alpha, beta and late vectors have total
caps1/2,1/4,1/4 and1/72, respectively, and3/4<=z<=1.
Here eta is the raw pure3 survivor measure, Lambda is the actual
raw35 source, and s=Lambda(1). The source quantities

    p=z-3/4, a=1/4-alpha1,
    b=1/4-(beta2+beta3+beta4), Delta=p+a+b             (B1)

are budget deficits in[0,1/4], not independent probabilities.

Write F_0,...,F_4 for the first-five slots, including the full
ternary coordinate in their meaning. Define

    x_j=h/5-Lambda(F_j), r=min_j x_j,
    H in argmin_j x_j, m=Lambda(F_H)=h/5-r.           (B2)

All x_j are nonnegative because Lambda<=eta times raw-five Haar.

For each present original mixed7 label, retain its actual old
cofactor cylinder C_i and seven depth e_i. With u_e=6/(5*7^e),
profile57 defines the positive measures

    V(dx)=sum_i u_(e_i)*1_(C_i)(x)*Lambda(dx),
    delta(dx)=actual projected mixed7 deletion,
    mu=Lambda-delta, omega=(V-delta)(1)>=0.           (B3)

The actual normalized seven probabilities can be smaller than u_e;
overlap and this cap loss are both included in omega. The common
actual carrier mixture pi of46 gives

    S0=sum_c pi_c*D_c(theta), rho=S-S0,
    T=s-S0, V(1)<=T,
    rho=[T-V(1)]+omega.                              (B4)

This exact decomposition is used once throughout the argument.

## 2. A root-wide packing set separates the best slot

First suppose the original source labels5,15,45 are present,
label15 is on root1, label45 is in a root1 cell L, and their
first-five slots P,A,B are pairwise distinct. These are hypotheses
for this general lemma; section4 proves them throughout the slab.

Let U be the five-coordinate union of the complete pure5 source
family and the complete alpha family on root1. Since alpha1 is
the additional measure after pure5 deletion,

    |U|_5=(1/4-p)+(1/4-a)=1/2-p-a.

Every point in U is deleted throughout the whole root1 ternary
mass. Both P and A lie in U, so for R=U minus(P union A),

    |R|_5=1/10-p-a.                                 (P1)

The complete beta tail after first five depth has capacity
sum_(k>=2)5^-k=1/20. The total root1 beta budget is1/4-b;
therefore the first beta label contributes at least1/5-b after
pure5 and alpha deletion. Its first slot is B, giving

    |U intersect B|_5<=b,
    |R intersect B|_5<=b.                            (P2)

This deduction does not identify the five projections of beta
labels in different ternary cells.

Let eta_star=min(eta2,eta3,eta4), and suppose

    r<min(h/5,h1/5,eta_star/5).                       (P3)

The complete source deletion in P, in root1 times A, and in cell L
times B shows that H differs from P,A,B. Write Q for the remaining
fifth slot. Since R is deleted throughout root1,

    |R intersect H|_5<=r/h1.

Its only possible slots are B,H,Q. Equations(P1)--(P2) imply

    |R intersect Q|_5>=1/10-Delta-r/h1.

It follows that every non-H slot obeys

    x_j-r>=G, j!=H,
    G=min(h/5-r,h1/5-r,eta_star/5-r,
                              h1*(1/10-Delta)-2*r).  (P4)

The first three entries are the P,A,B gaps. The last uses the
root-wide R deletion in Q. Formula(P4) remains a valid lower bound
when G is nonpositive. Every division by G below additionally
requires G>0; (P3) alone does not establish that condition.

## 3. Keep actual cofactor capacity and union loss separate

Restrict V to the original forbidden cofactors5*7^e, e>=1,
calling the resulting virtual measure V5. Define

    E5=h/25-V5(1).                                  (D1)

This is an actual unused-capacity quantity. The complete pure5
cofactor budget in T is

    h*sum_(k>=1)5^-k*sum_(e>=1)u_e=h/20
                       =h/25+h/100.                 (D2)

The first summand is exactly the capacity used in(D1); the
second covers all k>=2. Conditioning on the shallow ternary
carrier changes other cofactor terms, not this one. Therefore
E5 is a nonnegative summand of T-V(1), and

    E5+omega<=rho.                                  (D3)

Let q5 be the sum of u_e over those original cofactor-5 labels
whose old slot differs from H, together with every absent label.
The complete sum of all u_e is1/5. A present H label loses r
relative to its individual h/5 cap; a present non-H label loses
at least r+G. An absent label loses h/5, also at least r+G
because G<=h/5-r. Thus

    E5>=r/5+G*q5.                                   (D4)

In particular E5>=r/5 holds without a positive gap, directly
from the maximality of Lambda(F_H). Assume now G>0. Since

    V5(F_H)=m*(1/5-q5),

the one error measure V-delta gives

    delta(F_H)>=m/5-(m/G)*(E5-r/5)-omega.             (D5)

For an arbitrary independent modulus-5 test slot F_J, its
surviving mass is therefore at most

    mu(F_J)<=m-Gamma_var,
    Gamma_var=[min(G,m/5-(m/G)*(E5-r/5)-omega)]_+.     (D6)

If J differs from H, use Lambda(F_J)<=m-G. If J=H, use(D5)
and the additional elementary bound delta(F_H)>=0. This explains
the positive-part truncation in(D6).

For the simpler residual form put

    t=rho-r/5>=0, c=max(1,m/G).

Both E5-r/5 and omega are nonnegative, and their sum is at most t
by(D3). Consequently

    mu(F_J)<=m-Gamma_rho,
    Gamma_rho=[min(G,m/5-c*(rho-r/5))]_+.             (D7)

The two defects in(D6) have not been assigned independent laws;
(D7) is an upper bound on their total charge inside(B4).

## 4. Uniform constants on the slab Delta<=1/18

The whole effective source domain satisfies

    1/2<=h<=5/9, 5/18<=h1<=1/3,
    h1-h0>=1/18, 1/18<=eta_c<=1/9.                  (G1)

These follow from the total deficit cap1/2. In particular they
do not require the deficit or late coordinate to lie near either
controlling face.

On Delta<=1/18, each of p,a,b is at most1/18, so each corresponding
source budget is at least7/36. This exceeds the post-first-depth
capacity1/20 by13/90. Hence label5 is present, label15 is present
on root1, and label45 is present in a root1 cell. If P=A, the first
alpha label contributes no additional measure and its root1 budget
is at most1/20. If B=P or B=A, the same argument applies to the
root1 beta budget. All contradict7/36>1/20. Thus the three first
slots are pairwise distinct, as required in section2.

Take

    r0=1/12000, g0=397/36000.

If r>=r0, the always-valid E5>=r/5 and(D3) give(S1).
If r<r0, condition(P3) follows from(G1), and all four entries of
(P4) are bounded below by

    h/5-r >=1/10-r0,
    h1/5-r>=1/18-r0,
    eta_star/5-r>=1/90-r0=g0,
    h1*(1/10-Delta)-2*r
       >=(5/18)*(2/45)-1/6000
        =1973/162000>g0.                            (G2)

The final strict gap is373/324000. Therefore G>=g0>0 throughout
this branch, discharging every division condition in(D5)--(D7).
Also

    m/5>=1199/60000, m<=1/9,
    max(1,m/G)<=4000/397.                            (G3)

For t=rho-r/5>=0, substitution in(D7) proves(S2).
The positive-part bound has a constant branch, a decreasing affine
branch and a zero branch. It is valid for all actual residuals;
positivity is claimed only where the displayed expression is positive.

## 5. The K zero-box concentration region lies in this slab

Use71's product-barycentric convention: simplex index0 is the zero
vector, index j>0 is the corresponding cap basis vector; z0 means
z=3/4. Let zeta be the product mass, including the actual carrier
weights, on the union of the two K zero boxes. Both boxes require

    alpha factor=2, beta factor in{3,4,5}, z factor=0.

Write their three common factor weights as a2,b345,z0. Since the
zero union lies in each of these events,

    zeta<=a2, zeta<=b345, zeta<=z0.

The actual source coordinates satisfy

    a=(1-a2)/4, b=(1-b345)/4, p=(1-z0)/4.

Thus

    zeta>=25/27 => p,a,b<=1/54 => Delta<=1/18.        (C1)

This is a product-mass concentration statement with complement2/27.
It imposes no additional deficit, late or carrier concentration
condition in the proof of(S1)--(S2). It is not a Euclidean-radius
claim or an interpolation of newly improved vertex values.

## 6. Modulus15 shares the same residual budget

Remain in the small-r branch Delta<=1/18, r<r0. Set

    m1=Lambda(root1 times F_H), r1=h1/5-m1.

The loss on root1 times H is part of the full H loss, so
0<=r1<=r. Every old cofactor15 cylinder other than root1 times H
has mass at most m1-g0. To see this, a root0 cylinder has mass
at most h0/5, and

    m1-h0/5>=(h1-h0)/5-r>=g0.

On root1, P and A are deleted entirely; B loses at least eta_star/5;
and Q loses at least h1*(1/10-Delta)-r. Subtracting r1 gives the
same guards as(G2). A cylinder in the removed ternary root contributes
zero and also satisfies the bound.

Let V15 be the virtual measure of the distinct original forbidden
labels15*7^e. Define

    E15=h1/25-V15(1),
    q15=sum_(wrong old carrier or absent label)u_e.

The same complete-cap argument gives

    E15>=r1/5+g0*q15,
    E5>=r/5+g0*q5.                                  (J1)

The complete cofactor families5^k and3*5^k are disjoint sets of
original labels. Their contributions h/20 and h1/20 to the old
mass cap are separate. Therefore(B4) yields the joint inequality

    E5+E15+omega<=rho,
    rho-(r+r1)/5>=0.                                (J2)

One must use this shared inequality, rather than charging omega
once for each family. The original seven residues remain arbitrary.

## 7. A bounded-head interface retains both families with one error charge

Let B be the load of the six original test moduli{1,3,9,5,15,45},
including the unit. For t in{4,5}, put phi=(B-t)_+ and M=6-t.
Pointwise0<=phi<=M. More strongly, in any fixed first-five column,

    sum_(c=0..4)phi(c,H)<=M.                         (H1)

Indeed B<=4+1_(c=c9)+1_(c=c45,s=s45): the unit, test3, test5
and test15 contribute at most4. For t=4, sum the two remaining
cell indicators. For t=5, positivity requires both cell indicators
at once and the value is at most1. Missing or source-disjoint
test labels only reduce these bounds.

Since Lambda(cell_c times F_H)<=eta_c/5<=1/45, (H1) gives

    I_H=integral_(F_H)phi dLambda<=M/45,
    I_1H=integral_(root1 times F_H)phi dLambda<=M/45. (H2)

Drop nonnegative wrong-carrier contributions from each virtual
integral. Equations(J1)--(H2) then give, with k_M=M*800/397,

    integral_V5 phi >=I_H/5-k_M*(E5-r/5),
    integral_V15 phi>=I_1H/5-k_M*(E15-r1/5).          (H3)

The coefficient is exact:1/(45*g0)=800/397.

One may also retain the exact virtual measures V3,V9 from the
original cofactor3 and cofactor9 families. Their supports may vary
at every seven depth, and absent labels contribute zero. All four
families are distinct subsets of V. The bounded transfer of57,
applied once to0<=phi<=M, gives

    integral_delta phi
       >=integral_(V3+V9+V5+V15)phi-M*omega.

Combining this with(H3), the exact identity mu=Lambda-delta,
and the single budget(J2) yields

    integral_mu phi
       <=integral_Lambda [1-(1_H+1_(root1 times H))/5]*phi
          -integral_(V3+V9)phi
          +k_M*[rho-(r+r1)/5].                      (H4)

Here k_M>=M permits M*omega<=k_M*omega. The weaker form with
the last bracket replaced by rho is also valid. Alternatively,
before using(J2), the exact separate error allowance is

    k_M*[(E5-r/5)+(E15-r1/5)]+M*omega.              (H5)

Thus the new first-slot observations can enter a common-head source
bound while charging the actual union/cap loss only once. The exact
V3,V9 integrals are retained virtual payments, not additional
independent mass-residual budgets.

## 8. Verification and remaining comparison obligation

The [checker](../../frontier/endpoint-bounds/broad_five_slot_tradeoff.py) verifies the
affine parameter-domain bounds, all four rational slab guards,
the wrong-root15 guard, the complete first-five remainder1/20,
the complete seven weight1/5, and the zero-box containment giving
25/27=>Delta<=1/18. It checks125000 combinations of shallow
head, column and threshold for(H1), whose ordinary proof is given
above. These are bounded-function checks, not claimed actual
congruence-family realizations. Its
[certificate](../../certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json)
retains the exact constants, budget definitions, guards and interface.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/broad_five_slot_tradeoff.py --check
```

The source packing uses only finitely many first slots and complete
nonnegative label budgets. All virtual sums converge by their
complete geometric cap bounds, so absent finite-family tails and
changing original residues are included. Bounded transfer requires
no unbounded-moment approximation here.

The result supplies a broad conditional constraint on actual source
and deletion. To improve the old comparison, a consumer must retain
these observations jointly with the old source/event payments and
prove the remaining gain without counting an existing payment again.
Neither a positive increment of the old identity-cost margin nor
a consequent global K improvement is established by this note.
