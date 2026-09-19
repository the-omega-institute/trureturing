[Index](../marked_head_profile.md) · [Source compatibility](48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Full conditional costs](49-full-linear-and-quadratic-carriers-refine-the-frontier.md)

# Sharp source compatibility and the off-diagonal endpoints

In the effective9 source branch of profiles46 and48, the infimum of
limiting normalized survivor masses over actual finite original-label
families whose source parameters tend to theta402 is

    233/1500 = D402 + 2/375.

The corresponding off-diagonal endpoint(theta404,D404), with the beta
budget in cell2 and the late budget in cell3, is attainable. Here
D402=D404=3/20. Both statements concern limits of finite families;
neither asserts an integer covering or resolves unrestricted Erdos #7.
The arguments below are ordinary mathematical proofs, not Lean results.

## 1. A continuous universal source correction

Retain eta, Lambda, lambda, S and D from profile48. Write

    h0=eta0+eta1, h1=eta2+eta3+eta4, h=h0+h1,
    delta=(z-3/4)+(1/4-alpha1)+(1/4-beta2),
    epsilon=1/72-late2.

The source constraints give delta,epsilon>=0 and

    h>=1/2, 5/18<=h1<=1/3, h0<=2/9, eta2>=1/18,
    h1-h0>=1/18, 5*eta2>=h1, 4*h1>=5*h0.

For every actual finite original-label family in this branch,

    S>=D+(2*h1/125-2*delta/3-12*epsilon)_+.       (1)

Under delta<1/125 and epsilon<1/2250, a stronger bound holds:

    S>=D+(2*h1/125-2*epsilon)_+.                 (2)

All exponents are unrestricted in these inequalities. Absent labels
are accounted for by the full unused geometric budget.

For five-adic cylinders P of depth1 and Q of depth2, let

    m5 =max_P Lambda(Z3 x P),
    m25=max_Q Lambda(Z3 x Q),
    m15=max_(r,P) Lambda(root r x P),
    m75=max_(r,Q) Lambda(root r x Q),
    A0=h/5-m5+h/25-m25,
    A1=h1/5-m15+h1/25-m75.

All four component losses are nonnegative. The four old caps occur
separately in the complete cofactor sum defining D. Replacing only
these four caps by the actual maxima and summing the complete
normalized seven-coordinate caps gives

    S>=D+(A0+A1)/5.                              (3)

Indeed nu7(E_e)<=6/(5*7^e), and the sum over e>=1 is1/5. Each original
mixed7 label keeps its independently chosen old-coordinate carrier.

### Shallow budget forces two levels of geometry

Write P_b,A_b,B_b for the five-coordinate cylinders of source labels
5^b,3*5^b,9*5^b, with A counted only when on root1 and B only when in
cell2. The effective five-coordinate union in cell2 has mass

    (1-z)+alpha1+beta2=3/4-delta.

The sum of all three raw label budgets is3/4. Partition their effective
union among its original labels. The sum of all unused label budgets
is exactly delta. Consequently delta<1/125 forces the nine labels at
b=1,2,3 to be present, correctly located, and pairwise disjoint in
the five coordinate. A missing or misplaced one wastes at least1/125;
an overlap of two cylinders of these depths also wastes at least1/125.

P1,A1,B1 occupy three full depth1 slots. Let Y be the parent of P2 and
X the fifth slot. Partition actual additional late deletion in cell2
among its original deep labels, writing

    c_(a,b)=3^-a*5^-b, 0<=q_(a,b)<=c_(a,b),
    d_(a,b)=c_(a,b)-q_(a,b),
    epsilon_b=sum_(a>=3)d_(a,b), sum_b epsilon_b=epsilon.

An absent label receives q=0. Any b=1 late label outside X loses at
least one fifth of its raw budget, or contributes zero to cell2.
If any of the nine shallow cylinders were inside X, every b=1 late
label over X would lose at least1/25 of its raw budget. Thus epsilon
would be at least(sum_(a>=3)c_(a,1))/25=1/2250. In the strict
neighborhood this is impossible.

It follows that P2,A2,B2 occupy three distinct children of Y. The
depth2 parent V of P3 is a fourth child; let W be the fifth. W need
not be entirely source-free.

### Assigned deletion supplies the two-depth loss

The raw b=1 and b=2 budgets are respectively a=1/90 and b=1/450.
Call a b=1 label good if it is in cell2 over X. Every other such label
loses at least3/5 of its raw budget: Y has three excluded children,
the three other depth1 slots are excluded, and labels outside cell2
contribute zero. If C_bad is its total bad raw budget and E_bad,E_good
are the corresponding deficits, then

    C_bad<=(5/3)*E_bad, E_bad+E_good=epsilon1,
    assigned good deletion over X>=a-(5/3)*epsilon1.   (4)

Define source losses, for any five-coordinate set B,

    L(B)=h*mu5(B)-Lambda(Z3 x B),
    L1(B)=h1*mu5(B)-Lambda(root1 x B).

Each is a nonnegative measure. Every assigned late piece lies in the
deleted part of eta tensor Haar5 and in root1. A good raw b=1 rectangle
places one fifth of its raw mass in each child Q of X. Removing an
assigned deficit d can lower that restriction by at most d. Hence,
for either L or L1 and for every child Q of X,

    L(X)+L(Q)>=(6/5)*(a-C_bad)-2*E_good
               >=1/75-2*epsilon1.                    (5)

Call a b=2 label good if its ternary support is in cell2 and its five
cylinder is either a child of X or W. Any other b=2 label loses at
least1/5 of its budget; in V the pure5 source P3 supplies this loss.
Its total assigned good deletion is therefore at least b-5*epsilon2.
The assigned b=1 and b=2 deletions are disjoint and are contained in
X union W. For either loss measure this proves

    L(X)+L(W)>=1/75-(5/3)*epsilon1-5*epsilon2
               >=1/75-5*epsilon.                     (6)

### Independent maximizing carriers

For A0, if its maximizing depth1 slot is not X, the depth1 loss alone
is at least h1/25: the four possibilities P1,A1,B1,Y have losses at
least h/5,h1/5,eta2/5,h/25, respectively.

If it is X, a maximizing depth2 child of X is covered by(5), and W by
(6). Every other depth2 slot has shallow source loss at least1/450:
the fully excluded cases give at least eta2/25, and V gives h/125.
Adding(4) then gives at least1/75-(5/3)*epsilon1. Since h1/25<=1/75,

    A0>=(h1/25-5*epsilon)_+.

For A1, a depth1 carrier in root0 has loss at least
(h1-h0)/5>=h1/25; a depth2 carrier in root0 has loss at least
(h1-h0)/25>=1/450. A carrier in the killed root has its whole nominal
cap as loss. Within root1 the same cases apply. In particular the
V loss is h1/125>=1/450. Thus

    A1>=(h1/25-5*epsilon)_+.

Substitution in(3) proves(2). To prove(1) globally, use h1<=1/3.
Outside the strict neighborhood either 2*delta/3>=2/375 or
12*epsilon>=2/375, so the correction in(1) is zero. Inside it,(2)
implies(1). At theta402, h1=1/3 and delta=epsilon=0. Continuity of D
and the correction gives the claimed lower limit233/1500.

## 2. Matching finite families for theta402

Use cells C0=[0]9,C1=[3]9,C2=[1]9,C3=[4]9,C4=[7]9. Pure3 labels
are[2]3,[6]9, and T_a(0,1) at a>=3, where

    T_a(c,j)=[c+j*3^(a-1)]_(3^a), j=1,2.

For fixed c the T cylinders are pairwise disjoint in(a,j). Define

    F_(j,b)=[j*5^(b-1)]_(5^b), j=1,2,3,4,
    X=F_(4,1), Q=[4]25 subset X, Y2=F_(4,2),
    E_b=[20+5^(b-1)]_(5^b), b>=3.

The F cylinders are pairwise disjoint. The E cylinders are pairwise
disjoint inside Y2. Source labels pure5,3*5^b,9*5^b use F_(1,b),
root1 x F_(2,b),C2 x F_(3,b). Deep mixed35 labels use

    a>=3,b=1: T_a(1,1) x X,
    a>=3,b=2: T_a(1,2) x Q,
    a>=3,b>=3: T_a(1,1) x F_(4,b).

Every deep source rectangle avoids the shallow exclusions and the
pure3 deletion. They are mutually disjoint; in particular the two
ternary families separate b=1 and b=2 despite Q subset X. Y2 is free
of all five-coordinate source deletions.

At height N>=3 put

    t=(1-3^(2-N))/18, q=(1-5^-N)/4,
    u7=(5+7^-N)/6, kappa=(1-7^-N)/(5+7^-N).

The finite source data are

    deficit=(9t,0,0,0,0), alpha=(0,q),
    beta=(0,0,q,0,0), z=1-q, late=(0,0,tq,0,0),
    s=5/9-t-q.

For mixed7 labels take the following old carriers and class indices;
V1=X,V2=Y2.

| Cofactor | Old carrier | Class |
| --- | --- | --- |
| a=1,b=0 | root0 x Z5 | 1 |
| a=2,b=0 | C1 x Z5 | 2 |
| a>=3,b=0 | T_a(0,2) x Z5 | 2 |
| a=0,b=1,2 | Z3 x V_b | 3 |
| a=1,b=1,2 | root1 x V_b | 1 |
| a=2,b=1,2 | C1 x V_b | 5 |
| a>=3,b=1 | T_a(4,1) x X | 5 |
| a>=3,b=2 | T_a(7,1) x Y2 | 5 |
| a=0,b>=3 | Z3 x E_b | 4 |
| a=1,b>=3 | root1 x E_b | 2 |
| a=2,b>=3 | C3 x E_b | 5 |
| a>=3,b>=3 | T_a(0,2) x E_b | 5 |

Let G_(j,e)=[j*7^(e-1)]_(7^e). Pure7 uses class6; mixed7 uses its
table class. The G cylinders are mutually disjoint across(j,e).
Within each class old carriers are disjoint. In class5 the nested
five supports Y2 and E_b are separated by ternary supports: those at
b=2 are in C1,C4, whereas those at b>=3 are in C3,C0. All other
within-class separations follow directly from distinct roots, cells,
T cylinders or E cylinders. Thus all mixed7 rectangles are disjoint
and avoid the pure7 source. CRT gives one original residue for each
nonunit modulus in the complete finite exponent box.

The old-carrier mass sum can be checked in five groups, by a=0,1,2,
a>=3 with b>0, and the pure3 cofactors. The pure3 group is(1-q)/3.
The two groups a=0 and a=1 each lose exactly6t/25 from their nominal
caps, because X contains the entire b=1 and b=2 deep source deletion.
All their b>=2 selected carriers lie in source-free Y2. The remaining
two groups attain their nominal caps. Consequently

    H=(1-q)/3+(5/9-t)*q-6t/25
       +q/3-6t/25+q/9+tq
     =1/3+2q/3-12t/25,
    S=s-kappa*H.

As N tends to infinity, s tends to1/4, H to71/150 and kappa to1/5.
This gives S tending to233/1500 and proves sharpness of the lower
limit. The source gap over D402 is2/375. Relative to profile48's
earlier interval, the new value is1/1125 above139/900 and1/4500
below7/45.

## 3. The off-diagonal endpoint remains attainable

Keep the same shallow source but replace every deep35 source label
by T_a(4,1) x F_(3,b). These lie in C3 while the shallow beta deletion
lies in C2. Every source label still spends its complete additional
budget. The source data are unchanged except

    late=(0,0,0,tq,0),

so they tend to theta404. Choose mixed7 old carriers and classes

| Cofactor | Old carrier | Class |
| --- | --- | --- |
| a=1,b=0 | root0 x Z5 | 1 |
| a=2,b=0 | C1 x Z5 | 2 |
| a>=3,b=0 | T_a(0,2) x Z5 | 2 |
| a=0,b>=1 | Z3 x F_(4,b) | 3 |
| a=1,b>=1 | root1 x F_(4,b) | 1 |
| a=2,b>=1 | C1 x F_(4,b) | 5 |
| a>=3,b>=1 | T_a(7,1) x F_(4,b) | 5 |

Use G_(j,e) as before. All positive5 carriers lie in source-free
F_(4,b); the ternary supports separate the class5 carriers, and the
other classes are disjoint for the same reasons as above. Thus

    H=(1-q)/3+(5/9-t)*q+q/3+q/9+tq
     =1/3+2q/3,
    S=5/9-t-q-kappa*H -> 3/20.

At the limiting source vertex,

    n=(1/24,1/12,1/36,1/24,1/18), s=1/4,
    R(n)=1/8, max(n)=1/12, max(d)/18=1/24,
    (h+h1+max(eta))/4+1/72=1/4.

The total old cap sum is1/2, so D404=1/4-(1/5)(1/2)=3/20. This
verifies the claimed endpoint against the same D used in the bounds.

At every present seven-depth the shallow carrier is(0,1). The
profile46 mixture uses empty padding at missing depths; therefore at
finite N its weights are

    pi_(0,1)=1-7^-N, pi_empty=7^-N.

Only the limiting mixture is concentrated exactly on(0,1).

The limiting survivor vector is also explicit. The old-carrier masses
by cell are

    H_l=(7/72,2/9,1/18,1/18,5/72).

To obtain these entries, the pure3 cofactors contribute
((eta0+t)*(1-q),2*eta1*(1-q),0,0,0). The four positive5 groups
contribute eta*q, eta restricted to root1 times q, (q/9)*e1, and
(t*q)*e4, respectively. Their limits give the displayed vector.
Therefore

    S_l=n_l-H_l/5=(1/45,7/180,1/60,11/360,1/24).

With omega=(1/5,2/5,0,0,0), the remainder vector in profile44 is

    r=n-omega*n-S=(1/90,1/90,1/90,1/90,1/72)
     =eta/20+(eta restricted to root1)/20
          +eta1*e1/20+d0*e0/90+e4/360.

This is a member of the existing weighted-cap support set, and its
total7/120 equals R(1). Thus the full vector and limiting concentrated
carrier are jointly attainable by actual families. This does not
establish simultaneous attainment of the source-cost envelopes or
numerator comparisons in profile44; those are separate quantities.

The eighteen existing control vertices have two choices of depleted
cell in the two-cell root, three choices of beta cell in the other
root, and three choices of late cell there. Six have the latter two
cells equal; twelve have them distinct. Permuting the first ternary
digit after a fixed root permutes its mod9 cells and maps every
deeper cylinder to a cylinder of the same depth. It preserves Haar
measure, every original modulus and all the source parameters up to
that permutation. Hence the sharp same-cell statement has six such
copies, while the off-diagonal construction supplies all twelve
distinct-cell copies. The new correction excludes the six same-cell
pairings with S=D, not all eighteen control points.

## 4. The old barrier boundary persists on actual finite families

Retain precisely profile44's source envelopes, fixed profile43
numerator comparison, and old m25 term. For each N use the actual
theta404-approaching family above, with its true cell vector S_N and
the finite mixture pi_N. Put omega_N=sum_c pi_(N,c)*omega_c. Allow
arbitrary nonnegative five-component barrier vectors C_(4,N),C_(5,N),
with no bound uniform in N.

For one threshold t and barrier C, the existing conditioned margin is

    m_t(C,pi_N)=C.n-C.(omega_N*n)-P_t-R(C)-F_theta(g_t),
    g_(t,l)=psi_t-omega_(N,l)*min(C_l,h_t).

The actual weighted deletion inequality is

    C.(n-S_N)<=C.(omega_N*n)+R(C), C>=0.

It therefore implies, without replacing S_N by a relaxed endpoint,

    m_t(C,pi_N)-C.S_N<=-P_t-F_theta(g_t)
                      <=-P_t-F_theta(g_(t,star,N)),
    g_(t,star,N)=psi_t-omega_N*h_t.               (7)

The second inequality is profile44's convex-increment comparison:
g_t-g_(t,star,N)=omega_N*h_(t+C) cellwise. It applies also to the
finite mixture, since0<=omega_(N,l)<=2/5, so all native hinge
coefficients remain nonnegative. No monotonicity for arbitrary
pointwise cost differences is used.

The stronger common clipped-remainder version also obeys(7) after
summing thresholds. Specifically put alpha4=1/6,alpha5=4/33 and
Cbar=alpha4*C4+alpha5*C5. Its combined barrier contribution is

    Cbar.(n-omega_N*n-S_N)-R(Cbar)
         -sum_t alpha_t*[P_t+F_theta(g_t)]
      <=-sum_t alpha_t*[P_t+F_theta(g_(t,star,N))].

Thus every such survival denominator on the actual family is at most

    B_N=(193/231)*sum_l S_(N,l)+m25(theta_N)/22
         -sum_t alpha_t*[P_t(theta_N)
                          +F_(theta_N)(g_(t,star,N))].       (8)

The upper bound is independent of all ten barrier coordinates. The
inherited source formulas are continuous finite maxima with complete
geometric tails, so B_N tends to the theta404 value. Direct exact
evaluation at theta404 gives the same old constants as at theta402:

    m25=68963/441000,
    P4+F(g_(4,star))=3365273/15435000,
    P5+F(g_(5,star))=272031233/1620675000,
    B=2025618599/26741137500,
    N_D=235676572069506444982211913251473065480803
        /6360462916399256045941092769236000000000.

Here N_D is the old combined numerator comparison at S=3/20, not a
claimed actual test integral. With C0=185694867601/8599322160, any
positive-denominator certificate using these unchanged comparisons
must therefore have limiting upper-bound value at least

    C0+N_D/B
      =1208994069650187954348450703035483220540461139
        /2367081918117057277892487238031745380160000
      =510.75294876651606... .

Indeed its denominator is at most B_N, its unchanged numerator tends
to the positive N_D, and B_N tends to the positive B. The bound(8)
is independent of C_(t,N), so barriers diverging with N cannot evade
this conclusion. A nonpositive denominator is inadmissible for that
ratio certificate.

This is an obstruction to the unchanged comparison family on actual
families. It does not assert that actual source-cost envelopes or
test integrals attain their comparison values. Profile47 and any
other route that changes the numerator comparison are outside the
scope of this numerical stopping bound.

## Verification scope

The universal lower bound, all-depth disjointness, mass identities and
barrier obstruction above are ordinary mathematical proofs. Neither
finite enumeration nor Lean verification is used to establish them.

The independent standard-library construction checker
[sharp_source_mass_endpoints.py](../frontier/sharp_source_mass_endpoints.py)
checks both families at heights3,4,5,6:63,124,215,342 distinct original
moduli respectively. It reconstructs all five source-cell masses,
all five cofactor-category masses, disjoint old-coordinate carriers
within every seven class, disjoint seven cylinders and the finite
cap-mixture tail. At height3 it separately enumerates the complete
CRT union on a period of1,157,625. Height6 exercises both the nonzero
global correction and the strict-neighborhood inequality.

The independent comparator checker
[actual_cellwise_barrier_boundary.py](../frontier/actual_cellwise_barrier_boundary.py)
reconstructs the theta404 constants, the limiting actual survivor
vector and its weighted-cap support decomposition. These exact
calculations check the numerical inputs of section4; the uniform
statement for all finite barrier vectors follows from(7)--(8).

Both programs are read-only by default and accept `--output PATH`
for exact rational JSON results:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/sharp_source_mass_endpoints.py
python3 -I -O docs/reports/erdos7-odd-covering/frontier/actual_cellwise_barrier_boundary.py
```

The mass correction has not been inserted into the global K bound.
It is a separate constraint on the same actual S, not an additive
credit to every carrier-specific D_c. The twelve off-diagonal
controls still approach their old mass endpoint. Unrestricted
Erdős #7 remains open.
