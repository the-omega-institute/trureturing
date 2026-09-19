[Index](../marked_head_profile.md) · [Original actual-source comparison](53-allocated-seven-thresholds-sharpen-actual-survival.md) · [Original control faces](71-global-j-k-control-faces-and-exact-escape-gaps.md) · [Previous far boundary](179-the-wider-source-union-reaches-the-far-escape-boundary.md)

# The original signed gap retains its own mass through interpolation

The original actual-source comparison admits the joint bound

    Phi(K0-h)>=gamma2*sigma-(gamma2-gamma1)*sigma^2
                 -h*(53/360+sigma^2/360)+(A-h)*rho,       (GM1)

for every original effective source, every0<=sigma=1-qK<=1,
and every

    0<=h<=H=(20/3)*gamma1=0.31300623832873406089... .    (GM2)

Here A is the original positive signed mass coefficient in71,
rho=S-S0 is the same actual residual as in85/106, and Phi is the
original sufficient signed comparison with all its independent
numerator tests and complete tails. The constant and quadratic
terms multiplied by h in(GM1) are a joint gap/mass bound. They
are not asserted to bound the denominator or S0 separately.

In particular, the whole far-source interval1/2<=sigma<=1 supports
the decrement H. At sigma=1 the previous scalar capacity was
4gamma1=0.18780374299724043653...; the new capacity is5/3 times
that number. This is an actual-source theorem for this branch,
not a complete joined global K bound or a resolution of Erdos7.

## 1. Change the true mass coefficient before interpolating

Use53(A14)--(A15), with its original target K0, offset b and
numerator slope L. Let

    E=q*S+sum_c pi_c*M_c(theta), q=23/42,
    A=q*(K0-b)-L>0,
    G_c(theta)=(K0-b)*M_c(theta)+C_c(theta).

The complete denominator satisfies0<E<=S. Its positivity is the
original survival result; E<=S also follows from53(A14) and the
fact that the actual survival fraction is at most one. The old
sufficient margin and its target change are

    Phi(K0)=A*S+sum_c pi_c*G_c(theta),
    Phi(K0-h)=Phi(K0)-h*E.

Thus, for h>=0,

    Phi(K0-h)>=(A-h)*S+sum_c pi_c*G_c(theta).        (GM3)

The functions here are the globally defined original functions,
with the same actual carrier distribution pi. As proved in49 §7
and53 §7, M_c and C_c are separately concave in each of the five
source groups. In C_c, all numerator-margin coefficients are
nonnegative, and the subtracted raw81 source operator is separately
convex before its minus sign. Also K0-b>0.

The original mass function

    D_c(theta)=s(theta)-(c.n(theta)+R(theta))/5

is separately concave: s and c.n are separately affine, and R is
the sum of maxima of affine functions and affine terms. Consequently

    F_(h,c)(theta)=(A-h)*D_c(theta)+G_c(theta)

is separately concave whenever A-h>=0. The certificate verifies
A-H>0. This is the mathematical function to which Jensen applies.

Let Lambda_v be the original product barycentric weights. At each
source vertex v,71's stored lower gap g_vc satisfies

    F_(h,c)(v)>=g_vc-h*D_c(v).

The same stored lower bounds remain valid because only the exact
D_c coefficient has changed; every unchanged numerator or survival
margin retains its original lower bound. Iterated Jensen, averaging
with the same pi, and S=S0+rho give

    Phi(K0-h)>=sum_(v,c) Lambda_v*pi_c
                         [g_vc-h*D_c(v)]
                    +(A-h)*rho.                    (GM4)

No assertion S0<=sum_(v,c)Lambda_v*pi_c*D_c(v) is used. That
inequality need not hold: concavity gives the opposite direction.
Its nonnegative Jensen surplus is retained automatically by the
nonnegative coefficient A-h in(GM3)--(GM4).

## 2. The complete original table has three joint layers

Let K and J be the original six and eighteen controls. The exact
source values, also valid throughout their original control faces,
are

    K: g=0,      D_c=dK=53/360, raw mass s=1/4;
    J: g=gamma1, D_c=dJ=3/20,   raw mass s=1/4.      (GM5)

The important difference is dJ<1/4. The lowest J gap occurs at
its lower mass endpoint3/20; moving the same source to the upper
endpoint1/4 increases its gap by A/10. One cannot retain the first
value while treating the latter mass as cost free in this joint
comparison.

The exact helper reconstructs the original46656 signed endpoints
from the established rational dictionary and verifies their full
ordered digest. At every one of the23304 lower endpoints outside
K union J, it proves

    g-h*D_c>=gamma2-h*dK,
                     0<=h<=H.                     (GM6)

To check the whole h interval, it checks the two endpoints h=0
and h=H: both sides are affine in h. At h=H the minimum is

    eta=gamma2-H*dK=0.5355140933000165...>0.

At both decrement endpoints, the only controls of(GM6) are source
386 with carrier(1,1) and source592 with carrier(1,0). Both have
D_c=dK and g=gamma2. Every original upper mass endpoint also obeys
the bound: its excess over its lower endpoint is

    (A-h)*(s-D_c)>=0.

This upper-endpoint check is independent evidence that the same
mass/gap association has been preserved. The continuum argument
itself is(GM3)--(GM4), not interpolation of the computed ratios.

For qK=sum_K Lambda*pi, qJ=sum_J Lambda*pi and u=1-qK-qJ,
(GM4)--(GM6) imply

    Phi(K0-h)>=-h*dK*qK+(gamma1-h*dJ)*qJ
                          +(gamma2-h*dK)*u
                          +(A-h)*rho.              (GM7)

All original carriers, including empty and partial carriers, occur
in this statement and in the complete table. No finite-family
realizability of a relaxed control is assumed.

## 3. The original product exclusion gives the full source envelope

Write sigma=1-qK. The original J/K product-support argument retained
in94 and in k_next_escape_layers gives qJ<=sigma^2. Its product
weights interpolate the actual source coordinates; it makes no
independence assumption about the actual forbidden residue labels.

The coefficient of qJ after inserting u=sigma-qJ in(GM7) is

    gamma1-gamma2-h*(dJ-dK)<0.

Substituting qJ<=sigma^2 in that direction, and using
dJ-dK=1/360, proves(GM1) for all0<=sigma<=1. The residual term is
the same nonnegative actual rho throughout.

At h=H one has gamma1-H*dJ=0. The part of(GM1) independent of rho
factors exactly as

    (1-sigma)*[(gamma2-H*dK)*sigma-H*dK].           (GM8)

At sigma=1/2 this equals0.11083778633691677...>0, and at sigma=1
it equals zero. Either(GM8) directly or concavity proves its
nonnegativity on the whole interval[1/2,1]. For0<=h<=H the
right-hand side of(GM1) is no smaller: its h coefficient is
-(dK+sigma^2/360+rho)<0.

At qK=0, the same complete table also gives

    min_(v,c outside K; X in {D_c,s}) g_vc(X)/X
          =gamma1/(3/20)=H.

Exactly the eighteen J lower endpoints attain this minimum. This
identifies the capacity of this particular vertexwise mass-payment
argument. It does not establish equality for an actual covering
family or optimality of a stronger comparison.

## 4. Scope and reproduction

The proof uses the original complete source and numerator formulas,
their established separate concavity, one carrier distribution,
and one actual residual. It changes neither the source geometry
nor any original independent label or infinite tail. The previously
proved comparisons remain available.

The [helper](../frontier/joint_gap_mass_escape.py) and
[certificate](../certificates/source_norms/joint_gap_mass_escape.json)
check the original full table, all three layers at both decrement
endpoints, the mass-coefficient sign and the exact final polynomial.
They accompany the ordinary proof above; no Lean or frozen-state
claim is made. Joining this stronger unmarked branch with the
complete local domains, all eight fallback comparisons and both
terminal errors is a separate global comparison obligation.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/joint_gap_mass_escape.py --check
```
