[Index](../../marked_head_profile.md) · [Previous](35-ap45-layout-costs-and-complete-core-tails.md)

<a id="joint-moment-caps-do-not-improve-the-row17-bound"></a>
# Joint marginal moments do not improve the current row17 bound

The four scalar bounds for the actual AP(4,5) law admit an abstract
joint law that saturates the existing row17 upper bound. This remains
true after imposing the additional cubic cap

    M=18967452734315727/3954501738752

on BOTH marginals. Here M is an explicit constraint of the abstract
model. This result does not assert a published uniform cubic-moment
bound for actual AP(4,5) tests. Even granting that additional information
would not improve the row bound through these marginal constraints alone.

The obstruction is sharp for integer Y>=1 and real Z>=1; its witness
has integer coordinates in both variables. No independence of Y and Z
is assumed. No realization by an actual forbidden layout is claimed.

## The actual row comparison and its marginal relaxation

Fix the normalized actual AP(4,5) probability sigma from profile35.
For every original positive17 depth e, extend the actual mixed old
cofactor indicators to one globally legal complete old test A_e,
including its unit term. Each test's original residues are chosen
once globally. They cannot be optimized afresh on each sampled row.
Complete absent depths as well and set

    Z=sum_(e>=1)16*17^(-e)*A_e.

The weights sum to1, so Z>=1. The original old box is finite, hence
these complete tests are bounded for that box and the weighted series
converges. The same construction can be passed through the established
uniform bounds; it does not delete a positive-depth tail.

The actual row inequalities DP6 and the weighted pair comparison in
profile30 give

    beta<=(Z-8)+/8,
    c_row<=kappa(Z)=16/(16-min(Z,8)),
    Xi17^-(sigma)<=(25/128)*sup_Y E_sigma[c_row*Y²].

Here Y ranges over globally legal complete original old tests. It is
not identified with any A_e. The assigned charge E_sigma beta is
independent of the optimizing test Y, so

    F17^-(403;sigma)<=sup_Y E_sigma G(Y,Z),
    G(y,z)=(403/8)*(z-8)++(25/128)*kappa(z)*y².       (JM1)

All terms use this same sigma. The physical17 and killed17 output
laws are not substituted for sigma. Original residues may be chosen
separately across tests; this is not probabilistic independence.

For each convex cost f on[1,infinity), Jensen gives

    E_sigma f(Z)<=sum_e16*17^(-e)*E_sigma f(A_e)
                 <=sup_A E_sigma f(A).              (JM2)

Consequently every uniform convex old-test cap also bounds Z. The
four published costs below are convex; so is x³. Applying(JM2) to a
cubic cap on actual tests would require proving that cap first. The
abstract obstruction below treats M as an additional granted constraint.

## The abstract optimization problem

Put

    h16(x)=(x²-16)+,          g5(x)=(x-5)+,
    phi17(x)=(5/11)*(x-5)++(10/99)*(x-6)+
             +(5/36)*(x-7)++(3577/72)*(x-8)+,
    phi19(x)=(112/351)*(x-5)++(224/3861)*(x-6)+
             +(112/1485)*(x-7)++(39449/990)*(x-8)+.

The four exact AP(4,5) bounds from the parent certificate are

    B16=270846242176061447735/1995737886953762094,
    B17=100132727701502372144877582605922281
          /674726358062825744606823291399000,
    B19=80861588193887548056649424431479320087
          /681895325617243268143270788870114375,
    B5=879407880702997034335/174405316454348209659.

Specifically B16=H16/rho13=Gamma13-16, and the other three values are the
parent's complete linear costs H divided by its actual survival lower
bound rho13. Their probability law and normalization are unchanged.

Let P be the set of all joint probability laws of integer Y>=1 and
real Z>=1 for which, for EACH X in{Y,Z},

    E h16(X)<=B16,    E phi17(X)<=B17,
    E phi19(X)<=B19,  E g5(X)<=B5,    E X³<=M.         (JM3)

Then the exact optimum is

    sup_(mu in P) E_mu G(Y,Z)
      =50/11+(25/64)*B16+B17
      =2223498946943730400848934820152878371
         /10795621729005211913709172662384000
      =205.96302860165332... .                       (JM4)

The same value holds if Y is allowed to be real. The upper proof is
valid for all real y,z>=1, and the attaining witness is already integral.

## A dual inequality valid on the entire unbounded domain

For all real y,z>=1,

    G(y,z)<=50/11+(25/64)*h16(y)+phi17(z).            (JM5)

Define

    H(z)=50/11+phi17(z)-(403/8)*(z-8)+-(25/8)*kappa(z).

Its nonnegativity follows from exact formulas:

    1<=z<=5: H(z)=50*(5-z)/(11*(16-z));
    k<=z<=k+1, k=5,6,7, t=z-k:
        H(z)=50*t*(1-t)/((16-k)*(15-k)*(16-k-t));
    z>=8: H(z)=0.                                   (JM6)

All denominators in the middle range are positive. The formulas can
also be obtained from convexity of16/(16-z) and the matching affine
secants at5,6,7,8. The full tail identity uses

    phi17(8)=75/44,
    sum of phi17 hinge coefficients=403/8,
    50/11+75/44=25/4.

If y<=4, the difference between the right and left sides of(JM5) is

    H(z)+(25/128)*kappa(z)*(16-y²)>=0.

If y>=4, that difference is

    H(z)+(25/128)*(2-kappa(z))*(y²-16)>=0,

since kappa(z)<=2. This proves(JM5) for the whole real domain, including
both infinite tails. Its expectation under(JM3) proves the upper half
of(JM4). No finite grid or unproved tail cutoff enters the argument.

## An exact eight-point attaining law

The support is

    (Y,Z)=(4,5),(4,6),(9,14),(12,9),
          (19,12),(35,19),(49,52),(87,8).

Write q_i for these eight probabilities in the listed order. They are
the unique rational solution of the following eight linear equations:

    sum_i q_i=1,
    E h16(Y)=B16,  E phi19(Y)=B19,  E Y³=M,
    E h16(Z)=B16,  E phi17(Z)=B17,
    E phi19(Z)=B19, E g5(Z)=B5.                      (JM7)

The [exact certificate](../../certificates/moment_obstructions/row17.json)
contains all eight rational probabilities and all ten rational moment
values. Its verifier solves(JM7) with rational Gaussian elimination,
checks that every probability is strictly positive, and checks every
inequality in(JM3). The remaining three slacks are

    B17-E phi17(Y)=0.02352812027455891...,
    B5-E g5(Y)=0.41917581773196877...,
    M-E Z³=644.160012986642... .

These decimals describe exact positive rationals in the certificate.
Each support point is an equality point of(JM5). The active Y-h16 and
Z-phi17 caps therefore give equality after expectation. This proves
attainment and the lower half of(JM4), including feasibility of P.

## Meaning and verification scope

Keeping the two observables correlated, keeping their complete four
scalar caps, and adding this cubic cap to both of them does not lower
the present row17 bound. Improving that bound requires information
which excludes the displayed abstract joint law: for example a sharper
valid marginal restriction, or a restriction coupling the actual
forbidden layout to original test intersections. This calculation does
not say that every stronger moment bound is ineffective.

The passage from actual rows to(JM1) is an upper comparison. The exact
abstract maximizer is not asserted to attain an actual F17 value. In
particular this obstruction neither constructs an odd covering nor
settles unrestricted Erdos#7. It does not combine the17 and19 original
tests or change the physical input law required at19.

Reproduction uses only the Python standard library:

    python3 docs/reports/erdos7-odd-covering/frontier/moments-survival/verify_joint_moment_obstruction.py --check

The verifier binds the complete logical AP(4,5) parent certificate,
its verifier, and its recorded direct mathematical source hashes. It checks
all exact moment inequalities, the complete-domain dual identities,
and primal-dual equality, then compares the full reconstructed result
with the stored certificate. The verification is ordinary mathematics
and exact rational arithmetic, not a Lean-kernel proof. Moment
optimization and conditional Jensen are existing methods; the result
here is the sharp obstruction for these specific current caps.
