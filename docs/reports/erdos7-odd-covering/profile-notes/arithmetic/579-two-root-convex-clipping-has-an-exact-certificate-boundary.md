# The two-root convex clipping certificate has an exact boundary

The two legal ternary roots may be weighted and clipped independently,
while every query is still answered by one actual joint survivor law.
The source within each root remains its actual conditional Haar law;
only the two root weights and the two thresholds are varied.
For the two-class pure comb, the best certificate obtained from the
current B,K profile and the exact maximum of the two weighted hinges is

    r*=7548357118614250413488684/625732567524997445251785
      =12.063231978592357... >566/49.                       (RC1)

This optimizes all root weights and both real clipping thresholds, not
just a grid or their common-threshold subfamily. It is an obstruction to
the specified upper-bound certificate. It is not a lower bound on an
actual attainable query norm, and the auxiliary dual witness below is
not asserted to arise from an actual original family.

The source and conditional construction reuse [Report572](572-compatible-fibres-lift-one-six-prime-query-law.md) and [Report574](574-four-level-query-hinge-removes-pointwise-overlap.md). The
pure-prefix query geometry and the need to preserve the entire tail are
the same ones used in [Report578](578-pure-prime-density-query-tradeoff-and-scalar-clip-boundary.md) and Chapter03 HC4--HC7. The additional
calculation here optimizes a different, genuinely root-dependent law
construction. These are ordinary proofs with exact rational diagnostics,
not a new Lean result.

## 1. One actual law with two independently clipped roots

Fix the pure originals 1 mod 3 and 3 mod 9, with no additional pure 3
originals. The ternary survivor T has two roots:

    A={t: t=0 mod3 and t!=3 mod9},
    B={t: t=2 mod3}.

Let u_A and u_B be Haar conditioned on these sets. Fix one actual
finite family on P={3,5,7,11,13,17,19}, with pairwise distinct numerical
moduli and all original phases fixed. Suppose that each nonunit Q
cofactor, Q=P without 3, has at most two projected phases among its
originals 3^e d at e=0,1,2,3. Select those phases and retain the SAME
PA source nu on the selected Q-survivor V. Its bounds are

    R_Q(nu)<=B0=432040125182653876501/86355045355449035400,
    E_nu(L-t)_+<=K_t, t>=0,                              (RC2)

for every partial single-phase Q query layout L. Only the current K
values between 0 and 7 will be needed for the lower certificate; at
larger thresholds any nonnegative valid bound can be used.

For the complete original survivor indicator chi define

    c_A(x)=integral chi(t,x)du_A(t),
    c_B(x)=integral chi(t,x)du_B(t).

All Q-bearing originals with e<=3 vanish on V; the two pure 3 originals
vanish on A and B. For e>=4 let L_(A,e) and L_(B,e)
count those actual original Q incidences whose ternary phase belongs
to A and B, respectively. Phases outside T cause no surviving-fibre
deletion. Distinct full numerical moduli imply that
L_(A,e)+L_(B,e) is a partial single-phase Q query layout. Set

    Y_A=sum_(e>=4)2*3^(3-e)L_(A,e),
    Y_B=sum_(e>=4)2*3^(3-e)L_(B,e), Y=Y_A+Y_B.

The coefficients sum to 1; absent heights contribute zero. Conditional
ternary caps give

    1-c_A<=Y_A/12, 1-c_B<=Y_B/18,
    E_nu(Y-t)_+<=K_t.                                   (RC3)

The last assertion is convexity applied under the SAME nu to the
combined layout at each height. No independence between Y_A and Y_B
is assumed.

Choose 0<=w<=1 and0<kappa_A,kappa_B<=1 once, before any query. Define

    eta_A=w u_A nu chi/max(c_A,kappa_A),
    eta_B=(1-w)u_B nu chi/max(c_B,kappa_B),
    eta=eta_A+eta_B, s=eta(1), mu=eta/s.                  (RC4)

When s>0 this is one actual supported joint law. Its root conditionals
are not in general those of a fixed mixture u=w u_A+(1-w)u_B restricted
to each whole fibre: different roots have different normalizers.
Thus RC4 is permitted as a joint-law construction, but is not relabelled
as a member of the previous fixed-u fibre-uniform class.

## 2. Complete query cost and the exact scalar convex majorant

Write

    t_A=12(1-kappa_A), t_B=18(1-kappa_B),
    lambda_A=w/(12-t_A), lambda_B=(1-w)/(18-t_B),
    x=max(lambda_A,lambda_B), M=max(w,1-w).

The Q marginal of eta is at most nu. At ternary depth 1 each root's
Q marginal is at most its original weight times nu. At every depth
a>=2 the conditional caps are (9/2)3^(-a) for u_A and 3*3^(-a)
for u_B. Summing ALL ternary depths and ALL Q query labels therefore
gives

    R_P(eta)<=N:=B0+(1+B0)(M+9x).                       (RC5)

Here the depth 1 term is M and the sum over depths a>=2 is

    (1/2)max{3w/(2kappa_A),(1-w)/kappa_B}=9x.

Thus shallow queries do not incur the global 1/kappa penalty from the
old single-clip bound. The unit Q query occurs once in 1+B0.

The exact mass deficit obeys

    1-s<=E_nu[lambda_A(Y_A-t_A)_+
                  +lambda_B(Y_B-t_B)_+].                (RC6)

For every fixed Y>=0, the maximum of the bracket over all nonnegative
splits Y_A+Y_B=Y occurs at an endpoint of the interval. Consequently
the SHARP scalar majorant after discarding the root allocation is

    h(Y)=max{lambda_A(Y-t_A)_+,lambda_B(Y-t_B)_+}.          (RC7)

This is stronger than replacing both coefficients by their maximum
and both thresholds by their minimum. RC1 concerns RC7 itself.

Every such h has an exact representation by one or two hinges with
nonnegative coefficients. Order the thresholds t_l<=t_h, with slopes
lambda_l and lambda_h. If lambda_l>=lambda_h, then

    h(z)=lambda_l(z-t_l)_+.

Otherwise set

    v=(lambda_h t_h-lambda_l t_l)/(lambda_h-lambda_l)>=t_h;
    h(z)=lambda_l(z-t_l)_+
              +(lambda_h-lambda_l)(z-v)_+.              (RC8)

The zero-coefficient and equal-threshold cases follow directly. Let
L_K(h) denote the corresponding one- or two-term expression with
each (z-t)_+ replaced by K_t. Equations RC2--RC8 imply

    s>=1-L_K(h),
    R_P(mu)<=C:=N/[1-L_K(h)]                            (RC9)

whenever the denominator is positive. This is the precise certificate
optimized below.

## 3. A global dual, using only the existing low-threshold profile

Let

    K3=12019840537595758779003/5715264751774801992890,
    r=(24+48B0)/(24-K3)=r*,
    q=2-(1+3B0)/r,
    y=3+K3/q,
    alpha=[1+(1+B0)/(r q)]/2.                            (RC10)

Exact rational checks give

    0<q<1, q=0.6728927473230335...,
    6<y<7<12, y=6.125478425834316...,
    0<alpha<1, alpha=0.8697717322569035...,
    q y=4.121790006627624... < B0.                       (RC11)

The existing K_t envelope satisfies the global supporting inequality

    K_t>=q(y-t)_+, for every t>=0.                      (RC12)

For 0<=t<=7, verify it at the integer endpoints and at y. The existing
corner (1/2,2/3) dominates every other corner at those integer endpoints,
so K is its affine interpolation on each unit interval. The comparison
hinge has only the one additional break y. All differences are
nonnegative, with equality at t=3. For t>=y the right side is zero,
so nonnegativity of K proves the remainder of the unbounded range.
No uncomputed positive K tail is dropped from an upper estimate.

For any nonnegative hinge representation of h, RC12 implies

    L_K(h)>=q h(y).                                     (RC13)

Equivalently, the two-point probability with mass q at y and 1-q at 0
is a dual witness for these scalar moment bounds. Its first moment
also satisfies the available bound E Y<=B0 by RC11. It is an auxiliary
witness only; no actual-family realization or actual-source optimality
is asserted.

Because y<12<18 and lambda_A,lambda_B<=x, the two affine branches give

    h(y)>=w-(12-y)x,
    h(y)>=1-w-(18-y)x.                                 (RC14)

Use the convex combination with weights alpha and 1-alpha, together
with M>=1-w. Then

    N-r[1-L_K(h)]
      >= B0-r+(1+B0)(1-w+9x)
         +r q[alpha(w-(12-y)x)
                  +(1-alpha)(1-w-(18-y)x)]
      =0.                                               (RC15)

The cancellation is exact:

    r q=2r-1-3B0,
    r q(15-y)=12(1+B0),
    (2alpha-1)r q=1+B0.

The second identity is just r(24-K3)=24+48B0. These identities cancel
the coefficient of w, the coefficient of x, and the constant in RC15.
Hence every admissible certificate in RC9 satisfies C>=r, for every
w and every pair of real thresholds. The proof never assumes a bound
on their crossing v, and never replaces them by one threshold.

## 4. Attainment and exact meaning of the obstruction

Choose

    w=3/8, t_A=t_B=3,
    kappa_A=3/4, kappa_B=5/6,
    lambda_A=lambda_B=1/24.

Then h(z)=(z-3)_+/24, M=5/8,9x=3/8, N=1+2B0, and

    L_K(h)=K3/24,
    C=(1+2B0)/(1-K3/24)=r*.                            (RC16)

This proves the exact global minimum RC1. It excludes a particular
possible repair of the height-three argument: allowing arbitrary root
weights and independent root clipping, retaining the uninflated
depth 1 query bound, and using the COMPLETE scalar convex majorant
of the two root losses still does not cross the existing gate.

The obstruction is to this combination of query and mass-loss bounds.
It does not exclude tighter root-query debits under the same eta,
information about the actual pair (Y_A,Y_B), clipping on finer prefixes,
other within-root source laws, a changed Q source, or a smaller valid
total-load moment profile. In particular it neither proves nor refutes
the existence of a good actual joint survivor law for this class.

## 5. An actual finite normalization control

Use the pure originals above and, for p=5,7,11,13,17, one original
modulo 81p with Q phase 0 mod p and respective ternary phases

    0,6,9,15,18 mod81.

Each ternary phase belongs to A and they are distinct. All full
numerical moduli are distinct. There are no shallow mixed phases, so
the selected Q source is Haar. For a Q point activating n of these
five prime conditions,

    c_A=1-n/18, c_B=1,
    Y_A=2n/3, Y_B=0.

At RC16's parameters the only clipping loss occurs when all five
conditions hold. The actual raw mass loss is

    1-s=1/[72*(5*7*11*13*17)]=1/6126120>0.

It equals the actual maximum-hinge expectation in this control. Thus
the joint-law normalization and a nonzero clipping loss can be checked
on actual fixed congruences. This example is not asserted to attain the
uniform B0 or K3, or to be a previously untreated noncoverage family.

## Verification

The [exact producer](../../frontier/cover-geometry/two_root_convex_clipping.py)
checks RC10--RC16, the supporting inequality, hinge decompositions on
252 rational parameter controls, and the actual finite family above.
The 34 named checks pass with exit 0; [exact data](../../frontier/cover-geometry/two_root_convex_clipping.json)
include the hash of the retained moment input. The ordinary dual proof
establishes the universal optimization; the finite controls do not
substitute for its continuous quantifiers.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_root_convex_clipping.py

No new Lean verification or external novelty claim is made.
