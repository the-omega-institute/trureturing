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

The same exact minimum remains valid after retaining the individual
root-loss caps and allowing any loss estimate valid under just the
same scalar moment constraints. Define

    F(Y)=max_(a,b>=0,a+b=Y)
           [min{w,lambda_A(a-t_A)_+}
              +min{1-w,lambda_B(b-t_B)_+}].

This is the sharp bounded allocation envelope, with F<=h and F<=1.
At the dual atom y<12<18, every allocation has a<=y<12 and b<=y<18.
Neither cap can truncate its hinge, since its saturation scale is
respectively 12 or 18 (a zero root weight contributes zero). Thus
F(y)=h(y). Any bound D on E F(Y) valid for ALL probabilities with
E Y<=B0 and E(Y-t)_+<=K_t must satisfy D>=q h(y), using the same
feasible two-point law. Replacing L_K(h) by D in RC15 proves
N/(1-D)>=r whenever 1-D>0. At RC16's parameters, F<=h makes
D=K3/24 valid, and the dual forces equality. Hence r is also the
exact global minimum for this larger class of scalar-moment loss
certificates with the SAME raw numerator N. This does not identify
the optimal loss estimate for every individual parameter choice.

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

## 6. Refining all prefixes through depth four does not repair the scalar certificate

The same dual also gives a boundary for h=2,3,4, with the same pure originals 1 mod 3 and 3 mod 9, the same Q law nu and its B,K_t bounds. In this section B denotes the scalar bound B0 in RC2, not the ternary root named B.

Fix the same finite actual original family as above: the only pure 3 originals are 1 mod 3 and 3 mod 9; numerical moduli are pairwise distinct; each nonunit Q cofactor has at most two projected phases through ternary exponent 3, and those phases are selected. The same actual PA law nu is supported on their Q survivor V. All weights and clips below are chosen once, before any query.

At a chosen h, split the ternary survivor into all 5*3^(h-2) live depth-h cells. Within each cell use conditional Haar. Assign arbitrary nonnegative cell weights w_i summing to 1 and independent clips 0<kappa_i<=1. Let

    s_h=2*3^(3-h), t_i=s_h(1-kappa_i),
    lambda_i=w_i/(s_h-t_i), x=max_i lambda_i,
    M_a=max_(depth-a prefix) sum_(cells i in prefix) w_i,
    m=M_h, z=M_2.

For each live residue i mod3^h, write C_i=[i]_(3^h), let u_i be normalized Haar within C_i, and define

    c_i(x)=integral chi(t,x)du_i(t),
    eta_i(dt,dx)=w_i chi(t,x)u_i(dt)nu(dx)/max(c_i(x),kappa_i),
    eta=sum_i eta_i, mu=eta/eta(1) when eta(1)>0.

This is a single actual joint law, normalized once. It need not preserve a previously prescribed fixed-u conditional or the conditional Haar law within an entire root.

For an actual original modulo 3^e d with e>=4 and d>1, denote its fixed ternary phase by a_(e,d) and its fixed Q phase by b_(e,d). Define the ACTUAL cell layout

    L_(i,e)(x)=sum_(originals3^e d with a_(e,d)=i mod3^h)
                    1_[b_(e,d) mod d](x),
    Y_i=sum_(e>=4)2*3^(3-e)L_(i,e).

The finite original inventory gives a finite sum of nonzero layouts; the bounding geometric coefficients still include every possible height. Originals whose ternary phase is outside T contribute to none of these layouts and cannot delete a point of any u_i.

For h<=4, every residual original at e>=4 whose ternary phase lies in T belongs to exactly one live depth-h cell. Its full numerical label remains unchanged. Thus the cell loads Y_i sum to the same convex mixture Y of partial single-phase layouts under ONE nu, with E(Y-t)_+<=K_t. Conditional cylinder caps give 1-c_i<=Y_i/s_h. The sum of the untruncated hinges is convex on each allocation simplex, so its maximum occurs at a vertex. The resulting sharp majorant of those hinges is

    H(Y)=max_i lambda_i(Y-t_i)_+.

The same actual eta construction and all-depth query accounting give the raw numerator

    N_h=B+(1+B)[sum_(a=1)^h M_a+(s_h/2)x].

The first sum uses the uninflated prefix-weight bounds. The second term is the ENTIRE deeper query tail: conditional Haar inside a depth-h cell has sum of deeper maxima 1/2. Pure-Q labels exclude the unit, and positive ternary depths include it once through 1+B.

Reuse q,y,r from RC10. Its probability dual satisfies every K_t constraint, qy<B, and y>6>=s_h. Any scalar-moment upper bound C_loss for the expectation of this UNTRUNCATED majorant H must therefore satisfy

    C_loss>=q H(y)>=qy*m/s_h.

This remains true if the moment relaxation also keeps total probability 1 and E Y<=B. It makes no assertion that the dual is an actual arithmetic source.

Put k=3^(h-2), so s_h=6/k. A maximal depth 2 prefix splits into 3^(a-2) depth-a prefixes. Hence

    M_a>=z/3^(a-2), 2<=a<=h,
    sum_(a=1)^h M_a+m/2>=M_1+(3/2)z,
    m/s_h>=z/6.

Also x>=m/s_h. Root A has only two allowed depth 2 cells, giving M_1>=1-2z, while the five allowed depth 2 cells give z>=1/5. Consequently

    N_h-r(1-C_loss)
      >=B-r+(1+B)[M_1+(3/2)z]+rqy*z/6
      >=(5z-1)(r-1-2B)
      >=0.

The last equality uses rqy=30r-27-57B; its last factor is positive. Therefore every positive-denominator certificate from these raw-query and UNTRUNCATED scalar-moment bounds is at least

    r=7548357118614250413488684/625732567524997445251785
      =12.063231978592357... >566/49.

This covers all weights and independent clips at each of the three depths. It does not determine their individual exact minima or order the best ACTUAL laws. The result is that this particular scalar relaxation discards the cell-allocation information immediately after subdivision, so the existing dual continues to obstruct an improved certificate.

For h>4, an actual residual depth 4 cylinder can intersect several depth-h cells. The displayed one-original/one-cell partition of Y is then unavailable. Section 7 replaces that partition by exact Haar-overlap allocation, extending the bounded-loss obstruction to arbitrary finite prefix cuts. Retaining actual cell allocation, same-law query-loss debits or stronger source constraints remains outside these scalar certificates.

### Individual cell-loss caps still leave a strict certificate gap

The actual raw loss from cell i is also at most w_i. Account for this by the SHARP bounded allocation envelope

    F_h(Y)=sup_{y_i>=0, sum_i y_i=Y}
               sum_i min{w_i,lambda_i(y_i-t_i)_+}.

This retains both the individual limits and the total loss bound F_h<=1. The earlier numerical barrier r concerns the untruncated majorant H and is not asserted for F_h.

Nevertheless the SAME probability dual gives a strict lower barrier for F_h's scalar-moment certificate. A depth 2 prefix with maximum weight z has exactly k=3^(h-2) descendant cells. Give each of those cells allocation y_i=s_h=6/k. Their total allocation is 6, and each one's capped loss is exactly

    min{w_i,lambda_i(s_h-t_i)}=w_i.

Because the dual atom y is strictly above 6, distribute the remaining y-6 to any cell. Every loss summand is nondecreasing, so this allocation proves

    F_h(y)>=z.

This is a feasible allocation in the scalar relaxation, not a claim that these cell loads come from the actual original family. Its use is legitimate precisely because the certificate being tested keeps only the same scalar Y-moment constraints. The feasible probability q delta_y+(1-q)delta_0 therefore forces ANY valid upper bound D for E F_h(Y), based only on those constraints, to satisfy D>=qz. It also respects E Y<=B and F_h<=1.

The earlier full-query prefix inequalities give

    N_h>=1+2B-(1+B)z/2, z>=1/5.

Since 0<q<1 and z<=1, the relaxed denominator 1-qz is positive. Whenever the actual certified denominator 1-D is positive,

    N_h/(1-D)
      >=[1+2B-(1+B)z/2]/(1-qz).

The last ratio increases with z because

    q(1+2B)-(1+B)/2
      =17390107284801685724248961343831194148679463
        /3948335574863297592288635491589985266448000>0.

Its value at z=1/5 is

    r_sat=[B+(9/10)(1+B)]/(1-q/5)
      =33914609213286804860799851870837955027791000698
        /2820576058673273244795335584651143056943842655
      =12.024000951507533... >566/49.

Thus for h=2,3,4 even the sharp allocation envelope with all individual cell-loss caps and total loss<=1 cannot make these retained raw-query and scalar-moment certificates pass the gate. This is a LOWER BARRIER, not the exact optimum of the capped problem. It is not a lower bound on actual attainable query norms. Same-law query debits, actual allocation constraints or a stronger source profile remain outside this conclusion.

## 7. Arbitrary fixed finite prefix cuts retain the bounded-loss obstruction

Keep precisely the actual-family and same-source assumptions of section 1.
Let C_1,...,C_n be any finite prefix-free partition of the SAME ternary
survivor T into complete cylinders. Write C_i=[r_i]_(3^d_i) and require
d_i>=2. The depths may differ and have no fixed upper bound. The cut,
weights w_i>=0 with sum_i w_i=1, and clips 0<kappa_i<=1 are all fixed
before sampling the Q coordinate or choosing queries. They may depend
on the given original family; a Q-coordinate-dependent cut is not
included. Let u_i be conditional Haar on C_i and set

    s_i=54*3^(-d_i), t_i=s_i(1-kappa_i),
    lambda_i=w_i/(s_i-t_i), v=sum_i w_i u_i.

Use the same actual c_i and eta_i as in section 6, followed by one
normalization of eta=sum_i eta_i. Prefix gluing and the finite Kraft
identity are already used in [Report410](410-an-initial-ternary-budget-allows-asynchronous-stopping.md).
The additional issue here is the allocation of originals that cross
several leaves and the resulting scalar-certificate obstruction.

### Exact allocation of every original height

For each residual original modulo 3^e d with e>=4, d>1, let A_(e,d)
be its fixed ternary cylinder and B_(e,d) its fixed Q cylinder. Define

    alpha_(i;e,d)=H3(C_i intersect A_(e,d))/H3(A_(e,d)),
    Y_i(x)=sum_(actual residual originals)
                2*3^(3-e)*alpha_(i;e,d)*1_B(e,d)(x).

If A_(e,d) lies in T, its alpha values sum to one. If it is outside T,
they are all zero. These are the only possibilities because T is a
union of depth 2 cylinders. No original numerical label or phase is
changed. At each e the surviving originals still supply a partial
single-phase Q layout. Consequently sum_i Y_i is the same Y as before,
under the same nu, with E Y<=B0 and E(Y-t)_+<=K_t.

Since H3(C_i)=3^(-d_i), there is the exact identity

    [2*3^(3-e)*alpha_(i;e,d)]/s_i
       =H3(C_i intersect A_(e,d))/H3(C_i)
       =u_i(A_(e,d)).

Thus the actual union bound gives 1-c_i<=Y_i/s_i for every leaf,
including e<d_i. An original that contains many leaves is distributed
over them; its load is not counted once in each leaf.

The raw loss is therefore bounded by the allocation envelope

    F_cut(Y)=sup_(y_i>=0,sum_i y_i=Y)
                 sum_i min{w_i,lambda_i(y_i-t_i)_+}.

The supremum here discards the actual relations among the Y_i. Those
relations are not asserted to be realizable by an arbitrary allocation.

### The full query numerator, with individual query caps retained

For a ternary cylinder J of positive depth a put

    G(J)=sum_i w_i min{1,u_i(J)/kappa_i},
    A_cap=sum_(a>=1) max_(J of depth a) G(J).

For every Q query D, both the whole-leaf marginal bound and the
conditional Haar cap hold under the SAME eta_i. Hence

    eta_i(J x D)<=w_i min{1,u_i(J)/kappa_i} nu(D),
    R_P(eta)<=N_cut:=B0+(1+B0)A_cap.

The pure-Q marginal is at most nu; positive ternary depths include the
Q-unit once. This is a finite number with its entire infinite query
tail: beyond all leaf depths and the finite saturation thresholds,
every summand decays geometrically as 3^(-a). The minimum with one
can improve the earlier untruncated query caps and is retained here.

For each J, min{1,u_i(J)/kappa_i}>=u_i(J), so A_cap>=R3(v).
Let z=max_(J of depth 2) v(J), and let M1=max_(J of depth 1) v(J).
The five live depth 2 cylinders give z>=1/5. The root with two such
children has mass at most 2z, so M1>=1-2z. A maximizing depth 2
cylinder has 3^(a-2) descendants at depth a, and at least one has
v-mass at least z/3^(a-2). Summing every depth, including the full tail, gives

    A_cap>=R3(v)>=M1+(3/2)z>=1-z/2,
    N_cut>=1+2B0-(1+B0)z/2.

### A depth-independent saturation budget

Choose a depth 2 cylinder J_* with mass z. Its leaves form a complete
partition, so the same-source Haar identity gives

    sum_(C_i subset J_*) s_i
      =54 sum_(C_i subset J_*)3^(-d_i)=54/9=6.

At the old dual atom y>6, allocate y_i=s_i to these leaves and zero
elsewhere, then add y-6 to any one of the selected leaves. Each selected
loss already equals w_i and cannot decrease. Therefore F_cut(y)>=z.
The old auxiliary probability q delta_y+(1-q)delta_0 satisfies every
retained scalar moment constraint. Any D uniformly bounding E F_cut(Y)
from ONLY those constraints must satisfy D>=qz. For 1-D>0,

    N_cut/(1-D)
      >=[1+2B0-(1+B0)z/2]/(1-qz)
      >=r_sat=12.024000951507533... >566/49.

The last monotonicity and exact constant are those of section 6.
Thus arbitrary fixed finite prefix refinement, unequal leaf depths,
independent weights and clips, and individual query and loss caps
do not remove this scalar-certificate gap. This includes uniform
depth h for EVERY h>=2, not just h<=4. It is still only a lower
barrier for the specified certificates, not their exact optimum or
an actual-law lower bound. It does not cover changing nu, non-Haar
within-leaf sources, cuts depending on the sampled Q coordinate,
actual allocation constraints, or joint query-loss debits.

## Verification

The [exact producer](../../frontier/cover-geometry/two_root_convex_clipping.py)
checks RC10--RC16, the supporting inequality, hinge decompositions on
252 rational parameter controls, and the actual finite family above.
The 79 named checks pass with exit 0, including bounded-root controls at the dual atom, 3,159 actual ternary phase-partition controls, the bounded-loss prefix allocations, and 4,212 further original-cylinder overlap controls on uniform and unequal-depth cuts. The latter also check exact saturation budgets and the entire capped query tail; [exact data](../../frontier/cover-geometry/two_root_convex_clipping.json)
include the hash of the retained moment input. The ordinary dual proof
establishes the universal optimization; the finite controls do not
substitute for its continuous quantifiers.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_root_convex_clipping.py

No new Lean verification or external novelty claim is made.
