# Normalized joint hinges close the shallow two-phase slice

Every finite family of distinct odd nonunit numerical moduli supported
on `{3,5,7,11,13,17,19,23,29}` has positive survivor density under the
following two additional hypotheses:

* Its pure3 originals are exactly `1 mod3` and `3 mod9`.
* For each nonunit cofactor supported on `Q={5,7,11,13,17,19}`, the
  projections of its P-supported originals through ternary exponents
  `e=0,1,2,3`, where `P=Q union{3}`, fit in at most two fixed phases.

All later original heights and phases are arbitrary and globally fixed.
Originals touching23 or29 have no additional phase restriction. Actual
ternary surviving fibres may vanish. In particular, no extra small-tail,
pointwise reserve, low-query or loss-incidence hypothesis is required.
The uniform lower bound proved here is

    H(full survivor)>=5300723428170265775843
                       /5947345771483164278630400000
                     =0.000000891275475118...>0.           (NJ1)

The improvement propagates four uniform query-hinge bounds on each
normalized actual prefix. It combines row loss and cap slack before
using those bounds. This closes the high-query gap within the above
slice left in [Report587](587-actual-tail-obstruction-and-source-query-repair.md)
and [Report588](588-query-prefix-incidence-strengthens-actual-source-debits.md).
Sections8--10 further replace the global shallow restriction by finite
cofactor windows and allow arbitrary additional pure tails from a
specified depth. Unrestricted low ternary phases, arbitrary pure3
geometry and additional support primes remain outside the conclusions.
These are ordinary mathematical proofs with exact rational arithmetic,
not new Lean results or a resolution of unrestricted Erdős #7.

## 1. One actual construction and a uniform prefix contract

Start with any finite selected family having at most two fixed classes
at each nonunit Q-supported numerical modulus. Use the actual pure5/7
restrictions and mixed5/7 deletion of
[Report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md).
Process the remaining coordinates in this declared order:

| q | threshold t | cap C=(q-1)/(q-1-2t) | a=2C/(q-1) |
|---:|---:|---:|---:|
|11|2|5/3|1/3|
|13|2|3/2|1/4|
|19|4|9/5|1/5|
|17|4|2|1/4|

As in [Report560](560-reordered-pa-pure-union-savings.md), assign each
selected original to the last prime in its support under this order.
The full numerical label and residue are unchanged. Every original is
imposed once, with its other coordinates already available. The order
generally gives a different actual law from Report569's increasing
order. No bound or debit specific to that old law is imported here.

The actual row is `k(h,z)=kappa(h) 1_G(h)(z)`, with

    g(h)=H_q(G(h)), kappa=min(C,1/g),
    s(h)=min(1,Cg), ell(h)=1-s(h).

At g=0 use the zero row and kappa=C. These kernels define raw prefixes
lambda. Writing `nu=lambda/lambda(1)` only normalizes their analysis;
it does not replace any kernel or choose a different source for each
query. The next normalized prefix is `nu'=nu k/(1-d)`, where `d=E_nu ell`.

For every fixed one-phase nonunit query layout L on the old coordinates,
maintain simultaneously

    E_nu(L-j)_+<=Theta_j,  j=0,1,2,3.                    (NJ2)

Finite partial layouts and fixed complete all-height layouts are
included. Different queries need not maximize simultaneously. The
contract holds for each of them on the SAME nu. In particular, it
applies both to the original slots used to bound loss and to the
layers of any new query.

For real r, extend the envelope by

    Theta(r)=Theta_0-r,                       r<=0,
    Theta(r)=(j+1-r)Theta_j+(r-j)Theta_(j+1),   j<=r<=j+1.

For integer-valued L, interpolation is exact at the level of hinge
functions. Interpolating their uniform upper bounds remains an upper
bound. We use only r<=3. The inequalities `L<=j+(L-j)_+` also permit

    Theta_0 <- min_(0<=j<=3)(j+Theta_j).                  (NJ3)

NJ3 improves the mean contract without changing the law or the other
hinge bounds.

## 2. The actual5/7 anchor, including its complete tails

Let the pure-survivor masses be `x in[1/2,1]`, `y in[2/3,1]`.
The actual mixed deletion is at most1/12, so the raw anchor mass is
at least `xy-1/12>=1/4`. Its raw convex comparison uses independent
auxiliary coordinates with masses x,y and, for coordinate p of mass m,

    pi_p(1)=m-1/p,
    pi_p(n)=(p-1)/p^n, n>=2,
    integral n dpi_p=m+1/(p-1).

If F_h(x,y) is the hinge at h of their product count, including the
unit, then

    E_nu(L-(h-1))_+<=F_h(x,y)/(xy-1/12).                 (NJ4)

The worst corner for every h is x=1/2,y=2/3. Indeed decreasing either
mass increases the normalized coordinate tails and hence
F_h(x,y)/(xy); it also decreases the positive denominator factor
`1-1/(12xy)`. This proves the assertion throughout the rectangle,
not just at its four corners. For h=1,2,3,4, NJ4 gives

    (Theta_0,Theta_1,Theta_2,Theta_3)
      =(7/6,97/210,1759/7350,26953/257250).               (NJ5)

For any positive integer h, the identity

    integral(N-h)_+=integral N-h*mass
                      +sum_(n<h)(h-n)mass{N=n}

needs only finitely many low atoms and the COMPLETE first moment.
No original or query height has been truncated.

## 3. A single normalized row transports the hinge contract

At each positive current exponent e, split the selected originals into
two fixed slots, with at most one phase per old numerical cofactor in
each slot. Complete the slots to old queries including the unit. The
actual union bound, with `u=(q-1)(1-g)/2`, is

    u<=sum_(e>=1,j=1,2) beta_(e,j)(1+L_(e,j)),
    beta_(e,j)=(q-1)/(2q^e), sum beta=1.

Absent original layers may be completed by arbitrary fixed queries;
their introduction only enlarges this upper bound. Since
`ell=a(u-t)_+`, monotonicity and Jensen give

    d<=a Theta_(t-1)=:d_upper.                           (NJ6)

For the query comparison, completing an actual row to probability
with density at most C gives the independent auxiliary count

    Pr(N=1)=1-C/q,
    Pr(N=n)=C(q-1)/q^n, n>=2.

After the usual conditional nested comparison, on N=n the full query
count has the form `sum_(e=0)^(n-1)(1+L_e)`. The L_e are fixed old
queries. Convexity of the hinge therefore bounds its integrated
payoff at integer h>=1 by

    Psi_h=E_N[N Theta(h/N-1)].                           (NJ7)

For n<h the sum is finite. For n>=h its integrand is
`n(1+Theta_0)-h`, whose expectation uses the exact geometric tail.
For h>=2 that tail has mass `C/q^(h-1)` and first moment
`[C/q^(h-1)] [h+1/(q-1)]`. For h=1 use total mass one and mean
`1+C/(q-1)`.

The always-present unit in every exponent layer also supplies a
cap-slack credit. With phi(v)=(v-h)_+, each increment in the nested
envelope is at least `phi(e+1)-phi(e)`. Thus the full slope is at least

    eta_h=sum_(e>=h)q^(-e)=1/[q^(h-1)(q-1)].

If H_h is the actual raw hinge after applying the current row to nu,
then

    H_h<=Psi_h-eta_h E_nu(C-kappa).                      (NJ8)

When kappa<C the row already has mass one, so this is a cap comparison.
When kappa=C, the cap credit is zero and completion only adds
nonnegative hinge payoff. Consequently NJ8 holds for both cases
within this one construction; no incompatible completions are added.

For clarity, prove the conditional comparison first on complete finite
exponent boxes, retain their unit layers and cap slopes, and let the
boxes increase. Full geometric first moments dominate the envelopes;
the cap slopes converge to eta_h. A finite partial prescribed query
is bounded by each completed box containing it. Exhausting a fixed
countable layout then gives the full contract by monotone convergence.
Bounded actual densities and finite reciprocal-modulus sums on each
finite prime set ensure integrability. No difference of two increasing
approximations is asserted to be increasing.

## 4. Loss and cap slack must be combined before substituting bounds

For lambda>=C eta_h, use the increasing convex function already
appearing in [Report569](569-complete-suffix-debits-close-the-six-prime-query-target.md)
SD8, here applied to the normalized actual prefix:

    p_lambda(u)=eta_h[(q-1)/(q-1-2u)-C], 0<=u<t,
                lambda a(u-t),                     u>=t.

The branches meet at zero, with left slope eta_h C a no larger than
the right slope lambda a. On the actual row it satisfies exactly

    p_lambda(u)=lambda ell-eta_h(C-kappa).

The union mixture from Section3 and Jensen bound its expectation by
the mixture of `E p_lambda(1+L_(e,j))`. Signed constants are harmless
here because the old prefix is a probability, not merely a dominated
subprobability.

For our t=2 or4 define, for integers n>=1,

    v_n=(q-1)/(q-1-2n)-C, n<t;  v_n=0, n>=t,
    s_n=v_(n+1)-v_n,
    corr=v_1+s_1 Theta_0
                  +sum_(j=1)^(t-1)(s_(j+1)-s_j)Theta_j.

For integer l>=0 the exact discrete expansion is

    p_lambda(1+l)=eta_h v_1+eta_h s_1 l
      +sum_(j=1)^(t-1)
         [eta_h(s_(j+1)-s_j)+lambda a 1_(j=t-1)](l-j)_+.

All nonconstant coefficients are nonnegative when lambda>=C eta_h.
This follows from convexity of p_lambda, or directly from its discrete
slopes. Therefore NJ2 can be applied coefficient by coefficient, giving

    E p_lambda(u)<=eta_h corr+lambda a Theta_(t-1).

The final coefficient of corr ALONE is negative. Corr is not an upper
bound on a separate expected credit. It is used only in this combined
nonnegative-coefficient expansion. Combining with NJ8 yields

    H_h+lambda d<=Psi_h+eta_h corr+lambda d_upper.

Consequently, if d_upper<1 and

    lambda_h=(Psi_h+eta_h corr)/(1-d_upper)>=C eta_h,

then H_h<=lambda_h(1-d), and the next prefix has

    Theta'_(h-1)=lambda_h, h=1,2,3,4,                   (NJ9)

followed by NJ3. If the displayed lambda condition fails, the basic
valid bound is instead `Psi_h/(1-d_upper)`. No fallback is needed for
the sixteen row/hinge pairs in the schedule above. No old suffix or
J debit is separately subtracted; this is a new forward propagation
of the local joint penalty.

## 5. Exact propagation and one-source constants

The four retained hinges form a closed dependency set for this
schedule: t<=4, and h/N-1<=h-1<=3. The exact propagation gives the
following decimal display; the data file contains every rational:

| Prefix after q | d_upper | Theta_0 | Theta_1 | Theta_2 | Theta_3 |
|---:|---:|---:|---:|---:|---:|
|11|0.153968254|1.791275797|0.918599693|0.565548974|0.304069712|
|13|0.229649923|2.625979062|1.625979062|1.088675852|0.657610121|
|19|0.131522024|3.288817965|2.288817965|1.620533669|1.062171291|
|17|0.265542823|4.844942386|3.844942386|2.883154075|2.052246838|

Thus the ONE final actual law nu satisfies

    R_Q(nu)<=B=2907477445994511750779/600105680174967275330,
    E_nu(L-2)_+<=K2=4201907333478675099087/1457399508996349097230,
    E_nu(L-3)_+<=K3=50846040079973272728927/24775791652937934652910.
                                                               (NJ10)

The all-layout contracts imply the norm bound by selecting a maximizing
phase for each numerical modulus and exhausting the inventory. Here
K2 is not B-2; the separate hinge contract is necessary.

The raw mass and density are recomputed for this order:

    S>=alpha_new=(1/4) product_rows(1-d_upper)
       =504290487541989307/4852222295880960000>0,
    lambda_final<=9 H_Q, nu<=9 H_Q/alpha_new.             (NJ11)

All row factors are positive. The kernels vanish precisely on the
imposed constraints, so their final support is the complete selected
survivor set. Intermediate normalization is only bookkeeping for
this same raw construction.

## 6. The actual ternary lift has a strictly positive uniform margin

Apply the hypotheses stated at the beginning and select the two Q
phases containing all P-original projections through exponent3. Use
the source just constructed. Let chi be the complete survivor mask
of the P-supported originals, retaining every deeper original.
Originals touching23 or29 are imposed in the final continuation.
Following
[Report586](586-joint-clipping-retains-loss-query-correlation.md), let
u_A be normalized ternary Haar on `[0]_9 union[6]_9`, and u_B
normalized ternary Haar on `[2]_3`.
Put

    c_j(x)=integral chi(t,x)du_j(t),
    X=12(1-c_A), V=18(1-c_B), W=X+V,
    T=(W-3)_+, U=min(X,(3-V)_+), tau=E_nu T.

Original numerical distinctness gives one partial Q query L_e at each
ternary height e>=4, combining both branches, and

    W<=sum_(e>=4)54*3^(-e)L_e, sum_(e>=4)54*3^(-e)=1.

NJ10 therefore gives tau<=K3 and E W<=R, where R=R_Q(nu).
Use the SAME clipped submeasure with D=27, r=4/9,

    a_A=r c_A, a_B=min(1-r c_A,(3r/2)c_B),
    eta=chi[r u_A+(a_B/c_B)u_B]nu.

The B coefficient is zero where c_B=0. If both reserves vanish the
whole fibre has zero mass; no positive-reserve premise is inserted.
Its Q marginal is `(1-T/27)nu`, and `s=eta(1)=1-tau/27>0`.

Report586 CJ6 uses only these actual kernels and query contracts, so
it applies to the new law. The weighted second-hinge bound and
`E U<=R-tau` give, as in Report587 AT4,

    R_P(eta)<=1+2R+(3K2-3-3tau)/27.

For G=566/49, NJ10 and G>3 now yield

    Gs-R_P(eta)>=G-1-2B-[3K2-3+(G-3)K3]/27
       =10601446856340531551686/5463062059472814590966655
       =0.001940568629997143...=:delta>0.                (NJ12)

This is a bound for every actual residual configuration in the stated
slice, with no extra high-query or damage-tail condition. The normalized
supported P law eta/s has R_P<G.

For the continuation through23 and29, condition their Haar coordinates
on the complete actual pure-power survivors. Their density factors
are at most22/21 and28/27. The same-law count from Report586 leaves
raw survivor mass at least `(566s-49R_P(eta))/567`. Meanwhile
`eta<=486H_P/(27 alpha_new)`. Hence

    H(full survivor)>=49*27*alpha_new*delta/299376
                    =49*alpha_new*delta/11088,

which is NJ1. This continuation handles every original touching23
or29, including arbitrary powers and overlaps, within the declared
nine-prime support.

## 7. Evidence and remaining scope

The [exact producer](../../frontier/cover-geometry/normalized_joint_hinge_transfer.py)
and [data](../../frontier/cover-geometry/normalized_joint_hinge_transfer.json)
use only rational arithmetic for the proof constants. All624 named
checks pass. Their checks
include every lambda condition, every combined hinge coefficient,
complete geometric tails, the four anchor corners, mass and density,
and the strictly positive final margin. Finite point checks of the
discrete expansion supplement its general derivation in Section4;
they do not establish the arbitrary-family or all-height statements.

Run with Python3 standard library only:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/normalized_joint_hinge_transfer.py

The certificate uses one explicit schedule. It makes no claim of
optimality among schedules, caps or actual survivor laws. Removing
the shallow two-phase hypothesis, allowing arbitrary pure3 geometry,
and handling unrestricted prime supports remain open obligations for
this route to Erdős #7. The four-number envelope is sufficient for
these inequalities; it is not asserted to be a minimal exact boundary
state for arbitrary future operations.

## 8. Unselected shallow originals have a same-source defect budget

The two-phase assumption can be replaced by a quantitative actual-union
condition, and then restricted to a finite cofactor window. First retain
the two fixed pure3 originals and the nine-prime support above. At each
nonunit Q cofactor d, choose at most two phases A_d once, with only
finitely many A_d nonempty (for example, choose from the actual shallow
projections), and construct the corresponding law nu from Sections1--5.
The selection need not
contain every projection through ternary exponent3.

Let E be precisely the P-supported nonpure originals at exponents
e=0,1,2,3 whose Q phase is not in A_d. Let chi0 be the P-original
survivor mask after omitting only E, and chi the full P mask. With the
normalized branch laws u_A,u_B of Section6, put

    c_j^0=integral chi0 du_j, c_j=integral chi du_j,
    Z=12(c_A^0-c_A)+18(c_B^0-c_B)>=0,
    rho=E_nu Z.                                          (DF1)

This is the actual union increment after the deep originals have already
acted. Overlaps within E and with those deep originals are counted once.
Every original phase remains globally fixed, and the entire estimate
uses the same selected nu.

For a ternary cylinder C_e(t) define its weight

    w_e(t)=12u_A(C_e(t))+18u_B(C_e(t)).

The weights are30 at e=0; at e=1 they are12,0,18 on roots0,1,2.
For e>=2 they are zero inside the two pure forbidden classes and
`54*3^(-e)` otherwise. Thus w2<=6 and w3<=2. Union bounding and NJ11 give

    rho<=sum_(originals in E) w_e(t) nu([a_d]_d)
        <=(9/alpha_new) sum_(originals in E) w_e(t)/d.    (DF2)

Write W0 using c_j^0 as in Section6. On the selected source all remaining
shallow originals vanish, so the complete deep-height mixture still
gives `E W0<=R` and `E(W0-3)_+<=K3`, where R=R_Q(nu). Since W=W0+Z,

    E W<=R+rho, tau=E(W-3)_+<=K3+rho,
    E U<=R+rho-tau.                                     (DF3)

Use the same clipped law eta with D=27,r=4/9, now formed from the complete
mask chi. CJ6 and `R_Q(U nu)<=3K2+2E U` imply

    R_P(eta)<=1+2R+(3K2-3-3tau+3rho)/27,
    Gs-R_P(eta)>=delta-G rho/27.                         (DF4)

The defect is paid once in this joint loss/query inequality. In
particular it suffices that

    rho<rho_crit=27delta/G
       =15902170284510797327529/3505774518890717753386765
       =0.00453599345845622... .                        (DF5)

This also gives tau<27 and positive mass s. The density and23/29
continuation are unchanged, giving

    H(full survivor)>=(49 alpha_new/11088)
                              (delta-G rho/27)>0.       (DF6)

DF5 has not been proved for some selection in every original family.
It is a computable sufficient defect budget, not a redefinition of
the unrestricted objective.

## 9. Only a finite cofactor window needs the shallow restriction

The full reciprocal tail is

    T_Q(D)=sum_(Q-smooth d>D)1/d
          =323323/165888-sum_(Q-smooth d<=D)1/d.

For nonunit d<=D, suppose the original projections at e=0,1,2,3
fit at most two phases and select them. For every d>D, select just
the e=0 and e=1 phases if present. Numerical distinctness guarantees
at most two such phases. All other projections outside the window
are unrestricted. The only unselected shallow originals there have
e=2 or3, so

    rho<=(72/alpha_new)T_Q(D).                           (DF7)

At D=200000000 there are2654 nonunit Q-smooth cofactors, and exactly

    T_Q(D)=1730518949990034594107507351455704035339060047
             /453873446302914661773719565414768954104100000000000.

Consequently rho<=0.0026413989053468605...<rho_crit and

    delta-G rho/27 >=0.0008105370499318952...,
    H(full survivor)>=
      2810186044762638397088265938586200292012406819217
       /7548823158910076654620503811978437244659391200000000000
      =0.00000037226809869637773...>1/3000000.             (DF8)

Only actual labels3^e d inside the finite rectangle d<=2e8,e<=3
need the two-phase condition. Their presence is not required. Every
larger cofactor, every deeper nonpure original, and every original
touching23 or29 retains arbitrary fixed phases and finite heights.

Report569 SD19--SD21 already supplies the finite-window mechanism.
Its explicit window has534 nonunit cofactors up to500000 and depths
through5. The new window is larger in cofactor size but restricts
only depths through3. Neither hypothesis set contains the other.
In particular, third and fourth phases at e=4,5 on small cofactors
are allowed here. This is a new consumer of NJ10, not a new PA kernel.

Alternatively, impose the two-phase condition through e=2 globally,
and let E3 be the cofactors of the unselected e=3 originals outside
the pure forbidden classes. They form one fixed partial query L3.
The sufficient conditions

    E_nu L3<rho_crit/2=0.00226799672922811...,

or, without computing nu,

    sum_(d in E3)1/d <
      5300723428170265775843/202392839505740198515200000
      =0.00002619027155859399...                         (DF9)

follow from rho<=2E L3 and the same-law density cap. All other
allowed originals remain arbitrary. The actual union DF1 may be
smaller than these additive sufficient estimates.

## 10. Pure-tail constraints and shallow defects share the same margin

Now allow additional pure3 originals beyond the base classes1 mod3
and3 mod9. They have distinct numerical labels3^e, e>=3. Let U_pure
be their actual ternary union inside the base pure survivor, and put

    c=54 H_3(U_pure).

This is a fixed geometric quantity; pure overlaps are counted once.
Define chi0 by omitting these extra pure originals and the unselected
shallow originals E. First insert the extra pure originals, then E.
Let Z be the weighted increment caused by that second insertion and
rho=E_nu Z. Both insertions use the original fixed phases and the
same selected law nu. The extra pure increment at each Q point is
at most c: on the two supported branches the weighted Haar densities
are both54. Hence the original deep mixture Y from Section6 gives

    W<=Y+c+Z, E W<=R+c+rho,
    tau<=Theta(3-c)+rho, E U<=R+c+rho-tau.              (DF10)

The Theta in DF10 is the final all-layout envelope from NJ2 with its
integer interpolation. Jensen applies first to the fixed deep-height
mixture Y; the 1-Lipschitz hinge then pays Z. It does not assume that
pure damage, shallow damage and query counts are independent.

Substitution into the SAME CJ6 formula proves

    Gs-R_P(eta)
      >=G-1-2B-[3K2-3+3c+(G-3)Theta(3-c)]/27
                  -G rho/27.                           (DF11)

For 0<=c<=1, `Theta(3-c)=K3+c(K2-K3)`. In this range DF11 is

    Gs-R_P(eta)>=delta-A_pure c-G rho/27,
    A_pure=[3+(G-3)(K2-K3)]/27
           =0.37426313858085397... .                   (DF12)

A positive right side certifies s>0: eta is nonnegative, and s=0
would force eta=0 and contradict DF12. The identical density and
23/29 continuation then give Haar mass at least49 alpha_new/11088
times that right side. Thus both losses spend ONE common margin.
Passing each separate test does not permit adding their conclusions.

An explicit joint finite-window result follows. Keep the base pure
classes, prohibit additional pure numerical labels3^e for3<=e<=8,
and allow any finite collection of pure originals at e>=9, with
arbitrary fixed phases. Their complete geometric budget is

    c<=54 sum_(e>=9)3^(-e)=1/243.

Use a shallow window D=1000000000, containing3821 nonunit Q-smooth
cofactors, with the same selection rule as Section9. Then

    T_Q(D)=0.0000010180612304494368...,
    delta-A_pure/243-(8G/(3 alpha_new))T_Q(D)
         =0.00009865804614523054...>0,
    H(full survivor)>=0.00000004531223250395581...
                    >1/23000000.                       (DF13)

All figures in DF13 are displays of exact rationals stored in the
data file. Both the arbitrary pure tail and the unrestricted
projections outside the finite window are present simultaneously.
Every nonpure original at exponent e>=4 remains unrestricted,
including exponents4 through8. The absence condition in this
corollary concerns only pure numerical moduli.

With no shallow defect, the same bound permits c<0.005185038092063967....
The worst-case pure tail from exponent8 already exceeds that allowance.
This only limits the displayed estimate; it is not a covering example
or an impossibility claim for a different source construction.

The [defect/window producer](../../frontier/cover-geometry/shallow_defect_finite_window.py)
and [exact data](../../frontier/cover-geometry/shallow_defect_finite_window.json)
pin NJ10--NJ12's supplier data and independently enumerate each finite
cofactor complement by prime recursion and a heap. Complete tails are
obtained by subtracting these finite sums from the exact Euler product.
All28 named checks pass. Sections8--10 supply the general proofs;
the computations certify their explicit rational windows and margins.
No new Lean verification is claimed.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/shallow_defect_finite_window.py

The remaining obligations include unrestricted low pure3 geometry,
uncontrolled shallow defects on the finite window, and arbitrary
support primes. Neither numerical height exhaustion nor the positive
restricted margin resolves those obligations.
