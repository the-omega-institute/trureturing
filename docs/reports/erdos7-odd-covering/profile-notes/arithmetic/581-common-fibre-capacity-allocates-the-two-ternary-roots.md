# Common-fibre capacity allocates the two ternary roots

Keep one actual selected Q source and the complete original survivor.
The conditional mass assigned to the two legal ternary roots can depend
on that same Q coordinate. A pointwise capacity condition then constructs
one supported probability with exactly the prescribed Q marginal and no
normalization loss. Its optimized uniform query bound depends on the
minimum **joint** reserve, rather than the sum of two separate minima.

For the fixed pure3 slice below, this yields the sufficient condition

    Y_A <= 93/20,  Y_A+Y_B <= 9,
    R_P <= B+(151/140)(1+B) = 11.477804692877992... < 566/49.

The loads include all actual residual heights. A 40-original fixed-residue
family separates this adaptive uniform-cap certificate from every
constant-root, loss-free uniform-cap coefficient while both use the SAME
retained supplier bound B in CA1. It
also fails Report580's entire Gamma sufficient test on that source.
This is not an exclusion of all older instance-specific certificates.

The query-profile transport and geometric tail sum are reused from
[Report572](572-compatible-fibres-lift-one-six-prime-query-law.md) and
[Report579](579-two-root-convex-clipping-has-an-exact-certificate-boundary.md).
The additional construction is the pointwise allocation, its exact
uniform-cap optimization, and its realization by actual fixed originals.
These are ordinary proofs and exact arithmetic, with no new Lean
verification or external novelty claim. The shallow phase restriction,
the specified pure3 slice and the pointwise reserve remain hypotheses;
unrestricted Erdős #7 remains open.

## 1. The actual family and one source

Let P={3,5,7,11,13,17,19} and Q=P without3. The actual originals form
an arbitrary finite family of distinct nonunit P-smooth numerical moduli,
with one globally fixed residue per modulus. Its pure3 originals are
exactly 1 mod3 and3 mod9. For each nonunit Q-cofactor d, select at most
two Q phases containing every original projection through ternary
exponent3. Only the actual finite cofactor inventory has selections.

Retain ONE actual Report569 PA source nu on the selected Q-survivor:

    R_Q(nu) <= B = 432040125182653876501/86355045355449035400,
    nu <= (9/alpha_min) H_Q,
    alpha_min = 7575003978548161/73724315753088000.       (CA1)

For a finite measure sigma, q_d(sigma) is its maximum residue-cylinder
mass at the exact numerical modulus d; q_1(sigma)=sigma(1).
R_Q sums q_d over every nonunit Q-smooth d, including all heights.
R_P is defined similarly. No source is changed for individual queries.

Write A=[0]_9 union[6]_9 and B3=[2]_3. Their conditional Haar laws
are u_A,u_B, with Haar density factors9/2 and3 on disjoint supports.
For the COMPLETE actual survivor mask chi put

    c_A(x)=integral chi(t,x) du_A(t),
    c_B(x)=integral chi(t,x) du_B(t).                   (CA2)

Every shallow Q-bearing original has vanished on the selected support.
The actual residual loads from Reports579–580 satisfy

    Y_j=sum_(e>=4)54*3^(-e)L_(j,e),
    1-c_A <= Y_A/12,   1-c_B <= Y_B/18.               (CA3)

Here L_(j,e) counts the actual original Q incidences in root j at
exponent e. The same x, the same fixed phases and the original numerical
labels occur throughout. Overlapping ternary cylinders are permitted;
CA3 is a union bound, not an independence assumption. No height tail is
discarded.

## 2. Capacity constructs a probability without losing its marginal

Choose 1/2<=M<=1 and lambda>0. Suppose, nu-almost everywhere,

    min(M,12lambda c_A(x))+min(M,18lambda c_B(x)) >= 1.  (CA4)

This is equivalent to the three pointwise inequalities

    12lambda c_A >= 1-M,
    18lambda c_B >= 1-M,
    lambda(12c_A+18c_B) >= 1.                         (CA5)

Necessity follows by bounding the other capped term by M and both
terms by their uncapped values. For sufficiency, when neither term is
capped use the third inequality. When exactly one is capped use the
corresponding first or second inequality; when both are capped use2M>=1.

Set

    a_B(x)=min(M,18lambda c_B(x)),
    a_A(x)=1-a_B(x).

Then a_A+a_B=1 and

    0<=a_A<=min(M,12lambda c_A),
    0<=a_B<=min(M,18lambda c_B).                      (CA6)

Define the single joint law

    mu(dt,dx)=chi(t,x)
       [a_A(x)u_A(dt)/c_A(x)+a_B(x)u_B(dt)/c_B(x)]nu(dx). (CA7)

A zero reserve necessarily receives zero weight, and that term is
defined as zero. Integrating the conditional kernel gives a_A+a_B=1,
so mu is supported on the actual survivor and its Q marginal is EXACTLY
nu. The weights are fixed functions of the actual x, not choices made
after seeing a query or its maximizing phase.

For every Q-smooth d>=1, a depth1 ternary cylinder meets the supported
ternary source in at most one root, and CA6 gives

    q_(3d)(mu) <= M q_d(nu).

At every depth h>=2, multiplying the conditional Haar caps by CA6 gives
the same bound in either root:

    q_(3^h d)(mu) <= 54lambda 3^(-h) q_d(nu).         (CA8)

The complete sum over h>=2 is9lambda. Pure-Q queries retain nu and
positive ternary depths include the unit Q-cofactor exactly once. Hence

    R_P(mu) <= N := B+(M+9lambda)(1+B),
    mu <= (486lambda/alpha_min) H_P.                 (CA9)

The density bound uses the maximum on the two disjoint root supports,
not their sum. Finite query boxes followed by monotone convergence
justify all query sums. This reuses the conditional-profile argument
of Report572 and the full-depth coefficients of Report579; it does not
exchange a query maximum with an integral in the wrong direction.

## 3. The precise gain from retaining common-fibre reserves

Take essential infima under the SAME nu:

    a=essinf 12c_A,  b=essinf 18c_B,
    r=min(a,b),     beta=essinf(12c_A+18c_B).

Then beta>=a+b>=2r. For r>0, CA5 is equivalent to

    lambda >= max((1-M)/r,1/beta).                    (CA10)

The switch occurs at M0=1-r/beta>=1/2. On [1/2,M0] the minimized
coefficient M+9lambda is9/r+M(1-9/r); on [M0,1] it isM+9/beta.
For beta>0, their slopes give the EXACT minimum of this uniform-cap
certificate:

    C_ad = 1+(9-r)/beta,          0<=r<=9;
    C_ad = 1/2+9/(2r),            r>=9.               (CA11)

For0<r<9 the attainer is M=1-r/beta,lambda=1/beta. For r>9 take
M=1/2,lambda=1/(2r). At r=9 either displayed attainer works and the
coefficient is1. If r=0<beta only M=1 is possible, andlambda=1/beta
attains the first formula. If beta=0 no finite uniformlambda works.

For comparison, keep constant POST-restriction root weights w,1-w.
When a,b>0 their best uniform-cap coefficient is

    C_fix(w)=max(w,1-w)+9max(w/a,(1-w)/b).

This piecewise affine convex function decreases before both breakpoints
w=1/2 andw=a/(a+b), and increases after both. Comparing their values
gives

    C_fix = 1+(9-r)/(a+b),        r<=9;
    C_fix = 1/2+9/(2r),          r>=9.                (CA12)

For r=0<a+b put all mass on the branch with positive minimum reserve;
the first formula still applies. If a=b=0 no such finite constant-root
certificate exists, although CA11 can apply when beta>0.

For a+b>0 and r<9 the exact improvement is

    C_fix-C_ad=(9-r)(beta-a-b)/[beta(a+b)].            (CA13)

Thus the gain records that the two worst reserves need not occur at
the same Q point. It is strictly positive exactly when beta>a+b in
this parameter range. These formulas optimize the stated uniform caps,
not the actual query norm over every supported law. CA12 is the
loss-free constant-root subclass of Report579; it does not cover
clipping with mass loss, actual query debits, arbitrary within-root
laws or Report572's fixed pre-restriction mixture.

## 4. A load criterion and arbitrary23/29 continuation

By CA3, the following pointwise conditions imply CA5:

    Y_A <= 12-(1-M)/lambda,
    Y_B <= 18-(1-M)/lambda,
    Y_A+Y_B <= 30-1/lambda.                           (CA14)

Take M=13/20 andlambda=1/21. The conditions

    Y_A <= 93/20,   Y_A+Y_B <= 9                      (CA15)

imply all of CA14, since Y_B<=9<213/20. They give

    N=B+(151/140)(1+B)
     =46254429425608360802397/4029902116587621652000
     =11.477804692877992... <566/49.                 (CA16)

No bound on the number of originals or their maximum finite height is
added beyond CA15. Direct reserve condition CA4 can be weaker than
CA15 when original cylinders overlap.

Independently condition23 and29 Haar on their complete actual
pure-power survivors. Report569 SD15–SD16, applied to THIS mu, removes
all additional mixed originals touching either prime and retains mass
at least(566-49N)/567. The two density factors are22/21 and28/27.
Together with CA9 this gives

    H(full survivor) >= alpha_min(566-49N)/(299376lambda)>0. (CA17)

For CA16 it equals

    121492068351127527013/4698650132269277184000000
    =0.000025856802471149576... >1/40000.

The added originals retain arbitrary fixed phases, distinct numerical
labels and arbitrary finite heights. The full prime support here is
P union{23,29}; this is not a statement about primes outside that set.

## 5. One actual40-original family separates the specified certificates

Let Q=(5,7,11,13,17,19), D=product Q=1616615. Retain the two pure3
originals. For each q_i, i=0,...,5, add originals at ternary exponents
0,1,4 with Q phases0,1,2, respectively. Their exponent1 ternary phase
is2 mod3; the six exponent4 ternary phases are

    0,6,9,15,18,24 mod81.

Add the Q-only original4 mod385. This gives21 originals. Add four
branch-A originals with cofactors D*5^j and Q phase2:

| j | ternary exponent | ternary phase |
|---:|---:|---:|
|0|5|27|
|1|5|33|
|2|6|36|
|3|6|42|

Finally add fifteen branch-B3 originals with Q phase3:

| cofactor | ternary exponent | ternary phase |
|---|---:|---|
|D*5^(4+i), 0<=i<=12|4|2+3i|
|D*5^17|5|41|
|D*5^18|6|44|

Each pair of coprime Q and ternary phases specifies its one full
numerical residue by CRT. All40 odd nonunit moduli are distinct.
Within each root, the listed ternary cylinders are pairwise disjoint,
including those of unequal depths. The exact producer supplies a
private CRT residue for every original and checks it against all40.

Fix S_q={0,1}, S_385={4}, with no selected phases at the new cofactors.
These selections contain every original projection through exponent3.
The actual PA source is explicit. Coordinates5 and7 are uniform on
roots2,...,q-1. At11, exclude roots0,1, and additionally exclude root4
only over the old root pair(4,4). Its conditional normalized row is
uniform on8 or9 roots, with density at most11/8<5/3. Coordinates13,17,19
are uniform after excluding roots0,1. All PA caps are inactive and the
higher digits retain Haar tails. This is the same single selected source
used in Report580's21-original control, with its branch-A phases changed
as displayed and additional unselected deep originals.

An A incidence requires some Q root2; each new A incidence requires
all Q roots2. Every B3 incidence requires ALL Q roots3. Thus the two
loads cannot be positive together, and pointwise

    Y_A <= 6*(2/3)+2*(2/9)+2*(2/27) =124/27,
    Y_B <=13*(2/3)+(2/9)+(2/27)     =242/27.          (CA18)

These imply CA15. Since the ternary cylinders are disjoint, both union
bounds in CA3 are equalities on every source fibre. On the positive
source cylinders [2]_(D*5^3) and[3]_(D*5^18), respectively, the reserves
attain

    (c_A,c_B)=(50/81,1),  (1,122/243).

Their source masses are1/(378675*5^3) and1/(378675*5^18). Consequently
the actual essential infima are

    a=200/27, b=244/27, r=200/27, beta=568/27.

The optimized parameters are M=46/71,lambda=27/568. Equations CA11–12
give the exact comparison under this SAME nu, retaining the uniform
supplier bound B from CA1 in BOTH certificates:

| uniform-cap certificate | coefficient | full query bound |
|---|---:|---:|
|constant post-restriction root weights, loss-free|487/444|11.587513263286876...|
|actual-Q-dependent root weights, loss-free|611/568|11.460592678273326...|

The first value exceeds566/49; the second is strictly below it. The
second also gives CA17 greater than1/32000. Neither value is asserted
to equal the optimal actual query norm of this finite family.

The qualification about B is essential. This explicit source itself has

    R_Q(nu)=29265142103/20101644288=1.45585812204... .

Indeed, for each of the eight subsets J of{5,7,11}, take the maximum
projected mass q_J of the134 source atoms. Their complete query sum,
including the unit, is sum_J q_J product_(p in J)p/(p-1). Multiply
by product_(q=13,17,19)[1+q/((q-1)(q-2))] and subtract1. Haar higher
digits justify all geometric tails. The exact producer performs these
eight projections. Substituting this ACTUAL R_Q in the fixed-root bound
already gives

    R_Q+(487/444)(1+R_Q)
      =37035348066149/8925130063872=4.14955835950... <566/49.

Thus this finite family illustrates the gain at the retained bound
interface; its bare noncoverage is not newly obtained, and failure of
the fixed-root bound using B is not failure of the fixed-root method.

For the displayed source, the11-root2 marginal is121/1080. The only
exponent4 A originals remain the six prime cofactors, so

    rho_A=sum_(q in Q)1/(q-2)+1/1080
         =174043/201960 =0.8617696573578927... .

This exceeds Report580's exact rho threshold0.8617656149481734... .
Its stronger Gamma test also fails on the SAME source: L_A4 has the
same integer-valued distribution, and

    Gamma_A(s)=(2/3)E(L_A4-s)_++K_(3-2s)/3,
    0<=s<=3/2,

is affine between0,1/2,1,3/2. The complete existing K envelope has its
verified dominant corner on[0,3]. The exact producer checks all four
endpoints strictly above the Gamma threshold, hence the entire range
fails that sufficient test. This says nothing about changing the
selected source, tighter instance-specific tails, or other old methods.

## 6. What has not been removed

Capacity is additional information about actual joint fibres. Distinct
numerical labels alone have not been shown to imply CA4 or CA15.
The conditional kernel's existence is not the construction of a
uniformly good lift for arbitrary pure3 families or arbitrary shallow
phase inventories. General joint-law optimization and finite-query
compactness were already available in Reports530 and571; they are not
new results here.

In particular, improving the joint allocation does not license changing
the actual Q law separately for different fibres or queries. One may
define a conditional kernel at every x, as CA7 does, while all those
kernels must be integrated against the same prescribed nu.

There is also an explicit obstruction to removing the joint-fibre
hypothesis using only the retained integer-layer and K_t moment data.
This is an AUXILIARY probability model, not an actual original family.
Put p=K3/3 and take one event E of probability p, with

    L_(A,4)=L_(A,5)=6*1_E,
    all other branch layers zero.

All layers are integer-valued on the same source, with only two
nonzero heights. The existing complete nonnegative envelope satisfies
K_t>=p(6-t)_+ for every t>=0 and6p<B. Check its affine pieces at the
integer knots0,...,6; for t>=6 the right side vanishes. Every convex
mixture of these layers consequently satisfies the retained K spectrum.
The permitted abstract union summary is

    Y_A=(16/3)*1_E, Y_B=0, c_A=1-Y_A/12, c_B=1.

Now permit LOSSY adaptive root masses under uniform caps

    0<=a_A(x)<=min(M,12lambda c_A(x)),
    0<=a_B(x)<=min(M,18lambda c_B(x)), a_A+a_B<=1.

Here0<=M<=1 andlambda>=0. The maximal retained mass at x is the minimum
of1 and the sum of the two capacities. The resulting submeasure has
Q marginal at most nu and the same raw budget
N=B+(M+9lambda)(1+B). Its mass deficit on actual fibres is bounded by

    E[1-min(M,lambda(12-Y_A)_+)
       -min(M,lambda(18-Y_B)_+)]_+.

For the auxiliary event E, let v be its retained conditional mass.
The caps give v<=1, v<=M+(20/3)lambda, and v<=(74/3)lambda. Hence

    M+9lambda >= v+(7/3)lambda >= (81/74)v.

Set d=(81/74)(1+B), r0=B+d=11.573992840877331... . Exact arithmetic
gives p*r0>d and r0>566/49. Since total retained mass s<=1-p(1-v),

    N-r0*s >= (p*r0-d)(1-v) >=0.                     (CA19)

Every positive-mass raw uniform-cap certificate on this auxiliary
model is therefore at least r0. On this ONE auxiliary law equality is
attained at M=27/37,lambda=3/74, with no loss; this is not the worst-case
optimum over all moment-compatible laws. Arbitrary actual-law profiles,
tighter query costs and arithmetic realizability are outside this
obstruction. It identifies the missing input: genuine joint incidence
information, beyond integer counts and their retained moment envelope.

## Verification

The [exact producer](../../frontier/cover-geometry/adaptive_branch_capacity.py)
and [retained data](../../frontier/cover-geometry/adaptive_branch_capacity.json)
check the capacity identities, analytic attainers, complete geometric
tails, actual fixed-residue family, all40 private points, source
distribution, Gamma comparison, exact actual R_Q and continuation
constants using rational arithmetic. They also verify the auxiliary
moment knots and dual constants. There are218 named checks, including
108 capacity boundary controls and49 lossy auxiliary parameter controls.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/adaptive_branch_capacity.py

The ordinary proofs above carry the arbitrary-family, real-parameter
and all-height quantifiers; finite controls do not replace them. No
new Lean verification is included.
