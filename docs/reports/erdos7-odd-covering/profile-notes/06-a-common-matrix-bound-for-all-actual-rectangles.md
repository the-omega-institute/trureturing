[Index](../marked_head_profile.md) · [Previous](05-the-actual-rectangle-gives-two-further-square-savings.md) · [Next](07-a-common-weighted-low-layout-and-a-nonnegative-tail-correction.md)

<a id="a-common-matrix-bound-for-all-actual-rectangles"></a>
### A common matrix bound for all actual rectangles

Let an actual nonempty 11/13 fibre be an m-by-n rectangle with k
remaining point holes, where m<=10, n<=12 and k<=12. The existing
clipped density satisfies

    f/120 = 1/max(93,mn-k),    h=f(mn-k)/120.

For four nonnegative old test amplitudes A=(a,b,c,d), the row, column
and point intersection counts directly bound its low-block square by

    integral_fibre xi L_low^2 <= h a^2 + (f/120) A^T B(m,n) A,
    B(m,n) = [[0,n,m,1],[n,n,1,1],[m,1,m,1],[1,1,1,1]].

Absent test indicators only reduce this nonnegative expression. Convex
concentration within each test block extends it to arbitrary test
assignments. Set

    U=(228733,264815,215188,41873)/1000000.

For all 120 dimension pairs, the matrix
diag(U)-B(m,n)/max(93,mn-12) is positive definite. The adjacent
standard-library verifier checks exact rational LDL decompositions
and reconstructs every matrix. Since B has nonnegative entries and
A is nonnegative, this also bounds every actual k and empty fibres.
The sum of the common diagonal is 750609/1000000. Averaging its
four squares on the same old law, and using the existing marginal
and higher-exponent estimates, gives

    Gamma(nu) <= 1+[(1+750609/1000000+12259/83700)G-1]/s.  (DV3)

Here G is any simultaneous old square bound, and s is the certified
remaining mass on this same construction. The higher-exponent
coefficient is exactly (40/31)(chi0-13/8), as in (SC9).

For the first moment the three positive-exponent coefficients satisfy

    q=(fn,fm,f)/120 <= (4/31,10/93,1/93),
    sum(q)<=11/48.

All 1372 nonempty count triples satisfy these rational inequalities.
Each old test amplitude is at least one, so their unused coefficient
mass saves 23/93-11/48=9/496. Including the same high-exponent mean
coefficient 89/3720 gives

    sup_test E_nu L <= 1+[(1+1009/3720)M-1-9/496]/s.      (DV4)

Neither matrix nor first-moment refinement changes the probability law.

<a id="simultaneous-transfer-and-exact-arithmetic"></a>
### Simultaneous transfer and exact arithmetic

For one b, let H_t be the unnormalized numerator in (DV2) for
psi(z)=(z-t)_+, and let G_num be its numerator for psi(z)=z^2.
Compute H_0,H_2,H_3,H_4,H_5 and G_num exactly; H_1=H_0-N because
every complete load is at least one. For t=6,...,12 retain the valid
numerator upper bounds (10,7,4,3,2,1,0). Put

    D_b=3720N-680H_2-160H_4-89H_0,
    s_b=D_b/(3720N),    ell_b=D_b/(4800N).                (DV5)

Every D_b is positive. Substituting M=H_0/N and G=G_num/N in
(DV3)--(DV4), always with this same D_b, proves the two bounds in
(DV1). Both maxima occur on the first shape at N=86, with

    M=271/86, G=1131/86, H_2/N=52/43, H_4/N=16/43,
    s_b=219961/319920.

The reference fraction is uniformly at least
ell_b>=108683/204000. Thus the existing upper-quantile comparator
may use this fraction while retaining all moment and hinge bounds
for the same nu.

For each rectangle dual, form each whole hinge cost on this b. Its
unnormalized numerator is bounded by the smaller of the sum of its
H_t bounds and the already certified (JC1) bound at this same (S,N).
The first-shape costs at N=77,...,83 can also use exact (DV2) maxima
over all actual b with that count. Including the rectangle constant
gives a numerator low_b and a positive dual denominator den. The
same high-exponent and mass transfer is

    Theta_nu(t) <= (3720 low_b+89 den H_0)/(den D_b).       (DV6)

Maximizing only after forming this ratio gives:

| t | Uniform upper bound for Theta_nu(t) |
|---|---|
| 4 | 1896712717819/1358537500000 |
| 5 | 5263525792649/4891475000000 |
| 6 | 306627/391318 |
| 7 | 306152576027/489147500000 |
| 8 | 2291713236139/4843600000000 |
| 9 | 1964369484727/4843600000000 |
| 10 | 169349448989/489147500000 |
| 11 | 21945226346/76429296875 |
| 12 | 111549448277/489147500000 |

The [actual-deletion experiment](../verify_actual_deletion_profile.py)
and [exact result data](../certificates/actual_deletion_profile_certificate.json)
reconstruct the complete finite geometry and costs. This separate
entry point explicitly requires NumPy; the original marked-profile
verifier remains standard-library only. Array arithmetic uses integers
with checked range bounds, and final rational comparisons use Python
integers. These are ordinary proofs with reproducible finite arithmetic,
not newly frozen Lean results. The unrestricted original 3/5/7 exponents
and a general successful tail certificate remain open.

<a id="an-actual-full-fibre-old-configuration-with-unrestricted-tails"></a>
## An actual full-fibre old configuration with unrestricted tails

Let U be the complement modulo 45 of the five classes

    (modulus, residue) = (3,0), (9,4), (5,0), (15,11), (45,2).

It has 16 points. In CRT coordinates modulo 315 put

    R = U × {1,2,3,4,5,6} ⊂ (Z/45Z) × (Z/7Z).             (BT1)

Consider a finite family of distinct odd nonunit moduli whose full original
3/5/7 part divides 315. Suppose its classes with modulus dividing 315 leave
exactly R in these coordinates. Then the family cannot cover the integers,
even with arbitrary finite 11/13 heights and arbitrary later prime factors,
exponents, cofactor supports and residues. The same assertion holds when
those old survivors contain R: the construction below uses a probability
supported on R, so it is still supported on the actual old survivors.

This is a genuine restriction on the old geometry. One complete original
315 family realizing it consists of the five displayed classes together with

    (7,0), (21,0), (35,0), (63,0), (105,0), (315,0).

All five mixed-seven classes in this example are redundant. The verifier
checks all 315 residues and obtains exactly the 96 points of (BT1). No
further move of those redundant classes is made. In particular, this result
is not an automatic removal of one branch from a procedure that first makes
every mixed-seven class effective. It does not settle unrestricted #7.

<a id="the-same-supported-head-law-throughout-the-continuation"></a>
### The same supported head law throughout the continuation

Use the existing clipped construction with C_clip=40/31 on the old uniform
law on R. This is the `root2_same_other_column`, N=96 input to (SC2)--(SC10)
and (JC1). Those inequalities require only 0≤b≤5 and the labelled-cylinder
upper bound on b, so they apply with b=0. Their proof does not require a
positive effective mixed-seven deletion. In the containing-survivor case,
use this same reference law directly; none of the later distinct-label
estimates requires adding new original classes.

The old first moment, square, threshold-two hinge and threshold-four hinge
bounds on this branch are respectively

    259/96, 21/2, 23/24, 5/16.

Thus its low clipped mass is at least 1811/2232, its full clipped mass is at
least s0=88903/119040, and its density comparison fraction is
ell=s0/C_clip=88903/153600. After the actual-rectangle square saving, the
same full-height supported probability nu satisfies

    sup_L E_nu L ≤ M0 = 1134400/266709,
    sup_L E_nu L² ≤ G0 = 35754161/1333545.                  (BT2)

Its nine full-height hinge bounds, in increasing order of t=4,...,12, are

    6877275965987/6667725000000, 333388924487/416732812500,
    310127/533418, 3115275948431/6667725000000,
    475717686817/1333545000000, 2048775931829/6667725000000,
    439561169399/1666931250000, 1468244673773/6667725000000,
    589122335161/3333862500000.                            (BT3)

All moments, hinge values, high-exponent contributions and normalization
here retain this single old configuration. No maximum over other branches
is substituted at an intermediate tail query.

<a id="a-pointwise-upper-function-with-an-exact-finite-observation"></a>
### A pointwise upper function with an exact finite observation

Write S=10^24, C=ceil(S M0)/S and G=ceil(S G0)/S, treating these rounded
constants as fixed exact rationals. The following construction is an upper
function for the actual hinge profile; it is not a probability comparator.

First, for 1<t≤43/13 set a=(t-1)/30, b=1-13a. Both are nonnegative, and
for every integer x≥1,

    Q_t(x)=a(x²-1)+b(x-1) ≥ (x-t)_+,
    Q_t(x)-(x-t)=a(x-6)(x-7).

The last expression is nonnegative on integer x, while Q_t(x)≥0. Therefore
a(G-1)+b(C-1) is a valid moment upper bound. For t>43/13 choose j≥7 with

    (j²-j+1)/(2j-1) ≤ t ≤ (j²+j+1)/(2j+1).

Comparing adjacent ratios (x-t)/(x²-1) shows that their positive maximum
over integers x≥2 is (j-t)/(j²-1). Hence

    E_nu(L-t)_+ ≤ (G-1)(j-t)/(j²-1).                     (BT4)

Next use the existing reference Y=X N11 N13, where X is the old comparator
and the two independent factors have probabilities
Pr(Np=1)=(p-2)/(p-1), Pr(Np=f)=p^(1-f) for f≥2. Density domination and
the actual hinge inequality give the reference upper function

    R(t)=3-t+E(Y-3)_+/ell       for 1<t≤3,
    R(t)=E(Y-t)_+/ell           for t≥3.

For t in [4,12], also use adjacent interpolation of (BT3). Let U(t) be the
minimum of all applicable reference, moment and interpolated upper bounds.
Define

    Psi(t)=C-t                         for t≤1,
    Psi(t)=max(C-t,U(t))               for t>1.            (BT5)

Then Psi dominates every actual complete-layout hinge. Its forced affine
baseline makes the following identity valid even though C is only an upper
bound on the actual first moment. For every positive integer random variable
N of finite mean and every T>1,

    E[N Psi(T/N)] = C E N - T
      + Σ_(1≤n<T) Pr(N=n) [n Psi(T/n)-Cn+T].              (BT6)

Each bracket is nonnegative by definition. This applies the finite-state
argument to Psi itself and does not replace the exact M by a rounded bound
inside the actual-profile identity (AP7).

The finite observation has a closed update. For a fixed K≥max T, retain
E N and Pr(N=n) for 1≤n<K. If an independent positive integer factor F is
adjoined, then

    E(NF)=E N·E F,
    Pr(NF=n)=Σ_(d|n) Pr(N=d) Pr(F=n/d),       n<K.         (BT7)

Every d on the right is less than K. A state at least K cannot return to
the retained range because F≥1. Equivalently, pulling observations backward
through the transition preserves the span of 1, n and the indicators
1_(n=j), j<K. Thus the full mean and finitely many point masses suffice for
all queries in this fixed schedule, without truncating the infinite mean.
This is an exact observation for the auxiliary comparison process; the
actual congruence family's labelled geometry remains an input to (AP2).

This use of the observation operator is the finite version of
[Recursive Relational Observation §32.3](https://github.com/the-omega-institute/trureturing/blob/11df59d12488feaf942a9b4c685b29c8dcc6ca4e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#32-bounded-borel-observation-uniqueness-and-order-sensitive-compact-completions).
The same volume's §33.9 distinguishes two measures with the same transition
matrix and different initial laws; here the head law and its moment/profile
bounds are fixed together. These are source connections, not additional Lean
verification or a deduction of positive residual mass from topology.

<a id="directed-certificate-and-infinite-continuation"></a>
### Directed certificate and infinite continuation

Use (AP2), (AP5) and (AP6) from the Problems dossier. For each tail prime q,
put delta_q=(T_q-1)/(q-2), d_q=q-1-T_q, c_q=(q-1)/d_q. The stored threshold
runs specify the following inclusive endpoints; after one endpoint use the
next row's threshold.

| Prime endpoint | T | Prime endpoint | T |
|---:|---:|---:|---:|
|17|4|19|5|
|31|8|41|12|
|61|16|73|24|
|113|32|151|48|
|211|64|229|72|
|293|96|419|128|
|449|144|577|192|
|809|256|883|288|
|1153|384|1601|512|
|1787|576|2377|768|
|3271|1024|3719|1152|
|5051|1536|7019|2048|
|8117|2304|8191|3072|

For 8191<q≤30011 use T_q=1+floor(3(q-2)/8). The exact prime list has
pi(30011)=3246, including 2 and absent primes, and 3240 tail steps from 17.
Every step has 1<T_q<q-1 and c_q≤q. The largest threshold is 11254.

The verifier rounds every nonnegative atom, mean, correction, charge and
square upper bound upward on the S grid. Its product probabilities use
(BT7). The full first-moment multiplier is 1+1/d_q, and the square multiplier
is 1+(3q-1)/((q-1)d_q). The negative affine term in (BT6) uses the one fixed
constant C, so upward probability estimates never multiply negative
corrections.

Reference calls are evaluated by a positive convolution restricted to
N11,N13≤80. For p in {11,13}, the omitted mean is exactly

    E[Np; Np>80]
      = p^(-79) [81/(p-1)+1/(p-1)²].

The union bound on omitted factors gives an upper error
E X·(E N13·E[N11;N11>80]+E N11·E[N13;N13>80]) for every call; its upward
rounding is 1/S. Integer calls are interpolated exactly between adjacent
knots before division by ell. Thus neither reference truncation nor retained
product states discard an unaccounted tail contribution.

At B=30011 the exact total charge and moment bounds are

    C_B ≤ 951034037806531654678813/10^24,
    1-C_B ≥ 48965962193468345321187/10^24 > 0.04896,
    J_B ≤ 2001909435263859468210322417/250000000000000000000000.

Every earlier charge sum is also less than one. After the single final
conditioning in (AP6),

    Gamma ≤ 2668895569005877113728870285/16321987397822781773729
          < 163516 < 167115
          < 3246 (log 3246+log log 3246-3)².              (BT8)

The final logarithm comparison uses the existing exact positive-series
lower bound in `verify_finite_continuation.py`. Consequently the BBMST
continuation applies to every subsequent prime, proving the stated
noncoverage theorem. If the family ends earlier, extend the comparison with
absent prime coordinates; its actual violation probabilities there are zero.

The `joint_cost_branch_tail17` field contains the exact inputs, thresholds,
checkpoints, positive residual and stopping fractions. An independent
implementation uses divisor-indexed convolution, trial-division primes,
scale 10^30, reference cutoff 40 and a different rational logarithm lower
bound. It checks 15,148,804 integer moment queries and also obtains (BT8);
its Gamma upper bound differs by less than 3.01·10^-8. These are ordinary
mathematical arguments with exact arithmetic. No new Lean endpoint, freeze
or unrestricted-axis result for all old configurations is asserted.

<a id="retaining-an-original-exponent-label-across-the-full-auxiliary-law"></a>
## Retaining an original exponent label across the full auxiliary law

The conditional comparison in (AP3)--(AP4) permits a stronger order of
averaging and maximization than the separate scalar calls in (BT6).
Fix one supported head probability mu and write
F_mu(f)=sup_test E_mu f(L). Every complete head load is at least one.
Let K be the auxiliary vector of old-tail heights, independent of the
head point, and put N=product_p(1+K_p). Original exponent labels a are
fixed before K is sampled. There are exactly N labels with a<=K.
For each label define

    p_a(n)=Pr(a<=K,N=n),   w_a=Pr(a<=K),
    v_a=E[1_(a<=K)/N],
    g_a(z)=E[1_(a<=K)(z-T/N)_+].

Each original head test belonging to a is the same in every auxiliary
outcome that includes a. Applying the existing Jensen comparison,
then collecting this test's contributions before taking its supremum,
therefore gives

    d_q b_q <= sum_a F_mu(g_a).                            (FL1)

The current-prime depth weights sum to one, as in (AP4). Missing
original tuples can be completed in advance by arbitrary fixed tests;
the extra terms are nonnegative. No test choice depends on the sampled
head point. This is a direct reorganization of the existing original
label comparison, rather than a new independence assumption.

On z>=1, the exact finite-cost representation is

    f_a(z)=w_a z+sum_(1<=n<T)p_a(n)(T/n-z)_+,
    g_a(z)=f_a(z)-T v_a.                                 (FL2)

The omitted put terms vanish because n>=T. Each f_a is convex and
nondecreasing: its slope is at least w_a-sum_(n<T)p_a(n)>=0.
Since mu has mass one, F_mu(g_a)=F_mu(f_a)-Tv_a. Counting active
original labels gives the exact identities

    sum_a w_a=E N,    sum_a v_a=1,
    sum_a p_a(n)=n Pr(N=n).

All sums are legitimate. For a fixed finite physical head its test
loads have a finite bound D, so F_mu(g_a)<=D w_a; also E N is finite.
Consequently (FL1) is at most sum_a F_mu(f_a)-T.

Let C bound all first moments on this same mu, and let Psi bound all
hinges, enlarged to satisfy Psi(t)>=C-t. Define the nonnegative
quantity kappa_n=Psi(T/n)-C+T/n. Put P_a=sum_(n<T)p_a(n).
For every actual head test there is an exact decomposition

    E_mu f_a(L)=(w_a-P_a)E_mu L
       +sum_(n<T)p_a(n)[E_mu(L-T/n)_++T/n].

The mean coefficient is nonnegative. Substituting the simultaneous
upper bounds directly proves
F_mu(f_a)<=Cw_a+sum_(n<T)p_a(n)kappa_n. Thus for any selected finite
set J of original exponent labels, with certified B_a>=F_mu(f_a),

    d_q b_q <= sum_(a in J)B_a + C(E N-sum_(a in J)w_a)-T
      +sum_(n<T)[n Pr(N=n)-sum_(a in J)p_a(n)] kappa_n.    (FL3)

Every bracket in the finite correction is nonnegative, by the active
label count. The subtractions here remove exact labelled contributions
from a specified upper-bound decomposition; they do not subtract two
unrelated bounds for an unknown physical mass.

In particular, the zero exponent label is always active. For J={0},

    f_0(z)=z+sum_(n<T)Pr(N=n)(T/n-z)_+,
    d_q b_q <= B_0+C(E N-1)-T
      +sum_(n<T)(n-1)Pr(N=n)kappa_n.                     (FL4)

The linear coefficient one retains the entire auxiliary law, including
all N>=T. Only the put corrections require low multiplier probabilities.
One can take B_0 to be the smaller of a whole-cost bound and
C+sum_(n<T)Pr(N=n)kappa_n. Both bound the same F_mu(f_0), so this
choice guarantees that (FL4) is no worse than the corresponding (BT6).
Using the zero-label constants for a nonzero label would be invalid;
the general formula is (FL3).

For fixed maximum query threshold R, the probabilities Pr(N=n), n<R,
and the full mean E N form a closed observation for (FL4). Inserting
an independent positive integer multiplier updates each low probability
by divisor convolution; every predecessor of n<R is itself below R.
The full mean updates multiplicatively. For additional selected labels,
retain their restricted low probabilities p_a(n) and w_a as well.
The first and second moments and all hinge bounds must continue to
belong to the same actual head law.

Directed evaluation also preserves these distinctions. With C and Psi
fixed, upper probability and mean bounds multiply nonnegative remaining
coefficients. A rounded cost built with upper probabilities still
dominates f_0 pointwise. Before applying a theorem restricted to
increasing convex costs, verify their sum is at most one, or add
max(0,sum p_upper-1)z to restore monotonicity while keeping domination.

The finite observation principle agrees with the repository's recursive
relational observation analysis. Its newer
[convolution result, section 34](https://github.com/the-omega-institute/trureturing/blob/5744e73ad2/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)
has a different additional premise: its residual index grows by at least
one per factor. Here an auxiliary multiplier can equal one. Every finite
admitted prefix has positive probability of N=1, so that theorem's
finite-time disappearance cannot be transferred to this recursion.
The valid reduction is the explicit finite observation above. Neither
(FL3) nor (FL4) alone proves positive final residual or settles #7.

<a id="saturated-low-labels-and-arbitrary-357-heights"></a>
## Saturated low labels and arbitrary 3/5/7 heights

Fix P={3,5,7}, h=(2,1,1), the nonempty survivor set Omega of a
finite family of distinct nonunit divisors of 315, and one probability
mu on Omega. Let lambda extend
mu by independent uniform higher prime digits, up to the original
family's arbitrary finite heights. The following transfer preserves
every original modulus and works for nonuniform mu. The separate
ambient-density estimate below requires uniform mu.

For J contained in P, put

    D_J={d dividing 315 : v_p(d)=h_p for every p in J}.

Every higher original modulus has the unique representation

    m=d product_(p in J) p^e_p,
    J={p:v_p(m)>h_p}, e_p=v_p(m)-h_p>=1,
    d=product_p p^min(v_p(m),h_p) in D_J.                 (SH1)

Distinct tuples (J,e,d) remain distinct original labels even when they
project to the same d. A test block at fixed (J,e) chooses one low
residue for each d in D_J; different e may choose different low tests.
The seven nonempty restricted families have 4,6,6,2,2,3,1 labels,
in the order {3},{5},{7},{3,5},{3,7},{5,7},{3,5,7}.

For their complete low test families define

    M_J=max_A E_mu A,        C_JK=max_(A,B) E_mu AB,
    H_mu(t)=max_A E_mu(A-t)_+,  A in the empty-J family.

The two choices in C_JK are independent choices from their respective
families. In particular C_JJ=max_A E_mu A^2: Cauchy--Schwarz gives
the upper bound and A=B attains it. Include the unit divisor in the
empty-J family, so every complete low or full test load is at least one.

<a id="the-eight-type-moment-kernel"></a>
### The eight-type moment kernel

For each p let

    alpha_p=sum_(e>=1)p^-e=1/(p-1),
    beta_p=sum_(e,f>=1)p^-max(e,f)=(p+1)/(p-1)^2,
    a_J=product_(p in J)alpha_p,
    K_JK=product_(p in J symmetric_difference K)alpha_p
          product_(p in J intersection K)beta_p.         (SH2)

Here the set K in the subscripts is distinct from the matrix K.
The matrix is the tensor product over p=3,5,7 of
[[1,alpha_p],[alpha_p,beta_p]]. Its local pairs (alpha,beta) are
(1/2,1), (1/4,3/8), and (1/6,2/9). Finite physical heights use
the corresponding finite sums, which are bounded by these limits.

Write an actual full test load as L=A0+U, where U contains exactly
the higher labels. Then, for the same lambda,

    E_lambda U <= r=sum_(J nonempty)a_J M_J,
    E_lambda A0 U <= c=sum_(J nonempty)a_J C_empty,J,
    E_lambda U^2 <= s=sum_(J,K nonempty)K_JK C_JK,
    E_lambda L^2 <= C_empty,empty+2c+s.                  (SH3)

To prove this, condition on the low point. Saturation in (SH1) means
the low class already fixes all h_p low digits at every p in J.
One higher label therefore contributes its low indicator times
product p^-e_p. Two higher cylinders at a common prime are either
incompatible or nested, so their joint probability is at most
p^-max(e_p,f_p). Different prime coordinates are independent under
lambda. Sum these bounds over the complete original tuples and use
M_J and C_JK. This proves (SH3) for every finite height without
assuming independence between overlapping classes. The square sum
is ordered. Its different terms need not have simultaneous maximizers.

For every real t and u>0 the elementary pointwise bounds

    (A0+U-t)_+ <= (A0-(t-u))_+ +(U-u)_+,
    (U-u)_+ <= U,          (U-u)_+ <= U^2/(4u)

give the uniform-in-height profile transfer

    E_lambda(L-t)_+
      <= inf_(u>0) [H_mu(t-u)+min(r,s/(4u))].            (SH4)

H_mu is defined on all real thresholds. Since A0>=1, its extension
below one is H_mu(t)=M_empty-t. Since A0<=12, for t>12 the choice
u=t-12 gives the simpler min(r,s/(4(t-12))).

With the low projected residues fixed, every higher test prefix may
also be centered at zero. Conditional on the low point and the other
prime coordinates, the indicators then form a nested family with
their prescribed probabilities. Such a comonotone coupling maximizes
every increasing convex cost of a nonnegative weighted sum. Successive
centering in the three coordinates preserves the preceding centerings;
CRT realizes each resulting test residue without changing its low
projection. This comparison concerns lambda. It moves no original
forbidden class and makes no assertion about concentration after
conditioning on those forbidden classes.

<a id="actual-deletion-and-the-supported-probability"></a>
### Actual deletion and the supported probability

Let F avoid all actual higher forbidden classes, q=lambda(F), and
nu=lambda(.|F). Completing missing test labels only adds nonnegative
terms, so their expected forbidden count is at most r and q>=1-r.
For uniform mu write delta=|Omega|/315. The existing density theorem
(CM8) in the Problems dossier then also gives delta*q>=53/432.
Consequently the following valid lower denominators are

    q_* = max(53/(432 delta),1-r)  for uniform mu;
    q_* = 1-r                    for any mu with r<1.

For the same lambda, F and nu,

    E_nu L^2 <= 1+(C_empty,empty-1+2c+s)/q_*,
    E_nu(L-t)_+ <=
      inf_(u>0)[H_mu(t-u)+min(r,s/(4u))]/q_*.            (SH5)

The square uses L^2-1>=0 before conditioning; its numerator is
nonnegative, so replacing q by q_* preserves the upper-bound direction.
The density alternative is unavailable for nonuniform low weights.
If low normalization added a class or moved a redundant class into
an effective position, nu is uniform on the strengthened family's
survivors and merely supported on the original family's survivors.
Only when Omega was the original low survivor set is it the original
unmodified full survivor law. No step replaces nu's low marginal by mu.

The adjacent certificate gives an explicit conditioning obstruction.
Choose a class a modulo 9 of positive mu-mass eta in its N=86 head,
and lift uniformly to period 945. Compare deletion of a modulo 27
with deletion of a+9 modulo 27. Both have the same low projection
and q=1-eta/3. For the fixed test 1+1_(x=a mod 27), the conditional
hinges at one are 0 and eta/(3-eta), and the squares are 1 and
1+3eta/(3-eta). Thus those compressed observations do not determine
the conditional cost; the centering comparison cannot be carried
through an unspecified deletion event.

<a id="exact-low-geometry-and-stronger-truncation-constants"></a>
### Exact low geometry and stronger truncation constants

For a normalized marked head, use its old45 carrier S and actual
deletion vector b from (DV2). For I contained in {3,5}, let T_I
be the complete old45 cofactor tests restricted to cofactors saturated
at the primes in I. Set I=J intersect {3,5} and let

    V_J=T_I times T_I   if 7 is not in J,
    V_J={0} times T_I   if 7 is in J.

For the uniform low315 law, with N=sum_x(6-b(x)), the globally unused
seven digit gives the exact finite optimization

    N M_J=max_((u,v) in V_J) sum_x[(6-b(x))u(x)+v(x)],
    N C_JK=max_((u,v) in V_J,(w,z) in V_K)
      sum_x[(5-b(x))u(x)w(x)+(u(x)+v(x))(w(x)+z(x))].   (SH6)

Indeed, expand the product at each low45 point. Its seven-containing
cross terms are at most uz+wv+vz; putting all such tests at the
common unused digit attains all three simultaneously. This proves
the product identity directly, without treating a bivariate product
as convex. For weights w_x common to the surviving digits over x,
multiply each summand by w_x and replace N by sum_x(6-b(x))w_x.
Thus (SH6) also supplies costs on that single nonuniform law.

There are useful explicit uniform bounds without optimizing (SH6).
If Omega avoids a class at each of 3,5,7, every cylinder d dividing315
obeys

    delta mu(a mod d) <= (1/d) product_(p not dividing d)(1-1/p).

Sum these bounds for D_J and for all ordered lcm intersections in
C_JK, then apply (SH2). This yields

    delta r<=103/720,  delta c<=7/9,
    delta s<=713/945,  delta(2c+s)<=2183/945.

The normalized heads also avoid an effective pure9 class disjoint
from the pure3 class. In cylinders with v_3(d)=0 the surviving
ternary proportion is therefore 5/9 rather than 2/3. For positive
v_3(d) the previous worst-case cap remains valid. The strengthened
result is

    delta r<=97/720,   delta c<=34/45,
    delta s<=16693/22680,
    delta(2c+s)<=10193/4536.                             (SH7)

For completeness, these sums have an independent product evaluation.
For each p set rho_3=4/9, rho_5=1/5, rho_7=1/7 and

    A_inf(p)=p/(p-1)-rho_p,
    A_low(p)=sum_(a=0..h_p)p^-a-rho_p,
    B_inf(p)=p(p+1)/(p-1)^2-rho_p,
    B_low(p)=sum_(a=0..h_p)(2a+1)p^-a-rho_p,
    D(p)=sum_(a=0..h_p)(a+1+1/(p-1))p^-a-rho_p.

The right sides for delta r, delta c and delta s are respectively
product A_inf-product A_low, product D-product B_low and
product B_inf-2 product D+product B_low. This proves (SH7) by
rational geometric sums. Compared with the previous ambient square
error 733/252, the error falls by 3001/4536. With the identical
density denominator 53/432 the saving is 6002/1113. This is a
truncation-error improvement; it does not by itself improve the
separate full357 square bound 3849/106 in (SD1).

<a id="twelve-cylinder-caps-for-optimizing-the-low-probability"></a>
### Twelve cylinder caps for optimizing the low probability

For arbitrary mu let m_d=max_a mu(a mod d), d dividing315, and set

    gamma_d=product_(p:v_p(d)=h_p)p/(p-1)-1.

For an ordered pair d,e, define gamma_de as the product of the
following prime factors, minus one:

    1                 if both exponents are below h_p,
    p/(p-1)           if exactly one exponent equals h_p,
    p(p+1)/(p-1)^2     if both exponents equal h_p.

Grouping (SH3) by the original labels' low projections proves

    R_high=sum_d gamma_d m_d,
    Delta_square=sum_(d,e)gamma_de m_lcm(d,e),
    q>=1-R_high,
    E_lambda L^2<=Gamma_low+Delta_square.                (SH8)

Here Gamma_low bounds the exact complete low square on this same mu.
If R_high<1, the supported full357 probability satisfies

    Gamma_nu <= 1+(Gamma_low-1+Delta_square)/(1-R_high).  (SH9)

All twelve cylinder caps are maxima of linear functions of the low
weights. They can therefore be optimized together with the exact
low square using epigraph constraints; (SH9) permits a linear
fractional transformation. The original high residues remain arbitrary.
This establishes a finite optimization route at unrestricted 3/5/7
heights, without importing uniform-density bounds into a changed law.

`verify_saturated_height.py` reconstructs the adjacent
`saturated_height_certificate.json` with exact standard-library arithmetic.
It checks six finite height boxes and 384 kernel entries by direct
exponent summation, both product and restricted-family evaluations
of (SH7), the twelve/144 regrouped coefficients, and three actual CRT
families of period 33075. The CRT cases check lifted moments, centering,
hinges and conditioning; a separate period945 case checks the
relative-position obstruction. The unrestricted-height conclusions
follow from the ordinary arguments above, not from the finite cases.
Run `python3 -I -O docs/reports/erdos7-odd-covering/verify_saturated_height.py`
from the repository root. No new Lean declaration or unrestricted #7
conclusion is supplied by this transfer.
