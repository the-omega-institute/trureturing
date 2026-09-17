[Index](../marked_head_profile.md) · [Previous](21-physical-and-killed-kernel-comparisons-at11-and13.md) · [Next](23-actual-maximizing-tests-constrain-the-killed-pair-matrix.md)

<a id="comparing-the-two-killed-steps"></a>
### Comparing the two killed steps

First change only the17/19 forbidden masks, retaining the full incoming
nu13. Write eta_mask for the resulting killed reference measure.
Triangle comparison and the common-kernel bounds in WT5/APC4 give

    Delta2(eta,eta_mask)<=(59/45)epsilon17,2+epsilon19,2,
    Delta0(eta,eta_mask)<=epsilon17,0+epsilon19,0.       (KC3)

For the first inequality, the17 difference is propagated through the
common reference19 kernel, whose weighted factor is59/45. For the
second, every killed kernel is a positive subprobability kernel and
contracts L1. The19 direct error may be integrated under the full
killed17 input, dominated by the physical source used in KC2. There is
one propagated17 mass error, not the two appearances arising when
separate physical-prefix assigned charges are compared.

For positive measures sigma,tau and any L>=1,

    |Q_sigma(L)-Q_tau(L)|
       <=integral(L^2-1)d|sigma-tau|
                           +483|sigma(1)-tau(1)|
       <=Delta2(sigma,tau)+483 Delta0(sigma,tau).       (KC4)

Consequently the mask part of the Q error is

    e_mask=(59/45)epsilon17,2+epsilon19,2
                          +483(epsilon17,0+epsilon19,0).

At box20/current8 it is0.0004651201891079085..., with only
0.000012270638551024422... from the mass term. This comparison neither
changes nor contradicts the earlier APC error for its different
physical/assigned-charge functional.

<a id="replacing-the-incoming-law-and-retaining-the-complete-test-box"></a>
### Replacing the incoming law and retaining the complete test box

Now replace the incoming probability by the actual AP13 law nu_B of
its retained original five-prime family. Construct it by precisely the
same uniform357, AP11/T4, AP13/T6 and one-conditioning rule. Keep the
reference17/19 kernels fixed. APC2--APC5 give

    Delta2(nu13,nu_B)<=eNw,
    Delta0(nu13,nu_B)<=eNm,                           (KC5)

also for unequal B, replacing each product cutoff by b_q and using
b11,b13 as the respective current cutoffs. Both full and core laws
have the same HC lower normalizer and upper square bound. Uniform
padding to a common physical period preserves the construction.

For a fixed common killed continuation, the weighted difference in
final square integrals is at most

    (89/64)(59/45)eNw=(5251/2880)eNw.

Its final survival probability, as a function of the incoming point,
is a fixed h with0<=h<=1. The two incoming measures are probabilities,
so their difference has total mass zero. Therefore

    |eta_mask(1)-eta_core(1)|<=eNm/2.

Using the raw form Q=integral L^2-484 mass gives the sufficient incoming
error

    e_incoming=(5251/2880)eNw+242eNm.                 (KC6)

There is no assumption that either final killed mass is positive. In
particular nu_B need not avoid omitted full-family constraints; their
effect is already included in KC2 and KC5.

Finally keep every original test label in the chosen seven-prime box H.
The final reference killed law is bounded by its physical law of Haar
density at most(18/5)D. The complete two-test tail gives

    e_test=(18/5)D {product_p p(p+1)/(p-1)^2
               -product_p[1+sum_(a=1..h_p)(2a+1)p^-a]}. (KC7)

Every omitted ordered test pair is included. For one original complete
layout, restrict its labels to the box, without altering any retained
residue. Then

    Q_actual(L)<=Q_core(L_box)+e_mask+e_incoming+e_test. (KC8)

If an actual exponent is smaller than a listed cutoff, use the
intersection with its inventory and uniform padding. Larger finite
exponents are paid by the full tails. Original forbidden and test
labels remain distinct throughout the comparison.

<a id="two-fully-specified-finite-cores"></a>
### Two fully specified finite cores

In the following table the five-prime incoming core and each old-
cofactor box use the corresponding entries of H. Pure and mixed current
cutoffs are listed separately. The full finite reference is the actual
AP construction for those retained original residues, followed by the
two specified reference kernels, and the complete test box H.

|H, ordered by3,5,7,11,13,17,19|current17/19|complete test labels|total Q error|safe allowance|
|---|---|---:|---:|---:|
|`(20,20,20,20,20,20,20)`|`(8,8)`|1801088541|0.0006664579809979847...|0.000667|
|`(17,10,8,7,6,6,6)`|`(6,6)`|4889808|0.2563651750935413...|0.263|

Thus the finite sufficient condition is

    Q_core(L_box)<=-safe_allowance                  (KC9)

for every retained original family pattern and every complete box test.
The error is strictly below its safe allowance, so KC8 then makes every
full Q strictly negative and KC1 gives positive survival and square<484.
KC9 itself has not been proved or evaluated uniformly.

The second core has at most99791 old five-prime forbidden labels,
598752 labels whose largest prime is17, and4191264 whose largest prime
is19:4889807 in total. Adding the test unit gives4889808. Its common
period may be taken as

    3^17*5^10*7^8*11^7*13^6*17^6*19^6
     =776550560750774609700229544439786533325582744140625.

This remains a51-digit period, and the number of residue assignments is
not asserted small. The core is a feasible cutoff choice, not a proof
of optimal cutoffs or feasible exhaustive enumeration.

<a id="a-source-square-hinge-observation-with-full-comparison-tails"></a>
### A source square-hinge observation with full comparison tails

For the same actual supported13 law define

    T13(tau)=sup_A E_nu13(A^2-tau)_+.

For each of the twelve PR original-root branches, let u3,u5,u7 and
D_branch be its certified reference pure masses and actual uniform357
Haar-density bound. Use independent comparison counts with caps

    (c3,c5,c7,c11,c13)=(1/u3,1/u5,1/u7,5/3,2),
    Pr(Xp=1)=1-cp/p,
    Pr(Xp=n)=cp(p-1)p^-n, n>=2.

Let M be their product. The nonnegative increasing convex function
(z^2-tau)_+ permits the PR restriction to the actual pure reference,
the complete labelled AP11/13 comparison, and finally division by the
same HC retained mass r. Hence

    T13(tau)<=max_branch (D_branch*u3*u5*u7/r)
                                      E(M^2-tau)_+.  (KC10)

The old uniform law is never replaced by a different supported law.
The comparison variables are independent; the actual forbidden events
need not be. For integer tau>=1, the entire product tail is evaluated
by the exact identity

    E(M^2-tau)_+=E M^2-tau
                    +sum_(n^2<tau)(tau-n^2)Pr(M=n),
    E M^2=product_p[1+cp(3p-1)/(p-1)^2].

All omitted product probabilities are accounted for by the full second
moment. Checking all twelve branches gives

    T13(81)<=27462732511027063792077002926276002
                    /234516374824438312292389830652525
             =117.10368852318302...,
    T13(1024)<=29.592792472449865... .                (KC11)

The largest value in each is the effective9 branch with5 and7 present.
Appending a complete cap2 comparison factor X17 gives, for the
unconditioned physical mu17=nu13 K17,

    sup_A E_mu17(A^2-1024)_+<=64.10180348992289... .

The bounds also apply to the core's actual AP13 source and its
normalized reference17 continuation: these are members of the same
arbitrary-family and cap-bounded construction. No conditioned single17
law is inserted.

<a id="a-killed-pair-frontier-that-retains-actual-testmask-overlap"></a>
### A killed pair frontier that retains actual test/mask overlap

For one globally fixed complete current test, index its original labels
by ell,k. Let C_ell,C_k be their old test cylinders and I_ell,k their
current-prefix intersection. Let m_x be the actual pure base, B_x the
actual mixed forbidden union, alpha_x=m_x(B_x), and

    a_x=1/(1-min(alpha_x,delta)).

The exact killed pair entry under old input sigma is

    P^-_(ell,k)=E_sigma[1_(C_ell intersect C_k)(x)
                         a_x m_x(I_ell,k outside B_x)]. (KC12)

Summing every ordered pair gives the killed square of that fixed test.
If b_x is the physical bad-side density, the physical entry exceeds
KC12 by exactly

    E_sigma[1_(C_ell intersect C_k) b_x m_x(I_ell,k intersect B_x)].

In PO notation b_x=g_x-h_x; here b means the bad-side density itself.
This avoids identifying two different coefficient conventions. The
actual overlap can vanish; no uniformly increased killed floor is used.

Let Xi_p^-(sigma) be the supremum of the sum of KC12 over pairs with
at least one positive current exponent, over globally legal complete
tests. Each original old block and current residue remains independent
of the forbidden layout. Set F_p^-(W;sigma)=W b_p+Xi_p^-(sigma), where
b_p is the assigned bad mass under the normalized physical input.
For0<=tau<=484 and W=484-tau,

    Q_eta(L)<=T13(tau)-W
                   +F17^-(W;nu13)+F19^-(W;mu17).      (KC13)

To prove this, expand L^2=A13^2+R17+R19, where R17 contains the ordered
pairs in the19-zero block with a positive17 exponent and R19 contains
pairs with a positive19 exponent. Both R terms are nonnegative. Since
eta17<=mu17 and every killed kernel has mass at most1, their integrals
are bounded by the respective Xi17^- and Xi19^-. The marginal of eta
through13 is dominated by nu13. Thus integral(A13^2-tau)d eta<=T13(tau).
Finally eta(1)>=1-b17-b19, and W>=0. These give KC13. Its two independent
suprema need not be attained by one common test; they are upper bounds
for the one test used in the expansion.

For each finite core, F17 here uses nu_B and its reference K17; F19
uses the normalized physical input mu17,B=nu_B K17, not killed or
conditioned17. Both Xi suprema use every complete test label in that
row's box H. In particular the uniform row retains test depths20 even
though the two current forbidden-mask cutoffs are8.

Taking tau=81,W=403, KC11 and the two safe allowances give sufficient
finite reference bounds, respectively,

    F17^-(403)+F19^-(403)<=285.895  [box20/current8],
    F17^-(403)+F19^-(403)<=285.633  [the unequal box].   (KC14)

For each row these constants are strictly smaller than403-T13(81)
minus its safe allowance. Therefore KC13 implies KC9. Neither frontier
bound is supplied by the tail computation.

<a id="pointwise-clipped-covariance-and-its-exact-scope"></a>
### Pointwise clipped covariance and its exact scope

A relaxation of Xi^- keeps

    J_p(sigma)=sup_A E_sigma[kappa_p(alpha) A^2],
    kappa_p(alpha)=((p-1)/(p-2))/(1-min(alpha,delta)).

The killed current-prefix mass is bounded by the same physical cap.
Weighted Cauchy--Schwarz for every pair of independent old blocks then
gives Xi_p^-(sigma)<=a_p J_p(sigma), with

    a17=25/128, a19=14/81.

Keeping J_p retains the cap covariance discarded in SH26. If this is
further bounded with the existing common-vector clipped cost H_K,
K=1024 is admissible at W403: its required thresholds a_p K c_p are
400 and14336/45, both below403. This is a pointwise stronger majorant
than SH27's unit-floor cap replacement; no universal strict numerical
improvement of the subsequent auxiliary comparison is asserted.

For the original row variables, the loss from clipping y^2 at1024 is

    a_p(c_p-kappa_p(alpha))(y^2-1024)_+.

Since kappa_p>=(p-1)/(p-2), its expectations under nu13 at17 and mu17
at19 sum to at most

    (35/192)T13(1024)
       +(98/765)sup_A E_mu17(A^2-1024)_+
          =13.606253764407912... <13.607.              (KC15)

This controls the pointwise original-row clip loss only. It does not
bound the additional errors of comonotone comparison, Jensen,
independently maximizing layouts, or every relaxation of KC14. The
actual joint frontier still requires its own upper bound.

The proof reuses PR, HC, APC, WT, PO and the existing H_K comparison;
it adds no Lean wrapper or formalization claim. Its exact verifier
checks the complete geometric tails, twelve root branches, both finite
reference specifications and all rational budget comparisons. Ordinary
proofs and certificates do not settle the unrestricted problem.

The [killed-core verifier](../verify_killed_core_continuity.py) reconstructs
the [full-tail certificate](../certificates/killed_core_continuity_certificate.json). It
pins the existing HC, PR and APC sources. Default mode compares every
field; `--write` regenerates. Numeric, duplicate-key and source-hash
changes are rejected under `python3 -I -O`.

<a id="shared-actual-cell-square-hinges-improve-the-same-ap13-law"></a>
## Shared actual-cell square hinges improve the same AP13 law

For the same actual supported AP(4,6)13 probability used in HC9, SP4 and KC, every complete original test obeys

    E L^2 <= 148878188597300778613/914721425816667898
          =162.75795493079391...,
    E(L^2-81)_+
       <=7950179084001887172777104410541784715667
          /76933096761156988347518483945560826250
        =103.33886738868257... .                         (SQ1)

The previous observations were170.9755187952681... and117.10368852318302..., respectively. The probability itself is unchanged: start with uniform actual357 survivors, apply the original pure-survivor AP11/T4 and AP13/T6 kernels, and condition once on all actual survivors. Its same HC lower normalizer is

    r=18925009844347/38266567762500.

All residues, missing classes, complete original labels and arbitrary finite heights remain in the domain. These are ordinary full-tail and continuous-parameter bounds, not exact maxima over actual families or Lean declarations.

<a id="reuse-of-the-actual-five-cells"></a>
### Reuse of the actual five cells

In the effective3/9 case use HC's five cells, roots r(l)=(0,0,1,1,1), and exactly its parameter domain

    w_l=1-D_l, D>=0, sum D<=1/2;
    alpha>=0, sum alpha<=1/4;
    beta>=0, sum beta<=1/4;
    t>=0, sum t<=1/72; 3/4<=z<=1.

Set d_l=z-alpha_r(l)-beta_l, n_l=w_l d_l/9-t_l, s=sum n_l and x=sum w_l/9. The raw complete35 cell masses are n_l; a depth-a ternary query in cell l has raw mass at most d_l 3^-a. The actual pure3 measure has masses w_l/9 and depth caps3^-a. Reuse the same-family mixed7 bound T from HC7, so its retained denominator is s-T/5>0.

For a fixed original root/cell choice c=(r,j), write b_l=1+1_(r(l)=r)+1_(l=j). For any nondecreasing cost g define exactly HC's monotone bound

    Delta_a(g,b)=max_(0<=i<=a-3)[g(b+i+1)-g(b+i)],
    P_g(c;m,v)=sum_l m_l g(b_l)
                +sum_(a>=3)3^-a max_l[v_l Delta_a(g,b_l)].

It follows by adding the original depth-a indicator: on its cylinder the previous deep count lies between0 and a-3. This requires neither convexity nor coherent nesting of the original ternary prefixes. Let P^A_g use masses n and caps d, and P^eta_g use masses w/9 and caps1. Constants integrate exactly. Inactive root/cell test choices are completed to active ones, increasing the load; no forbidden residue is changed.

<a id="square-cost-positive5-increment-and-its-complete-tail"></a>
### Square-cost positive5 increment and its complete tail

Let f_tau(v)=(v^2-tau)_+ for tau>=0. It is nonnegative, increasing and convex for v>=1. HC1's actual-zero-block decomposition remains valid for this cost. For a positive5 multiplier n>=2, Jensen gives

    f_tau(A0+...+A_(n-1))-f_tau(A0)
      <=g_n(A0)+(1/n)sum_(e=1)^(n-1)f_tau(n A_e),
    g_n(v)=f_tau(nv)/n-f_tau(v).                       (SQ2)

The cost g_n is nonnegative and nondecreasing. Below sqrt(tau)/n it is0, between sqrt(tau)/n and sqrt(tau) it is n v^2-tau/n, and above sqrt(tau) it is (n-1)v^2+tau(1-1/n). Its derivative is nonnegative on each interval, and it is continuous at both endpoints. It need not be convex, so its finite-n terms use the monotone P_g formula, not a convex specialization.

The complete raw35 upper bound is therefore

    F_tau=max_c {P^A_f_tau(c)
       +sum_(n>=2)4/5^n [P^eta_g_n(c)
            +(n-1)/n max_d P^eta_(f_tau(n .))(d)]}.     (SQ3)

The same original zero5 choice c stays outside the whole sum. Positive blocks may be maximized independently only as an upper bound. The raw probabilities4/5^n arise from the actual pure5 prefix comparison, with its pure mass canceling exactly as in HC2-HC3.

Put Q_c=P^eta_(v^2)(c), Qmax=max_c Q_c, E_c=P^eta_f_tau(c), and

    N=max(2,ceil(sqrt(tau))+1).

For every integer n>=N and integer v>=1, f_tau(nv)=n^2 v^2-tau. Also g_n has nondecreasing integer increments: every second integer difference of f_tau is at most max(2,2ceil(sqrt(tau))+1), whereas that of n v^2 is2n. Thus the running maximum in Delta_a occurs at its last increment. Since all eta depth caps equal1, the largest b_l maximizes the increments of g_n, f_tau and v^2 simultaneously. Consequently

    P^eta_g_n(c)=n Q_c-E_c-(tau/n)x,
    max_d P^eta_(f_tau(n .))(d)=n^2 Qmax-tau x.

The complete n>=N portion inside SQ3 is exactly

    5^(1-N)[(N+1/4)Q_c
       +(N^2-N/2+1/8)Qmax-E_c-tau x].                (SQ4)

It uses the full geometric mass, first moment and second moment. Taking only n>=ceil(sqrt(tau)) would not justify the discrete-convex specialization at the boundary; the finite preceding terms are retained in SQ3.

<a id="every-original-ternary-height-is-paid"></a>
### Every original ternary height is paid

For f_tau, Delta_a is its last increment because the cost is convex. Once b+a-3>=ceil(sqrt(tau)), that increment is2a+2b-5. At a fixed parameter vertex the tail integrand is therefore the maximum of five affine functions d_l(2a+2b_l-5). Choose its eventual line by largest slope and then largest intercept, and start the tail only after it dominates every other line. This finite crossing calculation proves the entire subsequent envelope, not merely a sampled range.

For a finite g_n term, once the queried integer is above sqrt(tau), its increment equals(n-1)(2a+2b-5). The verifier extends its finite prefix until this current increment dominates every preceding increment for every present b. The later increments strictly increase, so that condition remains true forever. Equal eta caps then select the largest b.

In both cases the remaining exact affine tail uses

    sum_(a>=A)3^-a = 3^(1-A)/2,
    sum_(a>=A)a 3^-a = (2A+1)/(4*3^(A-1)).

Thus no original height is hard-truncated. The finite checks establish entrance into a proved affine tail; they do not replace an infinite probability law by a normalized finite sample.

<a id="the-complete7-comparison-and-actual-conditioning"></a>
### The complete7 comparison and actual conditioning

Use HC6's full pure7 comparator, with probability29/35 at1 and36/(5*7^n) at n>=2. Since f_tau(nv)=n^2 f_(tau/n^2)(v), put M=max(2,ceil(sqrt(tau))). The raw cost before actual mixed7 deletion is bounded by

    B_tau=(29/35)F_tau
       +sum_(2<=n<M)36 n^2/(5*7^n) F_(tau/n^2)
       +(36/5)[F_0 sum_(n>=M)n^2 7^-n
                       -tau s sum_(n>=M)7^-n].       (SQ5)

For the last term tau/n^2<=1 and v>=1, so F_(tau/n^2)=F_0-(tau/n^2)s exactly. This equality follows from SQ3's exact treatment of constants; the positive5 increment of a shifted square is unchanged.

All added costs are nonnegative before expansion. Discarding the mixed7 union therefore gives the valid uniform357 bound B_tau/(s-T/5). This uses the original actual deletion union and the same denominator; it does not replace the conditioned marginal by a product law.

For any proposed constant C, the target margin C(s-T/5)-B_tau is separately concave in D,alpha,beta,t,z. Each branch of P^A is affine separately in those groups. All maxima have nonnegative coefficients. The negative tail term involving E_c in SQ4 is affine in w for its fixed zero5 choice, while the negative multiples of s in SQ5 are separately affine. Repeated vertex interpolation therefore reduces the whole continuous parameter domain to exactly6*3*6*6*2=1296 product vertices.

For each needed tau, the verifier evaluates the infinite-tail expressions at every vertex and takes the largest ratio. These shared-cell bounds cover all four effective9 missing5/7 branches. For each of the other eight branches it uses PR's actual pure-reference product comparator. In every branch that fallback for the square hinge is evaluated from its full second moment plus the finite correction at integer products m with m^2<tau. The resulting twelve upper bounds are all included. Finally the pointwise unit-floor inequality

    (L^2-tau)_+ <= L^2-min(tau,1), L>=1

permits taking the minimum with G-min(tau,1), where G=3849/106 is the established same-law uniform357 square bound. Denote the resulting simultaneous source observation by H357^(2)(tau).

<a id="the-same-physical-ap1113-chain-and-one-final-normalization"></a>
### The same physical AP11/13 chain and one final normalization

Let N=N11*N13 use the unchanged complete comparison factors with caps5/3 at11 and2 at13. They are auxiliary counts, not independent actual forbidden events. For tau=h^2,

    U2(tau)=sum_(n<h)Pr(N=n)n^2 H357^(2)(tau/n^2)
                  +G E[N^2;N>=h]-tau Pr(N>=h)         (SQ6)

bounds every physical13 square hinge. The high-n formula is exact for its bounding costs because tau/n^2<=1. Both tails are obtained by subtracting finite parts from the full probability1 and

    E N^2=(23/15)(55/36)=253/108.

The same original labelled AP comparison proves SQ6 before the sole conditioning. Nonnegativity then gives T13(tau)<=U2(tau)/r. The pointwise inequality L^2<=tau+(L^2-tau)_+ gives the further same-law observation

    Gamma13 <= tau+U2(tau)/r.                         (SQ7)

At tau16 the exact physical bound is2899096118869109/39943338435000, and SQ7 yields the first result in SQ1. At tau81 the exact physical bound is7950179084001887172777104410541784715667/155559525971351670013360122780046875000, yielding the second result in SQ1. No global optimization over all real shifts is claimed; tau16 is a sufficient witness. The stronger square observation changes neither the underlying kernels nor the HC charge and Haar-density observations.

The adjacent verifier checks both1296-vertex targets, all12 missing-class branches, the complete geometric and AP tails, and exact rational comparisons with the prior constants. It pins the existing pure-root and shared-cell-hinge certificates by SHA-256 and compares its complete output certificate. Run it with `python3 -I -O`, supplying `--source-directory` if its pinned inputs are elsewhere. This result does not prove the finite17/19 joint frontier or the unrestricted covering statement.

<a id="complete-continuations-and-the-larger-killed-frontier-allowance"></a>
### Complete continuations and the larger killed-frontier allowance

The new square observation and the earlier SP profile hold on the same
actual AP13 probability. For every positive integer h retain

    H13(h)<=min(SP_H13(h),(Gamma13-1)h/(4h^2-1)).

Reuse SP's complete auxiliary first-moment tails and fixed scalar-cost
formula with this stronger square input. Exact rational evaluation gives

    Gamma17<=9720067404606638015016317/25298087377147529307792
             =384.22143380637726...,
    Gamma19<=1947596368885525589065961707/873442090069958182244328
             =2229.7945004339476... .                 (SQ8)

The first bound uses a single AP17/T8 step. The second starts again from
supported13, applies normalized physical AP17/T8 and AP19/T8 kernels,
and conditions only after19. Both give positive survival by the SP
sufficient criterion. The single17 conditioned output is not inserted
in the two-step chain. Every original residue and finite height remains
allowed on the stated prime support.

The255 integer restart schedules1<=T17<=15,1<=T19<=17 still all have a
positive W483 defect for this upper functional. Its least value is
228.60653787361616... at T17=6,T19=8. This is a limitation of that
functional, not a lower bound on actual test moments. No different-law
PG1 observation is used by the reused generic helper.

The actual AP probability and KC reference constructions are unchanged,
so the earlier KC safe error allowances remain valid. Substituting the
stronger T13(81) into KC13 yields these sufficient finite bounds:

    F17^-(403)+F19^-(403)<=299.660  [box20/current8],
    F17^-(403)+F19^-(403)<=299.398  [the unequal box].   (SQ9)

They are strictly below403-T13(81) minus the respective KC safe allowance.
The available exact budgets are299.6604656113174... and
299.3981326113174... . The two finite frontier inequalities themselves
remain unproved; the extra allowance is not a computed saving in F.

The [shared-cell square verifier](../verify_shared_cell_square.py) checks
the [SQ certificate](../certificates/shared_cell_square_certificate.json), and the
[continuation verifier](../verify_shared_square_continuation.py) checks
its [same-law consumers](../certificates/shared_square_continuation_certificate.json).
They retain complete tails and pinned source identities. No Lean
formalization, actual-family sharpness or unrestricted resolution follows
from these ordinary proofs and exact arithmetic checks.

<a id="common-original-prefixes-across-depths-from-rro55"></a>
## Common original prefixes across depths from RRO55

The ordinary cross-difference construction in RRO55.2--55.5 supplies
an exact extension of CR1 for fully specified finite prefix observations.
It is reused here for the original-label interface, without a new Lean
wrapper. The finite criterion excludes joint patterns that independent
per-depth checks admit; it does not evaluate the killed objective.

<a id="finite-prefix-criterion"></a>
### Finite prefix criterion

Fix a prime p and two sets of distinct original labels L,R. First suppose
all labels are read to a common finite height H. Let

    E_t(i,j)=1 iff a_i=b_j mod p^t, 0<=t<=H.

These bits concern the same a_i,b_j at every depth. E0 is complete and
E_(t+1)<=E_t. At each t, every component with an edge in the bipartite
graph E_t must be complete bipartite. For each such component C, let
c be the number of edge-containing components of E_(t+1) restricted to C,
and let iL,iR indicate isolated vertices on its two sides. Then

    c+iL+iR<=p.                                       (CR2)

All vertices in C share one p^t-prefix, which has only p next digits.
Different mixed child components need different digits. Left-only and
right-only isolated groups, if present, require separate digits outside
the mixed groups. This proves necessity. Conversely, assign different
digits to these groups and recurse inside mixed groups. Same-side
isolated vertices can share all remaining digits because no cross
condition connects them at greater depth. After H steps this constructs
one simultaneous mod p^H witness for the complete prefix data. Equality
at H means only congruence modulo p^H; no infinity label is asserted.

This is the finite-prefix specialization of
[RRO55.2--55.5](https://github.com/the-omega-institute/trureturing/blob/ba8142cf990037c2af6a709ac82d6769cd0381e2/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L23169).
Its exactness concerns this free cross-prefix realization problem.
Pinned residues, activation constraints, old-cofactor compatibility and
source-law conditions are additional constraints and remain attached.

At depth1 the effective alphabet is p-1 when a pure root is removed,
and p when it is absent, as in CR1. Inside a specified retained root,
the generic next-digit bound is p. Further pure restrictions may reduce
the available set; one cannot automatically use p-1 at every depth.

<a id="strict-separation-from-independent-depth-cr1"></a>
### Strict separation from independent-depth CR1

Take p=3, six labels L0,L1,L2,R0,R1,R2, each of height2. Require all
nine cross pairs equal modulo3. At modulo9 require just L0=R0 and
L1=R1, and require the other seven cross pairs unequal:

    E1 = [1 1 1]       E2 = [1 0 0]
         [1 1 1]            [0 1 0]
         [1 1 1]            [0 0 0].                  (CR3)

E1 independently uses one root. E2 independently uses four roots: two
matched pairs plus one left isolate and one right isolate. Even after
removing root0, the depth2 alphabet has6 residues, so both independent
CR1 tests pass. Explicit independent witnesses are all roots1 for E1,
and L=(1,2,4), R=(1,2,5) modulo9 for E2; all six are nonzero modulo3.

Together E1 forces all vertices into one mod3 root. Inside it E2 needs
four distinct children although only three exist. Thus CR2 rejects the
array. In valuation language its diagonal observations are **at least2**
and all other entries are **exactly1**. It neither requires nor assumes
an exact valuation2 on the two diagonal pairs.

The [prefix verifier](../elementary-checks/verify_prefix_obstruction.py) independently enumerates all729 choices
of the six next digits under the common root1, finding no witness.
Every one-label deletion has a genuine modulo9 witness, retained in the [prefix certificate](../certificates/prefix_obstruction_certificate.json).
The ordinary pigeonhole proof above is independent of that finite check.

For arbitrary p, the analogous obstruction has p labels on each side:
one common parent, p-1 matched diagonal child pairs, and all remaining
cross child pairs unequal. It requires p+1 children. This is F_(p,t)
from RRO55.5; it uses2p labels regardless of the depth t.

For an integer-programming relaxation, write z_ij=E_(t+1)(i,j) and
x_ij=E_t(i,j). On the selected p-by-p submatrix one valid linear cut is

    sum_(i=1..p-1) z_ii + sum_(other pairs)(1-z_ij)
       <=p^2-1 + sum_(all pairs)(1-x_ij),             (CR4)

where the first sum contains exactly p-1 diagonal entries. If all parent
bits are1, the forbidden child pattern cannot have score p^2. If any
parent bit is0, the right side is at least p^2 and the inequality is
trivial. All variables refer to the same original labels across depths.

<a id="unequal-original-heights-and-shared-contexts"></a>
### Unequal original heights and shared contexts

An original label of height h carries a residue only modulo p^h. Two
labels of heights h,k have actual cylinder overlap according to equality
modulo p^min(h,k). Prefix observations exist only to this minimum height.
An observed first split below that height fixes a finite valuation; a
match at the minimum height gives a lower bound, not equality to infinity
and not a chosen finite valuation.

For unequal heights the exact feasibility question is therefore an
**interval/partial-prefix completion** problem. Unobserved deeper entries
remain unknown. CR2 or CR4 may reject a candidate only when the required
parent equalities and child equalities/inequalities are actually forced.
Alternatively, one can seek a full nested prefix completion respecting
all observed intervals and then apply the constructive finite criterion.

An auxiliary extension of a shallow residue used in such a feasibility
argument must not replace its cylinder by a single high-level leaf in
the killed calculation. The original cylinder is the union of all its
extensions and retains its original mass and AP weight. Distinct
original moduli stay distinct even when their prefixes coincide.

The2p induced-obstruction bound is for a **complete specified** cross
array. It is not an automatic bound for arbitrary partial input. For
example, a long even cycle with equality constraints on all but its
closing edge and an inequality on that edge is inconsistent, while
every proper induced restriction of those partial constraints is
consistent. Missing chords must not be interpreted as nonedges.

For the killed frontier, use one master prefix variable for each
original label and prime, reused across source cells, masks and test
blocks. A label may be active in several cells, but its original residue
cannot be reselected separately in each. The local graph cuts are
necessary restrictions on that common assignment. They do not by
themselves compute the same-law killed expectation, preserve all
test-test/source interactions, or prove the required484 barrier.

The source is RRO55 at devba8142cf990037c2af6a709ac82d6769cd0381e2.
The compared dev increment adds no D5 declaration for this criterion.
Dovgoshey--Petrov, [Subdominant pseudoultrametric on graphs,
Lemma2.1 and Theorem3.3](https://arxiv.org/html/1110.6802v1), supplies
the repeated cycle extremum condition for pseudoultrametric extension;
it does not impose the p-child capacity. Bradley,
[From image processing to topological modelling with p-adic numbers,
Section2](https://www2.ipf.kit.edu/Personen/bradley/CV/hier2vis.pdf),
describes the p residue children of a p-adic disk. Neither reference
supplies a weighted covering-system positivity bound.

<a id="translated-observations-and-shared-inputs-from-rro56-and-rro57"></a>
### Translated observations and shared inputs from RRO56 and RRO57

The relevant new interface is a joint observation of the same actual
point. [RRO57.10--57.14](https://github.com/the-omega-institute/trureturing/blob/902112b9c6e74cf8232c2f30962db749ac6ac573/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L24478)
distinguishes exact translated observations, shared representatives and
independent resampling. It supplies an observation design for KC; it
does not supply its missing numerical inequality.

For a fixed original congruence label i with modulus
m_i=product_p p^e(i,p) and fixed residue a_i, its indicator is exactly

    I_i(x)=product_(p dividing m_i)
                1_{v_p(x_p-a_i)>=e(i,p)}.             (TC1)

Only the truncated valuation min(v_p(x_p-a_i),e(i,p)) is needed. The
representative a_i is a fixed constant, and each occurrence reads the
same x. To use RRO57.11's nonnegative queries, choose0<=n_i<m_i with
n_i=-a_i modulo m_i; x+n_i has the same required truncated valuations.
This identity is independent of the probability assigned to x.
For finite periods it is simply the CRT membership test, including all
extensions of each original cylinder. RRO57.11 also shows how a finite
set of translated valuation queries recovers the full residue modulo
any specified finite period. That is a sufficient representation, not
a compression theorem or a uniform finite state for every period.

In particular the killed entries

    P_ij=integral I_i I_j d eta                        (TC2)

must use the one fixed actual killed measure eta. Before integration,
the test indicators, original forbidden indicators, actual union mask
and pure-prefix normalization all share their actual coordinates and
context. Retaining their separate distributions, or even a chosen
collection of pair distributions, does not authorize replacing their
joint law by a product. A repeated original label is one input reused,
not an additional sample. Its literal residue cannot be reselected in
different old rows, test pairs or auxiliary branches.

This requirement is substantive for the row factor
g_x=1/(1-min(alpha_x,delta)): alpha_x is the actual union mass in that
same old row. Thus evaluating g_x, the surviving test intersection and
the row weight requires their common context. The already retained
KC pair formula provides this exact evaluation. TC1 identifies finite
queries from which the underlying membership data can be obtained;
it does not replace the union by a sum or remove the incoming AP law.

[RRO56.6--56.7](https://github.com/the-omega-institute/trureturing/blob/902112b9c6e74cf8232c2f30962db749ac6ac573/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L23844)
allows resampling an intermediate orbit in an independent expression
tree under its stated invariant-law hypotheses, but gives a strict
failure for reused inputs: three pairwise independent outputs can
assign zero mass to an event to which the product of their marginals
assigns1/8. RRO57.14 further distinguishes a complete joint law of
valuation labels from the coupling of representatives within those
labels. Neither result establishes Haar invariance of the present
AP13 law or conditional independence of its source, masks and tests.
The Haar orbit convolution is therefore a separate construction and
is not substituted for nu13 or normalized physical mu17.

The finite core can consequently use TC1 jointly with CR2--CR4 and
actual row weights. Full translated observations would recover the
entire finite problem. Selecting a smaller collection that proves the
KC bound remains open. In particular these representation results
alone neither exclude every abstract scalar load law nor establish
the sufficient299.398 frontier. The source increment at dev902112b9c6
adds theory and digestion atoms, with no D5, Blueprint or frozen-state
changes relative to devba8142cf99. This application is an ordinary
mathematical explanation, not a new Lean result.
