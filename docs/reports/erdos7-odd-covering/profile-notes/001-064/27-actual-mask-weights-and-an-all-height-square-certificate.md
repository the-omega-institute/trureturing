[Index](../../marked_head_profile.md) · [Previous](26-conditional-head-deletion-with-a-priced-arbitrary-cofactor-tail.md) · [Next](28-zero-local-losses-do-not-imply-a-common-maximizing-original-layout.md)

<a id="actual-mask-weights-and-an-all-height-square-certificate"></a>
### Actual mask weights and an all-height square certificate

Ordinary proof with exact rational coefficient checks; no Lean verification.
Fix the actual killed19 input sigma=xi=nu13 K17^- and R=K19^-, so eta=sigma R.
The following argument also applies to any finite actual old measure sigma
and current prime p>=3 with row mass q and nonnegative prefix cap c satisfying
0<=q<=c. Neither input is normalized or replaced by the physical17 law.
For the actual flat killed row, R_x=c(x)1_(G_x)u_p; here c includes the actual
pure-survivor density, and q/c is its actual surviving Haar fraction.

Let D be the complete original old-test domain, with all divisor labels and
independently chosen original residues. For any nonnegative old weight f, put

    G(f)=max_(A in D) integral f A^2 d sigma,
    d_f(A)=G(f)-integral f A^2 d sigma.

Set S=1/(p-1), a=(3p-1)/(p-1)^2, b=a-S=2p/(p-1)^2,
theta=1/(2+S), and h=c-q. Choose 0<=r<=theta and define

    lambda=S/(S+r), rho=1-lambda, k=rho/theta, kappa=S k,
    w=c-theta h, v=q+lambda h,
    g=q+S c+r lambda c h/v, z=c/v.               (MW1)

The quotients are defined as0 on c=0, where every weighted term vanishes.
For c>0, v>=lambda c>0. In particular g,w,v are nonnegative and

    g<=q+Sc+rh<=(1+S)c,  w<=c,  k<=2+S.

Every original full test then satisfies the general bound

    integral L^2 d(sigma R)<=U_r,
    U_r=G(g)+(b-kappa)G(c)+kappa G(w).           (MW2)

At r=0 this is exactly the ordinary split cap
G(q+Sc)+b G(c). Thus minimizing U_r over its allowed parameter never worsens
that cap. No domination of the stronger OBE distance-profile bound is asserted.
The new observations are actual mask-weighted old square maxima, not another
encoding of the source-only scalar moments.

<a id="exact-identity-and-its-retained-losses"></a>
#### Exact identity and its retained losses

Write A_e for the literal old block of a full test at current exponent e,
including A_0. For finite actual current height H, the original prefix caps give

    integral L^2 d(sigma R)<=Phi_H,
    Phi_H=||A0||_q^2
      +sum_((e,f)!=(0,0),0<=e,f<=H) p^-max(e,f)<Ae,Af>_c.

This cap includes independent original current prefixes; it does not suppose
that they are compatible. Extend only the comparison sequence by A_e=A_0 for
e>H. It does not add original forbidden or test labels. The extra tail is

    Phi_infinity-Phi_H
      =p^-H[2S sum_(e=0..H)<Ae,A0>_c+(a-2S)||A0||_c^2]
      <=p^-H(a+2HS)G(c).                        (MW3)

It is nonnegative. Polarization, with s_e=p^-e and t_e=e+1+S, gives

    Phi_infinity=||A0||_(q+Sc)^2+sum_(e>=1)s_e t_e||Ae||_c^2
      -sum_(e>=1)s_e||Ae-A0||_c^2
      -sum_(1<=e<f)s_f||Ae-Af||_c^2.

Since r lambda=S rho, v=c-rho h and k theta=rho,

    Sc+g-(q+Sc)=Sc^2/v.

Completing squares pointwise therefore yields the exact nonnegative identity

    U_r-integral L^2 d(sigma R)
      =Lambda(L)+d_g(A0)
       +sum_(e>=1)s_e[(t_e-k)d_c(Ae)+k d_w(Ae)]
       +sum_(e>=1)s_e||Ae-z A0||_v^2
       +sum_(1<=e<f)s_f||Ae-Af||_c^2,            (MW4)

where Lambda=Phi_infinity-integral L^2 d(sigma R)>=0. All infinite
sums converge: the actual old domain is finite and the comparison tail repeats
A0. Also sum s_e t_e=b and sum s_e k=kappa, proving MW2.

The finite part of Lambda is the ordered original-label sum

    integral Ii Ij [c p^-max(ei,ej)-R_x(Ci intersect Cj)] d sigma,

excluding two zero-current labels. A compatible pair pays its actual deleted
prefix intersection; an incompatible pair pays the full cap. The comparison
tail MW3 supplies the rest. Thus MW4 retains both actual mask intersections
and original-test incompatibility on the same law.

If a test has square at least U_r-epsilon, MW4 forces each displayed
nonnegative loss to be at most epsilon. In particular

    sum_(e>=1)p^-e||Ae-z A0||_v^2<=epsilon,
    integral (c^2/v) A0^2 d sigma
      <=(sqrt(G(v))+sqrt(epsilon/S))^2.          (MW5)

The second statement follows from the triangle inequality in the direct sum
of the weighted spaces, using sum s_e=S. This specifies the extra near-maximum
condition: the positive old blocks must approximate the actual row-dependent
amplification z of the same baseline. No assumption of centered maximizers is
made, and a source-only high-energy condition does not supply MW5.

<a id="a-three-value-curvature-alternative"></a>
#### A three-value curvature alternative

Let E(t)=G(c-th), t0=1/(1+S), and define the nonnegative convexity gap

    C=theta E(0)+(1-theta)E(t0)-E(theta).

Here theta=(1-theta)t0. Write
V=(E(0)-E(theta))/theta and U=(E(theta)-E(t0))/(t0-theta).
Convexity and 0<=h<=c give 0<=U<=V<=E(0) and V-U=C/theta^2.
Since g<=q+Sc+rh, interpolation between t0 and theta gives

    U_r<=U_0-r[S V/(S+r)-U].

If V>0 choose r=S(V-U)/(2V), which lies in [0,theta]. The bracket is
at least(V-U)/2. If V=0 then C=0 and use r=0. Consequently, for E(0)>0,

    sup_L integral L^2 d(sigma R)
      <=U_0-S C^2/[4 theta^4 E(0)].             (MW6)

When E(0)=0 the full square is0. This does not assert positive C for every
family. If A_theta maximizes E(theta), then exactly

    C=theta d_c(A_theta)+(1-theta)d_(c-t0 h)(A_theta).

Thus C=0 supplies a common endpoint maximizer, while C>0 supplies the
quantitative saving MW6. Which alternative the actual family realizes remains
part of the joint optimization.

<a id="the-unchanged19-input-and-complete-old-test-tails"></a>
#### The unchanged19 input and complete old-test tails

At p=19 and r=theta=18/37 the weights and coefficients are

    w=(19c+18q)/37,
    g=q+c/18+18c(c-q)/(37c+324q),
    kappa=37/361, b-kappa=865/58482,
    z=361c/(37c+324q).

Therefore

    sup_L eta(L^2-484)
      <=G(g)+(37/361)G(w)+(865/58482)G(c)-484 eta(1). (MW7)

The actual caps c<=9/5 and K17's cap2, together with the existing same-AP13
bound, give

    G(c)<=(9/5)(89/64) Gamma13
      <=119251429066437923669013/292710856261333727360,
    (865/58482)G(c)<6.025855.

The comparison xi<=mu17 is used here only to bound a nonnegative square;
the weighted maxima in MW7 stay under xi. With this cap the coefficient of
C^2 in MW6 is greater than0.0006086; no uniform positive C is established.

For a finite box B in the original old test exponents at primes
P={3,5,7,11,13,17}, keep the actual sigma,c,q completely unchanged and optimize
only the test labels in that box, intersected with the actual inventory.
Write G_B for this maximum. The actual density bound sigma<=110 u_old gives,
for 0<=f<=F,

    0<=G(f)-G_B(f)<=110 F T_B,
    T_B=product_(p in P) p(p+1)/(p-1)^2
       -product_(p in P) sum_(j=0..B)(2j+1)p^-j. (MW8)

Indeed the square difference is a sum of omitted ordered label pairs;
each is at most110 F/lcm(d,e). The full pair sum factors by prime.
Every core assignment extends to the original labels, so the optimization
inequality has the stated direction. The exact single-prime tail is

    p^-B[(2B+3)p-(2B+1)]/(p-1)^2.

Using g<=19/10 and w,c<=9/5, the TOTAL MW7 error is at most

    (2090/9) T_B,
    B16: error<0.000564917,
    B20: error<0.000008522461.                   (MW9)

This truncates the original test inventory only. It does not bound the cost
of replacing forbidden masks or the actual input law by a finite reference.
Those changes still require KC's separate common-law estimates.

Rational upper certificates U_g,U_w,U_c for the three actual box16 maxima
would therefore give

    sup_L eta(L^2-484)
      <U_g+(37/361)U_w+(865/58482)U_c
       +0.000564917-484 eta(1).                 (MW10)

The arbitrary-label message certificates below can bound these weighted
maxima using their own exact unary/pair tables. No uniform such certificates
are currently supplied. MW10, the299.398 frontier and later-prime continuation
remain unresolved; the inequality is a reusable actual-mask reduction, not
an unrestricted #7 conclusion. The standalone verifier checks1296 rational
finite-array identities with complete comparison tails and the exact constants
in MW7--MW9. This is finite corroboration of the ordinary proof, not a kernel
verification of its universal quantifiers.

<a id="same-law-original-label-conflict-cuts-and-rational-message-certificates"></a>
### Same-law original-label conflict cuts and rational message certificates

These are ordinary mathematical results, with exact standard-library certificate checks, not Lean verification. All bounds below apply to the entire final signed objective under one actual killed law. The numerical fixture is evidence of a nonzero cut and an attained message certificate; it is not a uniform improvement to the existing Gamma split, KC299.398, or unrestricted Erdős #7.

<a id="1-general-actual-law-statement-and-original-labels"></a>
#### 1. General actual-law statement and original labels

Fix any finite actual family and one finite nonnegative final measure

    eta = nu13 K17^- K19^- .

At the second step its incoming measure is literally `nu13 K17^-`. Neither the normalized physical input `nu13 K17` nor a fresh supported law is substituted. Let `J` be the complete original divisor-test label set, including the single modulus-one label. Every other original modulus `m_i` has one globally selected residue `r_i mod m_i`, reused in every factor and every old row. Write `I_i=1_(x=r_i mod m_i)`, `L=1+sum_i I_i`, and `z=eta 1`.

The exact full objective is

    Q_eta(L) = eta(L²)-484 z
             = -483 z + sum_i u_i(r_i) + sum_(i<j) v_ij(r_i,r_j),
    u_i(r) = 3 eta C(r,m_i),
    v_ij(r,s) = 2 eta(C(r,m_i) intersect C(s,m_j)).              (LC1)

Every intersection is evaluated on the same eta. Generalized CRT makes it zero when the residues disagree modulo the gcd, otherwise the mass of the unique combined class modulo the lcm. There is no independent choice of a residue for separate entries containing the same label.

Put

    B0(eta) = -483 z + sum_i max u_i + sum_(i<j) max v_ij.

This is the entrywise pair envelope. It is generally different from, and can be weaker than, existing old-block Gamma envelopes.

<a id="2-arithmetic-stars-detect-information-erased-by-separate-pair-maxima"></a>
#### 2. Arithmetic stars detect information erased by separate pair maxima

Choose one original central label d and distinct neighboring original labels m in N. For each central residue a define

    J_m(a) = max_(r mod m) eta(C(a,d) intersect C(r,m)).

For every global test,

    sum_(m in N) 2 eta(I_d I_m) <= 2 max_a sum_m J_m(a).

Consequently the exact lost amount in independently maximizing just these star factors is

    kappa_(d;N) = 2 [sum_m max_a J_m(a) - max_a sum_m J_m(a)] >= 0. (LC2)

This is a quantified constraint on the selected original label, not merely a condition on an abstract Gram matrix. It costs only one table per neighbor and one maximization over residues of d. The result holds for arbitrary actual eta, arbitrary residues, and all finite original heights. No radial symmetry, common center, nested-chain maximizer, or zero charge is assumed.

If d divides m, this simplifies to

    J_m(a) = max_(r mod m, r=a mod d) eta C(r,m).                (LC3)

A version spending the unary factor of d has

    kappa = max_a u_d(a) + 2 sum_m max_a J_m(a)
            - max_a [u_d(a)+2 sum_m J_m(a)].                   (LC4)

The same label d is chosen only once. In particular, pair maxima that require conflicting residues modulo d cannot all be attained.

For a finite collection of such stars, assign rational weights lambda_C >= 0. For each original unordered pair, the total weight of stars using that pair must be at most1. If LC4 is used, impose the same capacity1 for its original unary factor. Then

    sup_L Q_eta(L) <= B0(eta) - sum_C lambda_C kappa_C(eta).    (LC5)

Proof: each original factor has nonnegative loss `max f-f`. Within each star their sum is at least kappa_C. Multiply and sum, using factor capacities to avoid charging any individual loss more than once. The constant `-483 z` is retained exactly. The certificate holds uniformly over every complete original test, although kappa depends on the actual family law. A bound valid for all families still requires an outer argument controlling these quantities; LC5 does not supply that missing argument.

These cuts may also be taken for any small factor tree. Its minimum total loss is computed by eliminating leaves, storing at each original separator label its complete residue table. A disconnected or cyclic collection is not silently converted into independent trees; either its exact joint minimum is verified or a legitimate fractional packing is used.

<a id="3-law-stability-of-a-selected-cut-and-finite-core-use"></a>
#### 3. Law stability of a selected cut and finite-core use

Let eta and eta' be two finite nonnegative measures on a common lifted carrier, with full L1 discrepancy epsilon. A star spending t pair factors and h unary factors, h in {0,1}, has

    |kappa(eta)-kappa(eta')| <= (2t+3h) epsilon.                (LC6)

To prove this write eta-eta'=delta_plus-delta_minus with masses a,b. Every spent nonnegative factor has amplitude bounded by its coefficient c in {2,3}; its integral changes between -c b and c a. The independent-max sum and the joint star maximum each change between -C b and C a, where C=2t+3h. Their difference changes between -C(a+b) and C(a+b). No normalization or equal-mass premise is needed.

Thus a depth/core reference certificate B_C implies the actual correction

    kappa_C(eta) >= max(0, B_C-(2t+3h)epsilon).                (LC7)

Only selected factors are charged. This does not incur the number of all original labels. The core must be lifted to the same carrier and the discrepancy must include the actual incoming-law and killed-kernel change once. If the full reference objective is already transported by KC's full-objective comparison, do not pay the same discrepancy a second time. Conversely LC7 may only be subtracted from an actual factor envelope whose spent factors are present; it cannot be attached to an unrelated Gamma bound or to the exact CT identity.

All original depths and tails remain in LC1. Selecting a finite set of star factors does not truncate L. If a separate full-objective finite-core reduction is used, its already established omitted-label and law errors remain necessary. LC2 alone provides no tail deletion.

<a id="4-arbitrary-signed-rational-messages"></a>
#### 4. Arbitrary signed rational messages

For each original pair i<j choose arbitrary rational functions h_ij,i(r_i) and h_ij,j(r_j). Define

    u_i^h(r) = u_i(r) + sum_(e incident i) h_e,i(r),
    v_ij^h(r,s) = v_ij(r,s)-h_ij,i(r)-h_ij,j(s).

The messages cancel exactly, assignment by assignment. Therefore

    sup_L Q_eta(L)
       <= -483 z + sum_i max_r u_i^h(r)
                  + sum_(i<j) max_(r,s) v_ij^h(r,s).           (LC8)

No sign restriction on the reparameterized factors or messages is required. The same algebra works for any exact finite unary/pair table, including signed factors obtained from an independently proved full-objective decomposition. A verifier checks all finite maxima using rational arithmetic. It need not trust LP convergence, floating dual feasibility, a branch count, or a solver's status. Missing messages mean zero messages and are valid, so one can work on selected stars or cycles without storing the full factor graph.

An LP using one candidate unary marginal per original residue, one pair marginal per literal residue pair, normalization, and agreement of pair projections with those unary marginals can generate h. This is the standard local marginal-polytope relaxation. Its optimality is not needed for LC8: every rational h is a valid upper certificate, and an actual assignment with equal value proves exactness for the stated input. The benchmark corrected by LC8 remains B0 for the same full objective. The method is a reusable certificate route; it does not assert the relaxation is exact on arbitrary arithmetic families.

For a chosen sparse message support, let G_h=B0-U_h. If only factor set F* has nonzero reparameterization, then

    |G_h(eta)-G_h(eta')| <= (sum_(f in F*) c_f) epsilon.

Indeed each factor's perturbations lie between -c_f b and c_f a; the difference of its original and shifted maximum changes by at most c_f(a+b). Messages must be held fixed during this comparison. The nonnegative improvement is max(0,G_h).

<a id="5-a-literal-nonradial-actual-family"></a>
#### 5. A literal nonradial actual family

Take Q=315 and forbid old classes

    0 mod3, 0 mod5, 0 mod7, 2 mod9, 4 mod15.

Their 102 survivors modulo315 carry the uniform actual old law. Use cofactor list

    (3,9,15,21,45,63,105,315,5,7,35).

For p=17 and19 forbid pure0 modp and, at current residues i+1 for i=0,...,10, the mixed class with that cofactor. The first eight old residues are1. The last three old residues are2 at17 and3 at19. The full forbidden classes are their literal CRT combinations. Thus there are29 distinct odd forbidden moduli and common period101745. The complete divisor-test inventory is12*2*2=48 original labels.

At old x let k_p be the number of matching mixed masks, alpha_p=k_p/(p-1), delta_p=7/(p-2), g_p=1/(1-min(alpha_p,delta_p)), beta_p=(alpha_p-delta_p)_+/(1-delta_p), t_p=g_p/(p-1), q_p=1-beta_p. The actual killed row puts mass t_p on each unmasked nonzero root. Current19 masks have no17 factor, so the actual final law has row products, and the physical17 input has the same old marginal. The exact charges and final mass are

    b17 = 1/1632, b19 under physical17 = 1/1836,
    eta1 = 9781/9792.

Define q=q17q19, u=t17q19, v=q17t19, w=t17t19. For four independent complete old blocks A,B,C,D, retaining each block's unit label as constant1, the exact current maximum is

    E[q A²+u(2AB+B²)+v(2AC+C²)
         +w(2AD+2BC+2BD+2CD+D²)].                              (LC9)

Every prescribed old assignment attains all current pair caps simultaneously by putting every17-positive label at globally clean root16 and every19-positive label at globally clean root18. This is why no independent current label is dropped. Positive current unit-cofactor labels also take those roots and supply the three additional block constants. Before current maximization the original modulus-one test is unique; LC9's four constants arise from four distinct original labels1,17,19,323.

For LC9, H=[[q,u,v,w],[u,u,w,w],[v,w,v,w],[w,w,w,w]]. Expanding the four blocks gives constant E(sum H_gh), unary coefficient H_gg+2 sum_h H_gh, and pair coefficient2H_gh. All11 nonconstant old divisor labels in each block remain independent. A residue whose entire old cylinder is empty has zero contribution in every term; changing it to a nonempty residue cannot decrease a nonnegative objective. The verifier keeps EVERY nonempty original residue, yielding1004 unary choices in total. There is no first-exit consolidation, permutation orbit quotient, or assumed centered maximum.

The rational message certificate gives

    entrywise bound = 317481153727/19995655680,
    exact maximum = 846619/55488,
    entrywise improvement = 12393530887/19995655680
                          = 0.6198111772546786... .

The all-block old assignment centered at1 attains the bound. This is an output of exact upper/lower matching, not an input restriction. A separate scan of all literal surviving triples (x,y17,y19) under their actual killed weights gives the same mass and square integral. The signed final objective is

    max Q_eta = -77938211/166464.

For the tiny original-label cut d=3, neighbors9 and15, only the old marginal of the same eta is needed. The complete profile tables are

| a mod3 | M9(a) | M15(a) |
|---|---:|---:|
|0|0|0|
|1|3/17|3/17|
|2|4/17|2/17|

Thus

    kappa_(3;9,15) = 2[(4/17)+(3/17)-(6/17)] = 2/17.

The two best pair observations individually choose different residues for the SAME original modulus3 test. This is nonzero genuinely joint information. With any actual common-carrier L1 perturbation epsilon, this selected cut retains at least max(0,2/17-4epsilon), positive for epsilon<1/34. The coefficient4 here belongs to the two original pair factors 2 eta(I3 I9), 2 eta(I3 I15) in LC1. It is not the general variation coefficient of all LC9 factors.

<a id="6-reproduction-and-limits"></a>
#### 6. Reproduction and limits

The standard-library verifier `verify_original_label_messages.py` rebuilds the literal source/masks, every nonempty original-domain table, the rational message upper bound, the attaining assignment, the tiny divisibility-star profile, and the literal point scan. It runs with `python3 -I -O`. The file `original_label_message_certificate.json` contains the exact rational messages and result data. The verifier rejects duplicate JSON keys, duplicate original pairs, and inconsistent reported values. An optimizer is unnecessary to check the certificate.

The remaining unresolved step is an outer, all-family constraint sufficient to control LC5/LC8 or a stronger common-law envelope on the full AP13 core and all paid tails. The unrestricted299.398 continuation and later primes remain open.

<a id="7-existing-results-and-public-basis"></a>
#### 7. Existing results and public basis

The repository search for common/shared original labels, star cuts, pair compatibility, marginal polytopes, and message reparameterization found the current KB maximizing-label comparisons, RS signed unary/pair branch envelopes, OBE common-old-block distances, CPI/PT current-prefix incompatibility, and BQX exact four-block optimization. Those results are reused as context, but none of the searched report sections states LC3's old-divisibility profile cut or verifies the nonradial rational message certificate. The repository's `FiniteCompatibleCrt` and `CompatibleResidueJointImage` already provide the CRT compatibility structure; it is not reproved in new Lean. The finite response-law obstruction in `CompleteMediatorCutSharpBounds.three_cycle_complete_mediation_sharp` and the Boolean gluing example in `LocalLawGluingObstruction` are different finite input problems, not this weighted arbitrary-source cut. Text searches in the pinned Mathlib combinatorics and convex-analysis trees did not locate an exact weighted original-residue certificate theorem. This is a searched-scope statement, not a claim that the method is new.

Public source: David Sontag, Talya Meltzer, Amir Globerson, Tommi Jaakkola, Yair Weiss, [Tightening LP Relaxations for MAP using Message Passing](https://people.csail.mit.edu/dsontag/papers/sontag_uai08.pdf), UAI2008, sections2–3. The downloaded author-hosted PDF confirms the local marginal polytope, dual message upper bounds, exact assignment/dual matching, and the cluster gain `sum max b_e - max sum b_e` in equation4. Thus the message relaxation and general incompatibility gain are established methods. LC1–LC7 supply their explicit full-signed-killed-law, original-modulus CRT, factor-capacity, and L1 application here. No new Lean wrapper, claim of an invented LP method, or standalone positive finite-instance formalization is proposed.

<a id="the-fixed-uniform-threshold-also-fails-for-the-actual-extra-union"></a>
### The fixed uniform threshold also fails for the actual extra union

The preceding191-label example separated the labelled gate T from the actual
residual P. The stronger proposed premise P_Omega<mstar is also false, even
with the original357 period dividing315 and the same actual AP11/T4,
AP13/T6 law. The following result is ordinary mathematics with exact rational
verification, not Lean verification or an unrestricted covering conclusion.

Keep the previous old constraints0 modulo every nonunit divisor of
Q=315*11*13, the actual uniform17280-unit source, the head masks, the pure17/19
constraints, and the complete191 forbidden-modulus inventory. Replace only
the tail current residues by the explicit120-entry color assignment in the
[certificate](../../certificates/actual_residual_tail_obstruction_certificate.json). Each entry is [stage,d,color]:

* stage0: d|Q, d not dividing315; modulus17d, old residue1 modulo d,
  current17 residue color, with1<=color<=15;
* stage1: the same36 cofactors; modulus19d, old residue1 modulo d,
  current19 residue color;
* stage2: all48 d|Q; modulus19*17*d, old residue1 modulo d, 17 residue16,
  current19 residue color.

Stages1/2 have colors1 through18. Thus17 root16 stays globally clean, every
original modulus is still distinct and odd, and all192 final test labels and
all48 inherited labels remain independent. These vectors define literal CRT
classes; they are necessary instance data, not optimization output trusted by
the verifier.

Reconstructing the actual current bad-root unions and the resulting physical17
and killed17/19 kernels gives

    eta1 = 9652315153/9853747200,
    P_Omega = 159510497/9853747200
            =0.01618780081957045...
            >mstar=704627631753217/45514648675654535.       (ARO1)

Both stages are genuinely charged:

    b17=23537/2211840,
    b19 under physical17=35739053/2463436800.

The actual head baseline remains220243/221184, and its difference from eta1
is exactly P_Omega by CHT4. This calculation uses the actual union masses,
including overlaps and the actual incoming killed17 measure. It is not a
labelled union upper bound. The corresponding gate has also been recalculated:

    T_Omega=11329657/656916480.

Although the labelled tail counts are unchanged, this T differs from the
previous example because the new17 mask geometry changes the19 input.

Let A2 be the complete inherited test centered at2 and E2={A2<=10}. The same
pointwise support argument applies: a positive tail residual requires A1>=6,
while A1*A2<=48, hence it lies inside E2. Exact evaluation confirms

    P_E2=P_Omega>mstar,
    T_E2=T_Omega,
    nu(E2)=4229/4320.                                  (ARO2)

Thus the fixed generic mstar threshold fails both for the whole-space actual
residual and uniformly over actual complete-test low-load events. Merely
replacing the labelled gate by the exact extra union cannot establish that
particular unrestricted numerical premise.

The head/tail identity itself still yields a positive joint surplus. For E2,
the actual head cost is1/160 and the intercept is2101/2160, giving

    eta(E2)>=9425083423/9853747200,
    Delta121>=65975583961/3284582400.                   (ARO3)

There is also a bound uniform over every original test in this same family.
The unchanged actual source gives E_nu A<=5005/1728 for every independent
48-label inherited test and head-cell mass at most1/144. Therefore the
actual-residual version of CHT6 gives

    eta(A<=10)>=14003/17280-1/160-P_Omega
               =7763974303/9853747200>0,
    Delta121>=54347820121/3284582400.                   (ARO4)

The required unrestricted estimate must therefore control the joint quantity
nu(E)-headprice(E)-P_E, or another faithful full-objective bound. A universal
P_E<mstar is now excluded by ARO1/2. ARO3/4 explain why this exclusion does
not contradict the successful same-law conditional identity. No bound over
arbitrary source families, the tau81 KC threshold, or later primes is supplied.

The existing191-family verifier accepts this certificate's complete original
color assignment, reconstructs all original CRT classes and every actual bad
root, and checks CHT4 and ARO1--ARO4 exactly under Python -I -O. It continues
to verify the preceding all-color12 certificate unchanged. An independent
enumeration of all17280 old units, grouped by their48 complete divisor-incidence
patterns, gives the same actual mass, P_Omega and T_Omega.


<a id="joint-source-geometry-sharpens-normalization-on-the-same-actual-law"></a>
### Joint source geometry sharpens normalization on the same actual law

The unchanged actual AP11/T4, AP13/T6 law satisfies the stronger uniform
bounds

    Gamma13 <= 2440240269691060633/15032927232998818
             = 162.32635413377662...,
    T13(81) <= 7949756328165560683803712670852067996917
               /77125457411930247476980068692523326250
             = 103.0756457716106... .                     (JN1)

The domain includes arbitrary finite original3/5/7/11/13 heights,
residues, missing classes and all original test labels. Start from the
uniform complete actual357 survivors, use the same two physical kernels,
and condition once. The improvement retains the same source geometry
in both the physical cost and the surviving mass. It does not change
the probability or replace a true union by an independent event.
These are ordinary inequalities and exact rational checks, not Lean
verification or claims of sharpness over actual residue families.

<a id="common-raw-numerator-and-denominator"></a>
#### Common raw numerator and denominator

Use exactly the five groups of HC and SQ. Write

    D = s-T/5,
    B_h = D H_h  (h=3,4,6),
    S_t = the raw square-hinge expression in SQ5.

Here H_h is the local HC upper expression before maximizing the parameter
vertex. B_h and S_t are raw upper formulae, not necessarily the actual
hinge integrals. They are separately convex in each parameter group;
D is separately concave. The HC evaluator's denominator is5D/6, so its
raw reported hinge numerator must be multiplied by6/5 to obtain B_h.
All complete geometric tails from HC and SQ stay in these formulae.

Use H1<=H3+2 and H2<=H3+1 in the existing complete AP charge formula.
Its exact simplification gives, at the same parameter point,

    rho13 >= 131/132-H4/6-14H6/99-7H3/132 = Delta/D,
    Delta = 131D/132-B4/6-14B6/99-7B3/132.                (JN2)

In particular, the numerator is not paired with a survival bound that
has been separately maximized over unrelated source parameters. Delta
is separately concave. Its minimum at the1296 product vertices is

    18955015484347/259923856500000 > 0.

Repeated vertex interpolation therefore proves Delta>0 throughout the
same continuous domain. This argument covers all four effective9 branches.

Let G=3849/106 and let N=N11*N13 be the unchanged complete auxiliary
multiplier with caps5/3 and2. Its second moment is253/108. For tau=h²,
retain exact masses p_n=Pr(N=n), n<h, and the full tail mass and second
moment. For each threshold t=tau/n² choose one formula over the entire
parameter domain:

    S_t, or (G-1)D.

Both divided by D bound the source square hinge because t>1. The choices
used here are

    tau16: uniform cap only at t=16/9;
    tau81: uniform cap at t=81/64,81/49,9/4;
    every other needed threshold: raw S_t.               (JN3)

These choices are fixed globally. Taking a pointwise minimum separately
at each vertex would not establish the convex interpolation argument.
With R_t denoting the selected formula, define

    U_tau = sum_(n<h) p_n n² R_(tau/n²)
                +D [G E(N²;N>=h)-tau Pr(N>=h)].          (JN4)

The physical hinge is at most U_tau/D; conditioning and JN2 therefore
give T13(tau)<=U_tau/Delta. For tau16 also use
Gamma13<=16+T13(16). No bound on original heights is introduced by the
finite multiplier sum: every n>=h is present in the exact tail term.

<a id="continuous-certificate-and-all-missing-class-branches"></a>
#### Continuous certificate and all missing-class branches

Write U_tau=K_tau D+sum a_t S_t, with a_t>=0, by collecting all globally
chosen uniform caps and the complete multiplier tail. For a proposed
hinge bound C the margin is

    C Delta-U_tau
      = (131C/132-K_tau)D
          -C B4/6-14C B6/99-7C B3/132-sum a_t S_t.     (JN5)

Thus it is separately concave provided131C/132-K_tau>=0. This coefficient
condition is required because D is concave rather than affine. For the
JN1 values, with C=Gamma13-16 at tau16, the exact positive coefficients are

    4781395875818352928637/39438884595772399023,
    6531660602371000161896116359784324956377857
      /67446212506733001418619070071611648805625.

The verifier checks all1296 product vertices with minimum margin0 for
both targets. Repeated interpolation now proves the whole continuous
inequality. Both maxima occur, among symmetric copies, at

    deficit=(1/2,0,0,0,0), alpha=(0,1/4),
    beta=(0,1/4,0,0,0), late=(1/72,0,0,0,0), z=3/4.

These are extremizers of the bounding formulae, not certified actual
families attaining JN1. For the other eight missing-class branches, the
same charge formula uses the established branch-specific PR hinges;
the physical numerator uses the PR product square-hinge bound capped
by G-1. Each corresponding survival is positive and each ratio is below
its JN1 target. All twelve original branches are therefore included.

The [exact verifier](../../verify_joint_source_normalization.py) pins the HC/SQ
source programs and preceding certificates, recomputes both margins and
the complete tails, and compares the entire
[certificate](../../certificates/joint_source_normalization_certificate.json). Independent
rational recombination gives the same two constants and positive
coefficient signs. No finite sampling assertion is substituted for the
continuous proof above.

<a id="quantitative-consumer-at-the-open-killed-frontier"></a>
#### Quantitative consumer at the open killed frontier

The existing KC errors remain valid on this same probability. Substituting
JN1 into KC13 increases the sufficient finite-frontier allowances to

    F17^-(403)+F19^-(403) <= 299.923  [box20/current8],
    F17^-(403)+F19^-(403) <= 299.661  [unequal box/current6]. (JN6)

The exact available budgets are403-T13(81)-667/1000000 and
403-T13(81)-263/1000, respectively, approximately299.9236872283894 and
299.6613542283894. The verifier checks the strict slack in both rounded
thresholds. The earlier299.660 and299.398 sufficient conditions stay
valid; JN6 permits a larger frontier. Neither finite maximum has been
bounded by the new allowance. The later-prime continuation and the
unrestricted Erdős7 conclusion remain open.

<a id="latest-sparse-valuation-interface"></a>
#### Latest sparse-valuation interface

RRO section61 on dev commit4ae21a8e6d gives an exact common-witness
criterion for sparse difference valuations: contract the edges requiring
agreement beyond a layer, then require a proper p-coloring of that
layer's quotient graph. The constructed digits lift all layers to one
integer tuple. Its ternary unit-sum specialization already encodes general
three-coloring with labels1 and2, even on a bipartite constraint graph.
These are realizability results. They supply no actual AP measure,
weighted objective or quantitative loss from nonrealizability. Using them
for the KC objective still requires that weighted bridge. JN1 instead
uses the existing actual-cell formulae and keeps their shared parameters
through normalization; no inference from NP-completeness to a bound on
this specific covering problem is made.
