# A complete-query hinge removes the pointwise overlap bound

For P={3,5,7,11,13,17,19}, Q=P\{3}, take any finite actual family with pairwise distinct odd nonunit numerical moduli and one globally fixed residue per modulus. At every nonunit numerical Q-cofactor d, suppose the projections of its originals 3^e d with 0<=e<=4 occupy at most two phases. Choose precisely these phases as A_d, with empty sets outside the finite actual inventory. Every later original phase and every finite height is unrestricted. No bound is imposed on the number of active residual cofactors at a Q point.

There is one probability mu in the fixed-pure3 conditional class C_u(U), where u is normalized Haar on the complete actual pure3 survivor, with

    R_P(mu)<=100187189764192062038511763
               /8675416202016775933328340
            =11.54840153270128... <566/49.           (FH1)

Arbitrary additional originals touching23 or29, with arbitrary P-smooth cofactors and arbitrary finite heights, still leave actual Haar survivor mass at least

    1113271896084138376764053
      /999154089609171598809907200000
    =0.0000011142144216410154... >1/900000.          (FH2)

The Q marginal is deliberately changed in response to the actual fibres. It is not asserted that the original PA marginal has a small fixed-marginal lift. Report571's obstructions to retaining that marginal remain valid. These are ordinary mathematics and exact rational certificates, not a Lean result or an unrestricted Erdős #7 solution.

## 1. A uniform third positive-part moment under the actual PA source

Use the unchanged selected-family PA source of Report569. Let x in[1/2,1] and y in[2/3,1] be its complete pure5/7 survivor Haar masses. Write lambda for its final unnormalized positive measure, s=lambda(1), and nu=lambda/s. Its same-law query bound is

    R_Q(nu)<=B=432040125182653876501/86355045355449035400.

Let m be the actual mixed5/7 loss and Delta_q the actual subsequent row losses. The same source has

    0<=m<=1/12,
    0<=Delta_q<=a_q F_q(x,y),
    s=xy-m-sum_q Delta_q >=alpha(x,y)>0,             (FH3)

where rows(q,t_q,C_q,a_q) are

    (11,2,5/3,1/3), (13,2,3/2,1/4),
    (17,4,2,1/4), (19,4,9/5,1/5).

These are Report569's original source parameters; no original phase or row is changed. The auxiliary count coordinates have masses and means

    mass(N5)=x, E N5=x+1/4,
    mass(N7)=y, E N7=y+1/6,
    mass(Nq)=1, E Nq=1+C_q/(q-1).

Their low atoms are those in that report: at the two anchors, pi_p(1)=w_p-1/p and pi_p(n)=(p-1)/p^n for n>=2; later pi_q(1)=1-C_q/q and pi_q(n)=C_q(q-1)/q^n. Let V_Q be their product, including the unit query, and put

    Phi4(x,y)=E(V_Q-4)_+.

The complete-suffix proof of Report569 SD4 applies with hinge threshold4 in place of3. It uses only that the averaged query payoff contains the complete later-only subinventory, whose nonnegative payoff is at least its suffix hinge. Thus for any complete finite Q exponent box and any one fixed phase for each numerical query label, with total count N including its unit once,

    integral (N-4)_+ d lambda
       <=Phi4(x,y)-zeta0 m-sum_q zeta_q Delta_q.     (FH4)

The complete suffix constants, in order before11, after11, after13, after17 and after19, are

    zeta0 =20115643355127233/378396319677192960,
    zeta11=711972268589/47382459263360,
    zeta13=7295473/2695861360,
    zeta17=1/68590, zeta19=0.

For completeness, each row is completed from its actual substochastic kernel k_q to a mass-one kernel bounded by C_q. The added mass is 1-s_q; the already averaged later-only query labels supply payoff at least zeta_q at every current state. Subtract zeta_q(1-s_q) before applying the conditional convex comparison, and integrate against the actual previous marginal. Subsequent backwards steps leave this debit outside the remaining comparison. The same argument treats the initial mixed5/7 deletion with zeta0. For a finite box use its finite suffix constants and finite main hinge first. Extend the fixed phases to increasing complete boxes; the main hinge and each suffix constant separately converge to their displayed full values by their finite first moments. No monotonicity of their difference is needed. This proves FH4 without transporting an actual loss onto a new auxiliary law.

Only the full mean and atoms below4 are needed to compute a hinge:

    E(V_Q-4)_+=E V_Q-4xy
                +sum_(v=1,2,3)(4-v)Pr(V_Q=v).

All higher counts, and consequently every query height, remain in the complete first moment. The raw auxiliary mass stays xy throughout.

Set

    K=12019840537595758779003/5715264751774801992890
     =2.103111764658523... .                         (FH5)

The four exact corner certificates are

    K alpha(x,y)-Phi4(x,y)+zeta0/12
      +sum_q zeta_q a_q F_q(x,y)>=0.               (FH6)

The quantity on the left is separately affine in x and y: every auxiliary mass, mean and retained low atom is so, and every fixed-threshold hinge is their linear combination. Nonnegativity at the four corners therefore proves it on the entire rectangle. K also exceeds every zeta_q and zeta0. From FH3–FH4,

    Ks-integral(N-4)_+ d lambda
      >=Kxy-Phi4-(K-zeta0)m-sum_q(K-zeta_q)Delta_q
      >=K alpha-Phi4+zeta0/12+sum_q zeta_q a_q F_q
      >=0.

The corner values of the corresponding quotient are

| x | y | [Phi4−zeta0/12−sum zeta_q a_q F_q]/alpha |
|---|---|---|
|1/2|2/3|2.103111764658523...|
|1/2|1|1.113052...|
|1|2/3|0.668795...|
|1|1|0.470340...|

Their exact fractions are retained in the producer data. The first is K. Dividing the actual inequality by s proves, under THIS SAME nu,

    E_nu(N-4)_+<=K                                 (FH7)

for every fixed complete query layout. A partial nonunit layout L has at most one fixed phase at each numerical cofactor; extend it to a complete finite box without changing its original phases. Then L<=N-1, so

    E_nu(L-3)_+<=K.                                (FH8)

The phase choices need not maximize any query, and FH8 holds simultaneously for all such layouts. This stronger tail-shape fact, not merely R_Q(nu)<=B, supplies the new input.

## 2. Original numerical distinctness produces an averaged residual load

Let V be the selected Q-survivor. The actual source nu is supported on V. All original projections at exponents0 through4 have been selected, so they cannot act on V. For each e>=5, define

    L_e(x)=sum_(actual originals 3^e d, d>1)
                  1_{x equals the original Q phase modulo d}.

There is at most one original for each exact numerical pair(e,d), hence L_e is a partial single-phase query layout of the kind in FH8. Selected phases can be included in this sum because they vanish on V. Original ternary phases remain unchanged; the contributions of their forbidden cylinders are bounded above by their actual cylinder-mass caps.

Let chi(t,x) be the complete original survivor and

    c(x)=integral chi(t,x)du(t),
    Y(x)=sum_(e>=5) 2·3^(4-e) L_e(x).

All absent e have L_e=0. The nonnegative coefficients sum exactly one. Since the complete pure3 source obeys u([a]_(3^e))<=2·3^(-e), the union bound on each actual fibre gives

    1-c(x)<=sum_(e>=5)2·3^(-e)L_e(x)=Y(x)/81.      (FH9)

No pointwise upper bound on Y or on the number of cofactors is required. Convexity of z↦(z-3)_+ and FH8 yield

    E_nu(Y-3)_+
       <=sum_(e>=5)2·3^(4-e) E_nu(L_e-3)_+
       <=K.                                       (FH10)

All expectations use the one source nu. The proof does not infer a bound on E(1/c), on C_Q(nu/c), or on a lift retaining nu.

## 3. Select the new marginal together with the actual fibres

Put kappa=26/27=1-3/81 and define one supported submeasure

    eta(dt,dx)=chi(t,x)u(dt)nu(dx)/max(c(x),kappa).

Its Q marginal is beta(x)nu(dx), where

    beta(x)=min(1,c(x)/kappa).

Thus bad or dead fibres lose their Q mass. Its total mass s_eta satisfies

    1-s_eta=E_nu[(kappa-c)_+]/kappa
       <=E_nu(Y-3)_+/(81kappa)
       <=K/78.

Consequently

    s_eta>=s0=1-K/78
       =144590270033612932222139
          /148596883546144851815140>0.              (FH11)

The actual marginal beta nu is a submeasure of nu. Hence the entire nonunit pure-Q query sum of eta is at most B. For positive ternary exponents a>=1 and any Q-smooth d>=1,

    q_(3^a d)(eta)<=q_(3^a)(u)q_d(nu)/kappa.

Summing every height and using R_3(u)<=1 gives

    R_P(eta)<=A_kappa:=B+(1+B)/kappa.

Normalize ONCE:

    mu=eta/s_eta,
    R_P(mu)<=A_kappa/s0,                            (FH12)

which is precisely FH1. The strict margin is

    566/49-FH1
      =1113271896084138376764053
         /425095393898822020733088660>0.

The final Q marginal is pi=beta nu/s_eta. On every live fibre its ternary conditional is u restricted to U_x and normalized, so mu belongs to C_u(U). For a raw product/deletion realization set

    Z=integral [1/max(c,kappa)]dnu,
    w(dx)=nu(dx)/[Z max(c(x),kappa)].

Here 1<=Z<=1/kappa, w is one probability, and normalizing the restriction of u times w to U gives exactly mu. Dead fibres create no singularity. This both retains the actual original family and changes the marginal in the way excluded by the fixed-marginal counterexamples.

## 4. Arbitrary23/29 originals under the same law

The PA source has nu<=9H_Q/alpha_min, with

    alpha_min=7575003978548161/73724315753088000.

Therefore

    mu<=18 H_P/(alpha_min kappa s0).

Condition23 and29 Haar on their complete actual pure-power survivors; their density factors are22/21 and28/27. Report569 SD15–16's same-law counting leaves probability at least [566-49 FH1]/567 after every additional mixed original touching23 or29. Dividing by the single joint density bound gives

    H(full survivor)>=
      [566-49 FH1]alpha_min kappa s0/11088,

which is FH2. No core query bound is asserted for the final nine-prime conditioned law. The support need not include every surviving original fibre. The positive measure and finite CRT suffice for an actual uncovered integer.

## 5. Genuine structural extension and a finite actual example

The new hypothesis allows two phases through exponent4 and arbitrary phases thereafter, with no pointwise overlap restriction. It strictly includes the all-cofactor through-five class of Report569 SD18. Report569's finite-cofactor-window version additionally permits unrestricted low exponents at large cofactors; that different class is not claimed to be included here.

The old direct residual bound at height4 is delta<=B/81. Substituting it into 566(1-delta)-49(1+2B) gives a negative result. FH10–FH12 retain the source's third positive-part moment and choose a new marginal, thereby certifying the whole height4 class. A separately favourable Q law is never substituted into that moment estimate.

A concrete 26-original family separates the new class from the preceding support and incidence classes. It has:

- pure3 original2 mod3;
- for each q in Q, originals at exponents e=0,1,5,6, with Q phases0,1,2,3 respectively and ternary phase0 when e>0;
- the Q-only triple original4 mod385.

Select A_q={0,1} and A_385={4}. These choices cover all exponents through4. Every prime cofactor gains a third phase at exponent5, so the old through-five restriction fails even at cofactors below500000. The same live Q point with every root2 activates six different residual cofactors, so Report572's h3/M2 condition fails. The essential Q-only triple excludes Report547's stars, Report561's all-three-rooted class and Report570's permitted non3 pair supports. The program supplies an actual private CRT witness for every original, so the triple is not a redundant addition. It does not enumerate the large full period.

This example separates structural classes; it is not a sharpness claim for FH1 and does not assert failure of every older instance-specific weighted certificate. Pure3 cases with low fibre loss can still have older proofs.

For unrestricted actual families, the requirement of at most two phases at exponents0,...,4 remains unproved and can fail. That shallow multiplicity is the remaining premise of this result. There is no assumption or conclusion that arbitrary fixed Q marginals admit a uniformly small lift.

## 6. The continuous scalar clipping estimate stops before height3

Keep this report's actual PA source, the fixed uniform complete-query
bound

    B=432040125182653876501/86355045355449035400,

and its complete-suffix deletion credits, without adding any other
moment or cap-slack information. For each real t>=0 let K_t be the
maximum over its four actual pure5/7-mass corners of

    [Phi_(t+1)-zeta0(t+1)/12
                 -sum_q zeta_q(t+1)a_q F_q]/alpha.

The full means and all needed low product atoms define Phi and zeta;
no positive tail is truncated. For the through-exponent3 hypothesis,
put theta=1/27 and kappa=1-t/27. For0<=t<27 the single scalar clip
certificate under review is exactly

    R_bound(t)=[kappa B+1+B]/[kappa-K_t/27],          (HC1)

provided its denominator is positive.

For this precise envelope, the GLOBAL minimum over every admissible
real t is

    t=3, kappa=8/9,
    min R_bound
      =32251975696663808317113607
         /2502930270099989781007140
      =12.885686861494296... .                      (HC2)

It exceeds566/49 by the exact positive amount

    163688276259932391488525503
      /122643583234899499269349860
    =1.3346664533310308... .                        (HC3)

Thus changing this one clipping threshold, with these particular
retained K_t bounds, cannot certify the unrestricted-overlap
through-exponent3 class.

### Every real threshold is included

Every comparison product count is an integer. Consequently each hinge
as a function of its real threshold is affine between consecutive
integers. In the range t in[0,27], its threshold is t+1 in[1,28].
Exact full first moments and product atoms at values1,...,28 therefore
suffice to give all four corner functions on all27 unit intervals.
The constants alpha and the actual loss upper bounds a_q F_q do not
vary with t.

The accompanying rational program checks the four corner functions at
every integer endpoint, and solves all six pairwise affine intersection
equations on each open unit interval. There are NO such interior
crossings. Explicitly, corner(x,y)=(1/2,2/3) dominates the other three
at EVERY endpoint, and hence throughout each interval. Thus K_t is
that one piecewise-affine corner function everywhere in[0,27]. The
crossing computation is retained as an independent guard against
omitting an interior upper-envelope breakpoint.

At every breakpoint K_t is at least every suffix zeta_q(t+1), including
zeta0. On each affine piece these differences remain nonnegative.
Therefore the signs needed to replace actual m and Delta_q by their
upper bounds are valid on the entire continuous interval. No
inadmissible negative loss coefficient is used.

On any affine piece the numerator and denominator of(HC1) are affine
functions of t. Where its denominator is positive, its derivative has
constant sign: for (a+bt)/(c+dt) it is(bc-ad)/(c+dt)^2. Hence the
minimum on that piece is at an endpoint, unless the ratio is constant.
The numerator remains positive even at t=27, so approaching any zero
of the denominator from its positive side sends the ratio to+infinity.
Such a boundary cannot introduce a missing finite minimum.

Exact evaluation of the complete breakpoint list therefore proves
(HC2), not merely a finite-grid observation. As a second form of the
same check, the gate

    G(t)=(566/49)(kappa-K_t/27)-(kappa B+1+B)

is piecewise affine. Its global maximum is also at t=3 and equals

    -163688276259932391488525503
       /151225905331961260731869400 <0.

This negative maximum independently states that no threshold in the
entire range supplies a positive scalar certificate.

### Scope of the failed certificate

This is a failure of ONE explicitly defined upper-bound certificate,
not a lower bound on the actual attainable R and not a covering
counterexample. It does not exclude a stronger bound on the same
source using R_Q<=B jointly with its moments, extra cap-slack credits,
stratified or different clipping, more detailed fibre geometry, or a
different actual source. It does not refute noncoverage of the
through-exponent3 class. The through-exponent4 theorem above remains
unchanged.

Artifacts: [height_three_clipping_envelope.py](../../frontier/cover-geometry/height_three_clipping_envelope.py) and [exact data](../../frontier/cover-geometry/height_three_clipping_envelope.json).
The exact producer passed36 named checks, including explicit corner0
dominance at every endpoint, the complete affine-crossing search,
valid debit signs and both continuous-envelope conclusions. No new Lean verification is claimed.

## Reproducibility and verification status

Program: [four_level_query_hinge_lift.py](../../frontier/cover-geometry/four_level_query_hinge_lift.py).
Exact result: [four_level_query_hinge_lift.json](../../frontier/cover-geometry/four_level_query_hinge_lift.json).

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_level_query_hinge_lift.py

Exit0, 84 named exact checks. They retain the all-height first moments and threshold4 low atoms, suffix constants, all four corner certificates and slope signs, recovery of Report569's old SD2 value, interior bilinearity diagnostics, the strict query and Haar gates, and all26 actual phases and private witnesses. The general source comparison and averaged-load arguments above establish the arbitrary-family quantifiers; finite diagnostics do not replace them. No new Lean verification is claimed.
