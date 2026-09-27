[Index](../../marked_head_profile.md) · [Previous](27-actual-mask-weights-and-an-all-height-square-certificate.md) · [Next](29-a-common-old-block-budget-strengthens-the-actual-mask-certificate.md)

<a id="zero-local-losses-do-not-imply-a-common-maximizing-original-layout"></a>
### Zero local losses do not imply a common maximizing original layout

This result supplies an actual odd-modulus obstruction to two tempting local closure rules. It uses the same finite actual source and all original test labels. The proofs below are ordinary mathematics, with an exact standard-library verifier. No Lean verification or unrestricted #7 bound is claimed.

<a id="1-what-a-zero-star-or-edge-really-asserts"></a>
#### 1. What a zero star or edge really asserts

Let eta be any nonzero finite measure on Z/QZ, and retain one independent original residue test for every d|Q, with the modulus-one test fixed to1. Put

    M_d = max_(a mod d) eta C(a,d),
    G_d = {a mod d : eta C(a,d)=M_d}.

For distinct original labels d,e, generalized CRT shows that the largest pair mass is M_lcm(d,e). Every maximizing combined residue is in G_lcm(d,e). This does not identify the shared residue choices in different pairs.

The full star centered at d, spending the unary `3 eta I_d` and every incident pair `2 eta(I_d I_e)`, has zero independent-max loss exactly when

    S_d = G_d intersect intersection_(d|m|Q, m>d) (G_m mod d)

is nonempty. Indeed a single central residue must maximize its unary and admit an extension to each relevant pair's maximum. Conversely every pair's lcm is a multiple of d; a residue in S_d permits a maximizing choice for each other label separately. The neighbor choices are independent within this star, but they are not choices that may be reused unchanged at every other star.

The two-ended edge cluster spending both endpoint unaries and its pair has zero loss exactly when

    exists r in G_lcm(d,e): r mod d in G_d and r mod e in G_e.    (LCZ1)

Thus all S_d nonempty and all LCZ1 feasible are explicit finite local conditions. Neither asserts that one original residue assignment attains all factor maxima.

<a id="2-an-actual-source-where-both-local-conditions-hold-and-global-saturation-fails"></a>
#### 2. An actual source where both local conditions hold and global saturation fails

Use the literal common old period

    Q = 1575 = 3² 5² 7.

Forbid the following17 classes, one at every nonunit old divisor:

    (modulus,residue) =
    (3,0), (5,0), (7,0), (9,4), (15,4), (21,19), (25,14),
    (35,18), (45,26), (63,1), (75,71), (105,83), (175,23),
    (225,199), (315,262), (525,383), (1575,754).

All moduli are distinct odd integers greater than1. Let S be the382 actual uncovered points modulo1575, and let nu357 be uniform on S. This is the actual uniform full357-survivor law, not an independently invented weighting.

The certificate reconstructs all18 divisor marginals by counting these same382 points. It verifies S_d nonempty for all17 nonunit original labels and LCZ1 for all136 distinct old-label pairs. Thus every full central-unary star and every two-ended edge cluster has zero loss.

Nevertheless the three original labels5,21,35 have

    G5 = {2},
    G21 = {8,17},
    G35 = {2,3,27,32}.

They have no simultaneous compatible choice. The label5 forces the label35 residue into {2,27,32}, whose residues modulo7 are {2,6,4}; label21 requires residue1 or3 modulo7. These sets are disjoint. This is a conflict of original CRT choices on the triangle of labels5,21,35, not an abstract Gram-matrix countermodel.

Each pair nevertheless has a common maximizing choice. Examples of combined residues are

    pair(5,21): 17 mod105,
    pair(5,35): 2 mod35,
    pair(21,35): 38 mod105.

Those three pair witnesses cannot be identified with a single choice for their repeated labels.

<a id="3-exact-triangle-correction-with-all-tradeoffs-retained"></a>
#### 3. Exact triangle correction with all tradeoffs retained

Consider the six literal factors of the full square supported on these labels:

    H = 3 eta I5 + 3 eta I21 + 3 eta I35
        + 2 eta(I5 I21) + 2 eta(I5 I35) + 2 eta(I21 I35).

The exact marginal maximum counts, before division by382, are

    M5*382=130, M21*382=50, M35*382=25, M105*382=15.

Consequently the independent six-factor envelope is

    [3(130+50+25)+2(15+25+15)]/382 = 725/382.

The verifier evaluates every one of the5*21*35=3675 literal residue assignments using the same counted source points. The exact maximum is

    max H = 716/382 = 358/191,

attained uniquely by the residue triple(2,2,2). Hence the six-factor correction is

    kappa_triangle = 9/382.                                  (LCZ2)

There is an important distinction from restricting every variable to its unary-maximizer domain. That restricted calculation yields loss30/382. It cannot be subtracted from the unrestricted full objective: the actual cluster maximum deliberately selects residue2 modulo21, whose count is47 instead of50, pays unary loss3*(50-47)/382=9/382, and attains all three pair maxima. LCZ2 includes that tradeoff and is the valid correction.

For any common-carrier L1 measure discrepancy epsilon, the six-factor loss changes by at most15 epsilon, the sum of their nonnegative amplitudes3+3+3+2+2+2. This is the same LC law-comparison argument, applied to one joint cluster. In particular this correction survives at least as max(0,9/382-15epsilon). It corrects the entrywise envelope of these six factors in the actual complete signed objective, not an independently derived Gamma or KC bound.

<a id="4-the-same-obstruction-on-actual-nu13-and-the-final-killed-law"></a>
#### 4. The same obstruction on actual nu13 and the final killed law

Add only the four pure classes

    0 mod11, 0 mod13, 0 mod17, 0 mod19.

The resulting actual family has21 distinct odd forbidden moduli, period72747675, and288 complete original divisor-test labels. At11 and13 there are no mixed exclusions; physical conditioning gives exactly nu357 times the uniform nonzero11/13 roots. Thus the actual nu13 has45840 equally weighted points. At17 and19 there are again no mixed masks, so assigned bad masses are both0 and the physical and killed kernels agree. The final eta is precisely

    nu357 times U((Z/11Z)^*) times U((Z/13Z)^*)
          times U((Z/17Z)^*) times U((Z/19Z)^*),

with13201920 points and total mass1. No supported replacement law, second conditioning, or independently selected incoming measure is used. At19 the input is literally nu13 K17^-, as required.

For every full divisor d=d0 e, where d0|1575 and e is a product of distinct primes from {11,13,17,19}, its marginal maximum is

    M_d = M_d0 / product_(p|e)(p-1),

and its maximizing residue domain is the CRT product of G_d0 and arbitrary nonzero roots in its extra prime coordinates. Therefore both local conditions of sections1–2 lift to every one of the287 nonconstant full original labels and every one of their41041 distinct pairs. The verifier checks these projection and pair conditions over the complete288-label inventory, using this explicit product formula. No original test label is identified or removed.

The three zero-current labels5,21,35 retain exactly their old marginals. Consequently, for the full signed objective with all288 original tests,

    sup_L [eta L² - 484 eta1] <= B0(eta) - 9/382,              (LCZ3)

where B0 is the same-law entrywise pair envelope from LC1. The correction is the six original factors just evaluated; all other factors and the signed mass term remain present. This is a positive higher-cluster gain despite every star and every two-ended edge separately having zero loss.

The zero charges are part of this example's scope. The example disproves universal local-to-global sufficiency claims over actual families. It does not assert the same blind spot under an additional positive-charge premise, and does not supply a uniform positive correction for all families.

<a id="5-exact-saturation-and-why-this-is-not-a-counterexample-to-full-arc-consistency"></a>
#### 5. Exact saturation and why this is not a counterexample to full arc consistency

Because the complete original label set includes Q, the entire pair envelope is saturated if and only if

    exists x in G_Q: x mod d in G_d for every d|Q.              (LCZ4)

If a test saturates the envelope, each nonnegative factor loss vanishes. The Q-label unary selects a maximum-mass atom x. Each pair of that label with d has its positive maximum only when the d-residue is x mod d. Hence all projections lie in G_d. Conversely such an x centers every original label; each intersection is the maximizing class for its original lcm, so all unary and pair maxima are attained.

It follows that full arc consistency on the unary-maximizer domains, using the Q-label and all its pair constraints, already decides saturation: retain exactly those x in G_Q whose projections lie in every G_d. If any remain, LCZ4 supplies a global assignment. If none remain, saturation is impossible. The counterexample above concerns nonempty local clusters checked separately, not a fully propagated arc-consistent instance.

This observation does not remove the research bottleneck. G_Q can require the complete actual-period carrier, and saturation is only a zero-loss feasibility question. Computing a useful weighted upper bound must retain near-maximal choices such as residue2 modulo21 above; hard restriction to all G_d would discard the true optimizing tradeoff.

The standard message and cluster-gain framework is the already cited Sontag et al. method. The new content here is the literal actual odd-CRT realization, its full original-label scope, and the exact9/382 consumer. The new RRO61 layer-coloring classifications concern sparse valuation realizability; no mapping from those unweighted problems to the present actual-law marginal maxima or weighted AP objective has been established.

<a id="verification-and-remaining-boundary"></a>
#### Verification and remaining boundary

Run `python3 -I -O verify_star_cycle_obstruction.py` next to `star_cycle_obstruction_certificate.json`. The program reconstructs the source, marginals, all local witnesses and the complete triangle calculation; the certificate is compared against that reconstruction. Pure-extension assertions use the explicit product proof above and finite checks of all full-label projection conditions. No optimization output is trusted.

The unrestricted299.398 estimate and later-prime continuation remain unproved. There is also no general positive deficit forced solely by distinctness of the original moduli: pure-prime exclusions with a product uniform survivor law admit a common centered maximizing layout and have zero deficit in the entire entrywise envelope. The useful direction is therefore a joint weighted case split, not a universal subtraction inferred from original-label uniqueness alone.


<a id="dv-supported-probability-gives-lower-bounds-for-the-actual-ap-killed-law"></a>
### DV-supported probability gives lower bounds for the actual AP killed law

This is an ordinary finite-measure proof using the existing DV1/DV5 head
theorem and AP/W1 kernel estimates. It is not a Lean proof. Its substantive
restriction is that every original 3/5/7 part divides 315. Original 11/13
cofactors and all finite 11/13/17/19 heights are arbitrary; 19 cofactors may
contain 17. It does not solve unrestricted Erdős #7 or continue beyond 19.

<a id="fixed-family-measures-and-labels"></a>
#### Fixed family, measures, and labels

Fix one original family of distinct odd nonunit moduli. All masks, residues,
pure-prime bases, heights and thresholds below refer to this same family.
Pad its old carrier, when needed, to
`Q = 315 * 11^H * 13^J`, with `H,J >= 1`, using uniform unused digits. This
is only a common ambient carrier. Kernels ignore unused digits. A test on
a smaller actual old period can be completed on this carrier in advance;
the additional indicators are nonnegative. No original test is identified
with another test, and no completion residue depends on the sampled point.

Let `m_Q` be uniform Haar probability on this finite carrier. Let `S_13` be
the full original survivor set through 13. Start from uniform probability
on the full original 357 survivors, use actual normalized physical AP11/T4
and AP13/T6 kernels without intermediate conditioning, and condition once
on `S_13`. The resulting probability is denoted `nu_13`.

Write `K_p` for the actual normalized physical pure-base AP kernel at
`p=17,19`, with `delta_p=7/(p-2)`, and `R_p=K_p^-` for its restriction to
the actual good points. Its lost row mass is

    beta_p(x) = (alpha_p(x)-delta_p)_+/(1-delta_p).

These row kernels depend on the actual masks, pure bases, coordinates and
fixed thresholds, not on the incoming probability. In particular they can
act on two different input measures without changing any row. Set

    eta = nu_13 R_17 R_19.

The auxiliary probability `nu_*` is the single supported clipped law of
DV1, on this same original family. The present argument never asserts
`nu_*=nu_13`. All comparisons between them are explicit measure inequalities.

The exact DV inputs are simultaneous on `nu_*`, uniformly over every
complete original old test `A`:

    E_nu_* A^2 <= G = 591122424341/16497075000,
    E_nu_* A   <= M = 1175795/219961,
    E_nu_* (A-t)_+ <= theta_t  (t=4,...,12),
    ell_b >= ell = 108683/204000.

The `theta_t` values are those of DV6 in the pinned source certificate.
Every complete test includes its single unit term, so `A>=1` is integer.

<a id="1-pointwise-comparison-of-the-two-old-probabilities"></a>
#### 1. Pointwise comparison of the two old probabilities

The canonical old-315 reduction in the existing head theorem constructs a
subset of the original old survivors. Its coordinate normalizations are
cylinder-preserving permutations. Pull back to the original coordinates
before doing this comparison. Thus the old auxiliary law is uniform on
a genuine subset `T` of the original survivors, with `N=|T|>=74`. This
argument uses containment of supports, not monotonicity of expectations
under pruning.

The DV reference law `tau` is this old uniform law, times the uniform
10-by-12 root rectangle and uniform higher 11/13 digits. A virtual pure
root exclusion when a pure class is absent only shrinks this support.
Consequently, relative to `m_Q`,

    d tau/d m_Q <= (315/74)*(11/10)*(13/12).

The unnormalized DV low-survivor density relative to `tau` is

    f = 1_low-survives min(C,1/s(x)), C=40/31,

and is zero at empty fibres. Remove every actual higher exclusion, and
normalize the resulting mass `s_actual`. DV5 proves `s_actual>=s_b>0`
and `ell_b=s_b/C`. Removing further points does not increase the
unnormalized density. It follows that

    nu_* <= tau/ell_b <= tau/ell,
    d nu_*/d m_Q <= D := (315/74)*(143/120)/ell
                       = 38288250/4021271.

Moreover `nu_*` is supported on `S_13`: pruning and virtual roots impose
extra deletions, whereas all actual low and high 11/13 exclusions were
removed. If the carrier was padded, completion of test labels is upward
only; these support and density statements still hold on the padded space.

Conversely, the actual unconditioned AP13 law has density at least one
relative to `m_Q` at every point of `S_13`. The initial full-survivor
uniform law has density `1/m_357(S_357)>=1` on its support. At a point
surviving the actual p-step, its kernel density relative to Haar in the
new p-coordinate is exactly

    1/[lambda_p*(1-min(alpha_p(x),delta_p))] >= 1,

where `lambda_p<=1` is the actual pure-survivor Haar mass. This applies
at p=11 and p=13, for the actual full history at that point. Product of
these factors is at least one. In particular the nonempty support of
`nu_*` proves positive actual conditioning mass `rho_13`; dividing by
`rho_13<=1` only increases this density. Hence

    d nu_13/d m_Q >= 1 on S_13,
    nu_* <= D nu_13.                                      (DB1)

Outside `S_13` both probabilities are zero. No assertion of an actual
global Haar lower bound outside the survivor set is being made.

Nonnegative kernels preserve domination. Since exactly the same actual
rows are used on the two sides,

    zeta := nu_* R_17 R_19 <= D eta.                       (DB2)

This is the bridge from an auxiliary supported law to the prescribed
actual AP13 continuation. It does not replace that continuation's law.

<a id="2-uniform-auxiliary-loss-bound-with-all-original-cofactors-retained"></a>
#### 2. Uniform auxiliary loss bound with all original cofactors retained

At a current prime p, original-modulus distinctness permits at most one
pure class at each depth, so its Haar survivor mass satisfies

    lambda_p >= 1-sum_(e>=1) p^-e = (p-2)/(p-1).

For each original current depth e, let `B_e(x)` count the active actual
mixed cofactor cylinders, retaining their original old labels. Complete
`1+B_e` upward to a complete old test `A_e`. Pure p classes were already
removed, so exactly the unit cofactor is absent. The union bound gives

    alpha_p(x) <= lambda_p^-1 sum_(e>=1) p^-e B_e(x)
               <= 1/(p-2) sum_(e>=1) w_e(A_e(x)-1),
    w_e=(p-1)p^-e, sum_e w_e=1.

Missing labels and depths only add nonnegative terms in this comparison;
no physical height is truncated. Completions are fixed before sampling.
If a probability sigma controls every complete old test square by `G0`,
Jensen and `A_e>=1` give

    E_sigma alpha_p^2 <= (G0-1)/(p-2)^2.

For any a>=0 and delta>0, `(a-delta)_+ <= a^2/(4delta)` (complete the
square on a>=delta). Therefore at `delta_p=7/(p-2)` the same physical
assigned charge obeys

    b_p(sigma)=E_sigma beta_p <= (G0-1)/[28(p-9)].         (DB3)

For the auxiliary 17 source this gives

    b_17^* <= (G-1)/224
            = 574625349341/3695344800000.

Every normalized physical 17 row has Haar density at most
`1/[lambda_17(1-delta_17)]<=2`, on both good and bad points. Applying
the existing W1 rectangle bound, or expanding pairs of original labels
by their two 17-depths and using Cauchy-Schwarz on their old loads, yields

    Gamma(nu_* K_17)
      <= [1+2 sum_(e>=1)(2e+1)17^-e] G
      = (89/64)G.                                        (DB4)

In the pair expansion, a pair at depths e,f has conditional probability
at most `2*17^-max(e,f)` when max(e,f)>0. There are `2m+1` ordered
nonnegative-depth pairs with max(e,f)=m; the pair (0,0) costs 1. Their
old load products are bounded in expectation by G. All original 17
labels remain separate, and the finite sum is only enlarged to the
displayed positive infinite series.

At 19 apply DB3 to the normalized physical input `nu_* K_17`, whose
complete old tests include every original 17 cofactor and height:

    b_19^* <= ((89/64)G-1)/280
            = 51554082966349/295627584000000.

The actual auxiliary second killed loss has input `nu_* R_17`, which
is dominated by this physical input. Its integrand beta_19 is nonnegative,
so the loss comparison has the permitted direction. Accordingly the old
marginal loss of `zeta` relative to `nu_*` has total mass at most

    b := b_17^*+b_19^*
       = 97524110913629/295627584000000
       < 0.329889.                                      (DB5)

No intermediate conditioning is used. In particular for every old event
E and every nonnegative old function f bounded above by F,

    zeta(E) >= nu_*(E)-b,
    zeta f >= nu_* f-F*b.                               (DB6)

<a id="3-actual-band-mass-uniformly-for-every-inherited-test"></a>
#### 3. Actual band mass, uniformly for every inherited test

For integer h>=1 define

    t_h = min(1, (M-1)/h, (G-1)/[(h+1)^2-1],
                   min_(4<=t<=min(h,12)) theta_t/(h+1-t)).

Every expression in the minimum bounds `nu_*(A>=h+1)`, using respectively
total mass, the unit-floor mean, the unit-floor square, and a hinge.
Set `s_h=max(0,1-t_h-b)`. DB2 and DB6 imply the genuine actual-law bound

    eta(A<=h) >= s_h/D.                                 (DB7)

In particular, the best displayed hinge input at h=8 is t=6 and at h=10
is t=7, giving

    eta(A<=8) >= 95114429591641272698674519 /
                 2214676516815754992000000000
              > 0.04294732385,

    eta(A<=10) >= 54305460404654859422887321 /
                  1006671144007161360000000000
               > 0.05394558166.                         (DB8)

These bounds hold for the literal inherited old block A of every complete
final test L, not only for a chosen optimizer or coherent-centre layout.
If padding was needed, the literal A has smaller load than an arbitrary
fixed complete padded extension; the moment and event conclusions remain
valid with the literal A. The unit lower bound is retained.

For comparison, using only the DV mean in the same proof already gives
band8 > 0.01333075059 and band10 > 0.02474046103.

<a id="4-stronger-direct-ct-deficit-consumer"></a>
#### 4. Stronger direct CT deficit consumer

CT3 gives `Delta_tau(L)>=eta j_tau`, where
`j_tau=(tau-A^2)_+`, for `1<=tau<=484`. On the auxiliary source,

    nu_* j_tau >= tau-G,
    0 <= j_tau <= tau-1.

Therefore the same DB2/DB6 bridge gives the stronger uniform statement

    Delta_tau(L) >= eta j_tau
       >= max(0, tau-G-(tau-1)b)/D.                     (DB9)

The displayed maximum with zero is valid because the deficit is
nonnegative. In particular

    Delta_81(L) >= 93008506203820579159 /
                    47162761846200000000
                 > 1.97207505589,

    Delta_121(L) >= 20841212131452733423 /
                     4353485708880000000
                  > 4.78724716815.                     (DB10)

These concern exactly the actual AP11/T4, AP13/T6, killed17/T8 and
killed19/T8 law fixed above. No independent maximization of the current
positive terms is claimed here. In particular these corrections alone
are not a complete uniform KC bound or a later-prime continuation.

<a id="verification-boundary"></a>
#### Verification boundary

The arithmetic consumer checks a SHA-pinned DV source certificate and
its pinned upstream-section digest, recomputes every rational constant,
all finite band choices and both direct deficits. Its source data are
the existing DV1/DV5/DV6 theorem inputs; it does not itself re-prove the
161375-vector geometry. That separate existing reconstruction is
`verify_actual_deletion_profile.py --check actual_deletion_profile_certificate.json`.
The measure domination, support containment, full-height comparison and
universal quantifiers in this note are ordinary mathematical arguments,
not assertions that a finite arithmetic script established them in Lean.
