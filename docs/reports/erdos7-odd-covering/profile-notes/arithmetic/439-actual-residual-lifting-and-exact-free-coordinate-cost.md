[Index](../../marked_head_profile.md) · [Height lifting](../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md) · [Minimum sources](435-minimum-height-two-sources-and-a-nine-point-flow.md)

# Actual residual lifting: exact free-coordinate cost and the remaining joint problem

These are repo-derived ordinary finite mathematical deductions. No Lean certification or literature priority is claimed. The definitions of the complete-layout invariant and its one-prime upper estimate are those in [Chapter08](../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md); the height-lifting certificate is [Chapter09](../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md); actual minimum-cover provenance is from [350](../321-384/350-extremal-paired-branch-and-source-support.md) and [376](376-complete-prime-chain-transport-and-joint-prefix-laws.md); the fifteen-point lower bound is [435](435-minimum-height-two-sources-and-a-nine-point-flow.md). The full mixed layout inventory is retained throughout.

## 1. An exact fixed-marginal free-coordinate theorem

For a positive integer N, a complete layout b assigns one residue b_d modulo d to EVERY divisor d of N, including d=1. Its load is

    L_b(x) = sum_{d|N} 1[x=b_d mod d],
    Gamma_N(mu) = max_b E_mu L_b^2.

The residues for different divisors are independent choices; they need not be nested or coherent. Put

    F(M) = sum_{a,b|M} 1/lcm(a,b)
         = product_{p^H || M} [1 + sum_{j=1}^H (2j+1)/p^j].

Let gcd(Q,M)=1 and let mu be ANY probability on Z/Q. Identify Z/(QM) with Z/Q x Z/M. Then

    min_{nu probability on Z/(QM), pi_Q*nu=mu} Gamma_QM(nu)
      = Gamma_QM(mu x Uniform_M)
      = F(M) Gamma_Q(mu).                                      (F1)

All fibres over the support of mu are free in this minimization. Restricting the extension to an actual survivor relation can only increase the minimum or make a prescribed marginal infeasible.

Proof of the universal lower bound, with all quantifiers explicit. Choose one old layout b* maximizing Gamma_Q(mu). For EACH center t in Z/M, choose the complete full layout whose residue for divisor d e (d|Q,e|M) is the CRT join of b*_d and t mod e. This is a legitimate full layout because coprimality makes d e a unique label. It uses the SAME old maximizing layout at every new divisor level and at every center. Its load factors pointwise as

    L_t(x,y) = L_b*(x) K_t(y),
    K_t(y) = sum_{e|M} 1[y=t mod e].

For every fixed y, averaging over a uniform center t gives

    E_t K_t(y)^2 = sum_{e,f|M} Pr_t[t=y mod lcm(e,f)] = F(M).

Thus for EVERY coupling nu with old marginal mu,

    E_t E_nu L_t^2 = F(M) E_mu L_b*^2 = F(M) Gamma_Q(mu).

One full layout has moment at least this average, proving the lower bound without independence of nu. Only the deliberately sampled layout center is random.

For the upper bound at the uniform product, apply Chapter08 T1 with delta=0 successively to the prime-power factors of M. Each step contributes exactly the displayed local factor. Equivalently, group an arbitrary full layout by its M-divisor e; conditional intersections at levels e,f have uniform probability at most 1/lcm(e,f), and Cauchy--Schwarz bounds each pair of old layout loads by Gamma_Q(mu). This covers ALL independent old and mixed phases, not just the centered subfamily. The lower bound proves equality.

A second proof of minimization, useful as a check, averages an arbitrary nu over translations in the new M-coordinate. Every such translation permutes the complete layout family, hence preserves Gamma. Convexity of Gamma implies

    Gamma_QM(mu x Uniform_M) <= Gamma_QM(nu).

The prime factorization of F follows by writing e,f through their prime exponents: exactly 2j+1 ordered exponent pairs have maximum j.

Consequences. For any nonempty R subset Z/Q, product support gives

    min_{nu supported on R x Z/M} Gamma_QM(nu)
      = F(M) min_{mu supported on R} Gamma_Q(mu).                (F2)

For every joint probability nu and its old marginal mu, the normalized quantity obeys

    Gamma_Q(mu)/F(Q) <= Gamma_QM(nu)/F(QM).                      (F3)

Uniform free-coordinate extension attains equality. Neither formula covers height extension at a prime already dividing Q. Neither formula asserts tensorization for arbitrary nonuniform new-coordinate laws or arbitrary survivor supports. Chapter15's fixed-shape tensorization and its incoherent-layout warning remain unaffected.

Taking Q=1 gives the unavoidable full-inventory floor Gamma_B(nu)>=F(B) for every probability nu, with equality for uniform measure. For the squarefree product of the fourteen primes5,7,...,53,

    F(B)=25836912640000/2775498881101,
    F(B)-9=857422710091/2775498881101>0.                         (F4)

Therefore nine is not an admissible uniform target for the COMPLETE Gamma_B when arbitrary outside primes are added. The target nine below concerns the specified5/7 head and its associated transfer. Any use of M1/M2 on a larger full carrier needs a compatible budget D, or an existing head-tail or weighted/partial-inventory formulation. Formula F4 concerns all probability laws, including Haar; it is not a covering counterexample.

## 2. What the actual minimum-cover projection supplies

Assume an odd distinct cover exists and choose one lexicographically minimizing (number of classes, sum of moduli), as in report350. Let

    Q = 3^h B, h>=1, gcd(3,B)=1,
    R_3 = Z/B minus the union of ALL actual 3-free original classes.

Report350's prime compression makes the support an initial segment of the odd primes, so the assumed 5/7 support includes3 and h>=1. Suppose 5^2 and7 divide B. Let S=pi_175(R_3). The word "projection" here includes all remaining prime coordinates and all higher5/7 digits in each fibre.

Report376 implies that S meets every product of a complete ternary subtree of depth two in the 5-tree and a five-element first-digit set in the 7-tree. To see this at the truncated heights, extend any specified shallow trees to the full original 5/7 heights and apply report376 there; the resulting actual R_3 witness projects into the specified shallow product. This does not substitute partial prime tails into the label-transport construction; it only projects an already proved full-height witness.

Report350 normalizes the original pure prime classes to 0 mod p and forces original25 to be present. Comparable original classes are disjoint, so a_25 lies in a nonzero first-5 root. Consequently

    S subset {nonzero first-5 root} x {five children} x {nonzero first-7 root},

and one level-two five-adic leaf across every seven column is absent. Hence

    |S| <= 4*5*6 - 6 = 114.                                   (P1)

The ambient abstract carrier has 140 points, so this is a genuine necessary restriction for the actual projection. Additional original35/175 exclusions apply only when those moduli are actually present; their presence does not follow merely from 5^2*7 dividing the LCM.

Every probability mu supported on S admits an actual supported lift nu on R_3 preserving its pi_175 marginal: choose one witness x_s in each nonempty fibre and put mass mu(s) there. This preserves every modulus-dividing-175 test, and hence Gamma_175, exactly. It imposes no useful bound by itself on Gamma_B. Formula F1 already shows why literal preservation of the full Gamma cannot hold even for newly adjoined completely free coprime coordinates.

The simple necessary restrictions in P1 do not eliminate the sharp source from report435. Relabel it as

    {(r,a,a+1): r=1,2,3; a=0,...,4}.

It avoids seven-root0; an excluded25 leaf can lie in root4, leaving the source untouched. This only checks compatibility with these projected necessary conditions. It is NOT a realization as R_3 of an actual minimum odd cover.

## 3. The exact finite lifting obligation

Let R be a nonempty actual fine survivor set, pi:R->S its surjective coarse projection, and Lambda the finite family of ALL full fine layouts. Put c_lambda(x)=L_lambda(x)^2. For a fixed probability mu on S, set

    V_R(mu) = min_{nu supported on R, pi_*nu=mu}
                 max_{lambda in Lambda} E_nu c_lambda.

All couplings form a nonempty compact polytope. Finite minimax gives the exact formula

    V_R(mu) = max_{theta probability on Lambda}
                sum_{s in S} mu(s) min_{x in R_s}
                    sum_lambda theta(lambda)c_lambda(x).       (M1)

Proof. Replace the finite maximum by a maximum over distributions theta. Interchange min over nu and max over theta by finite minimax. For fixed theta and fixed marginal mu, each fibre independently assigns its mass to a point minimizing that SAME theta-potential. This yields M1. The full layout mixture theta is chosen once and is shared by all fibres; no per-fibre phase re-selection is allowed.

If K_C={mu supported on S: Gamma_coarse(mu)<=C} is nonempty, a coarse theorem proves only that nonemptiness. The existence of a full law with both coarse budget C and full budget D is equivalent to

    max_theta min_{mu in K_C}
      sum_s mu(s) min_{x in R_s} sum_lambda theta(lambda)c_lambda(x)
      <= D.                                                    (M2)

The minimum over mu occurs INSIDE the maximum over theta. This follows by applying finite minimax to the single polytope of fine laws whose coarse marginal belongs to K_C. For a specified theta the inner fibre minimization remains valid. Compactness ensures attainment. This is a finite-LP reformulation of the missing joint estimate, not a proof that the desired D holds.

## 4. A scalar all-height obstruction already below the current target

Apply Chapter09 H1 at coarse exponents H5=2,H7=1 and allow both final heights to be arbitrarily large. Its all-height constants are

    B5=29/24, B7=11/9, B=319/216.

For 68/15 <= C <= 46/9, the minima in H2 select

    lambda5=(C-1)/32,
    lambda7=sqrt(C)/12,
    lambda57=(C-1)/840,
    lambda(C)=109(C-1)/3360 + sqrt(C)/12.

The resulting scalar full-survivor bound is

    J(C)=[(319/216)C-lambda(C)]/[1-lambda(C)].                    (H3)

Its being below nine is equivalent, when lambda<1, to

    (319/216)C+8lambda(C)<9.                                   (H4)

Report435's displayed admissible minimum source has exact minimax Gamma=68/15. Therefore any uniform scalar theorem for every source on the ambient carrier must use C>=68/15. But at C=68/15, sqrt(C)>17/8, so

    (319/216)C+8lambda(C)-9
      > 5423/810 + 5777/6300 + 17/12 - 9
      = 407/14175 > 0.                                        (H5)

Thus even the best possible universal scalar seed cannot make this particular all-height H1 certificate deliver Gamma<9. The three first-moment bounds, their minimum, and B are nondecreasing in C, so larger universal C cannot repair it; if lambda>=1 the certificate supplies no positive survivor guarantee at all. The infinite-height constants are suprema of finite-height coefficients, and their strict excess already occurs for sufficiently large finite heights.

There is also an explicit finite witness. Add four levels at each prime, giving final exponents K5=6,K7=5. With C=68/15, the exact finite H1 constants satisfy

    B=2214518/1500625,
    lambda > 30614733/105043750,
    CB+8lambda-9 > 3396739/157565625 > 0.                        (H6)

The same rational lower bound sqrt(C)>17/8 supplies both strict inequalities. On the whole C interval used above, sqrt(C)<7/3 gives lambda<9913/30240<1, so this is failure to cross the numerical target with a valid positive denominator, rather than an undefined application. For the minimizer selection, when 1<=C<=D^2 the third H2 expression is smallest, while for C>=D^2 the square-root expression is smallest. Writing t=sqrt(C), the latter comparison follows from (t-D)(Dt+1)>=0; this proves the selection throughout the stated interval rather than by sampling its points.

This is a failure of the scalar certificate, not a lower bound of nine on the true fine survivor minimax. It does not contradict one-axis lifting: with K7=1 and C=149/30, H1 gives 16927/2523<9 for arbitrary 5-height under its actual-family hypotheses. It also does not contradict the possibility that stronger actual-cover restrictions exclude the abstract source, or that a common multilevel law has better weighted moments than the scalar bound.

[The integer joint-moment certificate](441-integer-joint-moments-improve-two-axis-height-lifting.md)
changes the mixed-moment estimate itself. Under its full actual-family
seed hypothesis, it gives 3780053/430196 below nine at C=68/15 for all
finite additional 5/7 heights. Thus H5--H6 obstruct the displayed H1
formula, not all quantitative extensions from a scalar seed. Neither
formula supplies a missing seed on the complete cofactor carrier.

## 5. Exact scope of a solution of every 140-point source

A universal supported-law theorem at height(2,1) would:

1. apply to the actual S=pi_175(R_3), provided both coarse prime heights occur;
2. give an actual law on R_3 with those SAME coarse marginals and all six coarse tests bounded;
3. become a valid seed for subsequent results only after their original-family support, full divisor inventory, actual heights, and same-law hypotheses are checked.

It would not itself bound deeper5/7 tests, tests involving outside primes, mixed cofactors crossing those coordinates, or their common-law correlations. Even unlimited improvement of a single universal coarse scalar does not pass the two-axis H1 route to nine, by H5. No new prime-support exclusion beyond already known restricted noncoverage results follows from the 140-point theorem alone without such an additional bridge.

The shortest explicit remaining obligation is therefore a bound on M1/M2 for the ACTUAL minimum-cover residual, using original-label restrictions and joint fibre incidence. Possible sufficient inputs include a common multilevel weighted-layout profile, a source-aware extension law with simultaneous mixed-test estimates, or an alternative certificate that retains information discarded by scalar Gamma. The existence of a supported lift and the existence of a good projected law are already separate, closed finite facts.

The [exact companion](../../frontier/cover-geometry/free_coordinate_completion_controls.py) checks F(M) by divisor-pair summation and prime factors, the pointwise coherent-center identity, coprime multiplicativity, the rational H1 constants and minimizer domain, and the explicit finite-height obstruction. Its JSON output includes exact rational enclosures of the H1 expression. The general statements use the ordinary proofs above; finite checks alone do not establish unrestricted source or minimum-cover conclusions.

Run the exact controls with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/free_coordinate_completion_controls.py
