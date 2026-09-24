# Pure-unit conditioning restores a uniform fibre threshold

Fix the old primes P={3,5,7,11,13,17,19}, outside groups R={23} and S={29,31}, and a finite family of congruence classes with pairwise distinct odd numerical moduli greater than1, supported on P union R union S. Impose [report518](518-finite-prefix-templates-allow-arbitrary-old-residue-tails.md)'s finite old templates: for one p in{7,11,13,17,19}, two first-root-distinct prefixes of depths11,7,6 at3,5,p and one common prefix of depth4 at every other old prime. Each complete later label has one fixed selector simultaneously choosing its three split prefixes through the minimum of the prescribed and actual exponent. Old-only classes, all deeper old digits and all outside phases are arbitrary, subject to these template conditions.

Define the actual conditional inventories C3 below. If all three admit the divisor-supported transports C4, the original family has survivor Haar mass strictly greater than

    71/79833600000 > 1/1200000000.                     (C1)

In particular it cannot cover the integers. This is a condition on the actual phase-dependent inventories. It does not assert noncoverage for arbitrary families supported on these ten primes.

The conditioning reuses the single product-and-delete principle of reports463--465. The inventory proof reuses [report520](520-actual-modulus-inventories-and-divisor-transport.md)'s divisor transport. The additional point is a uniform strict bound for the formerly qualitative(21,26,35) pair after deleting the unit23 powers. It makes all retained rows valid at the same positive conditional-fibre threshold1/3696. Ordinary proofs and exact scalar arithmetic are used; no new Lean verification or geometric optimization is claimed.

## Delete exactly the two groups of pure unit classes

Resolve all outside exponents in one finite product carrier X_R times X_S with its normalized Haar law H_R times H_S. Every later original label factors uniquely as m=d*n_R*n_S, n_R*n_S>1, with d P-smooth and n_R,n_S supported on their named groups.

A unit pure-R class has d=1,n_S=1,n_R>1. A unit pure-S class has d=1,n_R=1,n_S>1. Take their actual unions F_R^0,F_S^0, and set

    U_R=X_R minus F_R^0, lambda_R=H_R(U_R),
    U_S=X_S minus F_S^0, lambda_S=H_S(U_S).

Delete ALL these actual unit pure classes once. They are independent of the old point. A mixed unit class has d=1,n_R>1,n_S>1; it is NOT predeleted and stays in the mixed account below.

The original unit pure moduli are distinct, so union bounds and complete reciprocal inventories give

    lambda_R>=1-sum_(j>=1)23^-j=21/22,
    lambda_S>=1-[29/28*31/30-1]=781/840.               (C2)

Only an upper bound uses the complete infinite inventories. No absent class is inserted, and no actual finite residue is replaced. In particular both retained sets are nonempty.

Define one fixed pair of conditional laws

    rho_R=H_R restricted to U_R / lambda_R,
    rho_S=H_S restricted to U_S / lambda_S.

Their product is valid because the predeletions depend on disjoint groups. The S coordinates29,31 need not be independent after the pure-S deletions; only the cross-group product rho_R times rho_S is used. The old source is not conditioned, normalized anew or replaced.

For each actual outside cylinder retain its phase-dependent conditional probability

    q_R(n,a)=H_R(U_R intersect {z_R=a modulo n})/lambda_R,
    q_S(n,a)=H_S(U_S intersect {z_S=a modulo n})/lambda_S.

These are exact rational counts on the actual finite carriers. Replacing them by1/n would omit both the removed overlaps and normalization. The probabilities are common to every old point and every estimate for this original family.

## Three actual conditional accounts and the same ancestor matrices

Let E be a finite divisor-closed set of P-smooth integers containing1 and every old cofactor of a remaining later label. Take E={1} if none remain. Every unit pure label has already been removed; other original labels retain their numerical identities, original outside residues and original selectors.

For each d in E define

    b_d^R=22*sum_(remaining original m=d*n_R, n_R>1)
                                          q_R(n_R,a_m),
    b_d^S=28*sum_(remaining original m=d*n_S, n_S>1)
                                          q_S(n_S,a_m),
    b_d^M=616*sum_(original m=d*n_R*n_S, n_R>1,n_S>1)
                         q_R(n_R,a_m) q_S(n_S,a_m).    (C3)

Residues in these expressions are reduced modulo the respective actual group cofactor. Each complete original label contributes once. Pure unit accounts satisfy b_1^R=b_1^S=0, but b_1^M need not vanish. Different numerical labels are not merged merely because their old or outside cylinders coincide. There is no factor1/d in any account.

Require a supplied nonnegative rational matrix T^X for each X in{R,S,M}, indexed by d,e in E, satisfying

    T^X_(d,e)=0 unless e divides d,
    sum_e T^X_(d,e)>=b_d^X,
    sum_d T^X_(d,e)<=1.                              (C4)

These are exactly report520's ancestor constraints, now applied to the actual conditional probabilities C3. Each account has its own matrix. Each old-label column, including the unit column, has capacity1 per account; no descendant receives a private copy of an ancestor. C4 is a hypothesis to check for the supplied family, not a consequence of conditioning alone.

To justify the resulting multi-point budgets, first use the full-common reference comparison from518. For fixed old points x_i, weights w_i>=0 and the same two global references define

    h_d(w)=max(sum_i w_i 1[x_i=A modulo d],
               sum_i w_i 1[x_i=B modulo d]),
    N(w)=sum_(old labels in their full matching boxes) h_d(w).

A single actual selector for each complete original label gives its weighted activation at most h_d(w). Let alpha_i,beta_i be the actual pure-R and pure-S union losses under rho_R,rho_S. Let gamma_i be the incremental mixed union loss inside their surviving product. Let raw_i be the sum of all active mixed rectangle probabilities under rho_R times rho_S, including mixed unit labels, so gamma_i<=raw_i. Put

    t_i=22alpha_i, u_i=28beta_i,
    y_i=616gamma_i, c_i=616raw_i.

The union bound, using the ACTUAL probabilities C3, gives

    w*t<=sum_d b_d^R h_d(w),
    w*u<=sum_d b_d^S h_d(w),
    w*y<=w*c<=sum_d b_d^M h_d(w).

For e|d both reference cylinders at d lie in their e cylinders, so h_d(w)<=h_e(w). C4 therefore bounds each right side by sum_e h_e(w)<=N(w), exactly as in report520. All inequalities concern the same original family and its same fixed conditional product law. Ancestor columns are accounting devices, not replacement original classes or new selectors.

The pure survivors depend on disjoint coordinate groups under that product law. Thus, for CONDITIONAL later survival s_i,

    0<=t_i<=22, 0<=u_i<=28, y_i>=0,
    (22-t_i)(28-u_i)-y_i=616s_i.                       (C5)

These are the unchanged capped geometric-row premises. The two within-group coordinates of S can have arbitrary conditional dependence.

## The removed unit23 powers force a strict pure-R margin

For the qualitative pair of [report506](506-finite-height-pair-excludes-zero-support-at-a-closed-boundary.md), take old inventories Q_x<=21,Q_y<=26 and shared-selector inventory N_xy<=35. Q_x includes the unit old cofactor1.

At each outside power23^j the pure unit class, if present, has already been removed. Hence the remaining active pure-R labels at x have at most Q_x-1<=20 distinct nonunit old cofactors. Numerical distinctness permits at most one original class for each complete d*23^j label. Its raw Haar mass is23^-j. Summing all original finite powers and then bounding by the complete geometric series gives

    H_R(remaining pure-R union at x)<=20/22.

Intersecting that union with U_R can only decrease its numerator. After the one common normalization,

    t_x=22alpha_x<=20/lambda_R<=440/21
                          =21-1/21.                  (C6)

This argument does not assume that the twenty largest prices are jointly attained, that an absent unit class was inserted, or that selectors are chosen after observing x. It counts the actual permitted nonunit labels for every fixed x. Even if no unit pure class is present at some exponent, that absent numerical label contributes nothing.

The remaining conditional transport inequalities give the same closed pair domain as506:

    0<=t_x<=21-1/21, 0<=t_y<=22, t_x+t_y<=35,
    0<=u_x<=21,      0<=u_y<=26, u_x+u_y<=35,
    c_x+c_y<=35.

Increasing pure deletion decreases the sum of pure survivor products. Each axis can be extended within these closed bounds to total35: its coordinate caps sum to more than35. At the minimum write

    t=(a,35-a), a in[13,440/21],
    u=(b,35-b), b in[9,21].

Subtract the mixed bound35 and put

    g(a,b)=(22-a)(28-b)+(a-13)(b-7)-35.

It is affine in each variable. The four exact corner values are

| a | b | g(a,b) |
|---|---|---:|
|13|9|136|
|13|21|28|
|440/21|9|17/21|
|440/21|21|251/3|

Every interior value is a convex combination of these values. Therefore C5 gives

    616(s_x+s_y)>=17/21>1/3,
    s_x+s_y>=17/12936>2/3696.                         (C7)

The pair cannot have both conditional survivals below theta0=1/3696. This strengthens this particular pair from a qualitative zero exclusion to the same uniform positive threshold already used by the ordinary rows.

Conditioning has not preserved the old odd-period endpoint proof. For example, unit root deletions at23,29,31 leave22*28*30=18480 equally weighted outside points. A scaled raw mixed count can have the form616I/18480=I/30, and I=1050 gives35. This observation only invalidates the old parity exclusion; it does not assert that that integer count is realized by a given pair. The strict inequality C7 uses the missing unit contribution instead of any odd conditioned denominator.

## All existing rows now share one conditional threshold

The ordinary pair, triple and four-point rows use the same weighted inventories, axis caps and identity C5; they remain valid for strict s<theta0 by the retained proofs in reports481,499,501,505 and the row summary in519. C7 handles all qualitative(21,26,35) pairs, including their symmetric orientation. Their binary triangle cliques therefore also hold for that same threshold. The order rows follow because increasing either old reference box adds original active classes with their fixed outside cylinders, under one unchanged conditional law. Safe Q<=19 still supplies s>=1/77>theta0.

Thus every row used by the exact old-source price certificate applies to the upward support of the CONDITIONAL theta0-bad event. The same signed row loads, old-prime caps,44 reference orbits,23408 finite profiles and complete infinite overflow are retained. No new geometry or price optimization is required. For each role p, the [report517](517-joint-anchor-budgets-close-five-split-patterns-with-finite-prefix-agreement.md) worst-type bound and [report491](491-all-split-common-patterns-force-six-shallow-classes.md) direct nonworst bound give, on the same completed old source,

    nu({x:s_comparison(x)>=theta0})>=delta_p.           (C8)

The nonworst argument uses its Q<=19 safe region, so it also meets this positive threshold. The conclusion does not substitute a bound for a different source or a mere exact-zero result into C8.

## Prefix repair preserves the conditional law and yields whole-Haar density

Repair only old residues as in518. Unit pure and mixed classes have d=1, so their old template conditions are vacuous and their outside phases are unchanged. Consequently F_R^0,F_S^0,U_R,U_S,lambda_R,lambda_S,rho_R,rho_S, all q_R/q_S values, the accounts C3 and the supplied matrices C4 are identical before and after repair. The old-only family and chosen completed source nu also stay fixed.

Outside the same old exceptional set E518, the original and comparison full fibres agree at every outside point. They therefore have equal conditional survival probabilities under this same rho_R times rho_S. Report518's source error satisfies

    delta_p-nu(E518)>1/20000.

Combining this with C8 gives

    nu({x:s_original(x)>=theta0})>1/20000.              (C9)

The retained old-source density cap nu<=(27/2)H_old implies that this set of actual old-only survivors has H_old mass greater than1/270000. At any such old point, the ORIGINAL full-Haar outside survivor fraction equals lambda_R*lambda_S*s_original(x): unit pure classes had been deleted exactly, mixed unit classes and all other originals remained in the conditional fibre.

Integration under the original whole Haar product therefore gives

    H_full(original survivors)
       >lambda_R*lambda_S/(3696*270000)
       >=(21/22)(781/840)/997920000
       =(71/80)/997920000
       =71/79833600000>1/1200000000.                  (C10)

This establishes C1 under the stated conditional-transport hypotheses. No final-survival conditioning changes the old marginal, and no actual outside law is selected separately for different old points. The positive density supplies an uncovered original integer by finite CRT.

## What conditioning resolves and what it leaves open

Actual unit labels23,29,31 all vanish from the two pure accounts after the common groupwise deletion. Their former overloaded unit pure account in520 is therefore not an obstruction to C4 by itself. Conditional probabilities of the remaining actual classes must still be evaluated: normalization may increase them, and conditioning alone does not prove the three transport matrices exist.

Mixed unit classes remain a real unit-column obstruction. With only the three unit root deletions at23,29,31, suppose unit mixed classes23*29 and23*31 both have outside phases surviving those roots. Their individual scaled conditional masses are1 and14/15, so b_1^M=29/15>1. The unit old cofactor has only the single ancestor1; no C4 matrix can pay that raw account. Phase overlap may offer other methods, but it is not erased by the current raw inventory definition.

Predeleting ALL mixed unit classes would remove their raw unit demands but generally destroy the product rho_R times rho_S. A single unit rectangle involving23 and29 already couples those coordinates after conditioning. In that model the exact pure survivor term would be the joint probability rho(A_R^c times A_S^c), which need not equal(1-alpha)(1-beta). C5 and the present row transfer would need a new joint-condition argument.

Even the total unit-survivor mass does not determine the needed conditional query prices. Keep unit0 classes at23,29,31 and a fixed later class1 modulo3*23*29. Compare two unit23*29 classes with outside pairs(1,1) and(1,2). Their unit-survivor masses coincide, but after all-unit conditioning the fixed later outside cylinder(1,1) has probability0 in the first model and1/615 in the second. The actual overlap and phase records are indispensable. This is an interface counterexample, not an integer covering example.

## An actual family that crosses the old unit obstruction

The following eight original classes give a finite control of the new interface:

| Original modulus | Original residue |
|---|---:|
|23|0|
|29|0|
|31|0|
|69|1|
|87|1|
|93|1|
|667|2|
|6003|1|

Use R={23}, S={29,31}, E={1,3,9}. All nonunit old residues are1 at their actual3 or9 cofactors, so one fixed A-selector satisfies the old finite templates. The unit classes have vacuous old conditions. In particular667=23*29 is a mixed unit class and remains in the mixed account;6003=9*23*29 has old cofactor9.

The predeleted classes are exactly the three unit root exclusions. Literal counts give

    lambda_R=22/23, lambda_S=(28*30)/(29*31)=840/899.

The conditional accounts have the following nonzero entries:

    b_3^R=1,
    b_3^S=1+14/15=29/15,
    b_1^M=b_9^M=1.

They admit the explicit payments

    T^R_(3,3)=1,
    T^S_(3,3)=1, T^S_(3,1)=14/15,
    T^M_(1,1)=T^M_(9,9)=1,

with every other entry zero. Every expense is paid exactly, every destination divides its source, and every column has capacity at most1 in each account. The ancestor1 is shared within its S account and is not copied per source.

The raw, unconditioned test of520 fails for every partition of these three outside primes. At least two of23,29,31 must lie in one group, and even the smallest scaled unit pure demand is

    22*(1/29+1/31)=1320/899>1.

A unit old label has only the unit ancestor, so no raw ancestor matrix can pay that demand. All eight global partitions are included in the exact control. This is an old-test failure and a new-test entry, not an integer covering example or a claim that arbitrary conditional inventories are feasible.

## Reproduction of the phase and strictness checks

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_unit_conditioned_transport.py

The portable standard-library [consumer](../../frontier/cover-geometry/pure_unit_conditioned_transport.py) reads the [literal eight-class input](../../frontier/cover-geometry/pure_unit_conditioned_transport_input.json) and the retained [finite-template source result](../../frontier/cover-geometry/finite_prefix_template_source.json). It factors the actual numerical moduli, checks their distinctness and fixed old selectors, counts the common pure-unit survivor sets, evaluates every actual q_R/q_S phase, and verifies all supplied ancestor row and column sums. It also checks each raw partition's unit obstruction, the four strict pair corners and the final density arithmetic. Default execution compares the [retained result](../../frontier/cover-geometry/pure_unit_conditioned_transport.json); --output writes it, and --input-dir selects the input directory.

These finite checks give an actual entry to the conditional theorem. They do not replace its all-family transport proof, its old-source comparison or the prefix-repair argument. No geometric rows or source producers are recomputed, and no LP or Lean build is claimed.

The old source construction and its arbitrary-height verification boundary remain those attributed through reports517--520 to Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1; see the [library entry](../../../../../Library/Arith/schroeder2026nine.md). The conditional transport, strict pair estimate and integration are ordinary mathematical proofs. Unrestricted Erdős#7 remains unresolved.
