# Fixed product subcarriers absorb shared mixed-unit projections

The pure-unit interface of [report521](521-pure-unit-conditioning-restores-a-uniform-fibre-threshold.md) can fail because several mixed unit labels must all pay the same unit ancestor. A fixed rectangular subcarrier can remove those classes while retaining the product law needed by the existing geometric rows. The price is its actual Haar mass and a remaining conditional transport obligation. This report gives that ordinary bridge, an actual nine-label entry beyond the fixed-group521 test, and a family with arbitrarily many finite-height mixed unit labels using the same certificate.

The bridge reuses the product-and-delete/common-law construction of reports463--465, the divisor transport of520 and the strict pair calculation of521. It is a synthesis of those interfaces and normalization, not a new foundational result, a Lean formalization or a claim of literature novelty. No geometric optimization or source producer is rerun.

## General certificate and conclusion

Fix the old primes P={3,5,7,11,13,17,19} and any two finite disjoint groups R,S of odd primes outside P. Consider a finite family of pairwise distinct odd numerical moduli greater than1 supported on P union R union S. Every later label has its unique actual factorization

    m=d*n_R*n_S,  d P-smooth, n_R R-smooth, n_S S-smooth,
    n_R*n_S>1.

Retain the [report518](518-finite-prefix-templates-allow-arbitrary-old-residue-tails.md) finite old templates: for one p in{7,11,13,17,19}, two first-root-distinct prefixes of depths11,7,6 at3,5,p and a common prefix of depth4 at the other four old primes. Every complete later label has one fixed selector simultaneously choosing its split prefixes through the minimum of template depth and actual exponent. Old-only classes, deeper old digits and outside phases remain actual; no residue is selected again after seeing an old point.

At finite outside periods resolving all original classes, supply two fixed positive-Haar sets U_R,U_S. Put

    lambda_R=H_R(U_R)>0, lambda_S=H_S(U_S)>0,
    rho_R=H_R(. intersect U_R)/lambda_R,
    rho_S=H_S(. intersect U_S)/lambda_S.

Require their one common product U_R times U_S to avoid EVERY actual d=1 original class. The sets and their defining phases are fixed for the whole family and unchanged under the old-prefix repair. They may contain arbitrary within-group relations; only the separation between R and S is required. No numerical lower bound for lambda_R or lambda_S is assumed without a supplied certificate.

For each original outside cylinder, retain its actual conditional query price

    q_R(n,a)=rho_R(a mod n),  q_S(n,a)=rho_S(a mod n).

For a finite divisor-closed old-label set E containing1 and every old cofactor, define the three actual accounts, as in521:

    b_d^R=22 sum_(m=d*n_R, n_R>1) q_R(n_R,a_m),
    b_d^S=28 sum_(m=d*n_S, n_S>1) q_S(n_S,a_m),
    b_d^M=616 sum_(m=d*n_R*n_S, n_R,n_S>1)
                              q_R(n_R,a_m) q_S(n_S,a_m).

Every actual d=1 term has price zero by the subcarrier requirement. Original numerical labels are retained separately even if their cylinders coincide. Require, separately for X=R,S,M, fixed nonnegative matrices T^X on E times E with

    T^X_(d,e)=0 unless e divides d,
    sum_e T^X_(d,e)>=b_d^X,
    sum_d T^X_(d,e)<=1.

In addition, supply one positive pure-R unit-column reserve:

    0<eta<=1,  sum_d T^R_(d,1)<=1-eta.                (P1)

Each ancestor column is shared within its account. The three matrices and their reserve are certificate premises; removing the unit classes does not prove them for an arbitrary nonunit inventory. The constants22,28,616 are retained conditional scales, not a claim about reciprocal sums for arbitrary outside groups.

Define

    theta=min(1/3696,17eta/1232)>0.                   (P2)

Under these premises, the original whole-Haar survivor set satisfies

    H_full(original survivors)
       >lambda_R*lambda_S*theta/270000.              (P3)

## Why the existing rows transfer

Apply the full-common reference comparison before transporting the finite templates back. For fixed old points x_i, nonnegative weights w_i, and the same two references define

    h_d(w)=max(sum_i w_i 1[x_i=A mod d],
               sum_i w_i 1[x_i=B mod d]).

Then h_d<=h_e when e divides d. The actual union losses alpha_i,beta_i on the two groups and the incremental mixed loss gamma_i obey the same weighted accounting as520:

    t_i=22alpha_i, u_i=28beta_i, y_i=616gamma_i,
    w*t<=sum_d b_d^R h_d(w),
    w*u<=sum_d b_d^S h_d(w),
    w*y<=sum_d b_d^M h_d(w).

Every matrix bounds the right-hand side by the unchanged old matching inventory N(w). Because one product law is used, conditional survival s_i within the subcarrier satisfies exactly

    (22-t_i)(28-u_i)-y_i=616s_i,
    0<=t_i<=22, 0<=u_i<=28, y_i>=0.                 (P4)

All ordinary rows at threshold1/3696 from519/521 still apply to the smaller bad event s<theta. Only the former qualitative(21,26,35) pair needs the positive reserve. At its point x with Q_x<=21, take the singleton weight. Since h_1=1, (P1) sharpens the transport bound to

    t_x<=sum_e h_e-eta<=Q_x-eta<=21-eta.            (P5)

The other pair budgets remain t_x+t_y<=35, t_y<=22, u_x<=21, u_y<=26, u_x+u_y<=35 and y_x+y_y<=35. Increasing the pure deletions can only decrease the sum of pure survivor products. Extend each axis to total35 within these caps and write

    t=(a,35-a), a in[13,21-eta],
    u=(b,35-b), b in[9,21].

The same bilinear gap as521 is

    g(a,b)=(22-a)(28-b)+(a-13)(b-7)-35.

Its four corner values are136,28,17eta,84-7eta. For0<eta<=1 their minimum is17eta. Every interior value is a convex combination of corner values; hence

    616(s_x+s_y)>=17eta.

Both s_x,s_y<theta would imply their sum<2theta<=17eta/616, a contradiction. Thus the formerly qualitative pair and its derived clique rows share thresholdtheta. This proof does not use an odd conditional denominator.

The retained ordinary rows, order rows and safe Q<=19 region therefore give exactly the old-source margins used in518--521 for s>=theta. Old-prefix repair changes neither masks, conditional probabilities, original outside phases nor matrices. Off the same exceptional old set, all full fibres agree, hence so do their conditional probabilities under this fixed product law. The retained five source margins give

    nu{x:s_original(x)>=theta}>1/20000,
    nu<=(27/2)H_old.

The good old set has Haar mass>1/270000. At each such old point the original outside survivors CONTAIN their survivors inside U_R times U_S. Therefore

    H_outside(original survivors over x)
        >=lambda_R*lambda_S*s_original(x).

Integration proves (P3). Equality is not asserted: a projected mask can discard points that no original unit class forbids.

## Fixed projection masks preserve the required product

Each unit mixed original class is an actual rectangle C_m^R times C_m^S. Before evaluating any old point, assign each such class to one side, retaining its complete original phase and numerical identity. On that side, delete its projection. Delete every pure unit class on its sole nontrivial side as well. Take U_R,U_S as the complements of these finite unions and verify they have positive Haar mass.

Every original unit rectangle is now avoided. Coincident or nested projections are unioned once; they are not charged once per original label as lost measure. Remaining class prices still use their actual phases in these very sets. This is a sufficient construction, not a necessary form of every admissible subcarrier.

In particular, any number of mixed unit originals whose R projections lie in one fixed finite union C_R are screened by deleting C_R once. Arbitrary additional nonunit labels still require the account and reserve checks. This procedure deliberately retains a product subcarrier; it does not represent the full correlated law obtained by conditioning on the complement of all mixed rectangles.

## Nine actual labels and an unbounded finite family

Take R={23}, S={29,31}, E={1,3,9}, the split/common prefixes A=1,B=2 of the521 control, and these original classes:

| Modulus | Residue |
|---|---:|
|23|0|
|29|0|
|31|0|
|69|1|
|87|1|
|93|1|
|667|2|
|713|2|
|6003|1|

The nonunit old cofactors are3 or9, with actual old residue1; one fixed A-selector satisfies every old template. In the521 pure-unit base, the mixed unit classes667=23*29 and713=23*31 have scaled weights1 and14/15. Thus b_1^M=29/15>1. The old cofactor1 has only ancestor1, so521's fixed-group matrix premise fails for this actual family.

Both mixed unit classes have R phase2 mod23. Project both to the same R cylinder and remove it once. Then

    U_R={x:x mod23 not in{0,2}},
    U_S={x:x mod29!=0 and x mod31!=0},
    lambda_R=21/23, lambda_S=840/899.

All five original unit classes vanish in this product. The remaining nonzero accounts are

    b_3^R=22/21, b_3^S=29/15, b_9^M=22/21.

The supplied transports are

    T^R_(3,3)=1, T^R_(3,1)=1/21,
    T^S_(3,3)=1, T^S_(3,1)=14/15,
    T^M_(9,9)=1, T^M_(9,3)=1/21.

All other entries are zero. Every expense is paid exactly, destinations divide sources, and each column has capacity at most1. The pure-R unit reserve iseta=20/21. The common threshold is1/3696 and (P3) becomes

    H_full(original survivors)>7/8188092000.

This is a certificate entry beyond521's fixed-group test, not an integer covering counterexample and not a claim that521's test is necessary for noncoverage.

Now retain these nine labels and add any finite collection of further distinct mixed unit moduli

    23^j*29^k*31^ell,  j>=1, k+ell>=1,

with actual residues satisfying a=2 mod23; their deeper R and all S phases may be arbitrary. All original moduli remain distinct, so existing labels are not reinserted. Each new original cylinder lies in the same deleted R root2. Its conditional price is zero, and the subcarrier survival function is unchanged pointwise. Raising finite outside periods only lifts the same root conditions uniformly. Consequently the same lambda values, the three accounts of the four nonunit labels, transports, reserve, threshold and guaranteed density lower bound persist, for arbitrary finite numbers of these labels and arbitrary finite exponents.

The retained667 and713 terms still force the old521 mixed unit account to be at least29/15. The enlarged family's true survivor set may shrink outside the subcarrier; no equality of its full density is claimed. The family assertion follows from cylinder containment and uniform lifting, not from a bounded enumeration, and does not assert the result for an infinite covering family.

## Exact finite control and remaining boundary

The standalone standard-library [consumer](../../frontier/cover-geometry/mixed_unit_projection_control.py) reads the [literal nine-label input](../../frontier/cover-geometry/mixed_unit_projection_input.json). It checks original numerical labels, fixed selectors, exact phase counts, the deduplicated mask, all three matrices, the unit reserve, the pair corners and density arithmetic. Default execution compares the [retained result](../../frontier/cover-geometry/mixed_unit_projection_control.json); --output writes that result and --input-dir selects the adjacent input directory. Run:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_unit_projection_control.py

This program is an input/account control, not a second source producer. The old-source result and repair estimates remain those reused from518--521, with their attribution and verification boundaries.

The full all-unit-conditioned joint-law problem remains: retaining more of the nonrectangular survivor base can introduce cross-group dependence, and its rectangle probabilities cannot be replaced by products of marginal prices. The present extension avoids that unresolved step by exhibiting a positive fixed product subcarrier with enough certified conditional capacity.

The inherited source construction is attributed to Michael Schroeder, *Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1; the [library entry](../../../../../Library/Arith/schroeder2026nine.md) records the source and verification boundary. The shared-source margins and finite-template repair remain the ordinary results of reports518--521. Unrestricted Erdős#7 remains unresolved.
