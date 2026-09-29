# Actual pure-support averaging gives a finite all-height query interface

For a fixed actual finite pure inventory, the root-balanced laws of [Report590](../550-599/590-root-balanced-star-screening-allows-complete-height-four-tails.md) admit an exact finite reduction of a specified source optimization: every dominated measurable outside kernel can be replaced by a kernel depending only on the outside q-squared prefixes, preserving mass and shallow support while not increasing any of the declared aggregated all-height query suprema. This reduction keeps the actual higher-pure holes. It does not replace them by full Haar tails.

The finite boundary needs actual prefix masses and atom density/capacity factors, together with the actual labeled compatibility predicates. Prefix masses alone do not recover the reading of every specified higher query. The theorem permits density variation between conditioning atoms, including atoms within the same first root; its proof requires constant density on each surviving conditioning atom. It can fail for a merely capped base law with density variation inside one such atom, or for a query menu lacking the needed descendants.

This is an ordinary mathematical extension of the conditional averaging argument already used in [Report682 section4](682-joint-retention-and-central-source-changes-preserve-the-obstruction.md). Report590 supplies the actual root-balanced pure laws. Actual root/edge union restriction and its use in full query interfaces already occur in Reports623,629,637,640 and680 and the earlier actual-union bridge; they are background here, not claimed as a new source-existence theorem. The extension below handles every retained outside coordinate, arbitrary finite higher-pure holes, explicit finite query representatives and a lossless finite optimization within the stated class. No Lean verification or new positive covering-problem gate is claimed.

## 1. Exact hypotheses and source class

Fix a finite set Q of outside primes; the current application is Q={7,11,13,17,19}. Let h_q be p-adic Haar probability. At q exclude the actual first pure root, or one fixed auxiliary root if that label is absent. For each other first root r, let S_(q,r) be its survivor after ALL actual pure q-power originals. Each original has its one globally fixed residue, and the pure inventory is finite, with at most one original at each numerical modulus.

Write

    r_q=1/(q-1),
    t_(q,r)=h_q(S_(q,r)),
    d_(q,r)=r_q/t_(q,r).

Report590's law is exactly

    rho_q|S_(q,r)=d_(q,r) h_q|S_(q,r).                 (P1)

The root-relative deletion bound gives t_(q,r)>0 and d_(q,r)<=D_q=q/(q-2). Its reference cylinder caps are

    u_q(1)=r_q,
    u_q(e)=D_q q^(-e), e>=2.                          (P2)

Thus Report590's density is constant ON EACH ACTUAL SURVIVING ROOT, although it is zero in the deleted holes and may differ between roots. Arbitrary higher pure heights are allowed, but the family under consideration is finite. This is more structure than the inequalities rho_q(C)<=u_q(height(C)) alone.

The proof below also applies under the following weaker atomwise hypothesis, which includes the root-balanced case. Let E_q be a fixed finite union of p-adic cylinders (the actual surviving support), and for every positive q² atom alpha require

    rho_q|_(E_q intersect[alpha]_(q²))
      =d_q(alpha) h_q|_(E_q intersect[alpha]_(q²)),
    d_q(alpha)>0.                                    (P1a)

Use arbitrary FIXED positive root normalizers u_q(1), and geometric deeper normalizers u_q(e)=D_q q^(-e) for e>=2, with fixed D_q>0. Root balance and d_q(alpha)<=D_q are not needed for the averaging and finite-menu identities; when the application also declares reference cylinder caps, those are separate hypotheses to verify. The source rho_q is a fixed probability law, common to all cells and comparisons. Atoms with zero rho_q mass are omitted. Density can differ across q² atoms even within the same first root. In formulas below put S_q=E_q and d_q(alpha)=d_(q,parent(alpha)) for the Report590 special case.

This extension includes actual central3/5 weak-leaf capacity laws when they are uniform within each surviving conditioning leaf. Averaging all seven coordinates is legitimate only when the support bounds are measurable on the selected joint conditioning atoms and every grouped central query is represented with its OWN actual all-height normalizers and full coefficient sum. The outside formula(P2) must not silently replace the central selectors or central gamma factors of Report640. A query with prescribed depth or phase is not an all-height grouped screen, and arbitrary source changes are not covered.

Let c range over a finite central-cell set, such as the80 mod9/mod25 cells in686. Put rho_Q=product_q rho_q. Consider outside submeasures

    eta_c=f_c rho_Q, 0<=f_c<=U_c.                     (P3)

Here U_c is a fixed function of the outside q² prefixes, with0<=U_c<=1. It may include all actual unary and pair compatibility predicates and any already proved prefix-measurable product domination factor. In particular it is zero on each forbidden head-prefix configuration. Full original identities and their globally fixed phases are retained when constructing these predicates and routing fees.

No factorization of f_c across outside coordinates is required. The kernels may depend measurably on arbitrarily deep outside digits. The upper envelope U_c and the pure laws must be common to every comparison using them; a different base law cannot be silently chosen for a query.

For a support T subset Q and nonnegative central coefficients a_c, define the actual all-height normalized screen

    N_T(a,eta)=sup_(e_q>=1,b_q mod q^e_q, q in T)
       [sum_c a_c eta_c(product_(q in T)[b_q]_(q^e_q))]
       /product_(q in T)u_q(e_q).                     (P4)

For T empty this is the weighted mass. Every queried cylinder tuple is ONE GLOBAL choice across the complete central sum. The allowed menu must contain all the descendants used below, with their original normalizers. Central selectors may be fixed first, and maximized afterwards. Different fixed heights, or a small prescribed subset of phases, are a different task.

## 2. Averaging on actual surviving prefix atoms

For a q² residue alpha define

    A_(q,alpha)=S_q intersect[alpha]_(q²),
    mu_q(alpha)=rho_q(A_(q,alpha)).

Use only Omega_q={alpha:mu_q(alpha)>0}. A null prefix is omitted and no division by its mass is made. Write rho_(q,alpha) for rho_q conditioned on A_(q,alpha), and Omega=product_q Omega_q.

Define a SINGLE operator on every central kernel:

    fbar_c(omega)=integral f_c(x) product_q rho_(q,omega_q)(dx_q),
    etabar_c=fbar_c(prefix(x)) rho_Q.                 (P5)

Conditional averaging preserves every eta_c mass and every joint q²-prefix mass. It also preserves0<=fbar_c<=U_c, because U_c is constant on each prefix rectangle. Thus every actual shallow head support predicate and prefix-measurable domination bound remains true. This includes a product of actual unary restrictions with prescribed omitted-coordinate masses when that product is expressed in U_c.

If a finite family of kernels carries pointwise linear priority inequalities across numerical corners whose coefficients and right-hand sides are fixed or measurable on the conditioning prefixes, applying the SAME positive averaging operator to them preserves those inequalities. Deep-digit-dependent coefficients require a separate argument. This observation does not establish an unproved factorization or a nonlinear continuation-policy constraint.

## 3. The all-height comparison, with one global descendant

For every T and every nonnegative a,

    N_T(a,etabar)<=N_T(a,eta).                        (P6)

To prove this, fix a query tuple for etabar. Divide its queried coordinates into shallow roots R and deeper coordinates B=T minus R. A query at q in B lies in one q² prefix alpha_q. If that prefix is null its reading is zero, so assume all such prefixes are positive.

For q in B the source density on the actual survivor inside alpha_q is the constant d_q(alpha_q) from(P1a), equal to d_(q,parent(alpha_q)) in(P1). Put

    kappa_q(alpha_q)=d_q(alpha_q)/D_q.        (P7)

The normalized mass of ANY deeper cylinder C inside that prefix is at most kappa_q(alpha_q). For etabar, the contribution of the B-coordinates therefore has an upper bound equal to product_B kappa_q times the conditional average, inside the chosen surviving prefix rectangle, of the remaining fixed integrand. That integrand includes the sum over ALL c with coefficients a_c, the same shallow-root queries, and integration of all unqueried coordinates.

Now choose M_q>=2 resolving all actual pure holes at q. Each A_(q,alpha_q) is a finite disjoint union of INTACT height-M_q cylinders. Partition the product surviving prefix rectangle by these cylinders. The conditional average of the fixed integrand is a convex combination of its averages on those intact rectangles. Its weights depend only on the actual pure laws and chosen prefixes, not on c, the value of f_c, or a separately selected source.

On each intact rectangle, the original source density in the B-coordinates is exactly product_B d_q(alpha_q), while the product query normalizer is product_B D_q h_q(cylinder). Consequently the corresponding normalized OLD query reading is exactly product_B kappa_q times that rectangle's integrand average, with the SAME shallow-root queries and the SAME complete central sum.

The old supremum contains every such global descendant tuple. It is at least their convex combination, which bounds the selected new reading. Taking the supremum over new query tuples proves(P6).

This finite partition resolves the pure holes, not f_c. Arbitrary bounded measurable kernels are allowed; their integrals on the partition atoms exist. No differentiation theorem, limit interchange or finite-prefix hypothesis on the original kernel is used. No descendant is selected independently for different central cells.

## 4. Explicit finite whole/root/square/deep representatives

For a prefix-constant kernel, its complete normalized screens have finite EXACT menus. Define tokens on Omega_q:

    whole_q(alpha)=1;
    root_(q,r)(alpha)=1_(parent(alpha)=r)/u_q(1);
    square_(q,beta)(alpha)=1_(alpha=beta)/u_q(2);
    deep_(q,beta)(alpha)=
        [kappa_q(beta)/mu_q(beta)]1_(alpha=beta).       (P8)

The whole token is used for an unqueried coordinate. For a queried coordinate use the live-root, square or deep tokens. All denominators refer to positive prefix masses. For a global token tuple tau and one fixed central selector a, the finite reading is

    L_(a,tau)(fbar)=sum_c a_c sum_(omega in Omega)
         fbar_c(omega) product_q mu_q(omega_q)
                         product_(q in T)tau_q(omega_q). (P9)

Equivalently, multiply each token into its mu_q: the unqueried row is mu_q, the root row is mu_q/u_q(1) on that root, the square row is(mu_q(beta)/u_q(2))delta_beta, and the deep row is kappa_q(beta)delta_beta. This is the same normalization in coefficient-vector form.

Root and square tokens are their literal query readings. Every depth-e>=2 query in beta gives a coefficient no larger than its deep token. Conversely, an intact resolving-height descendant of A_(q,beta) attains the deep token exactly. Since the averaged kernel is prefix-constant, this SAME descendant realizes the token simultaneously for every central cell. Independent choices at the queried coordinates give one legal global tuple. Therefore

    N_T(a,etabar)=max_(finite token tuples tau)L_(a,tau)(fbar). (P10)

The square token is dominated by the corresponding deep token for this all-height supremum, but keeping it explicitly records its distinct fixed-depth meaning. The supremum reduction does not claim to reconstruct every prescribed deeper query's exact reading.

One sufficient finite pure-source parameter set is the actual Haar masses

    h_(q,alpha)=h_q(S_q intersect[alpha]_(q²)).

In the root-balanced case their root sums give t_(q,r); then(P1) gives d_(q,r), mu_q(alpha)=d_(q,r)h_(q,alpha), and(P7) gives kappa_q. In the general atomwise case retain d_q(alpha), or equivalently both h_(q,alpha) and mu_q(alpha); then mu_q(alpha)=d_q(alpha)h_(q,alpha) and the deep token is exactly 1/[D_q h_(q,alpha)] on that atom. These values refer to the SAME actual surviving support, including overlapping higher-pure holes. They cannot be selected independently by cell or query. A boundary consisting only of an unqualified q² probability table is not asserted sufficient for all other tasks.

## 5. Exact finite source optimization, with its conditions exposed

Suppose the gate uses finitely many nonnegative coefficient groups and the all-height screens(P4), for example the declared complete512 interface with its unchanged residual additions and tails. Its mass term is linear in the cell masses. By(P5)--(P6), averaging preserves reward and cannot increase any fee; hence

    G(eta)<=G(etabar).                                (P11)

Prefix kernels themselves are allowed measurable kernels. Thus the suprema over the two source classes are equal. For a fixed family and fixed finite parameters, the prefix optimization is an explicit finite linear program:

- variables f_(c,omega), with0<=f_(c,omega)<=U_c(omega);
- any declared finite linear priority constraints, on these SAME variables;
- exact mass coefficients product_q mu_q(omega_q);
- one epigraph variable per charged bundle;
- an inequality for EVERY literal central selector and EVERY corresponding global finite token tuple in(P9);
- the same nonnegative complete fees and same mass coefficient as the original gate.

Taking maxima occurs after summing all cells. There is no per-cell phase optimization or independently attainable source table. The actual Haar capacities of finite pure inventories are rational. The whole finite LP has rational data if, additionally, the atom densities, U_c bounds, central selectors, fees, reward coefficients and priority data are rational; this includes the declared rational root-balanced application. Rationality is not needed for the exact finite reduction or attainment: with any fixed real coefficients the continuous finite-box objective attains its maximum. The general measurable class has the same optimum because its averaged representative is feasible. This attainment statement assumes exactly the linear/dominance class stated above; an additional nonlinear product or policy constraint requires a separate preservation argument.

The parameter count does not depend on the heights of the higher-pure originals, but their rational denominators and the cost of computing their union capacities can grow. The full joint table can be enormous: for Q={7,11,13,17,19}, the simple maximum number of live-root q²-prefix tuples is product_q q(q-1)=67,044,257,280. Finite is not synonymous with computationally small. No such LP is solved or expanded here.

This gives a conditional finite interface for ONE actual family at a time. It does not characterize all achievable capacity vectors across arbitrary pure families, prove a uniform positive optimum, improve a continuation threshold, or remove the remaining unrestricted assumptions of Erdős#7. An actual root/edge factorization may provide a compact representation for contraction, but its exact joint relationships must remain available.

## 6. Four finite diagnostics locating the necessary information

**Exact phase readings are not retained by prefix masses.** Take q=7. Both families have pure originals0mod7 and1mod49; family A adds2mod343, family B adds51mod343. Construct(P1) separately from each actual family. Their entire q² mass tables agree, including mass1/48 on prefix2mod49. Their root density factors also agree. Yet the named query2mod343 has readings0 and1/288. The finite menu above preserves the all-height supremum interface, not these two named readings. Both families keep one fixed residue per numerical original.

**Descendant closure matters.** In family A, retain only the surviving child51mod343 inside prefix2mod49. Its old reading at the single charged query100mod343 is zero. Averaging within the ACTUAL surviving prefix gives density1/6 there and changes that query reading to1/1728>0. Thus an isolated query menu need not be improved by averaging. The all-height supremum contains the other descendants and satisfies(P6).

**Caps alone do not justify this averaging theorem.** At q=3 exclude root2. On height3 atoms in root0, assign masses1/100 at residues0 and9,1/10 at18, and19/300 at each of the other six atoms. On each of the nine height3 atoms in root1 assign1/18. Extend by Haar inside each atom. This is a normalized root-balanced law satisfying every reference cap in(P2), but its density varies INSIDE the surviving conditioning atom0mod9. Retain the two atoms0 and9. Its full normalized query supremum is9/100. Averaging this retention with respect to rho inside prefix0mod9 produces supremum3/20. The proof requires atomwise density constancy(P1a), not merely reference caps or root balance.

**Unary masses and edge probabilities do not specify shared-endpoint overlap.** Use independent uniform nonzero roots at7,11,13. In family A use1mod77 and1mod91. In family B use1mod77 and79mod91;79 is2mod7 and1mod13. Both edge probabilities are respectively1/60 and1/72 and all unary masses agree. The two bad events intersect in A and are disjoint in B. Survivor masses are233/240 and349/360, differing by1/720. Thus the exact prefix compatibility tensor must preserve the actual shared endpoint identities, not just each edge's marginal probability. This elementary example diagnoses missing boundary data; it is not a new covering result.

## 7. Exact checks and relation to prior results

The standard-library [program](../../../frontier/cover-geometry/pure-support-prefix-averaging-checks/pure_support_prefix_averaging_checks.py) and its [JSON result](../../../frontier/cover-geometry/pure-support-prefix-averaging-checks/pure_support_prefix_averaging_checks.json) verify500 explicit predicates with Python -I -S -B -O. Its positive test uses two actual root-balanced laws with higher-pure holes,1316 joint terminal atoms, two central kernels and four nonnegative central coefficient vectors. For each vector it enumerates6240 literal prefix query pairs through the resolving depth, verifies all four support suprema, and independently evaluates the finite whole/root/square/deep menus. In this finite test rho, the original kernels f_c, and the averaged kernels fbar_c are all constant with respect to Haar below the resolving depth3. For every intact descendant, both its mass and its geometric normalizer scale by the same power; hence deeper queries have the same normalized coefficients as their height3 parent. The general measurable statement is proved in section3, not inferred from this test.

The program also verifies each of the four diagnostics above. It imports no optimizer or producer and accepts --output; all examples are explicit in the source. These checks validate examples and formulas, not arbitrary-height formalization.

Report682 already proves a fixed-source central/7/11 category reduction by the same surviving-cylinder averaging idea. The present interface makes its transfer conditions explicit for ALL retained outside coordinates and arbitrary finite higher-pure inventories, supplies the actual density/capacity factors and finite joint token menus, and separates preserved supremum tasks from named-query tasks. The actual-union source construction remains existing background. The resulting bridge is conditional and reusable; it is not a claim that the full arbitrary-phase gate is positive.


An independent q=7 counterexample checks the same missing hypothesis within the outside-prime range. Exclude root6; use Haar density7/6 on roots1 through5. Inside root0 use density7/5 on0mod343,1/10 on the other six descendants of0mod49, and331/252 on its other42 depth-three cylinders. Each surviving root has mass1/6, and the density bound7/5 implies all standard deeper caps. Retain the six low-density descendants. The prefix mass is2/343, the retained mass is3/1715, and its prefix-average density is3/10. The exact normalized all-height supremum increases from1/14 to3/10. Both the original and averaged densities are constant below depth3, so greater heights give no different normalized ratio.

The [independent counterexample program](../../../frontier/cover-geometry/prefix-averaging-capped-reference-counterexample/prefix_averaging_capped_reference_counterexample.py) and [result](../../../frontier/cover-geometry/prefix-averaging-capped-reference-counterexample/prefix_averaging_capped_reference_counterexample.json) pass805 explicit checks. This is a second direct falsification of the caps-only extension, not a proof of the positive general theorem. The general contraction and finite-menu arguments were independently derived and cross-reviewed, including the prefix-measurability condition on priority coefficients and the separate rational-data condition. Both retained programs replay their canonical results byte for byte:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure-support-prefix-averaging-checks/pure_support_prefix_averaging_checks.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix-averaging-capped-reference-counterexample/prefix_averaging_capped_reference_counterexample.py
```
