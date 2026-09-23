# Randomized completion retains all original survivor support under a stronger common query bound

Let an original finite family have pairwise distinct odd numerical moduli greater than one, at most seven support primes, and arbitrary residues and heights. Choose at most seven odd core primes containing its support. Let K be a fixed finite core period supported only on these chosen primes and resolving the original family and all old-coordinate query depths. Write U for its full original survivor set and H_K for uniform probability on Z/K. Using [report462](462-the-final-stage-ledger-gives-a-seven-core-common-law.md)'s attributed source comparison, there is one probability mu such that

    (1/5) H_K|U <= mu <= 455625 H_K,
    supp(mu)=U,
    R_K(mu):=sum_(1<d|K) max_a mu(a mod d)
           <=70871/3375=21-4/3375.

The same mu serves every fixed query layout on this K. The lower inequality is not an assertion that U has mass 1/5. It says mu(a)>=1/(5K) at each original surviving residue a, while mu is zero off U. The retained terminal certificate also sharpens report462's query bound from 70874/3375 to 70871/3375. Report462's coarser bound and its consequences remain valid. No gap below 21 is spent in a mixture with normalized Haar on U.

The proof averages the existing source completion and charged-enlargement choices. It is an ordinary deduction from those source interfaces and their uniform certificate, not a new generic randomization method, a geometry rerun, or Lean certification. It does not prove that adding two arbitrary new primes preserves noncoverage. The source is Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1, with attribution, source identity and the arbitrary-height verification boundary in the [library entry](../../../../../Library/Arith/schroeder2026nine.md).

## Source premises and point-preserving choices

Work first on the reference seven coordinates 3,5,7,11,13,17,19. The selected completion moduli are their pure powers together with

    D_mixed={15,21,35,45,63,75,105,165}.

The unused auxiliary 23-coordinate in report462's comparison may be completed independently; it is not part of the seven-core live law.

Source Section 2 processes selected moduli in increasing order. At a modulus m, let Free_m be residues avoiding all previously selected proper-divisor classes. If the original m-class exists and is disjoint from those classes, retain it. Otherwise insert or move the selected m-class into Free_m. Moving a class already meeting a proper-divisor class loses no originally covered point, precisely as in the source completion proof.

Every selected modulus has at least two free residues. Thus, for one arbitrary original surviving point x, completion can always choose a free residue different from x mod m. The countable completion then preserves x. This statement alone must not be confused with positive measure at one infinite point; the averaging argument below supplies the measure bound.

At 7, the selected 21,35,63,105 classes have nonzero target digits after the selected pure-7 root is normalized to zero. At a coarse anchor cell let s be the number of active selected projections and T the set of their current target digits. Then |T|<=s<=4. If s>0, T is nonempty. If x survives completion, its current digit z is nonzero and is absent from T. There are five other nonzero digits, enough to enlarge T to size s while excluding z. Hence charged enlargement can also preserve a prescribed original survivor.

The stronger uniform result below uses random choices which do not depend on a query or on a subsequently selected target point.

## A single random completion process

At each inserted or moved selected class choose uniformly from Free_m; retain every already legal original selected class as above. Use independent uniform random variables to implement the successive finite choices. The choices themselves are history dependent. This defines a probability space for a countable sequence of legal completion choices.

Fix any original survivor x only for the analysis. Conditional on the entire previous completion history and on x having survived it, retaining an original class has survival probability one. An inserted or moved class has survival probability

    1-1/|Free_m|.

All estimates below are conditional lower bounds, and are multiplied by the tower rule. No independence of the resulting exclusion events is assumed.

For m=p^e, the selected lower pure powers are disjoint, so the number of free residues is exactly

    F_(p,e)=p^e-sum_(j=1,...,e-1) p^(e-j)
           =[(p-2)p^e+p]/(p-1).

At e=1 the survival factor is at least (p-1)/p. For e>=2,

    F_(p,e) >= [(p-2)/(p-1)] p^e,
    sum_(e>=2) 1/F_(p,e) <= 1/[p(p-2)].

For every finite set of tail depths, the deterministic product inequality product(1-a_i)>=1-sum a_i therefore gives a tail factor at least 1-1/[p(p-2)]. Passage to the decreasing limit gives the same bound for all depths. This is a bound on a product of conditional lower bounds, not a product of independent pure-tail events.

For selected mixed m, the source proper-divisor budget gives

    |Free_m| >= m-sum_(d in D, d|m, d<m) m/d.

The resulting integer lower bounds are

| m | 15 | 21 | 35 | 45 | 63 | 75 | 105 | 165 |
|---|---|---|---|---|---|---|---|---|
| F_m | 7 | 11 | 23 | 13 | 23 | 27 | 19 | 51 |

Their uniform survival factors are 1-1/F_m. Let

    kappa_pure = product_(p=3,5,7,11,13,17,19)
                    [(p-1)/p] [1-1/(p(p-2))],
    kappa_mixed = product_(m in D_mixed)(1-1/F_m).

The finite conditional-product argument, followed by continuity from above, proves

    Pr[x survives the complete selected family]
        >= kappa_pure kappa_mixed.

All nonselected original classes already miss x and are unchanged by completion. Thus this is survival of the entire completed family, not just selected labels.

## A single random charged enlargement

Conditional on the completed family, at every finite coarse anchor cell choose T-plus uniformly among all size-s supersets of T in the six nonzero digits. Use these choices to define one measurable charged rule on all histories before any kernel or query is evaluated.

Conditional on completion survival, the target digit z is outside T. If t=|T|, its probability of avoiding T-plus is

    (6-s)/(6-t).

If s=0 then t=0 and this probability is one. Otherwise 1<=t<=s<=4, whose minimum is 2/5, attained at (s,t)=(4,1). The target need not be supplied to the algorithm: a uniform superset gives this bound simultaneously, pointwise in every possible target.

Consequently, if E_omega is the completed-and-charged survivor set for all these random choices,

    Pr[x in E_omega] >= kappa
      :=(2/5) kappa_pure kappa_mixed
       =33886755094528/713214217048905

for every original survivor x. For a point outside the original survivor set this probability is zero, since every outcome contains the original forbidden union.

## Why the same source certificate applies to every outcome

Completion retains precisely the source disjointness and coverage conditions. The charged lemma says to enlarge T to any size-s superset; “adding the smallest unused digits” is explicitly an example, not an additional hypothesis. Its current loss bound uses only the mass s/7 of the added first-digit cylinders and the pure mass 1/6. Its live mass and subsequent comparison use only

    S_s=min(1,(3/2)(6-s)/7)

and the unchanged positive-depth cylinder caps. The identities of added digits do not enter these upper comparisons. At 11 the fixed physical 165 projection is retained for each completed family; it is not reselected within an auxiliary expectation. The later comparisons and common vertex ledger depend on the completed anchor data, those fixed projections, the caps, and the displayed size bounds.

The displayed finite projection domain Xi in source Section 6 is specific to the canonical anchor chart. That restriction concerns the later finite geometric comparison, not the admissibility of the charged process. On every anchor chart, define T from the four actual selected classes and s from their four actual active projections. If Z_rest is their remaining original raw 7-load, the full original load is

    Z_7=Z_rest+(6/7)s.

Replacing the selected target union by any size-s T-plus costs exactly s/7 in Haar mass. The enlarged current loss is therefore at most

    (1/4)[Z_rest+(6/7)s-1]_+=(1/4)[Z_7-1]_+,

which is exactly the ordinary source threshold-2 raw hinge. Thus even an early ordinary screen pays for the entire extra deletion. At subsequent primes, ordinary reverse-integration comparisons still apply to the same normalized capped kernels; dropping the refined first-hit information only replaces S_s<=1 by the larger ordinary bound. The source architecture describes the fibre enlargement globally, and its compatible-screening lemma explicitly bounds one common fixed-family ledger. Canonical Xi or fixed-label eta domains are used only in the anchor charts where the source establishes them; other charts use the applicable ordinary bounds for the same process. There is no independent choice of a different process at each interpolation vertex.

Accordingly every randomized outcome belongs to the same source-wide comparison and terminal certificate used in report462. Before any query layout is supplied, form its explicit source live measure mu_omega. For all outcomes, uniformly,

    1/33750 <= M_omega:=mu_omega(1) <= 3/8,
    mu_omega <= (27/2) H,
    integral (L-1) dmu_omega <= (70871/3375) M_omega

for every fixed complete query load L. The upper mass bound is the initial anchor mass at most (1/2)(3/4)=3/8; normalized kernels and deletions cannot increase it. The lower mass is the inherited absolute-gap consequence. The stronger query bound follows from the relative-ledger deduction below, with the same source comparison and verification scope as report462.

## The relative terminal ledger gives a stronger query bound

The retained original certificate records all 28,001 terminal pairs of rounded reserve and aggregate loss,

    R_minus=floor(1000 R_screen),
    L_plus=ceil(1000 L_screen).

Every reserve is positive. The [relative-ledger consumer](../../frontier/cover-geometry/relative_terminal_query_bound.py) gives the exact maximum

    rho=max_rows L_plus/R_minus
       =33746/33750=16873/16875.

There are four maximizing rows, all coarse screens, with reserve_lower=33750 and loss_upper=33746. The [result data](../../frontier/cover-geometry/relative_terminal_query_bound.json) retains their configuration identifiers and every phase count. Since L_screen<=L_plus/1000 and R_screen>=R_minus/1000, each terminal screen satisfies L_screen<=rho R_screen.

For one fixed completed family, let R be the source's finest common reserve, S the sum of its common stage-loss upper bounds at 7,11,13,17,19, and U23 its final-stage common upper bound. These quantities are in the same 135-cell units as report462. The compatible-screening proof supplies more than a positive difference: each earlier screen credits no more reserve than the common reserve and charges no smaller corresponding stage bound. It ignores holes by enlarging nonnegative weights, releases prescribed phases through weighted aggregation, and replaces first-hit improvements by ordinary bounds. The fixed caps and positive omitted-region bounds are shared. Thus, at each vertex or uniformly over an ignored budget,

    S+U23 <= L_screen <= rho R_screen <= rho R.

The source's explicit vertex weights interpolate the common reserve affinely and majorize every positive comparison component by the same convex combination of its vertex values. Multiplying the reserve by the positive constant rho preserves this argument. The inequality consequently holds at all allowed continuous anchor parameters:

    S+U23<=rho R.

With D7=R-S and S>=0, the absolute certificate gap still gives D7>0, and

    U23/D7 <= (rho R-S)/(R-S) <= rho.

Report462's fixed-law bridge holds for every complete query L simultaneously:

    E_(mu_omega/M_omega)(L-1)
        <=11+10 U23/D7
        <=11+10 rho
        =70871/3375.

The improvement is exactly 1/1125. Neither the density cap nor the positive mass lower bound changes. In particular this also improves the query estimate for each fixed source outcome before randomization.

The certificate stores total loss, not the individual stage23 loss and D7. Its aggregate maximum is not claimed to equal the actual maximum of U23/D7 or R_K. The criterion U23/D7<9/10 needed by this bridge for R_K<20 is not supplied by these aggregate data. No geometric producer or screening traversal is rerun here.

## Averaging gives lower density on all original survivors

On its actual live fibre G_p, the source explicit kernel has density

    min(C_p,1/H_p(G_p)) >= (p-1)/(p-2).

Indeed G_p avoids the completed pure set of mass 1/(p-1), and the cap is feasible at that pure mass. Anchor initialization is unnormalized Haar restricted to its survivor set. Hence

    mu_omega >= c_* H|E_omega,
    c_* = product_(p=7,11,13,17,19) (p-1)/(p-2)=1536/935.

The random construction is measurable: each completion choice is a finite function of earlier choices; the completed pure union is a countable union of cylinders; charged rules use finite coarse cells; the explicit kernel integrates Borel indicators. Define every realization on the same original coordinate space. If source Haar-preserving anchor normalizations are used, pull both its measure and the same physical query back to these original coordinates before averaging; no query residue is chosen afresh in another realization. Tonelli therefore applies to the averaged finite measure

    mu_bar=E_omega mu_omega.

Writing U_infinity for the inverse image of the original finite survivor set, pointwise preservation gives

    c_* kappa H|U_infinity <= mu_bar <= (27/2) H,
    1/33750 <= mu_bar(1) <= 3/8.

Average the unnormalized query inequality first. Its right side is exactly (70871/3375) mu_bar(1), so one normalization produces a single probability with the same query bound for every layout. Its density upper bound remains (27/2)/(1/33750)=455625, while its lower density on U_infinity is at least

    c_* kappa/(3/8)
      =138800148867186688/666855292940726175
      >1/5.

Project to the stated fixed finite core period K resolving the original family. Because U_infinity is precisely the inverse image of U, both density inequalities project with the same constants. The lower bound makes every original surviving finite residue positive. This avoids any inference from positivity at an individual infinite point.

## Actual odd primes and one common law

Use report462's finite random prefix-injection transport, with reference p_i<=actual q_i and heights resolving the input and queries. For each injection F the original target family pulls back to an original source family, with survivor set exactly F^{-1}U. Apply the randomized completion construction to that pulled-back family and retain the unnormalized averaged source measure nu_F. Its constants above are uniform in F.

For every target event B,

    E_F [F_*(H_source|F^{-1}U)](B)
      =E_F [F_*H_source](B intersect U)
      =H_target(B intersect U).

Therefore averaging the unnormalized F_*nu_F preserves the same lower density c_*kappa on the full original target survivor set, as well as the upper cap, mass interval and simultaneous query inequality. Normalize only once. The displayed lower constant greater than 1/5, upper 455625 and query constant 70871/3375 all remain valid.

For fewer than seven primes, pad with unused primes, perform this construction and project. The padded original survivor set is a product with the unused coordinates, so the full original lower density projects unchanged. No original phase is replaced in the final target task, and no query selects its own law. These independently constructed finite-period laws need not be compatible. The following compactness argument selects a compatible family with the same bounds.

## One compatible law over every finite core depth

For a fixed original finite family and a fixed nonempty set P of at most seven odd core primes containing its support, the finite-period result has an ordinary compactness consequence. Let

    X_P=product_(p in P) Z_p,

with its product p-adic topology and Haar probability H. Write U_infinity for the inverse image of the original finite survivor set. This set is clopen. There exists one Borel probability nu on X_P such that

    nu(U_infinity)=1,
    (1/5) H|U_infinity <= nu <= 455625 H,
    sum_(d>1, every prime divisor of d in P)
        max_(a mod d) nu(a mod d) <=70871/3375.

In particular supp(nu)=U_infinity, and its finite-period marginals satisfy the theorem above simultaneously. Here the countable sum means the supremum of its finite nonnegative partial sums. The empty core has only the trivial one-point version.

To prove this, choose K0 supported on P and divisible by every original modulus, and put K_n=K0 (product_(p in P) p)^n. This is a cofinal divisibility chain among finite P-supported periods. Choose one finite-period probability mu_n from the theorem for each K_n. For n>=N, its projection to Z/K_N lies in a fixed finite-dimensional probability simplex. Repeated subsequence extraction and the diagonal argument give a single sequence along which these projections converge for every N; write nu_N for the limits.

Projection is linear and continuous, so the nu_N are compatible. Because each K_N resolves the original family, projection and the finite coordinatewise limits preserve

    nu_N(U_N)=1,
    (1/5) H_KN|U_N <= nu_N <=455625 H_KN.

The support condition is retained separately: the two density inequalities by themselves would not imply zero mass off U_N. Moreover R_KN is a finite sum of maxima of finitely many linear cylinder probabilities, hence continuous. Since every d|K_N also divides K_n for n>=N,

    R_KN(projection of mu_n)<=R_Kn(mu_n)<=70871/3375.

It follows that R_KN(nu_N)<=70871/3375. The usual extension of consistent finite probability distributions gives one Borel probability nu on the inverse limit, identified with X_P. The cylinder inequalities extend to Borel sets: each difference nu-(1/5)H|U_infinity and 455625H-nu is nonnegative on the finite cylinder algebra, hence on its generated sigma-algebra by the monotone class argument. Also nu(U_infinity)=1, since U_infinity is already a finite-level event.

Every P-supported divisor divides some K_N. Thus monotone exhaustion of the nonnegative divisor sums gives the stated all-depth query bound. Every open neighbourhood of a point of U_infinity has positive Haar intersection with that clopen set, so the lower inequality gives full topological support there; the retained support condition excludes its complement.

The upper density still supplies an explicit query-tail estimate. If E_p=v_p(K_N) and J_P=product_(p in P) p/(p-1), then

    sum_(d supported on P, d does not divide K_N)
        max_a nu(a mod d)
      <=455625 sum_(d supported on P, d does not divide K_N) 1/d
      =455625 J_P [1-product_(p in P)(1-p^(-(E_p+1)))].

This tends to zero with N. It controls the discarded divisor tail for the chosen law; it does not compute that law or supply a convergence rate for the diagonal subsequence used to obtain it.

This is a direct application of finite-simplex compactness and consistent-distribution extension to the uniform constants already proved. It asserts existence of one compatible choice, not that arbitrary previously chosen finite laws are compatible, and not an effective algorithm for choosing the limiting law. It does not enlarge the fixed set P, turn positive profinite measure into an integer for an infinite forbidden family, or change the finite-family quantifier of the original covering question. For a finite enlarged period, the finite extension criterion below remains the relevant one.

## Boundary

This construction removes support loss from auxiliary completion and charged enlargement by averaging permitted source choices. For the resulting law, any positive-Haar original survivor event has positive probability, and conversely the law remains supported on original survivors. On a fixed finite enlarged period, take a new-coordinate product law with positive mass at every residue avoiding the actual new pure classes, as in report463. Its product with mu assigns positive mass to every possible original survivor. After deleting the remaining actual original classes, positive mass is therefore equivalent to existence of an original survivor in that finite enlarged period. This equivalence does not apply to an arbitrary new-coordinate law that has already omitted permissible points, or to a nonempty infinite set of zero Haar measure.

That equivalence does not prove the latter existence for arbitrary extra primes. The joint original phase constraints and the quantitative continuation problem remain. The [report465 scalar-interface countermodel](465-two-query-scalars-do-not-determine-a-surviving-extension.md) concerns arbitrary supplied laws and remains valid; the new construction selects a more informative law rather than extending that delta law.

An actual finite completion control uses original classes 0 mod3, 0 mod9 and 2 mod27, and selected moduli 3,9,27. The keep-if-legal/uniform-move rule has 20 outcomes of total probability one: five of weight 1/6 and fifteen of weight 1/90. Each outcome contains the original covered set. The 17 original survivors have preservation probabilities 37/45 or 5/6; target 1 has probability 37/45. The legal fixed completion (0 mod3,1 mod9,2 mod27) removes target 1. Thus this control retains original phases and checks the history-dependent random-choice rule rather than assuming independence.

[Report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) applies the retained ordinary seven-core mass bound to this same charged process. It improves the upper density cap to 6075000000000/7235955529<840 while preserving the query bound, full original support and compatible all-depth conclusion. All coarser constants above remain valid.

## Exact consumers and verification boundary

The [randomized-completion consumer](../../frontier/cover-geometry/randomized_completion_support.py) pins both the retained report462 seed and the relative-ledger summary, checks their common source certificate and mass gap, verifies the proper-divisor budgets and all finite charged-superset probabilities, and computes the rational constants above. Its [result data](../../frontier/cover-geometry/randomized_completion_support.json) also contains the adaptive finite completion control. Its checks remain enabled under optimized Python. The original terminal certificate is supplied from the source edition 1.0.1 archive; it is not copied into this report.

From the repository root, run:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/relative_terminal_query_bound.py \
  --certificate /path/to/nine-prime-support/certificate/integer_certificate.json

python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/randomized_completion_support.py \
  --seed docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven_core_last_stage_bridge.json \
  --relative-ledger docs/reports/erdos7-odd-covering/frontier/cover-geometry/relative_terminal_query_bound.json
```

Both consumers accept optional `--output PATH`; otherwise they write their computed JSON to stdout. The optimized isolated runs passed. These are exact arithmetic and finite-control checks, not proofs of the countable completion, source-uniformity, interpolation or measure transport. Those are ordinary mathematical deductions above from the attributed source construction. No new Lean verification, source geometry regeneration or general noncoverage range is claimed.
