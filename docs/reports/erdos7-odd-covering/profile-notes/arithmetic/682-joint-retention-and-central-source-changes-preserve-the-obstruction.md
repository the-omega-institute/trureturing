# Joint retention and central source changes preserve the threshold obstruction

Keep [Report681](681-higher-pure-capacity-obstruction.md)'s 109 actual original classes, its outside conditional law, and the complete full-event fee interface of [Report680](680-actual-leaf-capacities-separate-generic-and-common-source-gates.md). The higher pure originals are the eight fixed classes at moduli27,81,243,729,125,625,3125,15625 in681. Their phases and all101 earlier phases remain unchanged.

For every measurable retention field in[0,1] depending on the central3,5 coordinates and the outside7,11 coordinates, the same complete comparison gate satisfies

    G(f) <= U711
         = 1507661452610803341661
           /8686831052451071520000000000000
         = 1.735571284289456... * 10^(-10).

The field may inspect arbitrarily deep digits; it need not be a finite-prefix function. Moreover, replace the central product law by ANY finite joint central measure nu supported on the same pure survivors and satisfying

    nu <= (8/3) Haar|S,

where Haar is ambient product Haar, restricted without normalization. Keep the same conditional outside law. Then every such central–7–11 field satisfies

    G_nu(f) <= R U711
             = 1507661452610803341661
               /8576320051036237500000000000000
             = 1.757935155916481... * 10^(-10)
             < 193/100000,

with R=153832/151875. Thus neither changing central weights and densities under this joint cap, nor revealing all central/7/11 digits to the retention field, reaches the inherited threshold.

This is a bound on the specified source and all-height query comparison. It is not a covering example, a nonexistence theorem for positive gates, or an obstruction to all source constructions. The explicit integer in681 still avoids all109 originals. The upper bound is positive; no exact optimum of zero is claimed. The arguments below are ordinary mathematics and exact rational verification, not new Lean verification.

## 1. The actual source and finite joint categories

Use680's root-major central coordinates

    x3(l)=floor(l/3)+3(l mod3),
    x5(m)=floor(m/5)+5(m mod5).

The occupied ternary leaves are l in{0,1,2,4,5}; the occupied quinary leaves are m in{0,...,19} except5. Delete the central15 rectangle l<3,m<5. This leaves80 central cells. Weights are2/9 on strong ternary leaves and1/9 on weak leaf4; quinary weights are4/75 on strong leaves and1/25 on weak leaf10. The weak physical residues are4mod9 and2mod25.

At each central cell c, start with independent outside Haar laws conditioned off root0 at q in Q={7,11,13,17,19}. Delete the actual active linear stars and square stars. The actual qs originals all require root1 at both endpoints; their joint avoidance is exactly the restriction that at most one outside coordinate has root1. All other pair originals in the fixed fixture are contained in these forbidden pairs. These are predicates of the same actual originals, not independently selected root bounds.

For a remaining coordinate q let A_q(c) be its surviving root1 mass and B_q(c) its surviving other-root mass. For U subset Q define

    B_U(c)=product_(q in U) B_q(c),
    F_U(c)=B_U(c)+sum_(q in U) A_q(c) product_(s in U\{q}) B_s(c).

Given7/11 categories, the unqueried13/17/19 contribution is B_U if one retained category has root1, and F_U otherwise. A category pair with both coordinates at root1 is absent. This also determines every joint query after the queried coordinates have been fixed.

At7 retain seven categories:

- the single second-level child1mod49;
- the other six second-level children within root1mod7;
- each whole root2,3,4,5,6mod7.

At11 retain ten categories: child1mod121, the other ten children within root1mod11, each whole root2,...,8mod11, and the union of free roots9,10mod11. These two free roots have identical source predicates at every central cell and in every pair constraint.

Out of80*7*10=5600 potential addresses,3484 have positive actual source. The unretained source mass remains

    305684996597/646498195200.

All counts are rebuilt from actual q-squared residues in the retained verifier. In particular, a deleted star or special child removes its exact atoms. No positive mass is assigned to a dead cell or category.

## 2. Literal query normalization and complete fees

For each queried outside coordinate the inherited reference bounds are

    u_q(1)=1/(q-1),
    u_q(e)=1/[(q-2) q^(e-1)] for e>=2.

For a category-constant field, an undeleted non-root1 first-root query has normalized coefficient1. An intact deeper query has coefficient(q-2)/(q-1). At root1 the special-child and other-child categories must remain separate.

Consequently the7 menu contains first roots1,...,6 and child1mod49. The verifier also retains the valid but redundant child8mod49: its coefficient5/6 on the nonzero-child category is dominated by the first-root1 coefficient6/7. The11 menu contains first roots1,...,8, representative free root9, and child1mod121. The other-child deep coefficient9/10 is dominated by first-root1's10/11. Deeper queries at other roots are dominated by their first-root queries.

The11 free category has unqueried mass2/10, but one representative root9 query has coefficient1. A single query never receives the mass of two first roots. For q=13,17,19 the field is independent of q; first root9 is intact and avoids the pair root1, so it dominates every other normalized query pointwise in the retained coordinates.

Every outside query tuple is chosen ONCE for its entire central selector sum. Maxima are taken after the complete sum, never separately at each central cell.

There are16 central types: whole, root, leaf or all-height deep on each of3 and5. Their literal selectors and32 outside supports give512 fee groups. Shallow selectors use the weights in section1; deep selector coefficients are gamma3_l on3 and(4/5)gamma5_m on5, where

    gamma3_l=81/82 on weak leaf4, otherwise1,
    gamma5_m=1875/1876 on weak leaf10, otherwise1.

The finite menus have559 central selectors. The coefficient vector is640's pinned512 array plus the four full9q² charges

    C_(mode8,{q}) += g/[q(q-2)], q=11,13,17,19,
    g=200163067/201247200.

These are mode8=(leaf3,whole5), not the guarded mode9=(leaf3,root5) portions. All four entire arbitrary-phase originals are charged, as required by680's inventory repair.

## 3. An exact rational dual bounds all category fields

Let i range over the3484 actual category addresses. Write p_i for g times its source mass, and a_(j,d,i) for its nonnegative coefficient in literal query d of fee group j. Then

    G(theta)=sum_i p_i theta_i
              -sum_j C_j max_d sum_i a_(j,d,i) theta_i,
    0<=theta_i<=1.

The retained witness gives2568 nonzero rational multipliers lambda_(j,d), all with denominator10^12. Each d is a legal original query tuple and complete central selector. Exact arithmetic verifies

    lambda_(j,d)>=0,
    sum_d lambda_(j,d)<=C_j for every one of512 groups.

Therefore, for every category field,

    G(theta)
      <=sum_i [p_i-sum_(j,d)lambda_(j,d)a_(j,d,i)] theta_i
      <=sum_i max(0,p_i-sum_(j,d)lambda_(j,d)a_(j,d,i))
      =U711.

This uses only a feasible dual mixture. Neither numerical optimizer correctness nor an optimum/minimality assertion is needed. Uniform source thinning by680's factor429470970629/743970230784 scales the entire gate and does not remove the obstruction.

## 4. Every bounded measurable central–7–11 field reduces to categories

Write the source as rho0(dx3,dx5) zeta_c(doutside), including the central15 mask in zeta_c. The base central density is constant on each actual surviving coarse leaf, and zeta_c depends on central digits only through c. Each central survivor is a finite union of intact height6 prefixes.

First conditionally average f over the surviving central cell while holding(x7,x11) fixed, giving f1(c,x7,x11). Mass and every central whole/root/leaf reading are preserved. For a deep3 screen, fix its coarse ternary leaf, the entire other central selector and ONE global outside query tuple. Integrate all other variables first. Partition the chosen ternary survivor into its intact height6 prefixes. The Haar-weighted mean of the integral averages on these prefixes is the whole survivor average. One prefix has average at least that mean; its normalized reading is at least the reading for f1. The argument for5 is identical; for two deep axes use intact prefix rectangles.

The partition resolves the fixed deletions, not f. Integrals on its atoms exist for every bounded measurable f. Hence this comparison requires no finite-prefix assumption, differentiation theorem or limiting interchange. A prefix is chosen for the entire fixed query sum, not separately for its cells. Thus each fine screen dominates its counterpart after central averaging.

Next average f1 jointly inside each7-category times11-category rectangle, using its normalized Haar law. Source predicates and density are constant on each such rectangle, so mass is preserved. For unqueried11, roots1,...,8, or child1mod121, all reduced-menu readings are preserved. When11 uses representative free root9, the averaged reading equals

    (fine reading at global11-root9
      +fine reading at global11-root10)/2,

with exactly the SAME7 query, central selector and other outside roots in both terms. Equal free-root capacities and source symmetry give these fixed global weights1/2. The fine supremum contains both queries and dominates their average. This remains valid for a simultaneous7 query, including its special child.

The reduced menus in section2 exhaust the category-field suprema by domination. With all fees nonnegative, the resulting category field theta satisfies

    G(f)<=G(f1)<=G(theta)<=U711.

Conversely category fields are admissible measurable fields, so their optimization suprema agree. This concerns the same aggregated all-height screens. It supplies no equality for a charging inventory that keeps each original depth separately.

## 5. Central joint density changes are absorbed by one scalar domination

Let S=S3 times S5 be the occupied pure-survivor support before the central15 mask. The base density on an occupied cell is

    d rho0/dHaar=(8/3) gamma3_l gamma5_m.

Indeed, the weak capacities41/729 and469/15625 carry weights1/9 and1/25, so their densities are81/41 and625/469. Strong densities are2 and4/3. In particular

    rho0 >= (8/3)(81/82)(1875/1876) Haar|S.

For any positive joint central measure nu<= (8/3)Haar|S,

    nu<=R rho0, R=(82/81)(1876/1875)=153832/151875.

Let h=dnu/drho0 with0<=h<=R. Keep the SAME outside kernel zeta_c. For a measurable retained field f depending only on3,5,7,11, set f0=hf/R. Then0<=f0<=1 and the retained measures obey

    f(nu zeta)=R f0(rho0 zeta).

Source mass and every query integral scale by R. Since the query normalizers, menus and coefficients are unchanged, positive homogeneity gives

    G_nu(f)=R G_rho0(f0)<=R U711.

The Radon–Nikodym derivative need not be a finite-prefix function; section4 covers the required measurable f0. The hypothesis is a JOINT density bound. Separate marginal bounds permit singular or concentrated couplings and do not imply it. Nor does this source domination establish a product factorization required by a later continuation theorem.

## 6. The same frozen dual does not bound unrestricted outside fields

There is an exact witness against lifting these multipliers unchanged to all five outside coordinates. Retain only central cell(4,10) and outside first root2 at each q in Q. Every one of those roots is intact in the fixed actual source. Any frozen dual query containing13,17 or19-root9 vanishes on this field.

The source term minus the debit of these SAME frozen multipliers is

    737374609602494947/48120620486400000000000000
      =1.532346428930387... * 10^(-8) > U711.

This is not a positive full gate: the true unrestricted query supremum also includes root2. It proves that the supplied partial-coordinate dual cannot simply be reused as a pointwise bound on all outside retention fields. A successful extension needs a new justified query mixture or additional joint information.

## 7. Exact evidence and remaining interface

The portable [dual witness](../../frontier/cover-geometry/clustered_q7_q11_retention_obstruction.json) contains only the fixed source pins, literal query addresses, rational multipliers and expected bounds. Its SHA256 is `1511cbb74aedd06b8e6750ebf5dfde886ee653bb545df029cd93d7535baa98cf`.

The standard-library [verifier](../../frontier/cover-geometry/clustered_q7_q11_retention_obstruction_verify.py) reconstructs q-squared atoms from the actual originals, the joint categories, source coefficients, normalized query coefficients, every fee budget and every residual. Its [result](../../frontier/cover-geometry/clustered_q7_q11_retention_obstruction_verification.json) records9498 explicit checks, including the actual central capacities, R U711 and the pointwise lifting failure. Checks remain active with Python assertions disabled. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered_q7_q11_retention_obstruction_verify.py
```

The fixed sources are `clustered_global_phase_fixture.json`, `clustered_higher_pure_capacity_obstruction.json` and `remaining33_global_root_exclusion_certificate.json`; all are hash-bound in the witness. No optimizer, discovery program or transient directory is needed for replay. The averaging and measure-domination arguments are the ordinary proofs above, not assertions established by finite enumeration.

The separately authored [independent checker](../../frontier/cover-geometry/clustered_q7_q11_retention_independent.py) reads the actual original phases and the portable numerical witness without reading or importing the producer implementation. It reconstructs each required response both by explicit local residue enumeration with a root1-count convolution and by categorical formulas. Its [result](../../frontier/cover-geometry/clustered_q7_q11_retention_independent.json) retains all3484 residuals and passes1,651,856 checks, reproducing U711 and R U711. These are independent implementations within the same model family, not independent model families or Lean proofs.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered_q7_q11_retention_independent.py
```

This excludes a specific proposed repair of681 across an entire measurable field and central-source class. Remaining directions include changing the outside source or its full joint retention, preserving actual depth-specific charges, or improving the continuation threshold. None removes the separate unrestricted requirements: arbitrary globally fixed original phases, arbitrary higher pure inventories, and unrestricted early network geometry. Erdős #7 remains unresolved.
