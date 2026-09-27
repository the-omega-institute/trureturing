# Fixed109 full-five-coordinate quotient and exact size

For the fixed actual109 original family of [Report681](681-higher-pure-capacity-obstruction.md) and [Report682](682-joint-retention-and-central-source-changes-preserve-the-obstruction.md), all bounded measurable retention fields on the two central coordinates and ALL five outside coordinates reduce, without decreasing the declared complete all-height gate, to a finite category field with2,125,830 positive variables. This is a lossless representation statement for the fixed source and query interface. It supplies neither a new dual nor a positive gate.

The central gamma factors remain81/82 and1875/1876. Every original numerical label and phase, every actual pure hole and the fullmode8 fees are unchanged. The source mass before retention is still305684996597/646498195200.

## Actual categories and their preservation

Use the same80 mod9/mod25 central cells as682. At q=7 use seven categories: special child1mod49; the other six children of first root1; and each whole root2 through6. At each q in{11,13,17,19}, use ten categories: special child1modq²; the other q-1 children of root1; each whole root2 through8; and the union of all free roots9 throughq-1.

Reading the actual101 base originals shows that each unary source predicate is constant on each category, and all pair exclusions are exactly the requirement that at most one outside coordinate has root1. Each category is either entirely allowed or entirely deleted at a central cell. The higher eight originals act only inside the two weak central leaves; their surviving-leaf laws are constant-density on those actual survivors.

First average centrally and inside actual outside q²-prefix atoms using the complete all-height theorem in [Report689](689-actual-pure-support-averaging-gives-a-finite-all-height-query-interface.md). Next average each q jointly within the displayed categories. Central support, every local original predicate and the pair predicate remain unchanged. Category mass is preserved.

For the resulting category field, the following queried menu is complete:

- q7: root1, roots2 through6, and the special-child deep query: seven choices.
- Each larger q: root1, roots2 through8, one representative free root9, and the special-child deep query: ten choices.

Root1 has coefficients1/q on its special child and(q-1)/q on its other-child category. A special-child deep query has coefficient(q-2)/(q-1). A deep query in any other root1 child is dominated by the root1 query, because(q-2)/(q-1)<(q-1)/q. A deeper query in any non-root1 category is dominated by its first-root query.

A free-root category has unqueried mass(q-9)/(q-1), but one representative root query has coefficient1, not q-9. Averaging over that free category turns its representative-root reading into the equal-weight average of the old readings at the corresponding actual free roots. For multiple queried free categories use the product of these fixed weights. Each member is ONE GLOBAL tuple for the complete central sum, so the old supremum dominates the new value. The special-child, root1 and individual non-root1 root readings are preserved. Thus every retained-menu screen is either preserved or a convex average of old global screens, and all removed screens are dominated. This proves the gate comparison for arbitrary bounded measurable fields, not just finite-cylinder fields.

This argument relies on this fixture's actual category symmetry. It does not authorize free-root pooling under changed phases or substitute a single query for several free roots.

## Exact count without expanding the table

Let a_q(c) be the number of positive root1 categories at cell c and b_q(c) the number of positive non-root1 categories. The number of positive joint category addresses at c is

    product_q b_q(c)
      +sum_q a_q(c) product_(s != q)b_s(c).

The actual at-most-one-root1 rule makes this exact. Summing over80 cells gives2,125,830, compared with5,600,000 unconstrained addresses. Cell(0,6) has zero actual source and is excluded; all other central cells have positive source. Multiplying category sizes instead of counting categories gives3,255,490,850,045 positive actual q²-prefix addresses across the80 cells. These need not be expanded.

Including the unqueried token there are8*11^4=117,128 outside query tuples across all32 supports. Of these29,648 request root1 at two or more coordinates and vanish identically. Exactly87,480 remain nonzero. The central interface has559 literal selectors,482 nonempty before the outside restriction. Consequently the raw product interface has65,474,552 rows; exactly25,359,668 literal rows are nonzero after intersecting their actual source support. This is not a count of linearly independent or distinct rows: additional equality/dominance reductions are not claimed.

The row count uses80-bit masks and a two-state support recurrence. For a selected outside token at coordinate q let A_q be the set of central cells with an allowed root1 category compatible with that token, and B_q the analogous non-root1 set. Start Z0 at all80 cells and Z1 empty; update

    Z0' = Z0 intersect B_q,
    Z1' = (Z1 intersect B_q) union(Z0 intersect A_q).

After all coordinates the nonzero source mask is Z0 union Z1. A central selector contributes one nonzero literal row exactly when its support intersects that mask. This handles dead source fibres and the shared root1 restriction explicitly.

## Verification and outstanding work

The [exact program](../../../frontier/cover-geometry/clustered-full5-interface-measure/clustered_full5_interface_measure.py) reconstructs the actual local predicates directly from the pinned originals. It checks the exact eight higher-pure moduli and phases, independently enumerates their actual surviving central capacities and gamma factors, verifies the source fixture pin, and checks all category partitions, full-or-empty status, pair-root identities and exact source mass before counting rows with the support recurrence. Its 873 explicit predicates pass under Python -I -S -B -O and reproduce the [JSON result](../../../frontier/cover-geometry/clustered-full5-interface-measure/clustered_full5_interface_measure.json) byte for byte. It uses only the standard library, does not expand the response matrix, and does not call an optimizer or import the old dual verifier.

The reduction is finite but the resulting2.1 million variables and25.4 million literal nonzero rows are not yet a small computation. A next certificate should exploit the same at-most-one-root1 tensor structure or produce an exact separation oracle. The frozen682 dual remains unproved on this larger field class; this note does not repeat its already known failed pointwise extension or claim a new optimization bound.


## Every uniformly mixed outside-root dual fails pointwise coverage

This next obstruction concerns a restricted dual class, not the source gate. In every literal central-selector row, suppose the outside query is replaced by the product uniform mixture of ALL live first roots at each queried coordinate. Allow arbitrary nonnegative mixtures of central selectors and arbitrary allocation within each original fee budget. No independence of the retained field is assumed.

At one outside coordinate,

    (1/(q-1)) sum_(r=1)^(q-1) [1_(x_q mod q=r)/u_q(1)]=1

on the actual base support, because u_q(1)=1/(q-1). Thus the product outside mixture equals1 pointwise, also after multiplying by the actual coupled source predicate. Every original query row reduces to its central-selector coefficient times the SAME outside source density. Summing the32 outside-support budgets of central mode m gives S_m. A necessary pointwise coverage condition is consequently

    sum_(m,d) lambda_(m,d) a_(m,d)(c) >= g w_l v_m

on every central cell c with positive actual outside source, where sum_d lambda_(m,d)<=S_m. Different central choices cannot bypass this condition: each of the79 live central cells has an actual outside realization and its source density cancels from that inequality.

For central axis levels whole/root/leaf/deep, the selector l1 norms on the full occupied axes are bounded by

    A=(1,2/3,2/9,1),
    B=(1,4/15,4/75,4/5).

These follow directly from the actual central weights and gamma3,gamma5<=1. Removing the central15 rectangle and the dead cell can only decrease each selector's l1 norm. Summing the necessary coverage condition over the79 live cells therefore requires

    g sum_live w_l v_m <= sum_(a,b) S_(4a+b) A_a B_b.

The actual positive-cell central weight is547/675. With the complete512 coefficients and all four fullmode8 additions, exact evaluation gives

    required = g*(547/675)
             =109489197649/135841860000,

    debit_upper =202063994637274331892893
                  /286717698659731046400000,

    required-debit_upper =29031860337191675392867
                           /286717698659731046400000 >0.

The required reward is0.806004847467489..., whereas the deliberately relaxed debit upper is0.7047489414913256.... This contradicts the necessary condition. It proves that NO choice of central-selector mixtures can turn uniform independent outside-root mixing into a pointwise dual cover, even with all fullmode8 budgets available. The argument uses a relaxed selector bound, so no optimization or claim that the bound is sharp is needed.

Nonuniform outside roots, correlations between queried roots, and coupling their mixture to central-selector choice are outside this uniform subfamily. The conclusion does not show a positive full gate, and it does not show that the full-five optimization is infeasible. It identifies why the simplest pointwise lifting repair cannot close that optimization.

## Independent separating bound

The independently authored [program](../../../frontier/cover-geometry/uniform-outside-central-cover-obstruction/uniform_outside_central_cover_obstruction.py) and its [result](../../../frontier/cover-geometry/uniform-outside-central-cover-obstruction/uniform_outside_central_cover_obstruction.json) reconstruct the same 79 positive-source central cells and enumerate all 559 literal central selectors. Let M_j be the maximum, over the literal selectors of mode j, of the sum of their coefficients on these 79 cells. The integrated debit of every uniform-outside dual is at most sum_j S_j M_j. Exact evaluation gives the sharper bound

    D_exact =4063265037031973858885786851
               /6128590808851751116800000000,

    required-D_exact =876408863047237046847333149
                       /6128590808851751116800000000 >0.

The independent verifier checks 5,728 predicates, including the relaxed analytic bound above. It imports no producer and uses no optimizer. Its raw root-tuple menu counts concern unpooled live roots; they are distinct from the compressed category menus in the earlier dimension calculation. These ordinary proofs and exact finite checks are not Lean verification.

## Reproduction

From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered-full5-interface-measure/clustered_full5_interface_measure.py --output /tmp/clustered_full5_interface_replay.json
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/uniform-outside-central-cover-obstruction/uniform_outside_central_cover_obstruction.py --output /tmp/uniform_outside_central_cover_replay.json
```

Both programs use repository-relative source fixtures and record their SHA-256 values. Byte-identical results are expected while each program and its inputs are unchanged.
