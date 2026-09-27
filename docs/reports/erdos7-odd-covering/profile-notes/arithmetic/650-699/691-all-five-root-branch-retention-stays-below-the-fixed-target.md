# All five root1 branches still do not reach the fixed continuation target

For the fixed actual109 original family in [Report681](681-higher-pure-capacity-obstruction.md) and [Report682](682-joint-retention-and-central-source-changes-preserve-the-obstruction.md), allow a retention field to see the central cell and WHICH of all five outside coordinates is the unique root1 coordinate, including whether it occupies the special q² child. Pool all nonroot1 identities within a regime. Every such field satisfies the exact complete fullmode8 gate bound

    G(f) <= U
         =676452579812687931521867
          /8935026225378244992000000000000000000
         =7.570795683748... *10^(-14)
         <193/100000.

This tests a different source repair from682's central–7–11 class: it can distinguish the13/17/19 root1 branches but pools nonroot1 identities that682 could distinguish at7/11. Neither class is claimed to contain the other. The result is for the fixed source and unchanged complete all-height fee interface. It is not an obstruction to arbitrary full-five fields, altered sources or changed original phases. The bound is positive; no exact optimum of zero is claimed. No new Lean verification is asserted.

Fix the actual109 source and complete fullmode8/512 fee interface of681/682. No phases or weights are changed. A regime is either no outside root1, or the unique root1 coordinate q together with whether its q² child is1 (special) or one of the other q-1 children. There are eleven possible regimes. The retention f(c,r) is constant on all allowed nonroot1 categories within that regime.

This is a restricted source-field class, not a lossless quotient of every full-five field. It permits dependence on root1 membership at13,17,19 that is absent from the central–7–11 class of682. [Report690](690-fixed-source-full-five-category-boundary-and-uniform-query-obstruction.md) treats the larger full category space; the present result tests a specific additional family inside that space.

For q>=11, the actual root9 is intact at every central cell. Any other nonroot1 root has first-root normalized coefficient0 or1 on a fixed central cell/regime. The retention is the same for all such nonroot roots, and the pair predicate sees only root1 membership. Consequently the global root9 query pointwise dominates every other nonroot1 query, for the complete central sum and every fixed choice on other coordinates. Deep nonroot queries have smaller normalization coefficient(q-2)/(q-1), so are also dominated by root9.

Root1 splits into special and other children. Its normalized coefficients are1/q and(q-1)/q respectively, while a surviving special deep query has(q-2)/(q-1). A deep other-child query is dominated by root1 because(q-2)/(q-1)<(q-1)/q. Therefore q>=11 has exactly the sufficient menu root1,root9,special-deep. At q7 no globally intact nonroot root is assumed, so retain root1, each root2,...,6 and special-deep: seven choices. Every query is fixed globally for the full selector sum. No per-cell root change is used.

Central queries retain all559 literal selectors and actual gamma3=81/82,gamma5=1875/1876. Every fee and all four fullmode8 additions remain in the512 groups.

Let B_q(c) be actual nonroot1 mass and A_(q,t)(c) actual root1 mass of child type t. The unqueried mass of regime none is product B_q. The mass of regime(j,t) is A_(j,t) product_(q!=j) B_q. For a query, replace each queried factor by its literal normalized coefficient above, setting it to zero if the regime and queried root disagree. Multiplication then gives the exact global-query response H(d,c,r). A full row is a_(mode,selector)(c) H(d,c,r), and source reward is g w_l v_m H(empty,c,r). These are exact rational coefficients on the same actual source.

The exact model has419 positive variables from880 potential cell/regime addresses. There are512 nonzero outside query tuples across all32 supports (2048 before the at-most-one-root1 restriction),135,584 nonzero complete literal rows,650,752 response-matrix nonzero entries, and all512 fee groups are nonempty. The source mass is305684996597/646498195200. Thus the restricted sparse LP is small enough to construct directly; no full5 table is needed.

The standalone verifier below rebuilds these dimensions and coefficients from the actual original phases and central pure capacities. These finite counts measure this restricted field class; they do not claim that419 states suffice for arbitrary full-five retention.


## One exact finite dual controls every regime field

Index the419 positive actual cell/regime addresses by i. Let p_i be g times their actual mass. A literal query d in fee group j has nonnegative response coefficients a_(j,d,i), computed by the product formula above. Its query tuple is fixed once for its COMPLETE central selector sum. Write

    G(theta)=sum_i p_i theta_i
       -sum_(j=0)^511 C_j max_d sum_i a_(j,d,i) theta_i,
    0<=theta_i<=1.

The retained witness gives700 nonnegative multipliers lambda_(j,d), each with denominator10^15. Each address names its central mode, left and right selector labels, outside support and all five literal outside choices. The choices use-1 for unqueried,0 for first root1,1 for special-child deep, and any value>=2 for that actual first root. They are one common set of query labels; no phases of the109 originals are changed.

Exact arithmetic verifies for every one of the512 groups

    sum_d lambda_(j,d)<=C_j.

The fees C_j are the pinned640 complete array PLUS each of the four entire fullmode8 charges g/[q(q-2)], q=11,13,17,19. They are not replaced by guarded mode9 residuals or charged separately at locally optimized sources.

The maximum dominates each budget-feasible query mixture, so for every field

    G(theta)
      <=sum_i [p_i-sum_(j,d)lambda_(j,d)a_(j,d,i)] theta_i
      <=sum_i max(0,p_i-sum_(j,d)lambda_(j,d)a_(j,d,i))
      =U.

The final equality is checked as a rational identity across all419 residuals. There are312 positive residuals from the chosen finite rational certificate. Their sum is the displayed U. This is a feasible dual certificate; its derivation requires neither a solver optimality claim nor an assertion that these multipliers minimize U.

## Exact evidence and remaining boundary

The witness is [rational witness](../../../frontier/cover-geometry/clustered11-regime-verify/clustered11_regime_dual.json). The standalone verifier [standalone verifier](../../../frontier/cover-geometry/clustered11-regime-verify/clustered11_regime_verify.py) reads only this witness and the three pinned canonical source JSON files; it imports no model module, discovery program or optimizer. It reconstructs all actual local predicates, the exact eight higher-pure phases, their central capacities41/729 and469/15625, actual gamma factors81/82 and1875/1876, allowed regimes, finite global menus, full512 fees, every dual budget and every residual. The result [exact result](../../../frontier/cover-geometry/clustered11-regime-verify/clustered11_regime_verify.json) passes5,623 explicit checks under Python -I -S -B -O, and two current runs reproduce it byte for byte.

All three input JSON files can live beside the program and witness. Its defaults use sibling paths; --base, --witness and --output are explicit portability overrides. The result retains hashes and exact residuals. No numerical optimizer is needed for replay.

The ordinary dominance proof supplies the complete all-height query reduction; the finite program verifies its actual fixture hypotheses and exact coefficient arithmetic. Finite enumeration is not presented as a general formal proof.

The fixed source's at-most-one-root1 predicate gives a natural small field class, but merely learning which coordinate is the exceptional root1 branch does not meet the unchanged continuation target. A different route must retain further distinctions, change the source or query interface, or use a different sufficient continuation criterion. This certificate does not determine which of those routes succeeds. In particular, it leaves arbitrary nonroot identities and their joint retention in the2,125,830-variable full category space open.


## Independent replay

The [independent verifier](../../../frontier/cover-geometry/clustered11-regime-verify/clustered11_regime_independent.py) reconstructs query coefficients by counting actual surviving q-squared residues, without importing the producer or primary verifier and without using optimization output. Its [result](../../../frontier/cover-geometry/clustered11-regime-verify/clustered11_regime_independent.json) passes 9,664 exact checks, reproducing every budget, all 419 residuals and the same upper bound.

From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered11-regime-verify/clustered11_regime_verify.py --output /tmp/clustered11_regime_primary_replay.json
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered11-regime-verify/clustered11_regime_independent.py --output /tmp/clustered11_regime_independent_replay.json
```
