# Exact central-and-outside query separator on one retained source

The 33-label query block joining the complete central eight-label block to the outside prime-pair triangles now has an exact computable separator. On full retention its outside atoms give no further saving beyond the central block; the two supplied nonconstant retained fields also remain below the continuation target. These are three actual-field evaluations, not an obstruction for every retained field.

[Report704](../700-749/704-a-full-joined-dual-excludes-the-retention-target.md) now gives a separate rational obstruction for every retention on this fixed source, and for its stated common-source extension. Its proof uses a new full dual; the field evaluations here retain their narrower meaning.

This is a current-source application of the independent-label machinery already present in Reports27/28, problem-details66 and [Report392](../350-399/392-root-optimal-laws-do-not-tensorize-the-full-layout-bound.md) RT11–RT12. It is ordinary finite mathematics, not a new generic theorem or Lean verification. The executable returns the exact selected query charge for one supplied nonnegative retained measure; it does not optimize that measure.

## Selected labels, ownership and conditional decomposition

Put P={3,5,7,11,13,17,19} and D0={3,5,9,15,25,45,75,225}. The central block owns all eight central unaries and all28 central unordered pairs. Add the five outside-prime unaries and, for each of the20 prime pairs other than{3,5}, the composite unary pq and the three pairs(p,q),(p,pq),(q,pq). These are33 distinct numerical labels,33 unaries of weight3, and88 unordered pairs of weight2: total atomic weight275. No numerical label is selected independently in two bags, and no atomic occurrence is paid twice. Unselected composite/composite or higher-power/outside pairs remain in the old residual.

For ONE common finite nonnegative measure ν, retain its joint9×25 central marginal and all seven first-root single marginals and21 first-root pair marginals. These projections need not factor. Let C(a,b) be the true maximum of the full eight-label central charge, conditional on b3=a,b5=b. For other prime pairs use

    E_pq(a,b)=2m_pq(a,b)
       +max_(u,v) [3+2[u=a]+2[v=b]]m_pq(u,v).

The joined charge is exactly

    Kjoin(ν)=max_(a_p:p∈P)
       [C(a3,a5)+3sum_(q outside)m_q(a_q)
        +sum_({p,q}≠{3,5})E_pq(a_p,a_q)].

Every outer prime variable is shared by all incident terms. Each composite pq outside the central block occurs only in its own edge and can therefore be eliminated conditionally. The six other central labels remain independent; none is forced to share a common residue. Backtracking C and all edge choices returns one legal33-label row attaining the displayed maximum. Its central part is n8²+2n8; its external part is the separately listed selected unaries and pairs. Taking n33²+2n33 would incorrectly add unselected interactions.

## Existing exact central separator, with the unit removed

Report392's nine-label second-moment separator includes the divisor-one indicator. With b3,b5 fixed, enumerate only b9,b25,b15. For each baseline, the remaining45- and75-cylinder partitions intersect in at most one mod225 source point. RT11–RT12 therefore eliminate those cylinders and the225-point query exactly. Subtract the total measure from the nine-label squared maximum to obtain C. This subtraction is performed for EVERY conditional value before insertion into Kjoin.

The current positive central support has79 points; the supplied input also retains its one zero-mass cell. The positive support has active domains of sizes5,19,7 for the three baseline labels. Thus there are665 baselines per condition,9,975 across all15 literal root conditions, followed by a direct scan of the final-cylinder pairs at each winning condition to reconstruct and check an attaining layout. The adapter preserves even zero-mass fixed roots. Nonnegative zero-column choices of a free label may be discarded: replacing an identically zero indicator by any supported indicator can only increase the nonnegative selected-square charge. Zero total measure is handled separately. Arbitrary-precision integer arithmetic is used when the checked int64 bound is exceeded.

## Safe outer domain reduction

For each value a of an outer prime p, form its COMPLETE response vector: its outside unary when present, every incident E_pq row against all neighbor values, and the appropriate full C row/column for p=3/5. If another value b is at least as large in every component, replacing only a by b never decreases any global energy. Remove such dominated values; for equal response vectors keep the smallest residue. Strict dominance has no cycle, and equality moves strictly toward smaller labels, so every deleted value reaches a retained maximal value. Repeating replacement proves that the reduced product domain has the SAME maximum. These inequalities are checked exactly and the removed-value/dominator list is retained. They are not an assumption that all free roots or all maxima coincide.

Every pointwise selected charge is at most275. For integer masses w_z with common denominator D, the energy numerator is at most275 sum_z w_z; division by D gives Kjoin(ν)≤275ν(1). The integer numerator bound guards int64 use, and the algorithm otherwise uses arbitrary integers. A literal reconstruction checks the returned central and pair-event row against the computed optimum. All15 conditional central layouts, the final33-label layout and the dominance certificate are retained.

## Current W splice and all heights

Write j=32(4e3+e5)+T with outside support T⊆{7,11,13,17,19}. The selected debit v_j is:

- (2e3+1)(2e5+1) if T is empty, e3,e5≤2 and e3+e5>0;
- 3^(e3+e5+|T|) times product_(q∈T)1/(q−1) if T is nonempty, e3,e5≤1 and e3+e5+|T|≤2;
- zero otherwise.

These are33 selected screens. The first line accounts for every ordered-square occurrence with lcm a nonunit divisor of225; the second for the remaining selected squarefree lcms. The token ledger independently sums all121 atomic occurrences by lcm and checks the original normalizers. Use the fixed c=1084133/201247200 and g=1−c. The old geometric-height coefficients satisfy W_j−v_j≥0, so the new gate is

    Gjoin(ν)=gν(1)−sum_j[C_j−c v_j]S_j(ν)−c Kjoin(ν)
            =Gold(ν)+c[sum_j v_j S_j(ν)−Kjoin(ν)].

The original-loss component C_j−cW_j, all fullmode8 additions and every unselected finite-height/tail query remain unchanged. At heights before selected shallow labels appear, use the actual selected subset or the old bound. The actual fixed109 resolving period already contains all selected labels. No terminal-depth computation is extrapolated to an unpaid infinite tail.

For outside queries, raw-root maxima only satisfy M_d(ν)≤the corresponding normalized complete screen; a deep query may control that screen. Therefore the actual saving is sum v_j S_j−Kjoin, not generally a raw-factor deficit. Each new retained field requires fresh complete screen readings. To handle deletion of remaining actual originals, distinguish the retained source ν from the survivor η≤ν: retain the actual unit mass η(1), dominate nonunit factors by ν, and use the same ν for the joined charge, residual and original-loss bounds. Neither a source-level saving nor independently attained branchwise gains may be imported.

## Averaging and pooled free roots

The689 actual-support averages preserve the joint9×25 central marginal and all selected first-root joint events. Thus they preserve every selected33-label row. Averaging within one outside first root also preserves those rows.

For the690 free-root pooling, use simultaneous permutations of roots9,…,q−1 at each q≥11. The actual fixed109 source and compatibility predicate are invariant. Apply the SAME permutation to the q-component of every incident numerical label; CRT gives legal transported residues. All repeated-endpoint equality patterns and all genuine intersections are preserved. The whole maximum is equivariant and convex, hence Kjoin(pooled ν)≤Kjoin(ν). Mass is preserved and unchanged screens retain their old nonincrease property, so the modified gate does not decrease under pooling. This is a whole-layout argument; individual named rows need not be preserved. Multiplying separately averaged incidence columns is forbidden because incompatible literals can then create a false intersection.

This proves that the existing finite category representation remains sufficient for the joined gate on the stated fixed source. It does not automatically transfer source invariance to changed original phases, arbitrary outside references or other interfaces.

## Computational provenance and evidence scope

The input consists of a common positive denominator, central points/weights, seven unary arrays,21 pair arrays, and the retained-field/source digests. The separator checks overlapping marginal identities; these identities alone are not a theorem that arbitrary invented marginals share a global realization. For actual sign/smooth fields the producer must derive every array from the same explicitly hashed field on the same pinned source. Exact old gate and selected full-screen fees must be supplied for a numerical joined-gate claim. If only certified upper bounds on individual S_j are supplied, a conservative lower gate must instead be recomputed directly as gν(1)−sum_j(C_j−cv_j)Supper_j−cKjoin, using nonnegative remaining coefficients. Adding an upper bound on the saving to an old gate would be invalid.

A positive feasible joined gate must come with this actual field, complete screens and actual layout/upper certification. A lower common-center subfamily maximum can help construct an obstruction dual but cannot certify a positive field against the true full Kjoin. Likewise an undelivered supremum at threshold is not an actual admissible witness. No such positivity or all-field obstruction follows merely from compiling this separator.

## Actual-field results and the all-one matching certificate

For the all-one source, the exact result is

    Kjoin = 13532790460667/1740572064000,
    K8 = 154916847841/34026220800,
    Boutside = 12151095362401/3771239472000,
    Kjoin = K8 + Boutside.

Here Boutside is the sum of all85 individual outside atomic maxima: five prime unaries plus20 independent composite unaries and60 pairs. The one returned prime tuple is(1,3,6,8,8,8,8); the central roots(1,3) attain K8. Its composite labels simultaneously attain every outside unary and pair maximum. Thus the displayed equality has a matching single-layout lower certificate and factorwise upper certificate. It is not just an enumeration observation. On this field every selected outside complete screen is attained by a shallow root query, as independently checked against its exact screen value. Thus expanding the full central block by these outside atoms creates no additional query saving. This statement does not extend to other retained fields.

For the two explicitly supplied698-derived retained fields, the full original-screen fees and all joined projections are derived from the same field. The exact gates are:

| Field | Exact Kjoin | Old gate (decimal) | Actual gate improvement (decimal) | Joined gate (decimal) |
| --- | --- | ---: | ---: | ---: |
| exact residual sign | 37386512449123/22627436832000 | -0.05672400421217159 | 0.0006616627010150343 | -0.056062341511156556 |
| explicit smooth20 dyadic table | 79418227357867605617/47453174407102464000 | -0.05539688116877915 | 0.0006297749781036806 | -0.05476710619067547 |

The exact sign joined gate is -27314684615333513400416820520967/487219832048895396817766400000000. The exact smooth20 joined gate is -142442637622714107367215361050937042243/2600879387835285656214620759654400000000. Both are below193/100000. Indeed, even dropping the entire selected query fee gives Gold+c sum(vj Sj)<0 for both fields, so their failure to reach the target does not depend on fine details of the joined maximization. Their role here is validation of the actual common-field interface, complete fees, arbitrary-integer branch and exact backtracking; no retained-field optimization is claimed.

Unlike full retention, these fields have a strictly positive extra raw sharing deficit beyond the complete central block. With Boutside defined from the SAME field's individual outside atomic maxima, the independent check gives

    K8+Boutside-Kjoin
      =339982414273/7542478944000                 (sign),
      =17045951102039521/451934994353356800       (smooth20).

Only38 of the85 outside atoms attain their own maximum in either returned layout, whereas all85 do so under full retention. The full-retention equality therefore cannot be asserted uniformly over retained fields. These deficits lower-bound the additional actual query credit divided by c, because the retained complete screens dominate the raw atomic envelope. They cannot be added to a gate value or dual upper attained on some other field: the positive deficit and all remaining fees must be evaluated together, and the displayed same-field gates remain negative.

The smooth20 field means the explicit integer NPZ array divided by2^20. Both arrays are retained as base64-encoded NPZ bytes in the registered `.b64` data format, with strict decoding and no pickle loading. It was proposed by binary64 sigmoid evaluation at tau=.0003 followed by rounding. No equality to the analytic real sigmoid and no approximation-error theorem is claimed.

The sign and smooth20 root products each reduce from4,849,845 to80,640 tuples by the exact componentwise certificates; the all-one product reduces to2. All15 conditional central layouts and the one final33-label witness are retained in every output. The sign and smooth runs each reported3,205 explicit checks, using respectively checked int64 and arbitrary integers. These finite checks supplement the displayed ordinary proof and are not Lean verification or an all-field exclusion.


## Reproducible source and separate verification scopes

The retained source verifier reconstructs all2,125,830 positive category states, verifies the exact sign of the698 rational debit and validates both stored fields as values in[0,1]. Full retention is constructed directly from the same source. For each of these three fields it computes the complete512 original screen maxima, the central mod225 marginal and all seven unary and21 pair root marginals. Its1,321,259 exact checks pass. A field is never assembled from separately optimized marginal tables.

The main separator records3,205 checks per field and all15 conditional central layouts. The independent maximum checker passes2,511 checks and enumerates all4,849,845 original prime tuples for EACH field, without using domain pruning. It separately reconstructs all121 selected factors, the33 selected screen deductions and all512 loss/remainder coefficients. Tiny sources include empty indicators, zero weights, zero total measure and arbitrary-integer scaling. Central optimality additionally uses the ordinary RT11–RT12 proof above; the literal layout checks alone certify attainment, not an independent upper bound.

A second independent program passes12,973 checks. It enumerates the actual central pure survivors modulo729 and15625, reconstructs the assigned central reference, and checks every central/unary/pair projection against the same stored field. Among the40 actual two-outside originals it verifies that the30 nonpure classes are subsets of the10 original pure pq classes with phase1. Their unions are therefore equal; no original constraint is silently removed by the category model. It does not rerun the512-screen contraction; that part is checked by the retained source verifier, its original-fee recombination and the existing screen representation proofs. All these are ordinary proofs and exact computations, not new Lean verification.

The exact all-one gate is

    -101545929867032596135512328043
    /1862325532039825870617600000000
    =-0.05452641233770135... .

Even replacing the complete new block fee by zero leaves negative gates in all three tests. The respective upper values are approximately-0.01264242053,-0.04716147453,-0.04575123628. These are useful rejection tests for THESE fields. They do not bound the supremum over other fields, and the zero field still supplies gate0.

From the repository root with NumPy installed, the following rebuilds the inputs, evaluates each field and checks both the maxima and the common-source bridge. The new directory contains only replay artifacts.

```sh
research_data=docs/reports/erdos7-odd-covering/frontier/cover-geometry
research_replay=$(mktemp -d /tmp/joined33.XXXXXX)
cp "$research_data/clustered109_698_sign_field.b64" "$research_data/clustered109_698_smooth20_field.b64" "$research_replay/"
python3 -I -B -O "$research_data/clustered109_retained_joined_verify.py" --base "$research_data" --witness "$research_data/clustered109_central_block_outside_witness.json" --sign-field "$research_replay/clustered109_698_sign_field.b64" --smooth-field "$research_replay/clustered109_698_smooth20_field.b64" --output-prefix "$research_replay/input"
for retained_field in allone sign smooth20; do
  python3 -I -B -O "$research_data/joined33_separator.py" --input "$research_replay/input_${retained_field}_joined_input.json" --output "$research_replay/${retained_field}_result.json"
done
python3 -I -B -O "$research_data/joined33_independent_audit.py" --controls --pair "$research_replay/input_allone_joined_input.json" "$research_replay/allone_result.json" --pair "$research_replay/input_sign_joined_input.json" "$research_replay/sign_result.json" --pair "$research_replay/input_smooth20_joined_input.json" "$research_replay/smooth20_result.json" --output "$research_replay/independent.json"
python3 -I -B -O "$research_data/joined33_source_bridge_audit.py" "$research_replay/input_allone_joined_input.json" "$research_replay/input_sign_joined_input.json" "$research_replay/input_smooth20_joined_input.json" --output "$research_replay/source_bridge.json"
```

The supplied integer fields, source projections, complete fees, maximum results and two independent checks are the retained experiment. Numerical proposal histories are not needed. Report704 now excludes the target for every retained measure under this interface and its declared common-source extension. Uniform noncoverage for arbitrary original phases, numerical labels, heights and prime support remains unresolved; these field computations and that fixed-family obstruction do not supply it.
