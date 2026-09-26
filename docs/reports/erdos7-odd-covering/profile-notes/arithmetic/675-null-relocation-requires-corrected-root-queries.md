# Null relocation requires corrected root queries

Ordinary mathematics and a finite diagnostic; no new complete gate, new arithmetic phase class, or arithmetic covering counterexample is asserted. The inputs are [624's actual-source construction](624-arbitrary-central-pure-phases-admit-two-complete-boundary-gates.md), [643's activation and source interfaces](643-central-cell-root-choices-preserve-complete-continuation.md), [645's priority mixing theorem](645-weak-marker-priority-preserves-actual-corner-mixtures.md), and [673's fixed-null whole-field calculation](673-heterogeneous-fields-complete-the-live-leaf45-role-domain.md).

Let I={0,1,2,4,5}, J={0,...,19}\{5}. On this old reference support put R0={0,1,2}, R1={4,5}, C0={0,...,4}, C1={6,...,9}, C2={10,...,14}, C3={15,...,19}. For a,b in{0,1}, apply F3=(0 3)^a and F5=(0 5)^b to leaf labels and leave all higher tails unchanged. These are Haar-preserving permutations of depth-two cylinders, fixing the deleted first-pure roots. They are generally not automorphisms of the rooted prefix tree. Use them as coordinates for one actual family; do not claim that pulling back a first-level mixed congruence still gives one arithmetic cylinder.

## 1. Four exact activation geometries

| a,b | Actual nulls | Actual row sets pulled to I | Actual column sets pulled to J | Actual unmasked cells |
|---|---|---|---|---:|
|0,0|3,5|012 ; 45|01234 ; 6789 ; 10..14 ; 15..19|80|
|1,0|0,5|12 ; 045|01234 ; 6789 ; 10..14 ; 15..19|85|
|0,1|3,0|012 ; 45|1234 ; 06789 ; 10..14 ; 15..19|83|
|1,1|0,0|12 ; 045|1234 ; 06789 ; 10..14 ; 15..19|87|

The pulled actual15 mask removes A0×B0, where A0=R0\{0} if a=1 and R0 otherwise, and B0=C0\{0} if b=1 and C0 otherwise. Therefore the old80-cell mask, removing R0×C0, is a genuine additional thinning of every actual geometry. The extra discarded central product mass is exactly

    a w0 v(C0) + b v0 w(R0) - ab w0 v0.

This is a statement of source domination, not preservation of its full mass.

Only two extra point-membership features are required to express every pulled first-root activation:

    t(l)=1_(l=0), s(m)=1_(m=0),
    A_r(l)=R_r(l)+a*(-1,+1)_r*t(l),
    B_c(m)=C_c(m)+b*(-1,+1,0,0)_c*s(m).

For the square-star unary decrement, with ell the pulled actual square leaf,

    n_new(l,m)=R_r(l)+C_c(m)+1_(l=ell)
                  +a*(-1,+1)_r*t(l)+b*(-1,+1,0,0)_c*s(m).

This is exact, stays in{0,1,2,3}, and applies simultaneously to the whole actual layout. Depth-two activations remain singleton leaf indicators; higher activations remain one cylinder with the transported leaf and unchanged tail. Product central congruences use the products of these actual sets. Conditional outside root tables must absorb originals on these exact sets, as in643. Reusing an old row/column activation without the corrections can leave an actual constrained original alive.

Two literal point witnesses demonstrate this last issue. With the usual deleted first roots, x=4852 has (mod9,mod25,mod49)=(1,2,1), avoids the new ternary null0, old quinary null1mod25 and central15, but belongs to147:1. Under the ternary swap it pulls to old l=0, where old row1 was inactive even though actual row1 is active. Likewise x=3676 has residues(4,1,1), avoids old ternary null1mod9, new quinary null0 and central15, but belongs to245:1. It pulls to old m=0, where old column1 was inactive. These are failure-of-containment witnesses, not covering systems or survivor-nonexistence claims.

## 2. Exact full-height selector repair

The depth-zero whole selector, depth-two singleton selectors and all deeper singleton-cap selectors transport individually. For depths at least two, leafwise translation preserves cylinder height and Haar mass, so624's density caps2*3^-e and(4/3)*5^-f remain valid at every finite height. Only depth-one root selectors change: replace R_r by A_r, and C_c by B_c. The four statuses remain whole/root/leaf/deep, with the same deep normalized weights1 and4/5. Their sixteen tensor-product menus must be evaluated on the same response table.

For one specified geometry, the exact menus still contain(1+2+5+5)(1+4+19+19)=559 original selectors. For a single nonnegative upper envelope covering both old and moved geometries, the inclusion-maximal root supports in the union are

    ternary: {012,045} when a=1;
    quinary: {01234,06789,10..14,15..19} when b=1.

Smaller sets12,45,1234,6789 are dominated by those. Hence one may replace old row1/column1 by the indicated cross support, without increasing the number of root selectors. The resulting supports overlap; they are an envelope, not a root partition. They preserve the exact maximum over the union of old and new root menus for every nonnegative response. Each listed support is inclusion-maximal and cannot be removed under universal componentwise domination. This is the precise minimality claim; it is not a claim about globally minimal DP memory or optimal gates.

When both coordinates move, the repair must include the cross-row × cross-column selector, and all other required tensor products. Separate marginal maxima cannot recover their joint screen. Signed grids require separate treatment; the domination assertion here uses nonnegative matching-response grids, as in673.

## 3. Exact finite counterpairs to the free old-maximum direction

Take ternary weak marker2, so w0=w1=w4=2/9. Take quinary weak marker0 and fix m=10, of mass4/75. Compare nonnegative grids A supported on{(0,10),(4,10)} and B on{(1,10),(4,10)}, each with value1 there. All sixteen old menu maxima agree. Their old ternary-root/whole-quinary screen is8/675. After the ternary swap, A's actual-root screen is16/675, while B's remains8/675.

For the quinary swap, fix l=4 and weak quinary marker10, so v0=v1=v6=4/75. Compare supports{(4,0),(4,6)} and{(4,1),(4,6)}. Again all sixteen old menu maxima agree, but the new whole-ternary/root-quinary screen is16/675 versus8/675.

For the joint repair, put value1 on{(0,6),(4,0),(4,6)} with the same equal participating weights. The root/root maximum is8/675 using old menus,16/675 after either one-coordinate repair, and24/675 after both. This makes the missing joint selector explicit.

These counterpairs are legitimate finite same-source thinnings: take central corner weights as actual constant leaf densities with no higher-pure originals, take one fixed positive outside submeasure, and retain only the displayed central cells. Its support envelopes are a common positive factor h_T times the displayed grid for each of32 supports. Thus the equalities extend to all32 old response screens at the fixed specified weak corner. No claim is made that these arbitrary thinnings are673's matching polynomial, that all95 corner outputs coincide, or that an arithmetic covering system has been refuted.

## 4. The exact source bridge still available

Start from the target actual624 pure sources, then pull them back through F. Their nulls become3/5, capacities and admissible mixture weights are merely reindexed, and the density caps remain valid. Construct645's priority effective thinning on the conservative old mask and attach ONE actual outside submeasure table whose absorption conditions have been proved with the corrected activation sets. Push this submeasure forward through F. It is dominated by the target actual pure product, avoids the actual15 event, and satisfies the transported two priorities. The shallow query proof uses the repaired root selectors; the deep query proof uses the unchanged density caps. All fields, phases and source tables are fixed globally, not selected independently per query.

Thus null relocation has a rigorous actual-source thinning bridge. What is unpaid is the new complete gate after corrected activations and root screens, plus any changes to incidence absorption. Neither larger actual unmasked area nor unchanged deep caps proves that the old512 maxima remain upper bounds. The explicit counterpairs rule out that free transfer. No large layout scan was performed.

The [finite geometry program](../../frontier/cover-geometry/null_geometry_boundary_independent.py) passes15,345 exact checks, verifies all four activation formulas and finite selector counterpairs, and records the CRT witnesses. Its [result](../../frontier/cover-geometry/null_geometry_boundary_independent.json) is diagnostic data, not a new positive arithmetic certificate. The common-source and every-height conclusions above are ordinary mathematical arguments; finite checking does not certify their universal quantifiers by itself.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/null_geometry_boundary_independent.py
```
