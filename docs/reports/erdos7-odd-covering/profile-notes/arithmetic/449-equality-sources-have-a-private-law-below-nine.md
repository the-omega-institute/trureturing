[Index](../../marked_head_profile.md) · [Literal equality reduction](448-literal-product-trees-exclude-the-equality-cut.md) · [Generic cut bound](447-strict-child-cut-surplus-and-arithmetic-boundaries.md)

# Every literal 65/63 equality source has one private law below nine

The sharp network in [448](448-literal-product-trees-exclude-the-equality-cut.md) is not a moment obstruction. Every source attaining that network's lower bound65/63, under its literal product-blocking and standalone-tree premises, has one actual supported law with

    Gamma_1225(nu) <= 25/3 < 9.

This result allows incidence five at every full root. It uses actual private points forced by the equality cut, gives the common column zero mass, and chooses ONE probability before all original numerical labels and all phase tests. The same law construction applies to any larger actual source containing the specified private structure, whether or not that larger source has an equality cut or satisfies the tree premises.

This is an ordinary proof with exact construction controls, not a new Lean-certified declaration. It does not prove that every remaining source contains this structure, lift the law through arbitrary original outside-cofactor tests, or settle unrestricted Erdős #7. The bound is uniform over a newly classified source family; it is not an improvement of448's particular117-point law bound107/13.

## Exact description of the equality sources

Let F be a subset of Z/25 x Z/49, with literal coordinates(r,c,g+7h): r,c are the first and second five-digits, and g,h the first and second seven-digits. There are four occupied five-roots, one with four occupied children and three with five. Call the former the gap root a and put q_a=2, q_r=3 at the full roots.

Assume that F blocks every product of a complete ternary five-tree and a complete five-ary seven-tree, both of height two, and that its seven projection contains a standalone complete five-ary tree. Use447's actual-child network with root/child capacities1/3,1/9, private seven-prefix capacities(2/7)3^(-B), public prefix capacities3^(-B), and actual bridge capacities2.

The network has a cut of capacity65/63 if and only if F has the following exact representation. There are five pairwise distinct first-seven digits g0 and g_r, one private digit for each occupied five-root, such that every occupied child's actual fibre is

    F_rc = {g0+7h : h in C_rc} union {g_r+7h : h in D_rc}.

There are no additional points outside these two designated columns at that child. The private and common sets satisfy:

1. At each full root, the five D_rc are singleton sets with pairwise distinct elements.
2. At the gap root, after naming its four children, the private sets are {z}, E1, E2, E3. The Ei are three distinct two-element sets, and none contains z.
3. The gap private union has at least five elements:

       |{z} union E1 union E2 union E3| >= 5.

   Equivalently, the three Ei together have at least four elements. The singleton is included in the five-element condition.
4. The union of all common sets C_rc has at least five elements.
5. For every distinct root pair r,s, every q_r-element subset A of actual children at r, and every q_s-element subset B at s,

       |union_(c in A) C_rc union union_(c in B) C_sc| >= 3.

The C_rc may be empty. Condition5 is a joint condition on the two chosen roots, not a requirement that each root separately supplies three common leaves. These conditions describe all equality sources; the four graph types below classify only the gap private part, not the entire source or its common fibres.

### Necessity: from a cut to actual private columns

The reduction in448, before its incidence exclusion, shows that any65/63 cut has all actual children source-side, zero top cost, public cost1/3, private leaf counts(1,2,2,2) at the gap root, and(1,1,1,1,1) at each full root. There are exactly22 private cut leaves and no private first-prefix cut edge. The public cut P is either one whole first-seven column or three individual seven leaves.

Every actual child fibre is contained in P together with that child's private cut leaves: its path to the sink cannot cross an actual bridge or a top edge. A cut leaf is not automatically an actual point; this implication must be proved.

For two full roots and any three children at each, literal blocking supplies a ternary seven-tree in their actual projection. If P is a whole column, six private candidates must supply the other two columns with three distinct leaves each. If P consists of three leaves, the projection has at most nine candidate leaves and must contain a nine-leaf ternary tree. In either case all six selected private leaves are distinct, outside P, and actual at their own children. No other selected child can supply a leaf lying outside P and outside its own private cut set.

Exchanging one child in a full-root triple leaves five of these six private leaves fixed. The missing leaf's column is the only column where the new leaf can restore the required three-leaf count. Thus all five private leaves at any full root lie in one column and are pairwise distinct. This is448's exchange argument. Pairing roots shows that their three private columns are distinct. If P consists of three leaves, the two full-root private columns already account for six leaves of the ternary tree, so all three public leaves must lie in a third column g0. Comparison with all full-root pairs makes g0 distinct from each private column.

Now fix the gap child with its singleton cut leaf z', one of its two-leaf children E'_i, and any full-root triple. There are at most six private candidates beyond the public column. A ternary tree requires all six, split into two columns of three. In the three-public-leaf case the same conclusion follows by saturating the total nine-leaf count. Therefore z' and the two leaves of E'_i are actual at their own children, distinct, and in one new column. The full-root triple already fills the other private column.

The fixed z' forces this new column to be the same for all three i. Comparing with every full root makes it different from all three full private columns and from g0. Thus all seven gap private incidences are actual and lie in a fourth private column. The singleton is outside every E_i. Selecting any two of the two-leaf gap children with a full-root triple requires at least three leaves in their gap column, so their two-element sets must be different. The actual leaves at different gap children may overlap; only the stated distinctness conditions are forced.

At this point the entire source occupies exactly five columns. If the public cut consisted of three leaves, its column would have at most three actual leaves, and only four columns could support five leaves each. This contradicts the standalone five-ary tree. Hence the public cut is a whole column.

Every private cut leaf has now been proved actual at its own child. The path containment proves the displayed exact fibre decomposition, with C_rc the remaining actual common-column leaves. The standalone tree, on exactly five columns, requires at least five leaves in both the common column and the gap private column; the other three columns already have five. This gives conditions3 and4.

For any selected pair of actual child subsets, each of their private columns has at least three leaves. Their entire projection occupies only these two private columns and the common column. It contains a ternary tree exactly when the common union contains at least three leaves. This proves condition5.

### Sufficiency and the explicit minimum cut

Conversely, the displayed conditions supply two private columns with at least three leaves each for every selected root pair. A pair of gap children supplies three leaves because either it includes the disjoint singleton and one edge, or it includes two distinct edges. Condition5 supplies a third three-leaf column.

These pair/subset conditions imply full literal product blocking. A ternary five-tree uses at least two occupied roots, since only one root is empty. Its three literal children contain at least q_r actual children at each such root. Their projection contains a ternary seven-tree, which meets every five-ary seven-tree because3+5>7 at each level. Conditions1,3,4 also supply the standalone five-ary tree in the full projection.

Cut the whole public column at its first-prefix edge and cut each listed private leaf at its private depth-two edge. All top and private first-prefix nodes remain source-side. In each private tree put exactly the listed private leaves sink-side; in the public tree put the whole common column source-side and every other node, including the sink, sink-side. Each actual bridge has both ends on the same side. The cut costs

    1/3 + 22*(2/63) = 65/63.

Report447 gives the matching lower bound for every cut, since the source premises have just been proved. Thus this is precisely an equality source. The classification does not assert that its representation or minimum cut is unique.

## The private incidence graphs and one common law

View the three gap two-element sets as distinct edges on the six available second-seven digits other than z. Their endpoint union has at least four vertices. A simple three-edge graph is either a forest or a triangle; the triangle has only three endpoints and is excluded. The possibilities are exactly:

| Gap edge graph | Endpoints of the three edges | Private union including z |
| --- | ---: | ---: |
| Star K1,3 | 4 | 5 |
| Path P4 | 4 | 5 |
| Two-edge path plus a disjoint edge | 5 | 6 |
| Three disjoint edges | 6 | 7 |

Put zero mass on every common point. Work in units1/60. At each full root put three units on each of its five actual private points, for a root total15. At the gap root put three units on the singleton and four units on each edge-child, divided between its two actual endpoints so that every endpoint receives at most three units in total.

Such a division always exists. For any collection of one, two, or three distinct edge-children, its endpoint set has at least two, three, or four vertices respectively. Endpoint capacity three therefore exceeds or equals the required supply four per edge. These are precisely the capacitated Hall conditions. Alternatively, all four divisions are explicit:

| Graph with displayed edge order | Endpoint allocations, in units1/60 |
| --- | --- |
| Star oa,ob,oc | (1,3), (1,3), (1,3), with o first |
| Path ab,bc,cd | (3,1), (2,2), (1,3) |
| Path ab,bc and disjoint de | (3,1), (1,3), (2,2) |
| Three disjoint edges | (2,2), (2,2), (2,2) |

Every gap edge-child has four units, the singleton has three, and the gap root also has total15. The four roots therefore carry total60. This is one normalized law on22 actual points, not a collection of laws chosen separately for different tests. The common fibres play no role in its construction.

## All original numerical cylinder caps under that law

For every divisor d of1225 define c_d=max_a nu(x=a mod d), using the literal CRT identification of the five and seven coordinates. Since the four private columns belong to four distinct five-roots, a mod35 cylinder has at most one root's mass. The other caps follow from the four-unit child bound and three-unit private-leaf bound:

| Original modulus d | 1 | 5 | 7 | 25 | 35 | 49 | 175 | 245 | 1225 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| c_d in units1/60 | 60 | 15 | 15 | 4 | 15 | 3 | 4 | 3 | 3 |

For example, a mod175 cylinder fixes a five-child and a first-seven column, so it has at most four units. A mod245 cylinder fixes a five-root and a full seven leaf, so its mass is at most three units even when several gap children share that leaf. These are joint caps under the same law, with no conditional re-selection of residues.

The number of ordered divisor pairs with LCM5^i7^j is(2i+1)(2j+1). Thus the complete LCM envelope is

    sum_(d,e | 1225) c_lcm(d,e)
      = 1 + 15*(1/4) + 20*(1/15) + 45*(1/20)
      = 25/3 < 9.

Every compatible original pair intersection is a cylinder of that LCM; incompatible intersections contribute zero. Consequently Gamma_1225(nu) is at most this envelope for all independent original phase choices. The calculation is not an assertion that the maximum-cylinder choices for all pairs can be attained by one phase layout, or that25/3 is the optimized layout-game value.

The proof only uses the private incidences. Therefore a source containing this same labelled private structure admits the same law after adding any actual points, including points in new columns or children. This monotonicity concerns choosing a law supported on an actual subset; it does not assert that the subset retains product blocking. The latter failed for the low-incidence selection proposal in448 and is not needed here.

## Exact construction controls and boundaries

The [constructor and shape recognizer](../../frontier/cover-geometry/equality_source_private_law.py) retain the actual root, child and seven-leaf labels. The recognizer verifies the exact decomposition and all480 joint common-subset conditions. The separate law constructor only requires actual containment of the private structure, so it also accepts supersources outside the equality class. It never supplies a missing private point or fills a common fibre.

The [exact controls](../../frontier/cover-geometry/equality_source_private_law.controls.json) enumerate all3185 choices of singleton and three unordered distinct two-element sets on the other six seven-digits. They reject140 triangles and construct the law for all3045 valid choices:420 stars,1260 paths,1260 two-edge-path-plus-edge graphs, and105 three-edge matchings. Every constructed law is checked against all1767 numerical cylinders for the nine original divisors and all81 ordered divisor pairs. This finite enumeration verifies the implementation and displayed private shapes; the ordinary argument above supplies the source theorem.

There is a37-point equality source of each of the four private types: retain the22 private incidences, give each of the15 full-root children only the single common leaf with second digit equal to its child digit, and give the gap children no common points. Any full-root triple already supplies three common leaves, so every pair/subset condition holds; the public union has five. Each example passes all600 original pair/triple literal tests and the standalone five-ary predicate. These sources show concretely that a common column need not be a complete five-leaf fibre at every child.

The controls also distinguish these boundaries:

* Adding an actual point outside the designated two columns breaks the exact equality shape, while the original private law remains valid on that38-point supersource.
* Removing a full-root common point from the37-point example can leave fewer than three common leaves for a gap/full selected pair; the recognizer rejects the missing joint premise.
* Removing a private point makes the supplied private witness invalid; the constructor rejects the phantom incidence.
* A common translation by253 modulo1225, applied to the source and private witness together, retains the shape and original-label bound. It is not an independent relabeling in different arithmetic branches.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/equality_source_private_law.py
```

## Remaining source and arithmetic gaps

All sources with a literal65/63 equality cut are now controlled without an incidence-at-most-two assumption. Their sharp cuts force actual support structure sufficient for a different law. Sources with larger network minimum cuts are not thereby controlled: their high root/column incidence can still invalidate the earlier mixed-cap estimate. Some may contain the private structure, but its existence has not been proved for every remaining source.

The theorem is at the fixed head1225. An actual full odd-covering residual must also carry every original outside-cofactor constraint under one common lift, as in439. A head law alone does not supply that lift, and a uniform complete-Gamma bound below nine for arbitrary free cofactors is already ruled out there. The next arithmetic obligation remains a bound for the actual original test family and its same-law deletion correlations. No unrestricted noncoverage conclusion follows from this finite head theorem alone.
