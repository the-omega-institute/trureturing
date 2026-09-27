[Index](../../marked_head_profile.md) · [Literal equality reduction](448-literal-product-trees-exclude-the-equality-cut.md) · [Generic cut bound](447-strict-child-cut-surplus-and-arithmetic-boundaries.md)

# Literal 65/63 and 66/63 cuts force private laws below nine

The sharp network in [448](448-literal-product-trees-exclude-the-equality-cut.md) is not a moment obstruction. Every source attaining that network's lower bound65/63, under its literal product-blocking and standalone-tree premises, has one actual supported law with

    Gamma_1225(nu) <= 25/3 < 9.

This result allows incidence five at every full root. It uses actual private points forced by the equality cut, gives the common column zero mass, and chooses ONE probability before all original numerical labels and all phase tests. The same law construction applies to any larger actual source containing the specified private structure, whether or not that larger source has an equality cut or satisfies the tree premises.

The next cut value66/63 also forces an actual private law, with bound141/16<9. Large cuts at least79/63 are controlled by a separate sharp flow-cap estimate below.

These are ordinary proofs with exact construction controls, not new Lean-certified declarations. It does not prove that every remaining source contains this structure, lift the law through arbitrary original outside-cofactor tests, or settle unrestricted Erdős #7. The bound is uniform over a newly classified source family; it is not an improvement of448's particular117-point law bound107/13.

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

## The next cut value66/63 also forces one private law

Keep exactly the literal height-two source, occupancy4555 and network
premises above. If the minimum cut is66/63, there is one actual supported
probability with

    Gamma_1225(nu)<=141/16=9-3/16<9.

This conclusion has no low-incidence premise. It neither assumes nor
proves that an original odd-covering residual realizes this cut value.

### The cut is fully active with public cost4/9

Write n=(4,5,5,5), q=(2,3,3,3). No actual bridge crosses such a cut, since a bridge costs2. Let a_r be its number of source-side actual children and I={r:a_r>=q_r}. The root nodes may be chosen to minimize the top cost without changing any child or tree node. A minimum cut therefore has exact top cost

    T=sum_r min(1/3,(n_r-a_r)/9).

Write its public cost R=k/9. For every active child put z_rc=9L_rc, the nonnegative integer unweighted private-cut cost. Let p_r be the least sum of q_r such costs among the a_r active children at eligible root r. The existing pair-of-subsets inequality gives

    p_r+p_s>=9-k.

Sorting a_r nonnegative integers with least-q_r sum p_r gives

    sum_(active c) z_rc >= f_(a_r,q_r)(p_r),
    f_(a,q)(p)=p+(a-q)ceil(p/q).                    (A1)

This is447's integer lemma with the actual active-child count in place of the full occupancy. Extra costs on inactive child trees only increase the cut.

The existing continuous bounds already exclude |I|<=2 (the |I|=1 refinement is448). If |I|=3 includes the four-child root, its continuous bound is at least69/63. If I consists of the three full roots, removing any active child raises the half-sum branch from66/63 by at least4/63, while the other branches are larger. The only possible profile is therefore three fully active full roots, with T=1/3; the gap root is ineligible.

For |I|=4, put delta_r=n_r-a_r. In the half-sum branch the lower bound is

    1 + 5 delta_0/126 + (4/63)sum_(r=1..3)delta_r.

The exclusion branches are at least90/63, and a positive top cost makes the top-plus-one branch at least70/63. Thus the only not-fully-active candidate at cost<=66/63 is a=(3,5,5,5), with T=1/9.

Both exceptional partial profiles are excluded by the exact integer version(A1). If u=9-k>0, the minimum of sum f_r(p_r) under all pair inequalities is

    Z_min = min_(j in I, 0<=p<=ceil(u/2))
               [f_j(p) + sum_(r in I,r!=j) f_r(max(p,u-p))].   (A2)

To justify(A2), choose a coordinate attaining the minimum p. Every other coordinate must be at least max(p,u-p); setting them to that value preserves all mutual pair inequalities and minimizes the increasing costs. A minimum p above ceil(u/2) can be lowered by setting every coordinate to ceil(u/2).

The resulting minimum cut numerators (over63), for k=0,...,8, are:

| active eligible profile | k0 | k1 | k2 | k3 | k4 | k5 | k6 | k7 | k8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| three full roots; T=1/3 |71|74|77|72|77|80|83|86|89|
| (3,5,5,5); T=1/9 |73|74|75|68|71|72|77|78|79|

R>=1 is also impossible for a partial profile because T>=1/9. Thus all nineteen actual children are source-side and T=0.

For this fully active profile,447's integer table gives minimum numerators

    k=0,...,8: 70,71,72,65,66,67,72,73,74.

At k=3 the actual numerator is21+2Z and hence odd, so cannot equal66. Thus k=4 and Z=19. For a fully active cut, the standalone-tree inequality below gives R+sum L>=5/3. For 1<=R<=5/3 the cut cost is at least R+(2/7)(5/3-R)>=75/63; for R>5/3 its public cost already exceeds66/63. Thus R>=1 is excluded.

### Every actual child has one private cut leaf

At k=4 the pair inequalities are p_r+p_s>=5. Here

    f_gap(p)=p+2ceil(p/2),
    f_full(p)=p+2ceil(p/3).

The unique p-vector whose total lower bound is19 is

    p=(2,3,3,3).

Indeed if every p>=3 the cost is at least22. If the minimum is0 or1, the minimum possible costs, according as it occurs at gap/full, are27/29 and27/27. If it is2, they are19/21; equality19 requires the minimum at the gap and every other coordinate exactly3.

The gap root's four child costs consequently total4 with least-two sum2, so all four equal1. Each full root's five costs total5 with least-three sum3, so all five equal1. A private depth-one edge would have unweighted integer cost3, so all private cuts consist of exactly one depth-two leaf for each child. Call that leaf y_rc.

Let P be the union of the public cut-prefix cylinders. Every actual child fibre lies in P union{y_rc}: otherwise its actual path from the source-side child to the sink crosses neither a private edge nor a public edge, while no bridge crosses.

### The standalone tree forces twenty actual external leaves

Public cost4/9 has just two forms: four depth-two leaves, or one full first-seven column G plus one depth-two leaf y_star. Four leaves would put the full seven projection in at most4+19=23 points, contradicting its standalone five-ary depth-two tree, which has25 leaves.

Hence P=G union{y_star}. The standalone tree must use G as one of its five first-seven columns: only20 candidate leaves lie outside G. It requires at least20 distinct actual leaves outside G. Therefore ALL nineteen y_rc and y_star are outside G, pairwise distinct and actual, and their union fills exactly four other columns with five leaves each. In particular each y_rc is actual at its OWN child: it is outside P and is no other child's private cut leaf, so no other child can supply it.

No cut leaf is declared actual merely because it occurs in the cut. Actualness follows from the forced25-leaf standalone tree and the exact outside count.

### Literal pair/subset tests force one private column per root

Fix any two gap children and any three children at one full root. The actual combined seven projection lies in G plus exactly six distinct candidate external leaves: their five private leaves and y_star. Literal product blocking requires a ternary depth-two tree. Such a tree must use G and exactly two other columns, with three leaves each; all six external candidates are therefore required.

Keep the gap pair fixed and exchange one child in the full-root triple. The vector of external column counts is always3e_g+3e_h, for distinct g,h. Its change is e_col(y_new)-e_col(y_old). Every coordinate of the former difference is divisible by3, whereas the latter has coordinates in{-1,0,1}. Thus the two exchanged leaves have the same first-seven digit. Every pair of full-root children can be compared this way. All five private leaves at that root lie in one column.

Each full root therefore fills five distinct leaves in one of the four external columns. The three full roots occupy different columns, since the global external column counts are exactly five. The four gap private leaves and y_star fill the fourth column. Thus the actual nineteen-point private pattern is:

- one distinct first-seven column per five-root;
- one actual private point per child;
- four distinct private leaves at the gap root and five at each full root.

### One fixed law handles every independently phased original query

Give every root mass1/4, distributed uniformly among its own n_r private points. It is a probability on ACTUAL F. Its root-level caps are

    q5,q7,q35 <=1/4.

Every cylinder whose exponent at5 or7 is two contains at most one private point. Its mass is at most1/(4*4)=1/16, so

    q25,q49,q175,q245,q1225 <=1/16.

The complete ordered-LCM envelope on all81 ordered divisor pairs gives

    Gamma_1225 <= 1 + (3+3+9)/4 + (5+5+15+15+25)/16
               = 141/16 <9.

This uses one fixed law and all nine independent query phases. The actual source's other points may receive zero probability, just as in449's private-law construction. No claim that deleting them preserves the source's tree premises is needed.

### Exact necessary-profile and private-law controls

The [cut-profile verifier](../../frontier/cover-geometry/height_two_cut66_private_law.py)
and its [exact result](../../frontier/cover-geometry/height_two_cut66_private_law.json)
check10800 necessary active/public profiles: all1080 active-child tuples
and k=0,...,9. They implement A1--A2 and additionally use Z>=sum a_r
when k=0 (each nonempty active child needs a private edge), and Z>=15-k
for fully active cuts (the standalone-tree inequality). The only lower
profiles at most66 have all children active, with(k,Z)=(3,22) or(4,19).
Parity leaves only the latter at actual cost66. Larger public costs
cannot yield another66 profile: partial cuts have T>=1/9, while fully
active cuts satisfy the standalone-tree bound.

The verifier also checks uniqueness of the p-vector and child-cost
shapes, then embeds the nineteen-point private pattern into literal CRT
residues and checks all1767 numerical cylinders and81 ordered LCM pairs.
A coherent layout attains141/16 for this particular constructed law;
this does not assert source-level minimax optimality. Necessary cut
profiles are not treated as realized sources. The ordinary actual-point
and column-forcing arguments above are essential, and the private subset
itself need not satisfy the full source's tree premises.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut66_private_law.py
```

## Large cuts give a different law without an incidence restriction

The same actual-child network also controls sufficiently large cuts using
its original capacities alone. Keep gamma=2/7 and write t for its maximum
flow, equivalently its minimum cut. Decompose a flow of value t>0 into
source-to-sink paths, put its mass on the actual child/leaf bridges and
normalize by t. This gives ONE probability nu on F before any query is
selected. Each path uses one actual bridge; no unsupported point is added.

The source/root, root/child and common-seven edges give

    q_5,q_7 <= 1/(3t),    q_25,q_49 <= 1/(9t).

For the mixed cylinders, use the private child tree when it is needed:

    q_35 <= 1/(3t),       q_175 <= 2/(21t),
    q_245 <= 1/(9t),      q_1225 <= 2/(63t).

The first and third bounds follow by containment in a pure5 or pure49
cylinder, respectively. A mod175 cylinder uses one child's private
first-seven edge, and a mod1225 cylinder uses its private second-seven
edge. None requires an upper bound on how many children meet a root/column
cylinder. The same normalized flow supplies all eight bounds.

The unit label still has q_1=1. Applying the complete ordered-LCM envelope
to all nine independent original query labels gives

    Gamma_1225(nu)
      <= 1 + [6/3 + 10/9 + 9/3
                    + 15*(2/21+1/9) + 25*(2/63)]/t
       = 1 + 10/t.                                      (LC1)

The joint constraints sharpen LC1. For a finite nonnegative measure lambda
on Z/25 x Z/49, write q_d for its largest literal modulus-d cylinder mass.
Suppose the eight nonunit bounds, in units1/63, are

| d | 5 | 7 | 25 | 35 | 49 | 175 | 245 | 1225 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 63 q_d, upper | 21 | 21 | 7 | 21 | 7 | 6 | 7 | 2 |

Then the full independent-phase maximum satisfies

    Gamma_1225(lambda)-lambda(1)<=625/63.               (LC2)

Here is a proof covering every layout. The independent pair envelope is10.
If the six labels with positive5-exponent do not all agree at the first
five digit, partition them by that digit. At least five unordered pairs
are incompatible. The same assertion holds on the7-axis. If both first
digits agree but a full depth-two digit does not, the three labels with
that depth split into at least two incompatible unordered pairs. Each
incompatible pair has zero mass and loses at least2*(2/63) from the
independent envelope. Thus every layout without a common centre has
nonunit charge at most10-8/63=622/63.

In the remaining case all first digits and all full depth-two digits
agree on their respective axes. CRT then supplies one centre for all nine
query labels. Write u_d for the mass of its modulus-d cylinder. The
nonunit square is exactly

    K=3u_5+3u_7+5u_25+9u_35+5u_49
        +15u_175+15u_245+25u_1225.

Within the modulus5 cylinder, the modulus25 and modulus35 cylinders have
intersection the modulus175 cylinder. Nonnegativity therefore gives
u_25+u_35<=u_5+u_175. Adding five times the resulting nonnegative
difference to K and applying the same eight bounds gives

    K<=8u_5+3u_7+4u_35+5u_49
          +20u_175+15u_245+25u_1225
      <=625/63.

This proves LC2 without assuming that a coherent layout maximizes an
arbitrary fixed source. For the flow above, lambda=t nu satisfies its
eight hypotheses. Thus

    Gamma_1225(nu)<=1+625/(63t),
    t>=79/63 implies Gamma_1225(nu)<=704/79<9.           (LC3)

This is a direct use of the existing flow and LCM bounds, not a new
formalized theorem or a statement about every supported law. It requires
no literal tree premise beyond whatever is used to establish the cut
value. In the occupancy4555 setting of447, the stated tree premises give
t>=65/63. All network capacities, including the actual bridges, are
integer multiples of1/63; so t=k/63 for an integer k. The source edges
also give t<=4/3=84/63. The private-law theorems above handle k=65,66,
and LC3 handles k>=79. Consequently the only remaining possible cut
values for that source class are k=67,...,78. This lists twelve
unresolved values, not a claim that each is attained or that each source
at those values fails. Any source already containing the private
structure above is handled regardless of its cut value.

## The eight flow caps alone cannot improve the discrete threshold

The constant625/63 is attained by an explicit nonnegative measure of
mass78/63 satisfying EVERY literal cylinder bound in LC2. To describe
it in units1/63, use the following five-child by seven-child matrix:

    T = [[2,2,2,0,0,0,0],
         [2,2,1,1,0,0,0],
         [2,0,0,0,0,0,0],
         [1,2,1,1,0,0,0],
         [0,1,1,0,0,0,0]].

At root pairs(r,g)=(0,0),(1,1),(2,2), put T_(c,h) at
(x5,x7)=(r+5c,g+7h). At(3,3), use the same matrix with its first row
removed. All other masses are zero. Each complete block has mass21/63,
the last has15/63, and there are53 positive atoms. The row sums are at
most6, column sums at most7, and each entry at most2. These facts check
all eight cylinder types, including the cross-coordinate caps.

At the common centre0 the masses, in the table's order, are

    (21,21,6,21,7,6,7,2)/63.

Its nonunit square is625/63. LC2 supplies the matching upper over ALL
independently phased layouts. Normalizing this SAME measure therefore
gives the exact value

    Gamma_1225(lambda/lambda(1))=703/78=9+1/78.          (LC4)

This is a counterexample to obtaining a universal value below9 from
these eight caps at t=78/63 alone. It is not an example satisfying all
the source's tree premises, nor a source whose network has minimum cut
78/63. It does not exclude a better law on a given actual source.
The next improvement must use more source structure or a more selective
construction of the common law.

The [sharp-cap program](../../frontier/cover-geometry/height_two_flow_caps_sharp.py)
and [result](../../frontier/cover-geometry/height_two_flow_caps_sharp.json)
check every one of the1767 numerical cylinders, the single unit term and
the displayed exact moments on the53-atom measure. The universal upper
for all layouts is the ordinary two-case proof above; the finite replay
does not enumerate or certify that universal quantifier in Lean.

## Additional cut-structure reduction for R>=1

For any fully active cut below79/63, no actual bridge crosses, and the whole seven projection is covered by its public and private cut prefixes. Let mu be the uniform law on a standalone five-ary depth-two tree. Every depth-B prefix satisfies

    mu(prefix)<=5^(-B)<=(3/5)3^(-B).

Consequently R+sum L_rc>=5/3. If R=k/9>=10/9, the cut cost is at least

    R+(2/7)(5/3-R)=(30+5k)/63>=80/63.

Therefore fully active cuts in the remaining low window never have R>1. For R=1, cuts below79/63 have Z=6 or7, giving75/63 or77/63, and no top cost. Covering all five complete branches of the standalone tree with public/private prefixes of total unweighted integer cost9+Z<=16 forces a first-prefix edge in each branch: replacing a first-prefix cost3 by its five required leaf edges costs5, already exceeding the possible slack1. Thus the public cut has three whole columns, the private cut has two further whole columns, and at77/63 it has one extra private leaf. This excludes other fully active R=1 low-cut structures. It does not yet supply a law for those75/77 shapes or justify deleting their exceptional children.

## One67/63 cut structure is also impossible

Every67/63 minimum cut is fully active. Extending the partial-profile
argument from66 to67 adds one eligible candidate, (4,4,5,5), and its
permutations among the three full roots. Its A2 lower numerators for
k=0,...,8 are

    (73,74,75,70,71,72,77,78,79).

Its minimum70, together with the earlier partial-profile minimum68,
excludes every partially active cut. The necessary-profile verifier
checks these cases as part of its10800 profiles. The447 all-active table
and parity then leave only(R,Z)=(1/3,23) or(5/9,16).

In the latter case the pair inequalities are p_r+p_s>=4. Their unique total16 integer minimum is p=(2,2,2,2). The gap child costs are all1; each full root's sorted costs are(0,1,1,1,1). Thus there are exactly sixteen private cut leaves and no private depth-one cut. Public cost5/9 means either five leaves or one full column plus two leaves. Five leaves give total seven projection size at most21<25. One full column leaves at most18 distinct points outside it, whereas a standalone five-ary tree needs either20 outside it or25 if it does not use that column. Both cases are impossible.

This excludes the `(5/9,16)` STRUCTURE at67/63. It does not close67/63: the fully active `(1/3,23)` case remains. The exact verifier checks both possible profiles and the unique rejected private-cost shape.

## Remaining source and arithmetic gaps

All sources with a literal65/63 or66/63 minimum cut are controlled without an incidence-at-most-two assumption. These cuts force actual support structure sufficient for a different law.
For occupancy4555, the large-cut estimate also handles every cut at
least79/63. General high-incidence sources in the remaining range67/63
through78/63 are not thereby controlled: their high root/column incidence
can still invalidate the earlier mixed-cap estimate. Some may contain
the private structure, but its existence has not been proved for every
remaining source. Other occupancy patterns retain their own stated
premises and are not classified by this twelve-value reduction.

The theorem is at the fixed head1225. An actual full odd-covering residual must also carry every original outside-cofactor constraint under one common lift, as in439. A head law alone does not supply that lift, and a uniform complete-Gamma bound below nine for arbitrary free cofactors is already ruled out there. The next arithmetic obligation remains a bound for the actual original test family and its same-law deletion correlations. No unrestricted noncoverage conclusion follows from this finite head theorem alone.
