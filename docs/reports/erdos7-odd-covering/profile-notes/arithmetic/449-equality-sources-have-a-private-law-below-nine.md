[Index](../../marked_head_profile.md) · [Literal equality reduction](448-literal-product-trees-exclude-the-equality-cut.md) · [Generic cut bound](447-strict-child-cut-surplus-and-arithmetic-boundaries.md)

# Literal cuts65/63 through68/63 force private laws below nine

The sharp network in [448](448-literal-product-trees-exclude-the-equality-cut.md) is not a moment obstruction. Every source attaining that network's lower bound65/63, under its literal product-blocking and standalone-tree premises, has one actual supported law with

    Gamma_1225(nu) <= 25/3 < 9.

This result allows incidence five at every full root. It uses actual private points forced by the equality cut, gives the common column zero mass, and chooses ONE probability before all original numerical labels and all phase tests. The same law construction applies to any larger actual source containing the specified private structure, whether or not that larger source has an equality cut or satisfies the tree premises.

The next cut values66/63,67/63 and68/63 also force actual private laws, with bounds159/19,79/9 and79/9, respectively. Large cuts at least79/63 are controlled by a separate sharp flow-cap estimate below.

These are ordinary proofs with exact construction controls, not new Lean-certified declarations. They do not prove that every remaining source contains this structure, lift the law through arbitrary original outside-cofactor tests, or settle unrestricted Erdős #7. The bound is uniform over a newly classified source family; it is not an improvement of448's particular117-point law bound107/13.

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

    Gamma_1225(nu)<=159/19=9-12/19<9.

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

Put the uniform law on all nineteen private points. It is a probability
on ACTUAL F, selected before the phases. Every first-five root and every
first-seven column contains at most five of these points. Its root-level
caps are therefore

    q5,q7,q35 <=5/19.

Every cylinder whose exponent at5 or7 is two contains at most one private
point. Thus

    q25,q49,q175,q245,q1225 <=1/19.

The complete ordered-LCM envelope on all81 ordered divisor pairs gives

    Gamma_1225 <=1+(3+3+9)*(5/19)+(5+5+15+15+25)/19
               =159/19<9.

This uses one fixed law and all nine independent query phases. The actual
source's other points may receive zero probability. No claim that deleting
them preserves the source's tree premises is needed. Giving every root
mass1/4 instead yields the valid but weaker bound141/16; uniform mass on
all nineteen actual points supplies the stronger bound above.

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
A coherent layout attains159/19 for this particular constructed law;
this does not assert source-level minimax optimality. Necessary cut
profiles are not treated as realized sources. The ordinary actual-point
and column-forcing arguments above are essential, and the private subset
itself need not satisfy the full source's tree premises.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut66_private_law.py
```

### A literal source realizing the66/63 stratum

The class is nonempty as a class of finite sources. Write source points
as(r,c,y), with x5=r+5c and y=x7, and put C0={0,7,14,21,28}. Define

    F_(1,c)=C0 union{29,1+7c},  c=0,...,3,
    F_(r,c)=C0 union{r+7c},   r=2,3,4, c=0,...,4.

This source has118 points. Its common column0 meets every occupied child,
so it has high incidence. Every gap/full pair-subset has ternary columns
0,1,r; every full/full pair-subset has columns0,r,s. Its whole projection
has five complete five-leaf columns0,...,4. The verifier checks all10000
literal ternary-five trees using the dual ternary-seven criterion, not
by enumerating all five-ary seven-trees.

An explicit cut consists of public column0, public leaf29 and the one
private leaf at each of the nineteen children. Its cost is

    21/63+7/63+19*(2/63)=66/63.

There is a matching actual flow in units1/63. Give each private point two
units. At each full root give its five actual common points with y=7c
weights(2,2,1,1,1); these add21 units altogether. At the four gap children
give their actual y=29 points weights(2,2,2,1), adding seven units. The
verifier checks every top, private-prefix and public-prefix capacity and
that the cut intercepts every actual path. Thus the minimum cut is
exactly66/63. This example is not claimed to be the residual of an
original odd whole cover.

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
also give t<=4/3=84/63. The private-law theorems in this report handle k=65,66,67,68,
and LC3 handles k>=79. Consequently the only remaining possible cut
values for that source class are k=69,...,78. This lists ten
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

Therefore fully active cuts in the remaining low window never have R>1. For R=1, cuts below79/63 have Z=6 or7, giving75/63 or77/63, and no top cost. Covering all five complete branches of the standalone tree with public/private prefixes of total unweighted integer cost9+Z<=16 forces a first-prefix edge in each branch: replacing a first-prefix cost3 by its five required leaf edges costs5, already exceeding the possible slack1. Thus the public cut has three whole columns, the private cut has two further whole columns, and at77/63 it has one extra private leaf. The two private whole columns are first-prefix cut cylinders, each in one child tree; this does not assert that the child has all seven leaves as actual points. This excludes other fully active R=1 low-cut structures. The public/private construction below supplies a law for these fully active R=1 shapes. It uses the precise pair-projection property retained after excluding the owner children, without asserting that deletion preserves product blocking.

## Whole-column75/63 and77/63 shapes admit one mixed law

Suppose the same literal source admits the fully active, bridge-free
R=1 cut shape just classified: three whole public first-seven columns,
two further whole private first-seven columns, and at77/63 one additional
private leaf. There is one actual supported probability with

    Gamma_1225(nu)<=491/55=9-4/55<9.                 (WC1)

This statement allows the two private columns to belong to the same child,
two children at one root, or children at different roots. It is a theorem
about the specified cut witness, which need not be a minimum cut. It does
not classify every source whose minimum cut numerically equals75/63 or
77/63: other public costs and partially active cuts remain separate.

### Actual private mass and the public projection left after restriction

Let P be the three public columns and U,V the two private columns, with
owner children e_U,e_V. At77/63 let w be the extra private leaf with owner
e_w. Actual path containment says

    F_e subset P
                union ([U] if e=e_U)
                union ([V] if e=e_V)
                union ({w} if e=e_w).

At75/63 omit the last term. The actual standalone tree requires five
columns with five leaves each. The one extra leaf cannot supply a whole
branch, so the tree uses exactly the three public columns and U,V;
these five column labels must all be distinct. Among its five leaves
in U, every leaf other than possibly w must occur in e_U itself.
Thus e_U contains at least four actual leaves in U, and e_V contains at
least four in V. Select four in each and put mass1/44 on each selected
point. This gives one private measure pi of total mass2/11, with mass1/11
in each private column. The eight points remain distinct when the owners
coincide, since U and V are different columns.

Let D={e_U,e_V} be the set of distinct owner children. For the public
construction alone exclude D. At each root r, let m_r be its remaining
child count and delta_r=q_r/m_r. Always m_r>=q_r. Choose any q_r remaining
children at r and q_s at a different root s. The original literal test
provides a ternary seven-tree in their actual union. That union lies in
P union{w}. A column outside P can contain only w and cannot supply three
leaves. Consequently the selected actual public projection contains the
whole ternary tree in P. This proves pairwise public projected-law
feasibility for every such selection. It does not assert arbitrary
product-blocker inheritance after deleting D.

### Six budgets and one common public law

Reserve public mass W=9/11. Order roots as gap a, then full b,c,d;
permute the three full labels as needed. Use the following public root
budgets A and public root-prefix coefficients B:

| owners of U,V | delta | A | B |
|---|---|---|---|
| same gap child | (2/3,3/5,3/5,3/5) | (12/55,1/3,1/3,1/3) | (9/22,9/22,9/22,9/22) |
| same full child | (1/2,3/4,3/5,3/5) | (2/5,12/55,1/3,1/3) | (1/2,4/11,17/44,17/44) |
| two gap children | (1,3/5,3/5,3/5) | (1/5,1/3,1/3,1/3) | (3/11,5/11,5/11,5/11) |
| two children at one full root | (1/2,1,3/5,3/5) | (2/5,1/5,1/3,1/3) | (1/2,3/11,19/44,19/44) |
| one gap and one full child | (2/3,3/4,3/5,3/5) | (3/10,4/15,1/3,1/3) | (9/22,4/11,19/44,19/44) |
| children at two full roots | (1/2,3/4,3/4,3/5) | (2/5,4/15,4/15,1/3) | (1/2,4/11,4/11,9/22) |

For every subset S of roots the table satisfies

    sum_(r outside S) A_r>=W                         if |S|<=1,
    sum_(r outside S) A_r+(1/2)sum_(r in S) B_r>=W    if |S|>=2,
    sum_(r outside S) A_r+sum_(r in S,r!=j) B_r>=W    if |S|>=2, j in S.

These are exactly [445's weighted pair-cut conditions](445-occupied-branch-restrictions-and-weighted-root-caps.md)
with alpha=A/W and beta=B/W. Their minimum slacks, in the three displayed
families and table order, are respectively

    (1/15,0,47/330), (1/15,0,79/660), (8/165,0,4/33),
    (8/165,0,4/33), (9/110,0,59/330), (8/165,0,41/330).

Independently and uniformly choose a q_r-subset of the m_r remaining
children at every root. For each complete selection, apply445's weighted
row/tree theorem to its actual public projection, with seven-prefix caps
3^(-j). Lift each projected point to a selected actual child and scale
by W. Average these conditional laws over all selections. This is one
actual public measure mu; the separate pair witnesses are only feasibility
premises for the common flow, and are never pasted together as laws.

A fixed remaining child is selected with probability delta_r. Its
conditional mass is at most the whole corresponding root or root-prefix
mass even though the conditional law depends on all selections. The
restriction averaging of[444](444-uniform-subtree-restrictions-couple-two-prefix-trees.md)
therefore gives, for each seven-prefix Y_v of depth j=1,2,

    mu(r)<=A_r,               mu(r,c)<=delta_r A_r,
    mu(Y_v)<=W 3^(-j),
    mu(r,Y_v)<=B_r 3^(-j),    mu(r,c,Y_v)<=delta_r B_r 3^(-j).

Owner children have zero mu mass. All mu points lie in P.

### All numerical cylinders under the same mixed law

Set nu=mu+pi. The two measures have disjoint first-seven columns and total
mass one. Let rho_r be pi's root mass; it is1/11 times the number of
private columns owned at r. The maximum private child mass is2/11 if
the owners coincide and1/11 otherwise. Thus

    q5<=max_r(A_r+rho_r)<=2/5,
    q25<=max(max_r delta_r A_r, maximum private child mass)<=1/5.

At the seven prefixes the disjoint public/private columns give

    q7<=max(W/3,1/11)=3/11,
    q49<=max(W/9,1/44)=1/11.

The joint cylinders similarly give

    q35<=max(max_r B_r/3,1/11)<=1/6,
    q175<=max(max_r delta_r B_r/3,1/11)<=1/11,
    q245<=max(max_r B_r/9,1/44)<=1/18,
    q1225<=max(max_r delta_r B_r/9,1/44)<=1/33.

Every independently phased pair of original divisor queries is either
incompatible or intersects in a numerical LCM cylinder. The complete
ordered-pair sum is bounded by

    1+3*(2/5)+3*(3/11)+5*(1/5)+9*(1/6)
      +5*(1/11)+15*(1/11)+15*(1/18)+25*(1/33)
    =491/55<9.

The source, private points and public law are fixed before the phases.
An extra private leaf used only to complete the standalone tree need not
receive mass. No claim is made that the selected probability support is
itself a product blocker.

### Exact budgets and actual-source constructions

The [whole-column constructor](../../frontier/cover-geometry/height_two_whole_column_law.py)
and [exact results](../../frontier/cover-geometry/height_two_whole_column_law.json)
check all264 rational budget inequalities and construct actual laws using
the existing weighted coupling and restriction programs. They cover all
six owner placements at both cut costs, plus an irregular public-fibre
control. Every control checks480 selected pair tests,10000 complete
literal five-tree tests,1767 numerical cylinders and81 ordered LCM pairs.

In the twelve basic controls, every nonowner child has the first five
leaves in each of the three public columns. At75/63 each private owner
has five leaves in its private column. At77/63 the U owner has only four,
and one nonowner supplies its fifth leaf as w; the V owner still has five.
This verifies the case where four actual U-owner leaves is the full
available guarantee. The irregular control changes public leaf sets by
child and requires three distinct restricted projection flows with their
original multiplicities. All thirteen laws have the bound(WC1).
The reported75/77 cut is an explicit fully active cut witness; no minimum
cut value is claimed for these controls.

These are ordinary mathematical deductions and finite exact constructions,
not new Lean results. The theorem does not supply an original odd-covering
realization or the same-source lift through arbitrary outside cofactors.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_whole_column_law.py
```

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

This excludes the(5/9,16) structure at67/63. The fully active(1/3,23) case is handled next. The cut66 profile verifier checks both possible profiles and the unique rejected private-cost shape.

## The67/63 stratum also has one common law below nine

Under the same literal source and network premises, every source with
minimum cut67/63 admits one supported law with Gamma_1225<=79/9<9.
Two of its three remaining private-cut shapes give159/19. The law uses
actual selected points, before any independent query phases are chosen.

### The three remaining shapes

The previously reviewed low-cut reduction makes the cut fully active. It leaves `(R,Z)=(1/3,23)` and `(5/9,16)`; the latter is excluded by the standalone projection count. Thus `R=1/3`, total unweighted private integer cost is `23`, and the public cut set `P` is either one whole first-seven column or three seven leaves.

Put `p_r` equal to the least `q_r`-child private sum, where `q=(2,3,3,3)`. The pair constraints are `p_r+p_s>=6`. The sorted-integer lower functions are

`f_gap(p)=p+2 ceil(p/2)` and `f_full(p)=p+2 ceil(p/3)`.

If the smallest `p` is0,1,2, the Report448 minimum-coordinate bounds are at least28 and exclude total23. Hence all `p>=3`. At `(3,3,3,3)` the lower sum is22. Increasing a full-root coordinate to4 increases that root's lower bound from5 to8 and is impossible. The gap coordinate can increase to4, whose lower bound is8, but cannot increase further. Consequently the only possibilities are:

- **A:** `p=(4,3,3,3)`. Gap costs `(2,2,2,2)`; every full root has five costs1.
- **B:** `p=(3,3,3,3)`, with the one excess unit at the gap root. Gap costs `(1,2,2,3)`; every full root has five costs1.
- **C:** `p=(3,3,3,3)`, with the one excess unit at one full root. Gap costs `(1,2,2,2)`; one full root has costs `(1,1,1,1,2)`; the other two have five costs1.

The sorted-vector claims follow directly from the prescribed least-two or least-three sum and total. For example, gap total8 and least-two sum3 force `(1,2,2,3)`; full total6 and least-three sum3 force `(1,1,1,1,2)`.

A child of cost1 has one private cut leaf; cost2 has two. A cost3 child may have three private leaves or one private first-prefix edge. The latter is only a candidate whole column until actual points are forced below.

For every child, path containment gives `F_rc subset P union S_rc`, where `S_rc` is its own private cut-prefix union. No bridge crosses. This statement does not identify all points of `S_rc` as actual.

### Two clean full roots lock the public and private columns

Call a full root clean when all five children have one private cut leaf. There are at least two clean full roots in A, B, and C.

Choose any three children at each of two clean full roots. Literal product blocking forces a ternary seven-tree in their actual projection. If `P` is one whole column, the six private candidates must provide exactly the other two three-leaf columns. If `P` consists of three leaves, the nine candidates must be distinct actual leaves and form exactly three columns with three leaves each. In either case every selected private leaf is outside `P`, globally distinct within the selection, and actual at its own child: no other selected child can supply its unique leaf outside `P`.

Exchange one child in a clean-root triple while retaining the other two and the partner triple. The column-count vector changes by the difference of two coordinate unit vectors, while both original vectors have entries divisible by3. Hence the exchanged leaves have the same first-seven column. Since each clean root has at least four singleton children, every pair of them can be compared using two other children.

Thus the five private leaves of each clean full root are actual at their own children, distinct, and in one column. The two private columns are different. In the three-public-leaf case, the two private triples occupy two complete three-leaf columns, so the three public leaves all lie in a third column `G`. In the whole-column case, call that column `G` too. Therefore in both cases

`P subset G`,

and every established full private column differs from `G`.

In A and B, apply the same argument to the third clean full root. There are three distinct full private columns `H1,H2,H3`, with five actual singleton points at each root.

In C, use any three of the four singleton children of the exceptional full root, paired with a triple at a clean full root. The same count and exchange argument applies to these four children: two alternative triples share two children, enough to compare any pair. Their four private leaves are actual at their own children and occupy one column `H3`. Pairing with both clean roots proves `H3` differs from `G,H1,H2`. We retain these four points and do not use the exceptional cost2 child's points. The exceptional full root still supplies legal triples from its four retained children for every gap argument below.

Accordingly all three cases have three distinct columns `H1,H2,H3`, each admitting a triple of actual private points at three distinct children of its root, and all disjoint from `G`.

### A useful consequence of pairing with full-root triples

Suppose a chosen pair of gap children has at most four private leaf candidates. Its actual projection, together with a fixed full-root triple in `Hj`, is contained in `G`, three points of `Hj`, and those at most four candidates.

A ternary tree cannot omit `G`: outside it there are at most seven leaves. It cannot omit `Hj`: the gap pair has at most four candidates, insufficient for two further three-leaf columns. Hence there is a third column, different from `G,Hj`, containing at least three distinct actual leaves supplied by the gap pair.

There can be only one column containing at least three leaves of a set of at most four. Testing the same gap pair against triples in `H1,H2,H3` therefore shows that this unique third column avoids all three full private columns. All statements concern actual unions of the two child fibres; candidate cut leaves are never promoted without this tree count.

### Shape A: four two-leaf children

Let `A_i` be the actual leaves outside `G` at gap child `i`; each has size at most2. For every pair `i,j`, the preceding argument gives at least three leaves of `A_i union A_j` in a unique column `K_ij`, outside `G,H1,H2,H3`.

All the `K_ij` coincide. Indeed, if `K_ij` and `K_ik` differed, child `i` would have exactly one leaf in each of those two columns. Child `j` would then need two leaves in `K_ij`, and child `k` two leaves in `K_ik`. Their pair would have no column containing three leaves, a contradiction.

Call the common column `K` and put `B_i=A_i intersect K`. These are nonempty actual sets of size at most2, with every pair-union having size at least3. They have a four-element system of distinct representatives. Hall's conditions for one, two, and three sets are immediate. For four sets, a union of size at most3 is impossible: a singleton would force all the other sets to be the same complementary pair, violating the pair condition; without a singleton, four distinct two-element subsets would be required inside a three-element set, which has only three such subsets.

Choose these four distinct actual gap leaves, one at each gap child. They all lie in `K`, outside all full private columns. Retain all fifteen actual points at the clean full roots. This gives nineteen selected points, different at every full five-child and every full seven-leaf.

### Shape B: one singleton, two doubles, and one cost3 child

Name the first three gap private sets `{z}`, `E1`, `E2`, and call the cost3 child `d`.

Pair the singleton child with either double child and a full-root triple. There are exactly three gap private candidates, so all three are actual at their own children, distinct, and in one third column. The shared `z` makes this the same column `K` for both doubles. Testing all three full roots shows that `K` avoids `G,H1,H2,H3`. Thus `E1,E2` are actual two-element subsets of `K`, neither containing `z`.

Pair the two double children with a full-root triple. Their union must contain at least three leaves in `K`, so `E1 != E2`, and `|E1 union E2|>=3`.

If child `d` has three private cut leaves, its actual leaves outside `G` form a set `A_d` of size at most3. Pairing it with the singleton and each full-root triple yields one of two alternatives:

1. `A_d` contains at least two actual leaves in `K` different from `z`; or
2. all three of its cut leaves are actual in one other column `J`, distinct from `K,G,H1,H2,H3`.

To see exhaustion, if the third tree column is `K`, the singleton accounts for only `z` and at least two further actual leaves are required. Otherwise three of `d`'s at most three candidates fill that other column. It is then fixed for every full-root test and cannot equal any `Hj`.

If child `d` instead has one private first-prefix edge, write its candidate column as `J`. This does not mean the entire column is actual. If `J=G` or `J=Hj` for some `j`, pairing `d` and the singleton with a triple in that `Hj` leaves at most the columns `G,Hj` and the lone point `z`, and no ternary tree is possible. Therefore `J` avoids `G,H1,H2,H3`. If `J=K`, the same pair test forces at least two actual leaves of `d` in `K` different from `z`. If `J!=K`, the lone `z` cannot fill a tree branch, so `d` must have at least three actual leaves in `J`.

The two resulting selection cases are simple. If `d` supplies actual leaves in a new column `J`, choose one there, retain `z`, and choose distinct representatives from `E1,E2`. If it supplies at least two actual leaves in `K` different from `z`, apply Hall to `E1,E2` and any two of those leaves: every set has size2, and their total union has size at least3 because `E1 != E2`. Choose three distinct representatives and also `z`.

Thus four actual gap points can be chosen, one per child, all distinct as seven-leaves, and all outside the three full private columns. They occupy either only `K` or `K` and one new column `J`. Retain all fifteen full-root points. There are nineteen selected points, and no seven-column contains more than five: each full column has five, while the gap contributes only four points total outside them.

### Shape C: retain four singleton children at the exceptional full root

The clean-root argument already supplies five points at each clean full root and four actual singleton points at the exceptional full root, in three distinct columns `H1,H2,H3`.

The gap has one singleton candidate `{z}` and three double candidates `E1,E2,E3`. Pair the singleton with each double and a triple from any of the three full columns. The same exact three-leaf count makes all of them actual at their own children, with `z` outside every `Ei`, all in one common column `K` outside `G,H1,H2,H3`.

Pairing any two double children with a full-root triple gives `|Ei union Ej|>=3`, so the double sets are distinct. They have distinct representatives: every set has two elements, every pair has at least three, and all three together have at least three. Choose those representatives and `z`.

Retaining these four gap points, the ten points at the two clean full roots, and the four singleton points at the exceptional full root gives eighteen actual selected points. There is at most one point per five-child and per seven-leaf; the seven-column counts are `(5,5,4,4)`.

### The stronger uniform law and every original phase

In A and B use the uniform law on all nineteen selected points. In C use the uniform law on all eighteen. Write the selected count as `N`.

Every first-five root has at most five points. Every first-seven column has at most five points, including B's possible additional gap column. Hence every modulus5,7,35 cylinder has mass at most `5/N`.

Each literal five-child and each literal seven-leaf contains at most one selected point. Every other nonunit cylinder —25,49,175,245,1225— therefore has mass at most `1/N`.

Select this one law before the query. Every pair of the nine independently phased original labels has empty intersection or a cylinder of its literal LCM. Including the unit-unit term exactly once, all81 ordered pairs give

`Gamma_1225 <= 1 + (3+3+9)*5/N + (5+5+15+15+25)/N = 1+140/N`.

For `N=19` this is `159/19`; for `N=18` it is `79/9`. The latter bounds all three cases. These are supported laws on selected actual points, with no requirement that the selected subset retain the source's product-blocking property.

### Exact shape, matching and source controls

The [cut67 verifier](../../frontier/cover-geometry/height_two_cut67_private_law.py)
and its [result](../../frontier/cover-geometry/height_two_cut67_private_law.json)
check every p-vector in{0,...,23}^4, all sorted child-cost shapes with total23,
the finite Hall claims up to relabelling of their union, and every literal
CRT cylinder of canonical19-point and18-point selected laws. Their exact
LCM bounds are159/19 and79/9. The general actual-point forcing comes from
the preceding ordinary argument, not from those canonical law patterns.

The three-public-leaf branch cannot be discarded. One actual source is
constructed as follows, in coordinates(r,c,g,h). At full roots r=1,2,3,
every child c=0,...,4 has the three public leaves(0,0),(0,1),(0,2) and its
private leaf(r,c). At the gap root r=0 the four child fibres are

    {(4,0)}, {(4,1),(4,2)}, {(4,3),(4,4)}, {(5,h): h=0,...,4}.

The public column0 has only three actual leaves. The standalone tree uses
columns1,2,3,4,5 instead. Its public cut consists of three leaves, and the
last gap child's private cut is a first-prefix edge. The total cut is
(21+2*23)/63=67/63. The verifier checks all480 selected pair/subset tests,
all10000 literal ternary-five trees through ternary-seven duality, an
exact integral maximum flow of67/63, and a19-point actual supported law.
It witnesses this previously easy-to-omit case without asserting an
original covering-family realization.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut67_private_law.py
```

## The68/63 stratum has an actual eighteen-point law

Keep the literal height-two product-blocking, standalone five-ary seven
projection, occupancy4555 and actual-child network premises stated above.
Every source with minimum cut68/63 has one actual supported probability
satisfying

    Gamma_1225(nu)<=79/9=9-2/9<9.

There are two minimum-cut profiles. The fully active profile uses a
standalone-tree supplier construction; the partially active profile uses
literal pair/subset tests to force private columns. Both produce eighteen
actual points with distinct five-child labels, distinct seven leaves and
at most five selected leaves per seven-column. The law is chosen once,
before every original query phase.

### Complete active/public and private-cost classification

Use a,T,k,p and f from(A1)–(A2). Write

    top=sum_r min(3,n_r-a_r),
    Z=sum_(all child trees) z_rc,
    cut numerator=7(top+k)+2Z.

Private costs on inactive children are included in Z. No actual bridge
crosses a cut of this size. The eligible-count bounds already used above
exclude zero, one or two eligible roots. For three eligible roots including
the gap root the continuous lower bound is69/63. If the eligible roots are
the three full roots, a missing active child raises the half-sum branch
from66/63 by at least4/63; with all three full roots active and top cost1/3,
the integer table above has minimum71/63. Thus all four roots are eligible.

For a partially active profile put delta_r=n_r-a_r. The half-sum lower
bound is

    1+5 delta_0/126+(4/63)sum_(r=1..3)delta_r.

The exclusion branches are at least90/63, and the top-plus-one branch
is at least70/63. A cut at most68/63 therefore requires

    5 delta_0+8 sum_(r=1..3)delta_r<=10.

Up to permutation of full roots, only the following three partial
profiles remain. Applying(A2), their lower numerators are:

| active profile | k0 | k1 | k2 | k3 | k4 | k5 | k6 | k7 | k8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| (3,5,5,5) |73|74|75|68|71|72|77|78|79|
| (2,5,5,5) |76|77|78|71|76|77|82|83|84|
| (4,4,5,5) |73|74|75|70|71|72|77|78|79|

Public cost R>=1 plus positive top cost is already at least70/63.
Consequently the only partial profile is a=(3,5,5,5), top=1, k=3, Z=20.
For full activity the earlier lower table leaves k=3,4,5; parity excludes
k=3 and5 at numerator68. The standalone-tree bound excludes R>=1.
Thus the only full profile is a=(4,5,5,5), top=0, k=4, Z=20.

The private shapes are also determined. In the partial profile,
f_gap(p)=p+ceil(p/2) and f_full(p)=p+2ceil(p/3). If the least coordinate
of p is0,1 or2, the minimum-coordinate argument gives private lower costs
at least29,29 or26. Otherwise all coordinates are at least3; the baseline
cost is5+3*5=20. Increasing any coordinate exceeds20. Hence

    p=(3,3,3,3),
    active gap costs=(1,2,2),
    each full root's costs=(1,1,1,1,1).

There is no private cost at the one inactive gap child. All active
private cut edges are leaves, since a first-prefix edge has integer cost3.

In the full profile the only p-vector with lower cost at most20 is
(2,3,3,3), with lower cost19. If every coordinate is at least3 the cost
is at least22; a minimum0 or1 costs at least27. A minimum2 at a full root
costs at least21; at the gap it costs19 only when all other coordinates
are3, and raising any of them exceeds20. The one excess unit therefore
gives exactly two shapes:

- gap costs(1,1,1,2), with every full-root cost equal to1;
- gap costs(1,1,1,1), with one full-root cost vector(1,1,1,1,2)
  and all other full-root costs equal to1.

In either shape there are twenty private leaf occurrences at nineteen
actual children. Exactly one child has two private cut leaves; all others
have one. This counts occurrences, without assuming that cut leaves are
actual or globally distinct.

### Full activity: use an actual standalone tree to select suppliers

For each child c let S_c be its private cut-leaf set, and P the public
cut-prefix support. The absence of a bridge crossing gives the actual
fibre containment

    F_c subset P union S_c.

Public cost4/9 is four leaves or one whole first-seven column G plus
one leaf y_star. Four public leaves would put the entire seven projection
in at most24 points, contradicting its actual twenty-five-leaf standalone
tree. Thus P=G union{y_star}.

Outside G the actual projection has at most21 candidates: the twenty
private occurrences and y_star. Fix one actual standalone five-ary tree.
It must use G, since otherwise all twenty-five leaves would be outside G.
Its four other columns contain twenty distinct actual leaves. Delete
y_star if it occurs. The remaining set X has at least nineteen leaves,
lies outside P, and has at most five leaves in each column.

For every y in X choose a child c whose actual fibre contains y. Such a
supplier exists because the fixed tree is actual. Since y is outside P,
the containment forces y into that supplier's own S_c. Each singleton
child can therefore supply at most one distinct chosen leaf, and the
unique double child can supply at most two. Keep one assigned leaf per
supplier. At most one leaf is lost, leaving at least eighteen actual
pairs with different children and different seven leaves. Retain any
eighteen. Their column caps are inherited from the fixed tree.

This construction does not need every private candidate to be actual,
and does not claim that the selected subset still blocks every tree.
Its hypotheses are weaker than the full literal source premises, so it
covers both full private-cost shapes at once.

### Partial activity: force three gap points and fifteen clean points

Here the public support P is one whole column or three leaves. For every
ACTIVE child its actual fibre lies in P union its own private leaf set;
this containment is not applied to the inactive gap child.

Choose three children at each of two full roots. Literal product blocking
forces a ternary seven-tree in their actual union. If P is a whole column
G, the six private candidates must be distinct actual leaves outside G,
split between two columns of three. If P consists of three leaves, there
are at most nine candidates altogether, so all nine must be distinct and
actual. In both cases each private candidate belongs to its own child's
actual fibre: it is outside P and every other selected private support.

Exchange one selected child while retaining two at its full root and the
partner triple. In the whole-column case the external column counts are
multiples of3; in the three-leaf case the full nine-leaf column counts are.
The change is the difference of two unit vectors, so the exchanged private
leaves lie in the same column. Any two of the five children can be
compared using two others. Thus each full root has five distinct actual
private leaves in one column H_r. The three H_r are different. In the
three-public-leaf case, the two private triples already occupy two
columns, so P occupies a third column G; comparing root pairs makes G
different from all three H_r. In both cases P is contained in G.

The three active gap children have private sets {z},E1,E2 of sizes1,2,2.
Pair the singleton child with either double child and a triple at any
full root. Outside G there are at most six candidates: three from these
gap children and three from the full root. A ternary tree requires all
six to be distinct and actual, divided into two columns of three. The
full-root triple is already in H_r, so z and the tested pair are in one
other column K, distinct from G and H_r. Their own-child actualness again
follows from the distinct private candidates and the public containment.
The shared z fixes the same K for both doubles; testing all full roots
makes K different from every H_r.

Keep z, any leaf of E1, and a different leaf of E2. The last choice exists
because E2 has two leaves; neither double contains z. Together with the
fifteen full-root private points these give eighteen actual pairs with
different child labels and seven leaves. Their column counts are3,5,5,5.
The inactive gap child remains part of the source and receives zero law
mass; no claim is made that removing its fibre preserves blocking.

### One uniform law and exact construction controls

Put uniform mass1/18 on the selected points in either case. Distinct
child labels give the full-five-digit caps, distinct seven leaves give
the full-seven-digit caps, and root/column occupancies are at most five:

    q5,q7,q35<=5/18,
    q25,q49,q175,q245,q1225<=1/18.

Every intersection of two independently phased original divisor queries
is empty or a cylinder at their numerical LCM. The complete ordered-pair
multiplicities therefore give, for this ONE law,

    Gamma_1225<=1+(3+3+9)*5/18+(5+5+15+15+25)/18
              =79/9<9.

The [profile and partial-source program](../../frontier/cover-geometry/height_two_cut68_private_law.py)
and its [exact result](../../frontier/cover-geometry/height_two_cut68_private_law.json)
check all10800 necessary active/public profiles and all21^4 p-vectors for
each survivor, including every compatible sorted private shape and
inactive-cost slack. They return exactly the two profiles and the three
private shapes above. These enumerations check the finite classification;
the source-to-law proofs are the arguments just given.

An actual144-point control realizes the partial minimum-cut profile.
Let G0={(0,j):0<=j<5}. For full roots r=1,2,3 and children c=0,...,4 use
F_(r,c)=G0 union{(r,c)}. At the four gap children use

    F_(0,0)={(4,0)},
    F_(0,1)={(4,1),(4,2)},
    F_(0,2)={(4,3),(4,4)},
    F_(0,3)={0,...,6}^2.

A gap pair containing the last child already has a ternary tree. Any
other gap pair supplies at least three leaves in column4, while a full
triple supplies its private column and column0. Two full triples also
supply three ternary columns. The standalone five-ary tree is immediate.
The exact actual-child network has maximum flow68, matching a cut with
top, private and public numerators7,40,21 and no bridge crossing. Its
residual-reachable active counts are(3,5,5,5). The program checks480
selected pair/subset tests,10000 complete literal five-tree tests,
1767 numerical cylinders and81 ordered LCM pairs. The selected eighteen
actual points give the envelope79/9. This control is not asserted to be
the residual of an original odd covering system.

The [actual supplier constructor](../../frontier/cover-geometry/height_two_cut68_actual_matching.py)
and its [controls](../../frontier/cover-geometry/height_two_cut68_actual_matching.json)
accept an arbitrary literal source and a specified actual standalone tree
satisfying the weaker full-profile containment hypotheses. They verify
integer CRT coordinates and actual suppliers before selecting the law.
One control has maximum matching exactly18: two singleton children share
the same sole actual leaf. Another has maximum matching19. Independent
child/leaf/column matching networks verify both values; these are matching
networks, not the actual-child cut network of447. Neither control is
claimed to satisfy literal product blocking. Thus18 is sharp for the
weaker matching hypotheses, without claiming that79/9 is an optimal law
bound or that the stronger cut68 source class cannot yield nineteen
points. Missing actual tree leaves and noninteger digit inputs are
rejected.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut68_private_law.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut68_actual_matching.py
```

## At78/63 the choice of maximum flow matters

All raw quantities in this section are integer units1/63 unless otherwise
stated. A literal68-point source realizes both a bad and a good maximum
flow at78/63. The example refutes the assertion that every maximum flow
works. The subsequent mixture criterion is conditional: existence of its
reroutings on every admissible source remains unproved.

### Integral flows leave a discrete equality obstruction

Choose an integral maximum flow of value78, possible because all scaled network capacities are integers. At one coherent centre write u_d for its integer cylinder mass. Let

    h=u5+u175-u25-u35>=0,
    s5=21-u5, s7=21-u7, s35=21-u35, s49=7-u49,
    s175=6-u175, s245=7-u245, s1225=2-u1225.

The conic identity behind449 LC2 gives exactly

    625-K = 8s5+3s7+4s35+5s49+20s175+15s245+25s1225+5h.

Every term is a nonnegative integer multiple of a coefficient at least3. Thus a coherent charge is either625 or at most622;623 and624 are impossible. In the625 case every displayed slack and h vanishes, so in particular

    u5=u7=u35=21, u25=u175=6, u49=u245=7, u1225=2.

The chosen five-root and seven-column carry21 and all their mass lies in their joint block. Such blocks use distinct roots and distinct columns, and there are at most three because total mass is78. Report449's existing noncoherent estimate622 already falls below the target624; the remaining issue is to select a law that removes these coherent obstructions with more than one unit of saving.

### The same actual source has a bad and a good maximum flow

The [exact flow-choice program](../../frontier/cover-geometry/height_two_cut78_flow_choice.py) and its [result](../../frontier/cover-geometry/height_two_cut78_flow_choice.json) construct the following source. Use full five-roots r=0,1,2, gap root r=3 with children0,1,2,3, and empty root4. Let common seven-column be0, the full roots' private columns be r+1, and the gap private column be4.

At each full root include the support of the matrix

    T=[[2,2,2,0,0,0,0],
       [2,2,1,1,0,0,0],
       [2,0,0,0,0,0,0],
       [1,2,1,1,0,0,0],
       [0,1,1,0,0,0,0]]

in its private column, with row=actual five-child and column=second seven digit. Add the actual point(c,h)=(0,4) in that private column. Also include one common-column point h=c at each child. At the gap root, child c has exactly the two actual leaves(4,0) and(4,c+1).

This is a68-point source with occupancy5554, equivalent to4555 by a root permutation. Every full-root triple has at least three private leaves and three common leaves. Every gap pair has three private leaves. Thus every pair of three literal five-children at distinct occupied roots projects to a ternary seven-tree; all600 literal tests pass. All five occupied seven-columns have at least five leaves, giving the standalone five-ary tree.

Put T's indicated masses on each full-root private block,21 per root. In the gap private column put masses(2,2,2,1) on the four h=0 points and mass2 on each distinct h=c+1 point. The gap contributes15. This is a legal actual-bridge flow of total78.

A matching actual network cut has the three full-root source edges, costing63; the common-tree leaf edge at(4,0), costing7; and the four private leaf edges at the gap's(c,4,c+1), costing8. No actual bridge crosses. The exact edge list and cut membership realization in the program show that the minimum cut is exactly78, rather than merely supplying a feasible measure of that mass.

At a full root's private centre with(c,h)=(0,0), the raw nonunit charge is625. The measured cylinder maxima, in order(5,7,25,35,49,175,245,1225), are(21,21,6,21,7,6,7,2). Their complete ordered-LCM envelope is625 for the nonunit square and is attained by that one centre. Thus this SAME normalized maximum-flow law has exact Gamma703/78=9+1/78 without needing the general449 phase bound. The sharp-cap obstruction therefore CAN occur as an actual maximum flow on a source satisfying the literal blocking/tree/network hypotheses. Those hypotheses do not make an arbitrary maximum-flow output good.

The source nevertheless has a better maximum flow. For each full root move one unit from its actual private point(c,h)=(0,0) to its actual common-column point(c,h)=(0,0). Child totals stay unchanged, private capacities remain legal, and the new common leaf receives only three units. The three old private columns now carry20 each, common column3 and gap column15, so every root/column cylinder is at most20. The measured cylinder maxima are(21,20,6,20,7,6,7,2). Using the full ordered-LCM multiplicities(3,3,5,9,5,15,15,25), their nonunit envelope is613. One coherent centre attains613, so this second maximum-flow law has exactly

    Gamma=1+613/78=691/78<9.

Both exact Gamma values follow from complete81-pair upper envelopes and matching legal layouts. The checker verifies5806 predicates: actual support,600 literal product tests, standalone tree, all1211 network capacities and conservation, the matching cut, all1767 literal cylinders for each law, and matching ordered-LCM/coherent-centre bounds. It uses only standard-library integer/rational arithmetic.

### A common mixture of conditional reroutings

Let lambda be any integral value78 maximum flow in the stated source class. List the b<=3 root/column blocks supporting625 centres. Assume for each such block i there is another integral value78 flow lambda_i on the SAME source with:

* that old root/column block's mass at most20;
* at each five-child which supports an old625 centre in that block, the new pure-five-child mass at most6.

All other eight caps follow from being a legal flow. Every cylinder of an old625 centre was at its cap except u25=6; the second condition prevents that exceptional term from increasing. Its u35 decreases by at least one. In the exact coherent formula with coefficient9 on u35 this gives charge at most616 in lambda_i. Every centre remains at most625 in every lambda_i.

Use one common mixture

    lambda_bar=(1/2)lambda+(1/(2b))sum_i lambda_i

when b>0; if b=0, lambda already suffices. For a centre not originally625, its mixed charge is at most(622+625)/2=623.5. For an old625 centre in block i it is at most625-9/(2b)<=623.5. Noncoherent layouts obey622 under every flow and hence under their mixture. All flows have the same mass and are supported on the same literal source, so

    Gamma(lambda_bar/(78/63))<=1+623.5/78=1403/156<9.

This avoids conflating independently available reroutes: their convex mixture is explicitly one feasible flow. It also avoids the false inference that making every old625 value merely strict automatically crosses624.

One transparent sufficient realization of each hypothesis is an actual off-block bridge plus a residual return route that moves a unit out of the old block, keeping its used child's total fixed. A free destination common leaf/column gives such a move immediately; an alternating residual path may provide it when the destination is saturated. If the new child had zero old mass, it was not an old625 child. Original bridge support, both private-prefix capacities, and both common-prefix capacities must be checked on the entire route. A presumed root-level four-cycle is not enough.

The unresolved uniform obligation is to obtain the stated reroutings
from literal product blocking and the actual source, or construct a law
by another method when a required residual route is absent. The existence
of an off-block point alone does not certify residual reachability under
all private and common capacities. The68-point example rules out solving
this obligation by excluding625 equality from every actual maximum flow;
it does not refute a uniform theorem selecting a good law.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut78_flow_choice.py
```

## Remaining source and arithmetic gaps

All sources with a literal65/63,66/63,67/63 or68/63 minimum cut are controlled without an incidence-at-most-two assumption. These cuts force actual support structure sufficient for a different law.
For occupancy4555, the large-cut estimate also handles every cut at
least79/63. General high-incidence sources in the remaining range69/63
through78/63 are not thereby controlled: their high root/column incidence
can still invalidate the earlier mixed-cap estimate. The fully active R=1
whole-column shapes at75/63 and77/63 are controlled by(WC1), but this
does not settle all sources at those numerical cut values. Some may contain
the private structure, but its existence has not been proved for every
remaining source. Other occupancy patterns retain their own stated
premises and are not classified by this ten-value reduction.

The theorem is at the fixed head1225. An actual full odd-covering residual must also carry every original outside-cofactor constraint under one common lift, as in439. A head law alone does not supply that lift, and a uniform complete-Gamma bound below nine for arbitrary free cofactors is already ruled out there. The next arithmetic obligation remains a bound for the actual original test family and its same-law deletion correlations. No unrestricted noncoverage conclusion follows from this finite head theorem alone.
