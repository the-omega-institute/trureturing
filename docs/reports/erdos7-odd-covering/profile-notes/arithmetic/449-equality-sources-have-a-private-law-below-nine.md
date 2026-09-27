[Index](../../marked_head_profile.md) · [Literal equality reduction](448-literal-product-trees-exclude-the-equality-cut.md) · [Generic cut bound](447-strict-child-cut-surplus-and-arithmetic-boundaries.md)

# Literal height-two cuts: supported laws and joint flow repairs

The sharp network in [448](448-literal-product-trees-exclude-the-equality-cut.md) is not a moment obstruction. Every source attaining that network's lower bound65/63, under its literal product-blocking and standalone-tree premises, has one actual supported law with

    Gamma_1225(nu) <= 25/3 < 9.

This result allows incidence five at every full root. It uses actual private points forced by the equality cut, gives the common column zero mass, and chooses ONE probability before all original numerical labels and all phase tests. The same law construction applies to any larger actual source containing the specified private structure, whether or not that larger source has an equality cut or satisfies the tree premises.

The next cut values66/63 and67/63 force actual nineteen-point laws with bound159/19. The68/63 and69/63 strata have eighteen-point laws with bound79/9. The saturated-block transport theorem below controls every cut78/63, with the sharp local refinement giving bound233/26. Large cuts at least79/63 are controlled by a separate sharp flow-cap estimate.

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
also give t<=4/3=84/63. The private-law theorems in this report handle k=65,66,67,68,69,
the saturated-block transport theorem below handles k=78, and LC3 handles
k>=79. Consequently the only remaining possible cut values for that source
class are k=70,...,77. This lists eight
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
minimum cut67/63 admits one supported law with Gamma_1225<=159/19<9.
All three private-cut shapes supply nineteen actual points. The law uses
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

In C, use any three of the four singleton children of the exceptional full root, paired with a triple at a clean full root. The same count and exchange argument applies to these four children: two alternative triples share two children, enough to compare any pair. Their four private leaves are actual at their own children and occupy one column `H3`. Pairing with both clean roots proves `H3` differs from `G,H1,H2`. These four singleton children supply complete actual triples outside G for every gap argument below. Shape C's additional fifth-point argument also uses the exceptional cost2 child.

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

### Shape C: a fifth actual point at the exceptional full root

The clean-root argument already supplies five points at each clean full root and four actual singleton points at the exceptional full root, in three distinct columns `H1,H2,H3`.

The gap has one singleton candidate `{z}` and three double candidates `E1,E2,E3`. Pair the singleton with each double and a triple from any of the three full columns. The same exact three-leaf count makes all of them actual at their own children, with `z` outside every `Ei`, all in one common column `K` outside `G,H1,H2,H3`.

Pairing any two double children with a full-root triple gives `|Ei union Ej|>=3`, so the double sets are distinct. They have distinct representatives: every set has two elements, every pair has at least three, and all three together have at least three. Choose those representatives and `z`.

The exceptional full root also supplies a fifth actual point. Let d be its double child and E=F_d minus G, so |E|<=2. Pair d and any two of its four singleton children with a clean-root triple. Outside G there are at most seven leaves. A ternary tree must use G, the clean column, and H3: no other column can receive three leaves from E alone. Thus E has an actual H3 leaf outside the selected pair. If all its H3 leaves were among the four old singleton leaves, choose a pair containing E intersect H3, contradicting that requirement. Therefore d has a new actual H3 leaf outside all four old leaves.

Retain this fifth point, the ten clean-root points and the four gap points. There are nineteen actual selected points, one per five-child and per seven-leaf, with seven-column counts `(5,5,5,4)`. This argument also applies to the four-singleton-plus-double full roots in the69/63 classification below.

### The stronger uniform law and every original phase

In all three cases use the uniform law on the nineteen selected points. Write `N=19`.

Every first-five root has at most five points. Every first-seven column has at most five points, including B's possible additional gap column. Hence every modulus5,7,35 cylinder has mass at most `5/N`.

Each literal five-child and each literal seven-leaf contains at most one selected point. Every other nonunit cylinder —25,49,175,245,1225— therefore has mass at most `1/N`.

Select this one law before the query. Every pair of the nine independently phased original labels has empty intersection or a cylinder of its literal LCM. Including the unit-unit term exactly once, all81 ordered pairs give

`Gamma_1225 <= 1 + (3+3+9)*5/N + (5+5+15+15+25)/N = 1+140/N`.

For `N=19` this is `159/19` in all three cases. The eighteen-point subsupport bound `79/9` remains valid but is weaker. These are supported laws on selected actual points, with no requirement that the selected subset retain the source's product-blocking property.

### Exact shape, matching and source controls

The [cut67 verifier](../../frontier/cover-geometry/height_two_cut67_private_law.py)
and its [result](../../frontier/cover-geometry/height_two_cut67_private_law.json)
check every p-vector in{0,...,23}^4, all sorted child-cost shapes with total23,
the finite Hall claims up to relabelling of their union, and every literal
CRT cylinder of canonical19-point and18-point selected laws. Their exact
LCM bounds are159/19 and79/9; the eighteen-point control remains a valid
subsupport bound. The stronger shape C conclusion uses the additional
fifth actual point proved above. The general actual-point forcing comes from
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

## The69/63 stratum has an actual eighteen-point law

For the same literal height-two source, every minimum cut69/63 has one actual law with Gamma_1225<=79/9. This is an ordinary mathematical result; not Lean verification and not unrestricted Erdős #7. All selected points below belong to the same original actual fibre family F. A private cut set remains a candidate set until an actual membership argument is given.

### Necessary minimum-cut profiles

Use occupancy N=(4,5,5,5), subset sizes Q=(2,3,3,3), source-root capacities21, root-child capacities7, private column/leaf costs6/2 and public column/leaf costs21/7, all in units1/63. The actual minimum cut has value69/63. No bridge of capacity126 crosses it.

For active counts a, minimum-cut root placement gives top cost7T, where T=sum_r min(3,N_r−a_r). Write public cost7k and private cost2Z. For every eligible pair of roots, the least-Q private sums satisfy p_r+p_s>=9−k. A sorted active root with a children and least-q sum p costs at least

    f(a,q,p)=p+(a−q)ceil(p/q).

For k=0 every nonempty active child requires a private edge. If fully active, the standalone five-ary tree gives Z+k>=15. The standalone bound and pair bounds are used only as necessary conditions.

The [cut69 verifier](../../frontier/cover-geometry/height_two_cut69_private_law.py) exhausts all10800 active/public cases and all feasible sorted private shapes. It finds exactly two necessary profiles:

| active | T | k | Z |
|---|---:|---:|---:|
| (4,5,5,5) |0|3|24|
| (4,5,5,5) |0|5|17|

There is no partial-active case. The k5 profile has three sorted shapes; every private child cost is at most2, hence every private edge is a leaf. Public k5 is either five leaves or one whole column plus two leaves. In the first case the total projection has at most5+17=22 leaves. In the second it has at most2+17=19 leaves outside the whole column. Both contradict a standalone five-ary tree, which requires25 total leaves and at least20 outside any one column. Thus k5 is impossible.

For k3, the eligible p-vectors are (3,3,3,3), with base cost22, and (4,3,3,3), with base cost23. The ten sorted shapes are listed below. A string such as1222 is a sorted cost vector; a cost3 may be three leaf edges or one whole private column, while cost4 may be four leaves or a column plus one leaf.

| ID | gap | full roots, up to permutation | selected count proved below |
|---|---|---|---:|
| A |0333|11111,11111,11111|18|
| B |1222|01222,11111,11111|18|
| C |1222|11111,11111,11113|18|
| D |1222|11111,11111,11122|18|
| E |1222|11111,11112,11112|19|
| F |1223|11111,11111,11112|18|
| G |1224|11111,11111,11111|18|
| H |1233|11111,11111,11111|18|
| I |2222|11111,11111,11112|18|
| J |2223|11111,11111,11111|18|

Every shape has total private cost24. For every child the source-side path argument gives F_rc subset P union S_rc, where P is either a whole public column or three public leaves.

### Common actual column facts

These use the literal requirement that any selected two gap children and three full-root children, or any two selected full-root triples, have an ACTUAL union containing a ternary seven-tree.

**Singleton locking.** Two selected triples of singleton private candidates have only six private candidates. If P is a column, all six must be distinct actual leaves outside it. If P consists of three leaves, all nine candidates must be distinct actual leaves and form three columns of three. A unique candidate outside P must be actual at its own selected child.

Exchange one singleton child, keeping the other two and the partner triple fixed. The applicable column-count vectors have every entry divisible by3 before and after the exchange. Their difference is a difference of coordinate unit vectors. Hence the two exchanged candidates have the same column. A full root with at least four singleton children therefore has all those singleton leaves actual at their own children, distinct and in one column. A root with exactly three singleton children has its three leaves in one column once paired with an already locked partner triple.

In every case here there are either two clean full roots, or at least four singleton children at each full root. Thus this argument gives P subset G for one column G and locked private full-root columns H1,H2,H3 whenever that root has at least three singleton children. The H columns are pairwise distinct and outside G, by pairing their triples. In shape B the exceptional root's column is obtained separately below. Each clean root supplies five actual points; a 11112/11113 root supplies four initially; a11122 root supplies three initially.

**Two small gap fibres.** Suppose at each of three full roots there is a selected child triple whose COMPLETE actual union outside G is exactly three distinct leaves in H1,H2,H3 respectively, with these columns distinct and outside G. Three locked singleton children supply such a triple; the zero+singleton+double triple in shape B also supplies one after its tight count. For a fixed gap pair with total private candidate count at most4, pair it in turn with those three triples. The union outside G has at most seven candidate leaves, so a ternary tree must use G. Outside G and the tested H_j there are at most4 gap candidates, so it must use the tested H_j and one additional column with at least3 actual gap leaves. A set of at most4 has at most one such column. It must therefore avoid all H1,H2,H3.

Consequently the two actual gap fibres, restricted outside G union H1 union H2 union H3, have union size at least3. This is an actual-union statement; it does not promote every private candidate.

**Small-set Hall fact.** Four sets of size at most2 whose every pair has union at least3 have four different representatives. Each is nonempty; every pair and every triple satisfy Hall. If the full union had at most3 elements, four such sets would be impossible: no singleton can coexist with more than one size-two set under the pair condition, while a three-element set has only three different two-element subsets. Three such sets likewise have three representatives. This is the small-set Hall fact already used in report449's cut67 proof.

**Gap singleton plus doubles.** With private profile1222, every singleton/double pair has exactly three candidates. The preceding tight tree count forces the singleton z and both double leaves to be distinct and actual at their own children, in a common column K outside G and all H_j. The shared z makes K the same for all doubles. Testing two double children forces their union to have at least3 leaves. The three double sets therefore have distinct representatives, all different from z; this gives four actual gap points in K.

With only two double children, profile122, the same tight argument already gives three actual gap representatives. No hypothesis about a fourth gap child is needed.

**Gap cost3 extension.** Suppose a gap singleton z and a double set E are already actual, lie in K outside G and all H_j, and are disjoint. Pair the singleton child with a cost3 child d against each of the three full-root triples.

If d has three candidate leaves, their union with z has at most4 leaves. The unique possible three-leaf column lies outside G and all H_j, by testing all three anchors. If it is K, d supplies at least two actual leaves different from z; if another column, all three are supplied by d.

If d instead has one private column J, the lone z cannot complete a new branch without d. J cannot be G or any H_j. When J=K, d supplies at least two actual leaves different from z; when J differs from K, d supplies at least three actual leaves in J.

Thus in either edge type d has at least two actual leaves outside G and all H_j and different from z. The three children with profile123 admit three distinct actual representatives. With profile1223, the two double sets have union at least3, and together with d's at-least-two-element set they admit three distinct representatives by Hall; adding z gives four. These points occupy at most K and one further column outside the H_j, so no selected gap column has more than4 points.

### Shape-by-shape actual selection

#### A: gap0333

Keep all15 clean full-root private points. The zero-cost child's actual fibre is inside G. Pair it and any one cost3 child d against each full-root triple. The only possible third branch must come entirely from d.

For three private leaves, all three must be actual in one column outside G and every H_j. For one private column, that column must avoid G and every H_j and contain at least three actual leaves of d. Each of the three cost3 children therefore has at least three eligible actual leaves. Choose different representatives greedily from these three sets. They are outside the full-root columns, and contribute only3 total points. With the15 full points this gives18.

#### B: gap1222 and exceptional full root01222

Lock the two clean full-root columns H1,H2 and P subset G. In the exceptional root, select its zero child, its singleton child w, and any one double child. Against a clean full-root triple there are exactly three exceptional private candidates. They must all be distinct actual leaves in one column H3 outside G and that clean column. The shared singleton w and tests against both clean roots put every exceptional double set in the same H3 outside G,H1,H2, with w excluded from each double.

Select the zero child and any two exceptional doubles, and test against a clean triple. At least3 distinct H3 leaves are required. Hence the three exceptional double sets have pairwise union at least3. Choose three distinct representatives from them, together with w, giving four actual exceptional-root points. The zero child is not selected.

The gap singleton/double test against H1,H2 gives its column K; testing the same gap pair against the exceptional triple zero+w+double proves K differs from H3. The gap Hall argument gives four actual gap points in K. Together with ten clean points and four exceptional points this gives18, with columns carrying5,5,4,4.

#### C: gap1222 and exceptional full root11113

Retain the ten clean points and the exceptional root's four locked singleton points. Ignore its cost3 child, whether its private cut consists of a whole column or three leaves. The three locked full-root columns supply the anchors for the four-point gap1222 selection. Total14+4=18.

#### D: gap1222 and exceptional full root11122

Keep the ten clean points and the three actual singleton points T in H3. For a double child d, put E=F_d minus G; then |E|<=2. Choose any two of T and d and pair with a clean triple. A ternary tree must use G and the clean column: outside them there are at most four candidates. Its third branch must be H3 because E alone has at most2 points in any other column. Therefore E supplies an H3 leaf outside the selected pair, for EVERY pair from T.

If E had no H3 leaf outside T, choose a pair of T containing E intersect H3, which has size at most2. This contradicts the preceding requirement. Thus d has a new actual leaf in H3 outside all three singleton leaves. Retain one such leaf from either double child. This gives14 full-root points. The gap1222 argument gives four outside all H_j, for18 total. The second double child is not selected.

#### E: gap1222 and two full roots11112

Singleton locking gives5,4,4 actual full points. The same pair test used in D forces each exceptional double child to supply a new actual leaf in its own full-root column, outside all four locked singleton leaves: if all its at-most-two actual H_j leaves were old, select a pair containing them. Thus the full roots provide5+5+5 actual points. Gap1222 gives four points in a fourth private column. Total19, with column counts5,5,5,4. Any18-point subset also suffices.

#### F: gap1223 and one full root11112

Keep the ten clean points and four singleton points in the exceptional root, giving14 full-root points and three distinct anchor columns. The gap cost3 extension above gives four different actual gap points outside all three H_j, including when the cost3 child has a private whole-column edge. Total18. Its full exceptional double child need not be used.

#### G: gap1224 and three clean full roots

Keep all15 clean full points. Use only the gap singleton and its two cost2 children. The tight gap122 argument gives three different actual points outside all full columns. Ignore the cost4 child; its alternative private-prefix realizations are irrelevant. Total18.

#### H: gap1233 and three clean full roots

Keep all15 clean full points. Use the singleton, the double child and either cost3 child. The gap cost3 extension gives three different actual points outside all full columns, for18 total. Both private realizations of the selected cost3 child are covered by that argument.

#### I: gap2222 and one full root11112

Keep the ten clean points and four singleton points in the exceptional full root. The actual outside-full-columns parts of the four gap fibres each have size at most2, and every pair has union at least3 by the two-small-fibres argument. Small-set Hall gives four different actual gap points. They contribute at most4 to any column, and lie outside the full columns. Total14+4=18.

#### J: gap2223 and three clean full roots

Keep all15 clean full points. Apply the two-small-fibres argument to the three cost2 gap children; their outside-full-columns actual sets have size at most2 and pair union at least3. Choose three different representatives by Hall. Ignore the cost3 child. Total18.

### Uniform law and scope

Every case supplies at least18 actual points with different five-children, different seven-leaves, and at most five points in each seven-column. Select18 and put uniform mass1/18 on them. First-five root cylinders also have at most five points because their children are distinct. Thus

    q5,q7,q35 <=5/18,
    q25,q49,q175,q245,q1225 <=1/18.

The complete ordered-LCM bound is

    Gamma_1225 <=1+(3+3+9)5/18+(5+5+15+15+25)/18
               =79/9 <9.

The selected subset need not preserve literal product blocking. The law is supported on one actual F, not independently selected marginals. Therefore the cut69/63 case of the report449 source theorem is closed by these ordinary arguments; no unrestricted odd-cover conclusion follows.

### Actual mincut69 control

The same verifier constructs104 literal actual points. Full-root fibres are the five public leaves in column0 plus their own distinct private leaf in columns1,2,3. The gap zero child has the same five public leaves; the other three gap children have respectively private leaves {0,1,2}, {2,3,4}, {0,3,4} in column4.

The seven projection is25 actual leaves in five columns of five. All480 selected-pair and10000 original-five-tree tests pass. All295 network forward capacities and node balances are checked. The exact maxflow and returned dual cut equal69; its split is top0, private48, public21, bridge0. The selected18-point actual law has all1767 cylinder readouts at the stated caps and ordered-LCM envelope79/9. The run passes10812 explicit checks under `python3 -I -S -B -O`.

The [exact results](../../frontier/cover-geometry/height_two_cut69_private_law.json) retain the exhaustive profiles, actual source, returned cut and selected law. The finite controls verify classification and one source; the ten-case actual-support argument supplies the universal step. No original odd-covering realization or outside-cofactor lift is asserted.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut69_private_law.py
```

## A partial-full-root70/63 profile has an eighteen-point private law

Retain the literal height-two occupancy4555 source and tree premises of447.
Suppose it admits a cut with all four root nodes source-side, active child
counts(4,4,5,5), common-tree cost R=3/9, and total unweighted private cost
Z=21. The four-active full root may be any full root, with any one of its
five children inactive. The cut has numerator

    7+7*3+2*21=70.

For this entire cut-profile family, an actual uniform eighteen-point law
satisfies

    Gamma_1225(nu)<=79/9<9.                            (PF1)

This includes both common antichains of cost3/9 and arbitrary actual
fibres at the inactive child. It does not classify every cut70 source.
The cut need not be a minimum cut for the support extraction to apply.

### Sorting determines the private cut leaves

Name the gap root a, the partially active full root b, and the other full
roots c,d. Let p_r be the sum of the least q_r active-child private costs,
where q=(2,3,3,3). The pair/subset cut inequalities give p_r+p_s>=6.
The sorting lower bounds for total costs at these roots are respectively

    f_a(p)=p+2 ceil(p/2),
    f_b(p)=p+ceil(p/3),
    f_c(p)=f_d(p)=p+2 ceil(p/3).

If the least p-value is t<=2, the following lower bounds result by giving
every other root at least6-t. They cover every root that can attain the
minimum; no assumption about tied minima is needed.

| Root attaining t | t=0 | t=1 | t=2 |
| --- | ---: | ---: | ---: |
| a | 28 | 28 | 26 |
| b | 32 | 31 | 27 |
| c or d | 30 | 30 | 26 |

All exceed21. When every p-value is at least3, the lower bounds sum to
7+4+5+5=21, and each strictly increases if its p-value increases.
Consequently p=(3,3,3,3), with no private-cost slack, including under the
inactive child. Equality forces the sorted active-child costs

    a:1222,  b:1111,  c:11111,  d:11111.               (PF2)

All these private cuts consist of depth-two leaves: a first-prefix edge
has unweighted cost3. The common antichain is either one whole column or
three leaves. Write its union as P. For every active child e its actual
fibre obeys F_e subset P union S_e, where S_e is its one- or two-leaf
private candidate set. These candidates must still be shown actual.

### Actualness and column separation use only active children

Choose any three children at c and any three at d. Their actual
projection contains a ternary-seven tree. In the whole-column case its
six singleton candidates must all be distinct and actual outside P,
supplying three leaves in each of two further columns. In the three-leaf
case there are at most nine candidates altogether, so all nine are
distinct and actual and form exactly three columns of three leaves.
Each private singleton is actual in its own child: no other selected
fibre can contain that distinct point outside P.

Exchange one chosen c-child while fixing the other two and the d-triple.
Removing the old candidate leaves a unique deficient column, which the
new candidate must fill. All five c-singletons therefore share one
column and are distinct. The same holds at d; their columns differ.
In the three-public-leaf case P must now form the third column itself.

Apply the same argument to triples among the four active b-children,
paired separately with c and d. Four children suffice for the exchange:
any two have two other children that can be held fixed. This gives four
distinct actual b-leaves in a third private column. The inactive child
is never used. Unlike a fully active source, its arbitrary fibre means
the three-public-leaf cut cannot be excluded using the standalone tree.

At a let its candidate sets be {z},E1,E2,E3 with each |Ei|=2. Pair its
singleton child and an Ei-child with a full-root triple. The same
saturation argument makes z and both Ei points actual at their own
children, distinct and outside P. They share one private column, because
the other private column is already filled by the full-root triple.
Repeating with b,c,d separates this gap column from all three other
private columns. In particular z is outside each Ei.

Pairing any two Ei-children with a full-root triple requires
|Ei union Ej|>=3. The three two-sets satisfy Hall: single sets have size2,
any pair has union at least3, and their total union has size at least3.
Choose three distinct representatives, one from each Ei, and retain z.
A triangle of two-sets is allowed; no stronger four-representative
condition is imposed on these three sets.

This constructs18 actual points, one per active child, in four distinct
private columns with root totals4,4,5,5. Their full49 leaves are all
distinct. Uniform mass gives the nonunit caps

    q5,q7,q35<=5/18,
    q25,q49,q175,q245,q1225<=1/18.

The complete81 ordered-LCM pairs, for arbitrary independent original
phases, give 1+(15*5+65)/18=79/9. This proves(PF1); the private subsupport
is not asserted to retain the original blocking premises.

### An actual minimum-cut70 source

Use points(r,c,g,h), meaning x5=r+5c and x7=g+7h. Let
C0={(0,h):0<=h<5}. At the gap root put

    F00=C0 union{(4,0)},
    F01=C0 union{(4,1),(4,2)},
    F02=C0 union{(4,2),(4,3)},
    F03=C0 union{(4,3),(4,4)}.

At root1 take F1c=C0 union{(1,c)} for c<4 and F14 to be all49 leaves.
At roots2,3 take Frc=C0 union{(r,c)} for c=0,...,4. Root4 is empty.
There are160 actual child-labelled points. Every required pair/subset
projection contains a ternary tree; the rich inactive child also supplies
the standalone five-ary tree. Common column0 meets every occupied child.

The explicit cut uses the root1/child4 edge7, common column0 of cost21,
and21 private leaf edges of cost2. Its cost70 is matched by an integral
actual flow. The [exact program](../../frontier/cover-geometry/height_two_cut70_partial_root.py)
and [results](../../frontier/cover-geometry/height_two_cut70_partial_root.json)
retain that positive bridge flow and the explicit cut, check all1303
network capacities and conservation,480 pair/subset tests,10000 literal
product tests,1767 cylinders and81 ordered-LCM terms. They also check
all455 triples of distinct two-sets on six leaves up to child permutation,
which include the triangle case in the Hall step.

The law uses(r,c,4,c) for r=0,c<4 and(r,c,r,c) for the other active
children. All18 points are actual and have the stated caps. The example
certifies nonvacuity of this finite source class, without claiming it
comes from an original odd whole cover or supplies an outside-cofactor
lift. The general profile conclusion rests on the preceding proof;
these checks are not Lean verification.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut70_partial_root.py
```

## Every cut70 source admits one actual law below nine

Retain the original literal4555 source hypotheses and the standalone five-ary seven-tree. If the actual-child network has minimum cut70 in raw capacity units, there is one probability on its actual points, chosen before all numerical phases, such that

    Gamma_1225(nu)<=643/72=9-5/72<9.                    (C70)

No root/column incidence bound or seven-side omission is required. This closes the entire numerical70 stratum at the fixed1225 head. It supplies neither an original odd-cover realization nor a common lift through outside cofactors. The proof below is ordinary mathematics, not new Lean verification.

### Canonical cuts and the complete list of necessary profiles

Use the bridge-free prefix normalization of[447](447-strict-child-cut-surplus-and-arithmetic-boundaries.md). A bridge has capacity126, so none crosses a70 cut. Choose a node-minimal minimum cut. At root r let n_r be its occupied child count and q_r=n_r-2. If its root is sink-side, all its private descendants may be put sink-side; record a_r=0. Otherwise let a_r be its source-side children. If a_r<q_r, its outgoing child edges cost at least3*7=21. Moving the whole private root subtree sink-side replaces these and any further private cut cost by the single source edge21. It does not increase the cut and strictly decreases its source-side nodes, contradicting the choice. Thus

    a_0 in{0,2,3,4},    a_r in{0,3,4,5} for r=1,2,3.

Similarly an active child never has private cut cost at least8: moving its private subtree sink-side would replace that cost by its child edge7. Write its unweighted private cost as z_rc, so its raw cost is2z_rc; then0<=z_rc<=3.

Let T be the sum of3 for each inactive root and n_r-a_r for each active root. Write the public antichain cost as7k and the total private cost as2Z. Exact cut equality is

    7(T+k)+2Z=70.                                    (C71)

For an active root r let p_r be the least sum of q_r private costs. For k<=8, every pair of active roots satisfies

    p_r+p_s>=9-k.

This follows by selecting their cheapest legal child subsets and applying literal ternary-tree blocking to the common and private covering prefixes. If a sorted list has length a, least-q sum p and integer entries, its total is at least

    f_(a,q)(p)=p+(a-q)*ceil(p/q).

The q-th entry is at least ceil(p/q); a balanced first-q list attains this lower bound. At k=0 every active child's private cost is positive, since its actual fibre is nonempty and no public cut covers it. Under full activity, the public and private prefixes cover the entire standalone25-leaf tree. Its uniform law has prefix mass at most(3/5)3^(-B), so k+Z>=15.

These finite integer conditions leave exactly14 labelled profiles. Up to permutations of the three full roots they form six families:

| Family | Active child counts | T | k | Z |
| --- | --- | ---: | ---: | ---: |
| A | Exactly one root, fully active |9|1|0|
| B | (3,5,5,5) |1|3|21|
| C | (4,4,5,5) |1|3|21|
| D | (3,5,5,5) or(4,4,5,5) |1|9|0|
| E | (4,5,5,5) |0|0|35|
| F | (4,5,5,5) |0|4|21|

The counts by family are4,1,3,4,1,1, respectively. This is a list of necessary cut profiles; it does not assert that every profile is realizable. The exact enumeration of the stated finite domains is included in the control below. There is no two- or three-active-root survivor. The fully active k=10,Z=0 candidate fails k+Z>=15.

For B the sorted private shapes are

    033/11111/11111/11111,
    122/11111/11111/11112,
    123/11111/11111/11111,
    222/11111/11111/11111.

C is exactly the previously proved1222/1111/11111/11111 case. E has the unique shape2222/12222/12222/12222. F has the nine shapes treated individually below. These shape lists use0<=z_rc<=3, the exact totalZ and all pair inequalities; they retain the gap root and only identify permutations of equal full-root roles.

### Family A: one active root and a punctured-tree law

The entire active root projects onto a single public leaf y, since k=1 and Z=0. Ignore that root for the law construction. At any other root s, choose any q_s of its occupied children and pair them with a legal subset at the active root. Their actual union contains a ternary seven-tree. If this tree omits y, all nine leaves come from the selected children at s. Otherwise its other eight leaves do. Select the uniform law on those nine or eight actual leaves, lifting each to an actual selected child. It has first-seven column mass at most3/8 and full-seven leaf mass at most1/8.

Average over all q_s-subsets at s. A fixed child occurs with probability q_s/n_s<=3/5, and even when the conditional law depends on the selected subset, its point or column mass is bounded by that law's total or corresponding marginal. Finally mix the three remaining root laws equally. In divisor order(1,5,7,25,35,49,175,245,1225), one obtains the simultaneous caps

    (1,1/3,3/8,1/5,1/8,1/8,3/40,1/24,1/40).

Their complete81-pair numerical LCM envelope is33/4<9. The cut-active root receives no mass; all selected points still belong to the unchanged actual source.

### Family D: a fixed three-branch public support

Here T=1,k=9,Z=0, so all active fibres lie in the public antichain P of cost9 leaf units. Any legal pair of active-root child restrictions has a ternary tree in P. Each of its three first-seven branches costs at least3 to cover, by either a whole-column edge or three leaves. Thus the first such tree exhausts the cut: P consists of three fixed branches, each represented by its whole-column edge or exactly three public leaves. Every later legal root pair must have at least three actual leaves in each of these same branches.

Fix a complete choice of child restrictions and one of the three branches. Treat its actual root/leaf incidences as four rows. Every pair of rows supports a law with leaf cap1/3. The m=4,q=2,depth-one instance of[443](443-one-supported-law-couples-rows-and-tree-prefixes.md) therefore supplies one actual law with root cap1/3, leaf cap1/3 and joint root/leaf cap1/6. This uses one flow; separate pair witnesses are feasibility premises, not independently pasted measures.

Lift its atoms to selected actual children, average over all complete independent child restrictions, and mix the three branch laws with weight1/3. Let delta=max_r q_r/a_r. The same law has caps

    (1,1/3,1/3,delta/3,1/9,1/9,delta/9,1/18,delta/18),

and hence

    Gamma_1225(nu)<=(97+85*delta)/18.

For active counts(3,5,5,5), delta=2/3 and the bound is461/54. For(4,4,5,5), delta=3/4 and it is643/72. The inactive child remains in the source and receives zero probability; no inheritance of blocking after deletion is assumed.

### Family E is impossible

With k=0 every private cut is a finite leaf cut. In the unique shape, every gap child has two candidates; at a full root there is one singleton and four double children. Select any two gap children and the full singleton together with any two full doubles. There are at most2+2+1+2+2=9 candidate occurrences. A ternary tree forces all nine labels distinct, actual at their owners, and a seven-column count vector with entries only0 or3.

Let a_i and b_j be the column-count vectors of gap and full-root double sets, and e the singleton's unit vector. Every selected vector

    a_i+a_i'+e+b_j+b_j'

has all entries in{0,3}. Exchange one full double while holding the other and both gap children fixed. The difference b_j-b_j' has coordinates between-2 and2 but divisible by3, so is zero. There are four doubles, so a distinct fixed partner can always be chosen. All full-double vectors equal b. The same exchange makes all gap vectors equal a. Thus2a+e+2b has entries0 or3. Away from the coordinate of e its entries are even, hence zero. Both a and b, each of total2, must then be concentrated at e, giving value9 there instead of3. This contradiction excludes E.

### Family B: the four partial-gap actual-support arguments

The common cut has cost3: its support P is either one whole first-seven column G or three finite public leaves. The gap has three active occupied children and one inactive occupied child. Each full root has five active children. A private cost1 or2 child has respectively one or two candidate leaves; cost3 is either three candidate leaves or one whole private column. Only the containment

    actual fibre at an active child <= P union its private cut support

is assumed. No private candidate is presumed actual. The inactive child's actual fibre is unrestricted and will receive zero mass. A selected pair means any two active gap children against any three active full-root children, or two full-root triples. These are legal restrictions of the original literal blocker.

#### Common clean-root consequence

Two clean full roots of shape11111 each supply triples of singleton candidates. Their selected pair lies in P plus six singleton candidates.

If P is a whole column G, the ternary tree must use G: outside it there are at most six candidates. The other two branches require all six candidates to be distinct, outside G, and actual in their own selected children. Their column-count vector has entries0 or3. Exchange one selected singleton while fixing the other five. The vector changes by the difference of two unit vectors and must stay divisible by3 coordinatewise, so the exchanged singleton has the same first-seven column. Any two of the five children can be exchanged while keeping two others fixed. Thus every clean root's five singleton candidates lie in one column H, are actual at their own children, and are pairwise distinct. Columns of different clean roots are distinct and avoid G.

If P consists of three leaves, each pair test has at most nine candidate occurrences, so a ternary tree forces all nine to be distinct and actual. The same one-child exchange locks each clean root's singleton family into its own column. The two clean columns must differ; the remaining three public leaves must form a third column G. Thus the preceding conclusion also holds in this case. The public leaves are used only where actually available; no assertion is made that they occur in every child.

There are at least two clean roots in every Family B shape. With three clean roots obtain three distinct columns H1,H2,H3, five actual singleton points in each.

#### A finite-four-candidate observation

Suppose a fixed selection of gap children has at most four private candidate leaves C, and is tested against a clean full-root triple in H_j. Its actual projection lies in G union H_j union C. A ternary tree must use G, since outside G there are at most7 candidates. It must also use H_j, since C alone has fewer than6 leaves. Its third branch is therefore a column K_j outside G,H_j containing at least three actual leaves contributed by the selected gap children.

There is at most one column containing three of the at-most-four candidate labels in C. Therefore K_j is independent of j. Testing all clean columns proves that the selected gap fibres have an actual union of at least three leaves outside G and every clean H_j. This is an actual-union conclusion; for double sets it does not say that every candidate is actual at its owner.

If the selected gap private costs are1 and2, all three private candidates are forced distinct and actual at their own children, in this one column K.

#### Shape033 /11111 /11111 /11111

The zero-cost gap child has a nonempty actual fibre contained in G, so select any one of its actual public leaves.

Test that zero child together with either cost3 child against a clean triple. If cost3 consists of three leaves, the six candidates outside G must give the other two full branches, forcing all three private leaves actual at that child in one column outside G and the clean column. Testing the three clean roots excludes all H1,H2,H3. If cost3 is a whole column L, a third branch forces L different from G and each tested H_j and forces at least three actual leaves of the cost3 child in L.

Each of the two cost3 children thus offers at least three actual leaves outside G,H1,H2,H3. Choose different representatives from the two children. Together with the public point at the zero child and the fifteen clean points, this gives eighteen child-distinct and leaf-distinct points. The clean columns each have five points, G has one, and every other column has at most two.

#### Shape123 /11111 /11111 /11111

Write z for the singleton candidate, E for the double candidates, and W for the cost3 support. The singleton/double pair tested against all three clean roots has exactly three outside candidates. Consequently z and both E leaves are actual, distinct, and in a common K outside G,H1,H2,H3.

For the singleton/cost3 pair, first suppose W consists of three leaves. Apply the finite-four-candidate observation to{z} union W. Its unique three-leaf column is outside G and all H_j. If it is K, the cost3 child supplies at least two actual leaves distinct from z. If it differs from K, that child supplies all three of its actual leaves in the new column.

If W is a whole column L, a ternary tree on G,H_j,L and the lone z must use G,H_j,L. Thus L avoids G and every H_j. If z lies in L, that child supplies at least two actual leaves different from z; otherwise it supplies at least three actual leaves in L.

Select z, any one actual E leaf, and an actual W leaf avoiding those two. The W choice exists by the preceding two-or-three-leaf count. Adding the fifteen clean points gives eighteen, with at most three points in any new column and five in each clean column.

#### Shape222 /11111 /11111 /11111

For gap child i let U_i be its ACTUAL leaves outside G,H1,H2,H3. Each U_i has size at most2 by cut containment. For each pair(i,j), the finite-four-candidate observation gives

    |U_i union U_j| >=3.

These three sets have an SDR: each is nonempty (the other has size<=2), every pair union has size>=3, and the union of all three has size>=3. These are exactly Hall's conditions for three sets. Choose one distinct actual representative at each gap child. Together with fifteen clean points this gives eighteen; at most three selected gap points occur in a new column.

#### Shape122 /11111 /11111 /11112

Let H1,H2 be the clean columns. At the exceptional full root let w1,...,w4 denote its four singleton candidates and D its double candidates. Testing three of the singleton children against either clean triple gives the same tight-six argument. Their four candidates are distinct and actual in one common column H3 outside G,H1,H2.

The double child supplies a NEW actual H3 leaf outside all four w's. To prove this, test the double child together with any two singleton children against a clean triple. Outside G there are at most seven candidates, so the tree uses G. Outside the clean column, the two w's and D have at most four leaves and must supply the third branch. Because D has only two candidate leaves, that branch must be H3 and D must supply an actual H3 leaf outside the selected w pair. If all actual D leaves in H3 belonged to{w1,...,w4}, their set has size<=2 and could be included in a selected pair, contradicting the preceding conclusion. Thus the new leaf exists. Retain it and all four w's, giving five exceptional-root points in H3.

At the gap let z be the singleton and E1,E2 its double sets. Testing z+Ei against a clean triple forces all three candidates distinct and actual in one column K outside G and the tested H_j. The shared z fixes K for both double children. Testing against the other clean root excludes its column. Testing against an exceptional triple of singleton w's excludes H3. Hence z,E1,E2 all lie in K outside G,H1,H2,H3, and neither E_i contains z. Select z and distinct representatives from E1 and E2; each has two leaves, so this is possible.

The ten clean points, five exceptional points and three gap points are the required eighteen, with column counts5,5,5,3.


### Family F: all nine fully active cost4 shapes

#### Premises and containment

All19 occupied children are active. Each child's actual fibre is contained in the public cut support P together with its own private cut support C_e. A cost1 or2 means respectively one or two candidate leaf labels; a cost3 is either three candidate leaves or an entire private column. Candidate labels need not initially be actual at their owners. Every occupied child has at least one actual point, including a zero-cost child whose fibre is contained in P.

A legal root pair means any two actual children at the gap root and/or any three at a full root. Its actual seven projection contains a ternary depth-two tree. Separately, the full source projection contains a five-ary tree with25 distinct leaves. The public antichain of cost4 is either four leaf labels or one entire column G plus a leaf y outside G.

#### Four public leaves

If all cost3 cuts are finite leaf cuts, there are exactly4+21=25 public/private leaf occurrences. Their union contains the entire source projection, which contains a25-leaf tree. Thus all25 occurrences are distinct labels and all occur in the actual projection; their union is exactly that standalone tree.

Each private candidate is actual at its OWN child: it is not a public label, and by distinctness no other child's private set contains it, so containment prevents any other child from supplying its actual occurrence. Select one from every nonzero-cost child, and omit one child if there are19 nonzero children. Every listed shape has at least18 nonzero children. The selected labels are distinct and inherit the standalone tree's five-per-column cap.

Only1111/11113/11111^2 and1113/11111^3 can have a whole private column. Ignore that single owner child. For any gap singleton pair and full-root singleton triple, the public4 plus private2+3 candidates give exactly9. Literal blocking forces nine distinct actual labels and a ternary tree. Its column-count vector has every coordinate0 or3. Exchanging singleton children shows all gap singleton labels lie in one column K and each full-root singleton family in one column H_r. The public vector must be1 in K and3 in one other column G, distinct from K and every H_r. Different full-root H_r are distinct: selecting singleton triples at two of them otherwise gives only two possible three-leaf branches, their common H and public G; the other public column K has only one leaf.

Every selected singleton is actual at its own child by the exact9 saturation. Select4+4+5+5=18 in the first shape, and3+5+5+5=18 in the second. The whole-column owner is not selected. All selected leaves are distinct, and the largest column occupancy is5.

#### Public support P=G union{y}: two reusable actual-incidence facts

##### Tight-six and singleton locking

If a legal pair has exactly five finite private candidates, its projection outside G is contained in y plus those five labels. A ternary tree cannot avoid G, because only six candidate leaves lie outside it. It must use exactly six DISTINCT ACTUAL outside leaves, grouped as two columns of three. Therefore all private candidates lie outside G, are distinct from y and one another, and are actual at their respective selected owners. The leaf y is also actual somewhere in the selected union; no particular owner for y is assumed.

A fixed legal two-candidate selection against every singleton triple of a clean11111 root locks that clean root into one column H. Indeed exchanges of one singleton in the triple change a0-or3 column-count vector by a difference of two unit vectors; the difference must be zero. Every singleton lies in H, and all five labels are distinct and actual. The fixed two candidates together with y consequently fill one other column K=col(y), distinct from H and G.

Once y and a fixed two-singleton gap pair have been locked in one column K by a clean-root test, a family of at least three singleton children tested against that pair in a tight-six test likewise forms a distinct actual branch in one column H. The three K labels already exhaust one branch, so the selected singleton triple supplies the other branch even when there are exactly three singleton children and no exchange within that family is available. Different full-root singleton families occupy different columns: pair two singleton triples; if their columns agreed, P supplies only G as a second full branch and the lone y cannot supply a third. This observation also separates a three-leaf exceptional branch from any clean branch.

##### A double child supplies an actual new leaf in a locked exceptional column

Suppose a full root has at least three singleton labels W in a locked column H, and a double child E. Suppose the gap root has two singleton labels z,z' with y,z,z' distinct in K!=H. Select any two singleton children w,w' at that full root together with E, and pair them with the gap children z,z'.

Outside G the candidate set is K's three labels{y,z,z'}, H's two labels{w,w'}, and E's at most two candidates. There are at most seven labels, so a ternary tree must use G. No column other than K or H can acquire three leaves from the at most two E candidates. Hence the actual E fibre must supply an H-leaf outside{w,w'}.

This holds for every pair from W. If all actual H-leaves of E belonged to W, there would be at most two of them and some pair W would contain them all, a contradiction. Therefore E supplies an ACTUAL H-leaf outside the entire singleton family W. This proves the new point at its own double-child owner; it does not assume every cut candidate is actual.

#### The nine G+y cases

Clean means a11111 full root. All mentioned disjointness and ownership come from the preceding tight tests.

##### F1:0222 /11111^3

Pair the zero gap child and any double E_i with a clean triple. Tight-six forces E_i to be two distinct actual leaves in K=col(y), disjoint from y; it locks the three clean families in distinct other columns H_1,H_2,H_3. Choose all15 clean points. Choose one actual point from the zero child (it lies in G or is y), and one point from each of two double children, choosing the two representatives distinct. This is possible even if their two-leaf sets coincide. The public point cannot equal any of those private labels. There are18 points; K receives at most3 and each H_r receives5.

##### F2:1111 /01222 /11111^2

Gap singleton pairs against clean triples lock all four gap labels in K and the ten clean labels in two other columns. Let w be the exceptional singleton and E_i its three doubles. Pair(z,z') at the gap with(zero,w,E_i) at the exceptional root. Tight-six puts w and both actual leaves of E_i into another column H, with w outside every E_i. This column differs from either clean H_r, as otherwise pairing(zero,w,E_i) with that clean triple would have only two full branches.

Any two E_i,E_j have union of size at least3. Otherwise they are the same two-leaf set; the exceptional selection(zero,E_i,E_j), paired with a gap singleton pair, would have only two H-leaves and could not provide the third ternary branch. The three two-element actual sets therefore have a three-element transversal by Hall (each singleton subfamily has2, each pair at least3, and the full union at least3). Select the4 gap points, w plus those3 representatives, and10 clean points. Column occupancies are4,4,5,5.

##### F3:1111 /11113 /11111^2

Use only the4 exceptional singleton children and ignore its cost3 owner, whether that owner is finite or a whole column. Gap pairs against singleton triples establish actual distinct columns K,H,H_1,H_2. Select4 gap,4 exceptional and10 clean points. Occupancies4,4,5,5.

##### F4:1111 /11122 /11111^2

The4 gap singletons,3 exceptional singletons and10 clean points are locked and actual. By the actual-new-leaf fact, either exceptional double supplies an actual leaf in its exceptional H outside all3 singleton labels. Select that one double point as well. Counts4+4+10=18; occupancies4,4,5,5.

##### F5:1111 /11112 /11112 /11111

The four gap labels, both exceptional singleton families of size4, and the5 clean labels occupy four distinct columns. Apply the actual-new-leaf fact to either exceptional double, using its four singleton siblings. Add its new actual leaf. Counts4+5+4+5=18, with maximum column count5.

##### F6:1112 /11112 /11111^2

Ignore the gap double. Use its3 singleton labels, the exceptional4 singleton labels, and10 clean points. The actual-new-leaf fact applies to the exceptional double using any two of the3 gap singletons; select its new exceptional-column leaf. Counts3+5+10=18; column counts3,5,5,5.

##### F7:1113 /11111^3

Ignore the gap cost3 owner. Its3 singleton labels and the15 clean labels are actual and locked in distinct columns. They give18 points with counts3,5,5,5.

##### F8:1122 /11111^3

The only gap singleton pair z1,z2 against clean triples locks{y,z1,z2} in K and all15 clean points in three other columns H_1,H_2,H_3. The two gap doubles contribute at most4 further candidate labels. Any column outside{G,K,H_1,H_2,H_3} consequently has at most4 actual leaves, so cannot be a branch of the standalone FIVE-ary tree. That tree must use these five named columns, in particular K, and K must have at least5 actual leaves.

Only y,z1,z2 among the already known labels lie in K. Therefore there is an actual K-leaf outside{y,z1,z2}; containment places it at one of the two double gap children. Select that leaf, z1,z2, and the15 clean points. Counts3,5,5,5. The exclusion of y here is essential to the ownership inference; merely saying “outside{z1,z2}” would not suffice.

##### F9:1222 /01111 /11111^2

Let w1,...,w4 be the exceptional singleton labels and e0 its zero child. Pair(e0,wj,wk) with any clean triple. Tight-six and singleton locking force ALL of y,w1,...,w4 into one column H, with five distinct actual labels. The two clean families lie in distinct columns H_1,H_2 outside H and G.

This directly forces col(y)=col(w_j). An alternative with different columns for y and the w_j would violate these clean-root tests.

For each gap double E_i, pair the gap singleton z together with E_i against(e0,wj,wk). Tight-six already contains the full H branch{y,wj,wk}, so z and E_i's two labels form an actual three-leaf branch in one column L!=H,G. Its label is fixed by z, and it differs from H_1,H_2: otherwise pairing(z,E_i) against the corresponding clean triple would again provide only two full branches. In particular z is distinct from all E_i leaves.

Select w1,...,w4 and ANY actual point of e0. That point lies in G or equals y, so it is distinct from every private selected point and increases the H count to at most5. Select z and distinct representatives from any two double children; two sets of size2 always admit two distinct representatives, even if equal. Add all10 clean points. Counts5+3+10=18; no column exceeds5.


### One chosen law and the worst-case bound

Family C was proved in the preceding partial-full-root section. Every B,C,F case selects18 actual points with distinct second-five children, distinct full seven leaves and at most5 points in a first-seven column. A first-five root also contains at most5 because it has at most5 children. The uniform law on these18 points has caps5/18 at divisors5,7,35 and1/18 at25,49,175,245,1225. For independently chosen numerical phases, every ordered divisor pair is incompatible or intersects in its numerical LCM cylinder. The81-pair bound is

    1+(3+3+9)*5/18+(5+5+15+15+25)/18=79/9.

The selection is made once before phases are tested. Its support is not asserted to be a blocker. Combining these cases with A,D and the impossibility of E gives

    max(33/4,461/54,643/72,79/9)=643/72,

which proves(C70). In particular the standalone-tree premise is used on the full active source in Family F, including the missing-leaf step of F8; it is never applied to only the active part of a partial profile.

### Exact profile and actual-source controls

The [profile enumerator](../../frontier/cover-geometry/height_two_cut70_profiles.py) and [exact classification](../../frontier/cover-geometry/height_two_cut70_profiles.json) exhaust the canonical active vectors, public costs and sorted private costs described above. They recover14 labelled profiles and4,1,1,9 private shapes for B,C,E,F. This finite enumeration establishes those integer lists; it does not replace any actual-point implication.

The [public-profile constructor](../../frontier/cover-geometry/height_two_cut70_public_profiles.py) and [results](../../frontier/cover-geometry/height_two_cut70_public_profiles.json) provide four Family A sources and both Family D sources, all with matching explicit cut and actual flow of70. At the D sources every active root has only two actual leaves in each public branch; thus the branch construction uses the pairwise coupling premise and does not assume a ternary tree at each individual root. Their measured LCM envelopes are33/4,461/54 and643/72, respectively.

The [B/F actual-source constructor](../../frontier/cover-geometry/height_two_cut70_actual_sources.py) and [results](../../frontier/cover-geometry/height_two_cut70_actual_sources.json) cover all four B and nine G+y F shapes, with four further cost3 whole-column variants:17 templates. Every template has actual minimum cut70, the prescribed70 cut, and an actual18-point child/leaf/column selection with LCM upper79/9. The selector uses the actual incidence graph; its success on these templates does not substitute for the universal incidence proofs above. These controls do not classify realizability of the four-public-leaf F subcases.

Each of the23 new actual sources passes all480 selected pair tests,10000 complete literal product tests and the standalone tree check. Each network witness checks every edge capacity and conservation. Each chosen law checks all1767 numerical cylinders and81 ordered LCM pairs under one probability. These are exact standard-library computations with checks active under Python-O. They neither certify unrestricted odd noncoverage nor constitute Lean verification.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut70_profiles.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut70_public_profiles.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut70_actual_sources.py
```

## At78/63 the choice of maximum flow matters

All raw quantities in this section are integer units1/63 unless otherwise
stated. A literal68-point source realizes both a bad and a good maximum
flow at78/63. The example refutes the assertion that every maximum flow
works. The subsequent mixture criterion is conditional; the forced-block
source below refutes its universal rerouting premise.

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

The conditional mixture statement remains valid, but its uniform supplier
premise is false: the next actual source forces an old625 block to retain
mass21 under every value78 flow. An off-block actual point therefore does
not certify a route that lowers the block, even when such points are
present at every child. The saturated-block transport theorem below gives a uniform good-law
construction by redistributing mass inside the blocks while controlling
the original coherent charges.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut78_flow_choice.py
```

## An actual cut78 source forces the old bad block to stay full

There is a literal source satisfying all the stated tree and network
premises for which one maximum flow has625 coherent centres, but EVERY
value78 flow keeps their root/column block at mass21. This includes
fractional flows and holds before imposing any additional old-child caps.
Thus the proposed uniform requirement to lower that block to20 is false.
The same source still has a good law, obtained by changing its distribution
inside the forced block. All amounts in this section are units1/63.

### One actual source and its fixed capacity obstruction

Use full roots0,1,2, gap root3, and empty root4. Every actual child has all
seven leaves of common column A=0. Additional private support is:

| root | additional actual points |
|---|---|
| 0 | every child has all seven leaves of column G=1 |
| 1 | child c has leaf c in column B=2; child0 also has leaf5 there |
| 2 | child c has leaf c in column C=3 |
| 3 | children0,1,2,3 have leaves `{0}`,`{1,2}`,`{3,4}`,`{5,6}` in column D=4 |

This is one186-point source:133 common-A points,35 root0/G points, and18
other private points. Every full-root triple contributes A and at least
three leaves of its own private column; every gap pair contributes A
and at least three D leaves. Any required pair therefore supplies a
ternary seven-tree. The five projected columns have7,7,6,5,7 leaves, so a
standalone five-ary tree exists.

For ANY feasible flow, partition its actual bridge masses into these
three disjoint parts. Their masses satisfy

    mass(root0/G)<=21,
    mass(A)<=21,
    mass(other18 points)<=18*2=36.

The first bound is the source-to-root0 capacity, the second the public-A
column capacity, and the third the eighteen private leaf capacities.
They sum to78. Every flow of value78 must attain all three bounds,
including mass(root0/G)=21. This argument applies to real-valued flows;
it does not infer a universal property from two enumerated flows.

There is also an explicit cut of this capacity: its forward edges are
the source-to-root0 edge, the public-A column edge, and the eighteen
private leaf edges. Its35 actual root0/A bridges cross backwards. Flow-cut
equality at value78 forces zero on these bridges and saturation on all
forward cut edges, giving the same forced-block conclusion.

### The premise is triggered by an actual625 maximum flow

Place the earlier matrix T on root0/G:

    (2,2,2,0,0,0,0),
    (2,2,1,1,0,0,0),
    (2,0,0,0,0,0,0),
    (1,2,1,1,0,0,0),
    (0,1,1,0,0,0,0).

Place mass2 on each of the other18 private points. On common A put
masses2 at root1 children/leaves(0,0),(1,1),(2,2),(3,3), plus mass1 at
(0,5); masses2 at root2 children/leaves(0,0),(1,1),(2,2),(3,3), plus mass1
at(4,4); and masses2 and1 at gap child0 leaves0 and6. These common masses
total21. The resulting root totals are21,21,19,17 and the flow value is78.
Every private, public and child capacity is satisfied, so the preceding
upper bound proves it is a maximum flow.

At numerical centres(x mod25,y mod49)=(0,1),(0,8),(5,1),(5,8), the
nonunit cylinder masses in order(5,7,25,35,49,175,245,1225) are

    (21,21,6,21,7,6,7,2).

The corresponding coherent charge is625. The existing full-phase
bound LC2 gives the matching upper bound, so this bad normalized law has
exact Gamma703/78>9. Its separate cylinder-maxima envelope is630,
which alone is weaker and is not used to claim exactness.

These centres are all in root0/G. Since EVERY value78 flow keeps that
block at21, no same-source maximum flow can meet the conditional
rerouting hypothesis mass(root0/G)<=20. The failure holds even though
every root0 child has actual points outside the block, in A.

### A good law redistributes mass inside the same forced block

Keep every non-root0 atom unchanged. Within root0/G put mass1 at

    (c,h)=(c,c+d mod7),   c=0,...,4, d=0,...,3,

and one additional unit at(4,1). These are21 distinct actual points.
The child totals are4,4,4,4,5 and the G leaf totals are2,3,3,4,4,3,2.
All network capacities still hold, and the block total remains21.

This one law has numerical cylinder maxima

    (q5,q7,q25,q35,q49,q175,q245,q1225)
       <=(21,21,7,21,6,5,4,2)/78.

The complete81-pair LCM envelope is therefore

    Gamma<=1+(3*21+3*21+5*7+9*21+5*6+15*5+15*4+25*2)/78
          =643/78<9.

This is an upper bound, not a claim that one phase layout attains643/78.
It uses the measured caps and all original numerical pairs directly;
it does not need the earlier noncoherent622 estimate.

The [forced-block verifier](../../frontier/cover-geometry/height_two_cut78_forced_block.py)
and [exact source, flow and cut data](../../frontier/cover-geometry/height_two_cut78_forced_block.json)
check23734 exact conditions, including480 selected pair tests,600 literal
triple tests,10000 complete literal five-tree tests,1329 network edge
capacities and both flow conservation equations, the cut and its backwards
bridges,1767 numerical cylinders per flow,1225 coherent centres per flow,
and both complete81-pair envelopes. The universal impossibility of
reducing this block is the capacity-partition or flow-cut argument above.

This refutes the specific uniform block-reduction supplier. It preserves
the conditional mixture lemma and the goal of selecting a good law; it
is not an original odd-covering counterexample or a new Lean result.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut78_forced_block.py
```

## Saturated-block transport closes every78/63 source

For any actual-child network in this literal height-two carrier admitting
an integral flow of value78, there is one rational feasible flow of the
same value and on the same positive actual support whose normalized law
satisfies

    Gamma_1225(nu)<=701/78=9-1/78<9.                  (SB1)

An integral flow exists whenever the integer-capacity network has a flow
of at least78; one may reduce an integral larger flow to that value.
Consequently every minimum-cut78/63 source in the stated class is
controlled. The construction keeps the masses of all first-five/first-seven
blocks fixed. It therefore also applies to the preceding forced-block
source, for which moving mass out of its old625 block is impossible.
All raw quantities below are in units1/63.

### A rational transport lemma on any five-by-seven support

Let E be any subset of five rows times seven columns. Suppose E supports
an integral nonnegative matrix of total21, with row sums at most6,
column sums at most7, and each entry at most2. There is a rational matrix
x on E, with the same total and all the same caps, such that for EVERY
cell(i,j), including cells outside E with x_ij=0,

    20 r_i(x)+20 c_j(x)+25 x_ij<=308.                (SB2)

Every positive entry of the chosen initial matrix remains positive. If
E is its positive support, the resulting positive support is exactly E.
Only containment in E is claimed when additional zero edges are allowed.

Use the bipartite network with source-row capacity6, allowed cell-edge
capacity2, and column-sink capacity7. For each allowed cell(i,j), there
is an integral value21 flow in which at least one of its row, column or
cell bounds is not saturated.

If the network admits a value22 flow, take an integral one. When its
(i,j) entry is positive, subtract one unit along that cell's complete
source-to-sink path. The new entry is at most1. If that entry is zero,
subtract a unit along any positive path instead. This supplies the
required value21 flow.

It remains to treat maximum flow21. Suppose all integral maximum flows
saturate source-row i, cell(i,j), and column j-sink. Each of these three
arcs then belongs to some capacity21 minimum cut: reduce its capacity by
one. The new integer network cannot have an integral value21 flow, so
integrality and max-flow/min-cut supply a cut of new capacity at most20.
Its old capacity is at least21 and changes by at most one. Hence its
old capacity is exactly21 and the reduced arc crosses it.

Let R,M,C be source sides of minimum cuts crossing these three arcs,
respectively. Minimum cuts are closed under intersection and union:
cut submodularity bounds the sum of the intersection and union capacities
by42, while each is at least21. Therefore

    S0=R intersect M,   S1=M,   S2=M union C

form an increasing chain of minimum cuts. Row i is absent from S0 and
present in S1; column j is absent from S1 and present in S2.

For a cut let a count rows outside its source side, b columns inside,
and c allowed cell edges crossing outwards. Its capacity is6a+7b+2c.
The complete nonnegative integer solutions to capacity21 are

    (a,b,c)=(0,3,0),(0,1,7),(1,1,4),(2,1,1).

S0 omits row i, so it has exactly one column. S1 has an outward cell
edge, so it also has exactly one column. Their nested source sides make
this the same column. S2 contains that column and also j. It must therefore
have three columns, all five rows, and no outward cell edge. Thus the
ENTIRE allowed support E lies in those three columns.

Passing from S0 to S1 adds at least row i and no columns. Every added
row has at most two allowed neighbors outside their shared column.
Its change to the cut capacity is therefore at most

    -6+2*2=-2.

The cut strictly decreases, contradicting that both cuts have capacity21.
This proves the required alternative flow for each cell.

Take the initial integral matrix x0. Call a cell bad if its row sum is6,
column sum7, and entry2. At most three rows and three columns can be
saturated because the total is21, so there are k<=9 bad cells. For each,
select an integral value21 alternative where that cell is not bad.
Average these k matrices and x0 with equal weights1/(k+1).

For any integral feasible matrix the expression in(SB2) is at most310.
At a nonbad cell it is at most290: at least one integer coordinate drops
by one, saving at least20. Every cell is nonbad in at least one matrix
in the average, either x0 or its designated alternative. Thus

    20 r_i+20 c_j+25 x_ij<=310-20/(k+1)<=308.

The average preserves nonnegativity, total, capacities and support;
including x0 with positive weight preserves its positive entries.
This proves(SB2). Four-child roots are covered by padding with a zero
fifth row.

Fractional output is essential for this lemma. On K_(4,3), any integral
value21 matrix has all three columns at7 and at least one row at6.
That row's three entries are all2, so it has bad cells. An explicit
feasible integer matrix has row triples(2,2,2),(1,2,2),(2,1,2),(2,2,1).
The rational uniform value7/4 on the twelve edges is feasible and has
no such obstruction. This integer counterexample does not contradict
(SB2), whose output is a rational mixture.

### Replace disjoint saturated blocks in the same actual flow

Start with an integral value78 flow lambda. For each first-five root r
and first-seven column g write a_r,b_g,d_rg for its root, column and
joint masses. They are integers at most21. Call(r,g) full when

    a_r=b_g=d_rg=21.

Such a block contains all mass of its root and all mass of its column;
every other block in that root or column has mass zero. Full blocks
therefore have distinct root labels and distinct column labels. There
are at most three, since four would require total84>78.

Inside one full block, index its actual positive bridge masses by the
five-child digit c and the fine seven-digit h. They form a matrix of
total21. Its row bound6 is the private first-prefix capacity; its column
bound7 is the public leaf capacity; its entry bound2 is the private leaf
capacity. Its support consists entirely of actual source points.
Apply(SB2) using that original positive support.

Replace all full blocks by their resulting rational matrices. Their
roots and public columns are disjoint, and each full block already
isolates all flow at its root and column. The replacements consequently
respect every root, child, private-prefix, public-prefix and actual-bridge
capacity simultaneously. The child cap7 is implied by the stronger
within-block row cap6. All other masses are unchanged. Each coarse joint
mass d_rg and the root and column masses remain unchanged integers.
This is one explicitly defined actual flow, not a combination of
incompatible separately optimized marginal laws.

### Every coherent and noncoherent phase layout is controlled

At a coherent centre in a full block, the root and column isolation
gives u5=u7=u35=21, u25=u175=r_i, u49=u245=c_j and u1225=x_ij. Hence
its raw nonunit charge is

    K=315+20 r_i+20 c_j+25 x_ij<=623.

At a centre outside the full blocks write

    (a,b,c,d,e,f,g,h)=(u5,u7,u25,u35,u49,u175,u245,u1225).

The actual set-inclusion inequality c+d<=a+f still holds for a rational
measure. Consequently

    K=3a+3b+5c+9d+5e+15f+15g+25h
      <=8a+3b+4d+20f+5e+15g+25h.

The eight unchanged network caps bound the latter expression by625.
Since a,b,d are integers and are not all21 at this centre, one is at
most20, saving at least3. Thus K<=622. This step uses integrality only
of the unchanged coarse masses, not of the new fine entries.

Finally, the earlier noncoherent LC2 bound622 was proved from rational
cylinder caps and incompatibility of numerical queries; it does not
require integral flows. Every noncoherent layout therefore also has
charge at most622 after replacement. Dividing the one repaired flow
by78 and restoring the unit-unit term gives(SB1). No phase choice enters
the construction of the law.

### Exact support construction and actual-flow controls

The [saturated-block constructor](../../frontier/cover-geometry/height_two_saturated_block_transport.py)
and [exact results](../../frontier/cover-geometry/height_two_saturated_block_transport.json)
implement the proof by trying a one-unit reduction of the row, column
or cell capacity for each initial bad cell, finding the alternative
integer21 flow, and averaging at most ten flows. All matrix entries and
final checks use exact rational arithmetic.

The controls enumerate all216 labelled three-column supports in which
each column has at least four neighbors among five rows. They also test
5000 supports generated with fixed seed20260927;3692 admit value21.
These finite checks do not supply the universal quantifier: the minimum-cut
argument above does. The program checks(SB2) at all35 cells, including
zero cells outside the support.

It also repairs the bad maximum flows of both actual examples above,
using their original positive supports. It checks every network-capacity
family, unchanged coarse blocks, every one of the1225 coherent centres,
and the resulting all-layout bound using LC2 for noncoherent layouts.
The actual-source controls are not asserted to be original odd-cover
residuals. No Lean formalization is claimed.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_saturated_block_transport.py
```

## Sharp mass21 transport and the remaining cut77 interface

All masses here are raw integer-capacity units. The sharp support theorem below improves the full-block estimate and reduces the general cut77 problem to near-full mass20 blocks. It does not settle every cut77 source or the original odd-covering problem.

Let E be any subset of {0,...,4} x {0,...,6} admitting a nonnegative matrix of total21, row sums at most6, column sums at most7 and entries at most2. There is a rational matrix x supported in E, with the same total and caps, such that at every cell, including absent cells,

    S_ij = 20 r_i + 20 c_j + 25 x_ij <=295.

For a particular feasible initial x0 with rational entries, apply the construction on E=supp(x0). One can retain exactly that positive support by taking (3/4)x+(1/4)x0. Then every score is at most1195/4=298.75<301. Thus a full isolated coarse block has coherent raw charge at most315+1195/4=2455/4=613.75<616 after positive-support-preserving replacement. If mere support containment suffices, the sharper bound is610.

### Minimal support reduction

Delete edges while preserving mass21 feasibility, producing inclusion-minimal E'. Let M be its integer maximum flow for source-row capacities6, entry capacities2 and column-sink capacities7. Removing any edge reduces maxflow to at most20. Removing a cap2 edge reduces maxflow by at most2, so M is21 or22.

If M=22, take any22 flow. For each edge, its removal leaves a mincut of capacity20; that cut had capacity22 before removal, and hence the edge is saturated at2 in every22 flow. Therefore E' has11 edges and every row and column has degree at most3. Give each edge mass21/11. This is feasible, and at a positive cell

    S <= (20*3+20*3+25)*21/11=3045/11<295.

At a zero cell the bound is smaller.

### The M=21 cut cases

Choose a minimum cut. Let I be its inside rows, J its inside columns, and let a=5-|I|, b=|J|, c=|E' intersect(I x J-complement)|. Its capacity is6a+7b+2c=21, whose possibilities are

    (a,b,c)=(0,3,0),(0,1,7),(1,1,4),(2,1,1).

A maximum21 flow saturates all forward cut arcs and has zero backward cut flow. Thus outside rows have mass6, inside columns have mass7, crossing entries are2, and outside-row/inside-column entries are0. The last type is impossible: its only inside column would need7 from only3 inside rows, each entry at most2.

#### Type(0,3,0)

All edges lie in3 columns. Each column has at least4 neighbors. Distribute7 uniformly on its neighbors. Then every row is at most21/4, every entry at most7/4, and every score is at most

    20*(21/4)+20*7+25*(7/4)=1155/4<295.

#### Type(0,1,7)

Let j* be the sole inside column and d_i the row's degree among the7 crossing edges. Keep these edges at2. We have sum d_i=7 and d_i<=3. Rows with d_i=3 cannot contribute to j*. The set H of rows adjacent to j* with d_i<=2 has cardinal k>=4, since j* must receive7 with entry cap2.

Outside column totals are unchanged even integers at most7, hence at most6. Every outside-column positive score is therefore at most20*6+20*6+25*2=290. Any zero-cell score is at most260. It remains to allocate j*.

If k=5, give every row7/5. Row caps hold and the j* score is at most

    20*(4+7/5)+140+25*(7/5)=283.

If k=4, let h be the number of its rows with d_i=2. Since sum d_i=7, h<=3. If h=0, give all four rows7/4; their scores are at most20*(2+7/4)+140+25*(7/4)<295. If1<=h<=3, give each of the4-h low-degree rows2 and each high-degree row

    v=(7-2*(4-h))/h=2-1/h.

The masses sum7, and1<=v<=5/3<2, so all entry and row caps hold. Low-degree row scores are at most270. High-degree row scores are

    20*(4+v)+140+25v=220+45v<=295.

#### Type(1,1,4)

Let r* be the outside row and j* the inside column. Choose an integral maximum21 flow and keep its outside-row flows v_j, of total6, and the4 crossing edges at2. The four inside rows all have an allowed j* edge, because each contributes at least1 to its required mass7. Their crossing degrees d_i are at most2 and sum4. Let h count the rows of degree2; h is0,1 or2.

If h=0, put7/4 at each inside-row/j* entry. Every inside row has mass at most15/4. Its j* score is at most1035/4; a crossing-entry score is at most265.

If h=1, put1 in the high row's j* entry and2 in the other three. The high row has mass5 and the others at most4. Their j* scores are at most270, and crossing scores at most20*5+20*7+50=290.

If h=2, the degree vector is(2,2,0,0) up to permutation. Put3/2 at each high row's j* entry and2 at each zero-degree row. High rows have mass11/2. Every outside column meets at most2 crossing edges; with v_j<=2 its total is at most6. Crossing scores are at most110+120+50=280; high-row j* scores are at most220+45*(3/2)=575/2. Other j* scores are at most230.

For the unchanged outside row, let D_j be a column's crossing degree. Its column total is2D_j+v_j<=7. If D_j<=2, its score is at most120+120+50=290. If D_j=3, then v_j<=1 and its score is at most120+140+25=285. Zero-cell scores are at most260. Hence this entire cut type has bound290.

All constructions preserve total21, the original caps, and support containment. This proves295 in every case. Mixing with x0 as stated follows because every original feasible score is at most310.

### The constant295 is sharp over arbitrary allowed supports

Use columns A,B,C,D,E and four nonempty rows, with support

    row0: A,B,C
    row1: A,D
    row2: empty
    row3: A,B,E
    row4: A,B,E.

A cut through column A (capacity7) and the seven other entry edges (total capacity14) has capacity21. Every mass21 flow therefore puts2 on those seven non-A edges and7 on column A. Write v_i=x_iA. Since v_1<=2,

    v_0+v_3+v_4=7-v_1>=5.

At least one of these three v_i is at least5/3. That row has four units outside A, so its cell score at A is220+45v_i>=295. Conversely v_1=2 and v_0=v_3=v_4=5/3 gives a feasible matrix with maximum score295; B has total6, C and D total2, E total4. This cut and pigeonhole argument proves that the universal minimax constant is exactly295.

### Same-source cut77 reduction

Start from any integral actual flow of value77 with the eight raw caps. Replace each isolated full21 coarse block by the295 construction, retaining positive support through a quarter-original mixture. All coarse root masses a, coarse column masses b, and coarse block masses d remain unchanged integers; every fine cap remains valid. This is one flow of total77.

### Noncoherent layouts: the old622 bound can be sharpened below616

If the six labels with positive first5 exponent disagree, at least5 unordered pairs are incompatible; each loses at least4 from the independent630 envelope. The same holds on the7-axis. Such layouts have charge at most610.

Assume both first digits agree. Let A,B,E be the full5 digits selected by labels25,175,1225, and C,D,F the full7 digits selected by49,245,1225.

If A differs from B, their ordered pair contribution loses12, since lcm(25,175)=175 and its raw cap is6. At least one of A or B differs from E, losing another4 from its pair with1225. Thus the charge is at most614. If C differs from D, the same argument loses14+4 and gives612. If A=B but E differs, AND C=D but F differs, four distinct incompatible pairs with1225 lose16 in total, giving614.

Consequently only two exceptional noncoherent patterns need extra work: A=B=E, C=D different from F; or A=B different from E, C=D=F.

### One inequality controls both exceptional patterns

Write x_ij for the fine matrix in their common coarse root/column block. Write z_i for row-i mass in that root outside the column, and y_j for fine-column-j mass in that column outside the root. Let

    a=d+sum z_i,  b=d+sum y_j,  f=sum_j x_Aj,
    g=sum_i x_iC, e=g+y_C,  x=x_AC.

The displaced top cell x' is x_AF in the first pattern and x_EC in the second. On the coarse block the query count is4+2[ i=A ]+2[ j=C ]+[displaced top cell]. Outside it the count is2+[i=A] or2+[j=C]. Thus the exact nonunit charge is

    K=3a+3b+9d+20f+20g+8x+13x'+5z_A+5y_C.

Using z_A<=a-d and e=g+y_C gives

    K <= 8a+7b+20f+20e+8x+13x' -4(b-d)-15y_C
      <= 617-8(21-a)-7(21-b)-4(b-d).

The last line uses f<=6, e<=7, x,x'<=2. This inequality is valid for a rational measure; only the next step uses unchanged coarse integrality.

If the block is not full, either a<=20, b<=20, or a=b=21 and d<=20. The displayed bound is respectively at most609,610, or613.

If the block is full, a=b=d=21 and z=y=0. The repair supplies S_AC=20f+20g+25x<=L=1195/4. Therefore

    K=315+20f+20g+8x+13x'
      <=315+(8/25)L+(17/25)*260+26
      =3067/5=613.4.

Hence EVERY noncoherent layout of the repaired flow has K<=614<616. No new cross-block rerouting is needed for this part.

### What coherent layouts still require

In a full block the repair gives K<=2455/4=613.75. Outside them the inclusion bound and coarse caps show:

* If a<=20, then d<=20, so the Report449 slack estimate gives K<=625-8-4=613.
* If d<=19, the original coherent formula gives K<=3a+3b+9d+315<=612.
* If a=21,d=20, then b is20 or21 unless the preceding case applies.

Thus the only remaining coherent obstructions have a=21, d=20 and b in{20,21}. For the initial integer flow, the only actual charges>=616 are621,618,616. Specifically f6,e7,g7,x2 are all forced; for b21, child mass7 gives621 and child mass6 gives616; for b20, child mass7 gives618. This classification of exact fine masses is for the initial integer flow, whereas the coarse exclusions above remain valid after the disjoint full-block replacements.

### The mass20 transport analogue is false on arbitrary positive support

Use5 rows and7 columns. The positive support and unique mass20 feasible matrix are

    row0: A2 B2 C2
    row1: A2 B2
    row2: A2 B2
    row3: empty
    row4: A1 B1 D2 E2.

All row caps are6, column caps7, entry caps2. A cut consists of the source-to-row4 arc of capacity6 and the seven entry arcs incident with rows0,1,2 of total capacity14. Therefore every feasible mass20 flow forces row4 mass6 and all those seven entries2. Columns A and B already receive6 from the first three rows, so row4 contributes at most1 to each; D and E allow at most2 each. Achieving row4 mass6 forces exactly(1,1,2,2). The flow is unique even among rational flows.

At cells(row0,A) and(row0,B), r=6,c=7,x=2, giving S=310. No supported redistribution lowers it. One flagged column cap6 does not help: flag an unused column. Thus no universal same-positive-support mass20 lemma with S<300 can hold, even though the mass21 analogue has bound295.

This is a local counterexample to an algorithmic premise, not a full literal-source realization, not an obstruction to using previously zero actual edges, and not a counterexample to existence of a good law. For a=21,d20, outside root mass1 implies row allowances7-row_outside>=6, so row capacities do not resolve this example. For b21, one flagged fine column has cap6, but it can be the unused column just described. To advance general cut77, an argument must use additional actual source points beyond the chosen positive support, change coarse block masses through a joint reroute, or construct a different law from the source's literal tree/blocking premises. Merely keeping all coarse masses and replacing arbitrary positive20 blocks cannot supply the needed theorem.

### Two direct consumers of the same repaired law

For a value77 initial flow with no coarse root/column block satisfying
root mass21 and joint mass20, every coherent centre is at most2455/4
or613 and every noncoherent layout is at most614. Hence the same law gives

    Gamma_1225(nu)<=1+614/77=691/77<9.                 (SH1)

This is a sufficient source-flow condition, not a claim that every
cut77 source supplies such a flow. A block of joint mass20 has column
mass20 or21 automatically.

For value78, all nonfull coherent centres have K<=621: if a<=20 then
K<=613; if d<=19 then K<=612; otherwise a=21,d=20,b<=21, and the
original coherent formula gives K<=306+315=621. This uses only the
unchanged coarse integrality and the fine caps. Full blocks have
K<=2455/4, and the same noncoherent proof gives K<=614. Consequently the
uniform cut78 bound in(SB1) sharpens to

    Gamma_1225(nu)<=1+621/78=233/26<9.                (SH2)

All these bounds use one repaired rational flow selected before the
phase queries, preserve its original positive actual support and all
network capacities, and retain every original query label.

### Exact constructive controls

The [sharp-block constructor](../../frontier/cover-geometry/height_two_sharp_block_transport.py)
and [results](../../frontier/cover-geometry/height_two_sharp_block_transport.json)
implement support deletion, integral minimum-cut classification, the
explicit rational allocations, and the quarter-original mixture. They
reuse the existing Dinic implementation. Each output is checked at all35
cells, including absent cells, with total and every capacity checked
exactly. The controls exercise all four branches by explicit supports,
216 three-column supports, and96 further fixed-seed supports:316 cases,
of which286 are feasible. Each feasible case also has a separate run
restricted to its initial positive support. The degree/allocation checks
cover275 eligible-row cases for cut017 and19 degree cases for cut114.
The sharp295 witness and unique20 counterexample retain exact matrices
and their cut arguments. Finite controls do not replace the universal
minimum-cut proof, realize a full original odd cover, or prove the
missing near-block supplier. No Lean verification is claimed.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_sharp_block_transport.py
```

## Mass20 transport from an actual neighborhood condition

The arbitrary-support obstruction above disappears under the following additional support condition. This is an ordinary mathematical theorem, not Lean verification. It treats an optional column of capacity6 explicitly because one outside atom can reserve one unit of a public-leaf budget.

Let E be an allowed subset of a5x7 array. Every row has capacity6, every entry capacity2, and every column capacity7 except for at most one flagged column F, whose capacity is6. Assume E supports a nonnegative rational matrix of total20 and that every three distinct rows have at least three neighbors in their union.

Then there is a rational matrix y supported in E, with the same capacities and total, such that at every one of the35 cells

    S_ij(y) = 20 r_i(y) + 20 c_j(y) + 25 y_ij <= 6200/21 < 300.

No total-neighborhood>=5 assumption is needed. Zero entries have their literal score20r_i+20c_j and are included in the bound.

### Maxflow at least21

The standard transportation network has source->row capacity6, allowed row->column capacity2, and column->sink capacity7 or6 as specified. Its maximum M is integral. If M>=21, choose an integral flow of mass21 and multiply it by20/21. Before scaling every score is at most310; afterwards it is at most6200/21. Scaling also preserves the flagged column cap6. This branch does not use the sharp295 mass21 theorem.

### Maxflow exactly20 and cut types

For a minimum cut let I be the source-side rows, J the source-side columns, a=5-|I|, b the number of ordinary columns in J, f in{0,1} indicate whether F belongs to J, and c count allowed edges from I to the complement of J. In the unflagged problem set f=0. Then

    6a + 7b + 6f + 2c = 20.

Cut equality implies that all outside rows have mass6, all inside columns are filled to their specified capacity, all c crossing entries equal2, and all backward outside-row->inside-column entries are zero. Feasibility therefore remains a concrete constraint in every case below.

For f=0 the possible(a,b,c) are

    (0,0,10), (1,0,7), (2,0,4), (3,0,1), (0,2,3), (1,2,0).

For f=1 they are

    (0,0,7), (1,0,4), (2,0,1), (0,2,0).

We construct a bound at most1175/4 in every feasible case.

### No inside flagged column: f=0

Type(1,2,0) is impossible: the four inside rows have all their neighbors in the two inside columns, contradicting the three-row hypothesis.

For type(0,2,3), the three crossing edges meet three different rows. Otherwise at least three rows have all their neighbors in the two inside columns. Keep those entries2. Each of the two inside columns has at least four neighbors because it must carry7, and distributing7 uniformly among its neighbors gives entries<=7/4. Every row mass is at most2+2*(7/4)=11/2. Every outside column has mass at most6, including F if present. Scores in the two inside columns are at most

    20*(11/2) + 20*7 + 25*(7/4) = 1175/4.

Outside positive cells have score<=280; zero cells have score<=250.

For type(0,0,10), every allowed entry is2. Every column mass is even and at most its capacity7 or6, hence is at most6. All scores are<=290.

For type(1,0,7), four inside rows carry seven forced entries2 and one outside row v has mass6. Write d_i for inside row degrees and D_j for crossing column degrees. Feasibility gives d_i<=3 and D_j<=3.

If no crossing edge has both d_i=3 and D_j=3, keep any feasible flow. Inside rows with d_i<=2 have mass<=4 and score<=270. A row with d_i=3 meets only columns D_j<=2, whose total mass after the outside row is at most6, giving score<=290. In the outside row a column with D_j<=2 gives score<=290; a column with D_j=3 allows an outside entry t<=1 and its score is240+45t<=285. Zero cells have score<=260.

Otherwise let a degree3 inside row h meet a degree3 column A. A is the only degree3 crossing column: if B were another, h must meet B (otherwise its other two edges together with the six incidences in A,B exceed the seven edges). Then h's third edge is the only edge outside A,B; the other three inside rows have all neighbors in A,B, a contradiction. The outside row can send at most1 to A and at most2 elsewhere; its total6 implies at least three neighbors other than A. Send2 to any three such neighbors and zero elsewhere. Now every column has mass<=6, so all scores are<=290. This obeys F's cap whether or not F=A.

For type(2,0,4), the three inside rows have four forced entries. Their neighborhood has size>=3, so crossing column degrees are<=2 with at most one degree2 column. The two outside rows need total12. Clip each residual column allowance to4, which is valid because there are only two outside rows. All allowances are4 except that a degree2 ordinary column has allowance3, or a degree2 flagged column has allowance2. There is at most one exceptional odd allowance3. Lower it to2 if present. All other network capacities are even; a cut using the odd arc previously had odd capacity at least13, so after this reduction it still has capacity at least12. All other cuts are unchanged. Divide the resulting even capacities by2, take an integral maxflow of value6, and multiply by2. Restoring the inside entries gives column masses<=6 and scores<=290.

For type(3,0,1), one inside entry2 is in a column A, and the three outside rows need total18. Clip their residual column allowances to6. If A is ordinary its allowance is5; lower it to4. This preserves value18 since cuts using this sole odd arc previously had odd capacity at least19. If A=F its allowance is already4, so no reduction is needed. Every other allowance is6. Divide capacities by2, take an integral flow of value9, and multiply by2. Restoring the forced entry gives all columns mass<=6 and all scores<=290.

### Inside flagged column: f=1

For type(0,0,7), the flagged column has mass6 and every ordinary-column entry is one of the seven forced entries2. All ordinary column masses are even and<=7, hence<=6. The original feasible flow already has all scores<=290.

For type(1,0,4), four inside rows have four crossing edges. No ordinary column A can contain three of them: the fourth edge is in a different column (four entries in A would violate its capacity), and after excluding its row the other three inside rows have all neighbors in{F,A}, a contradiction. Thus every crossing column has degree<=2. The single outside row adds at most2 per ordinary column, giving total mass<=6; F already has mass6. The original feasible flow has all scores<=290.

Type(2,0,1) is impossible: the three inside rows have all neighbors in F and the column of the unique crossing edge.

For type(0,2,0), all allowed edges lie in two ordinary columns and F, which require masses7,7,6. The ordinary columns each have at least four neighbors, and F at least three. Distribute each column uniformly over all its neighbors. The resulting entries are respectively<=7/4,7/4,2, and every row has mass<=11/2. Ordinary-column scores are<=1175/4 and flagged-column scores<=280. Zero scores are<=250.

This completes all minimum-cut cases. Since1175/4<6200/21, the stated uniform bound follows.

### Positive support and the local consumer

The theorem constructs a matrix supported in E. If x is any original mass20 law with the same caps, take

    z = (7/8)y + (1/8)x.

Its score is at most

    (7/8)*(6200/21) + (1/8)*310 = 3565/12 < 300.

Every originally positive entry stays positive. If the initial positive support is exactly E, the mixture's positive support is also exactly E.

For a consumer whose coherent raw charge is a fixed coarse contribution at most316 plus this local score, the resulting charge is at most

    316 + 3565/12 = 7357/12 < 614.

That last implication assumes the consumer has proved both the coarse contribution bound and the three-row neighborhood condition on the actual allowed support E. This local theorem does not establish either premise for general literal sources and does not by itself prove general cut77 or an outside-cofactor lifting.

### Stronger unflagged bound

If every column has capacity7, the M>=21 branch can use the sharp295 theorem above before scaling. Its score is then at most5900/21<1175/4. All M=20 cases already have bound1175/4. Thus the unflagged conclusion strengthens to

    S_ij<=1175/4.                                      (NT1)

A quarter-original mixture has score at most

    (3/4)*(1175/4)+(1/4)*310=4765/16<300.

The total number of neighboring columns need not be at least five; the stated three-row condition suffices. The universal proofs are the cut arguments, not the finite controls below.

### Exact construction controls

The [mass20 constructor](../../frontier/cover-geometry/height_two_mass20_three_row_transport.py) and [exact results](../../frontier/cover-geometry/height_two_mass20_three_row_transport.json) implement the optional-flag theorem with bound6200/21 and its7/8-new plus1/8-original mixture. They reuse the existing integral-flow code. This program keeps the uniform6200/21 branch even when no column is flagged. The stronger unflagged theorem(NT1) is the mathematical combination above with the preceding sharp295 construction; the program does not provide a separate entry point implementing that improvement.

There are72 named fixture runs and864 bounded two-column controls. The fixtures exercise all eight feasible minimum-cut20 types and the maximum-at-least21 branch. In eight complete-support runs, a supplied everywhere-positive rational mass20 law is retained as the actual1/8 term; every mixed entry is checked against that supplied input. The program also rejects an invalid supplied initial total. All checks remain active under Python-O and use exact rational arithmetic. These are constructor controls, not an exhaustive classification of actual sources.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_mass20_three_row_transport.py
```

## A cut77 bridge for one common column and four exclusive private columns

This restricted actual-source theorem uses the preceding coarse-block reduction, the sharp295 mass21 theorem and(NT1). It does not establish general cut77.

### Exact source class and conclusion

Let the four occupied five-roots have occupancy(5,5,5,4), with the fifth root empty. Fix five distinct first-seven columns P,G_0,G_1,G_2,G_3. Suppose EVERY actual fibre under root r is contained in P union G_r. There can be arbitrary actual leaves and child incidences within those two columns. Assume literal ternary-five/five-ary-seven product blocking. The usual standalone-five-tree premise may also be imposed, but the deduction below needs only blocking and an integral actual flow of value77 under Report449's network caps.

Then the source supports one rational probability with

    Gamma_1225 <= 691/77 <9.

This statement concerns the specified actual two-column-per-root support restriction. In particular, it does not replace the general source's pairwise joint tree premise by an unjustified individual-root tree premise.

### How the joint tree tests yield a private-neighborhood condition

Put q_r=3 at full roots and2 at the gap root. Select any q_r actual children at r and q_s actual children at another occupied root s. By adjoining empty children and the empty root, literal product blocking says that their combined seven projection contains a ternary height-two tree.

That projection is contained in only the three distinct columns P,G_r,G_s. Hence each of these three columns must contain at least three distinct leaves. Only root r can supply G_r in this selected pair, so the selected q_r children have at least three private neighbors in G_r. Since the selections were arbitrary, this holds for every q_r-child selection at every root.

At a full root it is exactly the three-row-neighborhood property. At the gap root pad by its empty fifth row: every set of three literal rows includes at least two actual rows, which already supply at least three private neighbors. Thus every private block, padded to5x7, has the needed property.

The conclusion about the COMMON column is different: its three leaves may be supplied jointly by the two selected roots. Nothing here asserts that each root separately has three common leaves.

### First remove a near-full common block using an actual edge

Start with an integral flow of total77. A coherent near20 obstruction has root mass a=21, block mass d=20 and public column mass b in{20,21}. If this block is in P, its root r has total private mass1 in G_r.

Its20 common units occupy at least four child rows, because each child/common prefix has cap6. At most two rows have no private neighbor, by the three-row-neighborhood property. Therefore there is a common-positive child c with an actual private edge(c,h) in G_r. Choose one unit from any positive common atom in that child and move it to this actual private point.

Every constraint remains valid:

* The child and root totals are unchanged.
* The private G_r row and entry had at most1 before the move, since the entire private block had mass1. They become at most2, within row6 and entry2.
* No other root uses G_r. Its column and leaf totals had at most1 and become at most2, within21 and7.
* All common-column and common-leaf totals only decrease.

The common block drops20 to19 and the private block grows1 to2. No other block increases. There is at most one20 common block because the whole common column has mass at most21. Thus after at most one such integral move, no common near20 obstruction remains. A common full21 block is instead covered by the existing mass21 repair.

### Repair the remaining disjoint blocks

Every remaining near20 obstruction lies in a private G_r. Its public column is exclusive to r, hence b=d=20. Its root has a=21, so the total mass outside the block is1; in the integral flow each child has outside mass at most1. Consequently the within-block row cap6 is sufficient for the full child cap7.

Apply the three-row-neighborhood mass20 lemma on the ENTIRE actual private support, allowing previously unused actual edges. It produces S_ij=20r_i+20c_j+25x_ij<=1175/4. If desired, mix one quarter of the initial block with three quarters of this matrix to retain all initially positive entries. The bound becomes4765/16.

There is no flagged column cap: no other root uses G_r. The replacement preserves total20, all local caps and every coarse block mass. Different private blocks use distinct roots and public columns, so the changes are jointly feasible. Full21 blocks are repaired by the sharp295 construction, with quarter-original mixture giving S<=1195/4. Their isolated roots/columns are disjoint from the near20 blocks.

For a private near20 coherent centre, the exact formula has constant303 and only the external child contribution z_i<=1:

    K=303+20r_i+20c_j+25x_ij+5z_i
      <=308+4765/16=9693/16<614.

Full21 blocks have K<=2455/4<614. All remaining coherent blocks have the previously established coarse exclusion bound at most613. The sharpened noncoherent argument in Report449 gives K<=614 for every other phase layout, since coarse masses remain integral and full21 blocks retain their fine score bound.

Thus the ONE repaired flow has every nonunit layout charge at most614. Normalizing its unchanged total77 and restoring the unit contribution proves Gamma<=1+614/77=691/77.

### Exact control and remaining boundary

The164-point actual source constructed below lies in this class. It passes480 selected tests,10000 literal product tests and the standalone tree predicate, has a matching actual flow/cut77, and forces root0/G_0 to remain20 under EVERY maximum flow. Its three-row private-neighborhood property therefore does not force internal mass21. Direct fractional replacement nevertheless gives the stronger complete-LCM upper674/77.

For a general source, other roots may use G_r, and root r may have actual points outside P union G_r. Then the private-neighborhood inference and the simple one-unit transfer above both need new arguments. Neither is supplied by the bare pairwise tree premise alone. The general cut77 near20 problem remains open here.

### General conditional consumer, including a column used by another root

The following consumer does NOT assume the common/private source decomposition. Let F be any actual source admitting an integral value77 flow under the same height-two network caps. Call a coarse root/column block dangerous when its root mass is21, its block mass is20 and its public column mass is20 or21. Assume that, for EVERY dangerous block of this selected integral flow, the block's ENTIRE ACTUAL5x7 support E has at least three neighbors in the union of every three rows. It is enough to verify this property for the dangerous blocks; no such hypothesis is needed for full21 blocks or other blocks.

The mass20 flagged-column extension supplies a rational matrix of total20 on E, row caps6, entry caps2, ordinary column caps7 and, if needed, one designated column cap6, with every local score at most6200/21. The proof is the finite minimum-cut classification for6a+7b+6epsilon+2c=20; when a21 flow exists, scaling it by20/21 already gives6200/21. The preceding proof covers all ten cut types, including both impossible cases; the capacity6 constraint is retained throughout.

For a dangerous block, exactly one unit lies outside the block in its root. Thus each row's external child mass z_i is at most1. Its public column has either zero or one external unit. By integrality, when it has one, that unit lies in a single fine column j*, so the permitted INTERNAL fine-column caps are6 at j* and7 at every other column. This is the precise source of the flagged local constraint.

Use the flagged matrix when necessary, then take7/8 of it plus1/8 of the initial block. This gives

    S_ij <= (7/8)*(6200/21)+(1/8)*310 =3565/12.

It preserves every initially positive entry; it may additionally use previously zero ACTUAL edges. Exact preservation of the initial positive support is not claimed when E is larger.

All dangerous blocks and all full21 blocks have pairwise distinct roots and public columns: two such blocks in the same root or column would have combined mass at least40>21. Replace all of them simultaneously, using the sharp295 quarter-mixture for full21 blocks. Every coarse block total remains unchanged. Every atom outside the replaced blocks stays fixed, including the external unit defining each flag and the external child units. Thus the local allowance calculations remain valid simultaneously; the replacements do not consume one another's reserved external budgets.

At a coherent centre in a dangerous block, let f_i and g_j be its internal row and column masses, x_ij its entry, and z_i,y_j its external row and public-leaf contributions. Its exact charge is

    K =3a+3b+9d+20f_i+20g_j+25x_ij+5z_i+5y_j
      <=316+3565/12=7357/12<614,

because a=21, d=20, b<=21 and0<=z_i,y_j<=1. A full21 centre has K<=2455/4<614. For any other coherent block, either a<=20 (giving K<=613 by the joint slack inequality) or d<=19 (giving K<=612 directly from the original caps). Every noncoherent layout still has K<=614 by the previously established argument: it only uses the retained caps, unchanged integer coarse masses and the full21 local score bound.

Consequently this one rational actual flow gives Gamma<=691/77. The exact remaining structural obligation for arbitrary literal4555 sources is now:

    Find a value77 integral flow whose every dangerous block has the
    actual three-row-neighborhood property, or repair the remaining
    bad-neighborhood blocks by another joint actual-source construction.

The common/private source class proved above supplies one genuine source-domain sufficient condition, after its explicit one-unit transfer removes a dangerous common block. The general literal pair tests alone have not been shown to imply the needed per-block property.


## A literal cut77 source can force a good-neighborhood block to stay20

The following actual source separates three different obligations: filling a block to21, repairing its internal weights, and changing its root mass. Failure of the first does not imply failure of the other two.

Use occupancy(5,5,5,4,0), common first-seven column P=0, and exclusive private columns G_r=r+1. Every occupied child contains all seven leaves in P. The private points are:

* Root0: every child has leaves A=0 and B=1 in G_0; children0,1,2 also have respectively C=2,D=3,E=4.
* Root1: child c has private leaf c, and child0 also has leaf5.
* Root2: child c has private leaf c.
* Root3: its four children have private leaf sets{0},{1,2},{3,4},{5,6}.

There are164 actual points. A network cut consists of P's cap21 arc, the two G_0 public-leaf cap7 arcs for A,B, and21 private-leaf cap2 arcs: the three exceptional G_0 points and the18 private points of the other roots. Its capacity is21+14+42=77. An explicit actual flow achieves77, so this is the minimum cut.

Every maximum flow, including every real-valued one, saturates all these cut arcs and has zero backward cut flow. G_0 is exclusive to root0, so its total mass is forced to

    7+7+2+2+2=20.

Every three root0 children nevertheless have at least three distinct private neighbors, and the union contains five leaves. Thus even this genuine literal source does not allow its internal block to be raised to21. This refutes that particular supplier claim; it does not refute(NT1), which only reallocates mass20.

One integral77 flow has private G_0 row entries(2,2,2),(2,2,2),(1,1,2),(1,1),(1,1), with the third entries in C,D,E. Replace each A/B incidence by7/5 and leave the three exceptional entries2. Keep every outside atom unchanged. This retains exactly the initial43 positive actual atoms. It gives a common law with complete LCM upper674/77<9.

There is also an external integral reroute: move one unit from actual point(0,0,0,0) to already-positive point(2,4,0,4). Root0 falls from21 to20, root2 rises from19 to20, and the G_0 block remains20. The resulting flow has no root21/block20 pair. It therefore meets(SH1) and has an all-layout upper691/77<9, even though its separate-cylinder LCM envelope is9. This source consequently does not obstruct external rerouting.

| One actual law | Maximum coherent raw charge | Nonunit separate-cylinder LCM envelope | Normalized LCM envelope |
| --- | ---: | ---: | ---: |
| Initial integral |618|621|698/77|
| Internal fractional repair |579|597|674/77|
| External integral reroute |610|616|9|

The last column is an upper bound formed from separate cylinder maxima, not a claim that all those maxima are attained by one phase layout. The stronger(SH1) bound for the last row uses the phase-compatibility argument.

The [actual-source control](../../frontier/cover-geometry/height_two_cut77_forced_twenty.py) and [exact data](../../frontier/cover-geometry/height_two_cut77_forced_twenty.json) construct the164 points, check all480 selected pair tests and10000 literal product-blocking tests, the standalone five-tree, every one of1307 network capacities and conservation, all1225 coherent centres, the cut and all three laws. Its minimum-cut argument applies to every maximum flow; the finite flow replay is an existence witness. This is not an original odd covering or a resolution of general cut77.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut77_forced_twenty.py
```

## An actual cut77 source requires a coarse change to repair its bad20 block

This is an ordinary explicit construction with exact standard-library controls, not Lean verification. It is a counterexample to an automatic local condition and to fixed-coarse fine-only repair, not to existence of a good law. The source has three individually robust roots, so the existing three-robust-root theorem already gives a good law independently of the explicit repairs below.

### The68 actual points

Use(r,c,g,h) coordinates, with roots0,1,2 having children0,...,4, root3 children0,...,3 and root4 empty. Let G=1 and let J_c=(0,2,3,4,5)_c. All sets below are literal actual points, not potential prefix leaves.

At root0, the G block has support

    child0: fine leaves0,1,2
    child1: fine leaves0,1
    child2: fine leaves0,1
    child3: empty
    child4: fine leaves0,1,3,4.

Outside G, child0 has(J_0,0), while every child c=1,...,4 has(J_c,h) for h=0,1,2. Root0 therefore has11+1+12=24 points.

At root1, every child c has(J_c,h), h=0,1,2; children0,1,2 additionally have h=3,4 in their respective J_c. Also include(1,0,G,5). Root1 has15+6+1=22 points.

At root2, every child c has(J_c,h), h=0,1,2, giving15 points.

At root3 use only column6, with successive children's fine sets

    {0}, {1,2}, {3,4}, {5,6},

giving7 points. The total is24+22+15+7=68.

### Literal source premises and exact cut77

Each of roots0,1,2 is individually robust. At root1 or2, any three children give three distinct J columns with three leaves each. At root0, a triple omitting child0 does the same; a triple including child0 gets a three-leaf G branch from that child and three-leaf J branches from the other two. Every ternary choice of first roots includes at least one of these three robust roots, since only root3 and the empty root4 lie outside them. Therefore every literal ternary-five tree has a seven projection containing a ternary seven-tree, which meets every five-ary seven-tree.

The standalone five-tree uses columns J_0,J_1,J_2,G,6: root1 supplies five leaves in each of the first three, G has at least five, and column6 has seven.

There is a network cut of capacity

    3*21 + 7*2 =77.

Cut the source edges of roots0,1,2 and the seven private leaf edges of root3. Put all public nodes on the sink side. All other root3 nodes, except its seven actual private leaves, are on the source side; all private nodes at the other roots are on the sink side. No actual bridge crosses forward. The explicit flow below has value77, proving equality and hence minimum cut77.

The [actual bad-neighborhood control](../../frontier/cover-geometry/height_two_cut77_actual_bad_neighborhood.py) and [exact data](../../frontier/cover-geometry/height_two_cut77_actual_bad_neighborhood.json) check all480 pair/subset tests,10000 complete literal product tests, the standalone tree,1211 edge capacities and all-node conservation, and every displayed cut and flow.

### A bad actual near20 block, including its external fine-column flag

In root0/G put the unique20 matrix

    child0: (0:2,1:2,2:2)
    child1: (0:2,1:2)
    child2: (0:2,1:2)
    child3: empty
    child4: (0:1,1:1,3:2,4:2).

Put one unit at(0,0,0,0). Thus root0 has mass21 and child0 has mass7.

At each of roots1 and2, give every h=0,1,2 point in J_c mass2 for c=0,1 and mass1 for c=2,3,4. Each root has mass21. At root1 transfer one unit from(1,0,0,0) to(1,0,G,5), preserving its total and child mass. Put2 on each of the seven root3 points, giving14 there. The total is21+21+21+14=77.

For root0/G the coarse masses are(a,d,b)=(21,20,21). The outside public unit is at fine leaf5, so the local flagged cap6 is at a column unused by this actual G support. Rows1,2,3 have neighborhood exactly{0,1}; the three-row sufficient condition fails on the ENTIRE actual support, not just the current positive flow.

At the centre(r,c,g,h)=(0,0,1,0), or original CRT residue50, the eight cylinder masses are

    (u5,u7,u25,u35,u49,u175,u245,u1225)
       =(21,21,7,20,7,6,7,2).

The coherent nonunit charge is621, so this particular normalized maximum flow has Gamma at least698/77>9. The control computes all1225 coherent centres and finds maximum621; it does not infer its all-layout maximum merely from that enumeration.

### Every fine-only repair at these three coarse masses fails

The local mass20 matrix is unique even among rational flows. A local cut uses the source-to-child4 edge6 and the seven entry edges at children0,1,2 of total14. Equality at20 forces those seven entries2 and child4 mass6. Fine columns0 and1 already receive6 each, so child4's remaining allowances are exactly(1,1,2,2) at its four neighbors. Their sum6 forces every value in the displayed matrix.

Hence every feasible value77 flow on this same ACTUAL source, subject to the same eight network caps and with(a,d,b)=(21,20,21), retains internal row0 mass6, internal fine-column0 mass7 and entry2. At the same fixed coherent centre, with external child/fine-leaf contributions z,y>=0,

    K=3a+3b+9d+(20*6+20*7+25*2)+5z+5y
      =616+5z+5y>=616.

Its normalized Gamma is therefore at least1+616/77=9. This permits arbitrary redistribution elsewhere in the actual source: as long as those three coarse masses stay fixed, no fine-only repair or convex mixture can give the needed strict inequality. Some coarse mass must change. This is stronger than failure of the sufficient three-row criterion.

### Two explicit joint repairs

A two-atom move subtracts1 from(0,0,1,0) and adds1 to(0,0,0,0). The destination rises1 to2; every cap holds. It leaves the root and child masses fixed and changes the dangerous block20 to19 and its public column21 to20. All old positive atoms remain positive. The complete numerical LCM envelope has nonunit value609, so the resulting SAME-SOURCE law satisfies

    Gamma <=1+609/77=98/11<9.

There is also a four-atom cycle preserving every root, every child and every public coarse column mass:

    (0,0,1,0) -=1,     (0,0,0,0) +=1,
    (1,0,0,1) -=1,     (1,0,1,5) +=1.

The first two changes are the same move; the latter two compensate the public column totals through a different actual root. All four points are actual and their resulting masses are1 or2, so positivity and entry caps remain valid. The exact network check verifies the changed fine-leaf and private-prefix budgets as well. The dangerous root0/G block drops20 to19 while a=b=21 stay fixed. Its complete nonunit LCM envelope is612, giving

    Gamma <=1+612/77=689/77<9.

Thus a true joint coarse-block change repairs a literal cut77 example on which every fixed-(a,d,b) fine rearrangement fails. The example already lies in the known three-robust-root good-law class. It does not prove a repair exists for every remaining nonrobust cut77 source, nor does it construct an original odd covering or an outside-cofactor lift.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut77_actual_bad_neighborhood.py
```

## Every cut71 source admits one actual law below nine

Retain the literal4555 source hypotheses, the standalone five-ary seven-tree and the actual-child network at the fixed1225 head. If its minimum cut in raw units is71, there is one probability on the unchanged actual source, chosen before all numerical phases, such that

    Gamma_1225(nu)<=79/9=9-2/9<9.                     (C71-law)

There is no root/column incidence restriction. The result is ordinary mathematics with exact finite controls, not Lean verification. It supplies no common outside-cofactor lift for unrestricted odd covering.

### The complete necessary cut profiles

Use the same node-minimal, bridge-free, prefix-normalized minimum cut as for cut70. Put n=(4,5,5,5), q=(2,3,3,3), and let a_r be the number of active children at root r. Then a_0 is0,2,3 or4; the other a_r are0,3,4 or5. An active child's unweighted private cost z_rc lies in{0,1,2,3}, with raw cost2z_rc. Its private support is empty, a finite set of z_rc leaves, or (only when z_rc=3) one whole column. These are covering candidates; actual incidence at the owner must still be proved.

Write Z_r=sum_c z_rc, Z=sum_r Z_r, let7k be the public prefix cost, and put T=sum_r(3 if a_r=0 else n_r-a_r). Necessary conditions are

    7(T+k)+2Z=71,
    p_r+p_s>=9-k for active root pairs when k<=8,
    p_r=sum of the q_r least private costs at root r.

At k=0 every active private cost is positive. When all children are active, covering the full standalone tree gives k+Z>=15. In addition node minimality gives, at EVERY active root,

    7(n_r-a_r)+2Z_r<21.                              (C71-root)

Indeed moving that entire root subtree sinkward removes all its outgoing child/private cut edges and replaces them by its source edge21. Actual forward bridges are removed, and no new forward actual bridge can appear: the only incoming private-tree edge is the source/root edge. Cost at least21 would contradict either cut minimality or node minimality. This strict root inequality keeps the classification on actual normalized cuts.

Exhausting these finite integer domains leaves ten labelled profiles, or eight rows after permuting the three full roots:

| Active counts | T | k | Z | Labelled multiplicity | Sorted private shapes |
| --- | ---: | ---: | ---: | ---: | ---: |
|0555|3|0|25|1|1|
|2555|2|3|18|1|2|
|3555|1|4|18|1|1|
|4000|9|0|4|1|1|
|4455|1|4|18|3|1|
|4555|0|1|32|1|4|
|4555|0|3|25|1|21|
|4555|0|5|18|1|13|

The finite enumerator establishes this necessary integer list, not realizability. The arguments below retain actual owners and all inactive source fibres. In divisor order(1,5,7,25,35,49,175,245,1225), ordered-LCM multiplicities are(1,3,3,5,9,5,15,15,25). Whenever18 actual points have distinct children and distinct full-seven leaves, with at most5 in each first-seven column, their uniform law has caps

    (1,5/18,5/18,1/18,5/18,1/18,1/18,1/18,1/18),

and hence Gamma<=79/9. This will be the common consumer of the support selections.

### A single active gap root:4000,k=0,Z=4

There is no public cut support. The four active gap children have positive private cost, totaling4, so each has one candidate leaf and its nonempty actual fibre is exactly that singleton. Write its actual point as x_i and its seven leaf as y_i.

If two y_i coincide, fix those two gap children. For any triple of occupied children at another full root, literal blocking provides a ternary seven-tree in the union of the selected full fibres and this one gap leaf. Delete the gap leaf if present. The remaining tree has8 or9 leaves, all actual at selected full children. Uniform mass on those leaves, lifted to actual owners, has seven-column cap3/8 and seven-leaf cap1/8. Average over all ten triples at the full root and then over the three full roots. Each child belongs to3/5 of the triples. The same law has caps

    (1,1/3,3/8,1/5,1/8,1/8,3/40,1/24,1/40)

in divisor order(1,5,7,25,35,49,175,245,1225), giving Gamma<=33/4.

Otherwise the four y_i are distinct. Fix any two gap children and repeat the construction, deleting their at-most-two leaves from each witness tree. At least7 leaves remain. This gives an actual law psi supported on the three full roots, with simultaneous caps

    (1,1/3,3/7,1/5,1/7,1/7,3/35,1/21,1/35).

Its LCM envelope is exactly9 at these bounds. Let eta be uniform on the four actual gap points, and set

    nu=(35/39)psi+(4/39)eta.

The two parts have disjoint first-five roots. Therefore their joint caps combine by maxima, not by sums. Only the seven marginal caps need the sum. Distinctness of the four y_i gives eta's leaf cap1/4, while its column cap is at most1. The resulting cap vector is

    (1,35/117,19/39,7/39,5/39,2/13,1/13,5/117,1/39).

For example, the full-point cap is max((35/39)/35,(4/39)/4)=1/39, and the joint first-five/first-seven cap is max((35/39)/7,4/39)=5/39. Multiplying the vector by the ordered-LCM multiplicities(1,3,3,5,9,5,15,15,25) gives

    Gamma(nu)<=112/13<9.

Thus the whole4000 profile has this bound, whether or not the gap leaves repeat. No standalone premise was used in the law argument.

### Three active full roots:0555,k=0,Z=25

The sorting bounds and pair inequalities force the three sorted cost lists to be11111,22222,22222, up to permutation. All these private cuts are finite leaf cuts. With no public support, every actual active fibre is contained in its own singleton or two-leaf candidate set.

Call the singleton root clean. Pair any clean triple with any triple at a doubled root. There are exactly3+6=9 candidate occurrences. A ternary tree forces these9 labels to be distinct and actual at their own selected children, and its column-count vector has coordinates0 or3. Varying the selected triples shows all candidate leaves actual. Exchange one clean singleton while keeping two other clean children fixed; its unit-vector difference must be divisible by3, hence vanishes. The five clean labels therefore lie in one column H and are pairwise distinct.

Exchange one doubled child while keeping two other doubled children fixed. Each difference between two double column-count vectors has coordinates in[-2,2] and is divisible by3, hence zero. Write their common vector as b. A tight pair gives3e_H+3b with coordinates0 or3. Thus b is1 in two distinct columns outside H, and0 elsewhere. Within either doubled root, the five labels in each of its two columns are pairwise distinct: any two owners fit together into a triple, whose nine labels are distinct.

Select the five clean points and all ten points at each doubled root. There are25 distinct actual source points, though a seven leaf may occur at both doubled roots. Uniform mass on these25 points gives simultaneous count bounds

    (25,10,10,2,5,2,1,1,1)/25.

The clean column cannot meet either doubled support. Any other seven column receives at most5 points from each doubled root. Every full seven leaf receives at most one point per doubled root. Each child has at most one point in a specified column, and each root has at most one point at a specified full seven leaf. These observations justify all joint entries of the vector under one law. Its envelope is

    Gamma<=41/5<9.

The inactive gap root receives zero probability; its fibres and the source remain unchanged. No standalone premise or relation between the two doubled roots' column pairs is needed for this bound.

### One inactive child:3555 or4455,k=4,Z=18

The sorting equalities force every active private cost to be1. There are18 active children. The public cost4 antichain is either four individual leaves, or a whole column G and one leaf y outside it.

Pair any two active gap children with any three active full-root children. For four finite public leaves, this gives exactly9 candidate occurrences. Literal blocking forces all9 actual and distinct, and a column-count vector with coordinates0 or3. Singleton exchanges lock the gap labels into one column K and each full-root family into one column H_r. All active lengths are greater than the selected length, so these exchanges are available, including the partial four-child full root. In the exact vector2e_K+3e_Hr+v_P, K cannot equal H_r. It follows that v_P=e_K+3e_G for some G distinct from K,H_r. The public labels are fixed, so the same G works for all roots.

For public G plus y, the outside-G candidates are exactly y plus the five selected private singletons. A ternary tree must use G and all six outside leaves, grouped into two triples. The same exchanges put every gap label and y in K=col(y), and each full-root singleton family into another column H_r, avoiding G and K.

In either public form, the full-root columns H_r are pairwise distinct: if two coincided, their two selected triples together with P could have only two columns with at least3 leaves; K contributes at most the one public leaf. This contradicts their literal pair test. Tight tests show every private singleton actual at its owner, and all labels within a root distinct. Labels in different roots have different columns.

Select the one private point from each of the18 active children. They have distinct children and distinct full seven leaves, with at most5 in any first-five root or first-seven column. The uniform18 law therefore has the original cap vector

    (1,5/18,5/18,1/18,5/18,1/18,1/18,1/18,1/18),

and Gamma<=79/9<9. The inactive child can carry arbitrary standalone leaves and is not used by the selector. The proof never applies standalone to the active projection.

### Partial2555: a weighted public/private law

The two private shapes are03/11111/11111/11111 and12/11111/11111/11111. Here there are only17 active children, so the18-distinct-child construction is unavailable. The following joint law gives the stronger bound127/15.

### Actual private branches and a public pair-projection premise

Write P for the cost3 public support. It is either one whole column G or three leaf labels. Pair triples of singleton children at two clean full roots. The same tight-nine/six and one-child exchange used for cut70 forces each clean root's five singleton labels to be actual at their OWN children, distinct, in one column H_r; the three H_r are different. If P is finite, its three leaves lie in one further column G. Otherwise G is already given. Every H_r avoids G.

Pair the two active gap children with any clean triple. For shape12 the gap singleton plus double contribute exactly three candidate leaves. The third branch of the required ternary tree forces all three distinct and actual at their own children in a column K outside G and every H_r. For03, the zero child's actual fibre is contained in G. If its cost3 partner is a finite leaf cut, the same saturation gives three distinct actual K leaves at that partner; if it is a whole-column cut, its column K must avoid G and all H_r, and that child must have at least three actual K leaves. Fix any three. Thus both shapes supply three actual private gap points in K; they may all lie at one child.

Fix any triple of children at EACH full root, and retain both active gap children. Every root pair has projection in exactly its two private columns plus G. Its ternary tree must use G, so its actual G-projection has at least three leaves. This is true for every complete child-restriction profile. It does not assert that any individual root has three actual G leaves.

### Weighted public law on the one actual common column

Set, in units1/275,

    W=65,       A_gap=B_gap=15,
    A_full=25,  B_full=39 for each of the three full roots.

Here W is desired total public mass, A are root budgets and B are leaf-coupling coefficients. For each subset S of the four roots, the scaled Report445 weighted pair-cut requirements are

    sum_(r outside S) A_r >= W,                    |S|<=1;
    sum_(r outside S) A_r + sum_(r in S) B_r/2 >= W,|S|>=2;
    sum_(r outside S) A_r + sum_(r in S,r!=j) B_r >= W, |S|>=2,j in S.

All44 inequalities hold. They can be checked by the number of full roots in S and whether the gap belongs to S; the smallest slacks in the three displayed families are respectively0,1/275,0. The sufficient conditions do not require sum A or sum B to equal W.

Apply[445](445-occupied-branch-restrictions-and-weighted-root-caps.md)'s weighted theorem at depth one on G's actual fine-leaf projection, with kappa=1/3, alpha=A/W and beta=B/W. The preceding pair premise holds for each fixed child-restriction profile. Scale its one flow to mass W, lift every atom to an actual selected child, and average uniformly over the ten triples at each full root, independently. The gap's two active children are always selected. Thus the actual public subprobability mu has

    mu(root r)<=A_r,
    mu(child r,c)<=delta_r A_r,
    mu(fine leaf)<=W/3,
    mu(root r,fine leaf)<=B_r/3,
    mu(child r,c,fine leaf)<=delta_r B_r/3,

where delta_gap=1 and delta_full=3/5. All of mu lies in G. Conditional flows may depend on all restrictions; averaging uses the pointwise bounds, not independence of that flow from the selections.

### Add the private atoms and bound all original cylinders

Give each of the15 clean private points mass x=13/275, and each of the three gap private points mass y=5/275=1/55. These private columns avoid G and one another. Their total mass is15x+3y=210/275. Together with mu of mass65/275 this defines ONE actual probability nu.

For shape03 the gap's entire private mass3y can occur at one child; using this upper bound also covers12. The same law consequently has caps, in divisor order(1,5,7,25,35,49,175,245,1225),

    (1,18/55,13/55,6/55,13/55,13/165,3/55,13/275,13/275).

For completeness these follow from the following maxima:

* root: max(A_full+5x,A_gap+3y)=18/55;
* public/private coarse column: max(W,5x,3y)=13/55;
* child: max((3/5)A_full+x,A_gap+3y)=6/55;
* root/column: max(A_gap,A_full,5x,3y)=13/55;
* fine leaf: max(W/3,x,y)=13/165;
* child/column: max(A_gap,(3/5)A_full,3y,x)=3/55;
* root/fine leaf: max(B_gap/3,B_full/3,x,y)=13/275;
* atom: max(B_gap/3,B_full/5,x,y)=13/275.

The repeated gap child is explicitly included; no false18-distinct-child selector is used. For arbitrary independent phases of the nine original numerical divisor queries, every pair is disjoint or intersects in its numerical LCM cylinder. The81 ordered-pair envelope is

    1+3*(18/55)+3*(13/55)+5*(6/55)+9*(13/55)
      +5*(13/165)+15*(3/55)+15*(13/275)+25*(13/275)
    =127/15<9.

All chosen points, public flow and private weights are fixed before phase queries. The standalone five-tree is not used: it may depend on inactive children, so it must not be applied to the active support alone. This component handles2555; it does not supply an outside-cofactor lift.

### Entire full k1 profile is impossible

Here P is one public leaf y. Every gap child has a private two-set. Every full root has shape02222 or11222, so its minimum legal triple has exactly four private candidate occurrences.

A gap pair of two children, together with a minimum full triple, has exactly1+4+4=9 public/private occurrences. Literal blocking forces all nine labels distinct, actual and exactly arranged as three columns of three leaves. In particular each selected candidate is actual at its private owner. Fixing the full triple and exchanging one gap child shows all four private gap two-sets have the same column-count vector a: the difference between their vectors has coordinates in[-2,2], whereas the difference between the two ternary column vectors is divisible by3.

Let e be the unit column vector of y, and choose minimum-private triples at two distinct full roots, with column vectors v,w. The three legal pair tests (gap with each full root, and the two full roots together) give

    2a+e+v =0 mod3,
    2a+e+w =0 mod3,
    v+w+e  =0 mod3.

Subtracting yields2a-e=0 mod3. Every coordinate of a is0,1 or2, with total2. At coordinates other than col(y), divisibility forcesa_j=0. At col(y), it forcesa_j=2. Thusa=2e.

But a gap pair then contributes four DISTINCT actual leaves in col(y), all different from publicy; any tight nine-leaf test already contains five leaves in that one column. A ternary depth-two tree of exactly nine leaves has exactly three in every occupied column. Contradiction. No standalone-tree premise is used.

This rules out all four k1 shapes together, including the all11222 case.

### A common-column obstruction for full k5

For k5, P is either five public leaves or a whole column G together with two public leaves y1,y2 outside G.

Consider any shape with a legal gap selection of total private cost2, and any full root containing a zero-cost child and at least three singleton children. Choose the zero child and any two singleton children. In the five-public-leaf case the pair has exactly5+2+2=9 candidates and is tight. In the G+y1+y2 case it has at most2+2+2=6 outside-G candidates; a ternary tree must use G and all six outside candidates, also tightly.

In either case all selected singleton labels are distinct and actual at their owners. Their column-count vectors are constrained modulo3. Exchanging one singleton in its pair locks that full root's entire singleton family into one column H_r. Comparing these tight tests at two such full roots, with the SAME fixed gap selection, gives

    2(e_Hr-e_Hs)=0 mod3,

hence H_r=H_s. Every participating full singleton family therefore lies in one common H.

Different singleton labels in this union are distinct even across roots: test the zero child and suitable two singleton children at each of two roots. Again the pair has private cost2+2 and the same tight public support. Such a test can include any chosen label at each root, so equality of two labels would contradict tightness. Consequently if these full singleton families total at least8 labels, the source would have eight distinct fine leaves in one seven-column, impossible.

### Apply the obstruction to eleven of thirteen shapes

The following ten shapes have at least8 singleton children of the preceding kind; the indicated number counts only full roots containing a zero child and at least three singleton children:

| shape | forced distinct leaves in H |
|---|---:|
|0222/01111/01111/01111|12|
|1111/00222/01111/01111|8|
|1111/01111/01111/01113|11|
|1111/01111/01111/01122|8|
|1111/01111/01111/11112|8|
|1111/01111/01112/01112|10|
|1112/01111/01111/01112|11|
|1112/01111/01111/11111|8|
|1113/01111/01111/01111|12|
|1122/01111/01111/01111|12|

All are impossible. This argument also covers whole-column realizations of a cost3: that owner child is never selected in the tight tests.

The additional shape1111/01111/01112/11111 has seven forced distinct singleton labels in one common H. Every private cut in this shape is finite, with total18 candidate occurrences. If P is five public leaves, the whole source projection has at most5+18=23 labels, contradicting the standalone25-leaf tree.

If P=G union{y1,y2}, the full outside-G projection has at most2+18=20 candidate occurrences. A standalone five-ary tree must use G because fewer than25 labels lie outside it. Its other four branches require exactly20 distinct outside labels, five in each of four columns. Thus all20 candidate occurrences are distinct actual labels outside G and every outside column has exactly5 labels. The seven forced distinct singleton labels in H outside G contradict that cap. Hence this eleventh shape is impossible too.

### Two remaining shapes give18 actual private points

The only remaining candidates are

    0111/11111/11111/11111,
    1111/01111/11111/11111.

Every private cut is a singleton, and there are exactly18 positive-cost children. Again five public leaves are impossible by the23<25 projection bound. In the G+y1+y2 case the same standalone saturation forces the20 public/private occurrences outside G to be distinct actual labels arranged as four columns of five.

Every private label is actual at its OWN child: it differs from the two public labels and every other private candidate, so no other child can supply its actual occurrence under cut containment. Select the unique private label at each of the18 positive-cost children. These are18 distinct children and18 distinct full seven leaves. Each seven-column has at most5 selected points; each five-root has at most5 because children are distinct.

Uniform mass1/18 on these actual points therefore gives the established numerical cap vector and the complete81-pair ordered-LCM boundGamma<=79/9. The zero-cost child remains in the source with zero law mass. No blocker inheritance is asserted.

### Full k3,Z25: the actual eighteen-point construction

All19 occupied children are active. Public cost3 means one whole column or three candidate leaves; private cost3 again permits a whole column. The21 sorted shapes are listed below.

### Common public column and locked singleton anchors

Every shape has at least two full roots with at least four singleton children, or two clean11111 roots. Test singleton triples at two such roots. If P is a whole column G, the six private occurrences must all be distinct and actual outside G and must form two branches of three. If P is three finite leaves, exactly nine candidate occurrences must form the ternary tree. Exchanging one singleton within a triple locks its family's column; the two locked columns differ and the three public leaves form one third column G. Thus in either case P is contained in G.

The singleton labels at each such root are actual at their own children, distinct, and in a column H outside G. Different singleton families have different H's. A full root with exactly three singleton children can also be locked by pairing its unique singleton triple with an already locked triple. Its three labels must form a third branch and are actual at their owners. Whenever used below, an additional full-root anchor is supplied by this rule or the zero/singleton/double rule. The02222 and11222 exceptional roots need not supply an anchor; those cases instead use the already locked gapK as an anchor for the exceptional-root argument.

An ANCHOR in H means a legal child restriction at another root whose actual projection outside G is precisely three distinct private leaves in H. A locked singleton triple is such an anchor. A gap singleton+double pair, once tightly locked below, also is an anchor. Only restrictions at DIFFERENT roots are paired.

The construction order is explicit in the cases with no initial third full-root singleton anchor. For2222/01222/11111/11111, first lock the two cleanH1,H2; next lock the exceptional01222 branchH3 using its zero/singleton/double restrictions against the clean anchors; only then test gap double pairs against all threeH's. For1222/02222/11111/11111 and1222/11111/11111/11222, first lock the two clean anchors, then lock the gapK using its singleton/double restrictions; useK as an additional anchor for exceptional-root unions. These deductions do not assume an exceptional full-root anchor that has not been constructed.

### Actual finite-union and representative facts

#### At most five private candidates against anchors

Take a fixed legal restriction at one root with at most m finite private candidate leaves, where m<=5. Test it against an anchor H. The combined projection outside G has at most m+3<=8 leaves, so its ternary tree uses G. The root restriction alone has fewer than6 private candidates, so the tree must also use H. Its third branch consists of at least3 actual leaves from the restricted root, in a column different from G,H.

There is at most one column with3 of the fixed m<=5 candidate labels. Testing the SAME restriction against several anchor columns therefore puts this actual branch outside ALL those anchors. This yields a statement about the ACTUAL UNION at the chosen children. It does not make every candidate actual at every owner.

When m=3, all three candidates are forced distinct and actual at their own owners in the resulting new column. In particular this holds for a gap singleton+double or a full-root zero+singleton+double.

#### Small actual sets

Three nonempty sets of size at most2 with pairwise unions of size at least3 have an SDR of size3, by Hall. More generally three sets each of size at least2 whose total union has size at least3 have an SDR of size3 (this form also allows a larger third set).

Four sets of size at most2 with pairwise unions of size at least3 have an SDR of size4. The only additional Hall condition is total union at least4. If the total union had size3, four two-sets could not all differ (there are only three such two-subsets); if a singleton occurred, the other sets would have to be the same complementary pair. Either alternative violates a pair-union condition.

#### A double sibling supplies a new locked-column leaf

Suppose at least three singleton children at a full root have distinct actual labels W in one H, and there is a double child E. Pair any two of those singleton children together with E against an anchor outside H. The finite-union fact forces an actual three-leaf branch from the two W labels and E. Since E has at most2 candidates, that branch must be H, and E supplies an actual H-leaf outside the selected W pair.

If all actual H-leaves of E belonged to W, their set has size<=2 and could be included in a selected pair, a contradiction. Thus E supplies a new actual H-leaf outside ALL singleton labels. This produces5 distinct points at a11112 root, or4 at a11122/11123 root. A cost3 child of11113 or11123 can simply be ignored when enough points have already been selected.

#### Zero/singleton/doubles at a full root

At01222, tight tests of(zero,w,E_i) against anchors force w and each double's two candidates actual, distinct and in one common H outside the anchors. Each E_i avoids w. Testing(zero,E_i,E_j) forces|E_i union E_j|>=3. Hence w plus a three-set transversal gives4 points in H.

At01223, the same rule handles w,E1,E2. For its cost3 child W, tests of(zero,w,W) against every anchor give at least2 actual leaves outside w,G and the anchor columns. For a finite W this follows from the at-most-four-candidate fact; for a whole column L, the tree requires L different from G and each anchor, and W supplies at least2 leaves other than w (or3 when w is not in L). The three setsE1,E2,W-minus-w each have at least2 members and their full union has at least3 because|E1 union E2|>=3. An SDR of3 plusw gives4 points outside the anchors.

At02222, test(zero,E_i,E_j) against all available anchors. The actual eligible setsU_i of each double, restricted outside G and the anchors, have size<=2 and pairwise unions>=3. The four-set Hall fact gives4 actual points at its four double children. They need not occupy a single new column, but only4 points in total are selected there.

#### Gap selections

For1222, tight singleton/double tests against full-root anchors forcez and each of the three two-setsE_i actual, distinct within each pair, in one common K outside all anchors. AllE_i avoidz. Testing two doubles gives|E_i union E_j|>=3. Thusz plus a three-set SDR gives4 points inK.

For1223, the same argument givesz,E1,E2 inK, with their pair union>=3. The singleton/cost3 test gives at least2 actual eligible W-leaves different fromz, whether W is finite or a whole column, exactly as in the full-root cost3 argument. Hencez plus an SDR fromE1,E2,W-minus-z gives4 points outside the full anchor columns. If only3 points are needed, usez and one point from each double and ignore W.

For1233, selectz, one point of its actual double, and one point from either cost3 child. The cost3 test supplies at least2 actual eligible leaves avoidingz, so the third point can avoid the double point too.

For0333, the zero-child/cost3 pair forces each cost3 child to supply at least3 actual eligible leaves outside every full-root anchor. Three such sets admit distinct representatives greedily, giving3 gap points; the zero child need not be used.

For1333, let Z be the singleton child's actual private leaf outside G and the full anchor columns, if one exists. If Z exists, each cost3 child supplies at least2 other actual eligible leaves, so retain Z and distinct representatives from two cost3 children. If Z does not exist, every singleton/cost3 test forces its cost3 child to supply3 actual eligible leaves; choose one distinct representative from each of the three cost3 children. Either way there are3 actual gap points. No missing singleton candidate is promoted to an actual point.

For2222, restrict each double's actual private set outside G and all full anchors. Every pair union has size>=3 by the finite-four-candidate fact, so the four-set Hall lemma gives4. If only3 gap points are needed, any three doubles suffice. The same three-double selection applies to2223, ignoring its cost3 child.

For2233, use the two double children and one cost3 child. The two actual eligible double setsU1,U2 have pair union>=3, so both are nonempty. Testing either double with the cost3 child gives an actual union of at least3 eligible leaves. For a finite cost3 this is the at-most-five-candidate fact. For a whole column L, a ternary tree must use G and the anchor (the two finite leaves cannot form another branch); L must avoid G and every anchor, and U_i union the actual W-leaves inL has at least3. Thus all three eligible sets are nonempty and every pair union is at least3. Hall gives3 actual points.

### The new four-point lemma: two singleton children and three doubles

This handles1222/11111/11111/11222, the only shape whose exceptional full root has just two singleton children.

The two clean roots give5 actual points in distinctH1,H2. The gap1222 rule gives4 actual points inK outsideG,H1,H2, and its singleton+double restrictions are anchors inK. ALL gap private candidates lie inK; the entire two clean-root supports lie inG union H1/H2. Thus all actual source points outsideG,H1,H2,K come from the exceptional root.

LetS be the ACTUAL singleton leaves at its two singleton children lying OUTSIDE those four columns. This set has size0,1 or2; its members need not equal all candidate singleton labels. For each double child letA_j be its actual leaves outside those four columns, so|A_j|<=2.

For eachj, test the exceptional triple consisting of both singleton children and that double against anchors in EACH ofH1,H2,K. The at-most-four-candidate fact showsS union A_j has at least3 actual leaves in one columnL_j outside all four known columns. The same column is obtained across anchors because a four-label candidate set cannot contain two three-leaf columns. In particularS is nonempty: two double leaves alone could not supply three.

If|S|=1, writeS={s}. EachA_j must consist of two distinct actual leaves incol(s), both different froms. The full triple of all three doubles, tested against a clean anchor, forces|A1 union A2 union A3|>=3: their projection is inG plus one private column, so a third branch needs at least3 in that column. The threeA_j have an SDR; select those3 double points ands at one actual singleton owner.

If|S|=2 and its leaves lie in different columns, eachA_j has two actual new leaves in the column of one of the singleton leaves, avoiding BOTH members ofS. Select both singletons and distinct representatives from any twoA_j; two sets of size2 always permit this. That gives4.

If|S|=2 and both leaves lie inH, putB_j=(A_j intersection H) minus S. EachB_j is nonempty. If their union has at least2 leaves, two distinct representatives at two different double children exist: choose one leaf at an owner, and if all other owners offer only that leaf, the owner with another leaf can take the latter. Together with the two singletons these give4.

The only remaining possibility is that everyB_j={w} for one fixed new actual leafw. ThenH has only the three actual source leavesS union{w}. Each double can supply at most one further actual leaf outsideH; across all three doubles there are at most3 such leaves. Every other root is already contained inG,H1,H2,K. Hence outside these four known columns there is no column with5 actual leaves: H has3 and all other outside columns together have at most3. This contradicts the standalone five-ary tree, which needs five different columns each with5 actual leaves.

Therefore the exceptional root always supplies4 actual points at distinct children and with distinct seven leaves outsideG,H1,H2,K. Together with4 gap and10 clean points, this is18. The exceptional points occupy at most4 places in any new column, so the column cap5 holds.

### All21 shapes and point counts

In the following table the counts are(gap,full-root1,full-root2,full-root3), matching the displayed sorted shape order. All chosen points at a locked full root lie in its ownH. All other-root selections are taken outside the locked anchors; when a gap1222/1223 K is available, it is also used as an anchor for the exceptional full-root union selections. Thus independently described selections have disjoint leaf sets, rather than merely separate existence witnesses.

| shape | chosen counts | justification beyond locking |
|---|---|---|
|0333/11111/11111/11112|(3,5,5,5)|new double leaf; three cost3 gap representatives|
|1222/01222/11111/11112|(4,4,5,5)|zero/singleton/double Hall; new double leaf|
|1222/01223/11111/11111|(4,4,5,5)|cost3 extension at exceptional full root|
|1222/02222/11111/11111|(4,4,5,5)|four-set actual Hall outsideK,H1,H2|
|1222/11111/11111/11123|(4,5,5,4)|three singleton siblings plus new double; ignorecost3|
|1222/11111/11111/11222|(4,5,5,4)|new four-point lemma above|
|1222/11111/11112/11113|(4,5,5,4)|new double at11112; four singleton points at11113|
|1222/11111/11112/11122|(4,5,5,4)|new double at both exceptional roots|
|1222/11112/11112/11112|(4,5,5,4)|new double at two roots; third contributes its four singletons|
|1223/01222/11111/11111|(4,4,5,5)|gap cost3 extension; exceptional Hall|
|1223/11111/11111/11113|(4,5,5,4)|gap cost3 extension; ignore exceptional cost3|
|1223/11111/11111/11122|(4,5,5,4)|gap cost3 extension; exceptional new double leaf|
|1223/11111/11112/11112|(3,5,5,5)|ignore gapcost3; both full double extensions|
|1233/11111/11111/11112|(3,5,5,5)|one gap cost3 extension; full double extension|
|1333/11111/11111/11111|(3,5,5,5)|actual-singleton-present/absent gap argument|
|2222/01222/11111/11111|(4,4,5,5)|gap four-set Hall; full zero/singleton Hall|
|2222/11111/11111/11113|(4,5,5,4)|gap four-set Hall; ignorefullcost3|
|2222/11111/11111/11122|(4,5,5,4)|gap four-set Hall; full double extension|
|2222/11111/11112/11112|(3,5,5,5)|three gap double representatives; full double extensions|
|2223/11111/11111/11112|(3,5,5,5)|ignoregapcost3; full double extension|
|2233/11111/11111/11111|(3,5,5,5)|two doubles and onecost3 actual Hall|

Every row sums to18. Every selected point belongs to a distinct child and therefore each five-root contributes at most5. Each lockedH has at most5, the gap contributes at most4 outside the full anchors, and an unlocked exceptional full root contributes at most4 outside the gapK and other full anchors. Thus no seven-column has more than5. All full seven leaves are distinct by actual Hall and the anchor exclusions. The selected uniform18 law is one actual law chosen before every numerical phase and satisfiesGamma<=79/9.

### Conclusion and exact controls

The eight profile rows have respective bounds41/5,127/15,79/9,112/13,79/9, impossibility,79/9 and79/9. Their maximum is79/9, proving(C71-law). The standalone premise is used only where the cut-active support is the full source; partial profiles never inherit it after inactive children are omitted from the law.

The [necessary-profile enumerator](../../frontier/cover-geometry/height_two_cut71_profiles.py) and [exact classification](../../frontier/cover-geometry/height_two_cut71_profiles.json) check the ten labelled profiles and every sorted-cost shape above. This checks finite arithmetic exhaustiveness; the actual-support implications are supplied by the preceding proofs.

The [actual-source program](../../frontier/cover-geometry/height_two_cut71_actual_sources.py) and [data](../../frontier/cover-geometry/height_two_cut71_actual_sources.json) give41 sources: both4000 controls,0555,3555,4455, the two surviving full-k5 shapes, all21 full-k3 shapes with finite private cuts, and13 additional versions with every cost3 private cut replaced by a whole column. Each has an explicit cut and matching actual flow71. The full-k3 selector uses the actual child/leaf/column incidence network and finds18 points at distinct children and leaves with column cap5; it does not treat candidate leaves as actual points.

The [partial2555 constructor](../../frontier/cover-geometry/height_two_cut71_partial2555.py) and [data](../../frontier/cover-geometry/height_two_cut71_partial2555.json) add six actual sources. They cross both public forms with private shapes03 finite,03 whole-column and12. In the whole-public controls each individual root has only two actual public leaves; it is the pair union that supports the weighted coupling. All44 sufficient weighted inequalities are checked exactly, and a single actual public flow is mixed with the private atoms. Their measured LCM envelopes are1391/165, below the universal127/15 bound.

Each of these47 controls checks all480 selected pair tests,10000 full literal product tests, the standalone five-tree, the actual maximum flow and explicit cut71, every capacity and conservation, all1767 numerical cylinders and81 ordered LCM pairs. Calculations use integers and exact rational numbers, with checks active under Python-O. Finite controls are not an exhaustive search over actual sources and are not Lean verification.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut71_profiles.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut71_actual_sources.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut71_partial2555.py
```

## Complement budgets and a finite sequence of cut77 repairs

The following ordinary finite-network theorem supplies exact repairs or explicit support obstructions for any integral value77 flow under the stated actual capacities. It does not require T3 for the selected block. Its final conditional moment bound uses the literal4555 premises above; no unrestricted arithmetic lift or Lean verification is claimed.

### Fixed data and the exact quantifiers

Let F be the entire actual source. Let lambda be an INTEGRAL feasible flow of value77, expressed by its nonnegative integer masses lambda(r,c,g,h) at actual points. The capacities are: root21, child7, private child/first-seven column6, actual entry2, public fine leaf7, public first-seven column21. Actual bridges have capacity126 and cannot constrain these entry masses further.

Fix a root r and first-seven column G with

    a_r=21,    d_(r,G)=20.

The public G total is automatically20 or21. The root's total mass outside G is exactly1, at one actual point. In the theorem below ALL point masses of the other three roots are held fixed. The root r total must remain21. Child totals at r need not remain fixed, and the old positive support need not be retained.

Define the other-root masses and remaining public budgets by

    o_g  = sum_(r'!=r,c,h) lambda(r',c,g,h),
    o_gh = sum_(r'!=r,c)   lambda(r',c,g,h),
    R_g  =21-o_g,             R_gh=7-o_gh.

They are nonnegative integers. For every g!=G let

    A_g={h: there is an ACTUAL child c with(r,c,g,h) in F}.

Previously zero actual points are included. Define

    C_g=min(R_g, sum_(h in A_g) R_gh),
    C=sum_(g!=G) C_g.                              (UC1)

C measures the capacity visible in this PUBLIC complement after the other roots are fixed. It is not claimed to be the maximum root throughput at larger values: the private and child constraints have deliberately not been included. The threshold at TWO is exact.

The following statements are equivalent:

1. C>=2.
2. There is an INTEGRAL value77 flow on F, with every other-root atom fixed, root r mass21 and block(r,G) mass19.
3. There is a REAL value77 flow on F, with every other-root atom fixed, root r mass21 and block(r,G) mass strictly below20.

Thus failure rules out fractional as well as integral improvements under these fixed-other-root conditions.

### Constructing the repair from two public units

Because all R values are integers, C>=2 allows two integer units on the actual public projection outside G, obeying every R_g and R_gh. Choose column amounts up to C_g and then fill actual fine leaves up to R_gh, stopping at total2. Lift each chosen leaf to ANY actual child at r that has that leaf. Call the resulting outside masses y. They use at most2 actual points; every entry, private column and child has y mass at most2.

Keep the old20-unit G matrix x for the moment, and replace the old outside unit by y. Every private G row of x has mass at most6. A child can violate its full cap7 only when its old G row has6 and y puts both units there, giving8. There is at most one such child, because y totals2.

If this child exists, remove one positive integer unit from an old G atom in that child. Its G row becomes5 and its total becomes7. If no child violates7, remove one unit from any positive old G atom. Such an atom exists because x totals20.

The new G block has19 units; the outside block has2; the root still totals21. All full-child caps7 hold. Private G and G-entry caps only decrease; outside private columns and entries have mass at most2, hence obey6 and2. In public G every mass only decreases. Outside G, y was chosen within the residual public column and leaf budgets after fixing the other roots. Every new atom belongs to F. Therefore this is a feasible INTEGRAL value77 flow on the same actual source.

At most four actual atoms change: the deleted G unit, the old outside unit, and at most two new outside atoms. These atoms need not share a child. In particular, there need not be any positive G atom, or even any actual G point, at a destination child.

Conversely, any flow in item3 puts strictly more than1 unit outside G. Its projection is supported on A_g and bounded by R_g and R_gh, so its outside mass is at most C. Thus C>1. C is integer, hence C>=2. Item2 implies item3 directly. This proves the equivalence, including its real-flow quantifier.

### If the repair is blocked, an actual support cover is forced

The initial outside unit proves C>=1. Hence blocking is exactly C=1. There is then exactly one column H!=G with C_H=1; all other C_g vanish.

There are two cases.

**Column bottleneck.** If R_H=1, the other roots already put20 units in H. The entire available complement is capped by that single remaining column unit.

**Leaf bottleneck.** If R_H>=2, then sum_(h in A_H) R_Hh=1. There is exactly one h_* in A_H with R_Hh*=1, and every other allowed H-leaf has residual0. The other roots put6 units in this critical leaf.

Every other actual off-G point is covered by a saturated public prefix: at a column g with C_g=0, either R_g=0 and the whole column is saturated, or every allowed leaf has R_gh=0. In the leaf-bottleneck column H, the other allowed leaves are saturated too.

Consequently there is an antichain Q of public prefixes, each having ZERO residual capacity, such that

    F_r outside G is contained in union(Q) union P_*,       (UC2)

where P_* is one critical column or one critical leaf with residual capacity1. The antichain can be chosen disjoint from P_* and from G: select a saturated column instead of its leaves when available; otherwise select the actual saturated fine leaves. No prefix outside the actual complement is needed.

This is a statement about the ENTIRE actual off-G support, not merely positive flow atoms. It follows from the one-unit obstruction after subtracting the other-root masses, not from the local5x7 support alone. Conversely, any such actual cover by residual-zero prefixes and one residual-one prefix gives C<=1, hence blocks the fixed-other-root repair.

### The other roots' total56 limits this cover

The other roots together have mass77-21=56. Let

    p=number of whole columns in Q,
    l=number of fine leaves in Q,
    epsilon=o_G in{0,1}.

All prefixes in Q, the critical prefix P_*, and G are pairwise disjoint. A zero-residual column contains21 other-root units; a zero-residual leaf contains7. The critical column contains20, or the critical leaf contains6. Thus

    21p+7l+20+epsilon<=56   in the column case,
    21p+7l+ 6+epsilon<=56   in the leaf case.          (UC3)

In particular,

    3p+l<=5   in the column case,
    3p+l<=7   in the leaf case.                       (UC4)

So only these coarse cover shapes need be considered:

| Critical prefix | Saturated columns p | Saturated leaves l |
|---|---:|---:|
| one column |0|at most5|
| one column |1|at most2|
| one leaf |0|at most7|
| one leaf |1|at most4|
| one leaf |2|at most1|

These are necessary coverage shapes, not claims that all occur under the literal blocker hypotheses. They preserve which other-root mass paid for each saturated prefix. In particular, a fixed-other-root obstruction cannot hide arbitrarily many disjoint blocked public leaves. This narrows a subsequent literal-source or residual-closure classification to five budget families.

### A cross-root release supplied by actual neighbors

The following sufficient condition applies even when C=1. It preserves every root total and every public coarse-column total, but it is allowed to change another root's flow.

Write the old unique outside atom as

    p=(r,rho,H,k),    lambda(p)=1.

Let q=(s,c,H,l) be a positive atom of ANOTHER root s!=r. It is an eligible donor when

    l=k    OR    the old total public mass at(H,k) is at most6.   (UC5)

This is exactly the fine-leaf condition needed for q's removal and p's addition: in the first alternative they cancel at the same leaf; in the second p has a unit of spare fine capacity. The common public H-column total will not change.

If the old full-child total at(r,rho) is7, its G row has6 units. Define

    J_bad={j: the old public(G,j) mass is7
                 and lambda(r,rho,G,j)=0}.

If that full-child total is at most6, define J_bad to be empty.

There are at most TWO forbidden digits. In the only nonempty case, t forbidden public leaves, each of mass7, are disjoint from the six units in the distinguished G row. The public G-column total b is at most21, so

    7t+6<=b<=21,      hence t<=2.                    (UC6)

Suppose the same donor child(s,c) has an ACTUAL G point(s,c,G,j) with j not in J_bad. Then an actual four-atom circulation decreases d from20 to19.

Add1 at p and at(s,c,G,j); remove1 at q and at a suitable old G atom x of root r. To choose x:

- If the child(r,rho) was full, remove x in that same G row. If public(G,j) was also full, choose x at its fine digit j; this atom is positive by j not in J_bad. If that public leaf was not full, any positive atom of the row suffices.
- If the child(r,rho) was not full, no particular removal row is required. If public(G,j) was full, remove a positive root-r atom at that digit. It exists because the other roots' ENTIRE G mass is at most1, while that public leaf has7. Otherwise remove any positive G atom.

All four points are distinct and actual. The donor root's child total stays fixed. The recipient old outside point rises1 to2; its root's other private off-G mass was only1, so the new private column and entry are legal. At the donor's G point, the old atom and private G prefix had mass at most1, because every other root together had at most1 in G; both rise to at most2. The target G removal handles the only possible recipient-child or G fine-leaf conflict. Condition(UC5) handles the H fine-leaf conflict. Every root and public first-seven column total is unchanged, and all entry/private/public caps remain valid.

In particular, any eligible donor child with at least THREE distinct actual G fine neighbors must have one outside J_bad and supplies this repair. This is an actual-neighborhood hypothesis, not a positive-flow-support hypothesis: its successful destination may previously have carried zero flow.

Conversely, if no circulation in this explicitly specified family exists, EVERY eligible donor child's entire actual G-neighbor set is contained in the SAME set J_bad of at most2 digits. If the old recipient child was not full, all those donor children have no actual G point at all.

The one-unit bottleneck now yields counts:

- In the critical-leaf case the old recipient leaf has6 units from other roots. Each atom is at most2, so at least3 distinct other-root child owners are eligible. If no four-atom release exists, all of their G neighborhoods lie in J_bad.
- In the critical-column case, if the old recipient fine leaf is not full, every positive other-root H atom is eligible. The other roots have20 units in H and each private child/H prefix is at most6, so there are at least4 distinct eligible child owners. Their G neighborhoods must all lie in J_bad if no release exists.
- If the critical-column recipient fine leaf is full, the same6-unit/3-owner conclusion at that leaf applies.

This transfers the obstruction from one root's bad local block to a common two-digit trap across at least3 actual donor children. These children may belong to different roots. It does not silently turn them into one root's three-row hypothesis, and it does not yet prove that the literal pair tests exclude their shared trap.

### Finite repair normal form without new dangerous blocks

Call a block dangerous when its root total is21 and its joint root/column mass is20. Either of the preceding repairs strictly removes its selected dangerous block and creates NO new dangerous block.

For the fixed-other-root repair, the selected root still totals21, its selected block is19, and all its other blocks together total2. Every other-root atom is unchanged.

For the four-atom cross-root repair, the selected root again has block19 and outside mass2. At the donor root, its target-column block had mass at most1 because the selected root already supplied20 in that public column; the donor block therefore rises to at most2. Its H-block had mass at most20 because the selected root already supplied its old outside unit in H; the donor H-block decreases to at most19. Every other joint block is unchanged, and every root total is unchanged. This proves the claim. It also proves that all joint blocks of mass21 are unchanged by these repairs: none of the modified blocks can have been21.

Consequently start with any integral value77 flow on the actual source. While some dangerous block whose actual support fails T3 admits either the two-unit complement repair or a four-atom release above, perform one such repair. A root can have at most one dangerous block. Moreover dangerous blocks are disjoint sets of actual atoms and each carries20 units, so there are at most3 of them, since4*20>77. Each step strictly reduces their number and creates none. Thus this procedure terminates after at most3 repairs. Here T3 tests every three of the five literal child digits, including empty rows, against the entire actual fine support. It is a fixed source property and is not changed by the procedure.

At termination, every remaining dangerous block either already satisfies T3, or satisfies BOTH of the following explicit obstruction certificates:

- C=1, so its entire actual complement has the zero-prefix-plus-one-critical-prefix cover(UC2), with the budget bounds(UC3)--(UC4).
- Every eligible donor child's entire actual target-column neighborhood is contained in the same J_bad of at most2 digits, as in(UC5)--(UC6).

This is an unconditional finite normal form and certifier for the specified repair families. It is not a certificate that all global negative-cost cycles are absent. If no trapped non-T3 block remains, the known local T3 refinement applies to each remaining dangerous block; the already available treatment of full21 blocks remains applicable, yielding one actual law with Gamma<=691/77. Classifying or eliminating the simultaneously certified traps is still a genuine global cut77 gap.

### Exact controls

The [exact companion](../../frontier/cover-geometry/height_two_cut77_complement_transport.py) uses the two published adjacent68/164 fixture files and constructs the192-point source below directly from coordinates. Its [data](../../frontier/cover-geometry/height_two_cut77_complement_transport.json) require no external solver and are reproduced by

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut77_complement_transport.py
```

It recomputes actual integral flow capacities and480 selected literal pair tests for each source, enumerates EVERY multiset of two actual off-G points, compares feasibility with(UC1), and checks the repaired root, child, private and public budgets for every feasible lift. It includes previously zero actual points, and recomputes the192-point source's10000 complete literal tests and explicit cut/flow certificate.

| Actual source | C | Two-unit multisets | Feasible lifts | Eligible cross-root releases |
|---|---:|---:|---:|---:|
| published68-point source |58|91|91|3|
| published164-point forced20 source |1|630|0|0|
| new192-point nonrobust source |1|820|0|3|

The blocked164-point fixture has the critical common column0. The blocked192-point fixture has critical leaf(2,0) and zero column0. The companion also exhausts the actual donor/destination choices in(UC5)--(UC6) and verifies each resulting four-atom flow; the table's release counts refer to that specified family, not to all possible residual cycles.

For the68-point source the program deliberately puts the two outside units at(0,3,4,0). That child has NO actual point in target columnG=1. Delete an old G unit at(0,0,1,0) and replace the old outside unit. All other roots remain pointwise fixed. The resulting common law has the complete numerical LCM upper681/77<9. This verifies the different-child part of the construction; the original same-child transfer is not its implementation.

C=58 in this row must not be read as an achievable root throughput58. Only C>=2 is used, and the root retains total21.

The companion separately includes capacity-only boundary controls, without claiming literal blocking for them: one has J_bad exactly{0,1} and a donor whose two actual G neighbors are both forbidden; adding a third actual neighbor creates the stated release. Another makes the recipient child nonfull and checks that a saturated destination fine leaf can be handled by deleting from a different target-root child. These distinguish the active premises of the cross-root argument from the three source fixtures, whose J_bad sets happen to be empty.

### A nonrobust actual control: root-only blocking is not global blocking

Use occupancy(5,5,5,4,0), with full roots0,1,2 and gap root3. At EVERY occupied child put all seven leaves in column0 and the single public leaf(2,0). At root0/column1 use the bad support

    child0:0,1,2; child1:0,1; child2:0,1;
    child3:empty; child4:0,1,3,4.

At each child of roots1,2,3 include column1/fine leaf2; additionally include(2,0,1,5). At root1 child c include(3,c), at root2 child c include(4,c), and at gap child c include(2,c+1). There are192 distinct actual points.

For the bad flow put the old unique20 matrix in root0/column1 and1 at(0,0,2,0). At every child of root1 put2 at its column3 private leaf and2 at its column0 leaf h=c, giving root total20. Do the analogous thing at root2 using private column4, and add1 at(2,0,1,5), giving root total21. At each gap child put2 on its private(2,c+1) point; at gap children0,1,2 put2 on(2,0), and add1 at(3,0,0,5), giving root total15. Total flow is21+20+21+15=77.

There is an explicit cut consisting of public columns0 and1, public leaf(2,0), and the14 private leaf edges just described, of cost21+21+7+14*2=77. The actual bridge paths and every network cap are checked from the same source and flow in the companion. Hence its actual maximum flow and minimum cut are77.

Literal blocking can also be seen directly. Any root0 triple has both column1 fine digits0,1; the tested other root supplies digit2 there. The pair then has a full branch at column0, at column1, and at that other root's private column (3,4,or2). In the gap case the two private leaves together with public(2,0) give its required3 leaves. For pairs among roots1,2,3, column0 and their two distinct private columns supply the three branches. Adjoining the literal empty children/root gives the full product-blocking statement. Globally columns0,1,2,3,4 each have at least5 actual leaves, so the standalone five-ary tree exists.

No root is individually robust: root0 has only columns0 and1 capable of3 leaves; root1 has only0 and3; root2 only0 and4 (its column1 has at most2 leaves); the gap only0 and2. The companion also checks every singleton-root triple directly.

Every occupied root uses more than2 first-seven columns, excluding the common-plus-exclusive-private two-column-per-root class. Moreover all5 occupied first-seven columns occur at more than3 distinct child owners. In a WC1 witness any nonpublic column can be supplied by at most the two private-column owners and the one extra-leaf owner, hence at most3 owners. Five such columns cannot fit in its3 public slots. Thus the source has no WC1 cut witness. These exclusions concern the three specified source classes, not every possible known or future supplier.

The companion independently checks all480 selected pair tests, all10000 full literal tests, the standalone tree, and the1335-edge cut/flow certificate.

The fixed-other-root complement has C=1, critical leaf(2,0), zero column0. Nevertheless the ACTUAL four-atom cycle

    (0,0,1,0) -=1,    (0,0,2,0) +=1,
    (3,0,2,0) -=1,    (3,0,1,2) +=1

preserves every root, child and public coarse-column mass, changes root0/G mass20 to19, and gives a complete LCM upper689/77<9. Both flows satisfy every actual network cap. Thus the root-only bottleneck does not imply any of the three source classes, and cannot be substituted for the absence of a GLOBAL residual improvement.

This control does NOT refute the proposed genuine global dichotomy. It has an explicit global improving cycle. Its purpose is to pin the fixed-other-root quantifier and demonstrate that the remaining bridge really involves another root's positive flow and actual unused points.

### The precise global residual conditions and the remaining gap

For any fixed integral maximum flow, lowering the root mass a_r is possible at the same total77 exactly when the residual graph has a path from the global source S to r: append the used reverse root arc r->S to get a circulation. Equivalently S and r lie in the same residual strongly connected component. If there is no such path, the set reachable from S is an actual global minimum cut excluding r, so the source-root21 edge crosses it and ALL maximum flows saturate that root edge. Conversely any global minimum cut crossing that edge forces a_r=21 in every maximum flow.

For lowering d_(r,G), assign cost1 to actual bridges in the designated block and0 to all other original arcs; residual reverse arcs have the opposite cost. A feasible same-value flow with smaller d exists exactly when this residual graph contains a negative-cost directed cycle. The difference between two flows is a residual circulation and decomposes into cycles, so improvement forces at least one negative cycle; augmenting an integer unit on such a cycle supplies a feasible integral improvement. Absence of a negative cycle is equivalently a feasible residual vertex potential with nonnegative reduced cost on every residual arc. This is a global min-cost-flow certificate, not a single-edge mincut certificate.

These standard residual facts explain why simply uncrossing a local20 mincut with a global77 cut does not yet prove the desired source dichotomy. The local block total is the sum of several network arcs; it is not one root or public-prefix edge. The new(UC1)--(UC4) bridge handles all residual improvements that hold the other roots fixed and restricts the actual complement if those fail; (UC5)--(UC6) then supply a class of actual cross-root repairs or a common two-digit neighborhood trap among their eligible donors. The192-point control shows exactly why a further cross-root closure argument remains necessary.

Also T3 is a property of the ENTIRE actual block support. Changing only the flow on a fixed source cannot make that same support satisfy T3. A correct global alternative is to remove the dangerous(a,d)=(21,20) status, or to choose a flow whose remaining dangerous blocks already have the requisite actual-support property.

Still unproved: if a literal cut77 source admits no global reduction of a or d for a selected bad-neighborhood block, whether the simultaneous residual closure and(UC2)--(UC4) force WC1, three robust roots, the restricted common/private class, some different known supplier, or a genuinely new supplier. No general cut77 closure follows from this note.

## Three cut77 strata with one inactive full root

This is an ordinary deduction in the actual Report449 network, not a Lean verification and not a closure of general cut77. Retain the literal4555 blocker and standalone five-ary seven-tree premises. Suppose the actual network has minimum cut77 and admits a normalized minimum cut with one full root inactive, the other two full roots and all four occupied children of the gap root active, public integer cut cost4, and total private integer cut cost14. In raw units the cut is

    21 + 7*4 + 2*14 = 77.

The active child counts, in the order inactive full / full / full / gap, are(0,5,5,4). This does not delete the inactive root from the source or assume that its deletion preserves blocking.

Then the source admits an integral value77 flow with NO root21/joint20 block. Consequently the existing(SH1) full-block repair supplies one actual probability law with

    Gamma_1225 <= 691/77 <9.                         (PF77)

The proof uses at most one two-unit complement repair. It does not require T3 at the initial dangerous block and does not require three robust roots, WC1, or a two-column-per-root source classification.

### The private cut must consist of fourteen singleton leaves

Let p1,p2 be the sums of the three smallest private costs at the two active full roots, and p3 the sum of the two smallest costs at the gap. Literal pair blocking and public cost4 imply

    p1+p2>=5,   p1+p3>=5,   p2+p3>=5.

These are the standard selected-pair prefix-cost inequalities: a ternary depth-two tree cannot be covered with unweighted integer prefix cost below9. Let the three private total costs be Z1,Z2,Z3. Sorted nonnegative child costs imply

    Z1>=ceil(5p1/3), Z2>=ceil(5p2/3), Z3>=2p3,
    Z1+Z2+Z3=14.

If p3<=1, both full p-values are at least4; for p3=1 the cost is at least7+7+2=16, and for p3=0 it is at least9+9=18. If p3>=3, the constraint p1+p2>=5 implies Z1+Z2>=9, so the total is at least15. Thus p3=2, forcing p1,p2>=3. Total14 then forces

    (p1,p2,p3)=(3,3,2),   (Z1,Z2,Z3)=(5,5,4).

Equality for sorted lists of lengths5,5,4 forces every individual cost to be1. For example a full-root list with smallest-three sum3 and total5 cannot have third entry at least2, because its total would be at least3+2+2=7; hence the first three and final two entries are all1. The gap argument is identical with two entries in each half.

Therefore each active child has exactly one private cut leaf. Its actual fibre is contained in that one candidate label together with the public cut support P. A candidate is not initially assumed actual. The public antichain P is either four leaf labels or one whole column G plus one leaf y outside G.

### Tight pair tests determine the entire active support

Test any gap pair against any triple at an active full root. There are exactly five private candidate occurrences.

If P is a whole column G plus y, the actual projection outside G has at most six candidate leaves. A ternary tree must use G, then use exactly six distinct actual outside leaves in two other columns of three. Thus all five private candidates and y are distinct, outside G and actual in the tested union. A private candidate is actual at its OWN child: it is outside P and distinct from every other selected private candidate, so containment forbids any other selected child from supplying it.

Exchanging one child in a full-root triple while retaining the other two and the gap pair changes the outside-column count vector by a difference of coordinate unit vectors. Both vectors have all coordinates divisible by3, so the two exchanged leaves have the same column. All five full-root private leaves lie in one column H_i. Exchanging one child in a gap pair while retaining the other child and a full triple proves the same statement for all four gap leaves, in a column K. The selected gap pair plus y fills one three-leaf branch, so K=col(y), different from G and H_i.

If P consists of four leaves, each gap/full test has exactly nine candidate occurrences. A ternary tree forces all nine distinct and actual, with exactly three leaves in each of three columns. The same exchange argument locks all four gap leaves into K and each full-root family into H_i. K and H_i differ, since otherwise the five selected private leaves already occupy one column and cannot belong to a nine-leaf ternary tree. The fixed public vector is necessarily one leaf y in K and three leaves in one further column G, different from K and both full private columns.

In either public case, H1 and H2 differ: if they agreed, the full/full triple test could use only that shared private column and G as full three-leaf branches; the public K contribution is only y. Every private family consists of distinct actual leaves at its own children, outside P. Thus G,K,H1,H2 are four distinct columns, and the entire active source has the following containment:

- full root i: public P plus its five private leaves in H_i;
- gap: public P plus its four private leaves in K, all different from y.

No location or support restriction has been placed on the inactive full root.

### Every maximum flow has the same other-root coarse masses

Take an integral maximum flow of value77. The cut has cost77, so every forward cut arc is saturated and every backward crossing arc carries zero flow. The inactive source-root arc contributes21. The fourteen private leaf arcs each contribute2. The public cut contributes28.

In a normalized cut, the inactive root's subtree is on the sink side. Its actual bridges to public cut support would run backward across the cut, so its flow on P is zero. Thus all28 public cut units come from the three active roots. Each saturated private leaf receives exactly2 units at its actual owner; all those fine labels are distinct outside P.

It follows that the OTHER three roots, jointly, have the exact coarse masses

    G:21,   K:15,   H1:10,   H2:10,               (PF-mass)

and zero mass in every other column. In the finite-four-leaf case, the G mass21 consists of its three saturated public7 leaves. In the whole-column case it is the saturated public-column21 edge. The K mass is the public y mass7 plus the four private gap leaves of mass2 each. The H_i masses are the five private leaves of mass2 each.

Each of these three roots has every joint root/column block at most15. At a full root its H_i block is10, its G block at most21-10=11, and its K block at most7. At the gap its K block is at most8+7=15 and its G block at most21-8=13. This statement holds without prescribing how the public mass is shared among those roots.

### The only possible dangerous block has a direct repair

The inactive root has mass21 because its source-root arc is saturated. If it has no joint block20, the entire flow already satisfies(SH1)'s premise, since the active roots' blocks are at most15.

Otherwise let its unique block20 be in column J. From(PF-mass), the residual public coarse capacities available to this root in G,K,H1,H2 are respectively0,6,11,11. Therefore J is outside those four columns. There is exactly one outside atom p=(r,rho,H,k), of mass1.

That atom cannot use G or y because their public capacities are saturated by the other roots. On every other actual fine leaf, the other roots have either0 or2 units; hence the residual fine capacity at p is at least5. The residual coarse capacity at its column H is at least6. In particular, TWO units can be placed at the very same actual outside point p with all public and entry capacities valid.

Add1 at p and delete1 from an old positive J atom. If rho's old J row has6, delete in that same row; otherwise delete from any positive J atom. Such an atom exists in the required row in the first case, and somewhere in J in the second. The only possible child conflict is thereby avoided. The resulting root mass stays21, the J block is19, and all its outside blocks together have mass2. Every other-root atom stays fixed. All private and public capacities hold.

No dangerous block remains anywhere. Original blocks of mass21, if any, were not touched and are handled by the existing(SH1) repair. This proves(PF77). The argument is a restricted source theorem: it uses this one inactive-full-root/public4/private14 cut profile and does not assert that every cut77 source has such a profile.

### The adjacent public2/private21 profile is impossible

Keep the same one-inactive-full-root active counts(0,5,5,4), but suppose a normalized cut77 has public integer cost2 and private total21:

    21 + 7*2 + 2*21 =77.

No literal4555 source admits this cut profile.

Here the selected private costs satisfy pair bounds p_i+p_j>=7. For a sorted five-child list whose three smallest entries sum p, its total is at least p+2*ceil(p/3). For a four-child list whose two smallest entries sum t, its total is at least t+2*ceil(t/2). These bounds use the largest selected entry to bound every unselected entry.

For t=0,1,2,3 the three-root total is at least26,23,22,23 respectively, since each full p-value must be at least7-t. For t>=5, the full p-values sum to at least7, so their total cost is at least13; the gap cost is at least11, giving at least24. Thus t=4. Equality at total21 then forces the two full p-values to be3 and4, with total costs5 and8, and gap total8. The only sorted child-cost shapes are

    11111 / 02222 / 2222,
    11111 / 11222 / 2222,

up to exchanging the two full roots. Every private cut is finite: all individual costs are0,1 or2. P is exactly two public leaves.

Call the11111 full root clean. Pair any clean triple with any gap pair. The union is contained in public2 plus clean3 plus gap4 candidate occurrences, exactly9. Literal blocking forces all nine distinct actual labels in three columns of three. Each private candidate is actual at its own owner by exact distinctness and cut containment.

Exchanging a clean child while fixing the other two and the gap pair locks the clean singleton family into one column H. Therefore P and each gap pair supply the other two three-leaf columns, and none of these six labels lies in H.

For a gap child c, let v_c be its two-candidate column-count vector. Exchange c with d while retaining another gap child and a clean triple. The resulting complete count vectors are divisible by3 in every coordinate, so v_c-v_d is coordinatewise divisible by3. But every coordinate of v_c and v_d is between0 and2. Hence v_c=v_d. All four gap children have the same vector v.

Now P+2v has every coordinate0 or3 and total6. If the two private candidates of one gap child lay in the same column, that coordinate of2v would already be4, impossible. Thus v has value1 in two different columns K,L. The two public leaves must contribute one in K and one in L, yielding3 in each. K,L differ from H. Every gap child's ENTIRE actual support is contained in K union L, because its private candidates and P are all there.

At the exceptional full root choose a legal triple whose private total is4: its zero child and any two doubles for02222, or its two singletons and any double for11222. Test this triple against a clean H triple. Again P2 plus private4 plus clean3 is exactly9. The H triple already fills its branch, while P supplies one label in K and one in L; the exceptional candidates must supply the missing two labels in each of K,L. Thus the ENTIRE actual union of this exceptional triple is contained in K union L.

Pair that same exceptional triple with any gap pair. Their actual projection is contained in only the two columns K,L, contradicting the required ternary tree. This excludes both private shapes and proves impossibility. The inactive root was never removed from the source; these tests are legal root-pair restrictions of the original literal hypothesis.

Together these results handle public costs2 and4 for this active profile. The next result handles the finite-private part of public0/private28; whole-private-column variants and other active profiles remain outside these conclusions.

### Public0/private28 also closes when every private cut is finite

Keep the same one-inactive-full-root active profile and suppose the normalized cut77 has NO public cut and consists of the inactive source-root21 edge plus28 private LEAF edges of capacity2. The qualifier matters: a private whole-column edge of capacity6 is not covered by this statement.

Take an integral maximum flow77. All28 private leaf edges are saturated and every active source point lies below one of them. Each such edge has a unique actual bridge to its public fine leaf. Hence the active source has exactly28 actual points and EACH carries2 units. In particular every active root has an even total at most20; none can be dangerous. All public coarse and fine masses contributed by those roots are even.

The inactive root has21 units. If it has no block20, apply(SH1). Otherwise let its unique dangerous block be J. The other roots have at most1 unit in J by the public21 cap. But any actual point of an active root would carry2, so there is NO actual J point at any active root, not merely no positive J mass.

If the entire actual J support satisfies T3, the existing actual-neighborhood mass20 refinement applies, giving the same bound691/77. Here T3 means every triple of the five literal child digits has at least three actual J fine neighbors. This is a property of the source, not of positive support.

If T3 fails, choose a legal triple at the inactive full root whose actual J neighborhood has at most two digits. I claim that the two-unit complement condition C>=2 must hold. Suppose instead C=1. Since all other-root public masses are even and the public capacities21 and7 are odd, no public prefix has residual capacity0. The(UC2) cover therefore contains no zero-prefix part. The ENTIRE inactive-root support outside J lies in its one critical prefix, which in either case is contained in a single column H different from J.

Now test the selected bad triple against ANY pair of occupied gap children. The gap has no actual J point. Thus J cannot be a three-leaf branch of this pair projection. The inactive triple has no points outside H or J. A ternary tree therefore needs at least TWO other columns, each with at least three leaves, contributed entirely by the selected gap children outside H and J. The gap pair contains at least six actual points outside H.

Let n_c count the actual points outside H at gap child c. Every one of its six child pairs satisfies n_c+n_d>=6. Summing gives

    3*(n_0+n_1+n_2+n_3)>=36,
    n_0+n_1+n_2+n_3>=12.

Each of those actual points carries2 in the maximum flow, forcing gap mass at least24, contrary to its root cap21. This contradiction proves C>=2. The two-unit complement repair removes the inactive root's dangerous block while holding every active atom fixed. There is then no dangerous block anywhere, so(SH1) applies.

Thus every source in this finite-private public0 stratum admits one actual law with Gamma<=691/77. The proof offers a genuine alternative: an already T3 dangerous block uses the known local refinement; a bad-T3 block must admit the actual two-unit complement reroute. It does not assert that the two-unit criterion holds for every T3 block, or that whole private-column cuts have even atomic flows.

### Exact actual controls

The [self-contained program](../../frontier/cover-geometry/height_two_cut77_partial0554.py) and [exact data](../../frontier/cover-geometry/height_two_cut77_partial0554.json) construct both public forms and the finite-private public0 source, checking the corresponding arguments on actual sources. It exhausts15573 sorted nonnegative private-cost triples of lengths5,5,4 and total14, without imposing an artificial upper bound3 on individual costs. The unique survivor of all three pair inequalities is11111/11111/1111. It separately enumerates239590 sorted triples for the public2/private21 case and checks exactly the four ordered versions of the two impossible shapes above; the ordinary tight-pair proof, rather than a fabricated actual source, supplies their impossibility.

Use labels G=0,K=2,H1=3,H2=4,J=1. At the three active roots put the common public G support and y=(2,0) in every occupied child. Private points are(3,c) at root1, (4,c) at root2, and(2,c+1) at gap root3. The common public support is either all7 G leaves or its leaves0,1,2.

At inactive full root0, put all7 leaves in every column except J, at each of its5 children. At J use the actual bad-neighborhood support

    child0:0,1,2; child1:0,1; child2:0,1;
    child3:empty; child4:0,1,3,4.

This gives347 source points for a whole public column and291 for four public leaves. The target block fails the actual T3 condition at child triple(1,2,3), whose target-column neighborhood is only{0,1}. Root0 is the sole individually robust root. Every column occurs at more than3 child owners, excluding WC1 by its nonpublic-owner budget; the source also lies outside the common-plus-exclusive-private two-column-per-root class.

Put the standard unique20 matrix in root0/J and one outside unit at(0,0,2,1). Put2 at every active private point. At active full root1 put common G masses2 at(c,h)=(0,0),(1,1),(2,2),(3,0); at full root2 use(0,0),(1,1),(2,2),(3,1). Give each full root one y unit at each of children0,1,2. At the gap put G masses1,1,2,1 at(0,0),(1,1),(2,2),(3,2), and one y unit at child0.

The resulting root totals are21,21,21,14. Its three active-root G fine totals are7,7,7, and its y total is7. The explicit cut comprises the inactive source-root21 edge, the public28 antichain and the fourteen private2 edges, for77. The program builds the complete actual network and verifies every capacity, all vertex balances, forward cut saturation and zero backward cut flow, establishing matching flow and cut77. It also checks480 selected pair tests and10000 full literal tests per source, plus the standalone five-tree and exact robust-root inventory.

The repair is simply

    (0,0,1,0) -=1,    (0,0,2,1) +=1.

For both controls, the separate-cylinder LCM envelope changes from698/77 to689/77. The latter is an exact stronger bound for these controls; the general stratum bound691/77 comes from(SH1), not from asserting that every source attains the same envelope. Program execution:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut77_partial0554.py
```

A third control has no public cut. At active root1 put(0,c),(1,c) in child c; at active root2 put(2,c),(3,c); at gap child c put(4,c),(4,c+1). These are28 actual points, all carrying2. Their root totals are20,20,16 and their public column totals are10,10,10,10,16. At inactive full root0 use every fine leaf in every column except J=5 at all five children, together with the same bad20 support in J. Put the bad20 flow there and one outside unit at(0,0,0,0). The source has249 points, one robust root, the same bad T3 child triple, and an explicit matching cut/flow77 made from the inactive root21 edge and28 private2 edges. All480 selected pair tests,10000 literal tests, standalone tree, full network balances and capacities are checked. Doubling the old outside atom and deleting one at(0,0,5,0) gives an exact separate-cylinder envelope683/77, compared with695/77 before the repair. This control establishes nonvacuity of the finite-private public0 theorem; its stronger numerical bound is not claimed uniformly for that entire stratum.

It uses no external solver or unpublished fixture. The source theorem above is an ordinary proof; these finite controls verify its nonvacuity and implementation, not Lean formalization.

## The entire one-inactive-full-root cut77 profile admits a law below nine

This is an ordinary source theorem assembled from the established Report449 interfaces and the actual-support deductions below. It is not Lean verification and does not settle every cut77 source.

Retain the original literal4555 blocker and standalone five-ary seven-tree premises. Suppose the actual network has minimum cut77 and admits a normalized minimum cut with one full root inactive and every occupied child of the other two full roots and the gap active. In root order inactive full / full / full / gap, its active counts are(0,5,5,4). There are no partial-child cut edges at the active roots.

Then there exists ONE actual probability law, chosen before every arithmetic layout, satisfying

    Gamma_1225 <=691/77 <9.                         (IF77)

The inactive root remains part of the actual source. No assertion that deleting it preserves blocking is used.

### Public costs reduce the question to the private-only shapes

Write the public antichain cost as7k and private cost as2Z. The one inactive full-root edge costs21, so

    21+7k+2Z=77.

Thus k is one of0,2,4,6,8.

For k4/Z14, the already proved singleton locking theorem gives exact external coarse masses21,15,10,10 and an actual two-unit repair for the only possible dangerous block, followed by(SH1).

For k2/Z21, the only private shapes are11111/(02222 or11222)/2222, up to full-root exchange. The fixed public-two-leaf/tight-nine argument puts the relevant gap pair and exceptional full triple in the same two columns, contradicting literal pair blocking. This profile is impossible.

For k6/Z7, let p1,p2 be the smallest-full-triple costs and t the smallest-gap-pair cost. All pair sums are at least3. Sorted costs give Z_i>=ceil(5p_i/3) at each full root and Z_gap>=2t. If t0, both p-values are at least3 and total cost is at least10. If t1, both are at least2 and the total is at least4+4+2=10. If t2, both are at least1 and their sum at least3, so their rounded total is at least2+4=6, giving at least10. If t>=3, the full pair-sum alone gives total full cost at least5, while the gap costs at least6. Every case exceeds7. For k8/Z0, zero private costs contradict the pair lower bound1. These profiles are impossible.

It remains to close k0/Z28.

### The eight private-only cost shapes and what they require

At a minimum cut an active child's private integer cost z is at most3: for z>=4, replace raw cost2z by its incoming edge7 and obtain a smaller cut. An active root has private total at most10, either by the same replacement with its incoming edge21 or by saturation and its flow cap. Pair sums of the least selected private costs are at least9.

The [exact shape enumerator](../../frontier/cover-geometry/height_two_cut77_whole_private_shapes.py) with [shape and overlap data](../../frontier/cover-geometry/height_two_cut77_whole_private_shapes.json) gives eleven ordered shapes, or eight up to full-root exchange:

| Row | Full1 | Full2 | Gap | Treatment |
|---|---|---|---|---|
|1|12222|12222|1333|all-finite law; any whole gap column impossible|
|2|12222|12222|2233|impossible for every cost3 realization|
|3|12222|12223|2223|impossible for every cost3 realization|
|4|12222|22222|2223|impossible for every cost3 realization|
|5|12223|12223|2222|impossible for every cost3 realization|
|6|12223|22222|2222|impossible for every cost3 realization|
|7|22222|22222|1223|all-finite law; whole gap column handled below|
|8|22222|22222|2222|all-finite law|

Cost3 has two possible normalized realizations: three leaf edges or a whole-column edge. They cannot be interchanged silently. The all-finite theorem already supplies691/77 whenever ALL private cuts are leaf edges: all active actual points then carry2, public masses are even, and a bad-T3 inactive-root block with C1 would force gap mass at least24.

### Row1 with any whole gap column is impossible

In the first row, if AT LEAST ONE of the three cost3 gap cuts is a whole-column edge, the literal blocker is impossible. No assumption is made about the realizations of the other two gap cost3 cuts.

At the gap let z denote its singleton cut candidate, and choose one whole-column child with column W. Each active full root has one singleton candidate w and four two-candidate children. There is no public support: every singleton/double child's ENTIRE actual fibre is contained in its own one/two candidate labels; the selected whole child is contained in W.

Fix one active full root. Test the gap pair consisting of its singleton child and the selected whole W child against the full triple consisting of its singleton child and any two of its doubles. Outside W there are at most SIX candidate labels: z, w and the four double labels. A ternary tree must use W, since otherwise it would need nine outside leaves. Its other two branches need exactly six distinct actual outside labels, divided into two groups of three. Therefore ALL SIX candidates lie outside W, are mutually distinct and actual in this selected projection.

Each is actual at its OWN child. It is outside W; and its label differs from all the other selected private candidates, so containment prevents another selected child from supplying it. This simultaneously proves z and w actual, outside W, and every candidate of each double actual at its owner. Each double is included in such tests.

Let v_c be the column-count vector of the two labels at full double child c. Exchange one double child c for d while keeping the singleton w, the other selected double and the fixed gap pair. Both six-label outside count vectors have every coordinate0 or3. Thus v_c-v_d is divisible by3 coordinatewise. Each coordinate of the difference lies between-2 and2, so it vanishes. All four doubles have the SAME count vector v.

The two labels of a double cannot lie in one column, since then the selected pair would put four labels there, incompatible with the0-or3 count vector. Thus every double has one label in each of two distinct columns H,L. The two fixed singleton labels z,w must supply one additional label in each column. Set H=col(z); then w lies in L. In particular W,H,L are distinct.

Repeat for the other active full root. Both full roots have the SAME H=col(z); call their other columns L1,L2. If L1=L2, the entire support of both full roots would be contained in H union L1. Their literal full/full pair test could not have three branches. Hence L1 and L2 differ.

At each full root, its four double H labels are distinct: any pair of double children participates in the tight-six test. They all differ from z. Thus there are two four-element subsets A1,A2 of the six seven-digits in H different from z. Consequently

    |A1 intersect A2| >=4+4-6=2.

Choose two common H labels. At EACH full root select the two double children that own them, together with its singleton child. The entire actual projection of this legal full/full pair is contained in:

- column H, with exactly those TWO common fine labels;
- column L1, with at most its singleton plus the two selected double labels;
- column L2, with at most its singleton plus the two selected double labels.

All selected fibres were already proved equal to their actual one/two candidate labels, so no hidden extra branch can occur. H has only two leaves. Only L1 and L2 can be ternary branches. This contradicts the required ternary tree and proves the exclusion.

The proof uses one whole-column gap child solely as an anchor for the exact outside-six tests. It does not silently interpret the other two cost3 cuts as whole columns, and it does not infer this exclusion for the all-finite realization from the same argument. The previously obtained finite-private law theorem remains the applicable conclusion for all-finite realizations.



### Row2 is impossible, independently of both unused cost3 cuts

Fix the two cost2 gap children. Their four candidate labels are distinct and actual because pairing them with a full singleton and any two full doubles gives exactly9 candidate occurrences. A ternary tree forces all9 distinct actual labels in three columns of three. Every selected private label is actual at its own owner: there is no public support, it differs from all other selected candidates, and containment excludes any other owner.

Let v be the fixed four-label gap column-count vector. At one full root, let w be its singleton column and u_c the two-label column vector of double child c. Exchanging one double while keeping the other double and the gap pair fixed shows u_c-u_d is divisible by3 coordinatewise. Its coordinates lie in[-2,2], hence all u_c equal one vector u. A double cannot place both labels in one column, because2u would already have coordinate4 in a ternary-nine count. Thus u has value1 in two different columns.

The tight count equation is

    v+e_w+2u =3*(three different column indicators).

There are exactly two possibilities for v.

**v has multiplicities(2,1,1).** Its double column K must contain the full singleton; its two singleton columns H,L must contain the two leaves of every full double. Both full roots therefore have singleton in K and doubles in H,L. Select the singleton plus two doubles at each full root. Their union has at most2 K leaves and can have full branches only in H,L, contradiction.

**v has multiplicities(3,1).** Write v=3e_K+e_L. Every full double lies in L and a new column H_i; the full singleton lies in H_i. If the two H_i agreed, both full roots would have support in only H_i,L, already contradicting literal blocking. Thus H1,H2 differ. Each full root's four double L labels are distinct and avoid the one fixed gap L label, by the tight-nine tests. Their two four-element subsets of the remaining six L digits share two labels. Select those two double owners plus the singleton at each full root. L now has only2 leaves, and only H1,H2 can be full ternary branches, contradiction.

These two cases exhaust v: if w is one of u's two columns, subtracting e_w+2u from the three3-counts leaves(3,1); otherwise it leaves(2,1,1). The program independently checks all315 labelled solutions of this vector equation. Both other gap cost3 children were unused, so their finite/whole realization is irrelevant.

### A parity obstruction excludes rows3 through6

The following local configuration is impossible: at least three gap cost2 children, together with a full root having a singleton and at least three cost2 children. This applies to each of rows3,4,5,6 and does not use any cost3 child.

Choose any two of those gap doubles and pair them with the full singleton plus any two full doubles. The total candidate count is4+1+4=9. Literal blocking forces exactly three columns of three distinct actual leaves. Exchange one full double while fixing the other selected children; all full double column vectors must agree, since their coordinate differences lie in[-2,2] and are divisible by3. Independently exchange a gap double while fixing the other selections; all gap double vectors likewise agree. There are enough children to keep the partner fixed in each exchange.

Write these common vectors as u and v and the singleton indicator as e_w. The complete column count is

    2u+2v+e_w.

It has exactly ONE odd coordinate, at w. But three columns of three have exactly THREE odd coordinates. This is impossible. The argument concerns all selected actual fibres by exact-nine ownership, not just an abstract column-count relaxation.

### Row7 with a whole gap column has no zero fine residual

Only one cost3 child occurs in row7, at the gap. If it is finite, use the all-finite theorem. Otherwise write its whole-column support as W. Let z be the gap singleton, and E1,E2 its two double candidate sets.

For either i, the gap pair z+Ei contributes3 candidates; any full triple contributes6. Their exact-nine test forces all labels distinct and actual at their own owners. Exchanging a full double within a triple locks all five full double column vectors together. Each double has one leaf in each of two columns H_i,L_i; placing both in one column would produce6 leaves in a branch of a nine-leaf ternary tree. The full triple already contributes3 to each column, so z and Ei are three distinct leaves in one other column K=col(z).

Thus both E1,E2 lie in K, each has two distinct leaves different from z, and each full root is entirely supported in its own two columns outside K. Within either full root, its five H labels are distinct and its five L labels are distinct: any pair of its children occurs in an exact-nine triple. The two full column pairs are not identical, since otherwise their full/full test would have only two branches.

The whole gap column W is outside BOTH full column pairs. Indeed if W were one of a chosen full root's columns, test the gap pair z+whole against a triple at that full root. Its projection would contain only the two full columns and the lone K leaf z, so no third ternary branch. W may equal K or be different from it.

Now take any integral maximum flow77. Every finite private leaf carries2, and the whole gap column carries6 spread over its actual entries, each at most2. The two active full roots have20 each and the gap has16. No active root can be dangerous.

Every other-root PUBLIC FINE mass is at most6:

- In a full-root column, each full root supplies at most2 at a fine label because its five labels there are distinct. At most two full roots share that column, so the total is at most4. The gap cannot contribute there.
- In K, the finite gap points give at most4 at any fine label: E1,E2 may overlap, but z belongs to neither. If W=K, its one whole-child entry adds at most2, yielding at most6.
- If W differs from K, only the whole child contributes to W, with each fine entry at most2.

All other-root coarse column masses are even: each finite prefix contributes2 in one column and the whole prefix contributes6 in one column. Hence they are at most20, and every public coarse residual is positive. The preceding fine bound makes every fine residual positive too. There is NO zero-residual public prefix.

The inactive root has21. If it has no block20, apply(SH1). Otherwise let its block20 be J. The active roots have at most1 mass in J, but an actual J point would belong either to a saturated finite2 prefix or to the saturated whole6 prefix in that column. Therefore there are NO active actual J points. If the entire actual J support satisfies T3, use the existing mass20 actual-neighborhood refinement.

If T3 fails, choose an inactive-root child triple with at most2 actual J digits. Suppose the two-unit criterion fails, C1. With no zero residual prefix, its(UC2) actual support cover says the inactive root's entire off-J support lies in one column H. Pair the bad triple with the gap singleton and either double. This gap projection lies entirely in K. The complete projection can have full ternary branches only in H and K: J has at most2 leaves and the gap has no J. Contradiction.

Thus C>=2 and the actual two-unit complement repair removes the sole dangerous block, keeping all active atoms fixed. Then(SH1) gives691/77. This proves row7's whole realization and completes every k0 shape.

Combining all public costs proves(IF77). This closes the entire specified active profile, while other cut77 active profiles and the unrestricted odd-covering problem retain their original unresolved status.

### Exact controls of the remaining vector equation and actual whole-column sources

The [self-contained program](../../frontier/cover-geometry/height_two_cut77_whole_private_row7.py) with [exact data](../../frontier/cover-geometry/height_two_cut77_whole_private_row7.json) exhausts the315 labelled row2 vector solutions and constructs two actual row7 sources, one with W=K and one with W different from K. Each has253 points.

At active full root1, child c contains(0,c),(1,c); at full root2 it contains(2,c),(3,c). The gap singleton is(4,0), its doubles are{(4,1),(4,2)} and{(4,3),(4,4)}, and its whole child has all seven leaves in W=4 or W=6. The inactive full root0 has all fine leaves in every column except J=5 at all five children, and the established bad20 support in J. The actual points at its child triple(1,2,3) have only two J neighbors, so T3 fails initially.

Give2 units to every active finite point and2 to each whole-child fine leaf0,1,2. The active root totals are20,20,16. Put the bad20 matrix at inactive root0/J and one outside unit at(0,0,0,0). The explicit cut consists of the inactive root21 edge,25 finite private2 edges and one private whole-column6 edge:

    21+25*2+6=77.

The complete network replay verifies the matching integral flow77, every edge capacity, all conservation equations, cut saturation and zero backward cut flow. Each source passes480 selected pair tests,10000 complete literal tests, the standalone five-tree and the exact robust-root inventory(one robust root, namely the inactive root0). It recomputes the claimed absence of zero fine residual after subtracting root0.

Increase the old outside atom by1 and delete1 from(0,0,5,0). In BOTH controls the separate-cylinder envelope falls from695/77 to683/77, and the repaired integral flow has no dangerous block. This is a stronger control-specific bound; the uniform active-profile statement remains691/77.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut77_whole_private_shapes.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut77_whole_private_row7.py
```

These programs use no external solver or unpublished fixture. The eleven/eight private-cost inventory and225 overlap controls from the prior shape program are reused, not recounted as new independent cases. These finite checks support the ordinary proofs and actual examples; they do not constitute Lean verification.

## Cut72: sparse laws, partial public cuts, and local support obstructions

This section gives ordinary source proofs for ten of the fourteen necessary cut72 profile families, counting full-root permutations as one family. A controlled family has a single actual law below nine; an impossible family has no source satisfying the literal premises. The four other families remain outside these results. This is not a complete cut72 theorem or an original-cofactor lift.

### Complete necessary profile inventory

Use root order gap/full/full/full, N=(4,5,5,5) and selected counts q=(2,3,3,3). A node-minimal normalized minimum cut has active counts from (0,2,3,4) at the gap and (0,3,4,5) at a full root. If a root is inactive its top cost is21; otherwise each inactive occupied child costs7. Write T for this top cost divided by7, k for the public antichain cost divided by7, and Z for private cost divided by2. Then

    7(T+k)+2Z=72.

Each active child's integer private cost is between0 and3; when k=0 nonemptiness requires at least1. Replacing an active root subtree by its source-root edge gives the strict node-minimal inequality

    7(N_r-a_r)+2Z_r <21.

For each two active roots the sums of their cheapest legal selected private costs obey p_r+p_s>=9-k. If all roots and children are active, standalone also requires k+Z>=15. The [profile enumerator](../../frontier/cover-geometry/height_two_cut72_profiles.py) and [exact inventory](../../frontier/cover-geometry/height_two_cut72_profiles.json) exhaust these bounded integer conditions:24 labelled profiles,14 families under full-root permutations,76 labelled shape rows and54 canonical shape rows. Within each labelled active profile, permutations of full roots with the same active count have already been quotiented in the private-shape rows. They are necessary possibilities; the enumerator does not assume their actual realizability.

| Active counts | T | k | Z | Canonical private shapes | Result in this section |
|---|---:|---:|---:|---:|---|
|0005|9|1|1|1|33/4 law|
|0055|6|0|15|1|173/21 law|
|0555|3|3|15|1|1214/139 law|
|3555|1|3|22|7|not settled here|
|3555|1|5|15|1|impossible|
|3555|1|9|1|2|643/72 or1603/195 law|
|4000|9|1|1|1|33/4 law|
|4455|1|3|22|5|not settled here|
|4455|1|5|15|1|impossible|
|4455|1|9|1|3|643/72 or1603/195 law|
|4555|0|0|36|3|impossible|
|4555|0|2|29|3|impossible|
|4555|0|4|22|22|not settled here|
|4555|0|6|15|3|not settled here|

The family0005 has three labelled positions,0055 has three, and each4455 family has three. Other displayed families have one. The proof below retains actual owners and common numerical labels throughout; relabeling full-root roles is only the stated classification symmetry.

### Four sparse cut72 profiles have same-source laws below nine

Scope: the actual literal4555 height-two source and Report449's prefix-normalized minimum cut, with raw minimum72. Root order is gap4/full5/full5/full5. This is an ordinary proof with finite exact construction controls, not Lean verification or a common outside-cofactor lift. All atoms remain at their original actual owners. Every law is selected before the numerical query phases.

Use numerical divisor order `(1,5,7,25,35,49,175,245,1225)` and LCM multiplicities `(1,3,3,5,9,5,15,15,25)`.

#### Single active root:0005 or4000, public1/private1

There is one public leaf y. Four of the five active full-root children, or three of the four active gap children, have private cost zero. Their nonempty actual fibres are exactly `{y}`. Fix a legal triple or pair among these zero-cost children. Its projection is exactly `{y}`; the one cost1 child and all its points remain in the source but are not used.

At any other root s, pair this fixed selection with ANY legal q_s-child restriction. Literal blocking supplies a ternary seven-tree. Removing y leaves at least8 actual leaves from the selected children at s. Uniform mass on those8 or9 leaves has column cap3/8 and leaf cap1/8. Lift each leaf to any actual owner among the selected children, average over all legal restrictions at s, and then mix the other three roots equally. A fixed child is included with probability at most3/5 (a gap child has the smaller probability1/2). Thus the simultaneous cap vector is

    (1,1/3,3/8,1/5,1/8,1/8,3/40,1/24,1/40).

Its LCM envelope is33/4. This is the existing punctured-tree construction applied to an actual zero-cost restriction, rather than an assumption that the entire active root has singleton projection. Standalone is not used.

#### Two active full roots:0055, public0/private15

The sorted private shapes are11111 and22222. Call the singleton root A and the doubled root B. Any triple from each has exactly9 candidate occurrences, so a required ternary tree makes them all actual at their own owners, distinct within the selection, and gives a column-count vector with entries0 or3.

Exchanging one singleton forces all five A labels into one column H, pairwise distinct. Exchanging one doubled child forces each B child's column-count vector to be the same two-vector; pairing with A makes it one leaf in each of two distinct columns J,K outside H. In each of J,K its five labels are distinct. This is the same tight-nine exchange as the cut71 three-full-root stratum; only one doubled root is needed here.

Let C be the other full root and D the gap root. For every legal triple at C or pair at D, pair it with a fixed A triple. A ternary tree in the combined projection has at least two three-leaf branches outside H. Select two such branches. Their six leaves are all actual at the selected C or D children, since the A triple lies entirely in H. The uniform six-leaf law has column cap1/2 and leaf cap1/6.

Apply Report443's one-flow theorem to these ACTUAL outside-H incidences. At C use `(m,q)=(5,3)` and at D use `(4,2)`. It yields one local probability at each root with child cap1/3, column cap1/2 and leaf cap1/6. At C the joint child/column and child/leaf caps are3/10 and1/10; at D they are1/4 and1/12. These are simultaneous caps on one probability per actual root, not separate marginal optimizations.

Mix the uniform five-point A law with weight1/7, the uniform ten-point B law with weight2/7, and the C,D laws with weight2/7 each. Every law except A is supported outside H. The resulting cap vector is

    (1,2/7,3/7,2/21,1/7,13/105,3/35,1/21,1/35).

For example, outside H the leaf cap is `(2/7)(1/10+1/6+1/6)=13/105`; the H leaf cap is only1/35. Child/column cap3/35 comes from C. The envelope is

    173/21 <9.

Neither standalone nor any additional relation between J,K and the other-root supports is used.

#### Three active full roots:0555, public3/private15

The three active full roots have private shape11111. Tight pair tests and singleton exchange give fifteen actual private points, five distinct leaves in each of three different columns H1,H2,H3. They avoid the common column G. If the public cut is three leaves, tight-nine also forces those leaves into the same G. Otherwise the public cut is already a whole column G. Thus the ENTIRE three-full-root actual support lies in G,H1,H2,H3.

The full source's standalone five-ary tree has five different columns, each with at least five actual leaves. At least one such column K is outside G,H1,H2,H3. Its five chosen distinct actual leaves must all occur at the inactive gap root. Select any actual gap owner of each leaf, allowing all five selected points to lie at ONE child. No false distribution among gap children is assumed.

For every fixed choice of one triple at each full root, each pair of the three restricted roots has at least three actual leaves in G: its other two branches can only be the two distinct private columns. Apply Report443 at depth one on G with `(m,q)=(3,2)` and leaf cap1/3. This supplies one public probability with root cap1/2, leaf cap1/3 and root/leaf cap2/9. Lift atoms to actual selected children and average over all ten triples at each full root. Its child cap is3/10 and its point cap2/15. The public law uses only actual common points; an individual root need not support three such points on its own.

Use total public weight W=30/139. Give each of the fifteen full private points weight x=20/417, and each of the five selected gap K points weight y=9/695. Then

    W+15x+5y=1.

The root-disjoint and column-disjoint support gives simultaneous caps

    (1,145/417,100/417,47/417,100/417,
       10/139,9/139,20/417,20/417).

Their justifications are respectively

    1,
    max(5x+W/2,5y),
    max(5x,W,5y),
    max(x+3W/10,5y),
    max(5x,W/2,5y),
    max(x,W/3,y),
    max(x,3W/10,5y),
    max(x,2W/9,y),
    max(x,2W/15,y).

In particular the concentrated gap-child cost5y is included in every relevant child and child/column cap. Multiplying by the LCM multiplicities gives

    Gamma_1225 <=1214/139 <9.

The inactive gap is not deleted before invoking standalone. Its ACTUAL K leaves are precisely what improves this three-active-root branch.

The [sparse-law constructor](../../frontier/cover-geometry/height_two_cut72_sparse_laws.py) and [exact controls](../../frontier/cover-geometry/height_two_cut72_sparse_laws.json) realize all four families, including both public forms at0555. The five actual sources have740,692,456,256,226 points respectively. Every source has a matching actual flow and cut72 and passes480 selected pair tests and10000 full literal tests. Every single constructed law is checked against1767 original numerical cylinders and81 ordered LCM terms. The selected five gap leaves at0555 all use one child, explicitly testing the concentrated-owner case. The actual whole-public0555 control has the stronger envelope5868/695; the uniform family statement is1214/139.

### Two local support obstructions for fully active cut72

Both arguments concern fixed actual sources and fixed normalized-cut candidate supports. These are ordinary proofs, with no Lean verification or closure of every cut72 source claimed.

#### A local nine-leaf parity obstruction

Let leaves carry a column map into an arbitrary set of columns. A ternary height-two tree means three distinct columns with at least three distinct leaves in each. Let I and J each contain at least three indices. Fix candidate sets A_i and B_j of at most two leaves each, and a fixed set E of at most one leaf. Suppose that for EVERY two distinct i,i' in I and EVERY two distinct j,j' in J,

    A_i union A_i' union E union B_j union B_j'

contains such a tree. These hypotheses are inconsistent.

Proof. Each tested union has at most9 candidate occurrences and contains at least9 distinct leaves. Thus all five component sets have their maximum sizes, their occurrences are pairwise distinct, and their column-count sum has exactly three nonzero coordinates, all equal to3. Write v_i and u_j for the two-leaf column-count vectors and e for the unit column vector of E. Every tested vector is

    v_i+v_i'+e+u_j+u_j'.

Fix any two different indices i,i'. There is a third index t distinct from both. Fix a pair j,j'. Compare tests(i,t;j,j') and(i',t;j,j'). Their difference is v_i-v_i'. Every coordinate is divisible by3 since both test vectors are. Every coordinate also lies between-2 and2. Therefore the difference is zero. This proves that all v_i have the same vector v. The identical exchange on J proves that all u_j have the same vector u.

Every test now has column vector2v+2u+e. Modulo2 this has exactly one odd coordinate. But three distinct coordinates equal to3 have exactly three odd coordinates. Contradiction.

Only three indices from each side are needed: the nine cross-product choices of two out of three suffice. All vectors are on the same fixed column set; choosing a different column relabeling for each test would invalidate the argument.

##### Application to the three fully active k0/Z36 shapes

The necessary shapes, in gap/full/full/full order, are

```text
2222/12222/12222/12223
2222/12222/12222/22222
2223/12222/12222/12222
```

Each gap has at least three cost2 children. Each row has a full root of type12222, which supplies a fixed cost1 child and at least three cost2 children. More generally12223 would also suffice, since it still has three cost2 children. Public k=0 gives actual-fibre containment in the private candidates alone. Every cost1/2 prefix consists of finite leaves, so any selected gap pair and full triple of the displayed form is covered by exactly the five candidate sets in the lemma. Literal4555 blocking gives the ternary tree for every such pair/triple. Hence the lemma excludes all three shapes.

No cost3 child is selected. Such a child's prefix may be three leaves or a whole column without affecting this argument. No assumptions about those unselected fibres, the other full roots, a probability law, or a maximum flow are needed beyond the normalized cut containment and the original legal pair tests. The gap/full selections use two occupied gap children and three full children, which are legal restrictions of the original literal hypothesis; no deletion of source roots is performed.

##### Exact boundaries of the local lemma

The requirement of at least three double children on EACH side cannot simply be dropped. Put E={(2,2)}. Take three double sets L_t={(0,t),(1,t)} for t=0,1,2 and two double sets

    S_0={(0,3),(2,0)}, S_1={(1,3),(2,1)}.

The union of E, both S sets and any two L sets has exactly three leaves in each of columns0,1,2. Thus all local tests hold when one side has only two indices. Interchanging the two sides gives the other boundary example. These are counterexamples to weakening the LOCAL lemma's cardinality hypothesis, not claims of complete literal4555 sources.

#### A local public-two-leaf obstruction

The earlier cut77/public2 proof is independent of its raw cut value and inactive-root status. The needed local hypotheses are only:

1. A fixed public candidate set P with at most two leaves.
2. A clean full root with at least four singleton-private children, with every legal clean triple available for the tests below.
3. A gap root with at least three double-private children, with every pair available.
4. One legal triple at another full root whose private candidates form a set Q of at most four finite leaves.
5. Every relevant actual fibre is contained in P plus its fixed private candidates; every clean/gap, clean/exceptional and exceptional/gap selected test contains a ternary tree.

These hypotheses are inconsistent. For the current applications the clean root has five children and the gap has four, so there is no minimal-cardinality issue.

Proof. A clean triple and gap pair are covered by P2+clean3+gap4=9 candidate occurrences. Tightness forces all nine distinct and actual in the tested union, with column counts0 or3. Exchanging singleton clean children while retaining two others forces all clean singleton labels into one column H. Exchanging gap children while retaining a third gap child forces all gap two-leaf count vectors to equal one vector v, since coordinate differences lie in[-2,2] and are divisible by3.

For every such test, the clean triple supplies3e_H. Hence P+2v has exactly two nonzero coordinates, each3, and has no H component. A double vector v concentrated in one column would contribute4 there and is impossible. Thus v=e_K+e_L for distinct K,L different from H, and the public vector is also e_K+e_L. All actual gap fibres lie in K union L by cut containment.

Now test the exceptional triple against a clean triple. The candidate bound is again P2+Q4+clean3=9, so the same tightness applies. The clean branch H is full, while P already contributes in K and L. Thus Q contributes two leaves in each of K,L, and none anywhere else. The ENTIRE actual exceptional triple lies in K union L. Pairing it with any gap pair yields an actual source in only two columns, contradicting literal blocking.

The proof uses fixed candidate containment and actual tests. It does not infer a tree from candidate costs alone, and no candidate is presumed actual before a tight test forces it.

##### Application to fully active k2/Z29

The three necessary shapes are

```text
2222/02222/02222/11111
2222/02222/11111/11222
2222/11111/11222/11222
```

Every row contains gap2222, a clean full11111, and another full root of type02222 or11222. At02222, choose its zero child and any two double children. At11222, choose both singleton children and any double. Each selected triple has total private candidate cost4, all finite. All hypotheses of the local public-two-leaf obstruction therefore hold. The remaining full root is unused; there is no need to assume it inactive. All three shapes are impossible.

The [local-obstruction controls](../../frontier/cover-geometry/height_two_cut72_local_obstructions.py) and [exact data](../../frontier/cover-geometry/height_two_cut72_local_obstructions.json) independently re-enumerate the two private profiles, test833 exchange-vector pairs and5488 parity vectors, verify105 public-two-leaf patterns and22050 exceptional vectors, and check both labelled boundary counterexamples. The ordinary local arguments prove impossibility; these controls do not manufacture a source for an impossible profile.

### Both partial public5/private15 profiles are impossible

The shapes are111/01111/01111/01111 at3555 and1111/0111/01111/01111 at4455. Each of the THREE full roots has one zero-private child and at least three singleton-private children. At every full root select its zero child and any two singleton children. The resulting legal full/full pair has four private candidates, in addition to public cost5.

If P consists of five public leaves, every such test has exactly nine candidate occurrences. They must all be distinct and actual, with column counts0 or3. Exchange one singleton while keeping another fixed; at least three singleton children make the exchange possible even at the partial0111 root. This locks all singleton candidates of full root r into one column H_r. Distinct roots cannot have the same H, since their four selected private leaves would then occupy one column. For every full-root pair r,s, the fixed public column vector must be

    v_P=e_(H_r)+e_(H_s)+3e_(G_rs).

Compare pairs(1,2) and(1,3). The difference e_(H2)-e_(H3) is divisible by3 coordinatewise, forcing H2=H3. Their own pair forbids this equality, a contradiction.

The other possible public-cost5 antichain is one whole column G and two leaves outside G. Each selected full/full test has at most six outside-G candidates: those two public leaves and the four private candidates. A ternary tree must use G and all six distinct actual outside leaves, split into two three-leaf columns. The same exchange locks all private singleton columns H_r outside G. Pairwise H_r are distinct, and the fixed two-public-leaf vector is e_(H_r)+e_(H_s) for every pair. Comparing two pairs gives the same contradiction. Two public whole columns would already cost6 and are not a third case.

Every private label used here becomes actual at its owner through a tight test and cut containment. Neither standalone nor a gap-root argument is needed. This excludes both displayed k5 families.

### Every partial cut72 public9/private1 profile has one law below nine

Scope: original actual literal4555 source and standalone five-ary seven-tree, minimum-cut profile3555 or4455, public integer cost9 and private cost1. There is exactly one original inactive occupied child u, and exactly one active child e with one private candidate leaf y; all other active fibres lie in the public antichain P. The proof concerns actual source laws at fixed head1225. It is ordinary mathematics, not Lean verification or an unrestricted outside-cofactor lift.

Omit e ONLY from the law and child restrictions. Every root retains at least its legal number q_r of active children. Pair restrictions drawn from these retained sets are legal tests on the unchanged original source, and their entire projection lies in P. Each contains a ternary seven-tree. Since a ternary tree costs at least9 to cover, P has exactly three fixed first-seven columns G1,G2,G3, each covered by its whole-column edge or by exactly three leaf edges. Every retained-root pair has at least three actual leaves in EACH of these three columns.

#### Three placements use the existing equal coupling directly

If3555 has e at a full root, the remaining counts are3455 (gap first). If4455 has e at the gap root, they are3455 after full-root relabeling; if e is at a five-child full root, they are4445. In every case

    delta=max_r q_r/(retained child count at r) <=3/4.

For each fixed complete restriction and each G_j, apply Report443 with four rows and pair premise, obtaining root cap1/3, leaf cap1/3, root/leaf cap1/6. Average actual lifts over restrictions and mix the three branch laws equally. This is Report449's existing fixed-three-branch construction, whose proof does not require the original cut's private cost to be zero: it only requires that the retained fibres lie in P. Its caps are

    (1,1/3,1/3,delta/3,1/9,1/9,delta/9,1/18,delta/18),

and Gamma<=643/72<9.

#### Two concentrated placements need the inactive child's actual external leaves

The remaining placements are3555 with e at the gap root, and4455 with e at the four-child full root. After omitting e their survival factors are, with the exceptional root first,

    (1,3/5,3/5,3/5), or (1,1/2,3/5,3/5).

The exceptional root is precisely the root containing the original inactive child u.

Apply Report445's weighted pair theorem on each G_j using

    alpha=(3,5,5,5)/13,
    beta =(3,5,5,5)/9,
    kappa(leaf)=1/3.

The44 sufficient cut inequalities hold exactly. Average the one actual coupling over retained child restrictions and mix the three branch laws. The resulting public-supported law psi has caps

    (1,5/13,1/3,3/13,5/39,1/9,1/13,5/81,1/27).

At the exceptional root itself the sharper root cap3/13 remains available. The LCM envelope of psi is3167/351, which is ABOVE9; this alone does not close the profile.

The full standalone five-tree uses five first-seven columns, so at least two of its columns lie outside G1,G2,G3 and contribute ten distinct actual leaves. All source points outside these three columns are at u or at the sole private candidate y at e. Delete y if it appears among these ten labels. The other at least nine labels are actual at u. Choose exactly nine, with five in one external column and four in the other. Let eta be their uniform law, entirely at the same original child u. It has column cap5/9 and leaf cap1/9.

Set

    nu=(9/10)psi+(1/10)eta.

The two parts occupy disjoint seven columns and disjoint actual children. Only their exceptional first-five root can overlap. Its mass is at most

    (9/10)(3/13)+1/10=4/13 <9/26,

while the other root caps are(9/10)(5/13)=9/26. Every other nonunit cap is at most9/10 times the displayed psi cap: the additional part's child mass1/10, column/child-column mass1/18, and leaf masses1/90 lie under the respective scaled caps. Hence nu has caps

    (1,9/26,3/10,27/130,3/26,1/10,9/130,1/18,1/30).

Its envelope is

    Gamma_1225 <=1+(9/10)(3167/351-1)=1603/195<9.

No actual point is invented from a cut leaf. The ninth-point supply uses the original inactive child's full source support and the original standalone tree. It does not assert that omitting e or u preserves standalone or blocking.

#### Exact controls

The companion constructs one actual source for each of the five placements. It verifies all44 rational weighted cut inequalities,480 pair tests and10000 full literal tests per source, standalone, matching actual flow/cut72, the actual public coupling on every complete retained-child restriction in all three branches, and all1767 numerical cylinders and81 ordered LCM terms. In the two weighted cases the nine additional atoms all lie at the original inactive child. The program is a construction control, not an exhaustive source search.

The [partial-public9 constructor](../../frontier/cover-geometry/height_two_cut72_partial_public9.py) and [exact data](../../frontier/cover-geometry/height_two_cut72_partial_public9.json) realize all five placements on actual428-point sources. They reuse the sparse-law network helper and the existing integral flow implementation. Each displayed family bound is attained by the separate-cylinder envelope of its constructed law; no maximization over all phase layouts is asserted.

The four programs reproduce these results with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut72_profiles.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut72_sparse_laws.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut72_local_obstructions.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/height_two_cut72_partial_public9.py
```

## Remaining source and arithmetic gaps

All sources with a literal65/63,66/63,67/63,68/63 or69/63 minimum cut are controlled without an incidence-at-most-two assumption. These cuts force actual support structure sufficient for a different law.
The saturated-block theorem and sharp refinement control every78/63 source with bound233/26. For77/63, (SH1) controls any source admitting an integral77 flow without a coarse block of root mass21 and joint mass20; existence of such a flow is not established for every source. For
occupancy4555, the large-cut estimate handles every cut at least79/63.
The neighborhood theorem also controls a value77 flow when every dangerous mass20 block satisfies its stated actual-support condition. The common-column plus exclusive-private-column source class supplies that condition after one possible integral transfer, so this entire restricted class has bound691/77. The164-point control shows that filling each such block to21 is unnecessary and can be impossible. The68-point control disproves automatic satisfaction of the neighborhood condition for an arbitrary selected maximum flow and rules out every repair that fixes its dangerous(a,d,b). It permits an explicit joint-block reroute. The two-unit complement criterion and cross-root releases give a finite procedure with at most three repairs and no new dangerous blocks. A remaining non-T3 block carries both a bounded saturated-prefix cover and a common two-digit trap on eligible donor children. The192-point source shows why root-only blockage is insufficient to rule out a global repair, even outside the three stated source classes. The entire one-inactive-full-root active profile(0,5,5,4) is now controlled by(IF77), with bound691/77. This includes every public cost and every finite or whole private-prefix realization; the proof combines actual-support exclusions with the complement repair and T3 consumer. Excluding every remaining terminal trap, or supplying a further global reroute, remains missing.
The complete cut70 classification and(C70) control every70/63 source with bound643/72. The complete cut71 classification and(C71-law) control every71/63 source with bound79/9. At72/63, the four sparse families and both partial public9 families have actual laws below nine, while both partial public5 and fully active public0/public2 families are impossible. The unclassified72 families are3555 or4455 with public3/private22, and4555 with public4/private22 or public6/private15. General high-incidence sources in the remaining
range72/63 through77/63 are not thereby controlled: their high root/column incidence
can still invalidate the earlier mixed-cap estimate. The fully active R=1
whole-column shapes at75/63 and77/63 are controlled by(WC1), but this
does not settle all sources at those numerical cut values. Some may contain
the private structure, but its existence has not been proved for every
remaining source. Other occupancy patterns retain their own stated
premises and are not classified by this remaining six-value window.

The theorem is at the fixed head1225. An actual full odd-covering residual must also carry every original outside-cofactor constraint under one common lift, as in439. A head law alone does not supply that lift, and a uniform complete-Gamma bound below nine for arbitrary free cofactors is already ruled out there. The next arithmetic obligation remains a bound for the actual original test family and its same-law deletion correlations. No unrestricted noncoverage conclusion follows from this finite head theorem alone.
