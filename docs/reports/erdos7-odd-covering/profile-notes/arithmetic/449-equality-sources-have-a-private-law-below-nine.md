[Index](../../marked_head_profile.md) · [Literal equality reduction](448-literal-product-trees-exclude-the-equality-cut.md) · [Generic cut bound](447-strict-child-cut-surplus-and-arithmetic-boundaries.md)

# Literal cuts65/63 through69/63 force private laws below nine

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

## Remaining source and arithmetic gaps

All sources with a literal65/63,66/63,67/63,68/63 or69/63 minimum cut are controlled without an incidence-at-most-two assumption. These cuts force actual support structure sufficient for a different law.
The saturated-block theorem and sharp refinement control every78/63 source with bound233/26. For77/63, (SH1) controls any source admitting an integral77 flow without a coarse block of root mass21 and joint mass20; existence of such a flow is not established for every source. For
occupancy4555, the large-cut estimate handles every cut at least79/63.
The partial-full-root70/63 profile above is controlled by(PF1), without
settling every cut70 source. General high-incidence sources in the remaining
range70/63 through77/63 are not thereby controlled: their high root/column incidence
can still invalidate the earlier mixed-cap estimate. The fully active R=1
whole-column shapes at75/63 and77/63 are controlled by(WC1), but this
does not settle all sources at those numerical cut values. Some may contain
the private structure, but its existence has not been proved for every
remaining source. Other occupancy patterns retain their own stated
premises and are not classified by this eight-value reduction.

The theorem is at the fixed head1225. An actual full odd-covering residual must also carry every original outside-cofactor constraint under one common lift, as in439. A head law alone does not supply that lift, and a uniform complete-Gamma bound below nine for arbitrary free cofactors is already ruled out there. The next arithmetic obligation remains a bound for the actual original test family and its same-law deletion correlations. No unrestricted noncoverage conclusion follows from this finite head theorem alone.
