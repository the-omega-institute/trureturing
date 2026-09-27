[Index](../../marked_head_profile.md) · [Three robust roots](431-three-robust-five-roots-admit-a-height-two-common-law.md) · [Root support classification](395-root-rectangle-blockers-need-no-standalone-projection-condition.md)

# Four-root source selections and the shared-column boundary

Several actual four-root source classes at heights `H5=2,K7=1`
admit one probability whose complete independent-layout second moment
is at most `46/9`. These classes include sources with no robust root.
They follow from supported matchings, three-child rectangles, or a
selection of twelve two-column child neighbourhoods. A source reduction
at every finite five height preserves all twenty-one five-column
projections while bounding each terminal degree by three.

These are ordinary combinatorial proofs and exact arithmetic
certificates, not Lean certification. The criteria are sufficient and
are not asserted to exhaust all admissible sources or to follow from
an arbitrary minimal odd covering system. The new criteria do not establish exhaustiveness of the admissible
source class; they retain explicit sources outside the earlier criteria
and construct improved laws on them.

## 1. The original six-label game

Write points as `(r,a,y)`, where `x=r+5a mod25`, `r,a in Z/5`, and
`y in Z/7`. For a law `nu` supported on an actual source `S`, set

\[
 \Gamma(\nu)=\max\mathbb E_\nu
 \left(1+1_{r=r_1}+1_{(r,a)=(r_2,a_2)}+1_{y=b_0}
       +1_{(r,y)=(r_3,b_1)}+1_{(r,a,y)=(r_4,a_4,b_2)}\right)^2.
 \tag{FS1}
\]

Every displayed phase is independent. These indicators retain the
original numerical labels `1,5,25,7,35,175`. Each construction selects
one law before all these phases. Extra source points receive zero
mass. When four roots are selected, a phase in the remaining root
has zero indicator and is dominated by an occupied-root choice.
Permuting child digits separately within roots and making one common
column permutation carries this entire family of labelled events
bijectively; no prime axes or numerical modulus labels are exchanged.

## 2. A finite source reduction at every five height

Let `H>=1` and let `S` be a source on the depth-`H` five-adic leaves
and seven columns. Assume it meets every complete ternary five-tree
times every five-column set, and its total column projection has
`q>=5` elements. There is an actual subset `S' subset S` such that:

* Every nonempty leaf fibre has exactly the smaller of three and its
  original degree.
* For each of the twenty-one five-column sets `D`, the projection onto
  leaves of `S' intersect (leaves times D)` is exactly the old projection.
* At least `min(q,6)` columns remain. The nonempty leaf set is unchanged.

For any fixed leaf, the other leaves together see at least three
columns. Otherwise choose five columns avoiding their at most two
columns and a complete ternary tree avoiding that leaf. Such a tree
exists because `H>=1`, and its product misses `S`.

In the bipartite graph of leaves and columns, put capacity three on
each leaf and one on each column. Integral maximum flow gives the
maximum number of distinct-column representative edges as

\[
 \min_A\bigl(3|A|+|N(\mathrm{leaves}\setminus A)|\bigr).
 \tag{FS2}
\]

The empty `A` gives `q`; a singleton gives at least six by the preceding
paragraph; and a larger `A` gives at least six. Select `min(q,6)`
representatives, with at most three per leaf. Extend these choices
within each original fibre to degree `min(3,degree)`. A neighbourhood
of size at least three meets every five-column set, both before and
after reduction; smaller neighbourhoods are unchanged. This proves
all three claims without moving any original point.

Six is sharp: start with a complete ternary leaf tree whose every
leaf sees columns `{0,1,2}`, then give one leaf all seven columns.
The four additional columns occur only at that leaf, so a degree-three
reduction cannot retain all seven. The `H>=1` hypothesis is necessary;
one leaf at height zero cannot retain five columns with degree three.

At height two with root zero absent, define the bad-pair set of root
`r` by

\[
 B_r=\{E\subset\mathbb Z/7:|E|=2,
      \#\{a:N_{ra}\not\subset E\}\le2\}.
 \tag{FS3}
\]

The product-tree condition is precisely pairwise disjointness of the
four `B_r`; see report 431. The reduction preserves these sets
pointwise, and preserves the actual singleton, doubleton and triple
neighbourhoods needed to choose a law. A bad-pair graph alone does
not specify a probability support.

## 3. Supported matchings and a common root-mask budget

Use mask bits `(P1,M1,P2,M2)` for the positive-five labels
`(5,35,25,175)` entering a particular root. Put
`c=1+P1`, `t=1+M1`, `e=P2`, and `f=M2`. The global label `7` remains
present in every root. As proved in report 431, locally coalescing
the two column indicators preserves their maximum. This is a local
bound for arbitrary original phases, not a global change of coordinates.

If a root contains an `n`-point matching of distinct children and
columns, its uniform law has exact local mask maximum

\[
 B_n(M)=\frac{(c+t+e+f)^2+(n-1)c^2}{n}.
 \tag{FS4}
\]

The simultaneous row, column and atom caps are all `1/n`. The square
expansion gives this bound, and choosing the nonconstant indicators
at the same selected point attains it. For chosen root weights
`w_1,...,w_4`, one therefore has

\[
 \Gamma(\nu)\le
 \max_{M_1\sqcup M_2\sqcup M_3\sqcup M_4=\{1,2,3,4\}}
                  \sum_r w_r B_{n_r}(M_r).
 \tag{FS5}
\]

There are `4^4=256` assignments. The following rational weights make
all of them at most `46/9`:

| Selected matching sizes | Root-weight numerators | Denominator | Maximum in FS5 |
| --- | --- | ---: | ---: |
| `(1,3,4,5)` | `(9,24,30,35)` | 98 | `143/28` |
| `(1,4,4,4)` | `(1,4,4,4)` | 13 | `66/13` |
| `(2,2,4,5)` | `(3,3,5,6)` | 17 | `1723/340` |
| `(2,3,3,5)` | `(3,4,4,6)` | 17 | `859/170` |
| `(2,3,4,4)` | `(2,3,4,4)` | 13 | `66/13` |
| `(3,3,3,4)` | `(1,1,1,1)` | 4 | `245/48` |

It suffices that the four roots, in some ordering, contain matchings
at least as large as one listed tuple: select exactly the listed
sizes. The table gives supported-law upper bounds, not free-law
minimax optima. No product-tree or standalone column premise is
needed for this implication.

There is also a mixed structural criterion. If each of four roots
is either robust as defined in report 431 or contains a four-point
matching, choose the report-431 law in a robust root and the uniform
matching law otherwise. Mix the four laws equally. Taking the larger
of the report-431 envelope and `B_4` gives, in mask order zero to fifteen,

\[
 (2,17/3,11/3,8,29/9,68/9,46/9,91/9,
   3,7,29/6,19/2,19/4,37/4,7,12).
 \tag{FS6}
\]

Its sum over every assignment of the masks is at most eighteen,
with equality only when all four labels enter a single root. Thus
this actual common law has `Gamma<=9/2`.

## 4. Four rectangular three-child fibres

Suppose four actual roots contain `A_r times N_r`, with `|A_r|=3`,
each `N_r` nonempty, and `|N_r union N_s|>=3` for every two roots.
Then there is one supported law with `Gamma<=46/9`. This condition
permits repeated column pairs among different children and does not
require a standalone five-column projection.

The four-row neighbour system `(N_r)` satisfies RB5 of report 395.
Delete root-column edges to one of its ten minimal types. At each
retained root-column cell, split its chosen mass equally among the
three actual children. The following weights, in the canonical edge
order of `root_rectangle_second_moment.py:edges(TEMPLATES[name])`,
give the stated exact maximum for that single law:

| Type | Integer root-column weights | Sum | Exact Gamma |
| --- | --- | ---: | ---: |
| A | `(3,3,2,2,2,2,3,3)` | 20 | `301/60` |
| B | `(4,3,4,3,4,3,4)` | 25 | `382/75` |
| C | `(4,3,3,3,3,3,3)` | 22 | `5` |
| D | `(4,3,3,3,3,3,3)` | 22 | `5` |
| F | seven ones | 7 | `100/21` |
| cycle4 | eight ones | 8 | `14/3` |
| triangle_full | nine ones | 9 | `46/9` |
| two_triples | nine ones | 9 | `46/9` |
| singleton_triangle | `(4,3,3,3,3,3,3)` | 22 | `5` |
| A_shared | `(4,3,3,2,2,3,3,3)` | 23 | `117/23` |

For an exact finite verification, fix the phases of labels `5,7,35`
and let `l` be their load together with the constant label. Write
`w_xy` for integer mass numerators, and set

\[
 C=\sum_{x,y}w_{xy}l_{xy}^2,\quad
 A_x=\sum_y w_{xy}(2l_{xy}+1),\quad
 D_{xy}=w_{xy}(2l_{xy}+1).
\]

The maximum over the two remaining independent labels `25,175` is
exactly

\[
 C+\max_{x,y}\left[D_{xy}+
        \max\left(A_x+2w_{xy},\max_{u\ne x} A_u\right)\right].
 \tag{FS7}
\]

This simply separates whether the selected leaf and point share a
leaf. It preserves both independent choices. The checker verifies
the table using all 784 old layouts and 140 point choices, with the
20 leaf choices accounted for by FS7; that represents 2,195,200
complete phase choices per law. Each winning layout is checked
against literal residues for all six original moduli. Transporting
the selected child sets and the common column names back preserves
these bounds on the original source.

## 5. Twelve selected two-column child fibres

Suppose each of four roots has three distinct selected children, and
each such child has two distinct selected neighbour columns. Put the
uniform law on these twenty-four actual points. Let `Delta` be the
largest number of selected points in a column, and `D` the largest
number in a root-column cell. Necessarily `D<=3`. The simultaneous
root, leaf, column, root-column and atom caps are

\[
 1/4,\quad1/12,\quad\Delta/24,\quad D/24,\quad1/24.
\]

For every independently phased layout, the intersection of two label
events is either empty or a cell at their LCM. The ordered pairs of
five-depths have counts `(1,3,5)` by their maximum; the seven-depths
have counts `(1,3)`. Under this same law the square expansion gives

\[
 \Gamma(\nu)\le
 1+\frac{3\Delta}{24}
 +3\left(\frac14+\frac{3D}{24}\right)
 +5\left(\frac1{12}+\frac3{24}\right)
 =\frac{67+3\Delta+9D}{24}.
 \tag{FS8}
\]

Thus `Delta+3D<=18`, in particular `Delta<=9`, gives
`Gamma<=121/24<46/9`.

A convenient stronger certificate is that all twelve selected
unordered column pairs are distinct. They form a simple graph on
seven columns, so `Delta<=6` and `Gamma<=14/3`. Their root bad-pair
sets are disjoint, and twelve distinct pairs use at least six columns,
so this selected subsource itself passes the original product-tree
and standalone projection tests.

A forty-seven-vertex integral network finds this witness:
`source -> four roots [3] -> twenty children [1] -> twenty-one pairs [1]
-> sink [1]`. Child-pair edges exist only when both columns occur at
that actual child. A flow of twelve chooses the required actual
points. Equivalently, for every subset `T` of all twenty child positions,
including positions with empty neighbourhoods,

\[
 |N(T)|+2|\operatorname{roots}(T)|\ge|T|.
 \tag{FS9}
\]

Add two private dummy right vertices per root, each adjacent to all
five of its children, and apply Hall's theorem to match all twenty
children. At least three per root use real pair vertices; retain
three and match the others to the two dummies. This proves the
criterion in both directions. A failed flow rejects this construction,
not the existence of a suitable source law.

## 6. Why the inherited seven phase must remain common

For fixed actual mass numerators, let `F_r(M;b)` be the root contribution
maximized over its local phases while holding fixed the global label-7
phase `b`. Assignment of the four positive-five labels to roots gives
an exact decomposition

\[
 \Gamma(\nu)=\max_b\max_\alpha\sum_r F_r(M_r(\alpha);b).
 \tag{FS10}
\]

Once `b` and the root assignment are fixed, the other phases belong
to their respective roots and their local maxima are simultaneously
attainable. The law still precedes all these choices.

For a concrete difference from separate column maximization, take

\[
 S=\{(r,a,y):r=1,2,3,4,\ a=0,1,2,\ y\in\{r-1,4+a\}\}.
 \tag{FS11}
\]

Every root is nonrobust, no root has a four-point matching, all seven
columns occur, and its twelve column pairs are distinct. Under its
uniform law the exact values are

\[
 \max_b\max_\alpha\sum_r F_r(M_r(\alpha);b)=103/24,
 \qquad
 \max_\alpha\sum_r\max_b F_r(M_r(\alpha);b)=65/12.
 \tag{FS12}
\]

The first is below `46/9`, the second above. A literal attaining
layout for the first uses residues `(0,1,1,0,21,126)` on moduli
`(1,5,25,7,35,175)`. This is a loss in a sufficient certificate for
one fixed law, not a refutation of a source-law existence statement.

## 7. A common column can also yield a stronger positive bound

Suppose one root contains three distinct children at a single column
`c`. Each of the other three roots contains a three-point matching,
with column sets `C_1,C_2,C_3` satisfying

\[
 c\notin C_i,\qquad C_1\cap C_2\cap C_3=\varnothing.
 \tag{FS13}
\]

Give the first root total mass `2/11`, uniformly on its three points,
and each other root total mass `3/11`, uniformly on its matching.
Then this one supported law has

\[
 \boxed{\Gamma(\nu)\le5<46/9.}                            \tag{FS14}
\]

Here is a finite mask proof that retains the shared column. For a
mask `(P1,M1,P2,M2)`, put `p=P1`, `m=M1`, `e=P2`, `f=M2`.
Let `b` be one or zero according as the global seven phase hits the
selected column set. Three times the local maximum on the first
root is

\[
 W_b(M)=(1+p+m+b+e+f)^2+2(1+p+m+b)^2.
\]

On a matching root it is

\[
 A_b(M)=(1+p+b+m+e+f)^2+2(1+p)^2.
\]

When the global phase is `c`, the hit pattern is `(1,0,0,0)`.
Otherwise it misses the first root and hits at most two matching
roots by FS13. Since adding a hit only increases the local function
and those three root weights are equal, the remaining patterns are
bounded by `(0,1,1,0)`. Over all 256 root assignments the respective
maxima of

\[
 2W_{b_0}(M_0)+3\sum_{i=1}^3 A_{b_i}(M_i)
\]

are 163 and 165. Division by 33 gives FS14. The checker verifies the
local formulae against their unmerged independent phases and these
512 assignments exactly; it does not choose a different law after
seeing the hit pattern.

This condition applies beyond the preceding sufficient classes.
Take the first root's three children at column six. In the other
three roots give the three children, respectively, the three edge
neighbourhoods of the triangles `{0,1,2}`, `{2,3,4}`, `{0,4,5}`.
These twenty-one actual points have bad graphs equal to the full
star at six and the three edge-disjoint triangles, so all original
product-tree tests pass and seven columns occur. The matching ranks
are `(1,3,3,3)`. No root is robust, the first has no two-column child,
and the other roots have no common column among three children.
Consequently the earlier matching, robust, rectangle and two-column
criteria do not cover this source.

Selecting a matching on each triangle gives FS13 and a twelve-point
positive-mass law with FS14. On original moduli
`(1,5,25,7,35,175)`, residues `(0,2,7,2,2,107)` attain value five.
This is the exact value of this specified law, not an optimality claim
against every other law on the source.

## 8. An eleven-point capacity flow gives the same bound

There is a broader matching criterion with no designated reference
column. Suppose the actual source contains eleven points such that
no root contains more than three, no seven column contains more than
two, and within each root both the child digits and the columns are
distinct. The uniform law on these eleven points satisfies

\[
 \boxed{\Gamma(\nu)\le5.}                                  \tag{FS15}
\]

For any phases, labels `25,35,175` each hit at most one selected
point. Let `l=1+1_{r=r_1}+1_{y=b_0}` be the remaining load. On the
eleven points its squared sum is

\[
 11+3n_{r_1}+3n_{b_0}+2n_{r_1,b_0}\le11+9+6+2=28.
\]

If `k_x` is the number of the three remaining labels hitting point
`x`, then `sum k_x<=3` and `l_x<=3`. Their extra square contribution is
at most `6 sum k_x + sum k_x^2 <=18+9=27`. Thus the full sum is at
most 55. This bounds every independent original phase under one law;
no independently optimized cylinder masses are substituted.

An integral flow finds the eleven points when they exist. The edges
are `source -> root [3] -> child [1] -> actual root-column -> column
[1 on each root-column-to-column edge] -> sink [2]`. With four roots,
twenty children, twenty-eight root-column positions and seven columns,
there are at most sixty-one vertices. A flow of eleven selects actual
source incidences satisfying the stated caps. Failure of this flow
alone is not a nonexistence certificate for a suitable probability law.

The network also gives an exact obstruction to this particular
selection. If `rho_r(D)` is the matching rank in root `r` restricted
to a column set `D`, its maximum flow is

\[
 \min_{D\subseteq\mathbb Z/7}
 \left[2(7-|D|)+\sum_{r=1}^4\min(3,\rho_r(D))\right].
 \tag{FS16}
\]

Fixing the global-column side of a cut charges two for every column
outside `D`. In each root the remaining minimum cut is its restricted
matching rank truncated by the root capacity three. These four cuts
are independent once the same `D` has been fixed; minimizing over
all 128 subsets proves FS16. Thus failure to select eleven points
has an exact witness

\[
 \sum_r\min(3,\rho_r(D))\le2|D|-4.
\]

The remaining structural question is whether every such obstruction,
under the original source conditions, supplies another supported law
meeting the target. FS16 alone does not answer it. For example, give
three roots the triangle-edge child neighbourhoods on `{0,1,2}`,
`{0,3,4}`, `{0,5,6}`, and the fourth three children each at columns
`{0,1,3}`. All seven columns occur and the four full-column matching
ranks are three, yet deleting column zero gives four ranks two and
maximum flow ten. Selecting `{1,3}` at each child of the fourth root
instead gives the twenty-four-point configuration of section 5 with
`Delta=6`, hence bound `14/3`. Proper column cuts therefore carry
information absent from the total matching ranks alone.

For example, the following source has twenty-one points:

| Root | child 0 | child 1 | child 2 | child 3 | child 4 |
| --- | --- | --- | --- | --- | --- |
| 1 | empty | `{0,3}` | `{0,2}` | empty | `{0,4,6}` |
| 2 | `{3}` | `{3,5}` | empty | `{5}` | `{1}` |
| 3 | `{6}` | empty | `{6}` | `{4}` | empty |
| 4 | `{2,6}` | empty | `{1}` | `{0}` | `{0,1}` |

Its bad-pair sets are

\[
 \{02,03\},\quad\{13,15,35\},\quad
 \{04,06,14,16,24,26,34,36,45,46,56\},\quad\{01\},
\]

where `uv` means `{u,v}`. They are nonempty and pairwise disjoint,
and seven columns occur, so it passes the original source tests.
Its root matching ranks are `(3,3,2,3)`, outside the six matching
patterns of section 3. The second root has no three-child common
column, and the third has no two-column child. The only possible
three-child column is zero in root one, while the third root has no
three-point matching, so section 7 does not apply either.

Nevertheless, select the root-by-root matching points

\[
 \begin{array}{c|l}
 1&(1,3),(2,2),(4,0)\\
 2&(0,3),(3,5),(4,1)\\
 3&(0,6),(3,4)\\
 4&(0,2),(2,1),(3,0).
 \end{array}
\]

These pairs are `(child,column)` in their original roots. The global
column counts are at most two and all matching conditions hold.
Their uniform eleven-point law therefore gives FS15 on the very
same source. No source-family exhaustiveness is inferred from this
example or the selection criteria above.

## 9. Verification scope

The retained standard-library programs are:

* [`source_column_compression.py`](../../frontier/cover-geometry/source_column_compression.py): constructs the actual subset and checks every retained column-deletion projection; controls include the sharp six-column limit at heights one through four, 210,000 literal depth-two tree tests, and seven rejected invalid inputs.
* [`four_root_source_common_laws.py`](../../frontier/cover-geometry/four_root_source_common_laws.py): verifies the six matching budgets, the mixed robust/matching budget, all ten rectangular laws and the twenty-one-point source outside the earlier selection criteria.
* [`shared_column_pair_source_law.py`](../../frontier/cover-geometry/shared_column_pair_source_law.py): constructs the integral pair selection, checks its positive and repeated-pair controls, and verifies FS12 through 96,768 local phase choices and 1,792 common-phase/root assignments.

* [`singleton_column_three_matching_law.py`](../../frontier/cover-geometry/singleton_column_three_matching_law.py): verifies FS14 using 13,824 literal local phase choices and 512 assignments, and the attaining original-label layout on its actual source.

* [`eleven_point_source_common_law.py`](../../frontier/cover-geometry/eleven_point_source_common_law.py): constructs the capacity-flow selection on two original sources, checks their product-tree tests, and verifies the exact six-label value five of the declared eleven-point laws; its exact rank tables check FS16, a proper-column cut obstruction, the empty source and the full-carrier flow value twelve.

All checks remain active under Python `-O`. Independent calculations
also verified the matching envelope against 120,960 unmerged local
phase choices; all ten rectangle values against 878,080 root-column
choices and 5,775 literal CRT point calculations; and the compression
matching against 300 graphs with 128 column-side Hall cuts each.
No source-family exhaustiveness or unrestricted Erdős #7 conclusion
is inferred from these finite controls.
