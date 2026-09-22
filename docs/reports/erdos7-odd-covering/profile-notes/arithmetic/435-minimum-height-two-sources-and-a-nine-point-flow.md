[Index](../../marked_head_profile.md) · [Three robust roots](431-three-robust-five-roots-admit-a-height-two-common-law.md) · [Shared-column cuts](432-four-root-source-selections-and-the-shared-column-boundary.md)

# Minimum height-two sources and a direct nine-point flow theorem

These are ordinary combinatorial proofs for the original height
`(H5,K7)=(2,1)` carrier. They retain all six original independently
phased labels `(1,5,25,7,35,175)` and actual source points. The
three-robust-root `46/9` theorem is already supplied by report 431 and
is not reproved here. No new Lean certification is claimed.

Write the source as `S subset {1,2,3,4} x {0,...,4} x {0,...,6}`.
For root `r`, let `G_r` be its child/column incidence graph. For a
seven-column subset `D`, define

\[
 t_r(D)=|\{a:\text{some }(r,a,y)\in S\text{ has }y\in D\}|.
\]

The original product-tree condition is

\[
 \#\{r:t_r(\mathbb Z/7\setminus E)\le2\}\le1
 \quad\text{for every two-column set }E.
\]

Equivalently, the four bad-pair sets `B_r` are pairwise disjoint.
The following results do not require a separate column-projection
assumption; minimum sources automatically use at least five columns.

## Minimum sources have exactly fifteen points

Every admissible source has at least fifteen points. Equality holds
exactly for three rootwise five-point matchings and one empty root.

A root with at most two edges is bad for every deleted pair. An
internally robust root has at least five edges: with at most four
edges, either it has at most two active children, or some deleted
pair removes enough singleton children to leave at most two.
More explicitly, three active children among at most four edges
include a singleton; four active children among four edges are all
singletons, and two of them can be deleted together.

A robust five-edge root is a five-matching. With only three active
children one child is a singleton and can be deleted. With four
active children the degree pattern is `(2,1,1,1)`, and two singleton
children can be deleted together. Therefore all five children are
active with one edge each. If any column is repeated, deleting that
column and a column of a third child removes at least three children.
Thus the five columns are distinct.

Two three-edge roots cannot coexist. A three-edge root with at most
two active children is bad for every pair. Otherwise its three
children are all singletons, and every pair containing any of its
occupied columns is bad. Choosing one occupied column from each of
two such roots produces a pair bad for both; if the choices coincide,
include an arbitrary other column.

Every three- or four-edge root has at least six bad pairs. For three
edges this follows from any singleton. For four edges and three
active children it again follows from a singleton. For four active
children, repeated column use gives all six pairs containing that
column; otherwise the four distinct occupied columns supply their
six internal pairs. At most two active children give all 21 pairs.

If `|S| <= 14` and some root has at most two edges, the other three
are robust and alone contribute at least fifteen. If every root has
at least three edges, their counts include two threes, also
impossible. Hence `|S| >= 15`.

For equality, a root with at most two edges must be empty, and the
other three must be robust five-edge matchings. Otherwise the four
positive counts either include two threes or are `(3,4,4,4)`; the
latter require at least `4*6=24` pairwise disjoint bad pairs in a
21-pair universe. Conversely, three five-matchings are robust and
one empty root is the unique bad root for each deleted pair.

## Sharp universal budget on minimum sources

Give the fifteen actual points equal mass before all independent test phases. Its
maximum root, child, global-column, root-column and atom masses are
bounded by

\[
 \alpha_R=1/3,\quad\alpha_L=1/15,\quad\alpha_C\le1/5,
 \quad\alpha_{RC}=1/15,\quad\alpha_P=1/15.
\]

The same-law LCM expansion of the squared six-label load gives

\[
 \Gamma(\nu)\le
 1+3\alpha_R+5\alpha_L+3\alpha_C+9\alpha_{RC}+15\alpha_P
 \le\frac{68}{15}<\frac{46}{9}.
\]

The constant is sharp uniformly over all minimum sources. For

\[
 S_\triangle=\{(r,a,a):r=1,2,3,\ a=0,\ldots,4\},
\]

choose a layout uniformly from the fifteen layouts centered at a
point `q` of this same source; each original label uses `q`'s own
residue at its own modulus. For any fixed source point `z`, there
is one identical center, four other centers in its root, two other
centers in its column and eight centers sharing neither. The
pointwise average squared load is

\[
 \frac{36+4\cdot4+2\cdot4+8}{15}=\frac{68}{15}.
\]

Averaging against any supported probability law shows that one
legal centered layout has expectation at least `68/15`. The uniform
law attains the upper bound, so the minimax value of `S_triangle`
is exactly `68/15`. This lower bound applies to this displayed
source, not to every minimum source's optimal law.

## All admissible sources have a nine-point joint selection

Every admissible source contains nine points with at most one per
child `(r,a)`, at most three per root and at most three per global
column. The present carrier admits a direct integral flow proof.

Use the network

```
source -> root [capacity 3] -> child [capacity 1]
       -> actual neighboring column -> sink [capacity 3].
```

The child/column edges can have capacity one or an effectively
infinite capacity; every child has input capacity one. A unit of
integral flow is one actual source point.

Fix the sink-side column set `D`. Every source-side column costs
three. For each root, either cut its capacity-three incoming edge,
or pay one for each child having a neighbor in `D`; children with
no such neighbor can remain source-side free of charge. If a child
with a neighbor in `D` stays source-side, cutting its outgoing
edges costs at least one, so moving it sink-side never increases
the cut. Hence the exact min-cut formula is

\[
 \operatorname{maxflow}
 =\min_{D\subseteq\mathbb Z/7}
 \left[3(7-|D|)+\sum_{r=1}^4\min(3,t_r(D))\right].
\]

If `|D| <= 4`, the first term is at least nine. If `|D| >= 5`,
choose five columns `D_0 subset D`. The original source condition
makes at least three roots have `t_r(D_0) >= 3`; monotonicity then
makes the root sum at least nine. Every cut has capacity at least
nine, so integral max flow provides the claimed selection.

The reusable cut principle is: if every set of all but `b` columns
has laminar rank at least `t`, and each column has capacity `c`
with `c(b+1) >= t`, then the joint flow has value at least `t`.
A sink-side column set large enough already has rank `t`; a smaller
one leaves at least `b+1` source-side columns to pay for. Here
`b=2`, `c=3`, and `t=9`.

This selection does not require distinct columns within a root.
It also permits three points per global column. Both differences
matter when comparing it to report 432's eleven-point selector,
which allows at most two per global column and at most one per
root-column. The deterministic proper-cut source with eleven-point
max flow eight still admits this nine-point selection.

## The remaining weighted condition is stronger than nonempty flow

Scaling a nine-point common basis by `1/9`, and then taking mixtures,
produces precisely the supported probability laws satisfying

\[
 \nu(r,*,*)\le1/3,\qquad
 \nu(r,a,*)\le1/9,\qquad
 \nu(*,*,y)\le1/3.
\]

Indeed scaling by nine yields the integer network-flow polytope
with total flow nine; its integral vertices select such bases.
These caps certify membership in that common-basis polytope, not
the required squared-load bound.

For example, inside the full admissible source, the common basis

\[
 B_0=\{(r,a,r-1):r=1,2,3,\ a=0,1,2\}
\]

has uniform-law price `74/9` at the layout centered at `(1,0,0)`:
one point has squared load 36, two have 16, and the other six have 1.
Thus one arbitrary basis can fail. The basis itself is not being
claimed as an admissible source.

For the basis-constrained construction, the exact remaining
finite-minimax condition is that for every probability `theta` on
legal original layouts, some actual nine-point common basis `B`
satisfies

\[
 \sum_{z\in B}\mathbb E_{\lambda\sim\theta}L_\lambda(z)^2\le46.
\]

If this holds, minimax gives one mixture of bases chosen before
all layouts with `Gamma <= 46/9`. Failure would reject this
basis-constrained construction only; a successful actual law may
violate one of its extra caps. No universal weighted bound is
established here.

The [exact companion checker](../../frontier/cover-geometry/minimum_sources_and_nine_flow.py) verifies the fifteen-center sharpness
certificate, same-law LCM upper bound, min-cut/flow agreement for
the minimum, full and new proper-cut sources, and the `74/9`
bad-basis witness. The analytic cardinality and general flow proofs
do not rely on finite sampling.
