[Index](../../marked_head_profile.md) · [Earlier source selections](432-four-root-source-selections-and-the-shared-column-boundary.md) · [Nonsingleton sources](437-four-root-nonsingleton-sources-admit-a-common-law-below-five.md)

# Weak-root laws with separated or shared column blocks

This result extends the common-column weak-root rectangle case to weak
roots whose three selected points can occupy different columns. The
pair-block construction also extends to nonrectangular strong roots
when an actual capacity-six flow supplies eighteen points outside the
weak columns. The final section supplies a different uniform law when
one strong grid uses all three weak columns; this includes the displayed
counterexample to separated extraction. These explicit selection
conditions do not cover all singleton sources or prove an unrestricted
covering statement.

Assume an actual source contains:

* in one root, three distinct selected children with one selected point
  each, on columns `u_1,u_2,u_3`; write `U={u_1,u_2,u_3}`;
* in each of the other three roots, three distinct selected children,
  each containing the same two columns `E_r`;
* three pairwise distinct unordered pairs `E_r`, all disjoint from `U`.

The pairs may intersect each other. The law below uses only these
21 actual points and is chosen before all six independent original
phases at moduli `(1,5,25,7,35,175)`.

Form the simple graph with three edges `E_r`.

1. If its maximum column degree is at most two, put integer weight four
   on each weak point and weight three on each of the 18 strong points.
   Normalize by 66. Then `Gamma <= 5`.
2. If its maximum column degree is three, the three distinct edges form
   a star. Put integer weight six on each weak point, weight four at
   the common star endpoint of every strong child, and weight five at
   its private endpoint. Normalize by 99. Then `Gamma <= 167/33`.

Consequently the whole subclass has

\[
 \Gamma\le167/33=46/9-5/99.
\]

## A consequence directly from the source condition

Suppose a source has exactly three active children in each of four
roots, its weak root's three neighborhoods are singletons, and the
other three roots have matching rank two and all child degrees at
least two. Each strong root must then have exactly the same two-column
neighborhood at every child: Hall failure for a three-matching cannot
come from one child or two children because every child has at least
two neighbors, so all three children have union of size two.

The strong pair sets are distinct because they are the corresponding
bad-pair graphs. Each weak singleton column makes every deleted pair
containing it bad for the weak root. Disjoint actual bad-pair graphs
therefore force all strong pairs to avoid every weak column. Thus the
preceding theorem applies to this entire singleton/rank-two subclass.

For example, choose weak columns `3,4,5` and strong pairs `01,02,12`,
repeated across all three children of their respective roots. This is
an admissible 21-point, six-column source with matching ranks
`(3,2,2,2)`, no robust roots, and empty weak common-column intersection.
The four-root common-column rectangle criterion does not apply. Nor
can the eleven-point selector succeed (full capped rank sum is nine),
or the existing singleton-plus-three-matchings selector (three strong
roots have rank two). This is a scope comparison with these named
criteria, not a claim that every earlier source-law theorem was searched.

## Exact local kernels and the one shared column

Let mask bits `(p,m,e,f)` record whether the original labels
`(5,35,25,175)` choose a given root. The global modulus-7 phase `b`
is fixed across every root.

For the weak root, every chosen atom has integer mass `z`. All local
nonconstant events hit either a subset of its three points or one
point. If `b` belongs to `U`, dominate its pure-seven indicator by one
on all three weak points; otherwise that indicator is zero. Likewise
dominate the weak modulus-35 indicator by one on all three weak points.
The modulus-25 and modulus-175 indicators each hit at most one selected
point, because the three selected children are distinct. Positive
cross terms are maximized by aligning those two hits. Hence, with
`h=1_{b in U}` and `t=1+p+h+m`, the weak contribution is bounded by

\[
 W_h(p,m,e,f)=z\bigl((t+e+f)^2+2t^2\bigr).
\]

This remains valid when the weak selected columns differ. It is
pointwise domination within the same actual law, not a replacement
of the original source or an independent choice of the global phase.

In a strong pair block, give its two columns per-child weights `u,v`.
For a chosen local modulus-35 column `d` and a pure-seven hit position
`h in {0,1}` (or `h=-1` when `b` is outside the pair), put

\[
 t_y=1+p+1_{h=y}+m1_{d=y}.
\]

The exact local maximum is

\[
 A_h(p,m,e,f)=\max_{d\in\{0,1\}}
 \left[3\sum_yw_yt_y^2
 +e\sum_yw_y(2t_y+1)
 +f\max_yw_y\bigl(2(t_y+e)+1\bigr)\right].
\]

The child and point hits can be put in the same one of the three
children, so the positive `ef` cross term is attained. The two local
column choices are finite and independent of the other roots after
fixing the one common `b`.

Every one of the four labels chooses one root; unused-root phases
are dominated by an occupied-root choice. Thus the exact finite mask
allocation set is the 256 maps from these four labels to four roots.
The following table is the complete arithmetic certificate for the
local upper profiles:

| Strong graph type | `b` location | Weak/strong integer weights | Maximum numerator |
|---|---|---|---:|
| maximum degree at most two | `b in U` | `z=4`, strong `(3,3)` | 326 |
| maximum degree at most two | two strong edges contain `b` | same | 330 |
| three-edge star | `b in U` | `z=6`, strong `(4,5)` | 489 |
| three-edge star | common star center | same | 501 |
| three-edge star | one private star endpoint | same | 480 |

The first graph type has at most two strong roots containing any `b`
outside `U`; adding a second hit only increases the nonnegative load,
so the displayed two-hit profile bounds zero or one strong hit too.
For a star, the other possible `b` is absent from all selected points
and is dominated by a private-endpoint profile. Separation of `U`
from the strong graph excludes simultaneous weak and strong hits.
Division by 66 or 99 gives the asserted bounds.

The [companion constructor and exact checker](../../frontier/cover-geometry/singleton_pair_blocks.py) preserves supplied actual root and child digits, constructs the positive 21-point law, and verifies two actual consumers with three different weak columns. The triangle consumer attains `5`; the star consumer uses permuted root and child digits and attains `167/33`. Both have disjoint original bad-pair sets, at least five columns, and empty weak common-column intersection. The checker reuses report 434's `exact_gamma` implementation, retaining the shared seven-column phase and reconstructing an attaining original six-label residue vector.

It also verifies the closed local kernels against
all actual local phase choices and then all 256 root allocations for
each of the five profiles. This finite mask arithmetic is the complete
remaining certificate after the general source reduction above; it
is not an experimental cutoff over source sizes or heights.

## Nonrectangular strong roots: an actual cap-six flow suffices

The preceding non-star bound has a more general support condition.
Keep the weak root's three selected points, with column set `U`.
In each of the other three roots, choose three actual children.
Assume that their actual neighborhoods outside `U` admit eighteen
selected points, two different columns per selected child, with at
most six selected points in any global column.

This is an explicit extraction premise. It does not require the
strong roots to be rectangular, nor require the selected pair sets
to be disjoint between roots. Under this premise, give each weak
point integer weight four and each selected strong point weight
three, and divide by 66. This one supported law satisfies

\[
 \boxed{\Gamma\le5<46/9.}
\]

### Constructing and checking the required selection

Use the integral network

```
source -> each of the nine strong children [2]
       -> each actual neighbor outside U [1]
       -> sink [column capacity 6].
```

A flow of value eighteen saturates all child capacities, so it gives
exactly the required actual selection. A failed flow does not
contradict the source-law problem; it rejects this separated-support
construction only. The constructor preserves the actual root and
child digits and assigns the probability before all original phases.

For completeness the exact cut criterion is

\[
 \min_{D\subseteq(\mathbb Z/7\setminus U)}
 \left[6|D|+\sum_{\ell=1}^{9}
       \min\{2,|N_\ell\setminus(U\cup D)|\}\right]\ge18.
\]

Here `D` consists of the source-side columns. For a fixed such set,
each child either pays its incoming capacity two or pays one for
each of its remaining sink-side neighbors. This yields the cut
formula and shows the selection is fully decidable on the actual
source without changing its law or its label phases.

### A general local bound that retains the shared column

Fix the single original modulus-7 column `b`. Let `n_r` be the number
of selected strong points in column `b` in strong root `r`. The
selection gives

\[
 0\le n_r\le3,\qquad\sum_r n_r\le6.
\]

Every strong root has six points of integer weight three, each child
contains two, each root-column contains at most three, and each atom
has weight three. The columns need not form a pair rectangle.

For mask `(p,m,e,f)` of original labels `(5,35,25,175)` in that
root, put `t=1+p`. Expansion of its squared load gives the following
valid integer numerator bound:

\[
 \begin{aligned}
 K_n(p,m,e,f)=3\big[&6t^2+(2t+1)(n+3m+2e+f)\\
                   &+2\big(mn+(e+f)1_{n>0}+me+mf+ef\big)\big].
 \end{aligned}
\]

The single-indicator counts are `n,3,2,1` for the global column,
mixed column, child and atom events. Global-column/mixed-column
intersection has at most `n` points. A global-column/child or
column/atom intersection has at most one point and is empty if
`n=0`. Each remaining pair intersection has at most one point.
These statements concern the same selected points and probability.
They supply every term in the displayed expansion.

The weak root is still bounded by

\[
 W_h(p,m,e,f)=4\big[(1+p+h+m+e+f)^2
                    +2(1+p+h+m)^2\big],
 \qquad h=1_{b\in U}.
\]

If `b` belongs to `U`, separation forces all `n_r=0`. If `b` is
outside `U`, the weak global-column hit is zero and the strong
integer counts satisfy the two displayed constraints. Each of the
four other original nonconstant labels selects one root, so there
are exactly 256 root allocations. Exact finite arithmetic gives

\[
 \max_{\text{allocations}}\left(W_1+\sum_rK_0\right)=326,
\]

\[
 \max_{\substack{\text{allocations},\ 0\le n_r\le3\\
                             \sum_rn_r\le6}}
           \left(W_0+\sum_rK_{n_r}\right)=330.
\]

The second maximization contains 54 possible count triples. Thus the
complete scalar certificate consists of 256 and 13,824 cases. The
displayed maxima are attained with all four mask bits in the weak root
for the first case, and all four in the first strong root with counts
`(3,0,3)` for the second. This does not characterize every maximizer.
Division by 66 proves the bound.
This finite certificate covers all original phases after the exact
source-to-cap reduction; it is not a cutoff over source sizes.

### An actual nonrectangular consumer

Take selected strong child neighborhoods

```
root 2: 01, 02, 01
root 3: 03, 13, 03
root 4: 12, 23, 12.
```

Their actual bad-pair sets are disjoint. Their global selected column
counts are `(5,5,4,4)`, so the displayed eighteen points already give
the required flow. None of the three strong roots is a rectangular
pair block. The weak selected columns can be `4,5,6`, giving a
21-point seven-column source with dispersed weak support. They can
also all be `4`, giving a five-column source. Both are admissible
original sources and satisfy the theorem.

The [companion constructor and checker](../../frontier/cover-geometry/separated_weak_flow.py)
retains nonstandard actual root and child digits, computes the
integral flow, and reuses the original-phase `exact_gamma` oracle
from report 434 to verify the two actual laws and their attained
literal phase vectors. It checks the complete finite cap certificate
with exact arithmetic. Neither consumer is used as a proof of the
general implication.

### The separated extraction is not automatic

Take the actual neighborhoods

```
weak root: {0}, {1}, {2}
strong root 2: 012, 012, 012
strong root 3: 34, 34, 34
strong root 4: 35, 35, 35.
```

There are 24 points and six columns. The weak bad-pair set is the
union of the stars at `0,1,2`; the other bad-pair sets are respectively
empty, `{34}` and `{35}`. They are pairwise disjoint, and exactly
one root is robust. Nevertheless deleting `U={0,1,2}` leaves the
second root empty. The required outside-`U` flow has value twelve,
not eighteen.

Thus original admissibility and strong child degree at least two
alone do not establish this separated-support hypothesis, even
with fewer than three robust roots. This source is a counterexample
to extraction only. No failure of its unrestricted supported-law
problem is claimed. The three-edge-star special law remains a
separate sufficient construction when cap-six selection is unavailable.

## Deleting the other two weak children is not a universal recipe

A distinct control explains why a singleton weak root cannot simply be
replaced by one selected point. Take the actual 22-point source

```
weak root: {3}, {3}, {3,4}
strong roots: three children on 01, three on 02, three on 12.
```

It has five columns and disjoint actual bad-pair graphs. Restrict a
proposed law to the first weak point plus the 18 strong points,
discarding the other two weak children. The weak-centered original
layout has price 36 on that weak point and one on every strong point.
A uniform mixture of the eighteen strong-centered original layouts
has price one on the weak point and `53/9` on every strong point.
Mix the weak-centered layout with probability `44/359` and those
strong-centered layouts with total probability `315/359`. Every
retained point then has expected squared load exactly

\[
 1899/359=46/9+577/3231.
\]

Linearity gives this lower bound for every law on the restricted
19-point support. It refutes only that deletion recipe. The full
source is already covered by the old common-column weak-root case,
and it is not a source-law counterexample.

These repo-derived proofs and certificate checks use ordinary mathematics and exact
arithmetic. No Lean certification or literature priority is claimed.

Run the retained construction and exact controls with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/singleton_pair_blocks.py

Run the nonrectangular flow construction and its exact cap certificate with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/separated_weak_flow.py

## A shared weak/grid block closes the separated-flow boundary class

The cap-six extraction can fail because another root uses exactly the
weak columns. That failure does not imply that a supported law fails.
The following whole class, including the preceding 24-point extraction
counterexample, admits a simple uniform law.

Let `U` be three distinct seven-columns. Assume an actual source contains:

* a weak root with three distinct selected children, one selected point
  in each, using the three different columns of `U`;
* a second root with three selected children, each containing every
  column of `U`;
* two further roots, each with three selected children on a common pair
  `E_1` or `E_2`, where the pairs are distinct and both avoid `U`.

The external pairs may intersect or be disjoint. Select the resulting
`3+9+6+6=24` actual points and give them equal mass. Extra source points
receive zero mass. Then, for all independent original phases,

\[
 \boxed{\Gamma\le5<46/9.}
\]

The probability is fixed before the phases. The shared pure-seven
column can affect both the weak matching and the nine-point grid;
that joint effect is retained throughout the proof.

### Three exact local kernels

Write mask `(p,m,e,f)` for original labels `(5,35,25,175)` entering a
root, put `t=1+p`, and let `h` indicate that the one global modulus-7
column belongs to that root's selected column set. Local phases of
labels 35, 25 and 175 maximize together at the same column and child:
the rectangular strong blocks have constant atom weights, and all
cross terms are nonnegative. In the weak matching, all three local
nonconstant events can use the point hit by the global column, when
that hit is present. Thus, writing `c=h+m`, their exact unnormalized
local maxima are

\[
 M_h=(t+c+e+f)^2+2t^2,
\]

\[
 G_h=(t+c+e+f)^2+2(t+c)^2+2(t+e)^2+4t^2,
\]

\[
 P_h=(t+c+e+f)^2+2(t+c)^2+(t+e)^2+2t^2.
\]

Here `M` is the three-point weak matching, `G` the three-by-three
grid, and `P` a three-by-two external pair block. These are local
maxima at a fixed value of the global column; they do not choose a
separate global phase for each root.

### A direct affine proof of the global bound

For binary mask bits, `2ab <= a+b`. Expand each displayed kernel
and apply this inequality to its nonnegative mixed terms. The result
is an affine upper bound `base + v_p p + v_m m + v_e e + v_f f`, with
coefficients

| Local block | Base | `(v_p,v_m,v_e,v_f)` |
|---|---:|---|
| `M_h` | `3+3h` | `(12+2h,6+2h,6+2h,6+2h)` |
| `G_h` | `9+9h` | `(34+6h,14+6h,14+2h,6+2h)` |
| `P_h` | `6+9h` | `(24+6h,14+6h,10+2h,6+2h)` |

Every one of the four labels selects at most one occupied root, so
the sum of its mask bit over the four roots is at most one.

If the global column `b` belongs to `U`, the actual hit pattern is
`(h_M,h_G,h_{P1},h_{P2})=(1,1,0,0)`. The four bases sum to 36,
and every coefficient vector is coordinatewise at most
`(40,20,16,8)`. The total numerator is therefore at most

\[
 36+40+20+16+8=120.
\]

If `b` is outside `U`, the weak and grid hits are zero. Each external
pair hit is at most one; dominate both by one within this same law.
The bases then sum to 42, and every coefficient vector is at most
`(34,20,14,8)`. Consequently the numerator is at most

\[
 42+34+20+14+8=118<120.
\]

These bounds hold for all original root, child and column phases.
Dividing by 24 proves `Gamma <= 5`. The proof uses no enumeration
of sources or layouts.

For additional exact checking, the full 256 root-mask allocations
at the two dominating global-column profiles have maxima 120 and
112. The first places all four masks in the nine-point grid root.
Thus the uniform laws on the exact displayed templates attain five;
this is sharpness of that specified law, not minimax optimality over
all probabilities on a source.

### Scope relative to earlier criteria

For the exact selected source, the weak root's common-column
intersection is empty and its matching rank is three. The grid root
is robust and has matching rank three. Each external pair root has
rank two. Thus there is only one robust root, the four-root common
column rectangle condition fails at the weak root, and the sorted
matching tuple `(2,2,3,3)` does not dominate any tuple in report 432's
matching table. Its full capped rank sum is ten, so the eleven-point
selector cannot apply; the singleton-plus-three-matchings selector
also lacks the required three strong matchings.

The separated-flow construction still fails when the grid children
have no neighbors outside `U`. The old extraction counterexample
therefore remains a valid counterexample to that recipe. This new
shared-support law closes its indicated source class without claiming
that the extraction became possible or that every singleton source
has been covered.

The [companion constructor and exact checker](../../frontier/cover-geometry/singleton_grid_pair_law.py)
retains actual root and child digits, verifies all three local kernels
against every local phase, checks the affine inequalities, and checks
the 256 root allocations in each profile. It uses report 434's
original-phase oracle on actual intersecting-pair and disjoint-pair
consumers, reconstructing literal six-label phase witnesses. The
second consumer has nonstandard root and child digits. All checks
use exact arithmetic; no Lean certification is claimed.

Run the shared weak/grid construction with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/singleton_grid_pair_law.py
