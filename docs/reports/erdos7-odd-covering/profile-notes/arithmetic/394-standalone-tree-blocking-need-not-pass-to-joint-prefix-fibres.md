[Index](../../marked_head_profile.md) · [Root laws](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [Repeated type-B sources](393-two-digit-seed-controls-repeated-type-b-sources-at-all-heights.md)

# Standalone tree blocking need not pass to joint prefix fibres

A source can meet the full depth-two product-tree tests and the separate
one-coordinate tree tests while some joint root fibres fail the separate
7-coordinate test at the next digit. The explicit source below has 116
points and an edge-minimal type-B root projection. Thus pruning root
cells while preserving the root product test cannot remove those fibres.

This obstructs inheritance of a hypothesis used by report 390. It does
not obstruct every recursive choice of conditional probability laws:
the thin fibres themselves have small second-moment laws, and an explicit
law on the whole source satisfies the proposed height-two comparison.
No realization as an actual minimum odd-cover residual is asserted.
These are ordinary proofs and exact controls, without new Lean content
or a resolution of Erdős #7.

## 1. A source satisfying the full tree conditions

Let

\[
 B=\{(1,1),(2,2),(2,3),(3,2),(3,4),(4,2),(4,5)\},
 \qquad A=\{1,2,3,4\},\qquad C=\{1,2,3,4,5\}.
 \tag{JF1}
\]

Use the following 7-tail sets at the three hub root cells:

\[
 T_{(2,2)}=\{1,2,3\},\qquad
 T_{(3,2)}=\{2,3,4\},\qquad
 T_{(4,2)}=\{3,4,5\}.
 \tag{JF2}
\]

At each of the four other root cells put `T_e=C`. Define the source
in `Z/25 x Z/49` by

\[
 R=\{(r+5a,c+7b):(r,c)=e\in B,\ a\in A,\ b\in T_e\}.
 \tag{JF3}
\]

Its size is `4*4*5+3*4*3=116`. Its root projection is exactly `B`,
and neither coordinate uses its zero first root.

Every three-row set in `Z/5` contains at least two active rows of
`B`. Every pair of active rows has at least three distinct neighbors,
which meet every five-column set in `Z/7`. Hence `B` meets every
three-by-five root rectangle.

Inside any root cell, the tail fibre is the full rectangle `A x T_e`.
Every three-element set of 5-digits meets `A`, and every five-element
set of 7-digits meets `T_e`, whose size is at least three. Given any
complete ternary depth-two 5-tree and complete five-ary depth-two
7-tree, first choose a root cell in their root rectangle. The chosen
nodes' child sets then meet that cell's tail rectangle. This gives an
actual point of `R` in the product of the two trees.

The 7-projection is exactly the complete five-ary depth-two tree

\[
 \{c+7b:c,b\in C\}.
 \tag{JF4}
\]

For root column 2 this uses `T_(2,2) union T_(3,2) union T_(4,2)=C`;
each other occupied root column already has its full tail `C`.
The set `C` meets every three-element subset of the seven digits,
so JF4 meets every complete ternary 7-tree. Similarly, the 5-projection
is `A x A` in digit coordinates and meets every complete ternary 5-tree.
These are full depth-two intersection statements.

## 2. Joint conditioning loses the standalone 7-test

Condition on a hub root pair `(r,2)`, for `r=2,3,4`. The actual tail
source is

\[
 R_{(r,2)}=A\times T_{(r,2)}.
 \tag{JF5}
\]

Its 7-projection has only three roots. A depth-one set meets every
ternary 7-tree precisely when it has at least five roots. For example,
the three missing-digit tests `{0,4,5}`, `{0,1,5}`, and `{0,1,2}`
miss the respective sets in JF2. The standalone test inherited by the
union over a 7-root therefore need not hold after fixing the 5-root too.

This defect cannot be removed by deleting root cells while retaining
the three-by-five root condition. Every edge of `B` can be isolated
by such a rectangle. For `(1,1)`, take rows `{0,1,2}` and columns
`Z/7 minus {2,3}`. For a hub edge `(r,2)`, take rows `{0,1,r}` and
columns `Z/7 minus {1,r+1}`. For a private edge `(r,r+1)`, use the
same rows and columns `Z/7 minus {1,2}`. Each rectangle meets `B`
in exactly its designated edge. Any root subset satisfying all the
rectangle tests must consequently retain every edge, including all
three hub cells.

In particular, a recursive construction that requires the hypotheses
of report 390 at the root and again in every selected joint root fibre
cannot be extracted from `R`. Its child requirement of at least five
7-roots fails in JF5. Injective coordinate relabelings that preserve
prefixes cannot increase those fibres' three 7-roots, even when the
relabelings may depend on the preceding prefixes.

The requirement here concerns the hypothesis class of report 390,
not every smaller support used by its probability constructions.
Conditional probability recursion remains possible. For example,
the uniform law on the full `4 x 3` rectangle JF5 has row, column
and atom caps `(1/4,1/3,1/12)`. Report 390's exact load expansion
therefore gives

\[
 \Gamma_{35}\le1+3/4+1+9/12=7/2<4.
 \tag{JF6}
\]

Thus failure to inherit the standalone test does not imply failure
to choose a useful conditional law.

## 3. A common law passes the height-two comparison

Give the isolated root point and each private root point mass `1/6`,
and each hub root point mass `1/9`, as in report 390. Within each
actual rectangle `A x T_e`, distribute that mass uniformly. This is
one probability on the whole source. Its 80 nonhub atoms have mass
`9/1080=1/120`; its 36 hub atoms have mass `10/1080=1/108`.

For this law, let `M_ab` be the maximum mass of a joint prefix cell
at depths `(a,b)`. The five caps beyond the root square are

\[
 M_{20}=\frac5{72},\qquad M_{02}=\frac19,\qquad
 M_{21}=\frac1{24},\qquad M_{12}=\frac1{27},\qquad
 M_{22}=\frac1{108}.
 \tag{JF7}
\]

Indeed, each 5-tail digit divides its root-row mass by four, giving
`M_20=(1/9+1/6)/4`. At 7-root 2 and tail digit 3 all three hub
fibres contribute `(1/9)/3`, giving `M_02=1/9`; other occupied
7-roots have tail mass `(1/6)/5`. Fixing both roots and one further
5-digit gives maximum `(1/6)/4`, while fixing one further 7-digit
gives `max((1/9)/3,(1/6)/5)=1/27`. Fixing both further digits gives
`max((1/9)/12,(1/6)/20)=1/108`.

For any independent layout on all nine divisors of `1225`, retain
the squared root load from `{1,5,7,35}`. Its expectation is at most
`35/9` under this very law's root marginal, by report 390. Every
remaining ordered pair of divisor indicators has an empty
intersection or one prefix cylinder at its LCM. The LCM exponents
`(2,0),(0,2),(2,1),(1,2),(2,2)` occur respectively
`5,5,15,15,25` times. Thus

\[
 \Gamma_{1225}\le\frac{35}{9}
       +5M_{20}+5M_{02}+15M_{21}+15M_{12}+25M_{22}
       =\frac{335}{54}<\frac{529}{81},
 \qquad
 \frac{529}{81}-\frac{335}{54}=\frac{53}{162}>0.
 \tag{JF8}
\]

All nine divisor residues remain independent. The caps are upper
bounds under one law; their simultaneous attainment is not assumed.
JF8 is an analytic upper bound, without a claim of its sharpness or
of minimax optimality. The same source therefore exhibits failed
hypothesis inheritance together with a successful full-layout law.

## 4. Exact controls and scope

The [standard-library checker](../../frontier/cover-geometry/joint_prefix_fibre_blocking_obstruction.py)
constructs the 116 points, checks all 210 root rectangles and all
1,470 fibre rectangles, and supplies seven isolating root rectangles.
It reconstructs both full coordinate projections and checks the
standalone digit intersections. These local checks support the
depth-two tree proof; the program does not enumerate every full tree.

For the specified law it reconstructs the actual root marginal and
all nine prefix maxima, directly evaluates all 1,225 independent root
layouts, and counts all 81 ordered pairs of the original nine divisor
labels. Exact rational arithmetic verifies JF8. Checks remain active
under `-O`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_prefix_fibre_blocking_obstruction.py
```

The obstruction concerns passage of standalone tree blocking to joint
prefix fibres, including attempts to recover that passage by pruning
root cells. It leaves broader conditional-law constructions and the
general full-height second-moment problem unresolved.
