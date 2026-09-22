[Index](../../marked_head_profile.md) · [Sparse second digits](399-sparse-second-digits-control-sources-outside-fixed-subclasses.md) · [Actual layout dual](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Common-law construction](402-one-common-law-with-a-universal-row-compatible-bound.md)

# A balanced five-tree selection controls all heights

A source containing a suitably balanced labelled five-ary tree has
one actual probability satisfying the target comparison at every
seven-adic height `K>=2`. Let `beta_r` be the row masses of the
uniform tree law and `M_r` its largest mass in a joint row/root-column
cell. The sufficient condition and resulting bound are

\[
\beta_r+3M_r\le\frac{22}{25}\quad\text{for every row }r,
\qquad
\Gamma_{1,K}(\nu)\le U_K\le2t_K-\frac{11}{180},
\tag{BT1}
\]

where

\[
U_K=\frac{17}{4}+4\sum_{j=2}^K(2j+1)5^{-j},
\qquad t_K=\sum_{j=0}^K(2j+1)3^{-j}
=3-\frac{K+2}{3^K}.
\tag{BT2}
\]

The criterion permits a monochromatic root child and applies to a
family outside the earlier sparse-cell and fixed-root sufficient
classes. It is a condition on one actual selected tree, not a
consequence of arbitrary source admissibility. A recursive family
below shows that admissibility can force every uniform full-tree law
to violate it. Neither result decides the general source minimax
comparison or unrestricted Erdős #7. The mathematical arguments and
exact research checks are not Lean-certified.

## The selected tree and the original finite game

Let `R` be a source in `{1,2,3,4} times Z/7^K`, with `K>=2`.
Seven-adic trees read digits from lowest to highest. A complete
five-ary tree selects exactly five children at each selected nonleaf.
Choose a complete tree `T` of depth `K`, and assign one row `r(y)`
to each leaf `y`, with `(r(y),y) in R`. Its uniform labelled law is

\[
\nu(r(y),y)=5^{-K},\qquad y\in T.
\tag{BT3}
\]

This gives one probability on the original source. Define

\[
q_{r,c}=\nu\{(r,y):y\equiv c\pmod7\},\quad
C_c=\sum_rq_{r,c},\quad
\beta_r=\sum_cq_{r,c},\quad M_r=\max_cq_{r,c}.
\tag{BT4}
\]

Exactly five root columns have mass `1/5`; all other root columns
have zero mass. At depth `j`, every selected plain prefix has mass
`5^-j`, and every joint row-prefix has mass at most `5^-j`.

Use CRT to identify `(r,y)` with a residue modulo `5*7^K`. For one
independently selected phase `a_d mod d` at every original divisor,
including divisor one, put

\[
L_{\mathbf a}(x)=\sum_{d\mid5\cdot7^K}
\mathbf1_{x\equiv a_d\pmod d},\qquad
\Gamma_{1,K}(\nu)=\max_{\mathbf a}\mathbb E_\nu L_{\mathbf a}^2.
\tag{BT5}
\]

Phases may be incompatible, and row-zero phases remain allowed.
The probability BT3 is selected once, before these adversarial choices.
The theorem needs only the selected tree and BT1; the pair-ternary
source conditions used elsewhere are not additional premises.

## All independent root phases obey the same bound

Since only five columns carry mass, `M_r>=beta_r/5`. Therefore BT1
implies

\[
\beta_r\le\frac{11}{20}.
\tag{BT6}
\]

Write the phase at divisor five as row `a`, the phase at divisor
seven as column `b`, and the phase at divisor 35 as cell `(s,d)`.
The load of these labels and divisor one is

\[
L_1=1+\mathbf1_{r=a}+\mathbf1_{c=b}+\mathbf1_{(r,c)=(s,d)}.
\]

Expanding under the actual law gives exactly

\[
\mathbb E_\nu L_1^2
=1+3\beta_a+3C_b+2q_{a,b}
+\bigl(3+2\mathbf1_{a=s}+2\mathbf1_{b=d}\bigr)q_{s,d}.
\tag{BT7}
\]

A row-zero indicator vanishes on the source. Replacing such a phase
by an actual-row phase with the same seven-coordinate can only
increase the load, so it suffices to prove the bound for `a,s` in
the four actual rows. Columns outside the selected tree have zero
mass and still obey `C_b<=1/5`.

If `s=a`, the joint terms in BT7 are at most `9M_a`. Hence

\[
\mathbb E_\nu L_1^2
\le\frac85+3\beta_a+9M_a
\le\frac{106}{25}<\frac{17}{4}.
\tag{BT8}
\]

If `s!=a` and `b=d`, the two distinct row masses share one column,
so `q_(a,b)+q_(s,b)<=1/5`. Thus `2q_(a,b)+5q_(s,b)<=1`, and

\[
\mathbb E_\nu L_1^2\le\frac{13}{5}+3\beta_a
\le\frac{17}{4}.
\tag{BT9}
\]

If both rows and columns differ, the joint terms are at most
`2M_a+3/5`. Using BT1 and BT6,

\[
\begin{aligned}
\mathbb E_\nu L_1^2
&\le\frac{11}{5}+3\beta_a+2M_a\\
&\le\frac{11}{5}+\frac{44}{75}+\frac73\beta_a
\le\frac{407}{100}<\frac{17}{4}.
\end{aligned}
\tag{BT10}
\]

These cases exhaust all independent original root phases. They retain
the common column constraint in BT9 rather than adding unrelated
marginal maxima.

## Higher original labels and the finite target margin

Group the ordered terms in `L_a^2` according to their largest
seven-adic depth `j`. For `j>=2` there are `2j+1` ordered depth
pairs and four pure/mixed type pairs. Each nonempty intersection is
one plain or joint row-prefix of depth `j`, so its mass under the
same law BT3 is at most `5^-j`. Incompatible phases only remove
intersections. The contribution from this depth is therefore at most

\[
4(2j+1)5^{-j}.
\tag{BT11}
\]

BT8–BT11 give `Gamma_(1,K)(nu)<=U_K`. At height two,

\[
U_2=\frac{101}{20},\qquad
2t_2-U_2=\frac{46}{9}-\frac{101}{20}=\frac{11}{180}.
\tag{BT12}
\]

For every `K>=2`, the next-height increment of the margin is

\[
\bigl(2t_{K+1}-U_{K+1}\bigr)-\bigl(2t_K-U_K\bigr)
=(2K+3)\left(\frac2{3^{K+1}}-\frac4{5^{K+1}}\right)>0.
\tag{BT13}
\]

This proves the uniform finite margin in BT1. The limiting upper
bound is `107/20`; the finite comparison follows from BT12–BT13,
not from comparing limits alone.

## A family beyond sparse second digits

The sparse-tree law of report 399 has `beta_r<=2/5` and
`M_r<=2/25`, hence `beta_r+3M_r<=16/25`. It is a special case
of BT1. The new criterion also allows `M_r=1/5` whenever
`beta_r<=7/25`, so a monochromatic root child is permitted.

A second extension is a source whose forced row-cell has four
second digits. At height two write `y=c+7d`. The following table
lists the allowed second digits `d` in each row/root-column cell;
all cells in root columns five and six are empty.

| Row | `c=0` | `c=1` | `c=2` | `c=3` | `c=4` |
| --- | --- | --- | --- | --- | --- |
| 1 | `3,4` | `2,3` | `0,1` | empty | `0,1` |
| 2 | `1,2` | `2` | `4` | empty | `1,2,3` |
| 3 | `0` | `0,4` | empty | `2` | `4` |
| 4 | empty | `1` | `0,2,3` | `0,1,3,4` | empty |

The source has 28 points and exactly the full five-by-five
projection. The numbers of distinct second digits in the six pair
unions are

| Pair | Counts in root columns `0,1,2,3,4` |
| --- | --- |
| 12 | `4,2,3,0,4` |
| 13 | `3,4,2,1,3` |
| 14 | `2,3,4,4,2` |
| 23 | `3,3,1,1,4` |
| 24 | `2,2,4,4,3` |
| 34 | `1,3,3,5,1` |

Every pair has three ternary-capable root columns, so the source
is admissible. Here admissibility means those six pair-ternary trees
and a full five-ary projection tree. The four three-row unions,
omitting rows one through four respectively, have count vectors
`(3,4,4,5,4)`, `(3,5,4,5,3)`, `(4,3,5,4,4)`, and `(5,4,3,1,5)`.
None has a complete five-ary tree; neither does any smaller row set.

Select the least available row at each of the 25 projection leaves.
The resulting row counts are `(8,5,5,7)` and the largest root-cell
counts are `(2,2,2,4)`. Consequently

\[
25(\beta_r+3M_r)=(14,11,11,19),
\tag{BT14}
\]

so BT1 holds. In root column three, digits `0,1,3,4` occur only in
row four. Every complete five-tree must use those leaves, and hence
every labelling has at least four second digits in that cell. No
sparse-two-digit tree selection is available. Only root columns
two, three and four have any individual row cell with a ternary
tail. Thus no subsource can supply the five root columns with
individual ternary tails required by the exact A–F interface of
report 398. The absence of proper-row full trees also excludes
the source premises of reports 396 and 397.

The base is inclusion-minimal: deleting a uniquely labelled
projection leaf destroys the full-five projection. The six points
above duplicated leaves are `(1,2)`, `(1,11)`, `(1,15)`, `(2,11)`,
`(2,15)`, and `(4,2)`; deleting them destroys pair trees 12, 13,
14, 24, 23, and 34 respectively. It therefore contains no admissible
27-point subsource, despite the sharp size minimum in report 400.

For every `K>=2`, attach an arbitrary complete five-ary tail tree
of depth `K-2` to each of these 28 labelled points. The tails may
vary with the point and with every prefix. For the 25 selected
points use their corresponding tails to define BT3. Each selected
depth-two leaf has mass `1/25`, preserving BT14. Pair trees extend
using ternary subtrees of the selected five-ary tails, so the
lifted source remains admissible. A forbidden proper-row full tree
or an individual ternary root tail would project to the corresponding
forbidden depth-two tree. The four forced second digits persist.
This proves a full-height family to which the extended criterion
applies, with no repeated-tail hypothesis.

## A necessary restriction on an actual dual counterexample

Let `theta` be one probability on whole literal layouts, and define
`f_theta(x)=E_theta L_a(x)^2`. Suppose its strict superlevel source

\[
R_\theta=\{x:f_\theta(x)>2t_K\}
\tag{BT15}
\]

is admissible. Equivalently its bottleneck rank `B(f_theta)` in
report 400 is greater than `2t_K`. This source cannot contain any
labelled complete five-tree satisfying BT1. Otherwise averaging
BT15 under its actual uniform law would give an expectation above
`2t_K`, while the same average of BT1 over layouts gives at most
`2t_K-11/180`, a contradiction.

Therefore every complete five-tree in such a highset, under every
supported row labelling, must have some row with

\[
\beta_r+3M_r>\frac{22}{25}.
\tag{BT16}
\]

At height two this becomes an integral restriction. If `n_r` is
the row's count among the 25 leaves and `m_r` its largest root-cell
count, then every labelled full-tree witness must have a row with

\[
n_r+3m_r\ge23.
\tag{BT17}
\]

This is necessary for an actual dual counterexample, not sufficient.
The argument uses one whole-layout mixture and one actual supported
law; it does not combine separate optima or unverified pairwise
phase couplings.

## Admissibility does not supply the balanced selection

Take any admissible source `R_0` whose projection is exactly a
complete five-ary tree and whose proper row subsets all fail the
full-five-tree condition. The 28-point base above is one example.
Fix a row `a`. At each new root level construct `R_(h+1)` with
five active columns: three contain copies of `R_h`, and two contain
complete five-ary tails entirely in row `a`. Every child has the
same remaining height.

The full projection is exactly one complete five-ary tree. A pair
excluding `a` gets three ternary-capable children from the continuing
copies. A pair containing `a` gets the two private children and a
continuing copy. Thus all these sources remain admissible.

A proper row subset omitting `a` has at most three active columns.
A proper subset containing `a` fails the full-five-tree condition
in every continuing child by induction, leaving only two good
children. Hence no proper row subset ever has a full-five tree.
In particular no individual row is a full-five-tree row, and the
all-three-row-unions hypothesis remains false.

At total height `K`, the full projection has exactly `5^K` leaves,
so a complete five-tree selection must use all of it. A leaf can
be labelled outside row `a` only if it chooses a continuing child
at every one of the `h` newly added levels. Every supported labelling
of the uniform full-tree law therefore satisfies

\[
\beta_a\ge1-\left(\frac35\right)^h.
\tag{BT18}
\]

For `h>=2`, this is at least `16/25>11/20`, contradicting the
necessary consequence BT6 of a balanced selection. Thus pair-ternary
and full-five admissibility does not guarantee BT1, even after
excluding sources with proper-row full-five trees. This obstruction
concerns all uniform full-tree selections; it does not refute a good
nonuniform law on these sources. The general common-law problem
requires more than a universal balanced-selection theorem.

## Reusable selection test and exact controls

[balanced_five_tree_common_law.py](../../frontier/cover-geometry/balanced_five_tree_common_law.py)
provides `test_selection(height, source, selected)`,
`make_common_law`, and `verify_common_law`. The supplied selection
must have exactly one actual supported row label per leaf and form
a complete five-tree. The test computes BT4 exactly. Valid selections
that fail BT1 return `criterion_met=False`; this tests only that
selection and does not refute another selection or another good law.
Malformed input is rejected separately.

The constructor returns BT3. Its verifier checks exact support and
uniform masses, every actual prefix mass, all 1,225 independent root
layouts, and the finite target margin. `example_family` supplies
varying five-ary tails above the displayed base; `boundary_family`
constructs BT18. The program uses only the standard library and the
sibling literal-layout API, with validation active under `-O`.

The no-argument self-check verifies the positive family through
heights two, three and four, the boundary through two added levels,
and 33 malformed-input controls. The positive family has respectively
28, 140 and 700 source points and exact root maximum `97/25` at all
three heights. Its corresponding universal-margin readouts are
`11/180`, `4801/13500`, and `35117/67500`. These controls support
the implementation; BT7–BT13 and the recursive construction prove
the statements at all heights.

The `--stdin` interface accepts an exact JSON object with `height`,
`source`, and `selected`. It reports the selection test and, when
the criterion holds, the supported law and verification. It performs
no exhaustive search over all possible tree selections and makes
no source-minimax optimality claim.
