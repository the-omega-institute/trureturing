[Index](../../marked_head_profile.md) · [Root types](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [Repeated sources](393-two-digit-seed-controls-repeated-type-b-sources-at-all-heights.md) · [Inheritance boundary](394-standalone-tree-blocking-need-not-pass-to-joint-prefix-fibres.md) · [Stationary mixtures](397-stationary-row-mixtures-control-all-seven-adic-depths.md)

# Six exact root types control arbitrary seven-adic tails

At 5-height one, each of the six exact root types A–F from report 390
admits a single supported probability satisfying the full independent-divisor
second-moment comparison at every positive 7-height. Assume both the
full product-tree obstruction and the standalone 7-tree obstruction.
The higher digits may vary arbitrarily inside the root cells; they
need not repeat the root graph, form a Cartesian product, or have
uniform unrestricted tails.

The exact root projection is essential. Although report 390 finds
one of these graphs inside a general four-row root blocker, deleting
other root cells can destroy the full-height tree conditions used here.
This is a theorem for the six stated source classes at 5-height one,
not an all-source theorem or a realization by an actual odd covering.
The proof and exact rational checks are not Lean-certified.
Unrestricted Erdős #7 remains open.

## 1. Source conditions and the full original-label functional

Fix `K>=1` and

\[
 R\subseteq\{1,2,3,4\}\times\mathbb Z/7^K.
 \tag{CT1}
\]

Read digits from lowest to highest. A complete `b`-ary tree selects
exactly `b` children at each selected nonleaf. Require:

1. `R` meets every product `A x T`, where `A` is a three-element
   subset of `Z/5` and `T` is a complete five-ary 7-tree of depth `K`.
2. The 7-projection of `R` meets every complete ternary 7-tree of
   depth `K`; equivalently, it contains a complete five-ary tree.
3. Its root projection is exactly one of the following graphs,
   after relabelling rows and columns.

| Type | Row 1 | Row 2 | Row 3 | Row 4 | Active columns |
| --- | --- | --- | --- | --- | ---: |
| A | `{a}` | `{b,c}` | `{a,b,c}` | `{d,e}` | 5 |
| B | `{a}` | `{b,c}` | `{b,d}` | `{b,e}` | 5 |
| C | `{a}` | `{b,c}` | `{b,d}` | `{c,e}` | 5 |
| D | `{a}` | `{b,c}` | `{b,d}` | `{e,f}` | 6 |
| E | `{a,b}` | `{a,c}` | `{b,c}` | `{d,e}` | 5 |
| F | `{a}` | `{b,c}` | `{d,e}` | `{f,g}` | 7 |

Distinct letters denote distinct residues modulo 7. The relabelling
only names the existing root cells; all moduli and prefix depths
remain unchanged. In particular the F graph uses all seven columns,
including whichever residue is zero.

Identify CT1 with residues modulo `Q=5*7^K` by CRT. For one freely
chosen residue at each original divisor, including divisor one, put

\[
 \Gamma_{1,K}(\nu)
 =\max_{(a_d)_{d\mid Q}}\mathbb E_\nu
       \left(\sum_{d\mid Q}\mathbf1_{x\equiv a_d\pmod d}\right)^2,
 \qquad
 t_K=1+\sum_{b=1}^K(2b+1)3^{-b}
    =3-\frac{K+2}{3^K}.
 \tag{CT2}
\]

The conclusion is that a single law on the actual `R` satisfies
`Gamma_(1,K)<=2t_K`. The construction below gives a strict inequality
except at the A-type height-one boundary. Every layout tests that
same selected law, with no compatibility required among its phases.

## 2. What the root graph forces inside its cells

For a root edge `(r,c)` define the actual tail set

\[
 R_{r,c}=\{z\in\mathbb Z/7^{K-1}:(r,c+7z)\in R\}.
 \tag{CT3}
\]

**Isolating a cell forces a ternary tail tree.** Suppose a
three-row, five-column rectangle meets the root graph only at
`(r,c)`. If `R_(r,c)` missed a complete five-ary tree of depth
`K-1`, use that tree below column `c` and arbitrary five-ary trees
below the rectangle's four other columns. Together with the selected
rows this is a full product tree missing `R`, contrary to condition 1.
Thus the tail set meets every five-ary tree and, by the tree duality
of report 375, contains a complete ternary tree.

All cells in types A, B, C, D and F have isolating rectangles. For
B, C, D and F, isolate a cell in a double row using that row, the
singleton row and missing row zero, excluding the two other columns
in their union. Isolate the singleton using row zero and any double
row. In A, the same construction handles the singleton, doubles
and `(3,b),(3,c)`; isolate `(3,a)` using rows `{0,2,3}` and excluding
`b,c`. In E, each triangle cell is isolated using row zero, its own
row, and the other triangle row which does not contain its column.

**Exactly five active columns force private five-ary tail trees.**
By condition 2 the full 7-projection contains a complete five-ary
tree. If exactly five root columns are active, all five must be
selected by this tree. The union of the cell tails above each such
column therefore contains a complete five-ary tree of depth `K-1`.
If that column has only one incident root cell, this is a five-ary
tree in that individual cell. This implication uses the singleton
column incidence, not general inheritance to arbitrary joint fibres.

Choose the following tail trees inside the actual source:

| Type | Cells given five-ary tails | Cells given ternary tails |
| --- | --- | --- |
| A | none required | all eight |
| B | `(1,a),(2,c),(3,d),(4,e)` | the three cells in column `b` |
| C | `(1,a),(3,d),(4,e)` | the four cells in columns `b,c` |
| D | none required | all seven |
| E | `(4,d),(4,e)` | the six triangle cells |
| F | none required | all seven |

In E the private cells use the five-column argument. The proof
does not require them to be isolatable. The extra five-ary trees
available in A's private columns are not needed. At `K=1` all tail
trees have depth zero and mean the corresponding nonempty root cell.

## 3. Root probabilities and independent layout maxima

Use the following strictly positive root masses `w_(r,c)`:

| Type | Root law |
| --- | --- |
| A | uniform `1/8` on its eight cells |
| B | `1/9` on each cell in column `b`; `1/6` on each other cell |
| C | `1/6` on `(3,d),(4,e)`; `2/15` on each other cell |
| D | `2/15` on `(1,a),(2,b),(3,b)`; `3/20` on each other cell |
| E | uniform `1/8` on its eight cells |
| F | uniform `1/7` on its seven cells |

These masses sum to one. Inside each cell, distribute its root mass
uniformly over the leaves of its selected tail tree. This constructs
one probability `nu` on actual `R`. No independence between different
source coordinates or agreement between the selected trees is assumed.

For a root law write `R_r` and `C_c` for row and column masses.
Independently selecting a row `r`, column `c` and point `(s,d)`
gives the exact root squared-load expectation

\[
 1+3R_r+3C_c+2w_{r,c}
  +\bigl(3+2\mathbf1_{r=s}+2\mathbf1_{c=d}\bigr)w_{s,d}.
 \tag{CT4}
\]

All absent rows, columns and cells have zero mass and remain admissible
phase choices. The six complete maxima, denoted `g`, are

\[
 (g_A,g_B,g_C,g_D,g_E,g_F)
 =\left(4,\frac{35}{9},\frac{39}{10},\frac{77}{20},
           \frac{29}{8},\frac{25}{7}\right).
 \tag{CT5}
\]

For A, E and F the general cap bound
`1+3 max(R)+3 max(C)+9 max(w)` is attained by selecting a suitable
supported point together with its row and column. The B computation
is the law and root calculation from report 390. For C and D,
substitution in CT4 gives the following maxima grouped by selected
column, still maximizing independently over the row and point:

| Type | Selected column | Maximum |
| --- | --- | --- |
| C | `a` | `47/15` |
| C | any of `b,c,d,e` | `39/10` |
| C | absent | `41/15` |
| D | `a` | `61/20` |
| D | `b` | `77/20` |
| D | `c,d` | `73/20` |
| D | `e,f` | `37/10` |
| D | absent | `53/20` |

For example C attains `39/10` by selecting row 3, column `b` and
point `(3,b)`; D attains `77/20` at row 2, column `b`, point `(2,b)`.
The exact checker independently evaluates the literal square and
CT4 over all 1,225 root layouts per type.

## 4. Common prefix caps at all later depths

Let `b_(r,c)` be the selected tail-tree branching base, either three
or five. Uniform tree leaves give, at every available tail depth
`1<=j<=K-1`,

\[
 \nu(\text{row }r,\text{ column }c,\text{ specified tail prefix})
 \le w_{r,c}b_{r,c}^{-j}.
 \tag{CT6}
\]

Write `G` for the selected root graph and define

\[
 c=\max_v\sum_{r:(r,v)\in G}w_{r,v}\frac3{b_{r,v}},
 \qquad
 a=\max_{(r,v)\in G}w_{r,v}\frac3{b_{r,v}}.
 \tag{CT7}
\]

Since `3/b_(r,v)<=1`, replacing its first power by its
`j`th power only decreases it. Consequently the same law has
plain and joint prefix maxima at full 7-depth `j+1` bounded by

\[
 M_{0,j+1}\le c\,3^{-j},\qquad
 M_{1,j+1}\le a\,3^{-j},\qquad 1\le j\le K-1.
 \tag{CT8}
\]

The resulting exact coefficients are:

| Type | `g` | `c` | `a` | `q=3(c+3a)` | `g+q` |
| --- | --- | --- | --- | --- | --- |
| A | `4` | `1/4` | `1/8` | `15/8` | `47/8` |
| B | `35/9` | `1/3` | `1/9` | `2` | `53/9` |
| C | `39/10` | `4/15` | `2/15` | `2` | `59/10` |
| D | `77/20` | `4/15` | `3/20` | `43/20` | `6` |
| E | `29/8` | `1/4` | `1/8` | `15/8` | `11/2` |
| F | `25/7` | `1/7` | `1/7` | `12/7` | `37/7` |

In particular, a private-cell mass larger than a shared-cell mass
at the root can still have a smaller cap beyond the root because
its tail tree has five children. This is used in B and C; it is
not valid to apply their joint caps at depth zero of the tails.

## 5. The whole root block and every later original label

Retain the complete four-label root square, for divisors `1,5,7,35`,
and bound it by `g`. An ordered pair of the remaining original
divisor indicators has nonempty intersection only in a cylinder at
its LCM. At LCM 7-depth `b>=2` there are `2b+1` ordered pairs of
7-exponents, one ordered pair of 5-exponents with maximum zero,
and three with maximum one. Thus CT8 bounds this entire shell by

\[
 (2b+1)(c+3a)3^{-(b-1)}
   =q(2b+1)3^{-b}.
 \tag{CT9}
\]

This counts all ordered pairs at every original divisor and allows
all independent phases. Set

\[
 s_K=\sum_{b=2}^K(2b+1)3^{-b}
     =1-\frac{K+2}{3^K},\qquad 0\le s_K<1.
 \tag{CT10}
\]

The result is

\[
 \Gamma_{1,K}(\nu)\le U_K=g+q s_K,
 \qquad 2t_K=4+2s_K.
 \tag{CT11}
\]

The exact comparison margins are:

| Type | `2t_K-U_K` |
| --- | --- |
| A | `s_K/8` |
| B | `1/9` |
| C | `1/10` |
| D | `3(1-s_K)/20` |
| E | `(3+s_K)/8` |
| F | `(3+2s_K)/7` |

Every margin is positive at every positive finite height except
type A at `K=1`, where it is zero. In D, the later coefficient
`43/20` exceeds two, but the root margin `3/20` pays the entire
finite excess: `1-s_K=(K+2)/3^K>0`. Its bound tends to six, the
same limit as the target; no strict limiting margin is asserted.
The other five bounds have the limits in the final column above.
These identities prove all heights without extrapolating from
finite enumeration.

## 6. Exact checker and limits of the construction

The [cell-tail checker](../../frontier/cover-geometry/cell_tail_root_type_bound.py)
has reusable functions for a positive rational root law and one
branching base between three and seven per cell. `cell_tail_envelope`
computes its full independent root maximum and CT7–CT11. It reports
whether both affine comparison endpoint margins, `4-g` and `6-g-q`,
are nonnegative. These are sufficient and necessary for the stated
envelope to obey the comparison at every positive finite height.

`mix_cell_tail_laws` takes actual conditional tail probabilities,
checks normalization and every prescribed prefix bound, and forms
one common law with the input root masses. It verifies CT8 directly
on that mixture. A caller applying it to a source supplies conditional
laws supported in that source; the program uses their union as the
mixture support.

The six controls check all 1,260 root rectangles and all 7,350
independent root layouts. They verify the available cell isolators,
the private-column criterion, each coefficient in the table, and
3,336 ordered original-label pairs across heights one through six.
Six depth-three conditional-law fixtures use selected tail trees
whose child sets vary with cell and prefix, and check the actual
mixtures and their caps. These fixtures test the probability
interface; the full source tree premises remain analytic hypotheses.
Eight invalid-input controls check rejection. All calculations are
exact rational arithmetic, and checks remain active under `-O`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/cell_tail_root_type_bound.py
```

The source condition is stronger than merely containing one of
these root graphs. Extra cells can prevent isolation, and deleting
them can remove the only full-height intersections with a product
tree. This report does not repair that inheritance gap for general
root sources, cover higher 5-powers or other primes, or assert that
the separately selected laws at different heights form a compatible
inverse system. It supplies the full original-label comparison for
each of the stated exact-root sources at its given finite height.
