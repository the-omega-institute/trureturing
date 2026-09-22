[Index](../../marked_head_profile.md) · [Root laws](390-two-prime-root-blockers-admit-a-common-second-moment-law.md) · [Heavy rows](396-a-heavy-row-controls-all-seven-adic-depths.md) · [Stationary mixtures](397-stationary-row-mixtures-control-all-seven-adic-depths.md) · [Exact-root sources](398-six-exact-root-types-control-arbitrary-seven-adic-tails.md)

# Sparse second digits control sources outside the fixed subclasses

Suppose a source at 5-height one has a complete five-ary tree in its
7-projection, and each joint root cell uses at most two second
7-digits. At every finite 7-height `K>=2`, a single probability on
the actual source satisfies the full independent-divisor comparison

\[
 \Gamma_{1,K}\le U_K
 =\frac{88}{25}+4\sum_{j=2}^K(2j+1)5^{-j}
 =\frac{231}{50}-\frac{4K+7}{2\cdot5^K}
 <2t_K,\qquad t_K=3-\frac{K+2}{3^K}.
 \tag{SD1}
\]

The theorem needs no pairwise ternary-tree premise. It includes an
explicit family which does satisfy those pair premises but has no
same-height subsource in any of the classes treated by 396, 397 or
398. Consequently, extracting those fixed-carrier subclasses and
mixing their certified probabilities cannot handle every source;
the new direct law handles this obstruction family.

These are ordinary mathematical arguments and exact finite controls,
without Lean certification. The general `H=1` comparison and
unrestricted Erdős #7 remain unresolved.

## 1. One supported law from a sparse second digit

Let `K>=2` and

\[
 R\subseteq\{1,2,3,4\}\times\mathbb Z/7^K.
 \tag{SD2}
\]

Assume its 7-projection contains a complete five-ary tree of depth
`K`. For every row `r` and first digit `c`, assume

\[
 \left|\{d\in\mathbb Z/7:\exists z,\ (r,c+7d+49z)\in R\}\right|\le2.
 \tag{SD3}
\]

Choose any such five-ary tree. Assign each selected leaf to one
actual available row and give that labelled point mass `5^-K`.
This is one probability `nu` on `R`; different leaves may use
different rows and the tree's children may vary with the prefix.
Every specified 7-prefix of depth `0<=j<=K` has mass at most `5^-j`.

Exactly five first digits are selected. Inside a fixed row and
first digit, SD3 permits at most two second prefixes, each of mass
at most `1/25`. Summing these same-law bounds gives

\[
 \nu(\text{row})\le\frac25,\qquad
 \nu(\text{first 7-digit})\le\frac15,\qquad
 \nu(\text{row, first 7-digit})\le\frac2{25}.
 \tag{SD4}
\]

The original source may have more than five active first digits;
only the selected tree is required to use exactly five. No
independence of row and 7-coordinate is assumed.

## 2. All original divisor labels remain independent

Identify the source with residues modulo `Q=5*7^K` by CRT and set

\[
 \Gamma_{1,K}(\nu)=\max_{(a_d)_{d\mid Q}}
 \mathbb E_\nu\left(\sum_{d\mid Q}
       \mathbf1_{x\equiv a_d\pmod d}\right)^2.
 \tag{SD5}
\]

Each residue `a_d` is freely selected; it need not agree with the
residue at any other divisor. All layouts test the same `nu`.

For the root labels `1,5,7,35`, select a row `r`, column `c`, and
point `(s,d)` independently. Writing root row, column and point
masses as `R_r,C_c,w_(r,c)`, direct expansion gives

\[
 1+3R_r+3C_c+2w_{r,c}
 +(3+2\mathbf1_{r=s}+2\mathbf1_{c=d})w_{s,d}.
 \tag{SD6}
\]

Using SD4 bounds this complete four-label square by

\[
 1+3\frac25+3\frac15+9\frac2{25}=\frac{88}{25}.
 \tag{SD7}
\]

Every remaining nonempty ordered-pair intersection lies in a
specified 7-prefix of depth `j>=2` and therefore has mass at most
`5^-j`. At each such LCM depth there are `2j+1` ordered pairs of
7-exponents and four ordered pairs of 5-exponents. Thus its whole
shell is bounded by `4(2j+1)5^-j`. This includes all plain and
joint divisor labels and yields SD1's expression for `U_K`.

At height two,

\[
 U_2=\frac{108}{25},\qquad
 2t_2-U_2=\frac{178}{225}>0.
 \tag{SD8}
\]

The comparison margin's increment at each new depth `j>=3` is

\[
 (2j+1)(2\cdot3^{-j}-4\cdot5^{-j})>0.
 \tag{SD9}
\]

Indeed `5^2>2*3^2`, and multiplying by five preserves a strict
advantage over multiplying by three. This proves the strict
comparison at every finite height, without extrapolating from
enumeration. The envelope tends to `231/50`, while the target
tends to six.

The same analytic calculation also gives a limited extension.
If each joint root cell uses at most `q` second digits, replace
the row and joint-root caps by `q/5` and `q/25`. The root envelope
becomes `g_q=(40+24q)/25`, with the same later shells. For `q=3`,
the resulting bound tends to `279/50`; at height three it is
`688/125`, below `2t_3=152/27` by `424/3375`. SD9 then gives the
comparison for all `K>=3`. At height two the envelope is
`132/25>46/9`, so this calculation gives no height-two conclusion
for `q=3`. This is an analytic extension; the probability API
below retains SD3's at-most-two-digit input contract.

## 3. The fixed-carrier bridge that fails

Consider sources satisfying two additional full-height conditions:
every pair of rows contains a complete ternary 7-tree, and the full
7-projection contains a complete five-ary tree. A proposed bridge
is to extract subsources `S subseteq R`, at the same height and
in the same literal prime-prefix coordinates, from these classes:

1. **396:** a row with a five-ary tree and ternary trees in every
   pair of the other three rows.
2. **397:** a five-ary tree in every three-row union.
3. **398:** the full source tree premises and an exact A--F root
   graph, up to row and column relabelling.

Their probabilities could then be mixed: expectation is linear
in the law, and the maximum over the same set of independent
layouts is convex, so convex combinations preserve a common
second-moment bound. The family below refutes universal extraction
by containing **no qualifying subsource at all**. The source
hypotheses fail before any mixture coefficients are chosen.

A row permutation and a common 7-prefix tree relabelling do not
change this obstruction. Conditioning on prefixes, discarding
those digits, or changing the carrier is a different operation
and is not excluded.

## 4. A 28-point source with no qualifying component

At height two write the 7-coordinate as `c+7d`. The table gives
all second digits `d` in each joint root cell. First digits 5 and
6 contain no points.

| Row | `c=0` | `c=1` | `c=2` | `c=3` | `c=4` |
| --- | --- | --- | --- | --- | --- |
| 1 | `{4}` | `{0,4}` | `{2}` | `{2,3}` | empty |
| 2 | `{4}` | `{3}` | `{1,3}` | `{0}` | `{0,4}` |
| 3 | `{1,3}` | `{1}` | `{1,4}` | `{1,4}` | `{1}` |
| 4 | `{0,2}` | `{2}` | `{0,4}` | empty | `{2,3}` |

Call this source `S`. Its row sizes are `6,7,8,7`, giving 28
points and 18 occupied root cells. Its root graph strictly
contains

\[
 B=\{(1,3),(2,0),(2,1),(3,0),(3,2),(4,0),(4,4)\},
 \tag{SD10}
\]

which is type B with singleton column 3, hub 0, and private
columns 1, 2, 4.

For each pair, count distinct second digits in first columns
`0,...,4`. The six vectors are

| Pair | Second-digit counts |
| --- | --- |
| 12 | `(1,3,3,3,2)` |
| 13 | `(3,3,3,4,1)` |
| 14 | `(3,3,3,2,2)` |
| 23 | `(3,2,3,3,3)` |
| 24 | `(3,2,4,1,4)` |
| 34 | `(4,2,3,2,3)` |

Each has at least three entries at least three, hence contains
a complete ternary depth-two tree. The full projection has
counts `(5,5,5,5,5)` and is the complete five-by-five digit tree.
Every joint cell has at most two second digits, so SD3 holds.

Every three-row subset of `Z/5` contains at least two nonzero
rows. Their ternary tree intersects any complete five-ary
7-tree: at each node three and five chosen children among seven
have a common child. Hence these pair conditions also verify
the original full product-tree intersection premise.

**No 396 component.** A row cannot have five second children
above any first digit, hence cannot contain a depth-two five-ary
tree. Deleting points cannot create one.

**No 397 component.** Removing rows 1, 2, 3, 4 gives respectively

\[
 (5,3,4,3,5),\quad(5,4,4,4,3),\quad
 (3,4,5,3,4),\quad(3,4,4,5,3).
 \tag{SD11}
\]

Every vector has fewer than five entries at least five. Thus
every three-row union fails the five-ary-tree condition, and the
failure is inherited by every subsource.

**No 398 component.** Every qualifying exact A--F source has a
cell whose tail contains a ternary tree. For A, B, C, D and F,
all cells have the isolating rectangles from section 2 of 398;
in E the six triangle cells have them. An isolating rectangle
and the full product-tree condition force a ternary tail tree
inside the isolated cell. Here every root cell has at most two
children, and so does every subsource. None can supply that
necessary tail tree, under any root relabelling.

Concretely, retaining only the SD10 root cells preserves a
type-B root graph but loses the full tree condition. Rows
`{0,1,2}` and first digits `{2,3,4,5,6}` isolate `(1,3)`, whose
second digits are `{2,3}`. Choosing `{0,1,4,5,6}` under first
digit 3 and arbitrary five-digit sets under the other selected
first digits gives a product tree missing that restricted
source. The additional root cells were needed for the original
full-depth intersections.

## 5. Every height, and the role of conditioning

For every `K>=2`, set

\[
 R_K=\{(r,c+7d+49z):(r,c+7d)\in S,
                         \ 0\le z<7^{K-2}\}.
 \tag{SD12}
\]

All digits after the second are unrestricted. Each selected
ternary or five-ary depth-two tree extends to depth `K` by
choosing respectively three or five children at every later
node. Thus all full-height source premises hold.

A depth-`K` five-ary tree would project to a depth-two one, so
the heavy-row and omitted-row failures persist. A joint root
tail still has at most two first children and cannot contain
a ternary tree of any positive depth. The 398 exclusion also
persists. These failures pass to subsets, proving that no
same-height fixed-carrier component from any of the three
classes exists, for every `K>=2`.

Nevertheless every `R_K` satisfies SD3, so the probability in
section 1 obeys SD1 on this very source. No obstruction to the
target moment bound is asserted.

The coordinate restriction matters. For `K>=3`, conditioning
on first digits `(c,d)=(0,4)` and then forgetting those digits
leaves rows 1 and 2 with unrestricted 7-tails. At height `K-2`
that conditional source satisfies 397's every-three-row
condition. It is not a qualifying component at the original
height: its 7-coordinate was restricted to one depth-two
prefix. The counterexample leaves such conditional or
reslicing approaches available.

## 6. Exact controls and limitations

The [source checker](../../frontier/cover-geometry/fixed_source_subclass_decomposition_obstruction.py)
provides finite tree and actual probability interfaces:

- `select_complete_tree` selects a complete tree with
  prefix-dependent children, or returns `None`;
  `has_complete_tree` decides its existence.
- `audit_fixed_source` checks pair, full, individual-row,
  omitted-row and joint-tail tree conditions at a supplied
  finite height. Its `excludes_fixed_subclasses` flag is a
  sufficient obstruction, not a complete classification
  when that test fails.
- `sparse_second_digit_law` checks SD3, selects a five-ary
  tree, supplies actual row witnesses and returns one
  supported probability. `verify_sparse_law` checks all
  simultaneous prefix caps and the independent root maximum.

The controls verify the literal source, all count vectors,
the type-B subgraph and its lost product-tree witness, and
tail lifts at heights 2 through 5. Those lifts have 28, 196,
1,372 and 9,604 source points. A separate height-three tree
uses children varying with their prefixes. Each constructed
law is checked against all 1,225 independent root layouts
and every prefix cap. Exact arithmetic checks SD1, SD8 and
the comparison increments, together with the analytic
three-second-digit remark; ten invalid-input controls
remain active under `-O`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_source_subclass_decomposition_obstruction.py
```

The all-height conclusions are proved in sections 1--2 and
5; the finite controls do not replace those arguments. The
selected laws at different heights are not asserted to form
a compatible inverse system. No realization of the example
as an actual minimum odd-cover residual is asserted.

Report 394 showed loss of a standalone five-ary test in some
joint fibres of an exact type-B source. Here the full source
has no same-height component in any of the three specified
classes, while a different general source condition gives
the desired common law. The remaining general problem must
also handle sources outside this sparse-second-digit condition.
