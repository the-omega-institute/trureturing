[Index](../../marked_head_profile.md) · [Sharp source size](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Recursive common laws](401-a-recursive-minimum-source-has-one-law-at-every-height.md)

# Root structure of sharp minimum sources

Fix four row labels `1,2,3,4`, and read seven-adic digits from lowest to
highest. A source `R` of height `K` is admissible when each of its six
row-pair projections contains a complete ternary tree of depth `K`, and
its full projection contains a complete five-ary tree of depth `K`.
There is no requirement that all four rows be active.

This note uses report 400, section 9: every admissible height-`h` source
has at least `5^h+2` points, including at height zero. It also uses its
complement duality: if the leaves of a complete five-ary tree are
partitioned into two sets, exactly one set contains a complete ternary
tree of the same depth.

The results below are ordinary mathematical deductions, with one fixed
fixture checked by an existing exact program. They have not been
Lean-certified. They classify sharp minimum sources; they neither cover
all admissible sources nor settle the unrestricted covering problem.

## 1. Five root columns and two surplus patterns

**Theorem.** Let `K>=2`, let `R` be admissible, and suppose

\[
 |R|=5^K+2.
\]

Choose any complete five-ary tree in the full projection and put
`h=K-1`. Then all points of `R` lie in the five selected root columns.
Their sizes, after reordering, are precisely one of

\[
 (5^h+2,5^h,5^h,5^h,5^h),
 \qquad
 (5^h+1,5^h+1,5^h,5^h,5^h).
 \tag{1}
\]

In particular, there are exactly five active root columns.

Call a selected child **clean** when it has exactly `5^h` source points.
Its points consist of exactly one row label above every leaf of its
chosen five-ary tail tree. A row pair is **good** in a child if its
projection contains a complete ternary tree of depth `h`.

**Proof.** The selected five-ary tree accounts for at least `5^K`
source points. Thus at most two points lie outside its five root
columns. A column with at most two points cannot be good for any row
pair, since `h>=1` and a ternary tree needs at least `3^h>=3` leaves.

If both surplus points lie outside the selected columns, all five
selected children are clean. For any partition of the rows into two
complementary pairs, each clean child is good for exactly one member,
by complement duality. This gives five good-child incidences. The two
root ternary trees require at least six, a contradiction.

If exactly one surplus point lies outside, four selected children are
clean and the fifth has `5^h+1` points. For each complementary
partition, the four clean children contribute four incidences. The
fifth must supply both missing incidences. It is therefore good for
all six row pairs and contains a full five-ary projection tree, making
it admissible at height `h` with `5^h+1` points. This contradicts the
height-`h` lower bound. No point can lie outside. Distributing the two
surplus points inside gives (1). ∎

## 2. A single child with two surplus points

For the first pattern in (1), the exceptional child is itself an
admissible sharp minimum source of height `h`. For each of the three
complementary partitions

\[
 \pi_1=12\mid34,
 \qquad \pi_2=13\mid24,
 \qquad \pi_3=14\mid23,
 \tag{2}
\]

the four clean children divide exactly `2:2` between its members.

Indeed, four clean children provide four incidences; the exceptional
child must supply both remaining incidences for each partition. It is
good for all six row pairs. Each root side now needs at least two good
clean children, forcing the `2:2` division. Conversely, these balances
and an admissible exceptional child imply all six root pair trees;
the five full child trees already imply the full root tree.

## 3. Two children with one surplus point each

For the second pattern in (1), denote the exceptional children by
`B_1,B_2`. Every child containing a complete five-ary tree is good for
at least one member of each partition (2): choose one available row
above each leaf of the contained tree and apply complement duality.
Neither `B_j` is good for all six pairs, since it has only `5^h+1`
points.

Define

\[
 D_j=\{\pi_i:\ B_j\text{ is good for both members of }\pi_i\}.
 \tag{3}
\]

Then the following restrictions hold:

1. Each `D_j` is a proper subset of the three partitions, and
   `D_1 union D_2` is the full three-partition set. Consequently, up to
   exchanging the exceptional children, their sizes are `(1,2)` with
   disjoint sets, or `(2,2)` with a one-partition intersection.
2. In every partition the three clean children divide `2:1` between
   its members.
3. If exactly one exceptional child is double-good for a partition,
   the other exceptional child is good for exactly its clean-minority
   member. The root good-child counts for its two members are `3:3`.
4. If both exceptional children are double-good for a partition, its
   root good-child counts are `3:4`, ordered according to the clean
   minority and majority.

These rules are also sufficient, given the actual child capabilities,
for all six root pair trees. This sufficiency does not assert that
every abstract assignment of capabilities is realizable by a source.

**Proof.** For any partition, the clean children supply three
incidences. If neither exceptional child were double-good, the total
would be only five, so at least one must be double-good. This proves
the union condition. Properness follows from the height-`h` minimum
bound, and the stated two possibilities for cardinalities follow.

The clean split cannot be `3:0`: the empty side could receive at most
two incidences from the exceptional children, below the required
three. Thus it is `2:1`. If only one exceptional child doubles, it
raises this split to `3:2`; the remaining child must choose the minority
side. If both double, the resulting split is `4:3`. These counts prove
necessity and sufficiency. ∎

## 4. Propagation along a one-surplus tail

The double-good data has an additional recursive restriction.

**Lemma.** Let `S` have height `h>=2`, contain a full five-ary
projection tree, and have `5^h+1` points. Suppose at least one partition
in (2) is double-good. Then its unique surplus point lies inside the
five selected root columns, with exactly one child of size
`5^(h-1)+1` and four clean children. Every partition double-good in
`S` is double-good in the exceptional child, and its four clean
children divide `2:2`.

**Proof.** If the surplus point were outside the selected columns,
its singleton column could not support a ternary tree of depth
`h-1>=1`. Five clean children would provide only five incidences for
the assumed double-good partition. Hence it lies inside. For each
double-good partition, four clean children plus one exceptional child
can provide the required six incidences only when the exceptional
child supplies both and the clean children split `2:2`. ∎

Consequently, along the unique exceptional-child path down to height
one, the nonempty double-good partition set only grows. It always has
at most two members, by the minimum admissible-source bound. A
two-partition tail retains exactly those same two partitions throughout;
a one-partition tail can acquire at most one additional partition.
At height one the six points project either to five columns with one
projection leaf carrying two distinct row labels, or to six columns
with one label each.

## 5. A fixed 27-point source with distributed row capabilities

Use the existing report 399 program

[fixed_source_subclass_decomposition_obstruction.py](../../frontier/cover-geometry/fixed_source_subclass_decomposition_obstruction.py)

and construct the source dynamically as

```python
R = fixture(2) - {(3, 30)}
```

The existing `audit_fixed_source(R, 2)` verifies all six pair trees and
the full five-ary tree. Its five child sizes are `(6,5,6,5,5)`. The
actual good-pair sets are:

| Root column | Size | Good pairs | Double-good partitions |
| --- | ---: | --- | --- |
| 0 | 6 | 13, 14, 23, 24, 34 | pi_2, pi_3 |
| 1 | 5 | 12, 13, 14 | none |
| 2 | 6 | 12, 14, 24, 34 | pi_1 |
| 3 | 5 | 12, 13, 23 | none |
| 4 | 5 | 23, 24, 34 | none |

Among the three clean columns, the minority sides are respectively
`34`, `24`, and `14`. In each partition the exceptional child that is
not double-good selects exactly that minority. All six root
good-child counts are three.

Every individual `(row, root column)` cell has at most two distinct
second digits. Accordingly the existing audit reports no ternary
tail in any individual joint cell. This example rules out a reduction
of arbitrary one-surplus tails to monochromatic ternary cell tails:
pair capability can be distributed across its two rows.

The example already falls within report 399's sparse-second-digit
theorem. The existing `sparse_second_digit_law` and `verify_sparse_law`
produce one actual supported law, with exact root maximum `79/25`
over all 1225 independent root layouts and the established envelope

\[
 \frac{108}{25}<\frac{46}{9},
 \qquad \frac{46}{9}-\frac{108}{25}=\frac{178}{225}.
\]

This is a reuse of the existing sparse theorem, not a new common-law
result or a general consequence of the root classification.

## 6. Scope and the remaining common-law bridge

The root theorem explicitly excludes `K=1`: two surplus points outside
the selected five columns can then contribute depth-zero pair trees,
and sharp minimum sources can have six or seven active columns.

The theorem also cannot reduce every admissible source to this sharp
class. Already at `K=1`, the eight-point type-E source

\[
 R_1=\{a,b\},\quad R_2=\{a,c\},\quad
 R_3=\{b,c\},\quad R_4=\{d,e\}
\]

is inclusion-minimal. Removing any point among the first three rows
reduces some pair projection from three columns to two; removing
either row-4 point reduces the full projection from five to four.
It therefore contains no admissible seven-point subsource. This is
the existing type-E obstruction, not a new counterexample family.

The classification and propagation lemma identify a remaining
interface: construct one probability on the two actual one-surplus
tails and the three clean tails, using their compatible pair
capabilities and exceptional paths, which simultaneously controls
the root square and all pure and joint prefix contributions to the
original-divisor layout square. The root capability rules alone do
not yet supply that common law or its second-moment bound. Independent
optimal row, column, and tail laws cannot be substituted for one
joint probability, and monochromatic cell-tree assumptions are
excluded by the fixed example above.
