[Index](../../marked_head_profile.md) · [Full and pair-tree laws](402-one-common-law-with-a-universal-row-compatible-bound.md) · [Minimum-source structure](403-root-structure-of-sharp-minimum-sources.md) · [Sharper common law](404-a-sharper-common-law-and-its-witness-choice-boundary.md)

# Limits of stationary row mixtures and finite-signature summaries

Two natural summaries do not provide the missing general supported-law
construction. First, weighting omitted-row pair laws by the stationary
final row distribution can produce an actual law exceeding the target
for every mixing coefficient. Second, the eight clean-tree majority
signatures cannot impose a nontrivial fixed convex constraint on the row
distribution of a law with prefix decay strictly faster than the ternary
scale. The second result is an obstruction to that proposed interface,
not a direct second-moment counterexample.

Both statements have explicit families and all-height proofs. They do
not rule out jointly selecting the component trees and probabilities,
using more of the actual source than its signature, or solving the
original supported-law minimax problem. These are ordinary mathematical
results and exact research programs, not Lean-certified declarations.
Unrestricted Erdős #7 remains open.

## 1. Stationary final-row weights do not repair arbitrary components

Consider the following modification of the full-tree and pair-tree
mixture construction. Fix actual tree probabilities `mu` and `eta_rs`
on one source. Write `a` for the row distribution of `mu`, and let

\[
 W_i=\frac13\sum_{\substack{r<s\\r,s\ne i}}\eta_{rs},
 \qquad
 M'_{ir}=\lambda a_r+(1-\lambda)W_i(\text{row }r),
 \qquad 0\le\lambda\le1.
\]

Choose a stationary row probability `beta` for `M'`, and set

\[
 \nu_\lambda=\lambda\mu+(1-\lambda)\sum_i\beta_iW_i.
 \tag{SO1}
\]

Then the final row law is indeed `beta`. Nevertheless, arbitrary legal
choices of the component trees and labels do not yield either the
desired target `2t_K` or a uniform `309/50` ceiling. The construction
below gives one actual admissible source and fixed component choices
at every height, such that SO1 fails for every `lambda`. This is an
actual layout expectation obstruction, not merely a failure of a
prefix-cap relaxation.

### 1.1. Actual source and component laws

For `K>=1`, interpret the digit sets

\[
 F_K=\{0,1,2,3,4\}^K,\qquad T_K=\{0,1,2\}^K
\]

as lowest-digit-first seven-adic residues, and put

\[
 R_K=(\{1\}\times F_K)
       \cup(\{2,3,4\}\times T_K).
 \tag{SO2}
\]

Every row pair contains a ternary tree, and the full projection is the
five-ary tree `F_K`. Choose `mu` uniform on row 1 above `F_K`. For
the three pairs containing row 1, choose their `eta_1r` uniform on
row 1 above `T_K`. For the remaining three pairs choose

\[
 \eta_{23}=\operatorname{Unif}(\{2\}\times T_K),\quad
 \eta_{34}=\operatorname{Unif}(\{3\}\times T_K),\quad
 \eta_{24}=\operatorname{Unif}(\{4\}\times T_K).
 \tag{SO3}
\]

All these are legitimate labelled tree probabilities on the same
source. The row matrix of the omitted-row laws is

\[
 W=\begin{pmatrix}
 0&1/3&1/3&1/3\\
 2/3&0&1/3&0\\
 2/3&0&0&1/3\\
 2/3&1/3&0&0
 \end{pmatrix}.
\]

The resulting `M'` has the stationary probability

\[
 \beta_1=\frac{2+\lambda}{5-2\lambda},\qquad
 \beta_2=\beta_3=\beta_4=\frac{1-\lambda}{5-2\lambda}.
 \tag{SO4}
\]

Direct multiplication verifies stationarity. For `lambda<1` the
transition matrix is irreducible, so this stationary probability is
unique; at `lambda=1` every row jumps to row 1 and the same uniqueness
holds. There is no alternative stationary distribution that avoids
the example.

### 1.2. One actual original-divisor layout

Choose the CRT point with row 1 and all seven-adic digits zero. At
every original divisor of `5*7^K`, select this point's residue. Put

\[
 S_K(q)=\sum_{j=0}^K(2j+1)q^j,
 \qquad t_K=S_K(1/3).
\]

For this layout, the pure prefix mass at depth `j` is

\[
 \lambda5^{-j}+(1-\lambda)3^{-j},
\]

and the selected row-prefix mass is

\[
 \lambda5^{-j}+(\beta_1-\lambda)3^{-j}.
\]

Every ordered pair of depths with maximum `j` has one pure/pure and
three row-constrained intersections. All these events are nested along
the chosen point. Therefore the literal squared-load expectation is

\[
 \begin{aligned}
 L_K(\lambda)
 &=4\lambda S_K(1/5)
   +\bigl(1-4\lambda+3\beta_1\bigr)S_K(1/3)\\
 &=4\lambda S_K(1/5)
   +\frac{(1-\lambda)(11-8\lambda)}{5-2\lambda}S_K(1/3).
 \end{aligned}
 \tag{SO5}
\]

Thus `Gamma_(1,K)(nu_lambda)>=L_K(lambda)`. Equality with the full
maximum is not needed or claimed.

### 1.3. Coefficient optimization does not repair the law

The infinite-series limit of SO5 is

\[
 F(\lambda)
 =\frac{15}{2}\lambda
   +3\frac{(1-\lambda)(11-8\lambda)}{5-2\lambda}
 =7-\frac52\lambda+(4\lambda-1)\frac{2+\lambda}{5-2\lambda}.
 \tag{SO6}
\]

Its minimum on `[0,1]` occurs at

\[
 \lambda_* =\frac{5-3\sqrt2}{2},\qquad
 F(\lambda_*)=\frac{54\sqrt2-51}{4}
 \approx6.341883092.
 \tag{SO7}
\]

This follows by differentiating SO6: the derivative has numerator
`-63/2+90lambda-18lambda^2`, and its only zero in `[0,1]` is
`lambda_*`, with negative derivative before and positive after.

There is also a rational lower certificate avoiding decimal inference:

\[
 \begin{aligned}
 F(\lambda)-\frac{317}{50}
 &=\frac{450\lambda^2-341\lambda+65}{50(5-2\lambda)},\\
 450\lambda^2-341\lambda+65
 &=450\left(\lambda-\frac{341}{900}\right)^2
       +\frac{719}{1800}>0.
 \end{aligned}
 \tag{SO8}
\]

For every finite `K`,

\[
 \frac{S_K(1/5)}{S_K(1/3)}\ge\frac58.
 \tag{SO9}
\]

Indeed, this ratio is the weighted mean of the decreasing sequence
`(3/5)^j`, with positive weights `(2j+1)3^(-j)`, truncated at `K`.
Adding the remaining smaller terms cannot increase the mean. The
full mean is `(15/8)/3=5/8`.

Since `lambda>=0`, SO5, SO6 and SO9 give

\[
 \frac{L_K(\lambda)}{t_K}\ge\frac{F(\lambda)}3
    >\frac{317}{150}>2.
 \tag{SO10}
\]

Thus this actual law fails the target for every finite height and
every coefficient, even when a different coefficient is selected at
each height. Moreover, for every `K>=4`,

\[
 L_K(\lambda)>
 \frac{317}{150}\,t_4
 =\frac{25043}{4050}
 =\frac{309}{50}+\frac7{2025}.
 \tag{SO11}
\]

The proposed stationary recipe with arbitrary legal components cannot
therefore improve the `309/50` ceiling.

The stationary failure belongs to the displayed component choices.
It does not rule out a stronger algorithm that chooses different pair
trees or row labels together with the mixing coefficient. Indeed SO2
has a full five-tree in one row, so the existing heavy-row method from
report 396 supplies a different successful law on the same source.

## 2. Eight signatures lose quantitative row information below the ternary scale

A clean source has exactly one row label above each leaf of a complete
five-ary seven-adic tree. For each of the three complementary partitions

\[
 12\mid34,\qquad13\mid24,\qquad14\mid23,
\]

record `+` when the first pair projection contains a complete ternary
tree and `-` when the second does. Clean-tree complement duality gives
exactly one winning pair in each partition.

### 2.1. The eight states and their majority operation

The row signatures and their opposites exhaust the eight states:

| State | Signature | Winning pairs |
| --- | --- | --- |
| star 1 | +++ | 12, 13, 14 |
| star 2 | +-- | 12, 24, 23 |
| star 3 | -+- | 34, 13, 23 |
| star 4 | --+ | 34, 24, 14 |
| triangle excluding 1 | --- | 34, 24, 23 |
| triangle excluding 2 | -++ | 34, 13, 14 |
| triangle excluding 3 | +-+ | 12, 24, 14 |
| triangle excluding 4 | ++- | 12, 13, 23 |

A star is realized at height one by giving all five leaves its row
label. A triangle excluding row `s` is realized by assigning its other
three rows multiplicities `2,2,1`. Every pair among those three rows
then has at least three leaves, and every pair using `s` has at most two.

At an internal node, its signature is the coordinatewise majority of
its five child signatures. For a fixed pair, a depth-`h+1` ternary
tree exists precisely when at least three children have a depth-`h`
ternary tree in that pair. This is an exact finite state operation,
but the states do not retain leaf counts or probabilities.

### 2.2. Fixed signature with any dominant row

**Construction theorem.** For every one of the eight signatures
`sigma`, every row `r`, and every integer `h>=1`, there exists a clean
height-`h` source `C_(sigma,r,h)` such that

\[
 \operatorname{signature}(C_{\sigma,r,h})=\sigma,
 \qquad
 \#\{(s,y)\in C_{\sigma,r,h}:s\ne r\}
 \le 5\cdot3^{h-1}.
 \tag{SC1}
\]

Start with the height-one star or triangle seed above. To pass from
height `h` to `h+1`, place three copies of the current source in root
children `0,1,2`, and put pure-row-`r` full five-trees of height `h`
in children `3,4`. The three copied signatures outvote the other two
in every coordinate, so the parent still has signature `sigma`.
Only the three copied children have non-`r` leaves. Their number
therefore multiplies by exactly three at each step, proving SC1.
Each constructed source has full projection equal to the digit tree
with digits in `{0,1,2,3,4}`.

This construction does not require different cases for the eight
signatures or for the chosen dominant row. In particular every fixed
signature is compatible with eventual concentration near any row.

### 2.3. Every sufficiently diffuse law is forced toward that row

Fix constants `C>=1` and `1/5<=c<1/3`, independent of height and
source. Let `nu_h` be any probability supported on SC1 whose pure
prefix masses obey

\[
 \nu_h(y\equiv u\pmod{7^j})\le Cc^j
 \quad\text{for every }0\le j\le h\text{ and every }u.
 \tag{SC2}
\]

Since a clean source has a single row label at each projected leaf,
the last-level case implies that every source point has mass at most
`Cc^h`. The exceptional leaf count in SC1 yields

\[
 \nu_h(\text{row}\ne r)
 \le 5C\,3^{h-1}c^h
 =\frac{5C}{3}(3c)^h\longrightarrow0.
 \tag{SC3}
\]

This conclusion holds for every such law, not just for uniform tree
mass. The condition is feasible: uniform mass on all five-tree leaves
satisfies SC2 for `c>=1/5`. For `c<1/5` no fixed finite `C` can permit
these caps at all heights, since even `5^h` maximal leaf masses have
total at most `C(5c)^h`, eventually below one.

### 2.4. No nontrivial fixed row polytope below the ternary scale

For each signature `sigma`, let `P_sigma` be a closed convex subset
of the probability simplex on four rows, fixed independently of
height and source. Suppose that every clean source of every positive
height with signature `sigma` admits some supported probability
obeying SC2 and having row distribution in `P_sigma`.

Apply this assumption to SC1, for each choice of `r`. By SC3, the
row distributions of the assumed probabilities approach the simplex
vertex `e_r`. Closedness puts `e_r` in `P_sigma`. As `r` was arbitrary,
all four vertices belong to `P_sigma`; convexity now gives

\[
 \boxed{P_\sigma=\Delta(\{1,2,3,4\})
        \quad\text{for every }\sigma.}
 \tag{SC4}
\]

Uniformity of `C,c` and independence of `P_sigma` from height are
essential hypotheses. No conclusion is claimed for a polytope that
depends on the actual labelled subtree, or for bounds whose constants
grow with height.

At `c=1/3`, a nontrivial particular face is possible. For each
signature choose one of its winning pairs `A_sigma`. Every clean
source with that signature has a ternary tree in that pair. Selecting
an available row in the pair above each of its leaves and giving
uniform mass yields pure prefix caps `3^(-j)` and row distribution
in the proper face

\[
 P_\sigma=\{p:p(A_\sigma)=1\}.
\]

This supplies a specific universal face at the endpoint. It does not
assert existence for arbitrary row polytopes, simultaneous balance of
all three partitions, or the target second-moment budget.

### 2.5. Relation to one-surplus partition states

Report 403's nonempty sets `D` mark those complementary partitions
for which both sides survive in a one-surplus subtree. Along its
exceptional path, a partition in `D` requires the four clean sibling
signatures to divide `2:2`. The clean signatures can satisfy those
counts while their fast-decaying leaf laws are concentrated in the
same actual row: prescribe any such signatures and apply SC1 with
the same dominant row to each sibling.

For example the four star signatures, one of each row, divide `2:2`
for every partition. Yet SC1 realizes all four with the same chosen
dominant row and SC3 forces every uniformly fast law on each to
approach that row. Thus the finite signature and `D` data preserves
the tree-winning relationships but does not supply the required
probability balance. This does not contradict the compatibility
classification or rule out measures using more of the actual source.

## 3. Reusable constructors and exact controls

The standard-library program
[row_summary_interface_obstructions.py](../../frontier/cover-geometry/row_summary_interface_obstructions.py)
provides two general constructors:

- `stationary_counterexample(height, coefficient, distinguished_row=1)`
  accepts any positive integer height, any exact rational coefficient
  in `[0,1]`, and any of the four rows. It returns the actual source,
  full-tree law, all six pair laws, omitted-row laws, row transition
  matrix, stationary row probability, their actual mixture, and one
  literal phase at every original divisor. Row relabelling changes
  those phases explicitly; it does not identify different moduli.
- `signature_source(height, kind, centre, dominant)` constructs SC1
  for every positive height, either a star or a triangle, any centre
  and any dominant row. `measured_signature` evaluates the six actual
  pair-tree predicates using the existing independent tree API.

Running without arguments emits fixed controls as JSON and writes no
files. Seven stationary controls use heights one and four, coefficients
`0,3/8,1`, and a further relabelled example. Rational matrix multiplication
checks stationarity, while the original-divisor API evaluates the
actual law under the displayed layout. At height four and coefficient
`3/8`, it returns

\[
 L_4=\frac{3584713}{573750},\qquad
 L_4-2t_4=\frac{227213}{573750}>0.
\]

The signature controls check all eight signatures and four dominant
rows at heights one, two and four: 96 actual clean sources. Their
maximum exceptional leaf counts are `5,15,135`, respectively. A separate
mixed-child example checks the coordinatewise majority operation, and
a ternary witness entirely outside the dominant row checks the endpoint.
Twenty-six malformed public-input controls reject nonliteral heights or
rows, invalid signature types, and inexact or out-of-range coefficients.
The program imports only the existing sibling original-divisor and tree
certificate API.

These finite checks verify implementations and their interpretation as
actual probabilities and trees. The uniform coefficient and height
assertions follow from SO8--SO11 and the recursive proof of SC1--SC4,
not from testing a cutoff. No optimization over arbitrary sources or
all component choices is performed.
