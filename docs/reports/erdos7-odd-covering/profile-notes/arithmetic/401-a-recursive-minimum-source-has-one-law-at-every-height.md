[Index](../../marked_head_profile.md) · [Exact source dual and sharp size](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Exact root classes](398-six-exact-root-types-control-arbitrary-seven-adic-tails.md)

# A recursive minimum source has one law at every height

A recursive four-row source attaining the sharp size `5^K+2` admits
one actual probability satisfying the full original-divisor comparison
at every positive seven-adic height. Its uniform bound is `4059/700<6`,
and its margin against the finite-height target is at least `43/1764`.
The construction also permits arbitrary common leaf colourings translated
among the four rows: the private branches need not stay in fixed rows.
For heights at least two, the uncoloured construction has eight root
cells, every row has degree
two, and no same-height source from the heavy-row, stationary-mixture or
six-exact-root classes can be selected inside it.

The proof uses an explicit probability, its actual prefix masses, and
independent phases at all original divisor labels. It is ordinary
mathematics with exact checks, not Lean certification. It proves a
restricted source theorem, not the arbitrary-source comparison or
unrestricted Erdős #7.

## 1. One continuing branch and four private branches

Let `F_h` be a complete five-ary subtree of the seven-adic tree of
height `h`; a standard choice uses digits `0,...,4`. Digits are read
from lowest to highest. For a probability `nu` on the four-row carrier,
use the original-label functional of report 398:

\[
 \Gamma_{1,K}(\nu)=\max_{(a_d)_{d\mid5\cdot7^K}}
 \mathbb E_\nu\left(\sum_{d\mid5\cdot7^K}
          {\bf1}_{x\equiv a_d\pmod d}\right)^2.
\]

Here `x` is the CRT point, divisor one is included, and every residue
is chosen independently, including phases whose 5-coordinate is zero.
At height zero put

\[
 R_0=\{(1,0),(2,0),(3,0)\}.
 \tag{RC1}
\]

At height `K>=1`, give root column zero the source `R_(K-1)` in its
remaining digits. For each row `r=1,...,4`, give private root column
`r` that row times a full five-ary tail tree of height `K-1`. Thus

\[
 R_K=\{(r,7y):(r,y)\in R_{K-1}\}
 \ \cup\ \bigcup_{r=1}^4\{(r,r+7y):y\in F_{K-1,r}\}.
 \tag{RC2}
\]

The four private trees may differ. Five distinct root columns may be
renamed, and the same construction may use different root labels at
each recursive node; only prefix depths and row incidences are used.
The explicit labels in RC2 fix one convenient representative.

Every row pair gets two private branches and a ternary tree in the
continuing branch, so its projection contains a ternary tree of height
`K`. The full projection has five branches, each containing a five-ary
tail tree. Inductively,

\[
 |R_K|=4\cdot5^{K-1}+|R_{K-1}|=5^K+2.
 \tag{RC3}
\]

Report 400 proves that this cardinality is minimal under these seven
tree conditions. For the standard private trees, every nonzero leaf
with digits in `0,...,4` has a unique row: its first nonzero digit.
The all-zero leaf occurs in three rows. This is another attainment of
the same minimum as the type-C construction there.

## 2. The supported probability

Fix

\[
 \alpha=\frac27,\qquad p=\frac5{28},\qquad \alpha+4p=1.
 \tag{RC4}
\]

Let `nu_0` be uniform on RC1. In `nu_K`, put mass `alpha` in the
continuing branch, distributed as `nu_(K-1)`, and put mass `p` in each
private branch, uniformly over that branch's actual five-ary tree.
This is one probability on `R_K`, chosen before any layout phases.

Writing `a_(K,r)` for its row masses, every step gives
`a_(K,r)=p+alpha*a_(K-1,r)`. Hence the three initially occupied rows have
mass `1/4+alpha^K/12`, and the fourth has mass `1/4-alpha^K/4`. In particular,

\[
 a_K^{\max}=\frac14+\frac{\alpha^K}{12}\le\frac13.
 \tag{RC5}
\]

The same law works on any larger actual source containing this recursive
subsource. No pruning theorem for an arbitrary source is asserted.

## 3. Exact control of the four-label root square

For the root law of `nu_K`, write `a_r=a_(K-1,r)`. The continuing cell
in row `r` has mass `alpha*a_r`, and its private cell has mass `p`.
The row maximum is `Rmax=p+alpha*max_r a_r`; the continuing column has
mass `alpha`, each private column has mass `p`, and all other cells or
columns have zero mass.

For arbitrary independently selected root phases at `5,7,35`, the
exact root-square expectation is the expression CT4 of report 398:

\[
 1+3R_r+3C_c+2w_{r,c}
 +(3+2{\bf1}_{r=s}+2{\bf1}_{c=d})w_{s,d}.
 \tag{RC6}
\]

Let `q=alpha*max a_r<=alpha/3`. The maximum of RC6 is

\[
 g_K=1+3Rmax+12p
     =\frac{109}{28}+\frac1{14}\alpha^{K-1}.
 \tag{RC7}
\]

Here is a case bound retaining independent phases. If the mixed phase
selects a private cell and the pure column is private, RC6 is at most
`1+3Rmax+12p`. A continuing pure column instead gives at most
`1+3Rmax+3alpha+2q+5p`. If the mixed phase selects a continuing cell,
a continuing pure column gives at most `1+3Rmax+3alpha+9q`, and a private
pure column gives at most `1+3Rmax+5p+5q`. These are all bounded by RC7
because

\[
 3\alpha+2q\le7p,\qquad
 3\alpha+9q\le12p,\qquad 5q\le7p.
 \tag{RC8}
\]

An absent column or mixed cell contributes zero in its corresponding
terms and obeys the same bound; for an absent mixed cell one may use
`3alpha+2p<=12p`. All these inequalities hold for RC4 and `q<=alpha/3`.
Choosing a row of largest mass and its private column and private cell
attains RC7. Phases selecting absent row zero are included.

## 4. Every deeper prefix belongs to that same law

For `1<=b<=K`, let `M_(0,b)` and `M_(1,b)` be the largest masses of a
specified seven-adic prefix, respectively without and with a specified
row. Then

\[
 M_{0,b}\le\alpha^b,\qquad
 M_{1,b}\le p\alpha^{b-1}.
 \tag{RC9}
\]

A prefix which follows the continuing branch for all `b` steps has
mass `alpha^b`; its joint row mass is at most `alpha^b/3`, bounded by
the second expression because `alpha/3<=p`. If it first enters a
private branch after `i<b` continuing steps, its mass is at most
`alpha^i*p*5^{-(b-i-1)}`. This is at most `alpha^b` and at most
`p*alpha^(b-1)`, using `p<=alpha` and `1/5<=alpha`. Uniform leaves of
any selected five-ary tree obey the same prefix bound, so RC9 does not
require the standard consecutive-digit trees.

Now retain the whole root square RC7. For every deeper shell `b>=2`,
an ordered pair of original-divisor indicators either has empty
intersection or meets in a cylinder at their literal LCM. At maximum
7-exponent `b`, there are `2b+1` ordered exponent pairs; at maximum
5-exponent zero there is one pair, and at maximum 5-exponent one there
are three. RC9 therefore gives

\[
 \Gamma_{1,K}(\nu_K)\le U_K
 :=\frac{109}{28}+\frac1{14}\alpha^{K-1}
    +\frac{23}{28}\sum_{b=2}^K(2b+1)\alpha^{b-1}.
 \tag{RC10}
\]

This expands every label `d|5*7^K`, including one, with arbitrary
independent residues. It does not tensorize separately optimized laws
or impose a common centre on the phases.

## 5. The finite comparison and its smallest margin

Put `T_K=2t_K=6-2(K+2)/3^K` and `d_K=T_K-U_K`. Directly,

\[
 d_1=\frac1{28},\qquad d_2=\frac{43}{1764}>0.
 \tag{RC11}
\]

The successive increases are

\[
 T_{K+1}-T_K=\frac{4K+6}{3^{K+1}},\qquad
 U_{K+1}-U_K=\frac{23K+32}{14}\left(\frac27\right)^K.
 \tag{RC12}
\]

The ratio of the second to the first is

\[
 r_K=\frac{3(23K+32)}{28(2K+3)}\left(\frac67\right)^K.
 \tag{RC13}
\]

It has `r_2=2106/2401<1` and is strictly decreasing. Indeed
`r_(K+1)/r_K<1` reduces to

\[
 7(23K+32)(2K+5)-6(23K+55)(2K+3)
 =46K^2+179K+130>0.
 \tag{RC14}
\]

Thus `d_K` strictly increases from `K=2` onward. Its global minimum
for positive heights is `43/1764`. Also,

\[
 U_K\uparrow\frac{4059}{700}<6,
 \qquad d_K\longrightarrow\frac{141}{700}.
 \tag{RC15}
\]

The finite sum in RC10 has the exact closed form

\[
 U_K=\frac{4059}{700}
      -\frac{115K+206}{50}\left(\frac27\right)^K.
 \tag{RC16}
\]

Consequently the constructed common law satisfies
`Gamma_(1,K)<=U_K<2t_K` for every positive height.

## 6. Why the existing fixed-subsource classes do not suffice here

For the original, uncoloured construction RC2 with `K>=2`, the
continuing source has all four rows active. The root
support consists of four continuing cells and four private cells, with
every row of degree two. A single row uses only two root columns, so
cannot contain a five-ary tree. Omitting a row loses its private column;
the other three rows use only four columns, so their union cannot
contain a five-ary tree. These facts exclude reports 396 and 397 even
as same-height subsources.

Every root edge is indispensable to the pair-tree conditions. Removing
a private edge leaves any pair using its row only one other private
column and the continuing column. Removing a continuing edge in row
`r` leaves a pair `{r,s}` with only row `s` in that column. But a single
row in `R_(K-1)` uses at most two root columns, so contains no ternary
tree when `K-1>=1`. That pair then has only its two private good columns.
Thus neither deletion can preserve the pair-tree conditions. A proper
root subgraph cannot be used, and the eight-cell, degree-two root is
none of the exact A–F roots of report 398. In particular, type E also
has eight cells and row degrees all two, but its column degrees are
`(2,2,2,1,1)`, whereas this root has `(4,1,1,1,1)`.

Each private root cell contains five second digits, so the sparse-cell
hypotheses of report 399 also fail. These are exclusions of those
specified sufficient classes, not an impossibility of other conditioning
or reslicing methods. RC10 controls the present family directly.

## 7. Leaf-dependent row labels preserve the same law

Identify the four rows with the Klein group `V=(Z/2)^2`; this only
names the four existing nonzero residues modulo 5. At each recursive
node take an abstract complete five-ary tree `F` of height `K-1`, a
colouring `c:F_leaves -> V`, and four rooted, level-preserving tree embeddings
`i_g` of `F` into actual seven-adic tail trees. The images may differ.
In private root column `g`, put exactly the points

\[
 \{(g+c(y),\ i_g(y)):y\in F_{\rm leaves}\}.
 \tag{RC17}
\]

The displayed tail coordinates are understood within their respective
private root columns. Keep the recursively constructed source in the
continuing column. The colouring and embeddings may change at each
recursive node. Constant colour zero gives the original construction,
including its four independently chosen private trees.

**The tree premises remain valid.** Every two-element row set `A` is
a coset of an index-two subgroup of `V`. Choose `d` outside that
subgroup. For private columns `g` and `g+d`, the abstract leaf sets
whose row belongs to `A` are complementary subsets of `F`. In a
complete five-ary tree, exactly one of a leaf subset and its complement
contains a complete ternary tree: at each node at least three of five
children select exactly one side, so induction proves the assertion.
Pair the four private columns by translation by `d`. Exactly two
private columns are good for `A`; the continuing source supplies its
third good column. The full projection still contains a five-ary tree.
Each private leaf carries exactly one row, so RC3 is unchanged.

**The probability is still common to all layouts.** Give each private
leaf mass `p/5^(K-1)` and the continuing source mass `alpha`. For every
abstract leaf, the four translations `g+c(y)` exhaust the four rows.
Consequently all private branches together contribute exactly mass
`p` to each row, and the row recurrence RC5 still holds. Each private
root column has mass `p`, each of its cells has mass at most `p`, and
the continuing column and cell bounds remain `alpha` and `q`.

Those inequalities are all the four root cases in section 3 use.
They give root cost at most `g_K`; equality is not asserted for a
nonconstant colouring. Plain prefix masses inside a private tree are
unchanged, and a joint row-prefix mass is bounded by its plain prefix
mass. Therefore RC9 and the full original-label bound RC10 hold
unchanged, as do the finite comparison and uniform margin RC11–RC16.

This extension preserves actual joint distributions; the group
translations are used to construct row labels and do not identify or
restrict any of the independently chosen congruence phases.

## 8. Pair-tree counts alone do not preserve this probability

The shared colouring in section 7 supplies actual row balance, not
just the count of good private branches. The latter count by itself
does not justify keeping the same branch weights.

At height two, use the original `R_1` in continuing column zero.
In private columns one and two, put all five tail digits `0,...,4`
in row one. In each of private columns three and four, put tail
digits zero and one in row two, digits two and three in row three,
and digit four in row four. This source still has 27 points.

Every pair containing row one has its two good private columns one
and two: in columns three and four its other row has at most two
tail digits. A pair avoiding row one has its two good private
columns three and four: its two rows together have at least three
tail digits. The continuing column supplies the third good child
in every case, and all five columns have full five-ary projections.
Thus every source premise holds, and the cardinality is minimal.

Nevertheless, put the same masses `alpha=2/7` in the continuing
source, using `nu_1`, and `p=5/28` uniformly in each private column.
The resulting row-one mass is `64/147`. Choose the actual original
phases

\[
 (a_1,a_5,a_7,a_{35},a_{49},a_{245})=(0,1,1,1,1,1).
\]

The expectation of the literal squared load is

\[
 \mathbb E_\nu\ell^2=\frac{253}{49}
   =\frac{46}{9}+\frac{23}{441}>2t_2.
 \tag{RC18}
\]

For a direct calculation, the continuing branch contributes
`51/98`; the two pure-row private branches together contribute
`30/7`; and the other two branches together contribute `5/14`.
Their sum is RC18. The certificate below also evaluates the
original six congruence indicators independently.

This rules out the stated equal-private-mass construction for
arbitrary pair-balanced branches. It does not rule out a different
supported probability on this source, and is not a counterexample
to the desired arbitrary-source bound.

## 9. Exact constructor and finite controls

The standard-library program
[recursive_minimum_source_common_law.py](../../frontier/cover-geometry/recursive_minimum_source_common_law.py)
constructs `law(K)` and `coloured_law(K, colour)` with exact rational
point masses. It imports the sibling original-divisor certificate,
prints its checks as JSON, and writes no result files. Its explicit
trees use digits `0,...,4`; arbitrary tree embeddings in section 7
are covered by the proof, not by exhaustive program enumeration.

The controls check the original and a last-digit-coloured family
through height five: source sizes `7,27,127,627,3127`, all six pair
trees and the full five-tree, row masses, actual prefix maxima,
and the finite comparison. The last-digit colouring maps digits
`(0,1,2,3,4)` to Klein elements `(0,0,1,2,3)`. All 1,225 independent
root layouts are checked at each coloured height. Strict input
checks reject 51 malformed height, root-parameter and colour inputs.

At height two, exact maximization of the six original labels gives
`907/196` for the original law and `853/196` for the coloured law.
For each root layout the two remaining tail phases are maximized
by separating their additive contributions and their possible
coincidence; this ranges over all `49*245` tail-phase pairs without
requiring them to agree. The attaining original residue tuples
are respectively `(0,1,1,1,1,1)` and `(0,1,0,21,7,56)`, independently
checked by the literal congruence evaluator. The program also
checks the actual source and the failing probability in RC18.

These are exact finite controls for the all-height arguments above.
They neither enumerate all admissible sources nor certify a Lean
proof of any statement.
