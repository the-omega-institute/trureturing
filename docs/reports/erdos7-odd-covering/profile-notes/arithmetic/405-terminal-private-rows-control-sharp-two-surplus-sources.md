[Index](../../marked_head_profile.md) · [Minimum-source root structure](403-root-structure-of-sharp-minimum-sources.md) · [Recursive common laws](401-a-recursive-minimum-source-has-one-law-at-every-height.md)

# Terminal private rows control sharp two-surplus sources

A terminal refinement can preserve the sharp source size and all six
pair-tree conditions while supplying an explicit probability for the
full independently phased original-divisor square. Its exact value at
height `K>=2` is

\[
 \boxed{\Gamma_{1,K}(\nu)
   =\frac{105}{32}+\frac{180K+55}{32\cdot5^K}
   \le\frac{19}{5}<2t_K,\qquad
 t_K=3-\frac{K+2}{3^K}.}
 \tag{TR1}
\]

Starting from the 27-point two-surplus-child source in report 403
gives a new explicit family of sharp minimum sources at every height
`K>=3`. The two surplus points remain in different root children.
The construction adds a substantive terminal support condition; it
does not prove a moment bound for arbitrary sources in that root class.
In particular it changes the source, rather than merely changing its
encoding, and gives no inequality comparing the original source's
minimax value with that of its refinement.

These are ordinary mathematical proofs, accompanied by exact controls
using existing source and original-divisor APIs. They are not
Lean-certified and do not resolve unrestricted Erdős #7.

## 1. Exact-law hypothesis and terminal refinement

The moment theorem has a direct support hypothesis. Let `K>=2`, let `T`
be the leaves of any complete five-ary tree of height `K-1`, and for each
`y in T` choose four distinct digits `d_1(y),...,d_4(y)` in `0,...,6`.
The target source may be any finite subset of the four-row carrier
containing every point

\[
 (r,y+7^{K-1}d_r(y)),\qquad y\in T,\quad 1\le r\le4.
\]

Assigning uniform mass to these `4*5^(K-1)` points gives TR1. Additional
source points receive zero mass. No pair-tree premise, fifth terminal
child or exact projection hypothesis is needed for this probability
statement. Sections 2 and 3 prove it directly from the stated support.

The following refinement supplies that support and, under additional
hypotheses, preserves the sharp admissible-source structure.

Let `H>=1`, and let

\[
 R\subseteq\{1,2,3,4\}\times\mathbb Z/7^H
\]

have projection exactly the leaves `T` of a complete five-ary tree of
height `H`. Thus `|T|=5^H`. For every `y in T`, choose five distinct
seven-adic child digits

\[
 d_0(y),d_1(y),d_2(y),d_3(y),d_4(y)\in\{0,\ldots,6\}.
\]

These choices may depend arbitrarily on `y`. Define `R'` at height
`K=H+1` by retaining each old label in the zero-indexed child and
putting one point in each of the four private children:

\[
 \begin{aligned}
 R'={}&\{(r,y+7^H d_0(y)):(r,y)\in R\}\\
     &\cup\{(r,y+7^H d_r(y)):y\in T,\ 1\le r\le4\}.
 \end{aligned}
 \tag{TR2}
\]

The index zero names the child retaining old labels; its actual digit
need not be zero. The projected terminal children are distinct, and
all old leaves receive exactly five children. Consequently the full
projection is again exactly a complete five-ary tree, and

\[
 |R'|=|R|+4\cdot5^H
      =5^{H+1}+(|R|-5^H).
 \tag{TR3}
\]

Thus the surplus above the five-tree leaf count is preserved.

For any row pair `A`, exactly two private children lie in `A`. The
retained child belongs to the pair projection exactly when the old
leaf `y` had a row label in `A`. Hence

\[
 \text{the pair projection below }y\text{ contains a depth-one
 ternary tree}
 \iff R_y\cap A\ne\varnothing.
 \tag{TR4}
\]

Contracting the bottom level proves that the pair projection of `R'`
has a depth-`H+1` ternary tree if and only if the pair projection of
`R` had a depth-`H` ternary tree. This preserves all six pair-tree
capabilities, including any failures; the argument also applies
separately inside each old prefix.

If `R` was admissible with `5^H+2` points, then `R'` is admissible
with `5^(H+1)+2` points. Its minimality follows from report 400.
Each old root column has exactly `5^(H-1)` projection leaves, so its
point surplus is unchanged by TR2. In particular a split of the two
surplus points between two root children remains a split between the
same two children.

The projection hypothesis excludes sharp sources whose two surplus
points introduce extra projection leaves outside every full five-tree.
No reduction of those sources to TR2 is asserted.

## 2. One actual probability and all of its prefix masses

Give each private point in TR2 mass

\[
 \nu(r,y+7^H d_r(y))=\frac{1}{4\cdot5^H},
 \tag{TR5}
\]

and give the retained points mass zero. There are `4*5^H` private
points, so this is one probability supported on the actual `R'`.
Zero probability at some source points is permitted.

For `0<=b<=H`, each selected depth-`b` prefix contains
`5^(H-b)` old leaves. Every one has one private point in each row.
It follows that the actual pure and row-prefix masses are

\[
 \nu(y\equiv u\pmod{7^b})=5^{-b},\qquad
 \nu(r=r_0,\ y\equiv u\pmod{7^b})=\frac14\,5^{-b}
 \tag{TR6}
\]

for each selected prefix and each of the four rows. Unselected
prefixes have zero mass. In particular the global row law is uniform.

At the last depth `K`, every private projected leaf determines its
row, and the pure and joint masses are both

\[
 \frac{1}{4\cdot5^{K-1}}.
 \tag{TR7}
\]

All of these statements concern TR5 simultaneously. There is no
choice of a different measure for different prefixes or phases.

## 3. The exact independently phased square

Choose arbitrary residues independently at every original divisor
of `5*7^K`. Let `P_b` denote the indicator for the `7^b` residue and
`Q_b` the indicator for the `5*7^b` residue, for `0<=b<=K`.
Thus `P_0=1`; a phase selecting row zero has zero source mass and is
still allowed.

For each ordered pair `(a,b)`, with `j=max(a,b)`, the term `P_a P_b`
is either zero or one pure prefix event of depth `j`. Each of the
other three terms `P_a Q_b`, `Q_a P_b`, and `Q_a Q_b` is either zero
or a row-prefix event of depth `j`. There are exactly `2j+1` ordered
pairs with maximum `j`. TR6 and TR7 therefore imply

\[
 \begin{aligned}
 \mathbb E_\nu\left(\sum_{b=0}^K(P_b+Q_b)\right)^2
 &\le\frac74\sum_{j=0}^{K-1}(2j+1)5^{-j}
       +(2K+1)5^{-(K-1)}\\
 &=\frac74 S_K(1/5)+\frac{13}{4}(2K+1)5^{-K},
 \qquad S_K(q)=\sum_{j=0}^K(2j+1)q^j.
 \end{aligned}
 \tag{TR8}
\]

This bound retains all original labels and imposes no compatibility
on their independently selected residues.

It is attained. Choose any one private point `x` of TR5, interpret
it as a residue modulo `5*7^K` by CRT, and choose the residue
`x mod d` separately at every divisor `d`. The resulting pure prefixes
are nested along the supported projection path, and every selected
mixed prefix uses the row of `x`. For `j<K` the intersections have
exactly the masses in TR6; for `j=K` every intersection has the
private-point mass in TR7. Thus every term used in TR8 attains its
bound in this one legitimate layout. The upper bound is the exact
maximum for TR5, not an asserted exact minimax value of `R'`.

Using

\[
 S_K(1/5)=\frac{15}{8}-\frac{4K+7}{8\cdot5^K}
\]

gives the equality in TR1. If `U_K` denotes its right-hand side,

\[
 U_2=\frac{19}{5},\qquad
 U_K-U_{K+1}=\frac{18K+1}{4\cdot5^K}>0.
 \tag{TR9}
\]

Since `2t_K` increases and `2t_2=46/9`, this proves the target for
every `K>=2`, with uniform margin at least

\[
 \frac{46}{9}-\frac{19}{5}=\frac{59}{45}.
 \tag{TR10}
\]

The exact moments decrease to `105/32`. The terminal private-point
law itself does not give the target at height one, which is excluded.

## 4. Sharp sources with two exceptional root children

Use the existing report 399 fixture and the point deletion from report
403:

```python
R_2 = fixture(2) - {(3, 30)}
```

This source is admissible, its projection is exactly a full five-ary
tree, and its root child sizes are `(6,5,6,5,5)`. Define `R_(K+1)`
from `R_K` by TR2, for instance using `d_i(y)=i`.

Induction gives, for every `K>=3`,

\[
 |R_K|=5^K+2,
 \qquad (|R_{K,c}|)_{c=0}^4
 =(5^{K-1}+1,5^{K-1},5^{K-1}+1,5^{K-1},5^{K-1}).
 \tag{TR11}
\]

The pair capabilities in each root child agree with those of the
27-point seed. In particular the two exceptional children retain
their double-good partition sets `{13|24,14|23}` and `{12|34}`.
The one-surplus paths extend through the children retaining the
old duplicated row labels. The source theorem uses those actual
retained labels, while its moment law uses the newly available
private points.

This is outside the previously specified sufficient classes at the
same height:

- No proper row subset contains a full five-ary projection tree:
  at each terminal parent it has at most its own private children
  and the retained child, hence at most four terminal digits.
  Thus reports 396 and 397 do not apply, even to subsources.
- Every root column contains every row after TR2, so the root has
  all twenty cells. It is none of report 398's six exact roots.
  A proper admissible subsource cannot repair this, since the source
  already has the sharp minimum `5^K+2` points.
- For `K>=3`, each actual joint root cell contains all five selected
  second digits: below each old projection leaf is a private point
  in every row. Therefore report 399's at-most-two second-digit
  condition fails. It also fails for every subsource retaining a
  full five-ary projection tree. The original projection has exactly
  `5^K` leaves, so such a subsource must retain every projection leaf,
  including each private leaf's unique row-labelled point.
- The root surplus pattern has two separate `+1` children, unlike
  report 401's single continuing `+2` child, including its V4-coloured
  extension. Sharp minimality again excludes a proper admissible
  subsource of that other pattern.

These are exclusions of the named sufficient hypotheses and their
same-height admissible subsources, not an assertion that no alternative
reslicing or general theorem could apply.

## 5. Constructor, certificate checker and finite controls

The standard-library program
[terminal_private_row_refinement.py](../../frontier/cover-geometry/terminal_private_row_refinement.py)
provides three public operations:

- `make_refinement(base_height, source, terminal_digits=None)` implements
  TR2 for an arbitrary finite base source whose projection is exactly a
  complete five-ary tree. Each leaf may supply its own five distinct
  child digits; index zero retains the old labels and indices one
  through four supply their respective private rows.
- `make_common_law(height, source, tree, private_digits)` implements the
  weaker direct support hypothesis in section 1 on an arbitrary actual
  target source. It returns the positive private-point law, the supplied
  tree and digit data, an actual supported attaining point, and its
  residue at every original divisor.
- `verify_common_law(height, source, certificate)` validates the full
  certificate against the source. It checks exact support and positive
  uniform rational masses, every selected pure and joint prefix mass,
  the resulting complete shell sum, and the attaining layout evaluated
  by the independent original-divisor API. Extra or missing certificate
  fields are rejected. The result is the maximum for this particular
  law, not an optimal value among all supported probabilities.

All literal heights, rows, residues, leaves and child digits reject
boolean and floating-point coercions. Source and tree lists reject
repeated entries. The supplied tree must be exactly a full five-ary
leaf set, and child digits at each leaf must be distinct. The program
uses sibling imports and writes JSON only to stdout. With `--stdin`,
JSON inputs select either the refinement or direct-law operation; its
module documentation gives both schemas.

Running without arguments checks a fixed collection of actual inputs.
It imports the existing report 399 fixture dynamically and uses the
existing original-divisor certificate API. The resulting source and
law measurements are:

| Height | Source points | Positive-mass points | Exact moment |
| ---: | ---: | ---: | ---: |
| 3 | 127 | 100 | 343/100 |
| 4 | 627 | 500 | 83/25 |
| 5 | 3127 | 2500 | 8227/2500 |
| 6 | 15627 | 12500 | 10261/3125 |

A height-two control refines the seven-point type-C root and obtains
exact moment `19/5`. Further controls use a nonconstant per-leaf
terminal digit map, an irregular five-ary tree with prefix-dependent
children and a base source that fails some pair-tree premises. The
latter confirms that the probability theorem does not silently assume
admissibility. Each construction is checked for preservation of all
six pair-tree truth values. The direct-law API is also tested on just
the private support and on a larger source with an unused extra point.
Both JSON operation schemas are exercised. Forty-nine malformed input
and certificate controls reject invalid geometry, omitted private
points, inexact or incorrect masses, altered tree data, false attainers
and malformed original phases. There is no source search or inference
from a height cutoff.

These checks verify concrete constructors, certificates and their
stated interface boundaries. The all-height identity, comparison and
source preservation follow from the preceding proofs, not from those
finite checks. The report and program are ordinary research results,
not Lean-certified declarations.

The unresolved bridge is the existence of a similarly effective
supported law on an arbitrary sharp two-surplus-child source without
the private terminal row support. The root partition sets and their
monotone propagation alone do not imply that additional support.
No claim is made that refinement of a source transfers the new
probability or its moment bound back to the old source.
