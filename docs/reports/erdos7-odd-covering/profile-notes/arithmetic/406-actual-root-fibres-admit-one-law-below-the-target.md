[Index](../../marked_head_profile.md) · [Full and pair tree laws](402-one-common-law-with-a-universal-row-compatible-bound.md) · [Sharp source roots](403-root-structure-of-sharp-minimum-sources.md)

# Actual root-fibre gluing can pass the finite-height target

Call a tail source admissible when it satisfies all six pair-ternary
and the full-fiveary tree conditions. Report 402 constructs on every
such source one probability with, at tail depth `j>=0`,

\[
 M_j\le m_j=\frac25\,5^{-j}+\frac35\,3^{-j},\qquad
 C_j\le c_j=\frac25\left[5^{-j}+(1-5^{-j})3^{-j}\right].
 \tag{CF1}
\]

In particular its row masses are at most `c_0=2/5`. Put

\[
 b_j=m_j+3c_j
 =\frac85\,5^{-j}+\frac95\,3^{-j}-\frac65\,15^{-j}.
 \tag{CF2}
\]

These are ordinary mathematical proofs and exact research checks, not
Lean-certified results. Unrestricted Erdős #7 remains open.

The results below glue these actual probabilities, chosen before any
layout phases. They do not claim that an arbitrary globally admissible
source inherits the required conditions inside its root fibres.

## Two admissible continuing fibres and three private full trees

Suppose five distinct actual root columns contain the following:
two admissible tail sources of height `K-1`, and, in each remaining
column, one row times a complete five-ary tail tree. Require the three
private rows to be distinct. The source may contain arbitrary other
points. These five pieces already give all global admissibility tests:
each row pair gets two good continuing children and at least one good
private child; the full projection gets five full-fiveary children.

Choose the report-402 law independently in each continuing fibre and
give each mass

\[
 a=\frac{11}{40}.
\]

Give each private tree mass `p=3/20`, uniform over its actual leaves.
Since `2a+3p=1`, this defines one supported probability. It works for
unrelated continuing sources and differently labelled private trees.

Its root row, column and cell bounds are

\[
 R_{\max}\le p+2a\frac25=\frac{37}{100},\qquad
 C_{\rm continuing}=a,\quad C_{\rm private}=p,\qquad
 w_{\rm continuing}\le q:=a\frac25=\frac{11}{100},\quad
 w_{\rm private}=p.
 \tag{CF3}
\]

Retain the exact root expression for arbitrary independently chosen
row `r`, pure column `c`, and mixed cell `(s,d)`:

\[
 1+3R_r+3C_c+2w_{r,c}
 +(3+2{\bf1}_{r=s}+2{\bf1}_{c=d})w_{s,d}.
 \tag{CF4}
\]

Classifying the pure and mixed columns as private or continuing gives
the following four upper bounds:

| Pure column | Mixed column | Bound |
| --- | --- | --- |
| private | private | `1+3Rmax+12p=391/100` |
| continuing | private | `1+3Rmax+3a+2q+5p=781/200` |
| continuing | continuing | `1+3Rmax+3a+9q=157/40` |
| private | continuing | `1+3Rmax+5p+5q=341/100` |

Absent columns or mixed cells remove terms and obey the same maximum.
Thus the entire four-label root square is at most `157/40`.

For every further global depth `b=j+1`, `j>=1`, a prefix lies in
exactly one selected root column. A continuing prefix has plain and
joint masses bounded by `a*m_j,a*c_j`. A private prefix has either
mass bounded by `p*5^(-j)`. Both are dominated by the continuing
bounds: `m_j>=5^(-j)`, and

\[
 \frac{c_j}{5^{-j}}
 =\frac25\left[1+(1-5^{-j})(5/3)^j\right]
 \ge\frac{14}{15},\qquad a\frac{14}{15}>p.
 \tag{CF5}
\]

Expand the square using every original divisor `1,5,7,35,...,7^K,5*7^K`.
At maximum seven-adic depth `b`, the ordered-pair counts are `2b+1`
for pure-prefix intersections and `3(2b+1)` for row-prefix
intersections. Incompatible phases give empty intersections. Keeping
the root square whole and bounding the remaining shells under the
same probability proves

\[
 \Gamma_{1,K}(\nu)\le V_K
 :=\frac{157}{40}
 +\frac{11}{40}\sum_{j=1}^{K-1}(2j+3)b_j.
 \tag{CF6}
\]

All summands are positive. The needed geometric sums are

\[
 \sum_{j=1}^{\infty}(2j+3)5^{-j}=\frac{11}{8},\quad
 \sum_{j=1}^{\infty}(2j+3)3^{-j}=3,\quad
 \sum_{j=1}^{\infty}(2j+3)15^{-j}=\frac{37}{98}.
\]

They give

\[
 V_K< V_\infty=\frac{28863}{4900}<6.
\]

Against `T_K=2t_K=6-2(K+2)/3^K`, the first four margins are

\[
 T_1-V_1=\frac3{40},\quad
 T_2-V_2=\frac7{225},\quad
 T_3-V_3=\frac{6979}{135000},\quad
 T_4-V_4=\frac{5273}{67500}.
\]

For every `K>=5`, monotonicity of `T_K` gives

\[
 T_K-V_K>T_5-V_\infty
 =\frac{61891}{1190700}
 =\frac7{225}+\frac{24847}{1190700}.
\]

Therefore this conditional class satisfies, uniformly at all heights,

\[
 \boxed{\Gamma_{1,K}(\nu)\le T_K-\frac7{225}.}
 \tag{CF7}
\]

When both continuing sources have minimum size `5^(K-1)+2`, the
selected source has `2*(5^(K-1)+2)+3*5^(K-1)=5^K+4` points.
This cardinality identifies the construction, not a classification
of all sources with that size.

## Four admissible root fibres

An alternative sufficient condition is four distinct actual root
fibres, each separately admissible. Give each report-402 conditional
law mass `1/4`. Its global row cap is `2/5`, column cap `1/4`, and
cell cap `1/10`. CF4 gives the root bound `77/20`. At deeper global
depth `j+1` the plain and joint caps are at most `m_j/4,c_j/4`.
Consequently

\[
 \Gamma_{1,K}(\nu)\le W_K
 :=\frac{77}{20}+\frac14\sum_{j=1}^{K-1}(2j+3)b_j
 <\frac{1381}{245}.
 \tag{CF8}
\]

The first three target margins are `3/20`, `19/90`, and `3739/13500`.
For `K>=4`,

\[
 T_K-W_K>T_4-\frac{1381}{245}
 =\frac{1423}{6615}=\frac3{20}+\frac{1723}{26460}.
\]

Thus `Gamma<=T_K-3/20` for this class. The whole source may separately
contain a fifth full-projection branch to satisfy global admissibility;
that extra branch need not receive probability. No whole-source
full-fiveary premise is needed for CF8 itself.

## Exact controls and scope

The standard-library program
[conditional_root_fibre_common_law.py](../../frontier/cover-geometry/conditional_root_fibre_common_law.py) constructs
both actual mixtures using the report-402 constructor in each selected
continuing fibre. Its controls use differing original and coloured
recursive fibres, the retained 28-point source, three-row full trees,
and full carriers. It checks all global tree conditions, every actual
prefix cap, and all 1,225 independent root phase choices at heights
one through four. The two-continuing examples have `9,29,129,629`
points. Private witnesses are selected by the existing shared tree API.
Ten malformed or unavailable-fibre controls are rejected.

These calculations verify implementations of the probabilities and
finite expressions. CF3--CF8 prove the all-height statements. The
conditions are sufficient and are not inferred from global tree tests;
the arbitrary-source bound and unrestricted Erdős #7 remain open.
