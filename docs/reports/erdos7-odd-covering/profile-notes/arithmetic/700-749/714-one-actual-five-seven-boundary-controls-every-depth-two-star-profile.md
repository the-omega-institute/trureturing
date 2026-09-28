# One actual5x7 boundary uniformly supports mass at least1/2 and query cost below3

Within the retained five-leaf ternary interface, every actual star
profile admits a single supported5x7 submeasure with total mass at
least1/2 and normalized query response at most9651/3220<3. All finite
nonternary heights and original phases are retained. The whole family
and the continuation queries have ternary exponent at most2.

This closes a source/query interface for the whole5x7 block, including
the concentrated star profiles that lie outside the two-small-prime
box of [Report711](711-small-prime-star-bounds-certify-depth-two-common-carriers.md).
It does not yet complete the remaining11,13,17,19 gluing or the
nine-prime continuation. The result is ordinary mathematics with exact
rational checks, not new Lean verification.

## 1. Complete the two inventories before taking vertices

Use Q={5,7}, b_q=1/(q-2), C_q=(q-1)/(q-2), p_q=C_q/q. The actual pure-q
survivor laws obey their original cylinder caps C_q/q^e. Retain leaves
0,...,4, root groups R0={0,1},R1={2,3,4}, and fixed weights

\[
 w=(1/4,1/4,1/6,1/6,1/6).
\]

For each q let x_qr be the completed cap sum of its source-live original
3q^e inventory at root r, and y_ql that of its original9q^e inventory at
leaf l. Initially sum_r x_qr<=b_q and sum_l y_ql<=b_q. Separately add
nonnegative unused budget to each inventory until

\[
 \sum_r x_{qr}=b_q,\qquad\sum_\ell y_{q\ell}=b_q.       \tag{PQ1}
\]

These additions are upper-bound budgets, not invented originals or
additional phase claims. Define

\[
 \beta_{q\ell}^*=x_{q,r(\ell)}+y_{q\ell},\qquad
 m_{q\ell}=1-\beta_{q\ell}^*.
\]

The actual star-survivor mass a_ql is at least m_ql, since its union
mass is at most its completed inventory budget. Always m_5l>=1/3 and
m_7l>=3/5, so m_ql>=p_q. For the actual star-survivor submeasure eta_ql,
use uniform thinning

\[
 \xi_{q\ell}=(m_{q\ell}/a_{q\ell})\eta_{q\ell}.         \tag{PQ2}
\]

It stays on the actual legal support, is dominated by lambda_q, and
has exactly the requested mass. Start from

\[
 \eta=\sum_\ell w_\ell\delta_\ell\otimes\xi_{5\ell}\otimes\xi_{7\ell}.
\]

Delete the union of all remaining actual originals whose nonternary
support is{5,7}, including d,3d,9d with every original d=5^e7^f,
e,f>=1. Denote the resulting actual submeasure by nu and its mass by
alpha. The normalized source is mu=nu/alpha. This is ONE source used
for all subsequent queries.

## 2. The supported mass bound needs no Shearer assumption

The star-carrier mass is

\[
 S(m)=\sum_\ell w_\ell m_{5\ell}m_{7\ell}.
\]

For mixed support{5,7}, the d inventory costs at most b5 b7; the3d
inventory at most(max root weight)b5 b7=(1/2)b5 b7; the9d inventory at
most(max leaf weight)b5 b7=(1/4)b5 b7. All exponents are summed, each
original numerical label once in its own inventory. A union bound gives

\[
 \alpha\ge G(m):=S(m)-(7/4)b_5b_7=S(m)-7/60.           \tag{PQ3}
\]

No conditional positivity premise is required: there is just one
mixed nonternary support group. For each q, PQ1 is the product of a
two-root simplex and a five-leaf simplex, with ten vertices. At one
vertex its star multiplicities are

\[
 A_\ell^{r,s}=\mathbf1_{\ell\in R_r}+\mathbf1_{\ell=s}.
\]

S is separately affine in the entire q5 and q7 budget blocks. Its
minimum on their product is therefore attained among the100 pairs of
vertices. Their exact minimum is37/60, so

\[
 G(m)\ge1/2\quad\text{throughout the completed budget domain}. \tag{PQ4}
\]

Unused budgets were handled by PQ1 and PQ2 before this reduction. No
monotonicity claim about the query score is needed, and no unused-budget
vertices have been silently discarded.

## 3. The same-star-carrier query bound has a finite closed form

For each leaf and q, use the unnormalized integer factor law

\[
 u_{q\ell}(1)=m_{q\ell}-p_q=:z_{q\ell},\qquad
 u_{q\ell}(v)=C_q(q-1)/q^v\quad(v\ge2).
\]

Its complete mass is m_ql and first moment m_ql+b_q. Positive-factor
atoms are identical across leaves, while z_ql retains the leafwise
actual-carrier information. A complete finite query layout keeps each
full d,3d,9d label and its original phase. The unit cofactor is included.
As in [Report710](710-shared-support-and-query-carriers-pass-the-fixed-depth-two-profile.md)'s
same-carrier query comparison, put N=V5 V7 and maximize the
ten root/leaf allocation corners pointwise before integrating:

\[
 H(m)=\sum_{E\subseteq\{5,7\}}\int
  \max_{r,s}\sum_\ell a_\ell(E)
       [(1+\mathbf1_{\ell\in R_r}+\mathbf1_{\ell=s})N-2]_+
  \,d\nu_E,
\]

where a_l(E)=w_l product_{q outside E} z_ql. The measures nu_E contain
the full positive-depth factors, of mass product_{q in E} p_q and
first moment product_{q in E}(b_q+p_q). The maximizer can vary with E;
it has not been moved outside the integral.

For a nonnegative five-vector a define

\[
 M(a)=\sum_\ell a_\ell+\max_r\sum_{\ell\in R_r}a_\ell+\max_\ell a_\ell.
\]

At threshold2, N=1 occurs only when E is empty. All other product loads
are at least2 and all hinges are affine. Consequently the full infinite
height comparison is the explicit finite formula

\[
\begin{aligned}
H(m)={}&\max_\ell w_\ell z_{5\ell}z_{7\ell}\
 &+(b_5+p_5)M((w_\ell z_{7\ell})_\ell)
      -2p_5\sum_\ell w_\ell z_{7\ell}\
 &+(b_7+p_7)M((w_\ell z_{5\ell})_\ell)
      -2p_7\sum_\ell w_\ell z_{5\ell}\
 &+\frac74(b_5+p_5)(b_7+p_7)-2p_5p_7.
\end{aligned}                                                       \tag{PQ5}
\]

The original finite layouts are bounded by this full-tail expression.
Restricting eta to nu only decreases nonnegative hinges. Thus every
permitted query layout, under the same normalized source mu, satisfies

\[
 R(\mu)\le1+H(m)/\alpha\le1+H(m)/G(m).                 \tag{PQ6}
\]

## 4. One fixed weight and threshold transport the100-vertex check

Fix one of the entire q budget blocks. PQ5 is a sum of maxima of affine
functions of the other block, plus affine terms; it is convex in that
block. PQ3 is affine in that block. Hence for every fixed k>=0,

\[
 kG(m)-H(m)
\]

is separately concave in the two completed q blocks. A nonnegative
vertex lower bound transports to the whole product of simplices by
successive convex decomposition of the numerical budget parameters.
This is a proof about a function evaluated at the current actual
profile's own target masses. It is not a decomposition or mixture of
incompatible actual source measures.

The exact checker verifies at all100 vertices, with the SAME w and
threshold2,

\[
 2G-H\ge1/700>0,
\]

and the stronger tight inequality

\[
 (9651/3220-1)G-H\ge0.                                 \tag{PQ7}
\]

Separate concavity transports both inequalities, while PQ2 constructs
the actual source for each profile. Therefore

\[
 \alpha\ge1/2,\qquad R(\mu)\le9651/3220<3.             \tag{PQ8}
\]

The largest vertex ratio is attained when q5 puts its two inventories
at the long root and one of its own leaves, and q7 puts them at the
short root and one of its own leaves. At such a vertex G=23/45,
H=6431/6300, and2G-H=1/700. This description is a budget extremizer,
not an assertion that all its maximal phase caps can be jointly attained
by a finite original family.

## 5. What must cross the next boundary

The actual output is the joint submeasure nu on(leaf,x5,x7), including
its actual original-source support and every labelled cylinder
response. It is not only the two scalar bounds in PQ8. For any allowed
nonnegative test f retain

\[
 \Gamma(f)=\int f(\ell,x_5,x_7)\,d\nu.
\]

In particular retain5-only,7-only and joint cylinders, and joint
products when two distinct remaining-prime constraints inspect the
same head. Remaining original labels may use the same head reference
with different11..19 cofactors. Their correlations are not made
independent by the fact that their outside supports are disjoint.

To continue the full proof, one must construct a source/gluing bound
for this same joint response (or a proved sufficient quotient), retain
which complete original labels induce each query, and pay the eventual
23/29 continuation. A total mass lower1/2, or a separate scalar query
upper3, alone is not permission to replace the block by an independent
coordinate or multiply arbitrary head marginal bounds. That missing
joint interface is the remaining obligation.

The [standalone checker](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_pair.py)
and [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_pair.json)
use only exact rational arithmetic and100 inventory vertices. The
query implementation integrates full tails and retains the allocation
maximum inside each exponent support. No original phase scan, exponent
cutoff, optimization package or new Lean theorem is used.

The checker evaluates the full-tail integral and the closed expression
PQ5 independently at each of the100 vertices and requires exact equality.
An independent integer-scaled computation gives the same37/60,1/2,
1/700 and9651/3220 extrema; at every one of the six worst owner pairs,
G=23/45 and H=6431/6300. These finite checks support the arithmetic;
the inventory completion, actual thinning and separate-concavity proof
above carry it to every actual profile. Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_pair.py
```
