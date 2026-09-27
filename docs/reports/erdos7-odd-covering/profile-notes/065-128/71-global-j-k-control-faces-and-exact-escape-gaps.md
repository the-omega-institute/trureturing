# Global J/K control faces and exact escape gaps

The complete profile53 certificate has two different control sets. Its
J target has two four-dimensional zero faces, each a product of a beta
triangle and a late-source triangle. Its K target has two beta triangles.
An improvement confined to the 404 endpoint cannot by itself improve K;
even neighborhoods of every control vertex can leave zero certificate
mass in the interiors of these faces.

This is a statement about the existing certificate, not an assertion that
the true source expression is constant on those faces or that every
relaxed point is attained by an actual family.

The exact arithmetic program is
`../frontier/source-budgets/global_control_faces.py`, with certificate
`../certificates/source_norms/source-budgets/global_control_faces.json`. It reconstructs
all source39 rows, the source53 allocated survival margins, and both signed
mass endpoints at all 1296 source vertices and 18 carriers. Its checks use
exact rational arithmetic, with complete tails supplied by the pinned
source programs. These are ordinary mathematical results and Python
certificates, not Lean declarations.

## Factor coordinates and the complete zero sets

The five source factors have vertex counts

\[
(6,3,6,6,2)
\]

in the order deficit, alpha, beta, late, and z. In each simplex, index zero
means the zero vector and index j>0 means the j-1 coordinate at its cap.
The respective caps are 1/2, 1/4, 1/4, and 1/72. The z indices zero and
one mean 3/4 and 1. The vertex index is the lexicographic product index.
The carrier is a sixth, categorical factor.

The following are all maximal Cartesian zero boxes, where B={3,4,5}.

| Target | Deficit | Alpha | Beta | Late | z | Carrier |
| --- | --- | --- | --- | --- | --- | --- |
| J | {1} | {2} | B | B | {0} | (0,1) |
| J | {2} | {2} | B | B | {0} | (0,0) |
| K | {1} | {2} | B | {1} | {0} | (1,1) |
| K | {2} | {2} | B | {2} | {0} | (1,0) |

Thus J has 18 zero controls and 36 Hamming edges; K has six zero controls
and six Hamming edges. An edge means that exactly one of the six factors
changes. All zero controls use the lower actual-mass endpoint D_c; none
use the upper endpoint s. The source-face dimensions are respectively
(4,4) and (2,2).

The enumeration algorithm starts with every singleton zero box and
exhausts all single-coordinate enlargements whose Cartesian product
remains in the zero set. Every subbox of a zero box is zero, so every
maximal zero box is reached this way. No larger Cartesian box is omitted.

## Exact next signed gaps

For a target T, write its old signed lower bound as

\[
g_{v,c}(X)=a_T X+(T-b)M_{v,c}+C_{v,c},\qquad
a_T=\frac{23}{42}(T-b)-L_T>0.
\]

Here b, L_T, M, and C are the same offset, complete numerator slope,
allocated survival margin, and numerator correction as in profile53.
The program checks this expression at X=D_c and X=s independently for
J and K. Each target has 46,656 endpoint checks.

The smallest positive signed gaps are

\[
\gamma_J=
\frac{66327021453770459472122158798315462843660611821}
{5055546137651716016757241061126601320779200000000}
=0.0131196550575996\ldots,
\]

\[
\gamma_K=
\frac{15240056495574031935365456355486859072608164346131}
{324595372857887445158200347866531571350436000000000}
=0.0469509357493101\ldots.
\]

The minima over both mass endpoints equal the minima over lower endpoints
alone. J's next gap is attained exactly at the six K zero controls. K's
next gap is attained exactly at the 18 J zero controls. The certificate
contains the complete lists and exact table digests.

Let Lambda_v be the product of the five source barycentric weights and
let pi_c be the actual carrier distribution. Iterated Jensen for the
existing separately concave source expressions gives the old lower bound

\[
B_T=\sum_{v,c}\Lambda_v\pi_c g_{v,c}(D_c)
\ge\gamma_T(1-q(Z_T)),\qquad
q(Z_T)=\sum_{(v,c)\in Z_T}\Lambda_v\pi_c.
\]

Concavity belongs to the existing source expressions. No new or patched
vertex table is asserted to be concave. If the product distribution is
supported in one of the listed boxes, B_T=0 throughout that product face.
For example, uniform weights on a K beta triangle give zero old
certificate margin while remaining away from all its vertices.

The two zero sets are disjoint. Consequently the two old lower bounds
also obey the joint certificate inequality

\[
\frac{B_J}{\gamma_J}+\frac{B_K}{\gamma_K}\ge1.
\]

This tradeoff does not alone lower either individual target.

## Concentration near one whole face

Write d_j, a_j, b_j, l_j, and z_j for the five factor barycentric
weights, and put b_B=b_3+b_4+b_5 and l_B=l_3+l_4+l_5. The exact zero-mass
polynomials are

\[
q(Z_J)=a_2z_0b_Bl_B
  \bigl(d_1\pi_{(0,1)}+d_2\pi_{(0,0)}\bigr),
\]

\[
q(Z_K)=a_2z_0b_B
  \bigl(d_1l_1\pi_{(1,1)}+d_2l_2\pi_{(1,0)}\bigr).
\]

If q(Z_T)>=1-delta with 0<=delta<1/2, each common factor outside
parentheses is at least 1-delta. Moreover there is one face for which
each distinguished deficit, carrier, and, for K, late weight is also at
least 1-delta. This does not require beta to concentrate at a vertex.

For the last assertion, write the parenthesized sum as
r=p_1h_1+p_2h_2>=1-delta>1/2, with sum p_i<=1 and sum h_i<=1. Since
r<=max p_i, choose i with p_i>=r. If h_i<=1/2, then

\[
r\le p_ih_i+(1-p_i)(1-h_i)\le\tfrac12,
\]

a contradiction. Hence h_i>1/2, and the same upper bound is at most h_i,
so h_i>=r. For K, h_i is a late weight times its corresponding carrier
weight; each factor is at least h_i. This proves all asserted bounds.

Define a delta-neighborhood of a listed face by precisely those lower
bounds on its supported-factor weights. Outside the union of the two
face neighborhoods, the old certificate therefore has reserve at least
gamma_T delta. No enumeration of clipped simplexes is needed for this
particular zero geometry.

## Actual mass slack remains a separate variable

At the first K face, with beta_2+beta_3+beta_4=1/4, the five source masses
are

\[
n=\left(\tfrac1{36},\tfrac1{12},
\tfrac{1/2-\beta_2}{9},\tfrac{1/2-\beta_3}{9},
\tfrac{1/2-\beta_4}{9}\right).
\]

The two root masses are 1/9 and 5/36; the largest cell mass is 1/12.
Therefore s=1/4 and D_c=D=53/360 on the entire face. At the first J face,
late_2+late_3+late_4=1/72 and

\[
n=\left(\tfrac1{24},\tfrac1{12},
\tfrac{1/2-\beta_2}{9}-\mathrm{late}_2,
\tfrac{1/2-\beta_3}{9}-\mathrm{late}_3,
\tfrac{1/2-\beta_4}{9}-\mathrm{late}_4\right).
\]

Both roots have mass 1/8; the largest cell mass is 1/12. Thus s=1/4 and
D_c=D=3/20. The other faces exchange cells zero and one. These identities
do not assert that an actual family has S=D.

There is an explicit neighborhood estimate for the gap between the
carrier-averaged lower mass S_0=sum pi_c D_c and D. Take a source in one
of the delta-neighborhoods above and project each factor onto the stated
face. Normalize the beta weights on B, and for J also the late weights
on B. For the resulting face point, starred quantities satisfy

\[
\begin{split}
\|\mathrm{deficit}-\mathrm{deficit}^*\|_1&\le\delta,\qquad
\|\alpha-\alpha^*\|_1\le\delta/2,\\
|z-3/4|&\le\delta/4,\qquad
\|\beta-\beta^*\|_1\le\delta/2,\qquad
\|\mathrm{late}-\mathrm{late}^*\|_1\le\delta/36.
\end{split}
\]

The source formula n_j=w_j(z-alpha_root(j)-beta_j)/9-late_j, with all
widths and availabilities at most one, then gives

\[
\|n-n^*\|_1\le
\frac{\delta+5\delta/4+3\delta/2+\delta/2}{9}
+\frac\delta{36}=\frac\delta2.
\]

On K's faces the selected root and cell exceed every competitor by at
least 1/36. For delta<=1/18 they remain maximizing, so the distinguished
carrier still has D_c=D throughout the source neighborhood. For J the
selected cell remains maximizing; its tied root can fall behind by at
most delta/2, giving D_c-D<=delta/10.

Globally each cell mass lies in [0,1/9], hence

\[
0\le D_c-D\le
\frac{\max_r n(r)+\max_j n_j}{5}\le\frac4{45}.
\]

Since the selected carrier has weight at least 1-delta, for
0<=delta<=1/18 this proves

\[
0\le S_0-D\le
\begin{cases}
17\delta/90,&J,\\
4\delta/45,&K.
\end{cases}
\]

Thus actual mass slack epsilon=S-D can be retained correctly. If a local
face theorem requires epsilon<=epsilon_0, failure of that condition
already contributes at least

\[
a_T(\epsilon_0-\xi_T),\qquad
\xi_J=17\delta/90,\quad\xi_K=4\delta/45,
\]

to the old signed comparison, provided epsilon_0>xi_T. The remaining
input for a strict global improvement is a uniform actual-family gain
throughout both relevant face neighborhoods. Neither the zero-face
enumeration nor the mass estimate supplies that gain by itself.
