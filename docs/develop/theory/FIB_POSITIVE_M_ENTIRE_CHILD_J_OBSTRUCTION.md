## 63. Three complete worlds and terminal-J obstruction near a positive M collision

### 1. Literal worlds and the result

A world is a triple $W=(P(r,b),g,d)$, where

$$
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

The actions

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}
$$

act on the left, in the chronological order $J,M,J,M,M,M$.
Writing $Q_0=I$ and $Q_i=X_iQ_{i-1}$, the reading at clock $i$ is
$d+g(i)\operatorname{tr}(Q_iP)$. The acquired readings at clocks
$0,\ldots,6$ are $(0,24,147/5,24,18,p,v)$.
The two alternatives at clock seven use $JQ_6$ and $MQ_6$; call their
readings $a(W)$ and $m(W)$. The entire acquired child $C(p,v)$ includes
all complete worlds with those seven readings.

Define the closed rational rectangle

$$
\begin{gathered}
p_c=7.27697979572462,\qquad v_c=61.48668743716016,\qquad h=10^{-10},\\
\mathcal Q=[p_c-h,p_c+h]\times[v_c-h,v_c+h].
\tag{1.1}
\end{gathered}
$$

**Theorem 1.1.** For every $(p,v)\in\mathcal Q$, the entire $C(p,v)$
consists of exactly three worlds. In increasing order of source width,
their widths lie in

$$
\begin{aligned}
I_1&=(0.04644285937,0.04644285939),\\
I_2&=(0.1199999998,0.1200000002),\\
I_3&=(0.1353256377,0.1353256382).
\end{aligned}
\tag{1.2}
$$

Their respective terminal-J readings satisfy

$$
a(W_1)\in(220.965,220.971),\quad
a(W_2)\in(315.408,315.725),\quad
a(W_3)\in(311.432,311.632).
\tag{1.3}
$$

Consequently $a$ is injective on every entire child over $\mathcal Q$.
Their terminal-M readings satisfy

$$
m(W_1)\in(340.209,340.217),\quad
m(W_2)\in(350.881,351.236),\quad
m(W_3)\in(350.945,351.173).
\tag{1.4}
$$

Any M collision in such a child must therefore use precisely $W_2,W_3$.
The three worlds, including their whole gains and fixed drifts, depend
real analytically on $(p,v)$ in the interior of $\mathcal Q$.

**Theorem 1.2.** There is an exact M-collision point $(p_*,v_*)$ in the
interior of $\mathcal Q$ with one source width $3/25$. Its entire child
has the three worlds of Theorem 1.1, and its only unordered M-colliding
pair is $\{W_2,W_3\}$. It has no J-colliding pair.
There is a real analytic M-collision branch through this point with the
first width allowed to vary. On a sufficiently short open segment,
every entire acquired child of that branch still has exactly three
worlds and an injective terminal-J reading.

The independent J/M quartet sought in the original problem cannot occur
anywhere over $\mathcal Q$. Its existence for some other $p\ne24,v$
remains unresolved. The two required pairs need not coincide or share a
terminal value; the obstruction here excludes every possible J pair.

### 2. Reconstruction without removing gain degeneracies

Put

$$
\begin{gathered}
e=d-24,\quad j=b+r(1-r)/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
Z=T+2j+4r,\qquad R=3U+2n,\\
\Lambda=1+6/T+1/U-4/j-4/n,\\
D_0=\frac{24}{5}(b-1/8)(6/T-2/U).
\tag{2.1}
\end{gathered}
$$

Direct multiplication of the literal matrices gives trace factors

$$
(1,j,T,n,U,U+n,2U+n;Z,R).
\tag{2.2}
$$

In particular the cumulative matrices at clocks six and the two clock-seven
alternatives are

$$
Q_6=\begin{pmatrix}3&1\\5&2\end{pmatrix},\quad
JQ_6=\begin{pmatrix}5&2\\3&1\end{pmatrix},\quad
MQ_6=\begin{pmatrix}5&2\\8&3\end{pmatrix}.
$$

All $j,n,T,U$ are strictly positive. If $\ell_i$ is the Lagrange basis at
$0,1,2,3$, the first four prescribed readings force the entire gain to be

$$
\begin{gathered}
z_0=-24-e,\quad z_1=-e/j,\quad z_2=(27/5-e)/T,\quad z_3=-e/n,\\
g(s)=\sum_{i=0}^3z_i\ell_i(s).
\tag{2.3}
\end{gathered}
$$

Interpolation gives $g(4)=-z_0+4z_1-6z_2+4z_3$ and the exact residual

$$
d+Ug(4)-18=U(e\Lambda+D_0).
\tag{2.4}
$$

Thus the complete five-row parent condition is $e\Lambda+D_0=0$.
On $\Lambda\ne0$, set $e=-D_0/\Lambda$ and use

$$
\begin{aligned}
g_5&=-4z_0+15z_1-20z_2+10z_3,\\
g_6&=-10z_0+36z_1-45z_2+20z_3,\\
g_7&=-20z_0+70z_1-84z_2+35z_3,\\
p&=24+e+(U+n)g_5,\\
v&=24+e+(2U+n)g_6,\\
a&=24+e+Zg_7,\qquad m=24+e+Rg_7.
\end{aligned}
\tag{2.5}
$$

These formulas use one whole polynomial and one fixed drift. They do not
divide by a gain value, leading coefficient, root difference or drift.
The gain cannot vanish identically, since the readings at clocks zero
and one differ. Lower degrees, sampled zeros and repeated roots are
therefore included.

### 3. Polynomial equations for all complete worlds

The following finite polynomials specify the elimination exactly:

$$
\begin{aligned}
\mathcal J&=b^2+r-r^2,&\mathcal N&=\mathcal J+rb,\\
S&=(8b-1)(2+5b),\\
D&=5\{(b^2+8b+4)\mathcal J\mathcal N
       -2(1+b)(1+2b)b(\mathcal J+\mathcal N)\},\\
C_0&=-24D+3S\mathcal J\mathcal N,&C_1&=3S\mathcal Nb,\\
C_2&=3(49b+34)\mathcal J\mathcal N
       -54(1+2b)b(\mathcal J+\mathcal N),&C_3&=3S\mathcal Jb,\\
B_5&=-4C_0+15C_1-20C_2+10C_3,\\
B_6&=-10C_0+36C_1-45C_2+20C_3,\\
L&=bD,\\
N_p&=-bC_0+\{b(1+2b)+\mathcal N\}B_5,\\
N_v&=-bC_0+\{2b(1+2b)+\mathcal N\}B_6,\\
F&=N_p-pL,\qquad G=N_v-vL.
\end{aligned}
\tag{3.1}
$$

The identities

$$
\Lambda=\frac{2D}{5TU\mathcal J\mathcal N},\qquad
D_0=\frac{6S}{5TU}
\tag{3.2}
$$

show that on $D\ne0$ the unique lift is

$$
d=-C_0/D,\qquad g(s)=D^{-1}\sum_{i=0}^3C_i\ell_i(s),\qquad
(p,v)=(N_p,N_v)/L.
\tag{3.3}
$$

The exact polynomial row identities are

$$
\begin{aligned}
-bC_0+\mathcal JC_1&=24bD,\\
-C_0+TC_2&=(147/5)D,\\
-bC_0+\mathcal NC_3&=24bD,\\
-C_0+U(-C_0+4C_1-6C_2+4C_3)&=18D.
\end{aligned}
\tag{3.4}
$$

Both $F,G$ have degree six in $r$, with leading coefficients

$$
\operatorname{lc}_rF=-96(8b-1),\qquad
\operatorname{lc}_rG=-45(59b+6).
\tag{3.5}
$$

Define $\mathcal W(b;p,v)$ by the twelve by twelve Sylvester determinant
$\operatorname{Res}_r(F,G)$, divided exactly by

$$
186624000000\,b^{20}(b+2/5)^4(b-1/8)^4(2b+1)^2.
\tag{3.6}
$$

This is a rational polynomial of degree eighteen in $b$, with 532
nonzero monomials in $(b,p,v)$.

For an explicit first-subresultant convention, form the ten by eleven
coefficient matrix with rows

$$
r^4F,r^3F,r^2F,rF,F,r^4G,r^3G,r^2G,rG,G
$$

and columns indexed by $r^{10},r^9,\ldots,r,1$.
Let $\Delta_1$ retain the first nine columns and the $r$ column;
let $\Delta_0$ retain the first nine columns and the constant column.
Divide $\Delta_1r+\Delta_0$ exactly by

$$
2430b^{13}(2b+1)(5b+2)^3(8b-1)^3
\tag{3.7}
$$

and write the resulting polynomial as $A(b,p,v)r+B(b,p,v)$.
These determinant definitions, including all exact divisions, specify
every coefficient without rounded roots. The polynomials $A,B$ have
336 and 315 nonzero monomials, respectively.

**Lemma 3.1.** Every strict complete world with $p\ne24$ satisfies

$$
\mathcal W(b;p,v)=0,\qquad A(b,p,v)r+B(b,p,v)=0.
\tag{3.8}
$$

**Proof.** On $\Lambda\ne0$, equations (3.2)--(3.4) give $F=G=0$.
If $b=1/8$, the parent equation forces $e=0$, and (2.3)--(2.5) give
$p=24$. Hence for the worlds under consideration all factors removed
in (3.6)--(3.7) are nonzero. The resultant and first subresultant give
(3.8).

For a singular parent, $D_0=0$ forces $b=1/8$. At that width put

$$
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853.
$$

Direct substitution gives $960jn\Lambda=\Phi(r)$, and the rational
Euclidean algorithm gives $\gcd(\Phi,\Phi')=1$.
Also $e\ne0$, since $e=0$ at this width would give $p=24$.
Thus the $r$ derivative of $e\Lambda+D_0$ is nonzero at any such world.
Keeping $e$ fixed, the implicit-function theorem continues it to strict
parents with nearby $b\ne1/8$. There $D_0\ne0$, so their $\Lambda$ is
nonzero. Their whole gains and readings converge to those of the
singular world. The polynomial identities (3.8) pass to the limit.
This retains singular parents without dividing by their zero
$\Lambda$. $\square$

### 4. An exact all-positive-width root certificate

Here is a rational arithmetic prescription for all bounds in this
section. For a rational polynomial $H$ and a rational box with center
$c$ and half-widths $\eta_i$, expand

$$
H(c+u)=\sum_\alpha h_\alpha u^\alpha.
$$

Use the enclosure

$$
H\in[h_0-E,h_0+E],\qquad
E=\sum_{\alpha\ne0}|h_\alpha|\prod_i\eta_i^{\alpha_i}.
\tag{4.1}
$$

All expansions and endpoint operations here are exact rational ones.
In particular cancellation is retained by expanding at the box center
before taking absolute values.

For a finite positive-width cell $(a,z)$ use

$$
T_{a,z}(t)=(1+t)^{18}\mathcal W((a+zt)/(1+t);p,v).
\tag{4.2}
$$

If $\mathcal W=\sum_{i=0}^{18}w_i(p,v)b^i$, its $t^k$ coefficient is

$$
\sum_{i=0}^{18}\ \sum_{\substack{0\le j\le i\\0\le k-j\le18-i}}
 w_i\binom ij a^{i-j}z^j\binom{18-i}{k-j}.
\tag{4.3}
$$

For the final cell $(a,\infty)$ use $\mathcal W(a+t;p,v)$, with
$t^k$ coefficient $\sum_{i=k}^{18}w_i\binom ik a^{i-k}$.
Evaluate each coefficient on $\mathcal Q$ by (4.1).
The following are the seven coarse cells and their coefficient-sign runs,
listed in ascending coefficient order. Every coefficient interval is
strictly separated from zero.

| Index | Coarse width cell | Coefficient signs | Variations |
| --- | --- | --- | --- |
| 1 | $(0.04644,0.04645)$ | $+^6-^{13}$ | 1 |
| 2 | $(0.11999,0.12001)$ | $-^9+^{10}$ | 1 |
| 3 | $(0.13531,0.13534)$ | $+^{10}-^9$ | 1 |
| 4 | $(0.74788,0.74791)$ | $-^7+^{12}$ | 1 |
| 5 | $(0.78820,0.78823)$ | $+^8-^{11}$ | 1 |
| 6 | $(2.88725,2.88728)$ | $-^8+^{11}$ | 1 |
| 7 | $(7.79219,7.79223)$ | $+^9-^{10}$ | 1 |

Here $+^q$ means $q$ consecutive strictly positive coefficients, and
similarly for $-^q$. On the eight complementary cells, starting with
$(0,0.04644)$ and ending with $(7.79223,\infty)$, the signs are,
respectively,

$$
+^{19},-^{19},+^{19},-^{19},+^{19},-^{19},+^{19},-^{19}.
\tag{4.4}
$$

Thus the complete variation list is
$0,1,0,1,0,1,0,1,0,1,0,1,0,1,0$.
Descartes' rule gives exactly one positive root in each coarse cell,
counting multiplicity, and none elsewhere. There is no root at a cell
endpoint. The polynomial has nonzero constant and leading coefficients
throughout $\mathcal Q$.

Endpoint substitution in $\mathcal W$, followed by (4.1) in $(p,v)$,
gives the following narrow cells; the endpoint signs are uniform on
$\mathcal Q$.

| Index | Narrow width cell | Left sign | Right sign |
| --- | --- | --- | --- |
| 1 | $(0.04644285937,0.04644285939)$ | $+$ | $-$ |
| 2 | $(0.1199999998,0.1200000002)$ | $-$ | $+$ |
| 3 | $(0.1353256377,0.1353256382)$ | $+$ | $-$ |
| 4 | $(0.74789116120,0.74789116127)$ | $-$ | $+$ |
| 5 | $(0.78821247876,0.78821247883)$ | $+$ | $-$ |
| 6 | $(2.8872621836,2.8872621839)$ | $-$ | $+$ |
| 7 | $(7.7922094697,7.7922094701)$ | $+$ | $-$ |

Each unique coarse root therefore lies in its corresponding narrow
cell. The final half-line cell accounts for all unbounded positive
widths; no bounded-width hypothesis is being added.

### 5. Source filtering, existence and the three terminal values

Apply (4.1) to $A,B$ on each narrow width cell times $\mathcal Q$,
and divide the resulting intervals to enclose $-B/A$. This gives the
following deliberately widened rational bounds.

| Index | Strict lower bound for $\lvert A\rvert$ | Enclosure of $-B/A$ |
| --- | --- | --- |
| 1 | $4.35029\cdot10^{15}$ | $(0.0484941718,0.0484941724)$ |
| 2 | $1.23788\cdot10^{17}$ | $(0.906190874,0.906190912)$ |
| 3 | $2.66859\cdot10^{17}$ | $(0.894638116,0.894638162)$ |
| 4 | $4.35916\cdot10^{17}$ | $(2.97302,2.97304)$ |
| 5 | $3.63120\cdot10^{18}$ | $(-1.29225,-1.29224)$ |
| 6 | $3.98752\cdot10^{28}$ | $(4.31166,4.31167)$ |
| 7 | $5.18478\cdot10^{34}$ | $(-6.89968,-6.89967)$ |

The last four rows are not strict sources. For the first three rows,
retain the unrounded rational ratio intervals from $-B/A$ and evaluate
(2.1), (2.3), (2.5) by rational interval addition, multiplication and
division. Multiplication uses the minimum and maximum of all four
endpoint products; division is used only when zero is excluded.
The resulting widened bounds are

| Index | $\Lambda$ | $e=d-24$ | $a$ | $m$ |
| --- | --- | --- | --- | --- |
| 1 | $(0.1275887,0.1275889)$ | $(11.53692,11.53694)$ | $(220.965,220.971)$ | $(340.209,340.217)$ |
| 2 | $(0.0290460,0.0290484)$ | $(3.09352,3.09378)$ | $(315.408,315.725)$ | $(350.881,351.236)$ |
| 3 | $(-0.0534120,-0.0534094)$ | $(3.44342,3.44359)$ | $(311.432,311.632)$ | $(350.945,351.173)$ |

The rounded displayed $r$ intervals are for presentation; using them
instead of the unrounded ratio intervals is not part of this arithmetic
prescription. Every denominator is separated from zero on the actual
intervals used.

**Proof of Theorem 1.1.** Lemma 3.1 and the all-width count force every
complete world into one of the seven narrow cells. The nonzero $A$
fixes $r=-B/A$ uniquely at a given width. The last four rows fail
$0<r<1$. In each remaining row, $\Lambda\ne0$ fixes the drift and
(2.3) fixes the whole gain. There is therefore at most one complete
world in each of the first three cells.

For existence, fix any $(p,v)\in\mathcal Q$ and any one of its first
three width roots. It is not $1/8$, so both leading coefficients
(3.5) are nonzero. Since $\mathcal W=0$, the resultant vanishes and
the two degree-six polynomials $F,G$ have a common complex root $z$.
The first subresultant, which is a polynomial combination of $F,G$,
vanishes at $z$. The removed factor (3.7) is nonzero at this width,
and $A\ne0$, so $z=-B/A$. Thus this common root is real and belongs
to the strict source interval in the table. Its $\Lambda$ is nonzero,
so $D\ne0$. Equations $F=G=0$, (3.3) and the original-row identities
(3.4) now lift it to a complete world in the specified child. This
proves existence as well as uniqueness in all three cells.

Each width root is simple, since its coarse cell has exactly one root
counting multiplicity. The implicit-function theorem makes its width
a real analytic function locally in $(p,v)$. Uniqueness in the fixed
disjoint cells glues these functions throughout the interior of
$\mathcal Q$. The nonzero-denominator ratios and interpolation above
then give analytic sources, drifts and whole gains.

The terminal bounds prove (1.3)--(1.4). The three J intervals are
pairwise disjoint, and the first M interval is disjoint from both
others. This proves all assertions of Theorem 1.1. $\square$

### 6. An independently specified exact M point inside the rectangle

Use the regular response functions (2.5), take $t=3/25$, and put

$$
H(t;y)=\bigl(p(r_0,t)-p(r_1,b_1),
v(r_0,t)-v(r_1,b_1),
m(r_0,t)-m(r_1,b_1)\bigr),\qquad y=(r_0,r_1,b_1).
\tag{6.1}
$$

The point used here is the unique zero in the cube
$X=c+[-\rho,\rho]^3$, where $\rho=10^{-30}$ and the exact rational center is

$$
\begin{aligned}
c_0&=0.9061908931198712127547591602154039801733,\\
c_1&=0.8946381389507281496387808544207111135031,\\
c_2&=0.1353256379466845264840666524203806781136.
\end{aligned}
\tag{6.2}
$$

Here is an explicit contraction certificate. Let $K$ be $10^{-30}$ times

$$
\begin{pmatrix}
-4192619585451099080189678406&3221205682319597372244397211&-602386624516677942742570537\\
-874784636257605187200503770307&298559364115390516933604694849&-19854480935902165558779255788\\
1158187998961995693969830487075&-400072618117639213536719475964&27636210512694614982150245476
\end{pmatrix}.
\tag{6.3}
$$

Rational interval evaluation of (2.1), (2.3), (2.5), (6.1) and their first
derivatives gives

$$
\|KH(t;c)\|_\infty<5\cdot10^{-41},\qquad
\|I-K\,\partial_yH(t;X)\|_\infty<2\cdot10^{-20}.
\tag{6.4}
$$

For a complete finite prescription for these particular bounds, use
rational endpoint intervals rounded outward after every arithmetic
operation to the grid $10^{-80}\mathbb Z$. Carry three derivative
coordinates in the order $(r_0,r_1,b_1)$, using the sum and product rules
and

$$
\partial_i(f/g)=\frac{(\partial_i f)g-f(\partial_i g)}{g^2}.
$$

Initialize the coordinate derivatives with the identity matrix. Evaluate
$H$ at the singleton center and its Jacobian on $X$. Multiply by the
exact matrix (6.3). For the matrix norm use the maximum of the three row
sums of interval absolute upper bounds. All trace and regular-parent
denominators in this calculation are separated from zero. This yields,
more tightly, a displacement below $4.833\cdot10^{-41}$ and a matrix norm
below $1.526\cdot10^{-20}$.

The map $y\mapsto y-KH(t;y)$ has derivative norm less than one on $X$,
and its displacement from $c$ is at most
$5\cdot10^{-41}+2\cdot10^{-20}\rho<\rho$.
It maps the closed cube strictly into itself and is a contraction.
The bound on $I-K\partial_yH$ also makes $K\partial_yH$ invertible;
in particular $K$ is invertible. The contraction's unique fixed point
is therefore a zero of $H$, not merely a zero of $KH$.

Interval substitution of $X$ into the first world's responses gives

$$
\begin{aligned}
p_*&\in(7.27697979572462068345,7.27697979572462068347),\\
v_*&\in(61.48668743716016155273,61.48668743716016155275),\\
m_*&\in(351.05857600832559931952,351.05857600832559931954).
\end{aligned}
\tag{6.5}
$$

Both sources are strict and regular. Their width cells are $I_2,I_3$,
so their lifted complete worlds are distinct. Their whole gains and
fixed drifts are exactly (2.3), with $e=-D_0/\Lambda$, and their original
rows follow from (2.2)--(2.5). Equation (6.1) gives equality of their
$p,v,m$. Equation (6.5) places their common acquired values strictly
inside $\mathcal Q$ and away from $p=24$.

The matrix bound in (6.4) makes $\partial_yH$ invertible at the exact
zero. The real analytic implicit-function theorem therefore gives a
local analytic solution $y(t)$ with $t$ free near $3/25$. Strict sources,
regularity and distinct width cells persist. Since the starting
$(p_*,v_*)$ is interior to $\mathcal Q$, continuity restricts this
solution to an open segment whose acquired values remain in $\mathcal Q$.
Theorem 1.1 applies to every entire child on that segment. No specified
finite continuation length follows from this local argument.

This proves Theorem 1.2. $\square$

A nearby rational localization can also be excluded exactly. Define

$$
\begin{aligned}
Y={}&[0.90619089311197,0.90619089311201]\\
&\times[0.8946381389505,0.8946381389510]\\
&\times[0.1353256379463,0.1353256379471].
\end{aligned}
\tag{6.6}
$$

For every $y\in Y$, the first component of $H(3/25;y)$ lies in
$(2.01,2.17)10^{-7}$, so this box contains no M-collision zero.
For this enclosure, evaluate that component at the exact midpoint
$y_c$ of $Y$ and enclose its gradient on $Y$ with the derivative
prescription above. If $\eta_i$ are the three half-widths, the rational
mean-value bound is

$$
H_p(3/25;Y)\subseteq
H_p(3/25;y_c)+[-E,E],\qquad
E=\sum_{i=0}^2\eta_i\sup_Y|\partial_i H_p|.
\tag{6.7}
$$

It gives the tighter interval
$(2.0111143971,2.1673330969)10^{-7}$.
This exclusion does not affect the exact existence proof in the cube $X$.

### 7. Scope and mathematical sources

The new conclusion is the complete three-world source classification
and J-injectivity on $\mathcal Q$, including the third source of width
about $0.04644285938$. The exact M point only locates an M-collision
route within that excluded region. The obstruction does not assume that
the sought J pair would be the M pair: there is no J pair at all in
these entire children.

All positive widths, the original independent pairs and independent
common terminal answers remain in the original problem outside
$\mathcal Q$. Singular parent worlds are handled in Lemma 3.1 before
the all-width certificate excludes them in this rectangle. No reset,
copy, new port, clock shift or fixed-width replacement is used. The
first-width slice in Section 6 specifies one point of the original
full source family and is released in the analytic continuation.

The ordinary algebraic sources are *FIB_ALL_BASE_CANONICAL_ASSEMBLY_CORRECTED*,
Sections 1--2 and 14, for literal-world and singular-parent coordinates;
*FIB_CANONICAL_APPEND_SECTIONS_47_54_CORRECTED*, Sections 48--49, for
the parent polynomial chart and resultant/subresultant organization;
and *FIB_OUTSIDE_U_M_BRANCH*, for the location of a positive M-collision
candidate. The proofs and rational bounds needed here are explicitly
specified in Sections 2--6; no numerical interval or finite continuation
claim from the candidate source is a premise.

Lagrange interpolation, Sylvester determinants and subresultants,
Descartes' rule of signs, the contraction mapping theorem and the real
analytic implicit-function theorem are the classical tools used.
These are ordinary mathematical proofs and rational certificates;
no Lean-kernel verification is asserted.

## 追加锚（本行以下为增补区）

