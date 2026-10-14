# k-bonacci 自校准获取资源续卷 XII：非相邻坐标的共享库存与有符号剩余量

This volume continues [Continuation XI, §§213–215](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XI.md).
The results are ordinary mathematical statements with their stated domains.
Write $x_+=\max(x,0)$ and interpret empty sums as zero.

## 216. Nonadjacent shared stock, exact fibers and signed additive limits

**Definition 216.1 (Full scores and a single certificate budget).**
Fix $L\ge3$. Let $\Omega=\{0,1\}^L\setminus\{1^L\}$,
let $n(w)$ be the first zero, and let $\Omega_j=\{w:n(w)=j\}$.
The notation $w(Z)$ means the length-$L$ word whose zero set is exactly
$Z$. Every word, including every multiple-zero word, remains in the domain.
A full score has independent coefficients $A_w,C_w,P_w,T\ge0$ and reward

$$
g_V(w,\ell)=A_w\mathbf1_{\ell=0}+C_w\mathbf1_{\ell=n(w)}
 +P_w\mathbf1_{\ell\in\{0,n(w)\}},\qquad
g_V(1^L,\ell)=T\mathbf1_{\ell=0}.
$$

Every cell maximizes over every label $0,\ldots,L$, including earlier
and unqueried labels. The complete catalogs contain empty and singleton
schedules and every pair $i<j$. N observes $00,01,10,11$; O observes
$0,10,11$, merging $00,01$ before maximizing. Write $(i,j;u,v,z)$
for a stopped table in this cell order. Reversals permute full cells;
repetitions carry singleton information. These representation facts do
not discount actual repeated or ignored requests. Put

$$
\begin{aligned}
B_{\mathcal C}(V)&=\max_{\text{complete schedules}}
 \sum_{\text{cells }E}\max_{0\le\ell\le L}\sum_{w\in E}g_V(w,\ell),\\
W_V&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_{\mathcal C}(V)&=B_{\mathcal C}(V)-W_V
 \quad(\mathcal C=N,O),\\
Q(V)&=(\beta,K),\qquad \beta_j=\sum_{\Omega_j}(C_w-A_w),\qquad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
$$

The anchor is $R=(1,2;1,2,0)$, so
$0\le\Delta_O\le\Delta_N$. Use the hull $H_L$, its signed support
$\sigma_H$, and the complete matrices of Definition 213.1 and
[199.1–199.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md#199-完整事件锥的有符号替代零成本闭包与剩余原始比较).
Explicitly, with $\alpha=(1,1,0,\ldots,0)$,

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\ b_2=b_3,\\
 &(L+1)e\le\sum_{j\ge3}b_j,\quad
 b_1+\sum_{j\ge3}b_j-(L+1)e\le1\},\\
F_q(b,e)&=\sum_j\beta_j(b_j-\alpha_j)-Ke,
 \qquad\sigma_H(q)=\max_{H_L}F_q.
\end{aligned}
$$

At each zero word the independent demands are
$1-b_n-e,b_n-e,1-e$ for A,C,P; the positive demand is $1-e$.
Negative singleton demands are retained. Set $r=z_R$, $h=d-r$,
$G_N=(z_D-r)_D$, and
$H_N=\{b\in H_L:\exists\lambda\ge0,\ G_N\lambda\ge h(b)\}$.
For a signed target q the existing certificate condition is

$$
V\ge0,\quad 0\le\theta\le1,\qquad
\Delta_N(V)+\theta\le1,\qquad \sigma_H(q-Q(V))\le\theta.
\tag{216.1}
$$

For the same complete feasible $\lambda$ of mass $M$, weak duality gives
$F_q(b)\le M\Delta_N(V)+\theta\le\max(1,M)$.
Every statement of affordability below requires an actual full input
$y$ with $\Delta_O(y)\le1$, or a separately established cost bound
at most one. Exact fiber minima alone supply neither premise.
Nonzero zero-cost cores are allowed at $\theta=1$.

All unspecified score coefficients are zero; coincident contributions
are added. Zero coefficients remove no acquisition constraints. For
class totals one always has

$$
A_j=(-\beta_j)_++z_j,\quad C_j=(\beta_j)_++z_j,\quad z_j\ge0,
\qquad K=\sum_j|\beta_j|+2\sum_jz_j+P_{\rm tot}+T.
\tag{216.2}
$$

This determines the stock convention separately in each theorem.
Full exact-Q minima allow arbitrary A, early and late P, cancellations,
suffix correlations, changed anchors and unaries. Only a displayed
constructor has its specified support. Coefficients are proof weights,
not a probability distribution on sources or an acquisition law.

### 216.1 An attained signed chamber with one aggregate tail slot

**Theorem 216.2 (Shared-stock lower bound and common chamber minimum).**
Let $3\le n<m\le L$, $m\ge n+2$, and prescribe
$\beta_n=g\ge0$, $\beta_m=h\ge0$, arbitrary $\beta_1,\beta_2$,
and $\beta_j\le0$ at every other late coordinate. Assume
$K\ge\sum_j|\beta_j|$. Define

$$
\begin{gathered}
S=K-g-h,\qquad D=(-\beta_1)_++(-\beta_2)_+,\\
I_-=\{1,\ldots,n-1\},\quad I_+=\{n+1,\ldots,m-1\},\quad
I=I_-\cup I_+\cup\{\star\},\quad |I|=m-1,\\
d_i=|\beta_i|\ (i\ne\star),\quad
d_\star=\sum_{j>m}(-\beta_j),\quad
d_-=\sum_{I_-}d_i,\quad d_+=\sum_{I_+}d_i,\quad S_0=d_-+d_++d_\star,\\
J=\max\left\{\frac S{m-1},\max_{i\in I}d_i\right\}.
\end{gathered}
\tag{216.3}
$$

For every full exact-Q competitor,

$$
\Delta_N\ge\Delta_O\ge D+(g+h-S+J)_+.
\tag{216.4}
$$

If in addition

$$
\begin{gathered}
g,h\ge J,\qquad
r_-:=\max(d_-,S-h)\le(n-1)J,\\
r_+:=\max(d_+,S-g)\le(m-n-1)J,\qquad
r_-+r_++d_\star\le S,
\end{gathered}
\tag{216.5}
$$

one full score $V_\star$ has

$$
Q(V_\star)=(\beta,K),\quad W_{V_\star}=S-D,\quad
B_N(V_\star)=B_O(V_\star)=g+h+J,
\qquad \min\Delta_N=\min\Delta_O=D+g+h-S+J.
\tag{216.6}
$$

Both minima are over the unrestricted full exact-Q fiber. Conditions
(216.5) are sufficient for this attained formula, not necessary conditions
for general certificate existence.

**Proof.** For $i<n$, let $\ell_i=i$ if $\beta_i>0$ and zero otherwise.
Use the legal stopped tables

$$
D_i=(i,n;\ell_i,n,m)\ (i<n),\quad
D_i=(n,i;n,0,m)\ (n<i<m),\quad D_\star=(n,m;n,m,0).
$$

Every table collects both correct pivot classes on every suffix. Table
$D_i$ collects its preferred base/correct label on all of $\Omega_i$.
Exactly $D_\star$ outputs zero on all post-m classes and at $1^L$.
These facts hold for all words, without limiting later zeros.

For any competitor use (216.2), put $Z=\sum_jz_j$,
$Z_p=z_n+z_m$, $P_p=P_n+P_m$, and $P=P_{\rm tot}$. Then
$S=S_0+2Z+P+T$ and $W=S-D-Z$.
Mix these detectors by one probability vector $\pi$ on I and set
$u=\min_i\pi_i$. Its expected reward satisfies

$$
R_\pi\ge g+h+Z_p+P_p+\sum_i\pi_i d_i
       +u[(Z-Z_p)+(P-P_p)+T].
$$

The pair reward has been counted once as its own coefficient. Subtract W
and the right side of

$$
R_\pi-W\ge D+g+h-S+\sum_i\pi_i d_i+u(S-S_0).
$$

The remainder is $(1-u)(Z+Z_p+P_p)\ge0$.
Uniform $\pi$ gives $S/(m-1)$; a point mass at a maximal slot gives
$\max_i d_i$. These are alternative unit tests. The head table
$(1,2;\ell_1,\ell_2,0)$ independently gives excess D, proving (216.4).

Choose one allocation $d_i\le x_i\le J$ with total S and
$X_-:=\sum_{I_-}x_i\ge S-h$, $X_+:=\sum_{I_+}x_i\ge S-g$.
It exists because the three group intervals

$$
[r_-,(n-1)J],\quad[r_+,(m-n-1)J],\quad[d_\star,J]
$$

are nonempty, their lower endpoints sum to at most S, and their upper
endpoints sum to $(m-1)J\ge S$. Start at their lower endpoints and
fill remaining capacities in order; within each ordinary group start
at $d_i$ and fill to J in increasing address order. This is a finite
simultaneous construction. It gives
$X_-+x_\star\le g$, $X_++x_\star\le h$ and $\max_i x_i=J$:
either a floor equals J, or every slot must equal the average J.

At $w(\{i,n\})$, $i<n$, put
$A=(-\beta_i)_+$, $C=(\beta_i)_+$, $P=x_i-|\beta_i|$.
At $w(\{i,m\})$, $n<i<m$, put
$A=-\beta_i$, $P=x_i+\beta_i$, $C=0$.
Put C=g at $w(\{n\})$, C=h at $w(\{m\})$, A=$-\beta_j$
at $w(\{j\})$ for $j>m$, and $T=x_\star-d_\star$.
This spends exactly S outside the two pivot atoms and gives the Q and W
in (216.6). In particular post-m negative mass and terminal mass share
the single aggregate slot $\star$.

Each ordinary stock atom has total weight $x_i$ and earns at most
$x_i$ at every label. Aggregate post-m/terminal stock has total
$x_\star$. On a queried pair containing n but not m, the stock in
the n-atom cell is at most $X_-$, in the m-atom cell at most
$X_++x_\star$, and outside both at most J. On a pair containing m
but not n these bounds are $X_-+x_\star,X_+,J$. On pair n,m they
are $X_-,X_+,x_\star$. The allocation inequalities make the first
two cells cost at most g and h, so every such full support is at most
$g+h+J$, maximizing over all labels.

If neither query is a pivot, both pivot atoms lie in cell 11. Outside
it at most two ordinary stock atoms or isolated post-m atoms occur;
their total z is at most $2J$. Inside it the reward is at most
$\max(g,h,S-z)$. Thus the support is at most
$\max(S,\max(g,h)+z)\le g+h+J$, since $S\le g+h$ and
$\min(g,h)\ge J$. Empty and singleton N schedules refine to pairs.
Every $D_i$ attains $g+h+x_i$, including the aggregate table; hence
the maximum is $g+h+J$ also in O. Moreover
$g+h\ge S+x_\star$, so the excess in (216.6) is nonnegative.
All zero masses, $S=0$, exhausted reserves and closed ties are included;
the only division is by $m-1>0$. $\square$

If all nonpivot beta vanish, (216.5) reduces to
$g\ge nS/(m-1)$, $h\ge(m-n)S/(m-1)$, and the cost is
$g+h-(m-2)S/(m-1)$. For $S>0$, $g,h\ge S$, splitting S into
two independently charged one-positive allocations gives cost at least
$g+h-(m-2)S/m$, using the owning one-positive formula 213.18.
The difference is $(m-2)S/[m(m-1)]>0$. This compares that decomposition
only; it is not exclusion from arbitrary signed or joint constructions.

For a signed example take $L=8,n=3,m=6$,
$\beta=(-1,1/2,4,-1/2,-1/4,3,0,-1/2)$ and K=12.
Then $S=5,S_0=11/4,D=J=1$. All five slots are one. The score is

| Zero set | A | C | P |
| --- | --- | --- | --- |
| $\{1,3\}$ | $1$ | $0$ | $0$ |
| $\{2,3\}$ | $0$ | $1/2$ | $1/2$ |
| $\{3\}$ | $0$ | $4$ | $0$ |
| $\{4,6\}$ | $1/2$ | $0$ | $1/2$ |
| $\{5,6\}$ | $1/4$ | $0$ | $3/4$ |
| $\{6\}$ | $0$ | $3$ | $0$ |
| $\{8\}$ | $1/2$ | $0$ | $0$ |

With T=$1/2$, W=4 and both supports eight, dividing every coefficient
by four gives a complete unit score with terminal $1/8$ and largest
late correct total one. This is an exact score, not an amplitude-cap
attainer. The actual unit score of 213.6 at $c=1,t_0=0$ has
$q=(0,0,1,0,0,1;4)$: here $S=2,J=2/5$ and the chamber would require
$g,h\ge6/5$. Its existing certificate shows why chamber failure is
not nonmembership.

For every actual full unit-O input whose quotient satisfies (216.5),
(216.4) forces the attained cost at most one. Its certificate is
$(V_\star,0)$, regardless of the input's carrier or anchor. For another
signed target only the sufficient test
$\Delta_N(V_\star)+\max(0,\sigma_H(q-Q(V_\star)))\le1$ applies.

### 216.2 The complete two-positive zero-cost cone and its sharp face

**Theorem 216.3 (One zero-cost cone at positions 3 and m).**
For every $L\ge m\ge5$, put $r=m-3$. For $g,h,B\ge0$ let q have
$\beta_3=g$, $\beta_m=h$, every other beta zero and K=$g+h+B$.
Over the unrestricted full fiber, zero-O existence and zero-N existence
are both equivalent to

$$
B\ge B_0(g,h):=\max\left\{
3g,\ (2+1/r)g+h,\ 2g+(1+1/r)h,
\ \frac{4g+(r+3)h}{r+1}\right\}.
\tag{216.7}
$$

One score attains zero in both catalogs. On $g\le h\le2rg$ the
formula is $B_0=2g+(1+1/r)h$; this is one common threshold, also used
in §§216.3–216.4, rather than additional zero-cost results.

**Proof.** For any full score define the base-reward measure
$Z_w=A_w+P_w$ and $Z(1^L)=T$. Then
$W=|Z|+\beta_1+\beta_2$. Put
$c=\Delta_O+\beta_1+\beta_2=B_O-|Z|\ge0$.
For a stopped terminal cell E and a label j, the table outputting j on
E and zero elsewhere proves

$$
G_j(E)-Z(E)\le c,\qquad
G_j(E)=\sum_{w\in E\cap\Omega_j}(C_w+P_w).
\tag{216.8}
$$

Let $E_{12}=\{w_1=w_2=1\}$,
$E_{13}=\{w_1=1,w_3=0\}$, $E_{23}=\{w_2=1,w_3=0\}$.
Let $D_j=\{w_3=w_j=1\}$ for $4\le j<m$, and
$D_\infty=\{w_3=1,w_m=0\}$.
Use U for the two label-3 guards $E_{13},E_{23}$ with weight one
each, and D for the r label-m guards $D_j,D_\infty$ with weight
$1/r$ each. Four bundles imply $K\ge a\beta_3+b\beta_m-tc$:

| Bundle | Cells and weights | $(a,b,t)$ |
| --- | --- | --- |
| I | U plus label 3 on $E_{12}$, weight 1 | $(4,1,3)$ |
| II | U+D plus label 3 on $E_{12}$, weight $1/r$ | $(3+1/r,2,3+1/r)$ |
| III | U+D plus label m on $E_{12}$, weight $1/r$ | $(3,2+1/r,3+1/r)$ |
| IV | The cycle below, plus weight $2/(r+1)$ on each U guard | $(1+4/(r+1),2+2/(r+1),(r+7)/(r+1))$ |

The cycle has vertices $\{1,\ldots,m-1,\infty\}$ in cyclic order
$(3,4,1,2,5,\ldots,m-1,\infty)$. Each finite edge $\{i,j\}$
uses label m on $\{w_i=w_j=1\}$, and each edge $\{i,\infty\}$
uses label m on $\{w_i=1,w_m=0\}$, with weight $1/(r+1)$.
These are all legal stopped cells; m may be an unqueried exhaustion label.

Here is the full independent-row verification. Let f(w) be total active
cell weight and $r_j(w)$ the active weight assigned label j. The gain
coefficients on A,C,P are $(-f,r_n,r_n-f)$; on T the coefficient is
$-f(1^L)$. Set $\eta_3=a,\eta_m=b$, all other $\eta_j=0$.
They dominate $a\beta_3+b\beta_m-K$ if

$$
f\le1+\eta_n,\qquad r_n\ge\eta_n-1,\qquad
f-r_n\le1,\qquad f(1^L)\le1.
\tag{216.9}
$$

For I, on classes 3,m the pairs $(r_n,f)$ are $(3,3),(0,1)$.
For II they are $(2+1/r,2+1/r),(1,1+1/r)$; for III they are
$(2,2+1/r),(1+1/r,1+1/r)$. Elsewhere $f\le1$.
For IV, on class 3 the two guards give $r_3=4/(r+1)$ and the
cycle contributes at most one, because vertex 3 is unavailable.
On class m every cycle edge is active, so
$r_m=f=m/(m-2)=(r+3)/(r+1)$.
On any other class with $w_3=1$, the first-zero vertex, or $\infty$
after m and at the positive word, kills two incident edges, giving
$f\le1$. If an early class has $w_3=0$, either both guards vanish,
or one contributes $2/(r+1)$. In the latter case its first-zero vertex
and 3 are nonadjacent and kill four distinct edges, leaving at most
$(m-4)/(m-2)$ cycle weight. Again $f\le1$. This covers arbitrary
later zeros and verifies every A/C/P/T row. Summing (216.8) gives
the four bounds. At zero cost in the prescribed fiber c=0; substituting
K=$g+h+B$ gives (216.7).

For attainment use five actual scores. Entries list nonzero C and P
at their zero sets; all A vanish. In this table $I=\{4,\ldots,m-1\}$.

| Score | $(g,h,B,T)$ | C atoms | P atoms |
| --- | --- | --- | --- |
| $U_0$ | $(0,1,(r+3)/(r+1),1/(r+1))$ | $\{m\}:1$ | $\{i,m\}:1/(r+1)$ for $1\le i<m$ |
| $U_1$ | $(1,2r,2r+4,2)$ | $\{3,m\}:1,\ \{m\}:2r$ | $\{1,3,m\},\{1,m\},\{2,3,m\},\{2,m\}:1$ each; $\{j,m\}:2$ for $j\in I$ |
| $U_2$ | $(1,1,3+1/r,1/r)$ | $\{3\}:1,\ \{m\}:1$ | $\{1,3,m\}:1/r,\ \{1,3\}:1-1/r,\ \{2,3\}:1,\ \{2,m\}:1/r$; $\{j,m\}:1/r$ for $j\in I$ |
| $U_3$ | $(r,r-1,3r,1)$ | $\{3\}:r,\ \{m\}:r-1$ | $\{1,3,m\}:1,\ \{1,3\}:r-1,\ \{2,3\}:r$; $\{j,m\}:1$ for $j\in I$ |
| $U_4$ | $(1,0,3,1)$ | $\{3\}:1$ | $\{1,3\}:1,\ \{2,3\}:1$ |

The endpoints $U_0,U_4$ are the one-positive water-level suppliers of
213.18 with zero early credits, at pivot m and pivot 3 respectively.
For the other three scores, labels supported only by P are dominated
cellwise by zero. Each active C label has one atom and no P of its own.
It suffices to compare its mass with Z in every cylinder containing it.
The complete pair-type table gives these two matching Z masses, for
label 3 then label m; $i,j$ are distinct members of I.

| Pair | $U_1$ | $U_2$ | $U_3$ |
| --- | --- | --- | --- |
| $12$ | $(2r,2r)$ | $(1,1)$ | $(r,r)$ |
| $13$ | $(1,2r+1)$ | $(1,1+1/r)$ | $(r,r)$ |
| $23$ | $(1,2r+1)$ | $(1,1)$ | $(r,r)$ |
| $1j$ | $(2r,2r)$ | $(2,2)$ | $(2r-1,2r-1)$ |
| $2j$ | $(2r,2r)$ | $(2-1/r,2-1/r)$ | $(2r-1,2r-1)$ |
| $3j$ | $(2,2r)$ | $(2,1)$ | $(2r,r-1)$ |
| $ij$ | $(2r,2r)$ | $(3-1/r,3-1/r)$ | $(3r-2,3r-2)$ |
| $1m$ | $(2r,2r)$ | $(1+1/r,1)$ | $(r+1,r-1)$ |
| $2m$ | $(2r,2r)$ | $(1,1)$ | $(r,r)$ |
| $3m$ | $(2,2r)$ | $(2-1/r,1)$ | $(2r-1,r-1)$ |
| $jm$ | $(2r,2r)$ | $(2,1)$ | $(2r,r-1)$ |

Nonexistent types are omitted. All entries dominate their C masses.
Other cells have only base/P/terminal rewards, so zero maximizes every
full N cell. Shorter cylinders contain checked pair cylinders, and
queries after m are constant one on this support. Every label remains
included. Merging cells preserves zero dominance, so both costs are zero.

For $h>0$ the consecutive sectors in $g/h$ have active faces IV, III,
II, I, with boundaries $0,1/(2r),1,r/(r-1),\infty$.
Explicit whole-score combinations on these sectors are respectively

$$
\begin{array}{c|l}
0\le g\le h/(2r)&gU_1+(h-2rg)U_0\\
h/(2r)\le g\le h&\dfrac{h-g}{2r-1}U_1+\dfrac{2rg-h}{2r-1}U_2\\
h\le g\le rh/(r-1)&(rh-(r-1)g)U_2+(g-h)U_3\\
g\ge rh/(r-1)&\dfrac{h}{r-1}U_3+
 \left(g-\dfrac{rh}{r-1}\right)U_4.
\end{array}
\tag{216.10}
$$

All coefficients are nonnegative. Each gives the specified g,h and
stock $B_0$, because its active form is linear on that sector.
For $h=0$ use $gU_4$; for $g=h=0$ use zero. Adding $B-B_0$ to T
preserves zero dominance. This proves all axes and closed sector ties.
The four inequalities also remain signed necessary cuts for arbitrary
full scores with $c=\Delta_O+\beta_1+\beta_2$; they are not a matching
formula for positive-cost fibers. $\square$

**Theorem 216.4 (Forced intermediate pair stock on the least-stock face).**
At B=$3g$ a zero-cost score in Theorem 216.3 exists exactly when
$0\le h\le(r-1)g/r$. Every full zero-O score on this face satisfies

$$
\begin{gathered}
A=0,\quad P(\Omega_3)=0,\quad P(\Omega_1)=P(\Omega_2)=g,\\
\operatorname{supp}(P|_{\Omega_1})\subseteq\{w_2=1,w_3=0\},\quad
\operatorname{supp}(P|_{\Omega_2})\subseteq\{w_3=0\},\\
\sum_{j\ge4}P(\Omega_j)+T=g,\qquad
\sum_{4\le j<m}P\{n(w)=j,w_m=0\}\ge h,\qquad T\le g-h.
\end{gathered}
\tag{216.11}
$$

One common zero-N/O score has total late P exactly h and T=$g-h$.
Thus for $h>0$ neither early-P-only output nor $T\ge g$ is possible
in this zero-cost face, even when all other full-score freedoms are allowed.

**Proof.** In (216.8), the two label-3 guards $E_{13},E_{23}$ and
the label-3 exhaustion guard $E_{12}$ give, respectively,

$$
g\le Z(\Omega_2\cap\{w_3=0\}),\quad
g\le Z(\Omega_1\cap\{w_2=1,w_3=0\}),\quad
g\le\sum_{j\ge4}Z(\Omega_j)+T.
$$

Their supporting stock sets are disjoint. Hence
$3g\le|Z|\le B$, since B=$|Z|+A_{\rm tot}$ in this fiber.
Equality B=$3g$ forces every equality, A=0 and no stock outside those
sets. This gives the first five assertions. Exact Q then leaves C only
in classes 3,m. The stopped 10 cell of $(3,m)$, assigned label m,
cancels its own $P(\Omega_m)$, excludes early stock with $w_3=0$,
and excludes T and post-m stock with $w_m=1$. Its guard yields the
penultimate inequality, and therefore $T\le g-h$.
Face II of (216.7) gives $h\le(r-1)g/r$.
Conversely the final combination in (216.10) has stock $3g$, total
late P=h and T=$g-h$. The all-zero case is included. $\square$

### 216.3 A nonzero-cost family on the same nonadjacent positions

**Theorem 216.5 (A signed whole-score cut).**
For every $L\ge m\ge5$, put $r=m-3$ and $R_r=3+1/r$.
Every unrestricted full score satisfies

$$
-\beta_1-2\beta_2+3\beta_3+(2+1/r)\beta_m-K
 \le R_r\Delta_O\le R_r\Delta_N.
\tag{216.12}
$$

There are no sign assumptions on beta or restrictions on A, late P,
class cancellations, suffixes or terminal mass.

**Proof.** Use this one conic mixture of legal stopped tables:

| Table | Weight |
| --- | --- |
| $(1,2;1,2,m)$ | $1/r$ |
| $(1,3;1,3,0)$ | $1$ |
| $(2,3;0,3,0)$ | $1$ |
| $(3,j;0,0,m)$, each $4\le j<m$ | $1/r$ |
| $(3,m;0,m,0)$ | $1/r$ |

Its total weight is $R_r$. Let $l_0,l_n$ be base and correct counts.
For n=1, $l_1\ge1+1/r$. Either $(2,3)$ outputs zero, or $w_3=0$
and the weight-one bundle beginning at 3 does so; hence $l_0\ge1$.
For n=2, $l_2\ge1/r$ and $l_0\ge2$: table $(2,3)$ gives one,
and either the 3-bundle or $(1,3)$ gives the other.
For n=3 the counts are $(l_0,l_3)=(1,2)$.
For $4\le n<m$, base count is at least $2+1/r$, including table
$(3,n)$, while the correct count is nonnegative.
For n=m the counts are $(2,1+1/r)$; after m the counts are
$(R_r-1,0)$, with positive-word base count $R_r-1$.
Thus the pair count is at least $R_r-1$ on every zero word.

Set $v_1=-1,v_2=-2,v_3=3,v_m=2+1/r$ and other $v_j=0$.
After subtracting $R_r$ copies of the anchor the independent row
coefficients dominate $-v_n-1,v_n-1,-1$ on A,C,P, and $-1$ on T.
Multiplication by the one nonnegative full score and summation proves
(216.12). The tests cover every suffix and every multiple-zero word.
The conic weights are proof weights; no auxiliary affine direction is
asserted to lie in $H_L$ or $H_N$. $\square$

**Theorem 216.6 (An attained full-fiber positive cost).**
For $L\ge m\ge5$, $r=m-3$, assume

$$
s\ge0,\qquad s/r\le a\le2s,\qquad 0\le d\le a/2.
$$

Set $g=s+d$, $h=ra+d$, $B=2s+(r+1)a$, and let q have
$\beta_3=g,\beta_m=h$, other beta zero and K=$g+h+B$.
Then the unrestricted full exact-Q minima for N and O both equal d,
attained by the same score.

**Proof.** Put $t=(a-s+d)_+$ and $p=s+a/2$. Set A=0 and, for
$e=1,2$, place

$$
\begin{gathered}
P_{w(\{e,3,m\})}=a/2,\quad P_{w(\{e,3\})}=s-a/2,\quad
P_{w(\{e,m\})}=a/2,\\
P_{w(\{j,m\})}=a\quad(4\le j<m),\\
C_{w(\{3,m\})}=t,\quad C_{w(\{3\})}=s+d-t,\quad
C_{w(\{m\})}=ra+d,\qquad T=a.
\end{gathered}
\tag{216.13}
$$

All coefficients are nonnegative: $d\le a/2\le s$,
$0\le t\le a$, and $s+d-t=\min(s+d,2s-a)\ge0$.
Also $h\ge s+d$. Summation gives Q=q and W=B. The exact complete-N
cell maxima are as follows; $i,j$ range over gap addresses, and nonexistent
types are omitted.

| Pair | $00,01,10,11$ maxima |
| --- | --- |
| $12$ | $(0,p,p,h)$ |
| $e,3$ | $(s,a/2,s+d,ra+a/2)$ |
| $e,j$ | $(0,p,a,\max(p+(r-1)a,h))$ |
| $e,m$ | $(a,s-a/2,h,p)$ |
| $3,j$ | $(0,2s,a,h)$ |
| $3,m$ | $(a,2s-a,h,a)$ |
| $i,j$ | $(0,a,a,\max(2s+(r-1)a,h))$ |
| $j,m$ | $(a,0,h,2s)$ |

Each early or gap numerical label earns only its own P mass, while
labels 3,m earn their specified C masses; label zero pools P and T.
Thus every label, including earlier unqueried labels, is in the maxima.
For example on $(3,m)$ the base masses a and $2s-a$ cover the two
C3 pieces. On $(e,3)$ the final base $ra+a/2$ covers h since
$d\le a/2$. On $(e,j)$, $p+(r-1)a$ covers every non-m label;
the total is B or $p+a+h\le B+d$ because $a\le2s$.
On $(i,j)$ it is B or $2a+h\le B+d$ by the same inequality.
Every other row sums to $B+d$.

Short schedules refine to active pairs. After m all scored bits are
one and extra labels earn zero, so all other schedules have no larger
support. The stopped head $(1,2;1,2,m)$ attains $2p+h=B+d$.
Hence both costs of (216.13) equal d. For every other full score with
the same Q, the numerator of (216.12) is

$$
2g+(1+1/r)h-B=(3+1/r)d.
$$

It forces both costs at least d, proving the unrestricted minima.
All weak boundaries are included: $s=0$ forces $a=d=0$, and $d=0$,
$a=s/r$, $a=2s$, $d=a/2$, $t=0$ require no limits. $\square$

The d=0 case gives the sector $g\le h\le2rg$ of (216.7) with
$s=g,a=h/r$. Extra terminal stock covers $B>B_0$. It is the same
zero threshold already proved there. When $a>0$, T=a<h, so this
constructor lies below the high-terminal regime.

At $m=5,s=a=1,d=0$ it spends B=5 for $(g,h)=(1,2)$.
Directly adding the one-positive zero-cost stocks of 213.18 spends
$3+10/3=19/3>5$. The fixed-address 3,4 threshold in 214.5 would
spend $\max(3g+h,2g+2h)=6$ at these totals; it cannot be relabeled
to the nonadjacent positions. These are comparisons with those specific
constructions, not exclusion from their entire signed or convex closure.

At $m=5,s=a=2,d=1$, the score has $(g,h,B,K)=(3,5,10,18)$,
W=10, T=2 and both supports eleven. Intermediate P at $\{4,5\}$
has mass two; the C3 masses at $\{3,5\},\{3\}$ are one and two.
Early P conditional on $w_3=0$ has $w_5=0$ fraction $1/2$, whereas
C3 has fraction $1/3$. Thus common-Markov suffix normalization is not
an automatic premise of this example.

For an actual full unit-O input in this quotient family, recover

$$
d=\frac{2\beta_3+(1+1/r)\beta_m-(K-\beta_3-\beta_m)}{3+1/r},
\quad s=\beta_3-d,\quad a=(\beta_m-d)/r,
$$

and check the stated domain. The full cut forces $d\le1$, so (216.13)
gives one certificate with $\theta=0$. Its input need not share A=0,
its baseline, unaries, carrier or terminal. For another signed q the
same score gives only $d+\max(0,\sigma_H(q-Q(V)))\le1$ as a sufficient
test. At d=0 that rule permits a nonzero core with $\theta=1$.

### 216.4 A distinct signed cut, conversion and coordinate-deletion boundary

**Theorem 216.7 (Gap-sensitive signed detector).**
For $L\ge m\ge4$, let $r=m-3$, $I=\{4,\ldots,m-1\}$ and
$S_r=3r+1$. Every full score, with arbitrary signed quotient, satisfies

$$
S_r\Delta_O\ge
-2r(\beta_1+\beta_2)+3r\beta_3+\sum_{j\in I}\beta_j
 +(2r+1)\beta_m-rK,
\qquad \Delta_N\ge\Delta_O.
\tag{216.14}
$$

**Proof.** Give weight one to $(1,2;1,2,m)$, weight r to each of
$(1,3;1,3,0),(2,3;0,3,0)$, weight one to each
$(3,j;0,j,m)$ for $j\in I$, and weight one to $(3,m;0,m,0)$.
The total is $S_r$. The minimum base/correct/pair counts are

| First zero | Base | Correct | Pair |
| --- | --- | --- | --- |
| 1 | r | $r+1$ | $2r+1$ |
| 2 | $2r$ | 1 | $2r+1$ |
| 3 | r | $2r$ | $3r$ |
| $j\in I$ | $2r$ | 1 | $2r+1$ |
| m | $2r$ | $r+1$ | $3r+1$ |
| $j>m$ | $2r+1$ | 0 | $2r+1$ |

The positive base count is $2r+1$. For first zero 1, either $w_3=0$
and the suffix bundle gives zero, or $w_3=1$ and the weight-r $(2,3)$
table does. For first zero 2 the weight-r zero output plus either the
suffix bundle or $(1,3)$ gives $2r$. The remaining cases follow from
their first-zero bits, and each gap class has its own correct table.
Thus the bounds hold for all multiple-zero patterns.

Normalize this single bundle by $S_r$. Its rows dominate the affine
demands with

$$
e=r/S_r,\quad b_1=b_2=(r+1)/S_r,\quad b_3=3r/S_r,
\quad b_j=1/S_r\ (j\in I),\quad b_m=(2r+1)/S_r,
\quad b_j=0\ (j>m).
$$

In particular the negative base demand at 3 and negative correct demands
in the gap are retained. Pair and positive rows hold independently.
Multiply by the full A/C/P/T score and subtract its own W. Expansion
of $S_rF_Q$ is (216.14). This affine test is not asserted to be in H
or to have an original amplitude realization. $\square$

For unsigned beta supported at 3,m this gives
$\Delta_O\ge r(B_0-B)/(3r+1)$ on $g\le h\le2rg$.
Below $B_0$ it is a positive lower bound, not a complete positive-cost
formula. Its signed numerator divided by r minus (216.12)'s numerator
is $-\beta_1+r^{-1}\sum_{j\in I}\beta_j$.
Neither signed cut dominates the other on all quotients. Bundle III
of 216.3 instead uses $-(3+1/r)(\beta_1+\beta_2)$ when expanded;
that is a third signed scope with the same unsigned face.

**Theorem 216.8 (Signed stock conversion attaining early debt).**
Let $L\ge m\ge5$, $r=m-3$, $0\le g\le h\le2rg$.
Prescribe $\beta_3=g,\beta_m=h$ and
$\beta_j=-a_j\le0$ otherwise, with

$$
\begin{gathered}
t=h/r,\quad s=g+t/2,\quad D=a_1+a_2,\quad
B_0=2g+h+t,\\
J=\min(a_1,s)+\min(a_2,s)+\sum_{4\le j<m}\min(a_j,t),\quad
B_{\rm req}=B_0-J,\quad
K=g+h+\sum_{j\notin\{3,m\}}a_j+B.
\end{gathered}
$$

For every $B\ge B_{\rm req}$ the unrestricted full exact-Q minima
in both catalogs equal D, with a common attainer. The stock condition
is sufficient; necessity for arbitrary signed profiles is not asserted.

**Proof.** A convenient zero-cost core has an explicitly available P
mass s in each early class and t in each gap class. Set

$$
\gamma=\frac{2rg-h}{2r-1},\quad
\lambda_0=\frac{h-g}{2r-1},\qquad
\gamma+\lambda_0=g,\quad \gamma+2r\lambda_0=h.
$$

For each $e=1,2$ put P masses

$$
\begin{array}{c|c}
\{e,3,m\}\cup I&\gamma(1-1/r)\\
\{e,3,m\}&\gamma/(2r)+\lambda_0\\
\{e,3\}&\gamma/(2r)\\
\{e,m\}&\gamma/(2r)+\lambda_0
\end{array}
$$

at their actual zero-set words, and P=t at each $\{j,m\}$, $j\in I$.
Put C=$\gamma$ at $\{3,m\}\cup I$, C=$\lambda_0$ at $\{3,m\}$,
C=h at $\{m\}$, and T=t. This is one alternate core on the same
zero face (216.7), retained for its classwise convertible stock.
It is $\gamma E+\lambda_0 H$, where E has $(g,h)=(1,1)$ and
H has $(g,h)=(1,2r)$; H is $U_1$.

The following complete cylinder table verifies cellwise zero dominance
on E; the H column also records its matching masses. Put $u=1/r$,
$e\in\{1,2\}$ and distinct $i,j\in I$. Each pair lists the Z mass
in the C3 cylinder then in the Cm cylinder.

| Pair | E | H |
| --- | --- | --- |
| $12$ | $(1,1)$ | $(2r,2r)$ |
| $e,3$ | $(1,1+u/2)$ | $(1,2r+1)$ |
| $e,i$ | $(1,1+u/2)$ | $(2r,2r)$ |
| $e,m$ | $(2-u,2-u)$ | $(2r,2r)$ |
| $3,i$ | $(2-2u,1)$ | $(2,2r)$ |
| $3,m$ | $(2-u,1)$ | $(2,2r)$ |
| $i,j$ | $(2-2u,1+u)$ | $(2r,2r)$ |
| $i,m$ | $(2-u,1)$ | $(2r,2r)$ |

Since $r\ge2$, these dominate $(1,1)$ and $(1,2r)$, respectively.
All other numerical rewards are P subsets of zero's reward. Coarsening
and constant-one padding cover all other schedules. Zero therefore
maximizes every cell of the combined core. Its total P is $2g+h$,
its terminal is t, and W=$B_0$.

In each nonpivot class convert exactly
$\min(a_j,\text{available class P})$ from P to A on the same words,
for example proportionally within that class. Convert zero if its P
mass is zero. The total converted mass is J. Zero reward stays unchanged
and the nonzero reward only decreases. Add the remaining $a_j$ as A
at $w(\{j\})$, then add $B-B_{\rm req}$ to T.
The final charge is

$$
g+h+B_0+\left(\sum a_j-J\right)+(B-B_0+J)
 =g+h+\sum a_j+B.
$$

Hence Q is exactly the required quotient; each negative coefficient and
each stock coefficient was funded once. Zero still dominates every cell.
For any full score with this Q, constant zero has excess
$-\beta_1-\beta_2=D$, providing an unrestricted lower bound.
The constructed score attains it in N and O. The proof includes
$g=h=0$, zero negative masses, both ratio endpoints and $B=B_{\rm req}$;
there is no division by g. $\square$

At $L=m=5$ the signed example
$\beta=(-1/2,0,1,-3/4,3/2)$, K=$27/4$, B=3 has
$t=3/4,B_0=17/4,J=5/4,D=1/2$. Its common score has W=$15/4$,
both costs $1/2$, and terminal below h. Every actual full unit-O
input in this signed domain has D at most one, so this one exact-Q
score supplies (216.1) with zero residual.

Deleting a zero-net coordinate is a different operation. At
$L=m=5,g=h=1,B=7/2$, the zero core has
$q=(0,0,1,0,1;11/2)$ and both costs zero. Deleting coordinate 4
while keeping the totals gives $q'=(0,0,1,1;11/2)$.
The valid $m=4,r=1$ instance of (216.14) forces
$4\Delta_O\ge1/2$, hence $\Delta_N\ge\Delta_O\ge1/8$ for every
full four-coordinate representative. This falsifies cost-preserving
zero-net-coordinate compression; it is not an original N/O separator.

### 216.5 A signed negative-gap pool funding two positive positions

**Theorem 216.9 (Common-budget exact minima on a capacity domain).**
Let $L\ge m>n\ge3$, $I=\{n+1,\ldots,m-1\}$, $s_i\ge0$,
and S=$\sum_I s_i$. Write $s_{[1]}\ge s_{[2]}$ for the largest
two masses, padded with zeros. Let $g,h,B\ge0$ satisfy

$$
S\ge\frac g{n-2},\qquad
h\le\min\{S-s_{[1]},\ g+S-s_{[1]}-s_{[2]}\}.
\tag{216.15}
$$

Prescribe $\beta_n=g,\beta_m=h,\beta_i=-s_i$ on I and zero elsewhere,
with K=$g+h+S+B$. The unrestricted full exact-Q minima are

$$
\min\Delta_N=\min\Delta_O=d:=\left(g-\frac{n-2}{n-1}B\right)_+,
\tag{216.16}
$$

attained simultaneously. These capacities are hypotheses of this
theorem, not necessary conditions for unrestricted certificate existence.

**Proof.** For any full competitor, (216.2) gives

$$
B=2\sum_j\min(A_j,C_j)+P_{\rm tot}+T,\qquad
R_{<n}:=\sum_{n(w)<n}(A_w+P_w)\le B.
$$

The earlier beta vanish, and W equals the constant-zero reward because
$\beta_1=\beta_2=0$. For each $j<n$ the stopped table
$D_j=(j,n;0,n,0)$ gains exactly g relative to constant zero on class n.
It loses $A_w+P_w$ only at earlier-first-zero words with $w_j=1,w_n=0$.
Every such word has at least one zero among the first $n-1$ bits,
so at most $n-2$ of the $n-1$ tables incur that loss. Later classes
have $w_n=1$ and incur none. Averaging these whole tables proves
$\Delta_O\ge g-(n-2)R_{<n}/(n-1)\ge g-(n-2)B/(n-1)$.
The anchor and N containment give the full lower bound, including all
independent P rows and all suffixes.

For S>0 define $V_0$ by

$$
A_{w(\{i,m\})}=s_i,\quad
C_{w(\{n,i,m\})}=g s_i/S\ (i\in I),\quad
C_{w(\{m\})}=h,
$$

with every other coefficient zero. Its anchor is S. An auxiliary
calculation, valid for S>0 even without (216.15), gives

$$
\Delta_N(V_0)=\Delta_O(V_0)
 =\max\{g,\ g+h-S+s_{[1]},\ h-S+s_{[1]}+s_{[2]}\}.
\tag{216.17}
$$

To verify this calculation put $c_i=gs_i/S$. Query n and output n
on zero, zero on one, to obtain g. The stopped table
$(n,i;n,0,m)$ gives $g+(h-S+s_i)_+$ after optimizing its final
label. Two gap queries with outputs $0,0,m$ give
$h-S+s_i+s_j$; when there is only one gap, query that gap then m,
obtaining h, the same expression with the padded second mass zero.
The full N excess on two gap addresses is

$$
(c_i-s_i)_++(c_j-s_j)_+
 +\max\{0,g-c_i-c_j-(S-s_i-s_j),h-(S-s_i-s_j)\}.
$$

For $g\le S$ it equals $(h-S+s_i+s_j)_+$.
For $g\ge S$ it equals
$\max(g-S,h-S+g(s_i+s_j)/S)$.
If $u=s_i+s_j\le S$, its second term is at most
$g+h-S+s_{[1]}$ when $g u/S\le g+s_{[1]}$, which holds since
$u\le S$. Its first term is at most g. Thus (216.17) bounds it.
Pairs n,i have excess $g+(h-S+s_i)_+$; pairs i,m have excess
$\max(s_i,c_i)+\max(S-s_i,g-c_i,h)-S$.
For $g\le S$ the latter is at most $(h-S+s_i)_+$; for $g\ge S$
it is at most $\max(g-S,g+h-S+s_i)$, again covered.
Pair n,m has excess $g+(h-S)_+$. Queries outside the active
coordinates are constant one; shorter schedules coarsen these pairs.
Only labels 0,n,m earn reward. This proves the full upper bound,
retaining unqueried n in both split gap cells, and proves (216.17).
Under (216.15) all three terms are at most g, so the cost is g.

If S=0 under (216.15), necessarily $g=h=0$; define $V_0=0$.
There is no assertion of (216.17) for S=0,g>0, where its proportional
constructor is undefined.

For g>0 put $r_0=g/(n-2)$ and $B_*=(n-1)r_0$. Define $V_*$ by

$$
\begin{gathered}
P_{w(\{j,n,m\})}=r_0\quad(1\le j<n),\qquad
C_{w(\{n,m\})}=g,\\
A_{w(\{i,m\})}=s_i\quad(i\in I),\qquad
C_{w(\{m\})}=h,\qquad T=0.
\end{gathered}
\tag{216.18}
$$

It has W=$S+B_*$. Prefix labels earn P subsets dominated by zero;
only n,m need additional comparison. Write $E=\{1,\ldots,n-1\}$.
For a pair in $E\times E$ the isolated P masses are $r_0,r_0$;
the remaining base is $S+(n-3)r_0$, at least g and h by (216.15).
For $E\times\{n\}$ the remaining two nonzero base masses are g,S,
covering g,h. For $E\times I$ the relevant base masses are
$r_0,s_i,S-s_i+g$; for $E\times\{m\}$ they are $r_0,S+g$.
For $\{n\}\times I$ they are $B_*,s_i,S-s_i$, and for n,m they
are $B_*,S$. These dominate the corresponding correct rewards because
$B_*\ge g$ and $S-s_i\ge h$.
For two gap coordinates the remaining base is
$S-s_i-s_j+B_*$, at least g and h, since
$h\le g+S-s_{[1]}-s_{[2]}$ and $B_*\ge g$.
For $I\times\{m\}$ the base masses are $s_i,S-s_i+B_*$.
These exhaust all active pairs, and every inactive query coarsens them.
Zero therefore maximizes every full cell and both costs of $V_*$ are zero.
For n>3 its prefix stock deliberately includes late P at $3,\ldots,n-1$.

For $0\le B\le B_*$ take the one whole score
$V=(1-B/B_*)V_0+(B/B_*)V_*$.
Both endpoints contain the same negative masses $s_i$; interpolation
retains them once. Q is the prescribed quotient, W=$S+B$, and support
subadditivity gives cost at most $g-(n-2)B/(n-1)$.
The full lower bound forces equality in both catalogs. For $B>B_*$
add $B-B_*$ to T in $V_*$; every table gains at most the anchor gain,
so the cost stays zero. For g=0 use $V_0$ with T=B; the capacities
and (216.17) give zero cost. All capacities, zero masses and stock
boundaries are closed. $\square$

For $L=m=8,n=4,g=4,h=6$, $s_5=s_6=s_7=4$, B=$9/2$, one
attainer has P=$3/2$ at each $\{j,4,8\}$, $j=1,2,3$;
C=3 at $\{4,8\}$; C=$1/3$ at each $\{4,i,8\}$ and A=4 at
$\{i,8\}$, $i=5,6,7$; C=6 at $\{8\}$; T=0.
Its K=$53/2$, W=$33/2$, and both supports $35/2$ give cost one.
At the inherited hull vertex $u_4$ its quotient has $F_q(u_4)=4/3$.
Thus V=0 with a residual alone cannot fund it. This does not assert
$u_4\in H_N$; the displayed V already is a unit certificate.

There is also a precise independent-budget failure. For $z>0$ and
$z<h\le2z$, take $n=3,m=7,g=z$, $s_4=s_5=s_6=z$, B=$2z$.
The theorem gives a nonzero zero-cost core. Suppose one splits only
this B and these negative coefficients, without cross-cancellations,
into separately charged one-positive-late components of total cost zero.
The n=3 components require total $B_g\ge2z$ by the same detector
lower bound. Thus $B_h=0$. In the h components querying the two largest
of the three negative slots gives total cost at least
$h-S_h+s_{h,[1]}+s_{h,[2]}\ge h-S_h/3\ge h-z>0$,
since $S_h\le3z$. Summing this inequality over components uses the
same total negative stock. This contradicts zero charge in that stated
decomposition class, not arbitrary signed certificates or joint support.

For an actual full unit-O input in (216.15), the unrestricted minimum d
is at most one and the constructed exact-Q score gives (216.1) with
$\theta=0$. No separate allowance is added for either positive pivot.

### 216.6 Signed late surplus and the limits of additive charging

**Theorem 216.10 (A quantitative surplus requirement).**
Let $L\ge3$, $m=L-2$, and let $h\ge0$ be an integer with $m\ge3h$.
Put

$$
c=\frac1{m-2h+1},\qquad a=(h+1)c,\qquad e=hc,
\qquad x_h=(a,\ldots,a;e).
$$

Let $S_h(\beta)$ be the sum of the h largest positive late entries
$\beta_3,\ldots,\beta_L$, using all positive entries if fewer exist,
and put $\tau_h(\beta)=\sum_{j\ge3}\beta_j-S_h(\beta)$.
For every unrestricted full score,

$$
F_{Q(V)}(x_h)\le\Delta_O(V)+c\tau_h(\beta(V))
 \le\Delta_N(V)+c\tau_h(\beta(V)).
\tag{216.19}
$$

For any finite decomposition
$q=\sum_iQ(V_i)+q_{\rm res}$ with full $V_i\ge0$, any signed residual
and $\theta\ge0$ satisfying $\sigma_H(q_{\rm res})\le\theta$,

$$
F_q(x_h)\le\sum_i\Delta_N(V_i)+\theta+c\sum_i\tau_h(\beta(V_i)).
\tag{216.20}
$$

Consequently additive charge at most one requires
$\sum_i\tau_h(\beta(V_i))\ge(F_q(x_h)-1)/c$.
Components all satisfying $\tau_h\le0$ obey $F_q(x_h)\le B$ at total
additive charge at most B, as do limits of those quotient sets at fixed
L,h and uniformly bounded charge B. This applies even when components
are chosen nonlinearly from q and when zero-cost components are nonzero.

**Proof.** The point $x_h$ belongs to the same $H_L$: its order bounds
hold, $b_2=b_3$, and its two capacity expressions are
$(m-3h)c\ge0$ and $(m-2h+1)c=1$.
Choose a set J of positive late coordinates attaining $S_h$, and write
$r_J=|J|\le h$. Reuse the stopped law of 205.3, with the same form
but the present parameters,

$$
\Pi_J=cR+c\sum_{j\in J}\operatorname{Const}_j
       +[1-(r_J+1)c]\operatorname{Const}_0.
\tag{216.21}
$$

It is normalized and nonnegative since $m\ge3h$. The whole table is
chosen before replies; constants use zero requests. Its base/correct/pair
probabilities on every word are

| First-zero class | Base | Correct | Pair |
| --- | --- | --- | --- |
| $n=1,2$ | $1-(r_J+1)c$ | c | $1-r_Jc$ |
| $n\in J$ | $1-r_Jc$ | c | $1-(r_J-1)c$ |
| $n\ge3,\ n\notin J$ | $1-r_Jc$ | 0 | $1-r_Jc$ |

At the positive word the base is $1-r_Jc$; remaining mass is c at
each other label in J. Thus this is one law, not separately specified
event marginals. Let $A_J,P_J$ denote totals in classes J and let
$A_{\rm tot},P_{\rm tot}$ be the complete totals.
Subtract these probabilities from the full demands at $x_h$.
The A/C/P deficits divided by c are

$$
(r_J-2h,0,r_J-h)\quad(n\le2),\qquad
(r_J-2h-1,0,r_J-h-1)\quad(n\in J),
$$

and $(r_J-2h-1,1,r_J-h)$ at omitted late classes; the terminal
deficit is $r_J-h$. Hence the exact identity is

$$
V\cdot(d(x_h)-z_{\Pi_J})
=c\left[\tau_h(\beta)-(2h-r_J)A_{\rm tot}-A_J
 -(h-r_J)(P_{\rm tot}+T)-P_J\right].
\tag{216.22}
$$

All terms after $\tau_h$ are nonpositive. This accounts for arbitrary
cross-word A/C cancellations and every late P row. Since
$V\cdot z_{\Pi_J}\le B_O(V)$, subtracting W proves (216.19).
Evaluate every component and the one residual at the same $x_h\in H_L$
to get (216.20). Continuity of the linear functional $F_q(x_h)$ proves
the bounded-charge closure assertion. The formulas include h=0 and
$m=3h$. For a single certificate (216.1) the same surplus requirement
holds even at $\theta=1,\Delta_N(V)=0$. $\square$

The domain $\tau_h\le0$ contains both scores with at most h positive
late beta entries and the narrower correct-class-support domain of 205.3.
It can also contain more than h positive beta entries when negative
late entries compensate the omitted positive sum. For example, at h=1
late beta $(2,1,-1,0,\ldots)$ has $\tau_1=0$.
To see the distinction from C support on actual words, at L=8 place
A=C=1 in each class 3 through 7 on two different suffix words, and C=1
in class 8; add any late P, for example mass two in class 4.
Then six C-class totals are positive while only $\beta_8=1$ is positive
and $\tau_1=0$. Pointwise A domination of C was not assumed.

The obstruction has actual complete unit inputs. Fix $\mu\ge2$ and
$0\le\gamma_j\le\mu$, $j=3,\ldots,L$, with maximum $\mu$.
Use the fair-suffix score of 205.4 with each late C total reduced to
$\gamma_j$:

$$
C_{1^{j-1}0v}=\frac{\gamma_j}{2^{L-j}},\qquad
P_{01v}=P_{10v}=\frac{2(\mu-1)}{2^{L-2}},\qquad
T=\mu-1,\qquad A=0.
\tag{216.23}
$$

Here v ranges over the whole indicated suffix cube. Let G=$\sum\gamma_j$.
The supplier gives the complete N support upper bound W+1, with
W=$5(\mu-1)$. Decreasing C totals leaves W fixed and cannot increase
any table reward. A stopped head $(1,2;1,2,j_*)$ at a maximal total
still attains $4(\mu-1)+\mu=W+1$. Thus both costs are exactly one,
K=$G+5(\mu-1)$, and the early beta vanish. The supplier is used for
$L\ge4$; at L=3 the head has maxima
$(0,2(\mu-1),2(\mu-1),\mu)$, and each early/3 pair has maxima
$(\mu-1,\mu-1,\mu,2(\mu-1))$, giving the same result directly.

Substitution into the new surplus inequality gives

$$
F_{Q(Y)}(x_h)=\frac{G-5h(\mu-1)}{m-2h+1}.
\tag{216.24}
$$

Every additive certificate using only $\tau_h\le0$ components costs
at least this amount. For fixed $\gamma_j=\mu\eta_j$ with
$0\le\eta_j\le1$, $\max\eta_j=1$ and $\sum\eta_j>5h$, it tends
to infinity with $\mu$. The last condition requires enough late
coordinates and is not asserted at every fixed L,h. Unequal profiles
and inactive addresses are allowed.

At $L=10,h=1,\mu=10$ take late totals
$(10,9,0,10,8,9,10,0)$. Then W=45, K=101, both costs are one,
$x_1=(2/7,\ldots,2/7;1/7)$ and $F_Q(x_1)=11/7$.
Any unit additive charge therefore requires $\sum_i\tau_1\ge4$;
restricting all components to nonpositive surplus costs at least $11/7$.
For the equal profile at $L=8,h=1,\mu=3$, the same formula gives
$G=18,W=10,K=28$ and $F_Q(x_1)=8/5$, again with both costs one.
This is a failure of additive component charging, not of evaluating
one joint score: every such input already has the certificate $(Y,0)$.
For every actual $b\in H_N$ and the same full feasible $\lambda$,
$F_{Q(Y)}(b)\le M\Delta_N(Y)=M$. Thus this family cannot supply
the required strict separator; no full feasible $\lambda$ is asserted
at the auxiliary point $x_h$.

### 216.7 Original sources, normalized companion laws and closed caps

**Definition 216.11 (The unchanged source and resource domain).**
The original labeled source and its static answers are

$$
X=\{(r,z):r\text{ prime},\ z\in\mathbb Z,
 \lceil F_r/10\rceil\le z\le\lfloor F_r/5\rfloor\},\qquad
N(r,z)=1+F_rz,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},
$$

where $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$ and $p_i$ are the
increasing primes. This is a countable labeled set, not a prior over
sources. Every N has finite prime support, so its first zero n(x) exists.
[Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows)
supplies every finite Boolean pattern on arbitrary finite addresses in
every sufficiently large prime-index window, with a threshold independent
of the pattern. The all-word arguments therefore include actual witnesses
for every multiple-zero word. A positive finite word describes a tail
source, not an infinite all-positive source.

The full carrier is the disjoint-union Borel space
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, each block
a copy of $(0,1)$. The fixed consumer returns unknown on B blocks and
proposes j on $P_j$. The original nonatomic targets remain exactly
those in Definition 213.22: for its fixed $h_0\in(0,1)$,
$t(x)=\sum_i3^{-i}q_i(x)$, $\nu_x$ has density proportional to
$e^{t(x)u}$ on $B_{n(x)}$, $\pi_j$ is uniform on $P_j$, and
$\mu_x=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$, with $\Omega(x)$ the number
of distinct prime divisors. The marks $\theta_j=(B_1,1/(j+2))$,
$j\ge0$, instead define the separately selected laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                 +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_j\longrightarrow0.
\tag{216.25}
$$

They do not replace $\mu_x$. In particular any law supported on finitely
many marks has TV distance one from every original nonatomic target:
that finite Borel set has mass one under the former and zero under the
latter. The companion laws below concern (216.25).

The resource is the hard bound of two actual requests of 90.1, including
repetitions and requests whose answers are ignored. Advice is zero.
There is one source-independent seed, actual sourcewise almost-sure
finite handoff, and error is uniform over every source and every Borel
event. Neither source labels nor N nor n are extra observations.
Arbitrary addresses and full-carrier outputs remain legal for competitors.
No address bound, runtime, mean count or source-average error is substituted.
N preselects a schedule and acquires its replies; O preselects an increasing
schedule and stops at its first queried zero or exhaustion. Output labels
may be earlier, later or unqueried.

For a finite normalized mixture, partition one $U\sim\mathrm{Uniform}[0,1)$
into its table masses and select the entire table before any answer.
The O execution and its N completion use the same U and the same
preselected addresses. The completion of 90.2 acquires the second reply
even after a first zero, then ignores it and preserves the stopped output.
These particular rules hand off finitely on every source and seed.
The score coefficients and stock allocations of §§216.1–216.6 are proof
weights, not acquisition probabilities or additional randomness.

The owning finite-to-original theorem is
[110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source).
Its necessity includes arbitrary-address full-carrier competitors:
countability supplies a common probability-one finite-handoff event,
the maximum-address seed tails vanish, finite-pattern witnesses transport
whole executions, and finite-catalog compactness preserves the closed cap.
Its sufficiency applies to one normalized configuration satisfying every
independent base, correct, pair and positive row. At $0<\varepsilon\le1$
the strict active horizon is
$L_a=\max(\{i:a_i>\varepsilon\}\cup\{0\})$.
For a finite law with output labels through H, every actual n>H has

$$
\operatorname{TV}\left(\sum_{j=0}^Hp_{1^H}(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-p_{1^H}(0),a_n\}.
\tag{216.26}
$$

In particular equality $a_n=\varepsilon$ is retained. This is the
existing transport and tail identity, not a new theorem about arbitrary
garblings. The separate criterion 109.1 concerns an actual normalized
probability-vector kernel on every word,

$$
p_w=c+\sum_i l_iw_i+\sum_{i<j}Q^{\rm ker}_{ij}w_iw_j,
\qquad
H^{\rm ker}=\sum_i\left(\sum_{j>i}(-Q^{\rm ker}_{ij})_+-l_i\right)_+.
$$

Its stopped condition is $c\ge H^{\rm ker}$ coordinatewise, with the
schedule-mass bound supplied by normalization. It is not a condition
on Q(V). Exact-law failure in 112.2 has an alternative O cap attainer
and remains an exact-law obstruction, not a cap separator.

**Proposition 216.12 (Companion laws of the shared-stock detectors).**
The following are actual common-seed laws on (216.25), with the stated
uniform errors. They illustrate the mathematical constructions; they
do not assert new optimal-cap classifications.

For Theorem 216.2 use any probability vector $\pi$ on its full slot set,
including $\star$, and select the displayed $D_i$. On every tail n>L
the output is $\pi_\star\delta_{\theta_0}+(1-\pi_\star)\delta_{\theta_m}$.
Its exact error is $\max(1-\pi_\star,a_n)$ by (216.26). The detector
lower bound does not claim that an arbitrary prescribed cap is met.

For Theorem 216.5 let $S_r=3r+1$, normalize its conic mixture by
$R_r=S_r/r$, and take

$$
\varepsilon=r/S_r,\quad a_1=a_2=a_3=(r+1)/S_r,\quad
a_4=\cdots=a_m=1/S_r,\quad a_{m+j}=1/(S_r2^j)\quad(j\ge1).
\tag{216.27}
$$

The counts in its proof imply all three TV rows on every word:
$p_0\ge1-a_n-\varepsilon$, $p_n\ge a_n-\varepsilon$ and
$p_0+p_n\ge1-\varepsilon$. At n=3 the counts are exactly
$(p_0,p_3)=(r/S_r,2r/S_r)$, giving error $\varepsilon$.
At $1^m$ the base is $(2r+1)/S_r$ and remaining mass $r/S_r$ is
at m. Every actual tail therefore has error $\varepsilon$.
The strict active length here is three.

For the distinct signed detector of 216.7, divide all its weights by
$S_r$, retain $\varepsilon=r/S_r$, and take

$$
a_1=\cdots=a_m=(r+1)/S_r,\qquad
a_{m+j}=\varepsilon 2^{1-j}\quad(j\ge1).
\tag{216.28}
$$

Its count table gives $p_0\ge r/S_r$, $p_n\ge1/S_r$ and
$p_0+p_n\ge(2r+1)/S_r$ on every zero word. These are exactly
the three required lower bounds. The positive-word law is again
$((2r+1)/S_r)\delta_{\theta_0}+(r/S_r)\delta_{\theta_m}$;
all actual tail errors equal $\varepsilon$, including
$a_{m+1}=\varepsilon$. This includes the detector's m=4 endpoint.

For Theorem 216.9 choose j<n uniformly and use $D_j=(j,n;0,n,0)$.
On every word

$$
p_n(w)=\frac{1-w_n}{n-1}\sum_{j<n}w_j,\qquad p_0=1-p_n.
$$

Put $\kappa=(n-2)/(n-1)$, $a_i=\kappa$ for i≤n, and
$a_{n+j}=\kappa2^{1-j}$. At an actual first zero $\ell<n$,
$p_n\le\kappa$, so the exact error is
$\max(p_n,a_\ell)=\kappa$; this keeps the pair-event condition.
At $\ell=n$ it is $1-\kappa\le\kappa$.
At every $\ell>n$ the output is base only, with error
$a_\ell\le\kappa$, including the first tail equality.

For the zero face 216.4 reuse the single four-table law (213.30),
with probability $1/4$ on each of

$$
(1,2;1,2,0),\quad(1,2;1,2,3),\quad
(1,3;1,3,0),\quad(2,3;2,3,0).
$$

Its same-seed N completions give one full mass-one $\lambda$ at
$v_3=(1,1,1,1/4,\ldots,1/4;1/4)\in H_N$.
Use $a_1=a_2=a_3=1$, $a_4=\cdots=a_L=1/4$ and
$a_{L+j}=2^{1-j}/4$. The existing all-word probabilities give the
cap $1/4$ and exact tail error $1/4$, including equality.
For B=3g and every admissible h,
$F_q(v_3)=(3g-B)/4=0$. This uses the very same feasible $\lambda$
for the whole score, not a new mass allowance for each generator.

Finally, $\Pi_J$ of 216.10 is an actual law but generally not a full
cap attainer at its auxiliary point. Every actual n>L has exact error
$\max(r_Jc,a_n)$. An omitted late class with target amplitude
$(h+1)c$ has correct probability zero and error $(h+1)c>hc$.
That missing row is measured by (216.22), not dropped. At h=0 the
auxiliary e=0 is not a positive closed cap for a positive tail.
All of these claims follow from the displayed all-word count formulas,
one normalized mixture, and (216.26). $\square$

**Corollary 216.13 (Necessary original amplitude inequalities).**
For an original hard-two N or O rule feasible at a positive cap
$\varepsilon$, Theorem 216.6 gives, when its strict active horizon
$L_a\ge m$,

$$
g a_3+h a_m\le d+(g+h+B)\varepsilon.
\tag{216.29}
$$

Under Theorem 216.9's capacity hypotheses, at any active horizon,

$$
g a_n+h a_m-\sum_{n<i<m}s_i a_i
 \le d+(g+h+S+B)\varepsilon.
\tag{216.30}
$$

**Proof.** Apply 110.2 to obtain one normalized finite configuration
at the same cap, and pair all its rows with the displayed full score.
Its demand minus W is exactly the left side minus K$\varepsilon$,
and its reward minus W is at most the score's complete support cost d.
For (216.29), pad the constructor to $L_a$ by constant-one suffixes.
For (216.30), if $L_a<m$ use the existing 215.7 extension: keep the
configuration's outputs and extend to a horizon at least m.
On new first-zero classes $a_i\le\varepsilon$, correct probability
is zero and base probability is at least $1-\varepsilon$.
Consequently base, correct, pair and positive rows all remain valid,
including their negative singleton demands; (216.26) keeps the actual
tail. If $L_a\ge m$, pad the score instead. This proves the necessary
relations without an optimality or sufficiency assertion. $\square$

### 216.8 Source correspondence and limits of comparison principles

The full signed quotient, hull and single residual certificate are the
objects of 199.1–199.4 and 213.1. The exact one-positive formula used
for the endpoints and the separately funded comparison is 213.18,
with its signed extension in 214.2. The head obstruction at 213.6,
the feasible four-table law 213.30, the restricted law 205.3 and the
complete unit-score supplier 205.4 retain their own hypotheses.
Equations (216.23)–(216.24) use that unit supplier and a new signed
surplus test; they do not count its existing construction a second time.
The positive-cost constructor, alternate convertible core and sector
generators share the one unsigned zero threshold (216.7). Their distinct
uses are positive-cost attainment, signed conversion and the other
sectors or sharp face, respectively.

The following literature comparisons concern relations and hypotheses;
none substitutes for the ordinary proofs or for 110.2's resource transport.
In the experiment correspondence, a Boolean word is a state, a transcript
cell an observation and a label an action. A common postprocessor must
reproduce all state laws with one normalized kernel. In Xia's §3.4
notation, the joint action sets are

$$
S_k(E)=\{E\Pi:\Pi\ge0,\ \Pi\mathbf1\le\mathbf1\},
\qquad \Pi\in\mathbb R^{M\times k},
$$

with the leftover row mass assigned to one further action. The scalar
set $S_1(E)$ cannot replace all these joint sets in a general multi-action
decision comparison. Here the common output law must additionally obey
the stopped schedule and hard request count. No source prior or scalar
cost factorization supplies these extra requirements.

| Source and precise correspondence | Limit of the correspondence |
| --- | --- |
| Blackwell, [Comparison of Experiments](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf), §§2–5: comparison of attainable risk sets and randomization/sufficiency. One common decision rule, rather than separate eventwise optimizers, is the relevant object. | Abstract comparison does not supply a preselected stopped acquisition with two actual requests. |
| Chen, [Experiments in the Linear Convex Order, v1](https://arxiv.org/pdf/2502.06530v1), §4.2 Theorems 1 and 3, §4.3 Definition 7 and Corollary 3: binary-action comparison and binary-decomposable value functions; the strategy conclusion in Corollary 3 has finite action space. | Whole-reward binary decomposability and resource-preserving realization have not been established here. Applying a binary theorem separately to A,C,P cannot produce their common full-score budget. |
| Bertschinger and Rauh, [The Blackwell Relation Defines No Lattice, v1](https://arxiv.org/pdf/1401.3146v1), Lemma 10 and Example 18: binary/zonotope comparisons can hold without one normalized joint channel. | The example's unique nonnegative coefficient matrix has row sums $(2,2,2,0)$, so is not stochastic. This diagnoses normalization, not a separator in the present original source model. |
| Zaev, [On the Monge–Kantorovich Problem with Additional Linear Constraints, v1](https://arxiv.org/pdf/1404.4962v1), §1 and duality theorem: all prescribed marginals and linear constraints belong to one joint measure. | Marginally feasible or separately optimized plans cannot be combined without joint feasibility. No transport-plan identification with the complete stopped catalog is assumed. |
| Šámal, [Cubical Coloring—Fractional Covering by Cuts and Semidefinite Programming, v3](https://arxiv.org/pdf/0911.2589v3), fractional cut covers and their linear programs: one set of nonnegative weights covers all constraints. | The cycle in 216.3 uses explicitly verified stopped cells. A graph cut cover alone does not identify those cells, labels or their costs. |
| Kaniewski, Lee and de Wolf, [Query Complexity in Expectation, v1](https://arxiv.org/pdf/1411.7280v1), Definition 8 and Theorem 9: nonnegative literal degree characterizes a scalar nonnegative output's expectation. | The reverse construction rescales scalar leaf outputs by total coefficient mass. It does not establish one normalized output-probability vector, stopped first-zero legality or all-Borel TV error. |
| Gupta, Nagarajan and Singla, [Adaptivity Gaps for Stochastic Probing: Submodular and XOS Functions, v1](https://arxiv.org/pdf/1608.00673v1), model and Theorem 1.1: independent activations with known probabilities and expected monotone-submodular value under prefix-closed constraints give factor three. | The present source bits are deterministic conditional on each source, the comparison is uniform TV and the resource is an exact hard count. Neither the stochastic prior nor the objective correspondence is available. |
| Xia, [Comparisons of Experiments in Moral Hazard Problems, v7](https://arxiv.org/pdf/2507.12476v7), Theorem 2: conic-span inclusion is equivalent to a nonnegative matrix factor and risk-neutral limited-liability cost comparisons. | A nonnegative factor need not be stochastic or satisfy the joint normalized output simplex and all acquisition constraints. Scalar conic inclusion does not establish the full shared-budget set. |
| Fritz, Gonda, Perrone and Rischel, [Representable Markov Categories and Comparison of Statistical Experiments in Categorical Probability, v3](https://arxiv.org/pdf/2010.07416v3), Theorem 5.6 and Corollary 5.15: standard-Borel kernels with finite parameter space in 5.6, and discrete parameter objects in 5.15, admit common postprocessing characterizations. | A kernel factorization does not construct a two-request stopped query algorithm. The countable-source, uniform-error and exact-resource transport still requires 110.2. |
| Wang et al., [Inferentially-Private Private Information, v2](https://arxiv.org/pdf/2410.17095v2), model and binary-secret result: a binary released state, fixed joint prior on state and secret, and inferential-privacy constraints govern Blackwell-optimal disclosure. | Neither this fixed-prior privacy model nor its optimality is the all-source original hard-two cap model. |
| Huber and Marić, [Bernoulli Correlations and Cut Polytopes, v2](https://arxiv.org/pdf/1706.06182v2), Theorem 1 and agreement probabilities in §2: attainable symmetric Bernoulli correlations require one joint cube law. | Pairwise admissibility or a positive-semidefinite correlation matrix does not suffice. For three symmetric bits, correlations all $-2/5$ would give three agreement probabilities $3/10$; their sum $9/10<1$ contradicts the fact that every binary triple has an agreeing pair. This is a joint-realization analogy, not a hard-two separator. |
| van Rooyen, [On Experiments, v2](https://arxiv.org/pdf/2508.08288v2), §3.1, Definition 25 and Theorem 26: finite basic sets, common postprocessing and prior-averaged directed deficiency. | A fixed-prior average is not the required uniform all-source bound; the postprocessor also needs an actual resource implementation. |

These specified sources explain common normalization, joint feasibility
and scope boundaries. They do not establish an exhaustive literature
search, a formal-library result or worldwide novelty of the formulas.

### 216.9 The remaining universal obligation

For every actual full score y with $\Delta_O(y)\le1$, the unresolved
positive statement still asks for one unrestricted full V and one
$\theta\in[0,1]$ satisfying

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H\bigl(Q(y)-Q(V)\bigr)\le\theta.
\tag{216.31}
$$

Every bound is evaluated with the same full score, and with the same
complete feasible $\lambda$ and residual budget at a given b. For
instance, the zero cores of 216.3 give $F_{Q(V)}(b)\le0$ for that
same $\lambda$; adding a residual of charge $\theta$ gives at most
$\theta$. No separate optimum or shared stock is counted twice.

A genuine negative alternative requires one actual $b\in H_N$,
one actual full unit-O y and one complete feasible $\lambda$ of mass
$M\ge1$ for that b, with $F_{Q(y)}(b)>M$, together with the original
source, law and resource correspondence. An auxiliary affine test or
hull point without that full feasible realization is insufficient.
Neither alternative follows for unrestricted multi-positive signed
quotients or general low-terminal scores from the domains above.

In particular, (216.5) and (216.15) are sufficient capacity domains;
their failure is not nonmembership. The signed conversion threshold
in 216.8 is sufficient, while (216.7)'s iff concerns its precise
two-positive zero-cost fiber. It is not a positive-cost classification.
Coordinate deletion and separately funded or bounded-surplus additive
decomposition have the specific failures proved above; they are not
failures of arbitrary joint V. The complete unit inputs of 216.10
already admit V=y and $\theta=0$. Affordability always retains the
actual full-unit-O premise or an independently established cost at most
one, and $\theta=1$ may retain a nonzero zero-cost core. The original
universal implication and a genuine same-realization separator remain
unresolved.

## 追加锚（本行以下为增补区）
## 217. Joint-triple acquisition-resource relations

The six relations below share one owning continuation and retain their distinct hypotheses.
All constructions below use the full finite Boolean word set, every word and every
label, one complete score, one stock and one common budget. They are ordinary
results with the hypotheses displayed beside each formula. Their failure
conditions are construction limits, never nonmembership in the original
comparison.

### 217.1 Shared notation and the single-budget certificate

For $L\ge3$, let $\Omega={0,1}^L\setminus\{1^L\}$,
$n(w)$ be the first zero, and $\Omega_j={w:n(w)=j}$. The word $w(Z)$ has
zero set exactly $Z$; multiple-zero words are retained. A full score consists
of independent $A_w,C_w,P_w,T\ge0$ and

$$
g_V(w,\ell)=A_w1_{\ell=0}+C_w1_{\ell=n(w)}+P_w1_{\ell\in\{0,n(w)\}},
\qquad g_V(1^L,\ell)=T1_{\ell=0}.
$$

All labels $0,\ldots,L$ are maximized in every cell, including earlier and
unqueried labels. A complete N pair has cells $00,01,10,11$; an increasing O
pair has $0,10,11$ after merging $00,01$. Empty and singleton schedules are
included. N reversals permute cells and repeated requests give singleton
information, while still counting as actual requests. The O pair catalog uses
distinct increasing addresses; its normalized information partitions do not
grant a free repeated or ignored original request.
For example at word 0100, the legal N table $(3,4;1,0,0,0)$ emits
the earlier unqueried label 1 and has base/correct/pair readings $(0,1,1)$.
Replacing that output by zero gives $(1,0,1)$ and loses the correct row.
No such pruning is used. Donor-label domination below is proved only for
each constructed score, while unrestricted inputs retain the full catalog.
Write

$$
W=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\quad
\Delta_C=B_C-W,\quad
\beta_j=\sum_{\Omega_j}(C_w-A_w),\quad
K=\sum_w(A_w+C_w+P_w)+T,
$$

where $C=N,O$ and $B_C$ is the complete catalog support. The quotient is
$Q(V)=(\beta,K)$. The anchor is $R=(1,2;1,2,0)$, and $Q$ permits arbitrary
cancellations, suffixes, terminal mass, early or late $P$, changed unaries and
changed baselines. Every stated fixed-Q minimum ranges over all nonnegative
full scores of that quotient, with no constructor-support restriction.
Coefficients are dual proof weights, not source laws.

The same hull and demand notation is used throughout:

$$
\begin{aligned}
H_L=\{(b,e):&1\ge b_1\ge\cdots\ge b_L\ge e\ge0, b_2=b_3,\\
&(L+1)e\le\sum_{j\ge3}b_j,\quad b_1+\sum_{j\ge3}b_j-(L+1)e\le1\},\\
F_q(b,e)&=\sum_j\beta_j(b_j-\alpha_j)-Ke,\qquad \alpha=(1,1,0,\ldots,0),\\
\sigma_H(q)&=\max_{H_L}F_q,
\end{aligned}
$$

and $H_N$ consists of those $b\in H_L$ admitting one complete
$\lambda\ge0$ with $G_N\lambda\ge h(b)$, where $h=d-r$ and $r$ is the full
anchor event vector. In $h(b)$ and $F_q(b)$ the argument b denotes the
entire hull point, including e. The matrix $G_N=(z_D-r)_D$ has a column for every complete N
table D. Here $z_D$ records independently whether D emits zero, the word's
first-zero label, or either label, together with its positive-word zero event.
The demands at every zero word are $1-b_n-e$ for $A$,
$b_n-e$ for $C$, and $1-e$ for $P$; the positive row is $1-e$. Negative
singleton demands are never clipped. A single certificate is

$$
V\ge0,\quad 0\le\theta\le1,\quad
\Delta_N(V)+\theta\le1,\quad
\sigma_H(q-Q(V))\le\theta.
\tag{217.1}
$$

For the same full feasible $\lambda$ of mass $M=\sum_D\lambda_D$, the
identity $V\cdot h(b)=F_{Q(V)}(b)$ and nonnegativity give

$$
F_q(b)=V\cdot h(b)+F_{q-Q(V)}(b)
 \le V\cdot G_N\lambda+\theta
 \le M\Delta_N(V)+\theta\le\max(1,M).
$$

The last inequality uses $(1-\theta)M+\theta\le\max(1,M)$.
This applies to a conic $\lambda$ of any mass; it does not identify such a
vector with a normalized acquisition law. No component of $h$ is replaced
by its positive part. These are the existing full-event and signed-residual
suppliers of Continuation VI 199.3–199.4. An exact-fiber minimizer yields
an affordable certificate when the actual full unit-O input has $\Delta_O\le1$ (or a
separately established cost bound at most one); $	heta=1$ may retain a nonzero
zero-cost core.

### 217.2 A — joint Boolean carrier and signed zero-terminal plateau

Let $q=(\beta,K)$ satisfy $K\ge\sum_j|\beta_j|$. Let
$J=\{j\ge3:\beta_j>0\}=\{j_1<\cdots<j_m\}$ be the entire positive
late support, with $m\ge3$,
let $G\subseteq\{1,\ldots,\min J-1\}$ have $k\ge3$ guards, and put
$\gamma_i=\beta_{j_i}>0$, $\mu=\max_i\gamma_i$,
$\xi_a=(-\beta_a)_+$, $D_G=\sum_{a\in G}\xi_a$,
$D_e=(-\beta_1)_++(-\beta_2)_+$,
$B=K-\sum_j|\beta_j|$, and $S=B+D_G$.
Let
$c_m=m(m+1)/\lfloor(m+1)^2/4\rfloor$ and
$c_{m,k}=\max(c_m,3+1/(k-1))$. For every $\rho\ge0$ with

$$
S\ge c_{m,k}\rho,\qquad k\xi_a\le S\quad(a\in G),
\tag{217.2}
$$

there is one full score with $Q(V)=q$, $T=0$ and

$$
\Delta_N(V)\le D_e+\sum_{i=1}^3(\gamma_{(i)}-\rho)_+,
\tag{217.3}
$$

where $\gamma_{(1)},\gamma_{(2)},\gamma_{(3)}$ are the three largest positive
late coefficients. Taking $\rho=S/c_{m,k}$ gives the displayed strongest bound;
if $S\ge c_{m,k}\mu$, the unrestricted minima satisfy

$$
\min_{Q(V)=q}\Delta_N(V)=\min_{Q(V)=q}\Delta_O(V)=D_e.
\tag{217.4}
$$

The lower bound is unconditional: replace the legal stopped anchor's output by
zero on classes $j=1,2$ with $\beta_j<0$. This changes reward by
$-\beta_j$ and leaves $P$ and every other class fixed, so every competitor has
$\Delta_O\ge D_e$ and hence $\Delta_N\ge D_e$.

For the upper bound, take one measure $\nu$ on $\{0,1\}^m$ of mass $S$ such
that every zero marginal is at least $k\rho/(k-1)$, every directed $10$ cell
has mass at least $\rho$, and every $11$ pair has mass at least $\rho$.
Such a measure exists exactly when $S\ge c_{m,k}\rho$. Necessity follows by
fixing a pair, which gives $S\ge(3+1/(k-1))\rho$, and by summing the directed
and $11$ conditions:
$\int z(m-z)\ge m(m-1)\rho$ and
$\int z(z-1)\ge m(m-1)\rho$. Since
$mz(m-z)+z(z-1)\le(m-1)\lfloor(m+1)^2/4\rfloor$, integration gives
$S\ge c_m\rho$. Indeed adding m times the first summed inequality to the
second gives $m(m-1)(m+1)\rho$ below the integrated quadratic upper bound.
For attainment, if $m=2h-1$ put mass $c_m\rho$ uniformly
on words with $h$ ones. If $m=2h$, put mass $2\rho$ uniformly on the $h$-one
words and $2h\rho/(h+1)$ uniformly on the $(h+1)$-one words. Add the remaining
mass at $0^m$. Counting incidences gives one marginal $2\rho$, zero marginal
$S-2\rho$, and pair cells $(S-3\rho,\rho,\rho,\rho)$ in order
$00,01,10,11$. Thus every directed $10$ or $01$ mass and every $11$ mass
is $\rho$. To see the incidence count explicitly, both layer choices give
$\int z=2m\rho$ and $\int z(z-1)=m(m-1)\rho$; permutation symmetry then
gives the one and pair marginals. The extra zero atom changes only the 00
cells and zero marginals. The guard inequality is exactly
$S-2\rho\ge k\rho/(k-1)$. When $\rho=0$, use
$\nu=S\delta_{0^m}$; all inequalities are closed. The equivalent scalar
constant is $c_m=4-2/(\lfloor m/2\rfloor+1)$.

For each guard $a$ and atom $x$ of $\nu$, let $w(a,x)$ have zero $a$, selected
bits $x$, and all other bits one. Put $P_{w(a,x)}=\nu(x)/k$. Put
$C_{w(\{j_i\})}=\gamma_i$ and initially $A=T=0$. The complete N cell maxima
of this unsigned core are, in order $00,01,10,11$,

$$
0,\quad S/k,\quad S/k,\quad \max((k-2)S/k,\mu)
$$

for two guards;
$((S-2\rho)/k,2\rho/k,\max((k-1)(S-2\rho)/k,\gamma_i),
\max(2\rho(k-1)/k,\mu_{-i}))$ for a guard and $j_i$; and
$(S-3\rho,\max(\rho,\gamma_i),\max(\rho,\gamma_j),
\max(\rho,\mu_{-i,-j}))$ for two selected positives. Here
$\mu_{-i}$ and $\mu_{-i,-j}$ omit the indicated coefficients. The conditions
in (217.2) give $(k-2)S/k\ge\rho$,
$(k-1)(S-2\rho)/k\ge\rho$ and $2\rho(k-1)/k\ge\rho$.
Thus each competing correct reward can contribute no more than its
$(\gamma_i-\rho)_+$ deficit. For a selected pair the excess is exactly
the sum of the two queried deficits and the largest remaining deficit.
Querying the two largest coefficients attains the sum of the three largest
deficits; guard pairs and mixed pairs have no larger sum. Schedules involving
inactive coordinates reduce to singleton or constant information on this
unsigned core. Empty, singleton and repeated schedules are coarsenings of
distinct-pair information, and O is contained in N. This bounds O without
turning a last-address stopped singleton into an unavailable larger pair.

For signed conversion, at guard $a$ set $A_{w(a,x)}=(\xi_a/S)\nu(x)$ and
$P_{w(a,x)}=(1/k-\xi_a/S)\nu(x)$ (equivalently, convert fraction
$k\xi_a/S$ of that guard's P mass) at the same words. Add sole-zero A
mass $(-\beta_j)_+$ outside the guard set and add early positive C masses. The conversion is valid exactly under
$k\xi_a\le S$, preserves every zero reward and decreases only guard labels.
If $S=0$, (217.2) forces all guard $\xi_a=0$, and all guard coefficients
are zero without division. An early guard conversion lowers W by $\xi_a$;
a late guard conversion leaves W unchanged. A late sole-zero A addition or
an early C addition raises W by its entire mass and raises any table reward
by at most that mass, so cannot increase excess. Early A outside G costs at
most its mass. This proves the early charge $D_e$ in (217.3), even with
negative positions between or after positives and positive early credits.
It spends the negative guard stock once. The resulting totals are
$A=\sum(-\beta_j)_+$, $C=\sum(\beta_j)_+$, $P=B$, $T=0$, so the quotient is
exact and (217.3) follows. At $\rho=\mu$ its upper bound matches the
unrestricted modified-anchor lower bound, proving (217.4) against all full
competitors, including arbitrary terminal mass and cancellations. The sharp
iff concerns the displayed carrier protection conditions. Plateau entry is
only sufficient for the unrestricted fiber; outside it (217.3) is an upper
bound rather than a claimed minimum.

A concrete unequal repair is $L=8$, $G=\{1,2,3\}$,
$J=\{4,5,7\}$,
$\beta=(-1/2,-1/2,-1,2,3/2,-1,1,-1)$ and $K=27/2$. Then
$B=5,D_G=2,S=7,D_e=1$, and $c_{3,3}=7/2$. The measure has masses
$\nu(000)=1$ and $\nu(011)=\nu(101)=\nu(110)=2$. The converted score has
$A_{w(a,x)}=\nu(x)/14,P_{w(a,x)}=11\nu(x)/42$ for $a=1,2$,
$A_{w(3,x)}=\nu(x)/7,P_{w(3,x)}=4\nu(x)/21$, plus
$A_{w(\{6\})}=A_{w(\{8\})}=1$ and
$C_{w(\{4\})}=2$, $C_{w(\{5\})}=3/2$, $C_{w(\{7\})}=1$.
It has $W=8$ and $B_N=B_O=9$. Moving the C mass two at class 4 to
$w(\{4,5\})$ preserves $Q,W$ and gives an input with
$(\Delta_N,\Delta_O)=(2,1)$; the repaired score has both costs one. This
illustrates score replacement, not an original separator. Its totals are
$A=4$, $P=5$, $C=9/2$ and $T=0$. For the moved score, before the two
late A additions, pair (4,5) has N maxima $(2,2,2,2)$, while its stopped
maxima are $(3,2,2)$. At (5,7), the earlier unqueried label 4 earns two in
01 and is covered by that cell's baseline two. At a guard/5 pair the
receiving baseline is $(2/3)(7-4)=2$. The other pair types keep the bound.
Both late A atoms lie in pair-(4,5) cell 11, giving final N maxima
$(2,2,2,4)$ and support ten. They raise any O support by at most two;
constant zero attains nine. The actual N table $(4,5;4,0,0,0)$ attains ten,
and constant zero attains the repaired support nine. Those are support
detectors, not claims of feasibility at an arbitrary selected cap.

### 217.3 B — moving consecutive unequal-triple threshold

Fix $k\ge3$, $L\ge k+3$, and consecutive pivots
$n=k+1,m=k+2,\ell=k+3$. Let
$u\ge v\ge w\ge a=u/(k-1)\ge0$, $G=u+v+w$, and
$B_0=ka+v+w$. Assume $(k-2)B_0\ge ku$. For
$\beta_n=u,\beta_m=v,\beta_\ell=w$ and all other beta zero, with
$K=G+B$, $B\ge0$, the exact unrestricted zero-cost threshold is

$$
\min\Delta_N=\min\Delta_O=0\quad\Longleftrightarrow\quad B\ge B_0.
\tag{217.5}
$$

Below threshold every full competitor has
$\Delta_O\ge(B_0-B)/H$, $H=(2k-1)/(k-1)$; no exact positive-cost formula is
claimed. More generally let every coordinate outside the three pivots have
$\beta_j=-\xi_j$, $\xi_j\ge0$; take pivot $\xi_j=0$ in sums.
Put $D=\sum\xi_j$, $E=\xi_1+\xi_2$, and absolute stock
$B=K-G-D$. Put $s=B_0/k$ and
$R_{\rm stock}=\sum_{j=1}^k(s-\xi_j)_+$. If $B\ge R_{\rm stock}$, one score with
$T=0$ attains

$$
\min\Delta_N=\min\Delta_O=E.
\tag{217.6}
$$

The stock $B$ in (217.6) is absolute; literal stock is $K-G=B+D$.

Proof of (217.5): let $w_i(v)$ have sole guard zero i, pivot bits v and
ones after $\ell$; $w_0(v)$ has all guards one and the same pivot bits
and padding. The complete unsigned core is the following table, with every
unlisted coefficient zero. Each guard has mass $s=B_0/k$.

| Word | P mass | C mass |
|---|---:|---:|
| $w_i(000)$ | $a/k$ | $0$ |
| $w_i(011)$ | $u/k$ | $0$ |
| $w_i(100)$ | $(v-a)/k$ | $0$ |
| $w_i(101)$ | $a/k$ | $0$ |
| $w_i(110)$ | $w/k$ | $0$ |
| $w_0(000)$ | $0$ | $a$ |
| $w_0(011)$ | $0$ | $u-a$ |
| $w_0(100)$ | $0$ | $v$ |
| $w_0(110)$ | $0$ | $w$ |

The guard-indexed rows occur for every $1\le i\le k$. Initially A and T
are zero. Zero dominates all guard labels pointwise.
For two guards the 11 baseline is $(k-2)s\ge u$; for guard/n, guard/m,
guard/ell the zero baselines are respectively
$(u,(k-1)(v+w)/k)$,
$((k-1)v+u)/k,(k-1)(u+w)/k$,
and $((k-1)(v+w)/k,u)$, which dominate the corresponding correct labels.
For the three pivot pairs, the zero-baseline vectors are
$(a,u,v,w)$, $(a,u,v+w-a,a)$ and $(v,a,w,u)$. The corresponding class-n C vectors are
$(a,u-a,0,0)$, $(a,u-a,0,0)$ and $(a,0,0,u-a)$; class-m vectors are
$(0,0,v,0)$, $(0,0,v,0)$ and $(v,0,0,0)$; class-$\ell$ vectors are
$(0,0,0,w)$, $(0,0,w,0)$ and $(0,0,w,0)$. Each is dominated because
$v,w\ge a$. In the mixed pairs the competing correct maxima are
$(u,v)$, $(v,\max(w,u-a))$ and $(v,u-a)$ respectively. The ordering
and ratio hypotheses imply $(k-1)w\ge v$ and
$(k-1)(u+w)/k\ge u-a$, so their baselines dominate too.
Short schedules are coarsenings, and addresses after $\ell$ are constant on
the core support. Hence every complete N support is $B_0$; cell merging
preserves zero dominance and every O support is $B_0$ too. At larger unsigned
stock B, add $B-B_0$ of sole-zero-1 P. This preserves zero dominance and
proves sufficiency for every $B\ge B_0$ with T still zero.

For necessity use stopped tables $S_j=(j,n;0,n,0)$ with weight $1/(k-1)$
for $j\le k$ and $J=(n,m;0,m,\ell)$ with weight one. Their total is H.
On a first-zero guard class let $z\ge1$ count all zero guard bits. If
the n bit is zero, nonzero output weight is $(k-z)/(k-1)\le1$; if it
is one, that weight is exactly one. No table emits the guard's first-zero
label. In class n the correct weight is $k/(k-1)$; in classes m and
$\ell$ it is one, and all pivot pair weights are H. After $\ell$ and on
the positive word nonzero weight is one. There are no intervening classes
between consecutive pivots. This checks every word, not only sole zeros.
Subtracting $H$ times $Z$ from an arbitrary score, the independent A, C,
P and positive rows give a lower reward $B_0-A_{out}-P_{out}-T$.
Here I is the three pivot classes and out is its complement. Using
$B+D=2A_I+2A_{out}-D+P_I+P_{out}+T$ gives
$H(\Delta_O-E)\ge B_0-B-D+2A_I+(A_{out}-D)+P_I\ge B_0-B-D$, since
$A_{out}\ge D$. Constant zero gives $\Delta_O\ge E$, hence (217.5) and the signed lower cut
$\Delta_O\ge E+(B_0-B-D)_+/H$.
This last cut remains valid for arbitrary nonnegative u,v,w without the
constructor's amplitude cone. It uses literal stock $B+D=K-G$, rather
than substituting absolute B into that stock identity.

For signed construction, convert the fraction
$\eta_j/s$ of each of the five P masses in guard $j$ to A,
where $\eta_j=\min(\xi_j,s)$, add sole-zero A of mass $\xi_j-\eta_j$ at
guard j, add $\xi_j$ of sole-zero A for every $j>\ell$, and put surplus
$B-R_{\rm stock}$ into sole-zero-1 P. One score
has $Z=B+D$, $W=B+D-E$ and every complete schedule support equal to $Z$,
so both excesses are
$E$. At $s=0$ all $\eta_j=0$ and no division occurs. This covers closed
endpoints, zero terminal mass, every suffix and every numerical label.

For $u=v=w=g$, replace the n C atoms by $C$ mass $g$ at pivot pattern 001
and add early A one. The resulting $Y_g$ has
$\Delta_O=1$ and $\Delta_N=1+(k-2)g/(k-1)$; restoring the C atoms gives
one same-Q score with both costs one. At $k=4,g=3$, $Q=(-1,0,0,0,3,3,3;20)$,
$W=10$, and $(B_O,B_N)=(11,13)$ versus the repaired $(11,11)$.
Only N pairs (n,m) and (m,$\ell$) gain $g-a$ from that relocation.
Their stopped first-zero cells merge and have baseline $g+a\ge g$;
the guard and mixed-pair bounds persist. The early A adds at most one to
every support and adds exactly one in an attaining late pair's 11 cell.
This proves the whole $g\ge0$ amplitude family, including $g=0$.

An unequal signed example takes $k=4,L=8$, $(u,v,w)=(3,2,1)$,
$\xi=(3/4,1/4,2,1,0,0,0,3/2)$ and absolute $B=13/4$.
Then $Q=(-3/4,-1/4,-2,-1,3,2,1,-3/2;59/4)$,
$W=31/4$, $B_N=B_O=35/4$, and the attained minima are one.
The guard condition is automatic for $k\ge4$, since $v,w\ge u/(k-1)$
give $(k-2)B_0\ge(k^2-4)u/(k-1)\ge ku$; at $k=3$ it is exactly
$v+w\ge3u/2$. The zero profile has $s=0$, $R_{\rm stock}=0$,
and is handled by sole-zero additions without division. Neither the signed
plateau condition nor the below-threshold lower cut is asserted to classify
all signed fibers or their positive-cost minima.

### 217.4 C — attained signed face with terminal and suffix extension

Fix $L\ge6$, $a\ge b$, $a,b,c,\delta,t\ge0$, $\mu=\max(a,b,c)$, with

$$
\begin{gathered}
a\ge3\delta,\quad 0\le t\le\min(a,b,c-\delta),\\
3\max(b,c)\le2(b+c-\delta)+t,\quad
3\max(a,c)\le2(a+c-\delta)+t,\\
6\mu\le3a+2b+2c+\delta+4t,\quad
3\mu+2t\le3a+2b+2c-2\delta.
\end{gathered}
\tag{217.7}
$$

Set
$x=(a-3\delta)/6$, $y=a/3$, $z=b/3$, $v=(c-\delta-t)/3$,
$s=x+y+z+v$, $B_{lit}=3s+t=(3a+2b+2c-5\delta)/2$.
For $\xi_j\ge0$ outside $\{4,5,6\}$ require
$\xi_i\le s$ for $i=1,2,3$ and $\sum_{j>6}\xi_j\le t$. Put
$E=\xi_1+\xi_2$, $D=\sum\xi_j$,
$\beta=(-\xi_1,-\xi_2,-\xi_3,a,b,c,-\xi_7,\ldots,-\xi_L)$ and
$K=a+b+c+B_{lit}$. Its absolute stock is $B_{abs}=B_{lit}-D$;
the donor and suffix capacities ensure $D\le B_{lit}$. Then

$$
\min_{Q(V)=(\beta,K)}\Delta_N(V)=\min_{Q(V)=(\beta,K)}\Delta_O(V)=E+\delta.
\tag{217.8}
$$

On six core coordinates, let $w_i(v)$ have sole guard zero i and pivot
bits v, and let $w_0(v)$ have all guards one. The initial measures are

| Core word | P mass | C mass |
|---|---:|---:|
| $w_i(000)$ | $x$ | $0$ |
| $w_i(010)$ | $y$ | $0$ |
| $w_i(100)$ | $z$ | $0$ |
| $w_i(110)$ | $v$ | $0$ |
| $w_0(010)$ | $0$ | $a$ |
| $w_0(100)$ | $0$ | $b$ |
| $w_0(110)$ | $0$ | $c$ |

The guard rows occur for each $i=1,2,3$, and unlisted A, C and P
coefficients initially vanish. All three guard bits are one at the C atoms:
$C_{111010}=a$, $C_{111100}=b$, $C_{111110}=c$. Their core zero sets
are $\{4,6\}$, $\{5,6\}$, $\{6\}$ respectively. The core terminal
mass is $t$. Convert fraction $\xi_i/s$ of every P row in guard class i
to A at the same word. If $s=0$, its capacities force all three
$\xi_i=0$ and no division or conversion is used.
For $j>6$, use one common suffix law of masses $\xi_j/t$ on its sole-zero
word and remaining mass on the all-one suffix; tensor every core measure with
this same law, put A mass $\xi_j$ on the corresponding extended sole-zero
word, and retain terminal mass $t-\sum_{j>6}\xi_j$. If $t=0$, all suffix
negative masses vanish and only ones are appended. This common tensor is a
single stock, not a second acquisition law. More explicitly, each
nonterminal core atom at u with mass r becomes atoms $(u,v)$ of masses
$r\nu(v)$. The old terminal zero reward $t\nu$ becomes A at core
$1^6$ and each nonpositive suffix, with terminal coefficient
$t\nu(1^{L-6})$. Thus every old numerical-label reward measure, including
label zero, is tensored with the same $\nu$, and every new numerical-label
reward is zero. K remains $a+b+c+B_{lit}$, W becomes $B_{lit}-E$, and
the actual terminal coefficient is $t-\sum_{j>6}\xi_j$, possibly zero.

For the unrestricted lower cut, $Z=\sum A+\sum P+T$ gives $W=Z-E$, hence
$\Delta_O\ge E$. A single stopped mixture of $(1,4;0,4,0)$,
$(2,4;0,4,0)$, $(3,4;0,4,0)$ (weight $1/5$ each) and $(4,5;0,5,6)$
(weight $2/5$) has total weight one. Its class counts are at least
$(3,0,3)$ on guard classes, $(2,3,5)$ on class 4, $(3,2,5)$ on classes 5,6,
$(3,0,3)$ after 6 and $(3,0,3)$ on the positive word. Weighted accounting
using $B_{lit}=2A_{tot}-D+P_{tot}+T$ gives
$5(\Delta_O-E)\ge3a+2b+2c-2B_{lit}=5\delta$.
For clarity the counts are for the unnormalized five copies of the mixture:
the positive word needs only its zero count three. Writing I for pivot
classes 4,5,6, the reward minus $5Z$ is at least
$3a+2b+2c-2(A_{out}+P_{out}+T)$, and

$$
B_{lit}-(A_{out}+P_{out}+T)
 =2A_I+(A_{out}-D)+P_I\ge0.
$$

This allows arbitrary cancellations and independent P atoms in competitors.
The single stopped table $(4,5;4,5,6)$ also yields
$\Delta_O\ge E+a+b+c-B_{lit}$, with nonnegative cancellation slack
$(A_{tot}-D)+A_I$. Both cuts apply without a constructor support assumption.

For the upper bound, before conversion the exact excesses for complete pair
types are
$\left(\mu-s-t\right)_+$ (two guards),
$(a-2(x+y))_++(\max(b,c)-2(z+v)-t)_+$ (guard/4),
$(b-2(x+z))_++(\max(a,c)-2(y+v)-t)_+$ (guard/5),
$(\mu-2s)_+$ (guard/6),
$(a-3y)_++(b-3z)_++(c-3v-t)_+$ (45),
$(a-3(x+y))_++(\max(b,c)-3(z+v))_+$ (46), and
$(b-3(x+z))_++(\max(a,c)-3(y+v))_+$ (56). The inequalities (217.7)
make each at most $\delta$; all labels, including earlier label 4 in pair 56,
are included. The first summands in guard/4 and guard/5 are respectively
$\delta$ and $(\delta+(b-a)/3)_+\le\delta$; the reservoir inequalities
cover their second summands. The last two inequalities bound two-guard and
guard/6 excesses. Pair45 has excess exactly $\delta$. In pairs46 and56
the first summands vanish, and the second summands are
$(\delta+t-\min(b,c))_+$ and $(\delta+t-\min(a,c))_+$, at most $\delta$.
Conversion leaves zero reward fixed and lowers donor labels. Tensoring with
the common suffix law preserves every old/old support. An N old/new pair
has exactly the old singleton support, and an N new/new pair exactly the
old empty support, because the same nonnegative factor multiplies each
label's reward in each suffix cell. No mixed schedule exceeds the old
support. O is bounded by N, while the old stopped guard/4
table attains $B_{lit}+\delta$, proving (217.8), including all equality cases.

For the relocation family, move $0\le u\le\min(a,b)$ of C mass from
the core word $111010$ to $111000$, retaining the same suffix law on
every moved fiber. Thus core zero set $\{4,6\}$ becomes $\{4,5,6\}$;
at suffix zero set Z the actual move is
$w(\{4,6\}\cup Z)\longmapsto w(\{4,5,6\}\cup Z)$.
Then $Q,W$ and $\Delta_O=E+\delta$ remain fixed,
while
$\Delta_N=E+\delta+(u-(a-3\delta)/2)_+$. At $L=7$ with
$(a,b,c,\delta,t)=(3,5/2,3,1/2,1/2)$,
$(\xi_1,\xi_2,\xi_3,\xi_7)=(1/4,1/4,1,1/2)$ and $u=1$, one has
$\beta=(-1/4,-1/4,-1,3,5/2,3,-1/2)$, $K=69/4$, $B_{lit}=35/4$,
$W=33/4$, and the moved score has $(\Delta_N,\Delta_O)=(5/4,1)$;
moving it back gives the common minimum one. Here $D=2$,
$B_{abs}=27/4$ and the actual terminal coefficient is zero: the common
suffix law is concentrated on its sole zero at 7. The actual relocation is
therefore $w(\{4,6,7\})\longmapsto w(\{4,5,6,7\})$ with mass one.
The repaired supports are $37/4$ each; the moved supports are
$(19/2,37/4)$.

To verify the relocation formula on the whole closed domain, only pairs
querying 5 change. At a guard/5 pair the inserted label-4 mass in the
late-zero cell is at most b, already present as label 5; its other cell
loses label-4 mass. Pair56 moves it into a cell already containing b, so
that maximum does not rise. O pair45 merges the affected cells and is
unchanged. N pair45 alone gains $(u-3x)_+$ in 00; its 01 reward stays
under $3y=a$ and its existing 11 excess is $\delta$. The attaining stopped
tables persist, proving both exact costs. The same suffix tensor proves the
statement for every actual moved fiber, including $u=0$ and donor exhaustion.

For the unsigned equal profile, every $L\ge6$ and $g,B\ge0$ gives

$$
\min\Delta_N=\min\Delta_O
 =\max\{0,3g-B,(7g-2B)/5\},\qquad K=3g+B.
$$

This is the $k=3$ case of (217.14), counted once. Its lower cuts are the
two just proved and the anchor. In the middle interval
$8g/3\le B\le7g/2$, take $a=b=c=g$,
$\delta=(7g-2B)/5$ and any $0\le t\le g-\delta$. They satisfy (217.7).
For $0\le B\le8g/3$, convexly mix the entire $B=8g/3$ score with the
C-only score on core patterns 010,100,110, keeping each C total g.
The mixture coefficient is $3B/(8g)$ when $g>0$, and the resulting
upper bound $3g-B$ matches the single-table lower cut. For $B\ge7g/2$,
add terminal mass $B-7g/2$ to the zero-cost endpoint: each support rises
by at most that mass and W by exactly it. At $g=0$ use $T=B$.
This accounts for every branch, all closed endpoints and the freely allocated
middle reservoir; it is not a second equal-profile classification.

### 217.5 D — natural ownership: arbitrary guards and one joint share test

Let disjoint finite address sets $I,J\subseteq\{1,\ldots,L\}$ satisfy
$1,2\in I$, $|I|,|J|\ge3$. Put $k=|I|$, $j_0=\min J$, and set
all beta coordinates outside $I\cup J$ to zero. Let $\gamma_j>0$ for $j\in J$,
$\xi_i\ge0$ for $i\in I$, $\alpha_i\ge0$ with $\sum_I\alpha_i=1$, and
$p_j,c,d,t\ge0$. The $\alpha_i$ here are donor shares, separate from the
anchor-offset vector in 217.1. Put
$G=\sum_J\gamma_j$, $P=\sum_Jp_j$, $S=P+c+d$,
$E=\xi_1+\xi_2$, $D=\sum_I\xi_i$.
For $U\subseteq I$, define
$a_j(U)=\sum_{i\in I,\ i>j,\ i\notin U}\alpha_i$ and
$f_j=1-a_j(\varnothing)$. If the following five conditions hold,

$$
\begin{aligned}
\xi_i&\le\alpha_i[d+\sum_{j\in J,\ j>i}p_j+c1_{i<j_0}],\\
f_jp_j&\ge\gamma_j,\\
(1-\alpha_i)(p_r+c)-(p_r+c1_{r=j_0})a_r(\{i\})&\ge\gamma_r,\\
(1-\alpha_i)(P-p_r+d)+t-p_ja_j(\{i\})&\ge\gamma_j,\\
(1-\alpha_i-\alpha_h)S+t-(p_j+c1_{j=\min J})a_j(\{i,h\})&\ge\gamma_j,
\end{aligned}
\tag{217.9}
$$

The first line is for every $i\in I$, the second for every $j\in J$,
the third for every $i\in I,r\in J$, the fourth for every $i\in I$ and
distinct $j,r\in J$, and the fifth for distinct $i,h\in I$ and every
$j\in J$. If these simultaneous conditions hold, then with $\beta_i=-\xi_i$, $\beta_j=\gamma_j$,
$K=G+S+t$, one explicit score has

$$
\min_{Q(V)=q}\Delta_N(V)=\min_{Q(V)=q}\Delta_O(V)=E.
\tag{217.10}
$$

The initial score is specified by the following rows; coincident words add.

| Word | P mass | C mass |
|---|---:|---:|
| $w(\{i,j\})$ | $\alpha_i p_j$ | $0$ |
| $w(\{i\}\cup J)$ | $\alpha_i c$ | $0$ |
| $w(\{i\})$ | $\alpha_i d$ | $0$ |
| $w(\{j\})$ | $0$ | $\gamma_j$ |

The indexed rows range over $i\in I,j\in J$, the middle two once per i,
with initial A zero and $T=t$. The actual P mass of first-zero class i is
$R_i=\alpha_i[d+\sum_{j\in J,\ j>i}p_j+c1_{i<j_0}]$.
In that class convert fraction $\xi_i/R_i$ of each P atom to A at the
same word. A row indexed by a donor i but whose first zero is a positive
j belongs to class j and is not converted. If $R_i=0$, the first condition
forces $\xi_i=0$ and no division or conversion occurs.
The total donor mass remains one shared stock, and the quotient is exact with
$W=S+t-E$. Its absolute stock is $S+t-D$, not literal $S+t=K-G$.

Proof: before conversion, zero reward dominates every donor label pointwise.
For a J/J pair at r,l the zero cells are $c,p_r,p_l,P-p_r-p_l+d+t$.
Label r in 01 has P reward $p_ra_r(\varnothing)$ in addition to its
correct atom; its remaining reserve is exactly $f_rp_r$, and likewise for l
in 10. An unqueried j in 11 has reward
$\gamma_j+p_ja_j(\varnothing)\le p_j$, which is included in the
baseline. All P-only cells are dominated by zero. For a mixed i,r pair,
in (guard bit, positive bit) order regardless of numerical address order,
the four zero masses are
$\alpha_i(p_r+c),\alpha_i(P-p_r+d),(1-\alpha_i)(p_r+c),
(1-\alpha_i)(P-p_r+d)+t$. Label r in 10 has extra P reward
$(p_r+c1_{r=j_0})a_r(\{i\})$; every other positive j in 11 has extra
P reward $p_ja_j(\{i\})$. These subtractions are exactly the third and
fourth reserves. For two guards, all correct atoms
lie in 11 and the final inequality protects every positive label. Inactive
coordinates reduce to singleton partitions; all labels remain present.
In that 11 cell positive j has P reward
$(p_j+c1_{j=j_0})a_j(\{i,h\})$, which the last inequality subtracts.
Conversion leaves zero reward fixed and decreases only donor labels, so
$B_N=B_O=S+t$ and (217.10) follows from the universal constant-zero lower
bound $W=Z-E$. A failure of any positive-label reserve is exposed by
its indicated pair cell; since zero's total is $S+t$, that failure raises
the N support above $S+t$. Thus, after valid class conversions, the four
reserve families are necessary and sufficient for this particular score
to have $\Delta_N=E$. Its attainment proves the unrestricted minimum on
the stated cone. The tests are only sufficient for unrestricted fiber
attainment and are not necessary conditions on every possible score.

If every guard precedes every positive, $p_j=\gamma_j$, and
$S=G+c+d>0$, put
$h=\min\{c/(\mu+c),\min_j[1-(\mu_{-j}-t)_+/(G-\gamma_j+d)]\}$,
$v=1+(t-\mu)/S$, and $l_i=\xi_i/S$ for $i\in I$. Here
$\mu=\max_{j\in J}\gamma_j$ and $\mu_{-j}=\max_{h\in J\setminus\{j\}}\gamma_h$.
Write $l_{[1]}\ge l_{[2]}$ for the two largest values among all $l_i$,
including ties. These ranks do not relabel physical addresses 1 and 2,
which still define E. The joint share problem is feasible exactly when

$$
\sum_{i\in I}l_i\le1,\quad l_{[1]}\le h,\quad
l_{[1]}+l_{[2]}\le v,\quad
1\le\min\{kh,kv/2,(k-1)v-(k-2)l_{[1]}\}.
\tag{217.11}
$$

This follows by reducing (217.9) to $\alpha_i\ge l_i$,
$\alpha_i\le h$, $\alpha_i+\alpha_j\le v$, $\sum\alpha_i=1$;
The first three tests say that the lower vector l is feasible before
requiring total one. If $h\le v/2$, its maximum-total extension has all
coordinates h. If $h>v/2$ and $l_{[1]}\le v/2$, use all coordinates
$v/2$. Otherwise keep the coordinate with largest lower share at
$l_{[1]}$ and put all others at $v-l_{[1]}$. The lower and pair tests
make each of these vectors feasible in its stated case. Summing individual
and pair constraints gives the first two total upper bounds. In the last
case, fixing a coordinate at least $l_{[1]}$ gives the third upper bound.
The corresponding constructed vector attains the minimum of all three.
Interpolation between that vector and l reaches total one exactly under
(217.11). The denominators in h are positive because at least three
$\gamma_j$ are positive. This includes ties, zero lower shares and every
closed cap, using one vector of shares on the actual physical addresses.

A concrete family takes $I=\{1,2,3\}$, $J=\{4,5,6\}$,
$\alpha_i=1/3$, $p_j=\gamma_j=g$, $c=g/2,d=t=0$ and
$0\le\xi_i\le7g/6$. Put $A_{w(\{i,j\})}=2\xi_i/7$,
$P_{w(\{i,j\})}=g/3-2\xi_i/7$,
$A_{w(\{i,4,5,6\})}=\xi_i/7$,
$P_{w(\{i,4,5,6\})}=g/6-\xi_i/7$, and C mass g at each pivot.
Then $Q=(-\xi_1,-\xi_2,-\xi_3,g,g,g;13g/2)$ and both minima are
$\xi_1+\xi_2$. For $0\le u\le g$, moving $u$ of class-4 C mass from $w(\{4\})$ to
$w(\{4,5\})$ gives $\Delta_O=E$ and
$\Delta_N=E+(u-g/2)_+$; at $g=4$, $\xi=(1,0,1)$, $u=4$ this is
$Q=(-1,0,-1,4,4,4;26)$ with input costs $(3,1)$ and repaired costs $(1,1)$.
Here the zero baselines in guard/guard, guard/positive and positive/positive
pairs are respectively $(0,7g/6,7g/6,7g/6)$,
$(g/2,2g/3,g,4g/3)$ and $(g/2,g,g,g)$. The moved label 4 remains covered
in every pair other than full (4,5); that pair has maxima
$(\max(g/2,u),g,g,g)$. Its stopped first cell has baseline $3g/2$ and
correct mass g. These formulas prove the relocation on $0\le u\le g$.
At the displayed unit input W is 13, supports are (16,14), and repaired
supports are (14,14). At $g=0$, capacities force $\xi=0$ and the score is zero.

For an interleaved instance, take $I=\{1,2,4,6,8\}$,
$J=\{3,5,7\}$, all donor shares $1/5$, $\gamma=(2,3,1)$,
$p=(5,5,5/4)$, $c=5,d=1,t=0$, and
$\xi=(1/2,1/4,1/2,1/5,1/10)$ on I. The same first-zero conversion gives
$\beta=(-1/2,-1/4,2,-1/2,3,-1/5,1,-1/10)$,
$K=93/4$, $W=33/2$ and both costs $3/4$. This retains negative
coordinates before, between and after positives, including ownership of
P rewards on positive first-zero classes.

### 217.6 E — common-chain multi-positive containment

Let $q=(\beta,K)$ satisfy $K\ge\sum_i|\beta_i|$, and let
$J=\{j\ge3:\beta_j>0\}=\{n_1<\cdots<n_r\}$ be the entire positive
late support, with $r\ge3$,
$n_1=k+1$ with $k\ge3$. Let $\gamma_t=\beta_{n_t}>0$,
$\mu=\max_t\gamma_t$, $\xi_i=(-\beta_i)_+$,
$D_0=\sum_{i\le k}\xi_i$, $D_1=\sum_{i>k}\xi_i$,
$E=\xi_1+\xi_2$, $E_+=(\beta_1)_++(\beta_2)_+$,
$B=K-\sum_i|\beta_i|$, $S=B+D_0$, and $\rho=(k-1)/k$.
Suppose there are $c_t\ge0$ with $\sum_tc_t=S$, $c_t\ge\gamma_t$,

$$
\rho\sum_{t\le i}c_t\ge\max_{t\le i}\gamma_t,\quad
\rho\sum_{t>i}c_t\ge\max_{t>i}\gamma_t\quad(1\le i<r),\quad
(1-2/k)S\ge\mu,\quad \xi_a\le S/k\ (a\le k).
\tag{217.12}
$$

Then one full score with $T=0$ has exact quotient and
$\min\Delta_N=\min\Delta_O=E$ over all full competitors.
Write $J_t=\{n_t,\ldots,n_r\}$. The unsigned core has rows

| Word | P mass | C mass |
|---|---:|---:|
| $w(\{a\}\cup J_t)$ | $c_t/k$ | $0$ |
| $w(J_t)$ | $0$ | $\gamma_t$ |

The first row occurs for each $1\le a\le k,1\le t\le r$, the second
once per t. Initially A and T vanish. Convert any total $\xi_a$ of
donor-a P to A at the same words; its total $S/k$ funds this conversion.
For definiteness proportional conversion uses fraction $k\xi_a/S$ of
each of that donor's atoms. Here $S>0$ follows from positive $\gamma_t$.
Add sole-zero A of mass $\xi_i$ for each negative coordinate $i>k$,
and early sole-zero C of mass $(\beta_a)_+$ for a=1,2. Unlisted rows
vanish; no other positive late coordinate exists outside J.

For the proof, a donor pair has zero cells $(0,S/k,S/k,(1-2/k)S)$;
the last capacity protects all positive labels. A donor/positive pair at $n_i$
has zero masses $(C_i/k,C_{>i}/k,\rho C_i,\rho C_{>i})$, where
$C_i=\sum_{t\le i}c_t$; (217.12) protects every block maximum. A positive/positive
pair at $n_i<n_j$ has an empty 01 cell and zero masses
$\sum_{t\le i}c_t$, $\sum_{i<t\le j}c_t$ and $\sum_{t>j}c_t$ in
00,10,11. Each block sum covers every earlier, intermediate and later
label by $c_t\ge\gamma_t$. In the donor/positive case at i=r, the
empty suffix maximum is zero and $\rho S\ge\mu$ follows from the
donor-pair condition. Thus zero dominates all labels for every core full
pair, including arbitrary numerical gaps; core-inactive coordinates are one
and reduce to short partitions. Conversion leaves zero reward unchanged.
For an old/new pair after an outside sole-zero A addition, its new-zero
branch has only base reward, and its new-one branch contains the old core
whose singleton zero reward already dominates every numerical label.
For two new addresses, the old core lies in 11, where its empty zero
reward dominates, while every other cell has only base additions. These
cases cover negative positions before, between and after J and prove both
supports $S+D_1$ before adding early C. Adding early C of total $E_+$ increases any schedule support by at most
$E_+$ and W by exactly $E_+$. The modified early anchor attains the upper
bound, so the two full supports are $S+D_1+E_+$ and
$W=S+D_1-E+E_+$; their excess is E. The unrestricted lower bound is the modified early anchor, giving
$\Delta_O\ge E$.
Direct totals give $A=D_0+D_1$, $P=S-D_0=B$,
$C=\sum_t\gamma_t+E_+$ and
$K=S+D_1+\sum_t\gamma_t+E_+=\sum_i|\beta_i|+B$.

For $r=3$, a sufficient explicit allocation is
$c_1=\gamma_1/\rho$, $c_3=\gamma_3/\rho$ and
$c_2=S-c_1-c_3$, provided

$$
S\ge\max\left\{\frac{\gamma_1+\gamma_3}{\rho}+
\max\left(\gamma_2,\frac{\gamma_2-\min(\gamma_1,\gamma_3)}{\rho}\right),
\frac{k\mu}{k-2}, k\max_{a\le k}\xi_a\right\}.
\tag{217.13}
$$

For equal $\gamma_t=g$, the first stock term is
$(3+2/(k-1))g$. This permits unequal and nonadjacent triples; it is a
sufficient common-chain cone, not a sharp unrestricted threshold.
The two outer cumulative constraints hold at equality for this allocation.
The inner constraints say
$c_2\ge(\gamma_2-\gamma_1)/\rho$ and
$c_2\ge(\gamma_2-\gamma_3)/\rho$, as well as $c_2\ge\gamma_2$.
Their simultaneous maximum is exactly the first stock term in (217.13).
The other two terms fund donor-pair protection and every conversion.
For equal g, the combined first and donor-pair terms reduce to
$(3+2/(k-1))g$: at k=3 the first term is $4g$ and the donor-pair
term is $3g$; for $k\ge4$ the first term also dominates $kg/(k-2)$.
No necessity for unrestricted scores is inferred.

At $L=8$, donors $a=1,2,3,4$, positives $5,6,7$, and one late negative at 8,
put P masses $1,3/4,1$ respectively at
$w(\{a,5,6,7\})$, $w(\{a,6,7\})$, $w(\{a,7\})$ for every donor.
Convert the first P atom at a=1 entirely to A, and add $A_{w(\{8\})}=1$.
Put C mass 3 at each of $w(\{5,6,7\})$, $w(\{6,7\})$, $w(\{7\})$.
Then $Q=(-1,0,0,0,3,3,3,-1;21)$, absolute B=10, $S=11$,
$W=11$ and both supports are 12. For $0\le u\le3$, move C mass u
from $w(\{5,6,7\})$ to $w(\{5,7\})$. Q and W stay fixed and costs
become $(1+u,1)$; u=1 is repaired from (2,1) to (1,1).
Pair (5,6) has N maxima $(4,u,3,5)$ and O maxima $(4,3,5)$.
At pair (6,7) the zero baselines 7 in 00 and 4 in 10 cover both pieces
of label 5; donor/6 receiving baselines are $21/4$ and 3. At (6,8)
the new-zero cell is base only and old singleton baselines 7 and 4 cover
the move. All other schedules are unchanged or coarser. This proves the
whole stated relocation interval with every label retained.
The fair-suffix sufficient plateau of §215.2 requires absolute
$B\ge4\mu$ and $B+D_l\ge5\mu$, whereas here $\mu=3,D_l=1$,
$B=10$ and $B+D_l=11$. That particular test fails; no claim excludes
all earlier signed or conic closures.

### 217.7 F — equal adjacent triple piecewise attained minimum

Let $k\ge3$, $L\ge k+3$, $n=k+1,m=k+2,\ell=k+3$,
$g,R\ge0$, and $0\le\xi_i\le R/k$ for $1\le i\le k$. Set
$\beta_i=-\xi_i$, $\beta_n=\beta_m=\beta_\ell=g$, other beta zero,
$D=\sum_{i\le k}\xi_i$, $E=\xi_1+\xi_2$, and $K=3g+R$. With literal stock R
and absolute stock $R-D$, the exact unrestricted minimum is

$$
\min\Delta_N=\min\Delta_O=E+\Phi_k(g,R),\quad
\Phi_k(g,R)=\max\left(0,3g-R,\frac{(3k-2)g-(k-1)R}{2k-1}\right).
\tag{217.14}
$$

For $g>0$, the breakpoints are $R_1=(3k-1)g/k$ and
$R_0=(3k-2)g/(k-1)$: the branches are $3g-R$, the second affine term,
and zero on the three successive closed intervals. The formula includes
$g=0,R=0$, exhausted donor capacities and all ties.

For any competitor, $Z=A_{tot}+P_{tot}+T$ gives $W=Z-E$ and hence
$\Delta_O\ge E$. The stopped table $(n,m;n,m,\ell)$ gives
$\Delta_O\ge E+3g-R$. The joint lower bundle assigns weight $1/(k-1)$
to $(i,n;0,n,0)$ for each $i\le k$ and weight one to
$(n,m;0,m,\ell)$. Its mass is $H=(2k-1)/(k-1)$; guard classes have
nonzero output weight at most one, pivot classes have weights $k/(k-1),1,1$,
and later/positive classes weight one. Subtracting $HZ$ gives
$H(\Delta_O-E)\ge(k/(k-1)+2)g-R$, yielding the third branch.
N dominates O, so these are common lower cuts. More explicitly, for every
competitor $R=2A_{tot}-D+P_{tot}+T$ and $A_{tot}\ge D$.
The single triple-output table has nonnegative slack
$(A_{tot}-D)+A_J$, where J is the three pivot classes. In the weighted
bundle, pivot pair weight is H and correct weights are $k/(k-1),1,1$.
On a guard class with z zero guard bits its nonzero-output weight is
$(k-z)/(k-1)$ if the n bit is zero and one otherwise, so it loses at
most its A+P mass relative to constant zero. Every later class has the
same loss bound and the positive row loses at most T. Therefore

$$
H(\Delta_O-E)\ge(k/(k-1)+2)g-R
 +(A_{tot}-D)+A_J+P_J.
$$

Dropping only this nonnegative slack gives the third cut. This separates
the A,C,P and positive rows, including every multiple-zero word and every
cancellation in unrestricted competitors.

For each guard $i\le k$, let $w_i(v)$ have sole guard zero i, pivot
bits $v\in\{0,1\}^3$ and ones after $\ell$. Let $w_0(v)$ have all
guards one, pivot bits v and the same one padding. Initially A and T vanish.
Put C mass g at each of
$w_0(000)$, $w_0(100)$ and $w_0(110)$: their zero sets are
$\{n,m,\ell\}$, $\{m,\ell\}$ and $\{\ell\}$.
Every branch below retains these same three C atoms. The complete initial
nonterminal measures, in terms of the branch parameters, are

| Word | P mass | C mass |
|---|---:|---:|
| $w_i(000)$ | $x$ | $0$ |
| $w_i(011)$ | $z$ | $0$ |
| $w_i(101)$ | $y$ | $0$ |
| $w_i(110)$ | $v_0$ | $0$ |
| $w_0(000)$ | $0$ | $g$ |
| $w_0(100)$ | $0$ | $g$ |
| $w_0(110)$ | $0$ | $g$ |

Each guard row occurs for all $i\le k$, $s=x+z+y+v_0$, and all
unlisted coefficients vanish before the surplus additions below.

For the middle branch put
$d=((3k-2)g-(k-1)R)/(2k-1)$,
$x=v_0=g/k$, $z=(g-kd)/(k(k-1))$, $y=(g-d)/k$ in the four pivot
patterns $000,011,101,110$ on each guard. Their total is $R/k$ per guard.
All complete pair supports are

$$
\begin{array}{c|l}
GG&2s+\max((k-2)s,g)\\
G n&s+\max((k-1)(x+z),g)+\max((k-1)(y+v_0),g)\\
G m&s+\max((k-1)(x+y),g)+\max((k-1)(z+v_0),g)\\
G\ell&s+\max((k-1)(x+v_0),g)+(k-1)(z+y)\\
nm&\max(kx,g)+kz+\max(ky,g)+\max(kv_0,g)\\
n\ell&\max(kx,g)+kz+\max(kv_0,g)+ky\\
m\ell&\max(kx,g)+ky+\max(kv_0,g)+kz.
\end{array}
$$

The guard/n, guard/m and nm supports equal $R+d$; guard/$\ell$,
n$\ell$ and m$\ell$ supports equal R. For guard/guard, the needed
inequality $(k-2)R/k\ge g-d$ is affine in d, with endpoint margins

$$
\frac{(2k^2-7k+4)g}{k(k-1)}\quad(d=0),\qquad
\frac{2(k^2-3k+1)g}{k^2}\quad(d=g/k),
$$

both nonnegative for $k\ge3$. Also $(k-1)(2g-d)/k\ge g$ verifies
the remaining maxima. Guard labels are pointwise subsets of zero reward;
every possible winning label is among $0,n,m,\ell$. Short or repeated
schedules are coarser, and after-$\ell$ queries are constant on the score
support. Thus the complete N excess is at most d. The unrestricted O
lower cut forces both excesses to equal d.

At $R=0$ use only the three specified chain C atoms. For
$0<R<R_1$, convexly mix the complete $R_1$ score with that C-only score
in proportions $R/R_1$ and $1-R/R_1$. The C atoms agree, each guard has
stock $R/k$, and support convexity gives $3g-R$, matched by the lower cut.
Equivalently $x=v_0=R/(3k-1)$, $y=(k-1)R/[k(3k-1)]$, $z=0$.
For $R\ge R_0$, use the $d=0$ score and add
$(R-R_0)/k$ P at each $w_i(111)$. Every table gains at most the total
surplus $R-R_0$ and W gains exactly it, so the cost remains zero.
For $g=0$ put $R/k$ of P at each $w_i(111)$ and retain zero C masses.
For $R>0$ convert fraction $k\xi_i/R$ of every donor
P row to A; zero reward and all support maxima are unchanged, W drops by E,
and the formula follows for the signed quotient. If $R=0$, all
$\xi_i=0$ and no conversion or division is performed.

The explicit unit input has $k=3,L=6,g=1,R=8/3$,
$\xi=(1/3,1/3,2/3)$. The common score has $W=2$, $B_N=B_O=3$.
Its guard P patterns are 000 with mass $1/3$, 101 with mass $2/9$,
and 110 with mass $1/3$, converted to A in fractions $3/8,3/8,3/4$
for guards 1,2,3. The C atoms remain $111000,111100,111110$, each
with mass one. Both repaired and moved scores have
$Q=(-1/3,-1/3,-2/3,1,1,1;17/3)$ and T=0.
Move $1/3$ of C at $w(\{4,5,6\})$ to $w(\{4\})$, that is,
$111000\longmapsto111011$, to obtain the same quotient
with $(\Delta_N,\Delta_O)=(4/3,1)$; restoring it repairs both costs to one.
For the moved score every empty and singleton support is $8/3$,
guard/guard supports are $25/9$, guard/4 and guard/5 are 3, and
guard/6 is $8/3$. Its remaining pair supports (N,O) are
45:$(10/3,3)$, 46:$(3,8/3)$ and 56:$(3,3)$.
In particular pair45 has full maxima $(1,1/3,1,1)$ and stopped
maxima $(1,1,1)$. This includes all seven output labels and proves the
exact unit-input gap. The g=0, R=0, breakpoint, tie and exhausted-capacity
cases use the same closed formulas and the explicit no-division conventions.

### 217.8 Original source, one-seed laws and owning transport

The original countable labeled source is

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
 \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\qquad
N(r,g)=1+F_rg,\qquad q_i(x)=1_{p_i\mid N(r,g)},
$$

where $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$ and the $p_i$ are increasing
primes. Each N has finite prime support, so $n(x)=\min\{i:q_i(x)=0\}$
is finite. There is no prior over X. The CRT/window proof of
[Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows)
supplies every finite pattern on arbitrary finite prime addresses, with actual
witnesses fixed before seeds. Thus every multiple-zero word is an actual
source pattern; a positive finite word represents a tail source, not an
infinite all-positive source. Source labels, N and n are not extra observations.
For the earlier-label example, $(r,g)=(19,436)$ is an actual source with
$N=1822917$ and first four prime replies 0100.

For concrete witnesses on the first seven primes, use $r=47$,
$F_{47}=2971215073$, $Q_0=9699690$, and prescribe a zero at 19.
For each prescribed positive bit require $g=-F_{47}^{-1}\pmod p$;
for each zero require $g=0\pmod p$. If c is the CRT residue, take
$g=c+Q_0\lceil(297121508-c)/Q_0\rceil$. The window
$[297121508,594243014]$ is longer than $Q_0$, so every representative
lies in it. Words 0000000 and 1111111 give respectively
$g=300690390,N=893415819074248471$ and
$g=305860043,N=908775969990028140$; the latter's actual first zero is eight.
On eight bits one can instead use $r=101$,
$F_{101}=573147844013817084101$ and the first-nine-prime product
$223092870$, prescribing zero at 23 and taking the least representative
above $\lceil F_{101}/10\rceil$. The all-one eight-bit word gives
$g=57314784401451390769$ and
$N=32849845109808618286359388848718688063670$, with first zero nine.
These finite witnesses corroborate source transcription; the arbitrary-address
statement is supplied by 35.2, not by checking finitely many integers.

The full original carrier is the disjoint-union Borel space
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, each block
an interval copy of $(0,1)$. Its unchanged consumer returns unknown on
$B_j$ and proposes j on $P_j$. The original nonatomic targets of
Definition 213.22 remain
$\mu_x=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$, with fixed $h_0\in(0,1)$,
$\Omega(x)$ the number of distinct prime divisors, $\pi_j$ uniform on
$P_j$, and $\nu_x$ on $B_{n(x)}$ having density proportional to
$\exp(t(x)u)$, $t(x)=\sum_i3^{-i}q_i(x)$. The distinct marks
$\theta_j=(B_1,1/(j+2))$, $j\ge0$, support separately selected laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\qquad 1\ge a_1\ge a_2\ge\cdots>0,\quad a_j\longrightarrow0.
$$

These laws do not replace the nonatomic originals. A finitely supported
marked law has TV distance one from each $\mu_x$, as its finite Borel
support has mass one under that law and zero under $\mu_x$. The companion
caps below concern the selected marked laws. Original competitors still
may output anywhere on the full carrier, not merely the marks.

The resources are exactly Definition 90.1: zero advice, one source-independent
common seed, sourcewise almost-sure finite handoff, uniform TV over every
actual source and Borel event, and at most two actual requests. Repeated
requests and requests with ignored replies count. N preselects its schedule
and obtains all its replies; O preselects an increasing schedule and stops
at its first queried zero or exhaustion. No source average, address, depth,
runtime, mean count or adaptive second address replaces these conditions.
Choose each finite whole table and every output label before replies by
partitioning one $U\sim\mathrm{Uniform}[0,1)$ into its full-table weights.
Its N completion uses the same U, schedule and output, acquiring both replies
even when the second is ignored. All displayed finite rules hand off on
every source and seed. Different finite partitions can use a common
refinement of this same U. Score coefficients, carrier weights and suffix
laws are deterministic proof measures, not additional acquisition seeds,
source distributions or separately funded resource allowances.

Here are the normalized common-law suppliers and their full row content.
Reuse the four-table law (213.30), with weight $1/4$ on each of

$$
(1,2;1,2,0),\quad(1,2;1,2,3),\quad
(1,3;1,3,0),\quad(2,3;2,3,0).
$$

At first-zero classes 1,2 the correct mass is $3/4$ and pair mass at
least $3/4$; the base demand $-1/4$ is retained. At class 3 its
(base,correct,pair) masses are $(1/4,3/4,1)$; after 3 they are
$(3/4,0,3/4)$, and positive-word base is $3/4$. Thus one mass-one full
$\lambda$ is feasible at
$b^*=(1,1,1,1/4,\ldots,1/4;e=1/4)\in H_N$.
For $a_1=a_2=a_3=1$, $a_4=\cdots=a_H=1/4$ and
$a_{H+t}=2^{1-t}/4$ for $t\ge1$, both executions attain cap $1/4$.
Every actual tail after 3 has error $\max(1/4,a_n)=1/4$, including
the first tail equality. For the displayed C quotient,
$F_q(b^*)=-53/16\le1$; this realized shared allocation is not a separator.

The subset supplier 87.1 gives a second common law: select uniformly a
three-subset $\{i<j<h\}$ of $\{1,\ldots,H,\star\}$, with star last.
Query i then j, emitting i on the first zero, j on 10 and h on 11;
star means output zero and is never queried. The N completion is
$(i,j;i,i,j,h)$ on the identical seed. On every word of first zero n,
output n occurs exactly when the selected subset contains n, so its
probability is $3/(H+1)$ independently of later zeros. Positive-word
base has that same probability. For $a_1=\cdots=a_H=1$,
$\varepsilon=(H-2)/(H+1)$ and
$a_{H+t}=\varepsilon2^{1-t}$, all base, correct, independent pair and
positive rows hold, including negative base demands, and every actual tail
has TV $\max(\varepsilon,a_n)=\varepsilon$.
At H=6 this is one 35-table mass-one allocation at $v_6\in H_N$,
with cap $4/7$; at the D example $F_q(v_6)=-27/7$.
At H=8 it is one 84-table allocation at $v_8\in H_N$ with cap $2/3$;
at the E example $F_q(v_8)=-6$. For these hull points,
$(H+1)e=\sum_{j\ge3}b_j=H-2$ and
$b_1+\sum_{j\ge3}b_j-(H+1)e=1$.
These are common full allocations, not independently selected event optima.

For the B/F lower bundle, normalization assigns probability $1/(2k-1)$
to each $(i,n;0,n,0)$ and $(k-1)/(2k-1)$ to $(n,m;0,m,\ell)$.
Put $\varepsilon_0=(k-1)/(2k-1)$,
$a_1=\cdots=a_\ell=\varepsilon_0$ and
$a_{\ell+t}=\varepsilon_0 2^{1-t}$ for $t\ge1$.
On a guard first-zero word correct probability is zero and base probability
at least $1-\varepsilon_0$, so TV is $\varepsilon_0$.
At n, the base and correct probabilities are
$(\varepsilon_0,1-\varepsilon_0)$ and TV is $1/(2k-1)$.
At m and $\ell$ the selected targets are reproduced exactly.
At every actual tail after $\ell$, the law is
$(1-\varepsilon_0)\delta_{\theta_0}+\varepsilon_0\delta_{\theta_\ell}$
and TV is $\max(\varepsilon_0,a_n)=\varepsilon_0$, including the first
tail equality. Its all-positive finite base is $1-\varepsilon_0$.
The word counts in the lower proof therefore give every independent cap
row for one law, including multiple zeros. The C lower detector likewise
has a one-seed realization with fifth weights $(1,1,1,2)/5$.
These detector executions alone confer no arbitrary prescribed cap;
the specific amplitude families just supplied establish their caps.

The owning transport is
[110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source).
It gives same-class feasibility at exact closed caps, not preservation of
an arbitrary competitor's law. Its necessity projects full-carrier outputs,
uses source countability for one conull handoff event, and controls the whole
preselected schedule by the single event that its maximum address exceeds
a cutoff. That event's seed probability vanishes. Actual finite low/fixed-high
witnesses and the measurable finite-execution supplier then give one common
catalog approximation; finite-simplex compactness retains the closed cap.
This requires measurable source-independent scheduling and readout, lawful
reachable reads and sourcewise conull finite handoff. The same-class
scheduled-witness interface supplies replay under those hypotheses; it does
not supply N-to-O conversion or arithmetic witnesses. Theorem 109.1 is
separately the $c\ge H^{\rm ker}$ criterion for a normalized probability-vector
kernel, not a condition on a dual quotient. The exact-law obstruction 112.2
has another O law at the same cap and remains distinct from cap separation.

For $0<\varepsilon\le1$, let the strict active length be
$L_a=\max(\{i:a_i>\varepsilon\}\cup\{0\})$, and let H be the
horizon of a score above. Transport first supplies one normalized complete
configuration at $L_a$. Use the existing prefix argument of Continuation
VII 202.13, 207.20 and §215.7, with the following two directions.
If $H<L_a$, restrict inputs to $(w,0,\ldots,0)$ and project labels above
H to zero only in the finite comparison. A zero in w retains its target;
a positive w has fixed next zero $H+1$, whose target projects to zero.
Fold the fixed higher replies into each terminal table and delete their
observations. At most two low preselected queries remain. In O all higher
addresses follow the low ones: a low zero stops before them, and otherwise
the fixed high continuation folds into exhaustion. This is a finite
representation restriction, not a free source observation or an original
cap attainer on removed active tails $H<n\le L_a$. Alternatively, pad the
score to $L_a$ by constant-one suffixes.

If $H>L_a$, extend the kernel by ignoring new coordinates and retaining
its labels through $L_a$. Low first-zero rows remain unchanged for every
later pattern. A new first zero n has $a_n\le\varepsilon$ and law equal
to the old positive-word law $p_+$, with no mass at n. Since
$p_+(0)\ge1-\varepsilon$, all its rows follow from the exact identity

$$
\operatorname{TV}(p_+,(1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n})
 =\max\{1-p_+(0),a_n\}\le\varepsilon.
$$

The positive row stays unchanged. This includes $L_a=0$, every multiple-zero
suffix and $a_n=\varepsilon$. At $H=L_a$ no change is needed. In the
actual realization at $L_a$, every tail $n>L_a$ has exactly this max-tail
error; the same holds after extension for $n>H$. A shorter restricted
comparison is not substituted for that original full-tail realization.

Finally pair all independent demands with the single score and this one
normalized configuration. If its complete cost bound is c, the necessary
original inequality for either N or O is

$$
\sum_{j\le H}\beta_j(a_j-\alpha_j)-K\varepsilon\le c.
$$

It uses no assertion that $(a,\varepsilon)$ belongs to the auxiliary hull.
For A take $c=D_e+\sum_{i=1}^3(\gamma_{(i)}-\rho)_+$; for B,D,E on
their plateaus take their stated early debt; for C take $E+\delta$; for
F take $E+\Phi_k$. In particular A's numerical example yields
$2a_4+(3/2)a_5+a_7\le(a_1+a_2)/2+a_3+a_6+a_8+(27/2)\varepsilon$.
B and D give $\sum\beta_ja_j\le K\varepsilon$; C gives
$a a_4+b a_5+c a_6-\sum\xi_ja_j\le\delta+K\varepsilon$;
E gives $\sum\beta_ja_j\le E_++K\varepsilon$, including
$3(a_5+a_6+a_7)\le a_1+a_8+21\varepsilon$ in its example;
F gives $g(a_n+a_m+a_\ell)-\sum_{i\le k}\xi_i a_i
\le\Phi_k+(3g+R)\varepsilon$.
For $\varepsilon\ge1$ the general inequality follows directly from
$a_j\in[0,1]$ and $K\ge\sum|\beta_j|$. All these inequalities are
necessary only, retaining arbitrary addresses, all Borel events and the
entire actual positive tail; none is a sufficient original cap classification.

### 217.9 Deduplication, source limits and retained boundaries

The common definitions, hull, lower-bound method, Markov/full-allocation
correspondence, CRT source witnesses and 110.2 transport are counted once in
217.1 and 217.8. A is the sharp joint Boolean carrier threshold and signed
zero-terminal plateau; B is the moving consecutive unequal-triple threshold
and lower cut; C is the attained unequal triple with terminal reservoir,
suffix tensor and relocation face; D is arbitrary-position first-zero
ownership and its exact joint share criterion; E is the common-chain
multi-positive capacity cone; F is the equal adjacent-triple piecewise exact
minimum. The equal-profile $k=3$ instance of C is the F triple face, and the
equal-profile zero-cost threshold of B is the F plateau endpoint; those are one relation each.
D's equal-triple core and example overlap A's core and are counted once.
Shared lower bounds, stock identities, hull tests, Markov comparisons, source
transport and the separate zero relation are suppliers rather than separate
relations. The sole-zero core is the owning Continuation VII 202.2 result.
Randomized-expectation terminology is only contextual to Definition 8 of
Kaniewski–Lee–de Wolf, arXiv:1411.7280v1; it supplies no normalized common
budget here.

Every theorem above keeps its own limits. A sufficient constructor condition
is not necessary for arbitrary exact-Q scores. A failed constructor, an
$H_L$ point without $H_N$, a fixed-law obstruction, a separately charged
coordinate optimum, or a score cost gap does not produce the original
separator. A genuine negative result still requires one actual $b\in H_N$, the
same complete feasible $\lambda$ with mass $M\ge1$, an actual unit-O input
with $F_Q(b)>M$, and the original source/full-carrier/common-seed/tail bridge.
The positive obligation remains one unrestricted $V$ and signed residual for
every actual unit-O input. The correspondence and overlap claims are bounded to the named sources and
regions; they grant no universal-completion or literary-priority conclusion.

### 217.10 Comparison sources and finite verification scope

The finite decision comparison uses Blackwell's *Comparison of Experiments*,
sections 2–5: words are states, transcript cells are observations, and numerical
labels are actions. A common stochastic postprocessing kernel is the relevant
joint object. That framework does not itself preserve increasing stopping or
the hard two-request resource. Bernoulli compatibility in
[Embrechts–Hofert–Wang, Theorem 2.2](https://arxiv.org/abs/1606.08212v1)
identifies second moments with the convex hull of Boolean outer products;
when $S>0$, A's $\nu/S$ is one such joint law. The explicit carrier proof
still supplies its protection mass, not independent pair optima.
[Zaev, Problem 1.3 and Theorem 2.1](https://arxiv.org/abs/1404.4962v1)
concern one coupling with prescribed marginals and additional linear
constraints under their stated admissibility conditions. Their duality does
not establish nonemptiness of our stock cone. The finite Farkas tools in
[Kaibel](https://arxiv.org/abs/1001.2161v1) are already part of the owning
199.3–199.4 alternative; they do not supply a new measure here.

[Bertschinger–Rauh, Example 18](https://arxiv.org/abs/1401.3146v1)
gives a boundary to separate attainability: its nonnegative representing
matrix has row sums 2,2,2,0 and fails to be stochastic despite zonotope
containment. It is a method boundary, not an embedded original separator.
[Kaniewski–Lee–de Wolf, Definition 8 and Theorem 9](https://arxiv.org/abs/1411.7280v1)
characterize scalar nonnegative expectation query complexity by nonnegative
literal degree; that scalar representation does not provide our normalized
probability-vector kernel, common schedule masses or stopped catalog.
[Chen, Theorem 3, Definition 7 and Corollary 3](https://arxiv.org/abs/2502.06530v1)
require binary decomposability for their finite-action extension. No such
decomposition preserving this acquisition budget is established.
The ordered-measure min-closure hypotheses of
[Yang–Yang, Theorem 1](https://arxiv.org/abs/2603.11448v1), and the
past-conditional measurability condition with prescribed marginals of
[Backhoff et al., Definition 2.1](https://arxiv.org/abs/1606.04062v1),
also lack a proved hard-two acquisition correspondence here. These references
locate usable structures and limits; none supplies the unresolved universal
implication or a worldwide-priority conclusion.

The independent rational program `check_printed.py` and its result data
`results.json` belong to the private experiment directory
`/Users/auricstudio/trureturing-experiments/repair217`.
Its score reconstructions read the printed word/mass tables, example
coefficients and relocation maps, then maximize over all output labels and
all empty, singleton and pair cells. Parameter checks include signed class
ownership, complete positive support, ranked share bounds, stock branches,
zero coefficients, terminal exhaustion, unequal and nonadjacent examples.
Probability checks keep the base, correct, independent pair and positive
rows, multiple-zero words, repeated and ignored request accounting, the
normalized common laws and exact tail endpoints. Arithmetic checks evaluate
actual CRT representatives in the Fibonacci windows. Finite exact evaluations
can corroborate or refute transcription and examples; the all-real-parameter,
all-address and all-sequence assertions depend on the ordinary proofs and the
owning suppliers, not extrapolation from these checks.

### 217.11 Remaining original obligation

For every full $y\ge0$ with $\Delta_O(y)\le1$, one still needs a single
unrestricted $V\ge0$ and $\theta\in[0,1]$ satisfying (217.1), or one genuine
same-realization separator with the full $b,\lambda,y$ evidence. The
finite relations above establish no universal implication from
$\Delta_O(y)\le1$ to their capacity cones. Outside their union, general
unequal and nonadjacent profiles, four or more unrestricted positives,
profiles beginning at 3, concentrated low stock, arbitrary signed residuals
and general low-terminal coupling remain open. The original all-sequence positive-closed-cap hard-two
comparison is therefore unresolved.

## 追加锚（本行以下为增补区）
