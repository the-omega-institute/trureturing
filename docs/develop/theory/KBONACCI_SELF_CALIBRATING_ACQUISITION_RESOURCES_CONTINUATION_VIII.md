# k-bonacci 自校准获取资源续卷 VIII：共同评分预算、早期正确信用与精确迁移

This volume continues the numbering of
[Continuation VII](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md).
It uses ordinary mathematical definitions and proofs. Existing statements
remain in their owning volumes. Throughout, $x_+=\max\{x,0\}$; empty sums
and maxima of empty families of nonnegative weights are zero. Closed
inequalities include equality and zero coefficients.

## 206. Pairwise moments, exact chain minima and dense early-credit certificates

The objects here are full event scores. The five groups concern moment
support reduction, exact chain optimization, balanced dense scores,
clipping, and stock exchange. Their sufficient regions can overlap.
All supports maximize over every terminal label, including labels at
unqueried or earlier addresses. A score coefficient is a proof weight;
it is not an acquisition probability or a probability law on sources.

**Definition 206.1 (Original source and the unchanged comparison).**
Use the source of [Definition 110.1 and Theorem
110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source):

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
       \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad F_0=0,\quad F_1=1,\quad
F_{r+2}=F_{r+1}+F_r,\\
q_i(x)&=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\},
\end{aligned}
\tag{206.1}
$$

where $p_1<p_2<\cdots$ are the primes. Replies are static. Every finite
Boolean pattern, including every multiple-zero pattern, has an actual
source witness, as supplied by Boundaries, Theorem 35.2. The original
carrier is the full disjoint union of Borel blocks
$\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, each a copy of
$(0,1)$. Its measurable distinct marks are
$\theta_j=(B_1,1/(j+2))$, $j\ge0$. The consumer and its original
nonatomic targets remain those of Acquisition Resources, Definition
73.1. For every sequence

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_j\longrightarrow0,
\qquad
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                +a_{n(x)}\delta_{\theta_{n(x)}},
\tag{206.2}
$$

these are separately selected marked laws, not replacements for the
consumer's original targets.

The classes $\mathcal N_2,\mathcal O_2$ have exactly the meaning of
Acquisition Resources, Definition 90.1: zero advice, one
source-independent common seed, actual sourcewise almost-sure finite
handoff, arbitrary query addresses and outputs anywhere in the full
carrier. The hard budget is at most two actual requests, including
repeated requests and requests whose replies are ignored. $N$ preselects
its whole schedule before replies and obtains its scheduled replies.
$O$ preselects an increasing schedule and stops at its first queried
zero or at exhaustion. There is no adaptive choice of the second
address. Error is the supremum of TV over every actual source and every
Borel event; no distribution on sources, address bound, runtime bound,
mean-request budget, extra observation or second seed is introduced.

For $0<\varepsilon\le1$, let
$L_a=\max(\{j:a_j>\varepsilon\}\cup\{0\})$. The finite cap constraints
for a probability-vector kernel are, for every low word with first zero
$n\le L_a$,

$$
p_w(0)\ge1-a_n-\varepsilon,\qquad
p_w(n)\ge a_n-\varepsilon,\qquad
p_w(0)+p_w(n)\ge1-\varepsilon,
\qquad p_{1^{L_a}}(0)\ge1-\varepsilon.
\tag{206.3}
$$

The pair row is independent of both singleton rows. Negative singleton
right sides are retained. Write $\mathscr N_{L_a}$ for the convex hull
of complete finite $N$ tables, and $\mathscr C_{L_a}$ for the finite
stopped kernels characterized by 109.1. Then $\mathcal F_N(a,\varepsilon)$
is the subset of $\mathscr N_{L_a}$ satisfying (206.3). The universal
question remains whether its nonemptiness always implies
$\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing$.
Theorem 110.2 owns the equivalence with original closed-cap feasibility;
its use for actual probability configurations is specified in 206.24.

**Definition 206.2 (Complete scores, catalogs and fixed data).**
Fix an integer $L\ge3$, independently of the actual active length until
an original-source application is made. Put

$$
\Omega=\{0,1\}^L\setminus\{1^L\},\qquad
n(w)=\min\{j:w_j=0\},\qquad \Omega_j=\{w:n(w)=j\}.
$$

A full score $V$ has separate nonnegative coefficients $A_w,C_w,P_w$
for every $w\in\Omega$, and $T\ge0$ at $1^L$. Label
$\ell\in\{0,\ldots,L\}$ earns

$$
g_V(w,\ell)=
\begin{cases}
 A_w\mathbf1_{\ell=0}+C_w\mathbf1_{\ell=n(w)}
       +P_w\mathbf1_{\ell\in\{0,n(w)\}},&w\ne1^L,\\
 T\mathbf1_{\ell=0},&w=1^L.
\end{cases}
\tag{206.4}
$$

For a fixed schedule, sum $g_V(w,\ell)$ over each of its cells, maximize
over all labels separately in each cell, then sum these maxima.
$B_N(V)$ is the largest such sum over the empty schedule, every single
address, and every distinct pair $i<j$ with four cells $00,01,10,11$.
$B_O(V)$ uses empty and single schedules and the increasing pairs with
stopped cells $0,10,11$. The notation $(i,j;\ell_0,\ell_{10},\ell_{11})$
specifies the three labels of an $O$ table.

The anchor is $R=(1,2;1,2,0)$, represented in $N$ by label $1$ on both
first-zero cells. Its reward and the complete excess are

$$
W_V=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,
\qquad \Delta_C(V)=B_C(V)-W_V\ge0\quad(C=N,O).
\tag{206.5}
$$

These are the objects of 199.1–199.2, with quotient

$$
Q(V)=(\beta,K),\qquad
\beta_j=\sum_{w\in\Omega_j}(C_w-A_w),\qquad
K=\sum_w(A_w+C_w+P_w)+T.
\tag{206.6}
$$

Except in the moment result, an input $y$ has $A=0$, arbitrary correct
rows, and pair rows supported in $\Omega_1\cup\Omega_2$. Set

$$
\gamma_j=\sum_{w\in\Omega_j}C_w,\quad
E=\gamma_1+\gamma_2,\quad G=\sum_{j=3}^L\gamma_j,\quad
\mu=\max_{j\ge3}\gamma_j,\quad S=\sum_wP_w,\quad t=T,
\quad W=E+S+t,
\tag{206.7}
$$

so $Q(y)=(\gamma,G+W)$; write $\delta=\Delta_O(y)$.
All these totals are nonnegative. Fixing them does not fix the
placement of correct rows or the early allocation of pair rows.

An empty or singleton $N$ output function is a function of a distinct
pair, with extra replies ignored. Reversing a static pair only permutes
its cells; repeating an address supplies singleton information.
Consequently a bound on all distinct $N$ pairs bounds the complete
catalog. This information representation does not exempt ignored or
repeated actual requests from the original count. Every $O$ output
function is an $N$ function, so $B_O\le B_N$.

**Definition 206.3 (The reused signed hull and certificate rule).**
Let $\alpha=(1,1,0,\ldots,0;0)$ and use the auxiliary polytope of
[198.5](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md):

$$
H_L=\left\{(b,e):\begin{array}{l}
1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
(L+1)e\le\sum_{j=3}^Lb_j,\quad
b_1+\sum_{j=3}^Lb_j-(L+1)e\le1
\end{array}\right\}.
\tag{206.8}
$$

For signed $q=(\beta,K)$ set
$F_q(b,e)=\sum_j\beta_j(b_j-\alpha_j)-Ke$ and
$\sigma_H(q)=\max_{(b,e)\in H_L}F_q(b,e)$. Its complete vertex set is

$$
\begin{aligned}
o&=(0,\ldots,0;0),&p&=(1,0,\ldots,0;0),\\
u_k&=(\underbrace{1/(k-1),\ldots,1/(k-1)}_k,0,\ldots,0;0),\\
v_k&=(\underbrace{1,\ldots,1}_k,e_k,\ldots,e_k;e_k),&
e_k&=(k-2)/(k+1),\qquad3\le k\le L.
\end{aligned}
\tag{206.9}
$$

The hull assertion and its proof remain in 198.5. In its difference
coordinates $x_i=b_i-b_{i+1}$, $b_{L+1}=e$, the conditions are
$x_2=0$, $x_1,x_3,\ldots,x_L,e\ge0$,
$\sum_{k\ge3}(k-2)x_k\ge3e$ and
$x_1+\sum_{k\ge3}(k-1)x_k-2e\le1$.
The normalized rays $(x_k,e)=(1,0),(1,(k-2)/3)$ and the $x_1$ ray
give precisely (206.9). Thus the same hull applies to signed
residuals without a positivity assumption on their coordinates.

For a comparison score with early correct totals $c_1,c_2$, late
correct totals $\eta_j$, no base rows, early pair support, and anchor
$W'$, write

$$
a=\gamma_1-c_1,\qquad b=\gamma_2-c_2,\qquad
R_k=\sum_{j=3}^k(\gamma_j-\eta_j).
$$

Here $a,b$ in the residual formula are scalar differences, whereas the
argument of $F$ in (206.8) is the vector $(b_1,\ldots,b_L;e)$.
Since $K_y-K_V=R_L+W-W'$, substitution at the four types of vertices
gives the exact formula

$$
\sigma_H(Q(y)-Q(V))=
\max\left\{-a-b,-b,
 \max_{3\le k\le L}\frac{R_k-(k-2)(a+b)}{k-1},
 \max_{3\le k\le L}\frac{3R_k+(k-2)(W'-W)}{k+1}\right\}.
\tag{206.10}
$$

Indeed at $v_k$ the early coordinates are one, the suffix late
coordinates equal $e_k$, and the late contribution is
$R_k+e_k(R_L-R_k)-e_k(R_L+W-W')$.
This yields the last column and shows exactly where the early terms
cancel. Both $u_k$ and $v_k$ columns are retained unless their dominance
is proved under the hypotheses of a particular application.

For completeness of the certificate notation, $d(b,e)$ has the three
rows $1-b_n-e,b_n-e,1-e$ at every $w\in\Omega_n$ and row $1-e$ at
$1^L$. Let $z_D$ be the complete event indicator vector of table $D$,
$r=z_R=d(\alpha)$, $h(b,e)=d(b,e)-r$, and let $G_C$ have all columns
$z_D-r$. No row is removed when its score coefficient is zero. Use
199.2's set

$$
E_N=\{q:\exists V\ge0,\ \exists\theta\in[0,1],\
       \Delta_N(V)+\theta\le1,\
       \sigma_H(q-Q(V))\le\theta\}.
\tag{206.11}
$$

Its weak-duality application, reused from 199.3–199.4, is the following.
For the same complete attained vector $\lambda\ge0$ with
$G_N\lambda\ge h(b,e)$ and $M=\sum_D\lambda_D$, a certificate gives

$$
\begin{aligned}
F_q(b,e)&\le V\cdot h(b,e)+\theta
 \le V\cdot G_N\lambda+\theta\\
 &\le M\Delta_N(V)+\theta\le\max\{1,M\}.
\end{aligned}
\tag{206.12}
$$

If $M\le1$, use $M\Delta_N\le\Delta_N$; if $M\ge1$, use
$\theta\le M\theta$. This covers $M=0,1$, $\theta=0,1$ and nonzero
zero-excess scores at $\theta=1$. It uses one assembled score and one
residual, without requiring $V\le y$ or assigning separate budgets to
its components. Auxiliary $e=0$ vertices do not represent original
positive tails.

**Definition 206.4 (Fair placement and its full cell rewards).**
Given nonnegative $c_1,c_2,p_1,p_2,\eta_3,\ldots,\eta_L,\tau$, define
$\mathcal V(c,p,\eta,\tau)$ as follows. For every suffix
$v\in\{0,1\}^{L-2}$ place

$$
C_{01v}=c_1/2^{L-2},\quad P_{01v}=p_1/2^{L-2},\qquad
C_{10v}=c_2/2^{L-2},\quad P_{10v}=p_2/2^{L-2}.
\tag{206.13}
$$

For each $j\ge3$ and $v\in\{0,1\}^{L-j}$ place
$C_{1^{j-1}0v}=\eta_j/2^{L-j}$. Set $T=\tau$; every other coefficient,
including every $A$, is zero. Put $f_a=c_a+p_a$,
$S'=p_1+p_2$ and $\mu_\eta=\max_j\eta_j$.
The anchor is $c_1+c_2+S'+\tau$.

The following full cell calculation will be used inside the proofs.
For $(1,2)$ the $N$ maxima in order $00,01,10,11$ are

$$
(0,f_1,f_2,\max(\mu_\eta,\tau)),
\tag{206.14}
$$

and the $O$ maxima are $f_1,f_2,\max(\mu_\eta,\tau)$.
For an early/late pair $(a,j)$, let $b$ be the other early index and
$H_j=\max_{3\le n<j}\eta_n$, $U_j=\max_{n>j}\eta_n$. Then the $N$
maxima are $(f_a/2,f_a/2,X,Y)$ and the $O$ maxima are $(f_a,X,Y)$, where

$$
X=\max(f_b/2,H_j/2,\eta_j),\qquad
Y=\max(p_b/2+\tau,f_b/2,H_j/2,U_j).
\tag{206.15}
$$

For $3\le i<j$, let $H_i=\max_{3\le n<i}\eta_n$,
$I_{ij}=\max_{i<n<j}\eta_n$ and $U_j=\max_{n>j}\eta_n$.
The $N$ maxima are $(A_{ij},A_{ij},B_{ij},C_{ij})$ and the $O$ maxima
are $(2A_{ij},B_{ij},C_{ij})$, with

$$
\begin{aligned}
A_{ij}&=\max(S'/4,f_1/4,f_2/4,H_i/4,\eta_i/2),\\
B_{ij}&=\max(S'/4,f_1/4,f_2/4,H_i/4,I_{ij}/2,\eta_j),\\
C_{ij}&=\max(S'/4+\tau,f_1/4,f_2/4,H_i/4,I_{ij}/2,U_j).
\end{aligned}
\tag{206.16}
$$

To derive these expressions, an early suffix is fair at each late bit.
A correct class before both late queries puts one quarter in each
cell. Class $i$ puts half in $00$ and half in $01$; a class strictly
between $i,j$ puts half in $10$ and half in $11$; class $j$ puts all
its weight in $10$; later classes put all their weight in $11$.
Label zero receives the sum of pair weights and receives $\tau$ only
in $11$. Each early numerical label receives its own $C+P$, and each
late numerical label its own $C$. This lists every label, not just the
queried ones. In the first two $N$ cells the entire reward vectors
have the same proportions, so their maxima add to the merged $O$
maximum. For $(1,2)$ the empty $00$ cell gives the same conclusion.
This is precisely the common-suffix specialization of 198.2, not an
assumption about the source distribution. It also bounds every shorter
schedule by Definition 206.2.

**Proposition 206.5 (The pairwise-cylinder moment application).**
For any full nonnegative score, independently for each event type
$R\in\{A,C,P\}$ and each actual first-zero class $n$, its suffix
measure can be replaced by a nonnegative measure supported on at most

$$
D_{L-n}=1+(L-n)+\binom{L-n}{2}
\tag{206.17}
$$

words from its original support. Keep $T$ unchanged. The replacement
preserves every individual schedule-cell-label reward in both catalogs,
hence $B_N,B_O,W,Q,\Delta_N,\Delta_O$. Thus at most

$$
3\sum_{d=0}^{L-1}\left(1+d+\binom d2\right)+1
 =\frac{L^3+5L}{2}+1
\tag{206.18}
$$

nonzero event-row atoms suffice. This is an upper bound; it does not
assert minimal support, boundedly many active labels, or sparsity of
an acquisition law.

**Proof.** On a fixed $(R,n)$ write $w=1^{n-1}0x$ with $d=L-n$ and use
$\Phi_d(x)=(1,x_i,x_ix_j\ (i<j))\in\mathbb R^{D_d}$.
If the positive support of $\sum_xm_x\delta_x$ has more than $D_d$
points, choose a nonzero dependence $\sum_xa_x\Phi_d(x)=0$ on that
support. Its constant coordinate gives $\sum_xa_x=0$, so the
coefficients have both signs. Let
$\lambda=\min_{a_x>0}m_x/a_x>0$ and replace $m_x$ by
$m_x-\lambda a_x$. All coefficients stay nonnegative, at least one
vanishes, no new point is introduced, and the whole moment vector is
unchanged. Repeat until at most $D_d$ points remain. Zero measures
need no elimination; for $d=0$ there is just one possible suffix.
This is the finite conic Carathéodory/Tchakaloff argument applied to
these Boolean features; see Bayer–Teichmann as cited in 206.23.

Within a fixed first-zero class, the indicator of any $N$ cell is a
product of at most two factors $x_i$ or $1-x_i$ after substituting the
fixed prefix. Empty and single cells have lower degree. An $O$ cell
has indicator $1-w_i$, $w_i(1-w_j)$ or $w_iw_j$, and its restriction
has the same degree bound. Repeated coordinates reduce by $x_i^2=x_i$.
Every such indicator is therefore a multilinear polynomial of degree
at most two. Its integral is preserved by the elimination.

For a fixed cell and label, the event contribution is this integral
times, respectively, $\mathbf1_{\ell=0}$, $\mathbf1_{\ell=n}$ or
$\mathbf1_{\ell\in\{0,n\}}$. First-zero classes and event types are
never mixed. Summing them and the unchanged positive-word contribution
preserves the label reward before any maximum. It follows that all
cell maxima, schedule supports and both $B$ values agree. Constant
moments preserve every row total, so (206.5)–(206.6) preserve $W,Q$
and both excesses. Finally
$\sum_{d=0}^{L-1}D_d=L+\binom L2+\binom L3=(L^3+5L)/6$,
which proves (206.18).

Applying the reduction separately to an input and a certificate leaves
the same residual and the same budget. In a full separator
$(b,y,\lambda)$, leave the attained full-row $\lambda$, $b$ and the
matrix unchanged; $Q(y)$ and $\Delta_O(y)$ stay identical.
Consequently this moment application reduces representation without
establishing any new cap-feasible region. $\square$

**Proposition 206.6 (Pair moments cannot be replaced by single moments).**
At $L=4$, the correct measure $C_{0v}=1/8$ on all eight suffixes has
the same degree-two moments as

$$
C_{0000}=C_{0011}=C_{0101}=C_{0110}=1/4.
$$

All other rows, including $T$, are zero. These measures give identical
cell-label rewards but different third moments. In contrast, consider
the following two full scores, all unspecified rows being zero:

$$
\begin{aligned}
&C_{1101}=C_{1110}=1,\qquad T=1,\qquad A=0,\\
\text{I: }&P_{0100}=P_{1000}=P_{0101}=P_{1001}=P_{0110}=P_{1010}=1/8,\\
\text{II: }&P_{0100}=P_{1000}=1/4,\qquad P_{0111}=P_{1011}=1/8.
\end{aligned}
\tag{206.19}
$$

Their separate class/event totals and single-bit moments agree, but

$$
\begin{array}{c|cc|cc}
 &B_N&B_O&\Delta_N&\Delta_O\\ \hline
\mathrm I&13/4&3&3/2&5/4\\
\mathrm {II}&15/4&13/4&2&3/2
\end{array}
\tag{206.20}
$$

**Proof.** In the first example both suffix measures have total one,
each coordinate moment $1/2$ and each pair moment $1/4$. Their cubic
moments are $1/8$ and zero. Proposition 206.5's cell argument applies.
For (206.19), $S=3/4$, $W=7/4$, and both late zero marginals are
$m_3=m_4=1/2$. The directed pair mass
$\nu(w_3=1,w_4=0)$ is $1/4$ in I and zero in II. For $(3,4)$ the
$N$ maxima are $(1/4,1,1,1)$ and $(1/2,1,1,5/4)$; labels
$(0,3,4,0)$ attain them. The stopped maxima are $(1,1,1)$ and
$(1,1,5/4)$. In both scores an empty schedule or early single has
support $7/4$, a late single has $9/4$, $(1,2)$ has $7/4$, and any
early/late pair has $5/2$ in either catalog. These exhaust the
schedules and establish (206.20). The unequal pair moment therefore
changes complete support despite equality of all one-bit data.
No optimality of the cubic upper bound follows. $\square$

**Theorem 206.7 (Optimized absorbing-chain support).**
Fix all nonnegative data $\gamma_1,\ldots,\gamma_L,S,t$ of (206.7).
Let $M_r$ be the sum of the $r$ largest late totals, padded with zeros
if fewer than $r$ late coordinates exist. Thus $M_1=\mu$. Define

$$
\begin{aligned}
q&=\max\{\mu,M_2-t\},\\
c_0&=\min\{(E+S)/2,\ S+\min(\gamma_1,\gamma_2)\},\\
d_0&=\max\{0,\mu-t,M_2-E-S,M_3-W,q-c_0\},\\
s_1&=\min\{S,\max\{0,(\gamma_2+S-\gamma_1)/2\}\},
\qquad s_2=S-s_1.
\end{aligned}
\tag{206.21}
$$

On $v_j^{\rm ch}=1^{j-1}0^{L-j+1}$ put $C=\gamma_j$.
Put $P=s_1$ at $v_1^{\rm ch}$, $P=s_2$ at $v_2^{\rm ch}$ and $T=t$,
with every other row zero. This score $V^{\rm ch}$ preserves $Q,W$
and has the exact complete excess

$$
\Delta_N(V^{\rm ch})=\Delta_O(V^{\rm ch})
 =D=\max\{d_0,q-E\}.
\tag{206.22}
$$

Every input in the stipulated $A=0$, early-pair family with these
fixed data has $\Delta_O\ge d_0$, and hence $\Delta_N\ge d_0$.

**Proof.** Put $X_a=\gamma_a+s_a$ and
$r_0=\max\{S,X_1,X_2\}$. For any nonnegative split of $S$,
$\min(X_1,X_2)\le(E+S)/2$; also the smaller early total can increase
by at most $S$, so this minimum is at most
$S+\min(\gamma_1,\gamma_2)$. The clamped split in (206.21) attains
the smaller of these bounds. Since $X_1+X_2=E+S$,

$$
E+S-r_0=\min\{E,X_1,X_2\}=\min\{E,c_0\}=:c.
\tag{206.23}
$$

A chain word gives only $00,10,11$ at $i<j$; its $01$ cell is empty.
For $i\ge2$, the three exact maxima are

$$
\max\{r_0,\max_{3\le n\le i}\gamma_n\},\qquad
\max_{i<n\le j}\gamma_n,\qquad
\max\{t,\max_{n>j}\gamma_n\}.
\tag{206.24}
$$

For $i=1$ they are
$X_1$, $\max\{X_2,\max_{3\le n\le j}\gamma_n\}$ and
$\max\{t,\max_{n>j}\gamma_n\}$. Label zero, both early labels,
and all late labels are included. These are also the stopped maxima.

Their maximum over the catalog is exactly

$$
B=\max\{W,E+S+\mu,r_0+M_2,r_0+\mu+t,M_3,M_2+t\}.
\tag{206.25}
$$

For the upper bound when $i\ge2$, an early or zero label in the first
cell contributes at most $r_0$, followed by at most two distinct late
labels or one late label and $t$. A late first-cell label permits at
most three late labels or two late labels and $t$. If $i=1$ and the
second cell chooses label $2$, the two early rewards total $E+S$,
and the final cell is at most $\max(\mu,t)$. Otherwise the same
$r_0$ bounds apply. This proves the upper bound for pairs and hence
for shorter schedules.

For attainment, $R$ supplies $W$, and
$(1,2;1,2,j_*)$ with $\gamma_{j_*}=\mu$ supplies $E+S+\mu$.
For two largest late classes at addresses $a<b$, the table
$(2,a;\ell_0,a,b)$ supplies $r_0+M_2$, where
$\ell_0\in\{0,1,2\}$ maximizes $r_0$. The table
$(2,j_*;\ell_0,j_*,0)$ supplies $r_0+\mu+t$.
The first two of three ordered largest late addresses, with the third
as exhaustion label, collect $M_3$. Querying two largest late
addresses and using exhaustion label zero collects $M_2+t$.
If there is only one late coordinate, the padded terms $r_0+M_2$
and $M_2+t$ are dominated by $r_0+\mu+t$, and $M_3$ by
$E+S+\mu$. If there are two, $M_3=M_2\le r_0+M_2$.
Thus no padded nonexistent address is queried. Ties, zero weights,
$S=0$ and $\mu=0$ cause no exception. Subtracting $W$ gives

$$
\begin{aligned}
B-W
 &=\max\{0,\mu-t,M_2-t-c,\mu-c,M_3-W,M_2-E-S\}\\
 &=\max\{d_0,q-E\},
\end{aligned}
$$

using (206.23).

For an arbitrary competitor with these same data, let its actual early
pair totals be $p_a$, and put $Y_a=\gamma_a+p_a$.
For each $a=1,2$, the legal stopped table $(a,j_*;a,j_*,0)$ collects
at least $Y_a+\mu+t$. With two distinct largest late addresses
$i<j$, the table $(a,i;a,i,j)$ collects at least $Y_a+M_2$.
Subtracting $W=Y_1+Y_2+t$ and maximizing over $a$ proves

$$
\Delta_O\ge q-\min(Y_1,Y_2)\ge q-c_0.
$$

With one late coordinate $q=\mu$ and the first collection suffices.
Changing only $R$'s final output gives $\Delta_O\ge\mu-t$.
Collecting two largest late labels and zero gives
$\Delta_O\ge M_2-E-S$; for one late coordinate the singleton table
with outputs $j,0$ gives that padded bound. Three late labels give
$\Delta_O\ge M_3-W$; with fewer labels a shorter collecting table
supplies the padded bound, or it is dominated by the preceding ones.
The anchor gives zero. All these bounds apply to the same competitor,
so their maximum is $d_0$. The inclusion of stopped functions in $N$
proves the $N$ lower bound as well. $\square$

**Corollary 206.8 (Restricted fixed-data minima and existing membership).**
If $q-E\le d_0$, both fixed-data minima in the family of 206.7 equal
$d_0$ and are attained by $V^{\rm ch}$. In particular this condition
holds when $E\ge\min(S,\mu)$. If the input has $\delta\le1$, either
this last condition or $q\le E+1$ gives $D\le1$ and the certificate
$(V^{\rm ch},0)$. Thus any remaining nonmember in the unit-input
family must satisfy both $E<\min(S,\mu)$ and $q>E+1$.
These are necessary exclusions, not a separator.

**Proof.** The lower bound and matching value in 206.7 prove the
minimum assertion. If $E\ge S$, then $c_0\le(E+S)/2\le E$, so
$q-E\le q-c_0\le d_0$. If $E\ge\mu$, use $M_2\le2\mu$ to get
$q-E\le\max(0,\mu-t)\le d_0$. These two cases exhaust
$E\ge\min(S,\mu)$. Also $d_0\le\delta$, so the asserted unit
conditions give (206.22) at most one.

This unit region already has an existing zero-score certificate.
Indeed $D\le1$ implies $\mu-E\le q-E\le1$. At $u_k$,

$$
F_{Q(y)}(u_k)=
 \frac{\sum_{j=3}^k\gamma_j-(k-2)E}{k-1}
 \le\frac{k-2}{k-1}(\mu-E)\le1.
\tag{206.26}
$$

The $o,p$ values are $-E,-\gamma_2\le0$. The complete subset-table
law in [200.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md)
already gives $F_{Q(y)}(v_k)\le\delta\le1$. That law selects three
labels from $\{1,\ldots,k,\infty\}$, queries the first two numerical
labels and interprets $\infty$ as output zero; it is a full stopped
law with every event row retained. Hence the reused hull gives
$(V=0,\theta=1)$. The contribution of 206.7 is its attained exact-$Q$
optimization and restricted minima, not additional unit-region
membership. No global minimum is asserted outside $q-E\le d_0$.
$\square$

**Proposition 206.9 (Chain relocation and its limitation).**
For every $L\ge6$ and $\mu>2$, take
$\gamma_1=\gamma_2=\mu/2$, all late $\gamma_j=\mu$,
$S=\mu$, $t=\mu-1$. Put $P=\mu/2$ at each of
$v_1^{\rm ch},v_2^{\rm ch}$. A complete choice of correct rows is

$$
\begin{aligned}
C_{0111011^{L-6}}&=\mu/2,&C_{v_2^{\rm ch}}&=\mu/2,\\
C_{1101101^{L-6}}&=\mu,&C_{1110111^{L-6}}&=\mu,\\
C_{w(\{j\})}&=\mu&& (5\le j\le L),
\end{aligned}
\tag{206.27}
$$

where $w(Z)$ is the length-$L$ word with zero set exactly $Z$.
All unspecified rows are zero, and $T=\mu-1$. It has
$\Delta_O=1$, $\Delta_N=\mu+1$, whereas the chain representative
has both excesses one and the same $Q,W$.

**Proof.** Each numerical label has reward at most $\mu$ in a cell:
early labels have total $C+P=\mu$, and each late class has total
$\mu$. The $11$ cell of any pair has no chain pair weight, so its
zero reward is $\mu-1$; other zero rewards are at most $S=\mu$.
Thus every $N$ pair has support at most $4\mu$ and every $O$ pair at
most $3\mu$. For a singleton, its zero cell has every reward at most
$\mu$, and its positive cell has every reward at most
$\max(\mu,S+t)=2\mu-1$; its support is therefore less than $3\mu$.
The empty schedule is bounded by $2\mu-1$ as well.
The $N$ labels $(0,5,3,4)$ at $(5,6)$ attain four rewards $\mu$,
and $(1,2;1,2,3)$ attains $3\mu$ in $O$. Since $W=3\mu-1$, the
claimed excesses follow. The same calculation permits moving the
class-two correct row to its sole-zero word, including the instance
$L=6,\mu=3$ with $C_{101111}=3/2$.
For the representative, $c_0=\mu$, $q=\mu+1$ and $d_0=D=1$ in
206.7. In fact its quotient already has readings
$-\mu,-\mu/2,0,(k-2)/(k+1)$ at $o,p,u_k,v_k$, respectively, so
zero score with $\theta=(L-2)/(L+1)$ certifies it.

Unconditional chain relocation fails on the example owned by 198.6:
$L=4$, $P_{0101}=P_{1010}=C_{1101}=C_{1110}=1$, with all other
rows and $T$ zero. Append ones for larger $L$. Its supports are three
and $W=2$. To collect all four rows a table must query address one
to distinguish $0101$ from $1101$, and address two to distinguish
$1010$ from $1110$. The two correct words then share transcript $11$
and have different rewarded labels, so four cannot be collected.
A stopped table collects three. Its optimized chain has
$E=t=0,S=2,M_2=2,c_0=1,q=2,d_0=1,D=2$, attained by
$(2,3;0,3,4)$. This is the existing limitation of a method, consistent
with the restricted minimum hypothesis, not a failure of $E_N$.
$\square$

**Theorem 206.10 (Balanced dense early-credit support).**
Choose arbitrary $\eta_j\ge0$ for $3\le j\le L$, and write
$\mu=\max_j\eta_j$ within this theorem. Let

$$
0\le c_1,c_2\le\mu,\qquad W'\ge2\mu,\qquad
p_a=\mu-c_a,\qquad \tau=W'-2\mu.
\tag{206.28}
$$

The score $V=\mathcal V(c,p,\eta,\tau)$ has anchor $W'$, quotient
$((c_1,c_2,\eta),\sum_j\eta_j+W')$, and exact excess

$$
\Delta_N(V)=\Delta_O(V)=D
 =\max\left\{0,3\mu-W',\frac{\mu-\min(c_1,c_2)}2\right\}.
\tag{206.29}
$$

**Proof.** Both early totals $f_a=c_a+p_a$ equal $\mu$.
The $(1,2)$ support is $2\mu+\max(\mu,\tau)$, with excess
$(\mu-\tau)_+$. For $(a,j)$, (206.15) bounds the stopped maxima
by $\mu,\mu,\max(\mu,p_b/2+\tau)$. Its excess is therefore at
most $\max(\mu-\tau,p_b/2)$.
For a late pair, $S'=p_1+p_2\le2\mu$; (206.16) bounds the first
two stopped maxima by $\mu,\mu$, and the last by
$\max(\mu,S'/4+\tau)$. The excess is at most
$\max(\mu-\tau,S'/4)$, and
$S'/4\le\max(p_1,p_2)/2$.
The complete cell equalities in 206.4 transfer these bounds to $N$;
the pair embedding covers all shorter functions.

The anchor attains zero. For any $j_*$ with $\eta_{j_*}=\mu$,
$(a,j_*;a,j_*,0)$ collects
$\mu+\mu+p_b/2+\tau$, giving excess $p_b/2$.
Together with $(1,2)$ these attain every term of (206.29).
At $\mu=0$, all $c,p,\eta$ vanish and the anchor collects $T=W'$,
so the excess is zero without division. All equalities and zero
coefficients in (206.28) are included. $\square$

**Corollary 206.11 (Signed completion and the exact family optimum).**
For any input (206.7) and any score from 206.10, compute all four
columns of (206.10), and let $\theta=\max(0,\sigma_H(Q(y)-Q(V)))$.
The single inequality $D+\theta\le1$ certifies $Q(y)\in E_N$.
The differences $a,b,R_k,W'-W$ may have either sign.

If $\eta=\gamma$ and $W'=W\ge2\mu$, zero residual budget is
possible exactly when

$$
c_1+c_2\le E,\qquad c_2\le\gamma_2.
\tag{206.30}
$$

The largest feasible $\min(c_1,c_2)$ is

$$
r_* =\min\{\mu,E/2,\gamma_2\},
\qquad c_1=c_2=r_*,
\tag{206.31}
$$

and the minimum cost within this fair family under zero residual
budget is $\max\{0,3\mu-W,(\mu-r_*)/2\}$.
For $\mu>2$, a data-only sufficient region is

$$
W\ge3\mu-1,\qquad E\ge2(\mu-2),\qquad\gamma_2\ge\mu-2.
\tag{206.32}
$$

If a unit-$O$ input has three distinct late classes of total $\mu$,
the first inequality in (206.32) is automatic.

**Proof.** The signed certificate is (206.11)–(206.12).
With the retained late profile and anchor, the $o,p$ residual readings
force (206.30). Conversely its value at any point of $H_L$ is

$$
-(E-c_1-c_2)(1-b_1)-(\gamma_2-c_2)(b_1-b_2)\le0,
$$

so those two conditions suffice. If $r=\min(c_1,c_2)$, they imply
$r\le\mu$, $2r\le E$ and $r\le\gamma_2$; (206.31) attains all
of them. Substitution in (206.29) proves the family minimum.
No condition $c_1\le\gamma_1$ is needed: signed domination is not
rowwise subtraction. The second early coordinate is essential;
swapping early labels would change the $p$ reading.
Under (206.32), $r_*\ge\mu-2$ and $D\le1$.
For three maximum late labels, query the earliest two and guess the
third on exhaustion. Every word in those classes is collected
regardless of its later zeros, so $W+\delta\ge3\mu$.
This proves the final assertion. The exact formulas continue to apply
for $\mu\le2$ whenever their displayed hypotheses hold; the optimum
is only within the specified family, not over all scores. $\square$

**Corollary 206.12 (Balanced completion with an explicit residual charge).**
For an input (206.7), choose $0\le d\le\min(\mu,1)$ and set

$$
h=(\mu-2d)_+,\qquad s=\mu-h=\min(\mu,2d),\qquad
c_1=c_2=h,\quad p_1=p_2=s,\quad
\eta=\gamma,\quad \tau=\mu-d,\quad W'=3\mu-d.
\tag{206.33}
$$

The balanced score has exact cost $d$, and its exact nonnegative
residual charge is

$$
\Theta=\max\left\{0,2h-E,h-\gamma_2,
             \frac{L-2}{L+1}(3\mu-d-W)\right\}.
\tag{206.34}
$$

Thus $d+\Theta\le1$ suffices. If $\mu\ge1$, $\delta\le1$, three
late totals attain $\mu$, and
$E\ge2(\mu-2)_+$, $\gamma_2\ge(\mu-2)_+$, take $d=1$.
This is a corollary of the balanced construction, not another
independent family gain.

**Proof.** The tail is nonnegative because $d\le\mu$, and
$W'\ge2\mu$. Formula (206.29) gives $D=\max(d,s/2)=d$.
With $R_k=0$, the residual readings are

$$
2h-E,\quad h-\gamma_2,\quad
\frac{k-2}{k-1}(2h-E),\quad
\frac{k-2}{k+1}(3\mu-d-W).
$$

After adjoining zero, the $u_k$ column is dominated by
$\max(0,2h-E)$. If the last bracket is positive, its coefficient
increases to $(L-2)/(L+1)$; if nonpositive, zero dominates it.
These are the proved dominances yielding precisely (206.34).
The unit assertion uses $W\ge3\mu-1$ from three-label collection.
The cases $\mu=d=0$ give the zero score. At $d=0,\mu>0$, the
constructed score has nonzero early correct rows and tail but zero
excess. The endpoints $d=\mu$ and $\Theta=1$ remain included.

This completion test is not universal. When $E=0$ and $\mu>2$, all
allowed $d\le1$ have $h=\mu-2d$, whence
$d+\Theta\ge d+2(\mu-2d)=2\mu-3d\ge2\mu-3>1$.
This is a limitation of (206.33), not nonmembership in $E_N$.
$\square$

**Proposition 206.13 (Balanced all-length examples and one shared budget).**
Let $2<\mu<3$, $m=L-2\ge3$, and $m(3-\mu)>1$.
Use the complete fair score

$$
c_1=c_2=\mu-2,\quad p_1=p_2=2,\quad
\eta_j=\mu\ (j\ge3),\quad \tau=\mu-1.
\tag{206.35}
$$

Thus (206.13) specifies every early row and every late correct row.
Its data are $E=2\mu-4,S=4,W=3\mu-1$, and both excesses equal
one. It demonstrates a strict loss in separately budgeting two
components of a common score, and it fails the named direct tests
below despite being its own unit certificate.

**Proof.** Equation (206.29) gives $D=1$.
Let $V_0,V_\mu$ have the same fair late rows and $T=\mu-1$,
with early $c_1=c_2=0$ and $c_1=c_2=\mu$, respectively, and
$p_a=\mu-c_a$ in each. The score in (206.35) is

$$
V=\frac2\mu V_0+\frac{\mu-2}\mu V_\mu.
$$

Their exact costs are $\mu/2$ and one. The weighted sum of these
costs is $1+(\mu-2)/\mu>1$, while the assembled score costs one.
This proves strict loss of that additive bound, not impossibility of
all decompositions.

For the zero-score test,
$F_{Q(y)}(u_L)=m(4-\mu)/(m+1)>1$, exactly by
$m(3-\mu)>1$. The fair family with zero early correct totals in
203.6 needs $W\ge5(\mu-1)$ to retain this late profile at budget
one, exceeding the present $W$ by $2\mu-4$.
For the actual fair pair projection,
$m_j=2$, $d_{ij}=1$, and the quantities in 203.2 are
$\kappa=2\mu-3>1$, $\pi=1$.
The maximal zero core at this fixed projection retains one in each
late class; its exact positive residual charge is
$(\mu+1)m/(m+3)>1$.
In 203.4's product family, the internal weights require its parameter
$u\ge\mu$, and the $(1,2)$ unit bound at $W=3\mu-1$ forces
$u\le\mu$. At $u=\mu$, an internal pair has its two non-$11$
gains equal to $\mu$ each, so that family cannot have unit cost.
For the terminal layer coefficient
$a_m=4-2/\lceil m/2\rceil\ge3$, the 202.6 interpolation threshold
is $\mu+a_m(\mu-1/2)>3\mu-1$.
These calculations concern only the specified tests and parameters.
The comparison with 205.10 and the overlap with clipping are given
in 206.22. $\square$

**Proposition 206.14 (A non-Markov input and its dense representative).**
For every $m=L-2\ge5$, set $\mu=5/2$ and place, for all
$v\in\{0,1\}^m$,

$$
C_{01v}=C_{10v}=\frac{1/2}{2^m},\qquad
P_{01v}=P_{10v}=\frac2{2^m},\qquad T=3/2.
\tag{206.36}
$$

Put correct mass $5/2$ at $w(\{3,4\})$, $5/2$ at
$w(\{4,5\})$, and $5/2$ at each $w(\{j\})$ for $5\le j\le L$.
All other rows are zero. Then $E=1,S=4,W=13/2$ and

$$
B_O=15/2,\quad\Delta_O=1,\qquad
B_N=10,\quad\Delta_N=7/2.
\tag{206.37}
$$

Replace only the late correct rows by fair suffix rows of the same
class totals. The resulting score has the same $Q$ and both excesses
one by 206.10, or equivalently 206.12 with $d=1$.

**Proof.** Each numerical label contributes at most $5/2$ to any
cell. For early-containing stopped pairs the first maximum is $5/2$;
the other numerical rewards and their zero rewards are at most
$5/2$. For late pairs the stopped zero-label rewards are
$2,1,5/2$, and early numerical rewards are smaller. Hence any stopped
pair has support at most $15/2$, attained at $(1,2)$.
Early-containing $N$ pairs still have support at most $15/2$.
For a late $N$ pair, the zero rewards are $1,1,1,5/2$; early
numerical rewards are at most $\mu/4$, and every late label at most
$\mu$. Thus support is at most $10$. At $(4,5)$ the labels
$(4,3,5,0)$ attain four cell rewards $5/2$. Shorter schedules are
covered by pair embedding. This proves (206.37) and the fair
replacement statement.

For precise comparisons, zero score fails at
$F_{Q(y)}(u_L)=(3/2)m/(m+1)>1$. The old fair-profile threshold is
$15/2>13/2$. The actual fair projection has $\kappa=2,\pi=1$.
The maximal fixed-projection zero core has early totals zero,
late totals one, $S=4,T=3/2$. Its unscaled charge is
$(7/2)m/(m+3)>1$. Scaling this specific core by $\lambda\ge0$
gives residual readings

$$
\frac{m(3/2-\lambda)}{m+1}\quad\hbox{at }u_L,
\qquad
\frac{m(1+5\lambda/2)}{m+3}\quad\hbox{at }v_L.
$$

To bound both by one would require
$\lambda\ge1/2-1/m$ and $\lambda\le6/(5m)$, incompatible for
$m\ge5$. For the product family 203.4, its definition and the
$(1,2)$ unit condition force $u=\mu$; an $(i,z)$ gain is then
$\mu>1$, and an internal pair also has total non-$11$ gain
$2\mu>1$. These statements exclude those named constructions only;
they do not exclude every 202.4 parameter or arbitrary old closure.
The score support maximizers are tables, not cap-feasible acquisition
laws. $\square$

**Theorem 206.15 (Clipping with both signed prefix columns).**
For any input (206.7) and $0\le s\le1$, define

$$
\eta_j=\min(\gamma_j,2s),\qquad
R_k=\sum_{j=3}^k(\gamma_j-2s)_+,
\qquad V_s=\mathcal V((0,0),(2s,2s),\eta,s).
\tag{206.38}
$$

It has anchor $5s$ and exact excess
$\Delta_N(V_s)=\Delta_O(V_s)=\max(0,\max_j\eta_j-s)\le s$.
If for every $3\le k\le L$,

$$
\begin{aligned}
R_k&\le(k-2)E+(k-1)(1-s),\\
3R_k&\le(k-2)(W-5s)+(k+1)(1-s),
\end{aligned}
\tag{206.39}
$$

then $(V_s,1-s)$ is a complete certificate. In particular

$$
\mu\ge2,\qquad E\ge\mu-2,\qquad W\ge3\mu-1
\tag{206.40}
$$

suffice with $s=1$, with no restriction on the early split or the
order of the late profile. If $\delta\le1$ and three late classes
attain $\mu$, the last inequality in (206.40) is automatic.

**Proof.** This score is exactly 203.6's fair supplier with
$\kappa_f=2s,\tau=s$. Its second-largest late total is at most
$2s$, so all the hypotheses of that supplier hold. Its formula
$\max(0,\max\eta-\kappa_f/2,\max\eta-\tau)$ gives the stated
complete cost. At $s=0$ every coefficient is zero.
The quotient difference has early coordinates $\gamma_1,\gamma_2$,
late coordinates $(\gamma_j-2s)_+$, and last coordinate
$R_L+W-5s$. Formula (206.10) gives readings

$$
-E,\quad-\gamma_2,\quad
\frac{R_k-(k-2)E}{k-1},\quad
\frac{3R_k-(k-2)(W-5s)}{k+1}.
\tag{206.41}
$$

The first two are nonpositive; (206.39) bounds both remaining columns
by $1-s$. Thus (206.11) holds with one shared budget.
For (206.40), each residual class at $s=1$ is at most $\mu-2$,
so $R_k\le(k-2)(\mu-2)\le(k-2)E$ and
$3R_k\le3(k-2)(\mu-2)\le(k-2)(W-5)$.
The three-label collection proves the automatic $W$ bound.
All equality cases, including $\mu=2$, $s=0,1$ and $\theta=1$,
are included. Consequently, for $\mu\ge2$, a nonmember must have
$E<\mu-2$ or $W<3\mu-1$; with three maximum late classes and
$\delta\le1$, it must have $E<\mu-2$. These are only necessary
conditions for failure. $\square$

**Proposition 206.16 (A clipping family and a whole-family limitation).**
For every $L\ge6$ and $c>4$, put $P_{01v}=P_{10v}=c/2^{L-2}$
for every suffix $v$. Put early correct mass $c/2-1$ at each of
$w(\{1\}),w(\{2\})$. For each late $j$ put correct mass $c/2$
at $w(\{j\})$ and $c/2$ at $v_j^{\rm ch}$, adding coefficients
when the words coincide. Set $T=c-1$ and all other rows to zero.
Then $E=c-2,S=2c,W=4c-3$, and both excesses are one.
The $s=1$ certificate of 206.15 applies.

**Proof.** At $(1,2)$ the complete $N$ maxima are
$(0,3c/2-1,3c/2-1,c)$. At every early/late pair they are
$(c/2,c-1,c,3c/2-1)$. At every late pair they are
$(c/2,c/2,c,3c/2-1)$.
To check all labels in the last list, a preceding correct class puts
at most $c/2$ in a cell, class $i$ puts half in each first-zero cell,
class $j$ contributes all $c$ in $10$, and later classes at most
$c$ in $11$. Zero reward in $11$ is $3c/2-1\ge c$; each early
numerical reward there is at most $3c/4-1$. The other lists follow
by the same split of the sole-zero and chain masses. On $O$ the first
two cell maxima merge with the same total: $3c/2-1$ for an early
first query, and $c$ for a late one. The pair supports are therefore
$4c-2$ for early-containing pairs and $7c/2-1\le4c-2$ for late
pairs. Pair embedding handles shorter schedules and $(1,2)$ attains
the upper bound in $O$. Subtraction of $W$ proves the exact excess.
Here $E=c-2$, $W\ge3c-1$, so (206.40) applies.

This quotient is also in the stock region of 206.17 at
$\mu=c,d=1,S=2c,E=c-2,t=c-1$. It is not counted twice.
For comparison, zero score fails at $u_L$ with value
$2m/(m+1)>1$, $m=L-2$. The actual fair pair projection has
$\kappa=c/2>1$, $\pi=1$.
The old fair-profile threshold $5(c-1)$ exceeds $W$ by $c-2$.
The 202.6 threshold $c+a_m(c-1/2)$ with
$a_m=4-2/\lceil m/2\rceil\ge3$ also exceeds $W$.
The maximal zero core at the actual projection retains $c/2$ per late
class, whose residual charge is $(c/2+2)m/(m+3)>1$.
The precise 205.10 comparison is in 206.22.

The clipping criterion is nevertheless incomplete even on known unit
scores. For every $L\ge3$ and $c>2$, take

$$
y=\mathcal V((0,0),(2(c-1),2(c-1)),(c,\ldots,c),c-1).
\tag{206.42}
$$

Its second-largest late total is at most $c\le2(c-1)$, so 203.6
gives both excesses exactly one. This actual score is its own unit
certificate. But for every $s\in[0,1]$, the clipping residual at
$u_3$ is $(c-2s)/2>1-s$, the strict difference being $c/2-1$.
Thus no such clipping test succeeds. This also demonstrates why the
$u$ column cannot be dropped in the general residual formula.
$\square$

**Theorem 206.17 (Dense stock exchange at fixed totals).**
Fix arbitrary nonnegative $\gamma_1,\ldots,\gamma_L,S,t$ and $d\ge0$.
Suppose

$$
\mu\ge2d,\qquad t\ge\mu-d,\qquad
S\ge\max\{2\mu,4(\mu-d)-2E\}.
\tag{206.43}
$$

There exists a full score $V$ in the $A=0$, early-pair family preserving
every $\gamma_j$, $S$ and $t$, hence $Q,W$, with $\Delta_N(V)\le d$.
If $t=\mu-d$, its exact $N$ and $O$ excesses are $d$, and $d$ is the
attained minimum of each excess over all scores in that family with
precisely these fixed totals. For $d\le1$, $(V,0)$ is a certificate.
When $t>\mu-d$, only the asserted upper bound is claimed.

**Proof.** Define

$$
\begin{aligned}
\tau&=\mu-d,&E_0&=\min(E,\mu-2d),\\
c_1&=\min(\gamma_1,E_0),&c_2&=E_0-c_1,\\
p_a&=2(\tau-c_a),&S_0&=p_1+p_2,
\qquad f_a=c_a+p_a=2\tau-c_a.
\end{aligned}
\tag{206.44}
$$

Because $0\le E_0\le E$, each $c_a$ is nonnegative and at most
$\gamma_a$. Also $c_a\le\mu-2d\le\tau$, so $p_a\ge0$.
In particular

$$
\begin{gathered}
S_0=4\tau-2E_0=\max\{2\mu,4(\mu-d)-2E\}\le S,\\
2\mu\le S_0\le4\mu,\qquad
\mu\le f_a\le2\mu,\quad f_a\le S_0,\quad
\tau\ge\mu/2,\quad p_a/2+\tau=f_a.
\end{gathered}
\tag{206.45}
$$

Construct the fair core $V_0=\mathcal V(c,p,\gamma_{\ge3},\tau)$,
with anchor $W_0=f_1+f_2+\tau=E_0+S_0+\tau$.
For $(1,2)$ its exact $N$ maxima are $(0,f_1,f_2,\mu)$ because
$\tau\le\mu$. The stopped table $(1,2;1,2,j_*)$ attains
$W_0+d$. For an early/late pair, the first two $N$ cells sum to
$f_a$; the $10$ cell has maximum at most $\mu$, since
$f_b/2\le\mu$ and all late totals are at most $\mu$.
In $11$, zero earns $p_b/2+\tau=f_b$, dominating all numerical
labels since $f_b\ge\mu$. Thus the support is at most
$f_a+\mu+f_b=W_0+d$.

For late $i<j$, each of $00,01$ has maximum exactly $S_0/4$.
This zero-label reward covers $f_a/4$, earlier late rewards at most
$\mu/4$, and class $i$'s half-total at most $\mu/2$, using
$S_0\ge2\mu$. The $10$ maximum is at most $\mu$, including
$S_0/4\le\mu$. The $11$ maximum is exactly $S_0/4+\tau\ge\mu$,
which covers every numerical label. Consequently the total is at most
$3S_0/4+\mu+\tau$, whose excess over $W_0$ is

$$
\mu-S_0/4-E_0=d-E_0/2\le d.
$$

These full-label bounds cover every pair and hence every shorter
schedule. The stopped attainer at $(1,2)$ proves
$\Delta_N(V_0)=\Delta_O(V_0)=d$, also when $\mu=d=0$.

Now add correct mass $\gamma_a-c_a$ fairly in early class $a$, pair
mass $S-S_0$ fairly in early class one, and $t-\tau$ to $T$.
More explicitly, divide each added early total equally over all
$01v$ or $10v$ as appropriate. All added coefficients are
nonnegative. The anchor collects each added row with coefficient one;
any fixed deterministic table collects it with coefficient at most
one. Hence adding them cannot increase that table's relative excess.
Taking the maximum only after this comparison gives
$\Delta_N(V)\le d$. Every prescribed total, the quotient and the
anchor are exactly restored. This does not assign separate positive
budgets to the additions.

If $t=\tau$, any competitor with these data permits the stopped
table $(1,2;1,2,j_*)$, which collects all early correct and pair rows
and the maximum late class. Its reward is
$E+S+\mu=W+d$, independent of suffix placement or early imbalance.
Thus $\Delta_O\ge d$ and $\Delta_N\ge\Delta_O$ for every such
competitor. The constructed upper bound matches, proving both minima.
No minimum-stock claim or optimization over unrestricted event types
is asserted. $\square$

**Corollary 206.18 (Coupled clipping, retained early totals and one charge).**
Choose parameters

$$
0\le d\le1,\qquad2d\le u\le\mu,\qquad
S\ge2u,\qquad t\ge u-d,
\qquad c=\max\{0,2(u-d)-S/2\}\le E.
\tag{206.46}
$$

Set $c_1=\min(\gamma_1,c)$, $c_2=c-c_1$ and

$$
\eta_j=\min(\gamma_j,u),\qquad r_j=\gamma_j-\eta_j,\qquad
R_k=\sum_{j=3}^kr_j,\qquad E_{\rm lost}=E-c.
$$

Applying 206.17 to the early totals $c_a$, the late totals $\eta_j$
and the original $S,t$ gives one score $V$ with $\Delta_N(V)\le d$.
Its exact nonnegative residual charge is

$$
\Theta=\max\left\{0,\max_{3\le k\le L}
              \frac{3R_k-(k-2)E_{\rm lost}}{k+1}\right\}.
\tag{206.47}
$$

If $d+\Theta\le1$, it certifies $Q(y)\in E_N$.
In particular, any unit-$O$ input with

$$
\mu\ge2,\qquad S\ge\max\{2\mu,4(\mu-1)-2E\}
\tag{206.48}
$$

has the exact-$Q$ certificate of 206.17 with $d=1$.

**Proof.** Since $S\ge2u$, the definition of $c$ gives
$0\le c\le u-2d$ and $S\ge4(u-d)-2c$. Because $u\le\mu$,
the retained late maximum is $u$ (also if $u=0$). The other stock
hypotheses are precisely (206.46). Each retained early total is at
most the corresponding original total. As $S,t$ are unchanged,
$W-W'=E_{\rm lost}$ and $K_y-K_V=R_L+E_{\rm lost}$.
The four residual readings are

$$
-E_{\rm lost},\quad-(\gamma_2-c_2),\quad
\frac{R_k-(k-2)E_{\rm lost}}{k-1},\quad
\frac{3R_k-(k-2)E_{\rm lost}}{k+1}.
\tag{206.49}
$$

Here, with the nonnegative $R_k,E_{\rm lost}$ just proved, the last
reading minus the preceding one is

$$
\frac{2(k-2)(R_k+E_{\rm lost})}{(k-1)(k+1)}\ge0.
\tag{206.50}
$$

Only this sign argument permits suppression of the $u$ column.
The first two readings are nonpositive, so adjoining zero yields
exactly (206.47). Now apply (206.11) once to the assembled score
and this single residual. At $u=0$ one has $d=c=0$, all retained
late totals vanish, and the construction retains the original $S,t$
rows without division. All equality cases are included.

Finally, the original stopped table $(1,2;1,2,j_*)$ always gives
$\delta\ge\mu-t$. For $\delta\le1$, this forces $t\ge\mu-1$,
so (206.48) implies (206.43) at $d=1$. This statement allows arbitrary
early imbalance and arbitrary ordering or growing support of the
late profile. It does not require raw subscore subtraction preserving
the input's stopped excess. $\square$

**Proposition 206.19 (Stock exchange with a matching fixed-total minimum).**
For every $L\ge8$, set all late totals to four, let
$\gamma_1,\gamma_2\ge0$ have sum two, and use

$$
y=\mathcal V((\gamma_1,\gamma_2),
              (6-2\gamma_1,6-2\gamma_2),(4,\ldots,4),3).
\tag{206.51}
$$

It has $S=8,W=13$ and both excesses one, the attained fixed-data
minimum. Every input in (206.7) with these same totals receives its
exact-$Q$ certificate. This example is also in the clipping region.

**Proof.** These are the stock core parameters
$\mu=4,d=1,E_0=2,\tau=3$, so 206.17 applies with equality.
For the explicit split $(\gamma_1,\gamma_2)=(2,0)$, the full $N$
maxima are $(0,4,6,4)$ at $(1,2)$,
$(2,2,4,6)$ at $(1,j)$, $(3,3,4,4)$ at $(2,j)$, and
$(2,2,4,5)$ at late pairs. They follow directly from (206.14)–(206.16).
The stopped first cells merge with the same total. Hence both complete
supports are $14$, including shorter schedules. For any split the
stock theorem proves the same value. Its lower bound is
$\mu-t=1$ for every fixed-data competitor.

Zero score fails at $u_L$ with $2m/(m+1)>1$, $m=L-2$.
The 203.6 fair-profile unit threshold is $15>13$.
The actual pair projection has $m_j=4,d_{ij}=2$, hence
$\kappa=2,\pi=1$. The clipping corollary applies because
$E=\mu-2$ and $W=3\mu-1$; this is one membership example with two
available certificates. At 205.10's threshold, writing
$r=\lceil(m+1)/2\rceil$, budget one requires
$W\ge\max(15-6/r,13)$. It is strictly larger than $13$ for
$r\ge4$, equivalently $L\ge8$. At $m=4,5$ it equals $13$,
so those equality cases are already in that named prior region.
$\square$

**Proposition 206.20 (Stock exchange beyond the named clipping and aggregate tests).**
For every $m=L-2\ge12$, take all late totals four and

$$
y=\mathcal V((1,0),(4,6),(4,\ldots,4),3).
\tag{206.52}
$$

It has $E=1,S=10,t=3,W=14$, and both complete excesses one.
It attains the fixed-total minimum, fails every clipping parameter
$s\in[0,1]$ in 206.15, and lies below the stated 205.10 aggregate
threshold for every allowed unit parameter $d\le1$.

**Proof.** Here $\mu=4,d=1,E_0=1$, so (206.44) gives exactly the
specified rows. For clarity, the complete $N$ maxima are

$$
\begin{array}{c|c|c}
\text{schedule}&(00,01,10,11)\text{ maxima}&\text{sum}\\ \hline
(1,2)&(0,5,6,4)&15\\
(1,j)&(5/2,5/2,4,6)&15\\
(2,j)&(3,3,4,5)&15\\
(i,j),\ 3\le i<j&(5/2,5/2,4,11/2)&29/2
\end{array}
\tag{206.53}
$$

In a late pair the $11$ zero reward $11/2$ dominates every numerical
label, and $00,01$ each have pair reward $5/2$. The common cell
calculation supplies the remaining entries. For $O$, the first two
maxima merge into their sum. Pair embedding and $(1,2)$ prove both
supports $15$, and 206.17 supplies the fixed-total lower bound one.

The old fair budget-one threshold is $15>14$. In 205.10,
$r=\lceil(m+1)/2\rceil\ge7$, and the threshold at $d=1$ is
$\max(15-6/r,13)>14$. Each of its two threshold terms decreases
with $d$, so a smaller allowed $d$ cannot help.
For clipping, $R_3=4-2s$, $E=1$; the $u_3$ residual is
$(3-2s)/2=3/2-s>1-s$ for every $s$.
The actual fair projection has $m_j=5,d_{ij}=5/2$,
$\kappa=3/2$, $\pi=1$; thus both the direct $\kappa+\pi$ test
and the positive-cell test 205.9 have cost exceeding one.
This is a distinct gap between these named sufficient tests. It is
not exclusion from all previous signed certificates or closures.
$\square$

**Proposition 206.21 (A zero-cost limitation of the coupled stock test).**
At $L=5$, specify all nonzero rows by

$$
\begin{aligned}
P_{01000}=P_{10000}=P_{01101}=P_{10101}&=4,\\
P_{01011}=P_{10011}=P_{01110}=P_{10110}&=1,\\
C_{11011}=C_{11110}&=1,\qquad C_{11101}=8,\qquad T=10.
\end{aligned}
\tag{206.54}
$$

All $A$ and unspecified rows are zero. This is eight times the score
owned by 203.12. Its data are
$E=0$, $(\gamma_3,\gamma_4,\gamma_5)=(1,8,1)$, $S=20,t=10,W=30$.
Both complete supports are $30$, so it is a zero-excess score.
Nevertheless every permitted $(u,d)$ in the coupled test 206.18
has $d+\Theta>1$.

**Proof.** The pair projection has masses eight at $000,101$ and
two at $011,110$. On any two late addresses, the correct word at
$101$ has mass eight and each of the correct words at $011,110$
has mass one. In its cell each is dominated by the corresponding
projected pair atom. For an early/late pair, a correct word with
late answer one shares the positive cell with $T=10$, which covers
every correct class. With late answer zero, half of the zero marginal
from the other early lift supplies capacities $5,8,5$ at addresses
$3,4,5$, respectively. They cover all correct rewards there, including
class four of mass eight at address four. At $(1,2)$, $T$ covers
all correct rows in $11$. Early numerical labels collect only subsets
of the zero-label pair reward. Thus zero maximizes every cell of
every pair. Merging cells preserves this domination for singles,
the empty schedule and stopped cells. Its total is always $S+T=30$.
For example the $(3,5)$ maxima are $(8,2,2,18)$ in $N$ and
$(10,2,18)$ in $O$.

In (206.46), $E=0$ forces $c=0$, and hence
$2(u-d)-10\le0$, or $u\le5+d$. Therefore
$R_4=(1-u)_++(8-u)_+\ge3-d$. Since $E_{\rm lost}=0$,

$$
d+\Theta\ge d+\frac{3R_4}{5}
 \ge\frac95+\frac{2d}{5}>1\qquad(0\le d\le1).
\tag{206.55}
$$

This excludes every allowed parameter of that test on an actual
zero-cost score. It does not exclude $E_N$ membership: the score
itself with residual zero is a certificate. $\square$

**Proposition 206.22 (Exact overlap with the earlier aggregate threshold).**
For $m\ge4$ active late coordinates, put

$$
b_m=4-\frac2{\lceil(m+1)/2\rceil}.
$$

The sufficient region of [Theorem
205.10](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md)
is, for $\mu\ge2d$ and $d\ge0$,

$$
W\ge\max\{(b_m+1)(\mu-d),4\mu-3d\}.
\tag{206.56}
$$

The examples and automatic regions above have the following exact
relations to it and to one another. The balanced and completion
examples with $\mu>2,W=3\mu-1$ fail its second threshold at every
$d\le1$. The stock example $\mu=4,W=13$ meets it at equality
for $m=4,5$ and fails for $m\ge6$. The stock example
$\mu=4,W=14$ fails for $m\ge12$. The clipping example
$\mu=c>4,W=4c-3$, $m\ge4$, fails its first threshold.
These are comparisons with (206.56), not with every consequence of
old closure or residual theorems.

**Proof.** Both terms in (206.56) decrease with $d$. For these
examples $\mu>2$, so $d=1$ minimizes them among $0\le d\le1$.
At that endpoint $3\mu-1<4\mu-3$ exactly when $\mu>2$.
For $\mu=4$, write $r=\lceil(m+1)/2\rceil$; the terms are
$15-6/r$ and $13$. They both fit $W=13$ when $r=3$ and the first
exceeds it when $r\ge4$. It exceeds $W=14$ when $r\ge7$,
which includes every $m\ge12$.
For the clipping example, the second term is exactly $W=4c-3$;
the first minus $W$ is

$$
(b_m-3)c-(b_m-2)>0.
$$

Indeed $b_m\ge10/3$ and $c>4$; at $b_m=10/3$ this is
$(c-4)/3>0$, and it increases with $b_m$.
The strict domain $c>4$ and the equality cases at $m=4,5$ are
therefore essential to these precise comparisons.

Within the present results, (206.32) implies (206.40) because
$2(\mu-2)\ge\mu-2$ for $\mu>2$. Thus the balanced automatic
region is contained in the clipping region. Its exact support,
signed residual, asymmetric optimum and retained-profile construction
are additional structural information. Corollary 206.12 is exactly
206.10 at $c_1=c_2=(\mu-2d)_+$ and $W'=3\mu-d$.
The stock example in 206.19 is also covered by (206.40), and the
clipping example in 206.16 also meets the stock hypotheses at
equality. The distinct stock family 206.20 fails every clipping
parameter by its $u_3$ inequality. The chain unit region already has
(206.26)'s zero-score certificate. Common fair or chain representatives
can themselves belong to the earlier common-Markov class 198.2.
None of these facts identifies five disjoint new cap regions.
$\square$

**Definition 206.23 (Owning suppliers and mathematical attribution).**
The finite moment reduction used inside 206.5 is
`literature-attested`: Christian Bayer and Josef Teichmann,
*The Proof of Tchakaloff's Theorem*,
[arXiv:math/0502473v2, Corollary 2 and Theorem 2](https://arxiv.org/html/math/0502473v2).
Corollary 2 preserves a finite vector of integrable functions by
positive weights at points of the original full-measure set. Here
those functions are the constant, single-bit and pair-bit features
within each actual first-zero/event class. The explicit elimination
and cell argument establish the Boolean dimension and the complete
reward preservation needed for this application. This gives a
representation bound, not additional cap coverage or a minimality
claim.

The remaining support calculations, parameter correspondences,
fixed-data optima and residual applications in this section are
`repo-derived` ordinary synthesis. Their suppliers retain ownership:

| Owning source | Exact use and boundary |
| --- | --- |
| [Continuation I, 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source) | Class-preserving original/finite closed-cap feasibility, arbitrary-address and full-carrier necessity, actual probability realization, and the exact positive-tail identity. |
| [Continuation VI, 198.2, 198.4–198.6](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md) | Common-suffix support equality, correct-label collection, the full signed hull, and the existing obstruction to unconditional chain relocation. |
| Continuation VI, 199.1–199.4, 199.7–199.8, 200.4 | Full-event quotient and certificate rule, the attained-separator alternative, its conditional normalization, common-seed realization and the subset-law bound at every $v_k$. |
| [Continuation VII, 202.6, 203.2, 203.4, 203.6–203.7](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md) | The stated interpolation threshold, actual pair-projection quantities, complete product and fair suppliers, and three-label capacity. |
| Continuation VII, 203.12, 204.1–204.2, 205.7–205.10 | The existing zero-cost example, the fixed-projection zero core and its residual, actual positive-cell protection and the precise correlated aggregate threshold. |

For the fixed-projection comparisons, the same actual pair measure is
used throughout: $m_j=\nu(x_j=0)$, $d_{ij}=\nu(x_i=1,x_j=0)$,

$$
\kappa=\max\left\{0,\max_j(\gamma_j-m_j/2)_+,
 \max_{i<j}\big[(\gamma_i-m_i)_++(\gamma_j-d_{ij})_+\big]\right\},
\qquad \pi=(\mu-t)_+.
$$

The zero core in 204.1–204.2 retains the capacity-limited late totals
at that fixed projection, with early totals zero and the stated
$S,t$. Its maximality is only under those restrictions. No comparison
above excludes all choices of projections, all 202.4 parameters, all
signed residuals, or all consequences of arbitrary-support and
zero-cost closures. The moment application and the ordinary synthesis
do not carry a claim of literary priority or exhaustive novelty.

Other mature results have different conclusion types.
Kaniewski, Lee and de Wolf, *Query complexity in expectation*,
[arXiv:1411.7280v1, Theorem 9](https://arxiv.org/html/1411.7280v1),
concerns a nonnegative scalar expectation and nonnegative literal
degree. It does not by itself provide one normalized probability-vector
kernel satisfying all event rows with increasing first-zero stopping.
Leskelä, *Stochastic relations of random variables and processes*,
[arXiv:0806.3562v1, Theorem 2.5](https://arxiv.org/html/0806.3562v1),
gives a closed-relation coupling criterion with fixed marginals; no
map supplying the present query-kernel coupling is assumed here.
Kaibel's *Basic Polyhedral Theory* supplies the finite alternatives
already used in 199.3. Blackwell's *Comparison of Experiments* and
*Equivalent Comparisons of Experiments* are distinct works and provide
background, not an additional acquisition bridge for this section.

**Proposition 206.24 (Original necessary inequality and exact transport scope).**
Let (206.2) be any original amplitude sequence, let
$0<\varepsilon\le1$, and suppose $L_a\ge3$ and an original
$N_2$ or $O_2$ acquisition attains this closed cap. At $L=L_a$, for
every balanced score of 206.10,

$$
c_1(a_1-1)+c_2(a_2-1)+\sum_{j=3}^L\eta_j a_j
       -\left(\sum_{j=3}^L\eta_j+W'\right)\varepsilon
 \le D,
\tag{206.57}
$$

with the same $D$ as (206.29). No assumption
$(a_1,\ldots,a_L;\varepsilon)\in H_L$ is required.
This is a necessary inequality; it is not sufficient acquisition
feasibility.

**Proof.** Apply the necessity direction of 110.2 to obtain one
normalized finite probability configuration in the appropriate full
catalog satisfying every row of (206.3). Sum those inequalities
against the single nonnegative score $V$. Its target reward is

$$
W'+c_1(a_1-1)+c_2(a_2-1)+\sum_{j=3}^L\eta_j a_j
       -\left(\sum_{j=3}^L\eta_j+W'\right)\varepsilon.
$$

The same probability configuration has reward at most the complete
support $W'+D$ by 206.10. Subtraction gives (206.57).
All rows, including the independent pair row and negative singleton
demands, participate in the same inequality.

The transport being used is specifically 110.2. Its necessity first
projects full tapes measurably onto the original marks
$\theta_0,\ldots,\theta_{L_a}$, contracting TV. Countability of the
source gives one probability-one seed event of finite handoff and
request compliance for every actual source. Truncating the preselected
maximum address on a common seed event and using finite-time cutoffs
on finitely many actual word witnesses gives finite tables in the
same class. The finite catalog simplex is compact, so limits preserve
the exact closed-cap rows. This covers arbitrary-address/full-carrier
competitors without claiming to preserve every competitor's full law.

Conversely, only an actual nonnegative probability vector of total
one on complete tables, satisfying all cap rows, is transported into
a cap attainer. Partition one $U\sim\operatorname{Unif}[0,1)$ into
intervals of those table weights, selecting the whole schedule and all
its terminal labels before any answers. Execute its scheduled actual
prime queries and emit its original terminal mark. $N$ obtains its
preselected replies; $O$ stops at its first queried zero or exhaustion.
All executed requests, including ignored or repeated ones, count.
The handoff is finite, and no source label, $N(x)$, first absence,
source law or extra randomness is supplied. Two class-specific
probability vectors may use partitions of the same $U$ and their
common refinement; they need not agree seedwise.

For every actual $n>L_a$, the transported law has exactly the tail
error supplied by 110.2:

$$
\operatorname{TV}\left(\sum_{j=0}^{L_a}p_{1^{L_a}}(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-p_{1^{L_a}}(0),a_n\}\le\varepsilon.
\tag{206.58}
$$

This includes $a_n=\varepsilon$. All actual tails stay positive,
monotone and vanishing. The finite positive word is tail bookkeeping,
not an infinite all-positive source. Immediate base output handles
$L_a=0$, including $\varepsilon=1$; smaller active lengths are covered
by the owning transport, not by the present $L\ge3$ score theorems.
Caps above one are trivial for TV. A score certificate or a
support-maximizing table alone is not a feasible probability vector,
so (206.11) cannot be substituted directly for this primal hypothesis.
$\square$

**Definition 206.25 (Remaining full-family and original-source obligations).**
Use the complete cone masses and feasible auxiliary domain

$$
\rho_C(b,e)=\min_{\lambda\ge0,\ G_C\lambda\ge h(b,e)}\sum_D\lambda_D,
\qquad
H_N=\{(b,e)\in H_L:\rho_N(b,e)<\infty\},
$$

where an infeasible minimum is infinity. The unresolved comparison is

$$
\rho_O(b,e)\le\max\{1,\rho_N(b,e)\}\quad((b,e)\in H_N).
\tag{206.59}
$$

Even within the entire all-$L$ family (206.7), with arbitrary early
credit, arbitrary correct suffixes and late profile, and arbitrary
low $t$, a certificate for every $\Delta_O(y)\le1$ has not been
established here. The moment reduction preserves this problem; the
other four groups have explicit coverage hypotheses. Their union is
not proved exhaustive. Failures of clipping, coupled stock completion
or unconditional chain relocation are failures of those constructions,
not counterexamples to (206.59).

A genuine finite refutation requires one common $(b,e)\in H_L$, a
nonnegative full score $y$ with $\Delta_O(y)\le1$, and an actual
attained $\lambda\ge0$ satisfying every row of

$$
G_N\lambda\ge h(b,e),\qquad
M=\sum_D\lambda_D\ge1,\qquad F_{Q(y)}(b,e)>M.
\tag{206.60}
$$

An auxiliary vertex, a support gap or failure of a sufficient test is
not such a $\lambda$. The existing normalization in 199.7 and its
positive-cap boundary supplier 168.1, followed by 110.2, apply only
under their proved hypotheses. Arbitrary original amplitude/cap
vectors are not presumed to lie in $H_L$.

For the original problem, the remaining obligation is, for every
sequence (206.2) and every positive closed cap,

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
\quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing,
\tag{206.61}
$$

or an explicit original common-seed $N_2$ attainer and a uniform lower
certificate against every full-carrier, arbitrary-address $O_2$
competitor. The exact-law obstruction of 112.2 permits a different
stopped law at the same cap and therefore does not settle this
obligation. Neither the five scoped groups nor their overlap
comparisons establish universal completion.

## 追加锚（本行以下为增补区）
