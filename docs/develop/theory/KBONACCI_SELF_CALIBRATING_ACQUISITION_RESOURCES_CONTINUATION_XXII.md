# k-bonacci 自校准：获取资源续卷 XXII

## 363. Actual sources, complete laws and canonical events

**Definition 363.1 (Source and selected targets).** Use the original source and carrier of [Acquisition Resources 71.1, 73.1 and 90.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md). Explicitly,

$$
\begin{aligned}
F_0&=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
 \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i\ge1:q_i(x)=0\},
\end{aligned}
\tag{363.1}
$$

where $p_i$ is the $i$th prime. The integer $N(x)$ is static; its prime support is finite, so $n(x)$ exists. There is no probability distribution on $X$. The measurable carrier is the Borel disjoint union

$$
\mathcal T=\bigsqcup_{j\ge1}B_j\ \sqcup\ \bigsqcup_{j\ge1}P_j,
\qquad B_j\cong P_j\cong(0,1).
$$

The consumer is unchanged: a tape in $B_j$ gives the unknown outcome, and a tape in $P_j$ proposes $j$. Its original nonatomic targets are denoted by $\mu_x$. The distinct measurable marks
$\theta_j=(B_1,1/(j+2))$, $j\ge0$, define the separate selected targets

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_i\longrightarrow0,
\qquad
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                    +a_{n(x)}\delta_{\theta_{n(x)}}.
\tag{363.2}
$$

Write $e_j$ for the unit vector of label $j$, or for $\delta_{\theta_j}$ when interpreted on $\mathcal T$. For an acquisition $A$ with handed-tape law $\nu_{A,x}$, put

$$
\operatorname{TV}(\nu,\rho)=\sup_{E}|\nu(E)-\rho(E)|,
\qquad e_a(A)=\sup_{x\in X}\operatorname{TV}(\nu_{A,x},\lambda_x^a).
\tag{363.3}
$$

Every finite Boolean reply word, including every multiple-zero word and every prescribed finite continuation, is realized by an actual $x\in X$, by [Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows). Its construction chooses a prime index above the entry ranks of the finitely many probe primes. Then $F_r$ is invertible modulo their product; the Chinese remainder conditions impose divisibility at the one bits and nondivisibility at the zero bits. Fibonacci growth makes the legal window for $g$ long enough to contain the required residue class. This finite-pattern result supplies witnesses, without supplying any observation or source prior to an acquisition.

**Definition 363.2 (One seed and actual requests).** The original classes $\mathcal N_2,\mathcal O_2$ have zero advice and one source-independent seed. Before replies, that seed fixes the entire schedule and every counterfactual terminal output. Handoff is measurable and almost surely finite separately at each actual source. The hard bound is at most two actual requests; repeated requests and acquired replies subsequently ignored are charged. In $\mathcal N_2$ the entire preselected schedule is acquired. In $\mathcal O_2$ the schedule is increasing and stops at the first queried zero or exhaustion. Outputs can name an earlier or unqueried label, and original competitors may use arbitrary addresses and output anywhere in $\mathcal T$.

These are the original classes of [110.1–110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source). No next address is chosen from a reply. No reset, copy, free observation, second seed, mean-request bound, maximum-address bound or running-time bound is substituted for this definition. Neither $N(x)$ nor $n(x)$ nor a source label is supplied. All replies are to the same static source, and the unchanged consumer receives the handed tape on that source.

**Definition 363.3 (Finite complete catalogs).** For $L\ge0$ let
$B_L=\{0,1\}^L$ and $J_L=\{0,\ldots,L\}$. Let $\mathscr N_L$ and $\mathscr O_L$ be the finite complete classes of [108.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#108-common-probability-vector-kernels-and-stopped-schedules) and [II 140.2–140.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_II.md). A pair $i<j$ in $\mathscr N_L$ has four nonnegative output-mass vectors $X_{ij}^{00},X_{ij}^{01},X_{ij}^{10},X_{ij}^{11}$, all of the same mass $m_{ij}$. Its contribution is

$$
(1-w_i)(1-w_j)X_{ij}^{00}+(1-w_i)w_jX_{ij}^{01}
+w_i(1-w_j)X_{ij}^{10}+w_iw_jX_{ij}^{11}.
\tag{363.4}
$$

A stopped pair has only cells $0,10,11$, with $X^{00}=X^{01}=X^0$. Include every empty and singleton schedule and every output label. Every cell of a singleton also has its owning schedule's mass. Empty, singleton and pair masses, each counted once, sum to one. Sorting a preselected pair and absorbing its order in the table does not change its information; deleting a repeated static query in the finite representation does not erase its charge in the original execution.

Equivalently, each class is the convex hull of its finite catalog of deterministic schedules with all terminal tables. One uniform seed $U\in[0,1)$ realizes any such complete allocation: partition the interval into schedule masses, rescale within a selected interval, and use that same local coordinate in every cell's label quantile partition. Intersecting those partitions fixes the whole table before any reply. Cells are not normalized or randomized independently. This is the common-seed realization of [Source-Correlated Laws 45.1–45.3](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#45-lawful-acquisition-through-one-inherited-seed).

**Definition 363.4 (All independent cap rows).** For $w\ne1^L$ write
$n(w)=\min\{i:w_i=0\}$. The canonical event vector $z(p)$ consists of

$$
z_{A,w}(p)=p_w(0),\qquad z_{C,w}(p)=p_w(n(w)),\qquad
z_{P,w}(p)=p_w(0)+p_w(n(w)),\qquad z_T(p)=p_{1^L}(0).
\tag{363.5}
$$

At a prefix $b=(a_1,\ldots,a_L)$ and cap $e$, its literal demands are

$$
\begin{aligned}
p_w(0)&\ge1-b_{n(w)}-e,&
p_w(n(w))&\ge b_{n(w)}-e,&
p_w(0)+p_w(n(w))&\ge1-e,\\
p_{1^L}(0)&\ge1-e.
\end{aligned}
\tag{363.6}
$$

The three zero-word rows remain separate, even if a singleton demand is negative. All words and all labels remain present when a score gives some rows weight zero. At $L=7$ there are $128$ words, eight labels and $3\cdot127+1=382$ rows.

Indeed, for $\eta_w=(1-b_n)e_0+b_ne_n$,

$$
\operatorname{TV}(p_w,\eta_w)
=\max\{1-b_n-p_w(0),\ b_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
\tag{363.7}
$$

The mass outside $\{0,n\}$ is the sum of the first two displayed deficits and is nonnegative; summing positive deficits gives precisely this maximum. At the finite positive word the target is $e_0$. If an original first absence is $n>L$ and $p$ uses only $J_L$, the exact tail formula is

$$
\operatorname{TV}(p_{1^L},\lambda_x^a)
                         =\max\{1-p_{1^L}(0),a_n\}.
\tag{363.8}
$$

The finite positive word is an endpoint condition, not an infinite all-positive source. These are the rows and tail identity used in 110.1–110.2.

## 364. A complete perturbation at the inherited optimal profile

**Definition 364.1 (Whole gauges and their two budgets).** For a degree-at-most-two entire kernel write its unique multilinear expansion as

$$
p(w)=c+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j.
\tag{364.1}
$$

For a vector $v$, let $m(v)=\sum_{z\in J_L}v(z)$; positive parts and maxima of vectors are coordinatewise. A whole gauge has $m(g_{ij})=0$ for every pair, including every pair with $Q_{ij}=0$. Use the data of [XIX 341.1–341.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIX.md#341-the-complete-preselected-coefficient-cone):

$$
\begin{aligned}
r_{ij}&=(-g_{ij})_+,&s_{ij}&=(-g_{ij}-Q_{ij})_+,\\
t_{ij}&=\max\{m(r_{ij}),m(s_{ij})\},&
D_i&=\ell_i-\sum_{h<i}g_{hi},\\
R_i&=\sum_{j>i}r_{ij},&S_i&=\sum_{j>i}s_{ij},\\
T_i&=\sum_{j>i}t_{ij},&U_i&=\max\{R_i,S_i-D_i\},\qquad u_i=m(U_i).
\end{aligned}
\tag{364.2}
$$

A funded gauge means that this same whole family satisfies both

$$
c\ge\sum_iU_i,\qquad \sum_i\max\{u_i,T_i\}\le1.
\tag{364.3}
$$

XIX 341.2 characterizes complete $\mathscr N_L$ realizability by the existence of such a gauge; the $g=0$ slice is the stopped criterion of 109.1. Here the criterion is used for the concrete family below.

**Theorem 364.2 (Complete family and the same-cap stopped survivor).** Set

$$
b=\frac1{64}(43,34,34,29,27,25,22),\qquad e_*=\frac{15}{64}.
\tag{364.4}
$$

For every entire sequence (363.2) with this prefix and $a_8\le e_*$, and for every $0\le t\le5/64$, there is a complete $p_t\in\mathscr N_7$ with an original $\mathcal N_2$ realization attaining error $e_*$. The law $p_0=:p_*$ belongs to $\mathscr O_7$ and has an original $\mathcal O_2$ realization at that same cap. The attained optimum $e_*$ in both original classes, and the stopped law $p_*$, are those of [XIX 346.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIX.md#346-a-complete-original-attainer-at-error-fifteen-sixty-fourths).

*Proof.* Put $h=64t$. All entries in the following table, including the owning masses, are numerators over $64$. An omitted coordinate or schedule is zero.

| Pair | Mass | $00$ | $01$ | $10$ | $11$ |
| --- | ---: | --- | --- | --- | --- |
| 12 | 17 | $17e_1$ | $17e_1$ | $17e_2$ | $7e_0+5e_3+5e_4$ |
| 13 | 7 | $7e_1$ | $7e_1$ | $7e_3$ | $7e_0$ |
| 14 | 2 | $2e_1$ | $2e_1$ | $2e_4$ | $2e_0$ |
| 15 | 2 | $2e_1$ | $2e_1$ | $2e_5$ | $2e_0$ |
| 23 | 7 | $(5-h)e_0+(2+h)e_2$ | $5e_0+2e_2$ | $7e_3$ | $7e_0$ |
| 24 | 2 | $2e_0$ | $2e_0$ | $2e_4$ | $2e_0$ |
| 25 | 2 | $2e_0$ | $2e_0$ | $2e_5$ | $2e_0$ |
| 34 | 5 | $5e_0$ | $5e_0$ | $5e_4$ | $4e_0+e_7$ |
| 35 | 4 | $4e_0$ | $4e_0$ | $4e_5$ | $4e_0$ |
| 36 | 2 | $2e_0$ | $2e_0$ | $2e_6$ | $2e_0$ |
| 45 | 4 | $4e_0$ | $4e_0$ | $4e_5$ | $4e_0$ |
| 46 | 2 | $2e_0$ | $2e_0$ | $2e_6$ | $2e_0$ |
| 56 | 6 | $6e_0$ | $6e_0$ | $6e_6$ | $2e_0+4e_7$ |
| 67 | 2 | $2e_0$ | $2e_0$ | $2e_7$ | $2e_0$ |

Every cell is nonnegative and has its owning mass, and the masses sum to $64$. Thus (363.4) defines the entire normalized kernel. At $t=0$ the first two cells of every pair agree, giving exactly the cited stopped survivor. On the whole cube,

$$
p_t(w)=p_*(w)+t(1-w_2)(1-w_3)(e_2-e_0).
\tag{364.5}
$$

Here are explicit cap calculations for every suffix. In $64p_*(w)$ the base coordinate is

$$
\begin{aligned}
B(w)={}&9(1-w_2)+11(1-w_3)+6(1-w_4)+6(1-w_5)+2(1-w_6)\\
 &+7w_1w_2+7w_1w_3+2w_1w_4+2w_1w_5\\
 &+7w_2w_3+2w_2w_4+2w_2w_5
   +4w_3w_4+4w_3w_5+2w_3w_6\\
 &+4w_4w_5+2w_4w_6+2w_5w_6+2w_6w_7.
\end{aligned}
\tag{364.6}
$$

For first zero $n$, the correct numerator $c_n$ is constant on its entire suffix fiber. Substituting $w_1=\cdots=w_{n-1}=1,w_n=0$ in (364.6) gives:

| $n$ | $c_n=64p_*(w)(n)$ | $\min B(w)$ | $\max(64-B(w)-c_n)$ |
| ---: | ---: | ---: | ---: |
| 1 | 28 | 21 | 15 |
| 2 | 19 | 30 | 15 |
| 3 | 19 | 30 | 15 |
| 4 | 14 | 35 | 15 |
| 5 | 12 | 37 | 15 |
| 6 | 10 | 43 | 11 |
| 7 | 7 | 47 | 10 |

Each minimum is over all $2^{7-n}$ suffixes. The table can equivalently be evaluated by repeatedly replacing a suffix polynomial $f$ by $\min\{f|_{w_j=0},f|_{w_j=1}\}$. Together with the explicit polynomial, this includes every multiple-zero case. The correct counts also follow directly from the displayed complete cells, and satisfy $c_n=64b_n-15$. The base deficit in (363.7) is therefore the wrong mass minus $15/64$; the last column bounds every union deficit by $15/64$.

Only $w_2=w_3=0$ changes in (364.5). If the first zero is $2$, its correct coordinate increases by $t$ and its union coordinate is unchanged. Its old base is at least $30/64$, so its new base is at least $25/64$, above the literal demand $15/64$. If the first zero is $1$, its correct coordinate stays $28/64$. On the affected subfiber the old base is at least $26/64$, hence its wrong mass is at most $10/64$. To see that restricted bound directly, put $u=w_4,v=w_5,z=w_6,r=w_7$; then

$$
B(w)=20+6(1-u)+6(1-v)+2(1-z)+4uv+2uz+2vz+2zr.
\tag{364.7}
$$

The part following $20$ has minimum $6$ when $z=0$, and minimum $8$ when $z=1$. The change increases wrong mass by at most $5/64$, and leaves base at least $21/64$, above its demand $6/64$. All other zero words are unchanged. This proves all three independent rows throughout the whole interval of $t$.

At the positive word, for every $t$,

$$
p_t(1^7)=\frac1{64}(49e_0+5e_3+5e_4+5e_7).
\tag{364.8}
$$

The positive row is tight. For an actual $n>7$, (363.8) gives exactly
$\max\{15/64,a_n\}=15/64$, including $a_8=e_*$. At every first-zero-$3$ word the correct deficit is $15/64$ and the law is unchanged by (364.5); actual such sources exist by 363.1. Thus the supremum error is attained at $e_*$, not merely bounded above.

For completeness, the same whole gauge in both coefficient budgets is

$$
g_{23}=t(e_0-e_2),\qquad g_{ij}=0\quad((i,j)\ne(2,3)).
\tag{364.9}
$$

It is $X^{01}-X^{00}$ in the displayed cells. In particular
$r_{23}=te_2$ and $s_{23}=7e_3/64$, so $t_{23}=7/64$ throughout the closed parameter range. Substitution in (364.2), for every pair including zero-$Q$ pairs, yields

$$
\begin{aligned}
U_1&=28e_1/64,&U_2&=(9/64-t)e_0+(2/64+t)e_2,\\
U_3&=11e_0/64,&U_4=U_5&=6e_0/64,\\
U_6&=2e_0/64,&U_7&=0,\\
c&=\sum_iU_i=(34/64-t)e_0+28e_1/64+(2/64+t)e_2,\\
(u_i)_{i=1}^7&=(T_i)_{i=1}^7=(28,11,11,6,6,2,0)/64.
\end{aligned}
\tag{364.10}
$$

Both (364.3) are equalities. They validate this complete $N$ law, without providing any universal score-selection budget.

Realize the table by the single interval seed of 363.3, query its actual two primes, and emit its mark. All $p_t$ executions acquire exactly two replies, even when the first is zero. For $p_*$, stop at that first queried zero and use its common first cell. These constructions have zero advice and finite measurable handoff. The original optimum and its lower bound are reused from XIX 346.1; no new optimality argument is needed. $\square$

## 365. Canonical non-domination and exclusion of every funded odd-list gauge

**Definition 365.1 (Full scores and the equality hull).** For $L\ge3$ let
$y=(A_w,C_w,P_w;T)\ge0$ assign a weight to every row in (363.5). Its word reward at label $z$ is

$$
f_w(z)=A_w\mathbf1_{z=0}+C_w\mathbf1_{z=n(w)}
             +P_w\mathbf1_{z\in\{0,n(w)\}}
\quad(w\ne1^L),\qquad
f_{1^L}(z)=T\mathbf1_{z=0}.
\tag{365.1}
$$

The anchor is $R=O(1,2;1,2,0)$ in stopped-cell order, with event vector $\mathbf r=z(R)$ and amplitude vector $\alpha=(1,1,0,\ldots,0)$. Define

$$
\begin{aligned}
W_y&=y\cdot\mathbf r
 =\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_{w\ne1^L}P_w+T,\\
B_C(y)&=\max_{D\in\mathcal D_C}y\cdot z(D),\qquad
\Delta_C(y)=B_C(y)-W_y\ge0\quad(C=N,O),\\
Q(y)&=(\beta,K),\qquad
\beta_n=\sum_{n(w)=n}(C_w-A_w),\\
K&=\sum_{w\ne1^L}(A_w+C_w+P_w)+T.
\end{aligned}
\tag{365.2}
$$

Here $\mathcal D_C$ is the entire deterministic catalog of 363.3. A unit-$O$ score means $\Delta_O(y)=1$, with no restriction to a basis or normalized total weight. The closed hull is

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\}.
\end{aligned}
\tag{365.3}
$$

For an arbitrary signed $q=(\beta,K)$ put

$$
F_q(b,e)=\sum_{n=1}^L\beta_n(b_n-\alpha_n)-Ke,
\qquad \sigma_{H_L}(q)=\max_{(b,e)\in H_L}F_q(b,e).
\tag{365.4}
$$

These are the full-score and signed-quotient conventions of [IX 207.1–207.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md) and [VI 199.1–199.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md). In particular, for the literal demand vector $d(b,e)$ in (363.6),
$y\cdot(d(b,e)-\mathbf r)=F_{Q(y)}(b,e)$. A signed quotient difference is not required to have a nonnegative score representative.

**Theorem 365.2 (No canonical-event dominator at the optimal $H_7$ profile).** For the family of Theorem 364.2 and

$$
\frac3{40}<t\le\frac5{64},\qquad
\delta_t=\frac{5t-3/8}{37}>0,
\tag{365.5}
$$

there is no $q\in\mathscr O_7$ with $z(q)\ge z(p_t)$ on all $382$ canonical event rows. More precisely, every $q\in\mathscr O_7$ loses at least $\delta_t$ on some row scored below. At $t=5/64$ this loss is at least $1/2368$.

The profile lies in $H_7$, has active length seven and has the same-cap stopped survivor $p_*$ of Theorem 364.2. Thus this is an obstruction to monotonically improving the canonical events of the supplied law; it does not exclude stopped feasibility at that profile.

*Proof.* Its hull coordinates satisfy

$$
b_2=b_3,\qquad
\sum_{j=3}^7b_j-8e_*=\frac{17}{64}\ge0,\qquad
b_1+\sum_{j=3}^7b_j-8e_*=\frac{60}{64}\le1,
\qquad b_7>e_*.
\tag{365.6}
$$

Take the following full nonnegative score $Y$. Every unlisted row, including the positive row, has weight zero; it remains part of (363.6).

| Type | Word | Weight |
| --- | --- | ---: |
| $P$ | 0110101 | 2 |
| $P$ | 0111110 | 3 |
| $C$ | 1000100 | 5 |
| $A$ | 1010010 | 1 |
| $A$ | 1010111 | 1 |
| $A$ | 1011001 | 2 |
| $A$ | 1011100 | 1 |
| $P$ | 1100000 | 2 |
| $P$ | 1101011 | 1 |
| $P$ | 1101101 | 2 |
| $C$ | 1110101 | 4 |
| $P$ | 1110110 | 1 |
| $C$ | 1111010 | 3 |
| $C$ | 1111101 | 5 |
| $C$ | 1111110 | 4 |

The weights sum to $37$. Here is a full all-label support calculation. For each schedule $S$ and cell $c$ set

$$
H_{S,c}=\max_{z\in J_7}\sum_{w:\operatorname{cell}_S(w)=c}f_w(z).
\tag{365.7}
$$

For an $O$ pair the cells are $w_i=0$, $w_i=1,w_j=0$, $w_i=w_j=1$; for an $N$ pair they are $00,01,10,11$. The empty and singleton cells are the same in both catalogs. Every maximum ranges over all eight labels, including earlier and unqueried labels.

| Schedule | $O$ cell maxima | $N$ cell maxima |
| --- | --- | --- |
| empty | $(16)$ | $(16)$ |
| 1 | $(5,11)$ | $(5,11)$ |
| 2 | $(5,11)$ | $(5,11)$ |
| 3 | $(5,11)$ | $(5,11)$ |
| 4 | $(7,9)$ | $(7,9)$ |
| 5 | $(6,10)$ | $(6,10)$ |
| 6 | $(9,7)$ | $(9,7)$ |
| 7 | $(8,8)$ | $(8,8)$ |
| 12 | $(5,5,6)$ | $(0,5,5,6)$ |
| 13 | $(5,5,6)$ | $(0,5,5,6)$ |
| 14 | $(5,5,6)$ | $(2,3,5,6)$ |
| 15 | $(5,6,5)$ | $(0,5,6,5)$ |
| 16 | $(5,7,4)$ | $(2,3,7,4)$ |
| 17 | $(5,5,6)$ | $(3,2,5,6)$ |
| 23 | $(5,5,6)$ | $(5,5,5,6)$ |
| 24 | $(5,5,6)$ | $(5,3,5,6)$ |
| 25 | $(5,3,8)$ | $(3,5,3,8)$ |
| 26 | $(5,6,5)$ | $(5,2,6,5)$ |
| 27 | $(5,6,5)$ | $(5,3,6,5)$ |
| 34 | $(5,5,6)$ | $(5,3,5,6)$ |
| 35 | $(5,3,8)$ | $(3,5,3,8)$ |
| 36 | $(5,5,6)$ | $(5,1,5,6)$ |
| 37 | $(5,6,5)$ | $(5,3,6,5)$ |
| 45 | $(7,3,6)$ | $(3,5,3,6)$ |
| 46 | $(7,5,4)$ | $(5,3,5,4)$ |
| 47 | $(7,4,5)$ | $(5,4,4,5)$ |
| 56 | $(6,5,5)$ | $(4,3,5,5)$ |
| 57 | $(6,5,5)$ | $(3,3,5,5)$ |
| 67 | $(9,5,2)$ | $(5,6,5,2)$ |

The entries are finite sums specified by the fifteen rows and (365.1): at zero sum the relevant $A,P,T$ weights; at label $z>0$ sum the $C,P$ weights with first zero $z$; then maximize these eight numbers within the indicated word cell. For example, in the $00$ cell of $N$ pair $23$ the row $C:1000100:5$ gives maximum $5$ at label $2$, whereas its $01$ cell has maximum $5$ at label $0$ from the four $A$ rows. Merging them into one stopped cell gives maximum $5$, rather than $10$.

For any complete allocation, a cell with owning schedule mass $m_S$ contributes at most $m_SH_{S,c}$. Therefore

$$
Y\cdot z(q)\le\sum_Sm_S\sum_cH_{S,c}
                 \le\max_S\sum_cH_{S,c},\qquad \sum_Sm_S=1.
\tag{365.8}
$$

There is one schedule budget, not a new budget per cell. Every stopped sum is $16$, and the maximal complete $N$ sum is $21$, attained at pair $23$. Choosing a maximizing label independently for each cell defines a single deterministic complete table, so the supports are exactly

$$
B_O(Y)=16,\qquad B_N(Y)=21.
\tag{365.9}
$$

Reversed or repeated finite preselected requests give no additional information beyond the pair or singleton tables already included.

Substitution of the entire law in Theorem 364.2 gives

$$
Y\cdot z(p_*)=\frac{125}{8},\qquad
Y\cdot z(p_t)=\frac{125}{8}+5t.
\tag{365.10}
$$

Only the correct row at $1000100$, of weight $5$, changes in this score. Thus for every $q\in\mathscr O_7$,

$$
Y\cdot(z(p_t)-z(q))\ge5t-\frac38.
\tag{365.11}
$$

A nonnegative weighted average with total weight $37$ forces some scored row loss at least $\delta_t$. The strict range in (365.5) and its endpoint value follow exactly. At $t=3/40$ the displayed gap is zero, so this proof makes no strict assertion there.

For comparison with the unit-score question, the same explicit arithmetic gives

$$
\begin{gathered}
W_Y=16,\quad\Delta_O(Y)=0,\quad\Delta_N(Y)=5,\\
Q(Y)=((0,0,0,4,3,5,4),37),\qquad
Y\cdot d(b,e_*)=\frac{879}{64}<16.
\end{gathered}
\tag{365.12}
$$

This is a zero-cost stopped score. No positive scaling makes it unit-$O$, and it violates no target-demand inequality at this profile. The survivor $p_*$ meets that same profile and cap. $\square$

**Definition 365.3 (The full edge/odd-list cone).** As in [XXI 358.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXI.md#358-alternating-odd-list-replacement), an edge $i<j$ contributes $-B$ to $g_{ij}$, where $m(B)=0$ and $B(z)\ge0$ for $0\le z\le i$. An increasing odd list
$I=(i_1<\cdots<i_{2h+1})$, $h\ge1$, contributes

$$
g_{i_si_t}\mathrel{+}=b_sb_tV\quad(s<t),\qquad
b_s=(-1)^{s+1},\qquad m(V)=0,\qquad
V(z)\ge0\quad(0\le z<i_{2h+1}).
\tag{365.13}
$$

Allow every finite sum, with overlapping lists and edges. Later label coordinates are restricted only by the zero total sum. Funding means (364.3) for the aggregate whole gauge, not separately for individual summands. Length three gives the edge/triangle condition of [XX 351.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XX.md).

**Corollary 365.4 (Every funded representation is excluded).** For every $3/40<t\le5/64$, no whole gauge for the entire kernel $p_t$ both satisfies (364.3) and belongs to the cone of Definition 365.3. This excludes every alternative representation of that kernel, not only the explicit gauge (364.9). The same-cap original stopped survivor remains $p_*$.

*Proof.* If such a gauge existed, [XXI 358.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXI.md) would produce one normalized complete stopped kernel $q$ with all three canonical event coordinates at every zero word at least those of $p_t$, and with $q_{1^7}=p_t(1^7)$ as a whole vector. That is the dominator excluded by Theorem 365.2. The implication uses the same whole gauge in both budgets and allows all odd lists to overlap. The narrower failed edge/triangle representation of XXI 359, whose kernel still has an odd-list representation, does not have this all-representation consequence. $\square$

**Theorem 365.5 (Distance from every original stopped law).** With the entire profile and parameter range of (365.5), every original arbitrary-address, full-carrier $A\in\mathcal O_2$ satisfies

$$
\sup_{x\in X}\operatorname{TV}(\nu_{p_t,x},\nu_{A,x})\ge\delta_t.
\tag{365.14}
$$

In particular the endpoint lower bound is $1/2368$. No original stopped acquisition can weakly dominate all canonical marked-event values of $p_t$ on all actual sources. Nevertheless $e_a(p_*)=e_a(p_t)=e_*$ with $p_*\in\mathcal O_2$; (365.14) is a law-distance assertion and gives no strict target-error separation.

*Proof.* Quantitative distances from all original competitors and resulting risk bounds already occur in [XV 270.1–270.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md). Here the specific canonical-order and every-funded-odd-list obstruction is supplied by (365.11). We apply the original transport of 110.2 and Source-Correlated Laws 45.3 to that score, retaining the following details.

Fix $A$ and let the left side of (365.14) be $d$. Countability of $X$ gives one conull seed set on which its executions are lawful, finish and obey the hard request bound at every actual source. The preselected schedule has at most two addresses on this set: otherwise a finite all-one pattern on its first three requests, realized by 363.1, would force a third actual request. Repeated static addresses do not prevent that all-one pattern. The same finite-pattern argument and the prescribed exhaustion rule exclude an infinite positive schedule. Replace the rule on a null complement by the empty schedule. Its entire maximum selected address $M$ is finite almost surely, so

$$
\gamma_m=\mathsf P\{M>m\}\longrightarrow0.
\tag{365.15}
$$

For each $m\ge8$ choose, before sampling seeds, one actual source $x_{w,m}$ for every $w\in B_7$, with low word $w$ and replies zero at addresses $8,\ldots,m$. The sources vary with $m$; the finite-pattern theorem supplies all $128$ of them for each $m$. Project the full carrier by the measurable map

$$
\pi(\theta_j)=\theta_j\ (1\le j\le7),\qquad
\pi(\tau)=\theta_0\quad\text{for every other tape }\tau.
\tag{365.16}
$$

It fixes the entire law $p_t$ and contracts TV, so the projected law of $A$ at each $x_{w,m}$ is within $d$ of $p_t(w)$.

Since this witness family is finite and handoff is sourcewise almost surely finite, choose a finite transition cutoff $t_m$ for which the late-handoff probability is at most $1/m$ at each of its sources. Simulate the seed-fixed rule with low replies $w$ and fixed higher replies zero through $m$. Output $\theta_0$ if a requested address exceeds $m$, the transition cutoff is exceeded, or a third actual request is attempted. Otherwise project its output by $\pi$. The coupled simulation and the actual execution on $x_{w,m}$ agree unless $M>m$ or handoff is late. The whole-event coupling bound of Source-Correlated Laws 45.3 gives a complete low law $q^{(m)}$ with

$$
\max_{w\in B_7}\operatorname{TV}(q^{(m)}_w,p_t(w))
                                      \le d+\gamma_m+\frac1m.
\tag{365.17}
$$

This simulation remains in $\mathscr O_7$. A low zero stops before a larger high address. On positive low exhaustion, any high continuation has fixed replies. Removing those fixed requests from the finite representation leaves an empty, singleton or increasing low pair schedule. Any repeated static query is redundant in that representation; in the simulated and original executions it is still charged. For a fixed seed the transition cutoff is constant on each stopped low cell, because the acquired transcript there is identical. Thus cutoffs do not split a first-zero cell into its two unqueried continuations. Finite-record measurability gives one probability distribution over the finite complete stopped catalog, not a separate choice of weights for each word.

The simplex of those catalog weights is compact. Pass to a convergent subsequence; its limit defines $q\in\mathscr O_7$, and continuity of all finitely many law coordinates gives
$\max_w\operatorname{TV}(q_w,p_t(w))\le d$. Every canonical row is an event, so

$$
\frac{125}{8}+5t=Y\cdot z(p_t)
                  \le Y\cdot z(q)+37d\le16+37d.
\tag{365.18}
$$

This proves (365.14). If the unprojected original law dominated the three marked events on every actual source, projection could only increase its base and union events and would preserve its correct marked event. The same finite witness families, truncation and compact limit would give a finite canonical dominator, contradicting Theorem 365.2.

The compact convex catalog argument is an application of ordinary finite-dimensional polyhedral theory; see Volker Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1, Theorems 7, 8 and 10](https://arxiv.org/abs/1001.2161v1). The whole-vector comparison viewpoint is also present in David Blackwell, [*Comparison of Experiments* (1951), §§2–3, Theorem 2](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf). Neither general result supplies the paid stopped catalog invariant (365.8); that invariant is the explicit all-cell calculation above. $\square$

## 366. A whole first-zero-fiber hull disjoint from the stopped catalog

**Definition 366.1 (Stochastic input averaging within an entire fiber).** Put

$$
\tau(w)=\begin{cases}\min\{i:w_i=0\},&w\ne1^7,\\8,&w=1^7.\end{cases}
\tag{366.1}
$$

For a kernel $P:B_7\to\operatorname{Prob}(J_7)$, define

$$
\mathcal K(P)=\left\{k:\ k_w=\sum_{v:\tau(v)=\tau(w)}A(w,v)P_v,
\quad A(w,v)\ge0,\quad
\sum_{v:\tau(v)=\tau(w)}A(w,v)=1\right\}.
\tag{366.2}
$$

For each row $w$, the same coefficients $A(w,v)$ multiply every output label. The coefficients may depend on $P$ and the entire profile. No uniformity, deterministic choice or common averaging measure between distinct rows is required. Every suffix in the fiber is allowed. This is an algebraic set of kernels, not a procedure which acquires a free new source or executes the averaging. For arbitrary kernels put

$$
d_\infty(k,q)=\max_{w\in B_7}\operatorname{TV}(k_w,q_w).
\tag{366.3}
$$

**Theorem 366.2 (All stochastic fiber maps of one complete law).** For every
$0<s<1/23$, define

$$
\begin{aligned}
T_w&=\frac12\bigl(e_{2w_1+w_3}+e_{4+2w_2+w_3}\bigr),\\
P_s(w)&=(1-8s)T_w+se_0
                +s\sum_{i=1}^7\bigl((1-w_i)e_i+w_ie_0\bigr).
\end{aligned}
\tag{366.4}
$$

This is a complete normalized $\mathscr N_7$ kernel, and

$$
d_\infty(k,q)\ge\frac{1-23s}{6}>0
\quad\text{for every }k\in\mathcal K(P_s)
\text{ and every }q\in\mathscr O_7.
\tag{366.5}
$$

Consequently $\mathcal K(P_s)\cap\mathscr O_7=\varnothing$. At $s=1/100$ the lower bound is $77/600$.

The assertion concerns the finite full catalog $\mathscr O_7$ and six general law events, not a canonical unit-$O$ score or an arbitrary-address original law-distance extension. Its associated profile

$$
a_1=\cdots=a_7=1-s,\qquad e_s=1-2s,
\qquad a_8\le e_s
\tag{366.6}
$$

with any entire positive ordered vanishing tail is outside $H_7$. Both $P_s$ and the zero-request original stopped law

$$
q^*=(1-7s)e_0+s\sum_{i=1}^7e_i
\tag{366.7}
$$

attain error $e_s$ at that same entire profile. Thus (366.5) is a failure of every fiber-averaging repair of this supplied kernel, with a same-cap stopped survivor.

*Proof.* The complete $N$ allocation has ten schedule types. In a pair, the four output labels are listed in $00,01,10,11$ order; each cell is the owning mass times its listed unit vector.

| Schedule | Owning mass | Complete cell labels |
| --- | --- | --- |
| $(1,3)$ | $(1-8s)/2$ | $(0,1,2,3)$ |
| $(2,3)$ | $(1-8s)/2$ | $(4,5,6,7)$ |
| empty | $s$ | $(0)$ |
| $(i)$, each $1\le i\le7$ | $s$ each | $(i,0)$ |

All masses are positive in the stated range, and their sum is
$(1-8s)+s+7s=1$. This is exactly (366.4), on every word. The single interval-seed construction of 363.3 fixes every complete terminal table in advance; pairs acquire both replies and singletons acquire one. Emitting the actual marks gives an original $\mathcal N_2$ realization without changing advice, requests or handoff. The constant law (366.7) is realized by the empty schedule with one seed and no requests.

We first verify the entire-profile assertion, independently of the separation. At a low first zero $n$, the empty branch of $P_s$ gives $p_w(0)\ge s$, and singleton $n$ gives $p_w(n)\ge s$. The three literal demands are

$$
1-a_n-e_s=3s-1,\qquad a_n-e_s=s,\qquad 1-e_s=2s.
\tag{366.8}
$$

Thus all three rows hold: the negative base demand is retained, the correct coordinate is at least $s$, and their union is at least $2s$. At the positive word,

$$
P_s(1^7)=8se_0+\frac{1-8s}{2}(e_3+e_7),
\tag{366.9}
$$

whose base coordinate exceeds $2s$. At word $1100000$ the two tagged labels in (366.4) are $2,6$, so its label-$3$ mass is exactly $s$; its correct deficit is $a_3-s=e_s$. There is an actual source with that word. This proves attained error $e_s$ on the low fibers.

For $q^*$ the correct coordinate is $s$, its union coordinate is $1-6s\ge2s$, and its base coordinate $1-7s\ge2s$ also meets the positive row. Its correct deficit on each low zero fiber is exactly $e_s$. For every actual $n>7$, the exact tail errors from (363.8) are respectively

$$
\max\{1-8s,a_n\}\le e_s,\qquad
\max\{7s,a_n\}\le e_s.
\tag{366.10}
$$

All the inequalities used here hold for $s<1/23$. They include the closed tie $a_8=e_s$, and include every allowed suffix and every later first absence. The active length is seven, but

$$
8e_s-\sum_{j=3}^7a_j=8(1-2s)-5(1-s)=3-11s>0,
\tag{366.11}
$$

so this prefix/cap fails the defining inequality of $H_7$. At $s=1/100$ one may, for example, take $a_n=(49/50)/(n-7)$ for $n\ge8$; then the prefix is $99/100$ and the cap is $49/50$. No optimum over all preparations is asserted.

For the separation use the six-event functional

$$
S(k)=\sum_{j=1}^6 k_{w^{(j)}}(E_j),
\tag{366.12}
$$

with the following complete fiber minima. The last two columns specify the tagged event probability $T_v(E_j)$ on the entire fiber, and a suffix attaining the minimum stock from the empty and singleton branches.

| $j$ | $w^{(j)}$ | $E_j$ | $\min_{\tau(v)=\tau(w^{(j)})}P_s(v)(E_j)$ | $T_v(E_j)$ | A minimizing $v$ |
| ---: | --- | --- | --- | ---: | --- |
| 1 | 0101111 | $\{0,5,7\}$ | $1/2-s$ | $1/2$ | 0000000 |
| 2 | 0111111 | $\{1,2,4,6\}$ | $1/2-3s$ | $1/2$ | 0111111 |
| 3 | 1001111 | $\{3,4\}$ | $1/2-4s$ | $1/2$ | 1011111 |
| 4 | 1011111 | $\{0,1,2,5,6\}$ | $1/2+s$ | $1/2$ | 1000000 |
| 5 | 1101111 | $\{1,2,6\}$ | $1-8s$ | $1$ | 1101111 |
| 6 | 1111111 | $\{3,7\}$ | $1-8s$ | $1$ | 1111111 |

Here is the full-fiber calculation. For any event $E\subseteq J_7$, the coefficient of $s$ from the empty and seven singleton branches is

$$
C_E(v)=\begin{cases}
\displaystyle\sum_{i\in E}(1-v_i),&0\notin E,\\[2mm]
\displaystyle1+|E\setminus\{0\}|+
        \sum_{i\notin E\setminus\{0\}}v_i,&0\in E,
\end{cases}
\tag{366.13}
$$

where the input sums range over $i\in[7]$. For the six rows, after fixing only the first-zero prefix, these are

$$
\begin{array}{c|c|l|c}
j&\tau(v)&C_{E_j}(v)&\min C_{E_j}\\ \hline
1&1&3+v_2+v_3+v_4+v_6&3\\
2&1&1+(1-v_2)+(1-v_4)+(1-v_6)&1\\
3&2&(1-v_3)+(1-v_4)&0\\
4&2&5+v_3+v_4+v_7&5\\
5&3&1-v_6&0\\
6&8&0&0
\end{array}
\tag{366.14}
$$

Every term bounded below is nonnegative, and the minimizing words in the table attain the bounds. On the first fiber, the two tagged labels are $v_3$ and $4+2v_2+v_3$; each of $E_1,E_2$ contains exactly one of them for either value of $v_3$. On the second fiber the labels are $2+v_3$ and $4+v_3$; each of $E_3,E_4$ again contains exactly one. On the third fiber they are $2,6$, and on the positive fiber they are $3,7$, both in the indicated event. This proves the tagged column for every free suffix, and (366.13)–(366.14) then prove the six displayed minima exactly. For any row-stochastic map in (366.2), convexity within each fiber gives

$$
S(k)\ge4-23s\qquad(k\in\mathcal K(P_s)).
\tag{366.15}
$$

It remains to bound the whole stopped catalog on these general events. For a cell, sum $\mathbf1_{z\in E_j}$ over its selected words and maximize over every $z\in J_7$, exactly as in (365.7). All six selected words have coordinates $4,5,6,7$ equal to one. The full list of schedule types therefore has the following cell maxima:

| Schedule type | Number of schedules | Cell maxima |
| --- | ---: | --- |
| empty | 1 | $(3)$ |
| singleton $i\in\{1,2,3\}$ | 3 | $(1,2)$ |
| singleton $h\in\{4,5,6,7\}$ | 4 | $(0,3)$ |
| pair $(1,2),(1,3),(2,3)$ | 3 | $(1,1,1)$ |
| pair $(i,h)$, $i\le3<h$ | 12 | $(1,0,2)$ |
| pair $(h,k)$, $4\le h<k\le7$ | 6 | $(0,0,3)$ |

This covers all $29$ schedules and every output label. For example, at each low pair its three cells each contain two selected words whose events are disjoint, so their cell maxima are all one. On a low singleton its zero cell has maximum one and its positive cell maximum two. An empty schedule has maximal label reward three. Fixed high replies give exactly the other rows of the table. By the common owning-mass argument (365.8),

$$
S(q)\le3\qquad(q\in\mathscr O_7).
\tag{366.16}
$$

For $d=d_\infty(k,q)$, each of the six event differences is at most $d$, giving

$$
4-23s\le S(k)\le S(q)+6d\le3+6d.
\tag{366.17}
$$

This proves (366.5), including the exact value $77/600$ at $s=1/100$. At $s=1/23$ the bound is zero; no positive separation is asserted there.

The events $E_j$ are general observation-law events and are not the canonical base/correct/union/positive rows. The quantifier in (366.2) excludes every stochastic input averaging within the entire first-zero fiber of this one $N$ kernel. It does not exclude selection confined to $H_L$, selection after changing the initial representative, or an arbitrary same-profile stopped preparation; (366.7) explicitly supplies the last one. It also does not assert an original arbitrary-address extension of (366.5).

The fixed endpoint and common-map repair obstructions of [XV 258](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md) range over terminal assignments of a different repair problem. [XV 266.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md) excludes one uniform averaging of an already stopped kernel, for which the identity map survives. Here the complete initial kernel is fixed and every row-stochastic fiber map is excluded from $\mathscr O_7$. The convexity and support arguments themselves are ordinary finite-dimensional methods, with the concrete complete law and the full-fiber invariant carrying this conclusion. $\square$

## 367. The unrestricted mathematical comparison

**Definition 367.1 (The remaining joint-selection problem).** With the full scores, signed quotients and unchanged closed hull of Definition 365.1, the universal problem is to establish

$$
\begin{gathered}
\text{for every }L\ge3\text{ and every full }y\ge0
\text{ with }\Delta_O(y)=1,\\
\text{there exist one unrestricted full }V\ge0
\text{ and one }\theta\in[0,1]\text{ such that}\\
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}\bigl(Q(y)-Q(V)\bigr)\le\theta.
\end{gathered}
\tag{367.1}
$$

The same $V$ and the same $\theta$ must satisfy both inequalities. The residual $Q(y)-Q(V)$ is signed. Every nonzero zero-cost $V$ with $\Delta_N(V)=0$ remains allowed at $\theta=1$, along with zero weights and the closed endpoints. No prescribed gauge, edge/odd-list cone, fixed partition, basis, normalized-mass slice or preservation of a supplied $N$ law is imposed on this selection.

The alternative sought is one actual entire profile (363.2), one complete original common-seed $A_N\in\mathcal N_2$ attaining a cap $c=e_a(A_N)$, and a strict uniform target-error lower bound

$$
\exists\varepsilon>0\quad\forall A_O\in\mathcal O_2:
                   e_a(A_O)\ge c+\varepsilon.
\tag{367.2}
$$

The quantifier includes all original arbitrary addresses, full-carrier outputs, actual paid requests and measurable sourcewise finite handoffs, at the same profile and its whole tail. This is the original comparison retained in [XIX 347](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIX.md), [XX 356](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XX.md) and [XXI 362](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXI.md). The radial alternatives of [IV 165–168](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md) and the full finite Farkas/certificate alternative of [VI 199.3–199.8](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md) are existing reductions of this problem, not further conclusions of the two obstructions above.

**Definition 367.2 (Mass and target boundaries).** For a mass-$M$ complete allocation the affine anchor convention remains

$$
k_w(E)\ge d_{w,E}(b,e)+(M-1)\mathbf r_{w,E}
\tag{367.3}
$$

on every canonical event. When $M>0$, division by $M$ changes the profile to

$$
b'=\alpha+(b-\alpha)/M,\qquad e'=e/M.
\tag{367.4}
$$

In particular, if $b_2=b_3$, then $b'_2-b'_3=1-1/M$. Thus mass normalization does not preserve the same equality slice or the same demands. This is the affine convention of XIX 341.3 and XXI 358.3; an all-mass conclusion is not implicit in (364.10).

The separately unchanged nonatomic targets $\mu_x$ and the complete-name paid M1 problem remain distinct from selected marked-law accuracy. The complete M1 requirements retain all-$D$ quantification, late requests, authentic indices, actual paid literals and one common all-count bound. A scalar nonnegative expectation representation supplies none of these additional requirements: in Kaniewski, Lee and de Wolf, [*Query complexity in expectation*, arXiv:1411.7280v1, Definitions 6 and 8, Theorem 9](https://arxiv.org/abs/1411.7280v1), the inverse rescales a scalar literal output and bounds maximum supported root-to-leaf depth. It does not impose the normalized labelled vectors, equal counterfactual cell masses or increasing first-zero stopping of 363.3.

**Proposition 367.3 (Same-profile survivors and singular targets).** At every profile of Theorem 364.2, each displayed $p_t$ has an original stopped competitor $p_*$ with exactly the same target error. At every profile of Theorem 366.2, $P_s$ has the original stopped competitor $q^*$ with exactly the same target error. Thus none of these displayed $N$ preparations can be the witness in (367.2). Every constructed preparation law on $J_7$ has TV distance one from every unchanged original nonatomic target.

*Proof.* The first profile has the original stopped survivor $p_*$ at the same inherited optimal cap as every $p_t$. Its score $Y$ has $\Delta_O(Y)=0$ and its demand pairing is below stopped support, by (365.12); it is neither a full unit-$O$ counterexample nor a violation of the demand comparison. Its distance bound compares a competitor's law with a supplied law, and not its error with the common target. Its all-gauge conclusion excludes the sufficient edge/odd-list mechanism for that kernel, without restricting the unrestricted $V$ in (367.1).

The second profile lies outside $H_7$ by (366.11), uses noncanonical events and excludes only the finite fiber hull of a fixed kernel. The constant original stopped $q^*$ attains the very same cap. Thus neither construction gives a strict same-profile all-original-$O$ target-error bound. Nor does either select a joint witness for every full unit-$O$ input and every required horizon. The unrestricted alternatives therefore remain undetermined by these results.

Finally, every constructed preparation law on $J_7$ is supported on the finite set $\{\theta_0,\ldots,\theta_7\}$. Each nonatomic $\mu_x$ gives that set mass zero, while each displayed law gives it mass one. Their TV distance is exactly one. The selected marked targets, rather than $\mu_x$, are precisely the targets in their cap statements. $\square$

## 追加锚（本行以下为增补区）
