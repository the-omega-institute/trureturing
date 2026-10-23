# Self-calibrating acquisition resources XXIII: a shared seven-coordinate witness and complete-cell normal form

## 368. Original resources, complete cells and signed scores

**Definition 368.1 (Original objects and selected laws).** Retain the source, carrier and consumer of [XXII 363.1–363.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXII.md#363-actual-sources-complete-laws-and-canonical-events). Explicitly, with $p_i$ the $i$th prime,

$$
\begin{aligned}
F_0&=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
 \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\}.
\end{aligned}
\tag{368.1}
$$

The integer $N(x)$ is static and has finite prime support. Every finite Boolean pattern, including every multiple-zero pattern and prescribed finite continuation, has an actual source witness by [Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows). This is an existence theorem about sources; it supplies no observation to an acquisition and no probability distribution on $X$.

The original measurable carrier is the Borel disjoint union of interval copies $B_j,P_j$, $j\ge1$. The unchanged consumer returns unknown on $B_j$ and proposes $j$ on $P_j$. Its original nonatomic targets remain $\mu_x$. The distinct measurable marks $\theta_j=(B_1,1/(j+2))$, $j\ge0$, define the separate selected targets

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_i\longrightarrow0,
\qquad
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                    +a_{n(x)}\delta_{\theta_{n(x)}}.
\tag{368.2}
$$

Write $e_j$ for the unit output vector at label $j$. Total variation means $\operatorname{TV}(\nu,\rho)=\sup_E|\nu(E)-\rho(E)|$, with all measurable events allowed. If $\nu_{A,x}$ is the handed-tape law of an original acquisition $A$, its selected-law error is $e_a(A)=\sup_{x\in X}\operatorname{TV}(\nu_{A,x},\lambda_x^a)$.

The original classes $\mathcal N_2,\mathcal O_2$ have zero advice, one source-independent common seed and measurable sourcewise almost-sure finite handoff. Before any reply, the seed fixes the whole schedule and every counterfactual terminal output. Class $\mathcal N_2$ acquires its entire preselected schedule; class $\mathcal O_2$ preselects increasing addresses and stops at its first queried zero or exhaustion. The hard bound is two actual requests, counting repetitions and replies later ignored. Original competitors retain arbitrary addresses and full-carrier outputs. There is no reply-adaptive second address, reset, copy, free observation, second seed, supplied source label or mean-request relaxation. The consumer runs on the same source and handed original tape. These are the resource interfaces of [108.1 and 110.1–110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#108-common-probability-vector-kernels-and-stopped-schedules) and [Source-Correlated Laws 45](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#45-lawful-acquisition-through-one-inherited-seed).

**Definition 368.2 (Complete finite allocations).** For an integer $L\ge0$ put $B_L=\{0,1\}^L$ and $J_L=\{0,\ldots,L\}$. The complete finite $N$ catalog has the empty schedule, every singleton and every pair $i<j$. A pair has cells $00,01,10,11$. The complete finite $O$ catalog instead has pair cells

$$
0=\{w:w_i=0\},\qquad
10=\{w:w_i=1,w_j=0\},\qquad
11=\{w:w_i=w_j=1\}.
\tag{368.3}
$$

A deterministic table assigns an arbitrary label in $J_L$ to every cell. Earlier and unqueried labels are included. A complete allocation assigns a nonnegative vector $X_c\in\mathbb R^{J_L}$ to every terminal cell $c$ of every schedule $s$. All cells of $s$ have its same owning mass $m_s$. The masses, counted once per schedule, sum to a finite $M\ge0$. The whole word vector is

$$
p_w=\sum_s X_{s,\operatorname{cell}_s(w)},\qquad
\sum_{z\in J_L}p_w(z)=M\quad(w\in B_L).
\tag{368.4}
$$

Zero-mass schedules and all their cells are retained as zero vectors. The catalogs include every word, not only words with a single zero. Sorting a static preselected pair merely permutes its complete table; a repeated query has singleton information. These finite representation facts do not erase the charge of an actual repeated or ignored request.

At mass one, the inherited common-table realization partitions one uniform seed interval into schedule masses. Within each interval the same rescaled coordinate supplies every cell's label partition; their finite common refinement fixes the entire table before replies. It introduces no randomness after a reply. This is the allocation/realization interface of [109.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#109-an-exact-coefficient-criterion-with-one-common-probability-budget), [XIX 341.1–341.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIX.md#341-the-complete-preselected-coefficient-cone) and XXII 363.3. We use that interface without requiring preservation of an input allocation's whole law.

**Definition 368.3 (Independent event rows and the affine anchor).** At a zero word let $n(w)=\min\{i:w_i=0\}$. The canonical event vector $z(p)$ has the separate coordinates

$$
z_{A,w}=p_w(0),\quad z_{C,w}=p_w(n(w)),\quad
z_{P,w}=p_w(0)+p_w(n(w)),\quad z_T=p_{1^L}(0).
\tag{368.5}
$$

For $b\in[0,1]^L$ and $e\in\mathbb R$, their literal demand vector $d(b,e)$ is

$$
d_{A,w}=1-b_{n(w)}-e,\quad d_{C,w}=b_{n(w)}-e,\quad
d_{P,w}=1-e,\quad d_T=1-e.
\tag{368.6}
$$

No singleton demand is clipped to zero. The union row is imposed independently. For probability vectors these are exactly the TV cap rows: at first zero $n$,

$$
\operatorname{TV}\bigl(p_w,(1-b_n)e_0+b_ne_n\bigr)
=\max\{1-b_n-p_w(0),\ b_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
\tag{368.7}
$$

Indeed the deficits at $0,n$ sum to the mass outside $\{0,n\}$; the sum of their positive parts is the displayed maximum. The positive-word target is $e_0$. This reuses the event convention of IX 207.1–207.3 and XXII 363.4.

For $L\ge3$ let $R=O(1,2;1,2,0)$ in stopped-cell order, let $r=z(R)$ and put $\alpha=(1,1,0,\ldots,0)$. Then $r=d(\alpha,0)$. For a mass-$M$ allocation the affine demands mean literally

$$
z(p)\ge d(b,e)+(M-1)r,
\qquad z(p)-Mr\ge h(b,e):=d(b,e)-r.
\tag{368.8}
$$

These equivalent forms retain the same anchor. For $M>0$, dividing by $M$ would change the profile to $\alpha+(b-\alpha)/M$ and the cap to $e/M$; that operation is not used below. In particular it changes $b_2=b_3$ into a difference $1-1/M$ between those two normalized coordinates, as in XIX 341.3 and XXII 367.2.

**Definition 368.4 (Full scores and the signed hull).** A full score $y=(A_w,C_w,P_w;T)\ge0$ has a nonnegative real coefficient at every event row in (368.5). Its reward at a zero word and label $z$ is

$$
f_y(w,z)=A_w\mathbf1_{z=0}+C_w\mathbf1_{z=n(w)}
              +P_w\mathbf1_{z\in\{0,n(w)\}},
\qquad f_y(1^L,z)=T\mathbf1_{z=0}.
\tag{368.9}
$$

Unlisted weights are zero, without deleting their rows. With $\mathcal D_N,\mathcal D_O$ the entire deterministic catalogs, define

$$
\begin{aligned}
W_y&=y\cdot r
 =\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
B_C(y)&=\max_{D\in\mathcal D_C}y\cdot z(D),\qquad
\Delta_C(y)=B_C(y)-W_y\ge0\quad(C=N,O),\\
Q(y)&=(\beta,K),\qquad
\beta_j=\sum_{n(w)=j}(C_w-A_w),\qquad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
\tag{368.10}
$$

For a schedule, its support is obtained by summing $f_y$ within each complete cell, maximizing over all labels in that cell, then summing those maxima. Maximizing over all schedules gives $B_C$. The anchor belongs to both catalogs, so both excesses are nonnegative. The complete common-mass bound is

$$
y\cdot\bigl(z(p)-Mr\bigr)\le M\Delta_C(y)
\tag{368.11}
$$

for any mass-$M$ allocation in class $C$. Each cell with owning mass $m_s$ contributes at most $m_s$ times its cell maximum. Sum over cells and schedules and subtract $MW_y$. This proves (368.11) directly, including $M=0$, without normalizing a nonunit allocation.

Use the unchanged closed hull

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\}.
\end{aligned}
\tag{368.12}
$$

For any signed $q=(\beta,K)$ put

$$
F_q(b,e)=\sum_j\beta_j(b_j-\alpha_j)-Ke,\qquad
\sigma_{H_L}(q)=\max_{(b,e)\in H_L}F_q(b,e).
\tag{368.13}
$$

In particular $y\cdot h(b,e)=F_{Q(y)}(b,e)$. Differences of quotients remain signed; they are not replaced by positive parts. These are precisely the score and residual interfaces of [IX 207.2–207.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md) and [XXII 365.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXII.md#365-canonical-non-domination-and-exclusion-of-every-funded-odd-list-gauge).

## 369. The inherited seven-coordinate polytope and its zero-cost generators

**Data interface 369.1 (The complete $H_7$ data).** Write

$$
x=(b_1,b_2,b_4,b_5,b_6,b_7,e),\qquad b_3=b_2.
\tag{369.1}
$$

Let $\mathcal D_7$ be exactly the dataset of [XIX 344.1–344.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIX.md#344-the-exact-seven-coordinate-dataset-and-its-finite-identities): [`calibration238-complete-n-h7/H7-certificate.json`](https://github.com/the-omega-institute/trureturing-experiments/blob/1be64035b2fc5d379ba49b52cb0c402010286922/calibration238-complete-n-h7/H7-certificate.json), schema `research161-H7-complete-normalized-common-allocation-v1`, $2{,}579{,}533$ bytes, SHA256 `621bed2ac570875c2bcb96796338e753ba045c544aa30fb8e1af8702cc94581d`. Rational strings specify exact rational numbers.

Its $481$ rows define $P=\{x:Ax\le B\}$. Rows $0,\ldots,9$, denoted $Dx\le d$, are the ten inequalities defining $H_7$: the descending chain from $b_1\le1$ through $e\le b_7$, then $-e\le0$, then

$$
8e-b_2-b_4-b_5-b_6-b_7\le0,\qquad
b_1+b_2+b_4+b_5+b_6+b_7-8e\le1.
\tag{369.2}
$$

The remaining $471$ rows come from its complete nonnegative cut scores $c_i$, $0\le i<471$. Words are lexicographic with $w_1$ first. Row $3t$, $3t+1$, $3t+2$ carries $A,C,P$ at the $t$th zero word, $0\le t<127$; row $381$ carries $T$ at $1^7$. A sparse weight list specifies a full score in these $382$ slots.

The geometry and lifts are inherited in their entirety: XIX 344.2 supplies all $1606$ vertices of $P$, and at each vertex one complete normalized stopped allocation satisfying every row of (368.6). XIX 345.1 supplies

$$
P=\Pi_{N,7}\cap H_7=\Pi_{O,7}\cap H_7,
\tag{369.3}
$$

where the two $\Pi$ sets mean mass-one complete feasibility. Thus $P$ is nonempty and bounded, and each real $x\in P$ has one simultaneous stopped lift: take one convex combination of its vertex allocations with the same coefficients on every cell and row. This volume does not replace those cuts, their complete geometry, their lifts or the normalized attained region.

**Lemma 369.2 (Zero excess and the exact affine constants).** Every full cut score $c_i$ of $\mathcal D_7$ satisfies $\Delta_N(c_i)=0$. There is a positive rational $\kappa_i$ such that, for $\widehat c_i=\kappa_i c_i$,

$$
A_{10+i}x-B_{10+i}=F_{Q(\widehat c_i)}(x),
\qquad
P=H_7\cap\bigcap_{i=0}^{470}\{F_{Q(\widehat c_i)}\le0\}.
\tag{369.4}
$$

*Proof.* The following gives the finite arithmetic verification directly from the specified score lists. For each list form $f_i=f_{c_i}$ by (368.9), and accumulate

$$
C_i^0=\sum_w(A_w+P_w)+T,\qquad
\beta_j^i=\sum_{n(w)=j}(C_w-A_w),\qquad
K_i=\sum_w(A_w+C_w+P_w)+T.
\tag{369.5}
$$

The anchor identity, obtained by separating $n\le2$ from $n\ge3$, is

$$
W_i=C_i^0+\beta_1^i+\beta_2^i.
\tag{369.6}
$$

For every one of the $29$ schedules $S=\varnothing,(j),(j,k)$, $j<k$, and each complete $N$ cell $a$, compute

$$
t_{i,S,a,z}=\sum_{w:\operatorname{cell}_S(w)=a}f_i(w,z),\qquad
v_{i,S}=\sum_a\max_{0\le z\le7}t_{i,S,a,z}.
\tag{369.7}
$$

For the empty schedule there is one cell; for a singleton there are two; for a pair there are four. These finite sums include all eight labels. Substitution of all $471$ weight lists gives the exact identities

$$
\begin{gathered}
\bigl(\max_z t_{i,(j,k),ab,z}\bigr)_{ab=00,01,10,11}
       =\text{the recorded pair cell maxima},\\
\max_{S}v_{i,S}=\text{the recorded }BN_i
       =C_i^0+\beta_1^i+\beta_2^i=W_i
       \qquad(0\le i<471).
\end{gathered}
\tag{369.8}
$$

This is an exhaustive finite identity: the indices in (369.7) range over every supplied list, all $29$ schedules, all its cells and every label. Equivalently, to check each maximum one sums the listed weights whose row event contains $z$ and whose word has the indicated one or two bits; there is no unlisted schedule optimization. The $21$ pair tables for each score give $9891$ four-entry comparisons, and the eight empty/singleton supports are included in the maximum. Reversal only permutes cells and repeated static queries give singleton information. Consequently (369.8) is exactly $B_N(c_i)=W_i$, proving zero excess.

To verify the affine constant as well as the normal, set

$$
a_i=(\beta_1^i,\beta_2^i+\beta_3^i,
       \beta_4^i,\beta_5^i,\beta_6^i,\beta_7^i,-K_i),
\qquad t_i=\beta_1^i+\beta_2^i.
\tag{369.9}
$$

The recorded primitive row is a positive multiple of
$(a_i,BN_i-C_i^0)=(a_i,t_i)$. Clearing denominators and dividing by the positive greatest common divisor gives exactly

$$
A_{10+i}=\kappa_i a_i,\qquad B_{10+i}=\kappa_i t_i.
\tag{369.10}
$$

The positive scales, grouped to specify their full finite range, are

| $\kappa_i$ | Number of scores |
| ---: | ---: |
| $1$ | 237 |
| $1/2$ | 128 |
| $1/3$ | 43 |
| $1/4$ | 20 |
| $1/5$ | 9 |
| $1/6$ | 16 |
| $1/7$ | 1 |
| $1/8$ | 6 |
| $1/9$ | 3 |
| $1/10$ | 2 |
| $1/12$ | 3 |
| $1/14$ | 2 |
| $1/15$ | 1 |

Their counts sum to $471$. Equations (369.9)–(369.10) give
$A_{10+i}x-B_{10+i}=\kappa_i(a_i\cdot x-t_i)=F_{Q(\widehat c_i)}(x)$. The first ten rows define $H_7$, so the second equality of (369.4) follows. This calculation uses the complete content-defined data and the support formula; the vertex enumeration and stopped lifts remain the inherited XIX 344.2 result. $\square$

## 370. One common score witness on the whole seven-coordinate hull

**Theorem 370.1 (Full-score shared witness at $H_7$).** For every full real nonnegative seven-coordinate score $y$ with $\Delta_O(y)=1$, there exists one full $V\ge0$ such that

$$
\Delta_N(V)=0,\qquad
\sigma_{H_7}\bigl(Q(y)-Q(V)\bigr)\le1.
\tag{370.1}
$$

Thus the same pair $(V,\theta)$ with $\theta=1$ satisfies

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_7}\bigl(Q(y)-Q(V)\bigr)\le\theta.
\tag{370.2}
$$

There is no restriction on $y$ to a score basis, a gauge or a fixed total weight. The selected $V$ may be nonzero at $\theta=1$.

*Proof.* Write

$$
a_y=(\beta_1,\beta_2+\beta_3,\beta_4,\beta_5,\beta_6,\beta_7,-K),
\qquad t_y=\beta_1+\beta_2,
\qquad F_{Q(y)}(x)=a_y\cdot x-t_y.
\tag{370.3}
$$

For each $x\in P$, use its one normalized stopped lift $p^x$ from Data interface 369.1. All event rows of that same allocation satisfy $z(p^x)\ge d(x)$. Nonnegative pairing and (368.11) give

$$
F_{Q(y)}(x)=y\cdot(d(x)-r)
 \le y\cdot(z(p^x)-r)\le\Delta_O(y)=1.
\tag{370.4}
$$

Hence $a_y\cdot x\le1+t_y$ is valid on the actual nonempty finite polyhedron $P=\{Ax\le B\}$. Apply finite valid-inequality duality, in the form of [Kaibel, *Basic Polyhedral Theory*, arXiv:1001.2161v1, Theorem 12](https://arxiv.org/abs/1001.2161v1). Its hypotheses are precisely a nonempty finite real inequality polyhedron and validity of this one inequality; no strict feasibility is required. It gives one vector

$$
\Lambda\in\mathbb R_{\ge0}^{481},\qquad
A^{\mathsf T}\Lambda=a_y,\qquad B^{\mathsf T}\Lambda\le1+t_y.
\tag{370.5}
$$

Use that same vector to define

$$
V=\sum_{i=0}^{470}\Lambda_{10+i}\widehat c_i,
\qquad \theta=1.
\tag{370.6}
$$

It is a full nonnegative score. By Lemma 369.2 and linearity of $Q$, at every $x\in H_7$ the signed residual is exactly

$$
\begin{aligned}
F_{Q(y)-Q(V)}(x)
 &=a_y\cdot x-t_y
       -\sum_i\Lambda_{10+i}(A_{10+i}x-B_{10+i})\\
 &=\sum_{j=0}^{9}\Lambda_j(D_jx-d_j)
                         +B^{\mathsf T}\Lambda-t_y\\
 &\le B^{\mathsf T}\Lambda-t_y\le1.
\end{aligned}
\tag{370.7}
$$

The domain terms are nonpositive because $x\in H_7$ and $\Lambda\ge0$. Thus one $V$, selected from $y$ before $x$ is varied, works simultaneously at every hull point. No residual coefficient has been clipped or given an independent allowance.

For any complete deterministic $N$ table $D$, Lemma 369.2 gives

$$
V\cdot(z(D)-r)
 =\sum_i\Lambda_{10+i}\widehat c_i\cdot(z(D)-r)\le0.
\tag{370.8}
$$

The paid $N$ completion of $R$ is in this catalog and makes the same expression zero. Taking the maximum over the full catalog therefore gives $\Delta_N(V)=0$. Equations (370.7)–(370.8) prove both inequalities with the same $V$ and $\theta=1$. If $y$ is rational, (370.5) is a nonempty rational linear system and admits a rational solution by rational polyhedral elimination; this supplies a rational $V$. No efficiency bound is inferred. $\square$

**Theorem 370.2 (Literal finite-mass feasibility implies a normalized stopped lift).** Let $x=(b,e)\in H_7$. Suppose some complete $N$ allocation of finite mass $M\ge0$ satisfies every literal affine demand

$$
z(p)\ge d(x)+(M-1)r.
\tag{370.9}
$$

Then $x\in P$, and one complete mass-one $O$ allocation satisfies all rows $z(q)\ge d(x)$. There is also a complete affine $O$ allocation of mass $M'=\max\{1,M\}$ satisfying

$$
z(q')\ge d(x)+(M'-1)r.
\tag{370.10}
$$

The implication includes the algebraic case $M=0$; it does not assert mass $M$ for $M<1$.

*Proof.* Subtract $Mr$ in (370.9). For each full nonnegative cut score, the same allocation and (368.11) give

$$
F_{Q(\widehat c_i)}(x)
 =\widehat c_i\cdot h(x)
 \le\widehat c_i\cdot(z(p)-Mr)
 \le M\Delta_N(\widehat c_i)=0.
\tag{370.11}
$$

Every cut inequality holds. Together with $x\in H_7$, (369.4) gives $x\in P$. The inherited simultaneous lift on $P$ supplies $q$ of mass one. Set $q'=q+(M'-1)R$ as an addition of complete allocations. Its mass is $M'$, it is stopped, and

$$
z(q')=z(q)+(M'-1)r\ge d(x)+(M'-1)r.
\tag{370.12}
$$

The added anchor has zero column after subtraction of its mass times $r$. No division by $M$, profile change or independent row optimizer occurs, including when $M=0$. $\square$

**Limit 370.3 (The hull is not itself feasible).** The point
$u_3=(1/2,1/2,1/2,0,0,0,0;0)$ belongs to $H_7$. Cut $0$ of the specified dataset has $F_{Q(\widehat c_0)}=b_3-b_6-4e$, which is $1/2$ there. Thus $u_3\notin P$. Any execution consequence of Theorem 370.2 requires its affine $N$ witness, or independently established membership in $P$; membership in $H_7$ alone is insufficient.

The lower-horizon conclusions for $L=3,4,5,6$ already follow from [III 160.1 and 162.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_III.md), their zero-cost prefix cuts and stopped synthesis, together with existing finite duality and padding/restriction. They are reused lower-horizon facts. The bridge developed in Theorems 370.1–370.2 is at $H_7$; neither theorem asserts a result at $L\ge8$ or outside the stated equality slice.

## 371. A one-pass normal form for every finite complete catalog

**Definition 371.1 (Arbitrary literal demands).** Fix any finite $L\ge0$, either complete class $N$ or $O$, and finite mass $M\ge0$. At every zero word prescribe arbitrary real numbers $d_A(w),d_C(w),d_P(w)$, and prescribe $d_T\in\mathbb R$ at $1^L$. Feasibility means

$$
p_w(0)\ge d_A(w),\qquad
p_w(n(w))\ge d_C(w),\qquad
p_w(0)+p_w(n(w))\ge d_P(w),\qquad
p_{1^L}(0)\ge d_T.
\tag{371.1}
$$

In particular these demands include (368.6) and the literal mass-$M$ affine vector (368.8), with no restriction on the signs of singleton demands. The demands remain fixed throughout the following construction.

**Theorem 371.2 (Complete-cell normal form with persistent tight witnesses).** Every feasible complete allocation for (371.1) has a feasible representative in the same class with exactly the same individual schedule masses such that each final positive nonbase cell entry $X_c(n)>0$, $1\le n\le L$, has a witness word $w$ satisfying

$$
w\text{ visits }c,\qquad n(w)=n,\qquad p_w(n)=d_C(w)
\quad\text{in the final allocation}.
\tag{371.2}
$$

Processing every complete terminal cell once, in any order, constructs such a representative. During the whole pass every nonbase cell entry and every nonbase word coordinate weakly decrease; every base word coordinate and every applicable union coordinate $p_w(0)+p_w(n(w))$ weakly increase.

*Proof.* Enumerate the finitely many cells in any order. Consider the current cell $c$, with owning mass $m$, current vector $X_c$ and visiting word set $\mathcal C_c$. For $w\in\mathcal C_c$ put $k_w=p_w-X_c$. This is the contribution from all other schedules at that word and is held fixed during this update. For $n=1,\ldots,L$ set

$$
a_n=\max\bigl(\{0\}\cup
 \{d_C(w)-k_w(n):w\in\mathcal C_c,\ n(w)=n\}\bigr).
\tag{371.3}
$$

If no such word exists, $a_n=0$. Current feasibility gives
$d_C(w)-k_w(n)\le X_c(n)$ for every word in that maximum, and $X_c(n)\ge0$. Hence

$$
0\le a_n\le X_c(n),\qquad
\sum_{n=1}^L a_n\le\sum_{n=1}^L X_c(n)\le m.
\tag{371.4}
$$

Replace this one cell by

$$
X_c^{\mathrm{new}}(n)=a_n\ (n>0),\qquad
X_c^{\mathrm{new}}(0)=m-\sum_{n=1}^L a_n.
\tag{371.5}
$$

It is nonnegative and has the same owning mass. Every other cell of this schedule keeps its old mass $m$, and all other schedules are unchanged. Thus every schedule budget remains exactly the same.

Put $\delta_n=X_c(n)-a_n\ge0$. At a visiting zero word with first zero $n$, the new correct entry satisfies its literal demand by (371.3). The base gain and the actual union gain are respectively

$$
p_w^{\mathrm{new}}(0)-p_w(0)=\sum_{j=1}^L\delta_j,\qquad
\bigl(p_w^{\mathrm{new}}(0)+p_w^{\mathrm{new}}(n)\bigr)
 -\bigl(p_w(0)+p_w(n)\bigr)
 =\sum_{j\ne n}\delta_j\ge0.
\tag{371.6}
$$

Therefore the base and independently imposed union demands remain satisfied. The positive word, if it visits $c$, only gains base mass. Words not visiting $c$ do not change. This proves feasibility after each update without deducing the union row from singleton estimates. It also proves all claimed monotonicities, including with negative demands and at equality.

If $a_n>0$, the finite maximum in (371.3) is attained by a word $w$ with $n(w)=n$, since its zero option cannot attain a positive value. Immediately after this update,

$$
p_w^{\mathrm{new}}(n)=k_w(n)+a_n=d_C(w).
\tag{371.7}
$$

Every subsequent cell update weakly decreases this word's nonbase coordinate and preserves its lower bound $d_C(w)$. A quantity already equal to that bound cannot decrease further while remaining feasible. It therefore stays equal through every later update. The processed cell is never changed again, so any positive entry retained in it has the same witness in the final allocation. Apply this argument to each processed cell. This proves (371.2) after one pass.

For $L=0$ there are no nonbase entries; the only cell is the empty base vector and the assertion is immediate. At $M=0$ all cell vectors vanish; feasibility and the same formulas give the zero allocation without division. Zero-mass schedules, absent first-zero classes within a cell, multiple-zero words and closed ties are all covered. The proof uses only each cell's visiting set and common owning mass, so it applies to both complete catalogs. $\square$

**Interpretation 371.3 (Actual correct slack).** At a word with first zero $n$, the full reduction of its correct coordinate is at most its initial slack $p_w(n)-d_C(w)$, because its final value still meets $d_C(w)$. Formula (371.6) states the union gain using that word's actual entries. This is a use of the signed transfer and actual-slack accounting of [XV 258.1–258.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md#258-signed-event-transfer-actual-slack-and-universal-common-input-maps). The additional assertion here is the all-cell pass and persistence of the final tight witnesses.

The pass is a construction on the complete feasible allocation set. It can change its entire output law and depends on the processing order; no uniqueness is asserted. It keeps an $N$ allocation in $N$ and an $O$ allocation in $O$. It neither identifies $00$ with $01$ nor converts $N$ into $O$. An earlier or unqueried label remains whenever its tight witness requires it. Counting one update per cell supplies no polynomial-time bound: each maximum in (371.3) ranges over the complete finite set of visiting words. Those words are used for offline mathematical construction, not acquired for free during an execution.

## 372. A reused shared-cell calculation and its fixed-complement application

**Reused calculation 372.1 (One shared vector and one budget).** Let $\mathcal C\subseteq B_L$ be a finite affected word set. A single vector $x\ge0$ of prescribed mass $m\ge0$ is to contribute at every $w\in\mathcal C$. The complementary contributions $k_w$ are fixed. All words outside $\mathcal C$ are fixed as well; if whole-allocation feasibility is sought, their rows must already hold. Put

$$
I=\{n(w):w\in\mathcal C,\ w\ne1^L\},
\tag{372.1}
$$

and define

$$
\begin{aligned}
A&=\max\bigl(\{0\}\cup\{d_A(w)-k_w(0):w\in\mathcal C,\ w\ne1^L\}
 \cup\{d_T-k_{1^L}(0):1^L\in\mathcal C\}\bigr),\\
c_n&=\max\bigl(\{0\}\cup\{d_C(w)-k_w(n):w\in\mathcal C,\ n(w)=n\}\bigr),\\
u_n&=\max\{d_P(w)-k_w(0)-k_w(n):w\in\mathcal C,\ n(w)=n\}
 \quad(n\in I).
\end{aligned}
\tag{372.2}
$$

The conditional set in the first line contributes an element only if the positive word belongs to $\mathcal C$. Each maximum defining $u_n$ is over a nonempty finite set; $u_n$ remains signed. There is one such shared $x$ satisfying all affected rows if and only if

$$
\sum_{n\in I}c_n+
 \max\bigl(\{A\}\cup\{u_n-c_n:n\in I\}\bigr)\le m.
\tag{372.3}
$$

For $I=\varnothing$ this means $A\le m$. A feasible selector is

$$
x(n)=c_n\ (n\in I),\qquad
x(n)=0\ (n>0,\ n\notin I),\qquad
x(0)=m-\sum_{n\in I}c_n.
\tag{372.4}
$$

*Proof of the reused calculation.* Any feasible vector has $x(0)\ge A$ and $x(n)\ge c_n$. Consequently

$$
m\ge A+\sum_{n\in I}c_n.
\tag{372.5}
$$

For each $n\in I$, its union rows also give $x(0)+x(n)\ge u_n$. The same vector and total mass therefore satisfy

$$
m\ge x(0)+x(n)+\sum_{j\in I\setminus\{n\}}c_j
 \ge u_n+\sum_{j\in I\setminus\{n\}}c_j.
\tag{372.6}
$$

These simultaneous inequalities are exactly (372.3). Nonnegative mass on unused labels cannot weaken them.

Conversely (372.3) implies $m-\sum c_n\ge A\ge0$, so (372.4) is nonnegative of mass $m$ and meets all base, correct and applicable positive demands. For each $n\in I$ it gives

$$
x(0)+x(n)=m-\sum_{j\in I\setminus\{n\}}c_j\ge u_n,
\tag{372.7}
$$

which meets every independent union demand. Thus one vector meets every affected row at once. Empty $\mathcal C$, positive-word-only $\mathcal C$, negative demands, zero mass and ties need no separate limiting argument. $\square$

This is finite simplex elimination, used here as a proof tool. The same completion formula and pair-$23$ calculation occur in the mathematical supplier `shared_reserve_exact.py`, content SHA256 `68c71f7fee2cdd46b6d9e875e919fb1107fefb819a915824eff5e1caff93d5b7`, in `trureturing-experiments/calibration176-6ad1d8cacdf886317e33c9e4-attempt-1-proportional-containment`. The direct proof fixes its complete-cell interpretation and gives it no separate new-result or attainment claim. Finite coordinate elimination is mature polyhedral mathematics; compare Kaibel, arXiv:1001.2161v1, Theorem 18.

**Application 372.2 (Merging one first cell with its complement fixed).** For one supplied $N$ pair $i<j$, keep its $10,11$ cells, its owning mass $m$, every other cell and every other schedule mass fixed. On $\mathcal C=\{w:w_i=0\}$ subtract the visited old $00$ or $01$ vector to obtain $k_w$. Then (372.3) is necessary and sufficient for replacing both old first cells by one stopped first vector of the same mass. Indeed this is exactly the shared-vector problem above, and words outside $\mathcal C$ are unchanged. Here $I=\{1,\ldots,i\}$: earlier unqueried first-zero labels are retained. Failure only rules out this frozen-complement merger. Other cells or masses may need to change in a search for a stopped allocation.

**Calibration 372.3 (The inherited $p_t$ family).** Use the complete family of [XXII 364.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXII.md#364-a-complete-perturbation-at-the-inherited-optimal-profile), at

$$
b=(43,34,34,29,27,25,22)/64,\qquad e=15/64,\qquad 0\le t\le5/64.
\tag{372.8}
$$

Its pair $23$ has mass $7/64$, first cells

$$
X^{00}=(5/64-t)e_0+(2/64+t)e_2,\qquad
X^{01}=(5e_0+2e_2)/64,
\tag{372.9}
$$

and all other pairs already have coincident first cells. The whole law satisfies
$p_t=p_*+t(1-w_2)(1-w_3)(e_2-e_0)$, where $p_*$ is the stopped law of XIX 346.1. Removing the actually visited vector in (372.9) cancels the entire $t$ term from $k_w$ on $\mathcal C=\{w:w_2=0\}$. Thus the fixed complement is the same for every real $t$ in the full closed interval.

For completeness, the residual thresholds can be obtained without assuming a merger outcome. On $\mathcal C$ the first zero is $1$ or $2$. The inherited table gives

$$
p_*(w)(1)=28/64\quad(n=1),\qquad
p_*(w)(2)=19/64\quad(n=2).
\tag{372.10}
$$

The minimum base coordinates on these two restricted word sets are respectively $21/64$ and $30/64$. Here is a direct check from the explicit polynomial XXII (364.6). Put $u=w_4,v=w_5,z=w_6,r=w_7$. For $w_1=w_2=0$, its base numerator is

$$
34-11w_3-6u-6v-2z+4w_3u+4w_3v+2w_3z
       +4uv+2uz+2vz+2zr.
\tag{372.11}
$$

For $w_1=1,w_2=0$, add $7w_3+2u+2v$. Minimize first over $r$, whose coefficient is nonnegative, then over $z$ and the four possibilities for $(u,v)$. The minima are

| $w_3$ | $64p_*(w)(0)$, $w_1=w_2=0$ | $64p_*(w)(0)$, $w_1=1,w_2=0$ |
| ---: | ---: | ---: |
| 0 | 26 | 30 |
| 1 | 21 | 30 |

Thus the two claimed minima hold over every affected suffix; $0011001$ and $1011001$ attain them. Subtracting the shared vector $(5e_0+2e_2)/64$ gives

$$
\begin{array}{c|c|c|c|c}
n&d_C&k_w(n)&\min k_w(0)&d_A\\ \hline
1&28/64&28/64&16/64&6/64\\
2&19/64&17/64&25/64&15/64
\end{array}
\tag{372.12}
$$

The independent union demand is $49/64$ for both classes. Therefore (372.2) gives exactly

$$
A=0,\qquad(c_1,c_2)=(0,2/64),\qquad
(u_1,u_2)=(5/64,7/64).
\tag{372.13}
$$

Its required mass is $2/64+\max\{0,5/64,5/64\}=7/64$. The shared selector is consequently $(5e_0+2e_2)/64$. Within this fixed-complement problem it is forced: $x(0)+x(2)\ge7/64$ exhausts the available mass, so all other labels vanish; the first-zero-$1$ union requires $x(0)\ge5/64$, and the correct row requires $x(2)\ge2/64$. Both are equalities. Replacing the two first cells therefore recovers exactly the inherited $p_*$ for every $t$, with every owning mass unchanged. Its profile, optimum and original attainer remain those of XIX 346.1 and XXII 364.2. This is an application of a reused tool, not a new attainment result.

**Limit 372.4 (A merger need not be affordable).** At $L=3$, take a mass-one $N$ pair $(2,3)$ with cell labels $(2,0,0,0)$ in $00,01,10,11$ order. Prescribe only $d_C(100)=1$ and $d_A(001)=1$, with all other demands zero. This complete allocation is feasible. Merging its first cells while keeping the complement fixed would require both $x(2)\ge1$ and $x(0)\ge1$, impossible at mass one. Nevertheless the stopped pair $(1,2)$ with labels $(0,2,0)$ meets those same demands. A failed merger is therefore not an all-$O$ obstruction, and Theorem 371.2 gives no universally successful merger order.

Separate row affordability also cannot replace the common-vector test: $m=1$, $A=0$, $c_1=c_2=1/2$, $u_1=u_2=1$ has an affordable correct pair and an affordable union row for each label separately. Jointly (372.3) requires mass $3/2$. The same budget must fund all rows.

## 373. Conditional original-source interpretation and remaining obligations

**Inherited interpretation 373.1 (Positive caps and the actual entire tail).** Let $a$ be an entire sequence (368.2), let $0<e\le1$, and suppose $a_{L+1}\le e$. A normalized complete finite allocation satisfying every row at $b=(a_1,\ldots,a_L)$ executes in its own original class using the common seed of Definition 368.2. If it is a stopped allocation, select one increasing schedule before replies and stop at its first queried zero. If it is an $N$ allocation, acquire both requests of a selected pair, including any reply that the table then ignores. Every emitted label names its actual original mark, and handoff is finite and measurable.

For an actual first absence $n\le L$, the full low word satisfies all three independent cap rows. For an actual $n>L$, the low word is $1^L$ and no tail mark is emitted. If $v=p_{1^L}$, the mass deficit at $0$ is $1-a_n-v(0)$ and the missing tail mass is $a_n$. Summing the positive deficits yields the exact identity

$$
\operatorname{TV}\left(\sum_{j=0}^Lv(j)\delta_{\theta_j},
          (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =a_n+\max\{1-a_n-v(0),0\}
 =\max\{1-v(0),a_n\}\le e.
\tag{373.1}
$$

The positive row supplies $1-v(0)\le e$ and the ordered tail supplies $a_n\le e$. This includes $a_{L+1}=e$ and all later ties, without summability. The finite positive word is not an infinite all-positive source. This is the reused realization and transport of 109.1–110.2 and Source-Correlated Laws 45; no evaluation of all Boolean words is performed as a source observation.

In particular, for an entire sequence (368.2), a positive cap $e$, $a_8\le e$ and prefix $(a_1,\ldots,a_7,e)\in H_7$, either membership of that prefix in $P$ or a complete finite affine $N$ witness as in Theorem 370.2 supplies a normalized finite stopped lift and hence an original $\mathcal O_2$ acquisition of error at most $e$. These feasibility premises are essential. If also $a_7>e$, the active length is seven; the arbitrary-address, full-carrier necessity theorem 110.2 and XIX 345.2 identify original $N$ feasibility with membership in $P$ and thus with original $O$ feasibility there. This last normalized original equivalence is inherited.

Theorem 371.2 has the same conditional execution interpretation only when its input is a normalized feasible finite allocation with an entire positive ordered vanishing profile, positive cap and $a_{L+1}\le e$. It then produces another actual acquisition in that same class. At $M\ne1$, its conclusion and Theorem 370.2's padded conclusion are statements about literal affine allocations; division does not turn them into acquisitions for the same profile. The closed finite boundary $e=0$ in $H_7$ supplies no positive-tail zero-error rule.

**Open problem 373.2 (Beyond the seven-coordinate bridge).** With Definitions 368.3–368.4, the unrestricted joint-selection obligation still asks, at every $L\ge8$ and every full $y\ge0$ with $\Delta_O(y)=1$, for one unrestricted full $V\ge0$ and the same $\theta\in[0,1]$ such that

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}\bigl(Q(y)-Q(V)\bigr)\le\theta.
\tag{373.2}
$$

Signed residuals, nonzero zero-cost $V$ at $\theta=1$, zero weights and both endpoints remain allowed. Theorem 370.1 uses the specific complete $H_7$ data; Theorem 371.2 does not supply zero-cost generators or universal cell-merger feasibility at larger horizons.

The alternative remains one actual entire profile (368.2), one complete common-seed original $A_N\in\mathcal N_2$ attaining $c=e_a(A_N)$, and a strict uniform lower

$$
\exists\varepsilon>0\quad\forall A_O\in\mathcal O_2:
                   e_a(A_O)\ge c+\varepsilon,
\tag{373.3}
$$

against all original arbitrary-address and full-carrier competitors at that same profile and entire tail. A fixed-law obstruction, failed merger, absence of a funded gauge or loss of exact-law preservation does not establish (373.3). The inherited $p_*$ explicitly prevents the $p_t$ calibration from being such a separator. The complete radial and Farkas reductions of IV 165–168 and VI 199 retain their own hypotheses and do not by themselves settle either remaining alternative.

The original nonatomic targets and the complete-name paid M1 requirements also remain separate: all-$D$ quantification, late requests, authentic indices, actual paid literals and one common all-count bound are unchanged. Every finite marked construction here is supported on a finite set of $\theta_j$. Any unchanged nonatomic $\mu_x$ gives that set mass zero, so the corresponding TV distance is one. Selected-law accuracy therefore gives no nonatomic-target accuracy or paid M1 conclusion.

## 374. Mathematical dependencies and reuse boundaries

The complete source, carrier, seed and event interfaces are 108–110, IX 207.1–207.3, Source-Correlated Laws 45 and XXII 363–367. Complete realizability and the stopped inverse are 109.1 and XIX 341.2. The $471$ cut scores, $481$ rows, $1606$-vertex geometry and simultaneous stopped lifts are precisely XIX 344–345 and the content-defined $\mathcal D_7$. They are used as inherited mathematical data, not as new geometry or a new attained region. Lemma 369.2 supplies their zero-$N$-excess identity and the exact affine constants needed for the shared-witness and finite-mass arguments.

The lower $L=3,\ldots,6$ prefix-cone results are III 160.1/162.2. The special score $Y$ of XXII 365.2 is already absorbed by the protected-core payer of [XVI 282.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md): its late totals are $(0,4,3,5,4)$, $G=16$, $\mu=5$ and $K=G+21\mu/5=37$. No separate score-ray result is inferred from renaming that application. XVI 294–295 remain scoped existing suppliers.

XV 258 supplies signed transfer and actual-slack accounting. XX 350 supplies sufficient face deletion; XX 351 and XXI 358 supply funded domination under their explicit gauge hypotheses. Theorem 371.2 instead states the complete-cell pass and final persistent correct-row witnesses, without requiring domination of the original correct coordinates. The shared-cell formula and pair-$23$ calculation in §372 are reused tools; XIX 346 and XXII 364 supply the profile, stopped survivor and optimum. None of these attributions implies an exhaustive repository or literature priority claim.

Volker Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1](https://arxiv.org/abs/1001.2161v1), Theorem 12, provides the finite valid-inequality multiplier theorem used in (370.5). Its nonempty-polyhedron and validity hypotheses are verified there for the actual $P$ and the full score. Theorem 18 gives finite elimination background. These general results supply neither the concrete cuts and lifts nor an acquisition protocol.

David Blackwell, [*Comparison of Experiments* (1951), §§2–3, Theorem 2](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf), compares entire attainable loss vectors for finite families of measures on a Borel field with bounded finite-dimensional action/loss sets. That is a comparison viewpoint, not a hard-two stopped-query converse and not a probability law on this source. No such converse is used above.

Kaniewski, Lee and de Wolf, [*Query complexity in expectation*, arXiv:1411.7280v1, Definitions 6 and 8, Theorem 9](https://arxiv.org/abs/1411.7280v1), treats nonnegative scalar expectations and maximum supported root-to-leaf depth. Its scalar rescaling does not supply normalized labelled vectors, equal counterfactual cell masses, increasing first-zero stopping or the separate paid M1 requirements. The common masses and actual hard-two execution here use the explicit complete-table interface, not a mean-budget or scalar-output substitution.

## 追加锚（本行以下为增补区）
