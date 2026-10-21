# FIB atoms: categorical decision blindness under legal-toggle support

## 1. Five windows, finite readouts and the support contract

**定义 1.1（五窗、指标与分类风险）。** Use the low-to-high three-bit coordinates of [the FIB ML volume, Definition 2.1](FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md):

$$
(a,b,c,d,e)=(000,100,010,101,001).
$$

Let $S$ be a finite probability space and $C:S\to\{a,b,c,d,e\}$, $Q:S\to\mathcal Q$ deterministic maps. Write

$$
\begin{aligned}
p_i&=\Pr(C=i),&\lambda_q&=\Pr(Q=q),&
v_i(q)&=\Pr(C=i\mid Q=q),\\
r_i&=\mathbb E\min(v_i(Q),1-v_i(Q)),&
\epsilon&=\mathbb E(1-\max_iv_i(Q)),&
I&=H(p)-\mathbb EH(v(Q)).
\end{aligned}
\tag{1.1}
$$

Only $\lambda_q>0$ is considered. Thus $r_i$ is the Bayes error for $\mathbf1_{\{C=i\}}$, and $\epsilon$ is the categorical Bayes error. Entropies are in bits, $H(v)=-\sum_iv_i\log_2v_i$, $h(t)=-t\log_2t-(1-t)\log_2(1-t)$, and $0\log_20=0$. A label-only readout has $Q=f(C)$. An auxiliary readout is any deterministic $Q$ on a supplied finite $S$; $Q$ need not be a function of $C$ alone.

A finite posterior specification $(\lambda_q,v(q))$ with $\sum_q\lambda_qv(q)=p$ is realized on states $(i,q)$ of masses $\lambda_qv_i(q)$, with $C(i,q)=i$ and $Q(i,q)=q$. This is the finite splitting construction used in Kamenica–Gentzkow, *Bayesian Persuasion*, Proposition 1, [primary text](https://web.stanford.edu/~gentzkow/research/BayesianPersuasion.pdf), [DOI 10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590). It is an intermediate representation tool, not an additional five-window result.

**定义 1.2（实际切换图与额外支撑假设）。** Join two windows when they differ in exactly one bit and both windows are legal. The resulting undirected graph is

$$
G=(\{a,b,c,d,e\},E),\qquad E=\{ab,ac,ae,bd,de\}.
\tag{1.2}
$$

The support contract in this volume is the additional assumption

$$
\operatorname{supp}v(q)\text{ is a singleton or the two endpoints of an edge in }E
\quad(\lambda_q>0).
\tag{1.3}
$$

The graph itself is the existing five-edge graph of [the static-seam/toggle-cycle volume, Definition 2.1](AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md), with vertex correspondence $(0,1,2,3,13)=(a,b,c,e,d)$, and [the legal-edge phase/parent volume, §8.6](FIB_LEGAL_EDGE_LOAD_PHASE_PARENT_AND_JOINT_OCCUPATION_DESIGN.md). In (1.3), two labels with positive posterior mass must be adjacent; mere connectivity of a larger support does not suffice. The matrix below is unsigned and differs from an oriented boundary matrix:

$$
B=\begin{pmatrix}
1&1&1&0&0\\
1&0&0&1&0\\
0&1&0&0&0\\
0&0&0&1&1\\
0&0&1&0&1
\end{pmatrix},
\quad\text{columns }(ab,ac,ae,bd,de),\ \text{rows }(a,b,c,d,e).
\tag{1.4}
$$

**命题 1.3（操作合法性不蕴含后验支撑约束）。** The graph (1.2) is the actual one-bit graph, with bipartition $L=\{a,d\}$, $R=\{b,c,e\}$ and leaf $c$ adjacent only to $a$. A source supported entirely on legal windows and admitting only legal-toggle operations need not satisfy (1.3).

Proof. From $000$ the three flips give $100,010,001$. From $100$ the only additional legal flip gives $101$, and from $001$ it also gives $101$. The other flips yield adjacent occupied bits. These are exactly (1.2), with the stated bipartition and leaf. For the last assertion take the uniform law on the five legal windows, the identity label, all edges in (1.2) as allowed toggles, and a constant readout. Its posterior has five-point support. Thus (1.3) restricts readouts beyond the legality of the underlying states and operations. $\square$

## 2. Uniform five-window plateau without the support restriction

**命题 2.1（同一五窗律上的两种盲区端点）。** Suppose $p_i=1/5$. Without (1.3), impose the full indicator baseline plateau $r_i=1/5$ for every $i$. Among finite auxiliary readouts,

$$
\min\epsilon=\frac12,\qquad
\max I=\log_25-1,
\tag{2.1}
$$

and both extrema hold for the same readout. Among label-only readouts on the same uniform deployment law,

$$
\min\epsilon=\frac35,\qquad
\max I=h(2/5),
\tag{2.2}
$$

again simultaneously. These readouts can be deterministic maps on one common finite source. Plateau equality, even together with $\epsilon=1/2$, does not force two-point posterior support. On the plateau, $I=\log_25-1$ does force every positive posterior to be uniform on two labels.

Proof. The classical binary Bayes identity, applied to each indicator, gives

$$
r_i=p_i-\mathbb E(2v_i(Q)-1)_+.
\tag{2.3}
$$

Consequently the plateau is equivalent to $v_i(q)\le1/2$ for every $i$ and positive output. Put $M(q)=\max_iv_i(q)$. Then $1-M(q)\ge1/2$ and

$$
H(v(q))=\sum_iv_i(q)\log_2\frac1{v_i(q)}\ge1.
\tag{2.4}
$$

Equality in (2.4) requires every positive coordinate to equal $1/2$, hence exactly two such coordinates. These are elementary entropy and Bayes tools, also consistent with the Hellman–Raviv entropy/error inequality, §III, equation (18), [primary text](https://ee.stanford.edu/~hellman/publications/07.pdf), [DOI 10.1109/TIT.1970.1054466](https://doi.org/10.1109/TIT.1970.1054466).

For a simultaneous witness let $J$ range over the ten unordered pairs of labels and set

$$
S=\{(i,J):i\in J\},\qquad
\Pr(i,J)=1/20,
\quad C(i,J)=i,\quad Q_{\rm aux}(i,J)=J.
\tag{2.5}
$$

Each label occurs in four pairs and has prior $1/5$. Every posterior is a fair pair, proving (2.1). On this very source take $Q_{\rm lab}=\mathbf1_{\{C\in\{a,b\}\}}$. Its two fibres have label counts two and three. Each coordinate posterior is at most $1/2$, so it remains on the plateau, with $\epsilon=3/5$ and $I=H(Q_{\rm lab})=h(2/5)$.

Conversely, a label-only readout partitions the five labels into nonempty blocks. Uniformity makes the posterior uniform on a block. Plateau excludes singleton blocks; therefore either there is one block of size five, or two blocks of sizes two and three. For $k$ blocks the categorical correct probability is $k/5$, and the information is the block entropy. This proves (2.2).

For a counterexample at the risk endpoint, take the thirty outputs indexed by a label $i$ and an unordered pair $\{j,k\}$ disjoint from $i$. Give each output mass $1/30$ and posterior $v_i=1/2$, $v_j=v_k=1/4$, all others zero. Symmetry makes the prior uniform. Every indicator stays at baseline and $\epsilon=1/2$, yet every support has size three and every conditional entropy is $3/2$. The construction in Definition 1.1 supplies a finite source. Also, the constant readout has the full five-point posterior and remains on the plateau with $\epsilon=4/5$, so plateau alone does not force the risk endpoint. $\square$

## 3. Exact legal-support risk distribution

**定理 3.1（五边支撑的完整风险区域）。** Fix any prior $p_i\ge0$, $\sum_ip_i=1$. Over finite auxiliary readouts satisfying (1.3), the full attainable region is

$$
\boxed{
\mathcal R(p)=\{(r,\epsilon):r=Bz,\ z\ge0,\ Bz\le p,
\ \epsilon=\textstyle\sum_{f\in E}z_f\}.
}
\tag{3.1}
$$

Equivalently, eliminating $z$ gives

$$
\boxed{
0\le r_i\le p_i,\qquad
r_a+r_d=r_b+r_c+r_e,\qquad r_c\le r_a,
\qquad
\epsilon=r_a+r_d=\frac12\sum_ir_i.
}
\tag{3.2}
$$

Every point in (3.1) is realized by an explicit finite law with fair-edge posteriors and singleton posteriors, including boundary and zero-prior cases.

Proof. For an output with edge support $f=ij$, put

$$
x_{i,q}=\Pr(C=i,Q=q),\qquad
x_{j,q}=\Pr(C=j,Q=q),\qquad
z_q=\min(x_{i,q},x_{j,q}).
$$

Both indicator risks $r_i,r_j$ receive contribution $z_q$, all other indicators receive zero, and categorical risk receives $z_q$. A singleton output contributes no risk. Set $z_f=\sum_{q:\operatorname{supp}v(q)=f}z_q$. This proves $r=Bz$ and $\epsilon=\sum_fz_f$. Since $z_q\le x_{i,q}$, summing gives $r_i\le p_i$.

Conversely, given $z\ge0$ with $Bz\le p$, make an output $q_f$ for each $z_f>0$, with joint masses $z_f$ at each endpoint of $f$, and an output $q_i$ of joint mass $p_i-(Bz)_i$ at label $i$ when this is positive. Total mass is

$$
2\sum_fz_f+\sum_i(p_i-(Bz)_i)=1.
\tag{3.3}
$$

The label prior is exactly $p$, all readouts are deterministic projections of the supplied finite state $(C,Q)$, and their risks are the required ones. In particular, (3.3) implies $\sum_fz_f\le1/2$.

For elimination, every edge joins $L$ and $R$, so $r_a+r_d=r_b+r_c+r_e=\sum_fz_f$; the only edge incident to $c$ is $ac$, so $r_c=z_{ac}\le r_a$. For the converse set $z_{ac}=r_c$, $u=r_a-r_c\ge0$, and $T=r_b+r_e=u+r_d$. If $T>0$, set

$$
\begin{aligned}
z_{ab}&=\frac{u r_b}{T},&z_{ae}&=\frac{u r_e}{T},\\
z_{bd}&=\frac{r_d r_b}{T},&z_{de}&=\frac{r_d r_e}{T}.
\end{aligned}
\tag{3.4}
$$

All are nonnegative with the required row sums. If $T=0$, then $u=r_d=r_b=r_e=0$, and these four edge weights are zero. Thus (3.2) is sufficient as well as necessary. $\square$

**定理 3.2（先验依赖的最大剩余歧义与叶点障碍）。** Under (1.3), the attainable categorical risks form $[0,M(p)]$, where

$$
\boxed{
M(p)=\min\{p_a+p_d,\ p_b+p_c+p_e,\ p_a+p_b+p_e\}.
}
\tag{3.5}
$$

If all $p_i\le1/2$, the full indicator baseline plateau $r_i=p_i$ is feasible precisely when

$$
p_a+p_d=\frac12,\qquad p_c\le p_a.
\tag{3.6}
$$

Here $M(p)$ is the maximum remaining categorical risk. The minimum achievable risk is zero, attained by revealing $C$.

Proof. Write $L_0=p_a+p_d$, $R_0=p_b+p_c+p_e$, $U=p_b+p_e$. For every feasible $z$, (3.2) gives $\epsilon\le L_0,R_0$. Also $z_{ac}\le p_a$ and

$$
\epsilon=z_{ac}+(z_{ab}+z_{bd})+(z_{ae}+z_{de})\le p_a+U.
$$

These give (3.5) as an upper bound. For attainment set $t=\min(p_a,p_c)$ on $ac$. The four remaining edges form the complete bipartite graph between $\{a,d\}$ and $\{b,e\}$. Its remaining total capacities are $L_0-t$ on the left and $U$ on the right. Put $x=\min(L_0-t,U)$ and choose explicitly

$$
\ell_a=\min(p_a-t,x),\quad \ell_d=x-\ell_a,\qquad
s_b=\min(p_b,x),\quad s_e=x-s_b.
$$

These are nonnegative, obey their respective capacities, and have both side sums $x$. If $x>0$, assign $z_{ij}=\ell_i s_j/x$ on those four edges; if $x=0$, assign zero. With $z_{ac}=t$, the total edge weight is

$$
t+x=\min(L_0,U+t)
=\min(L_0,U+p_a,U+p_c)=M(p).
\tag{3.7}
$$

The construction of Theorem 3.1 realizes it. Scaling this $z$ by any factor in $[0,1]$ gives the whole interval, including all degenerate cases.

For the plateau substitute $r=p$ into (3.2): the bipartite equality is $L_0=R_0=1/2$, and the remaining constraint is $p_c\le p_a$. Conversely these two conditions make $r=p$ feasible in (3.2). The assumption $p_i\le1/2$ makes $p_i$ the binary baseline error; no nonbalanced binary baseline has been replaced by its larger class mass. $\square$

## 4. Uniform legal-support risk and information frontier

**定理 4.1（均匀五窗的完整风险—信息区域）。** Suppose $p_i=1/5$ and impose (1.3). The attainable $(\epsilon,I)$ region over finite auxiliary readouts is exactly

$$
\boxed{
0\le\epsilon\le\frac25,\qquad
\log_25-h(\epsilon)\le I\le\log_25-2\epsilon.
}
\tag{4.1}
$$

Both information endpoints are attained at every $\epsilon$ in the interval. For each fixed $\epsilon$, any finite collection of these readouts and any chosen intermediate point can be realized on a common finite source with deterministic readouts. A single finite carrier for the entire continuum of parameter values is not asserted.

Proof. Theorem 3.2 gives $M(p)=2/5$. On an edge-supported posterior put $u(q)=1-\max_iv_i(q)\in[0,1/2]$; on a singleton put $u(q)=0$. Then

$$
\epsilon=\mathbb Eu(Q),\qquad
H(C\mid Q)=\mathbb Eh(u(Q)).
$$

The classical binary concavity/chord estimates, with the entropy/error attribution in Proposition 2.1 and [the ledger, §2](FIB_ATOM_MULTI_TASK_INFORMATION_LEDGER.md), give

$$
2\epsilon\le H(C\mid Q)\le h(\epsilon).
\tag{4.2}
$$

It remains to meet both equality conditions while retaining this actual graph and the uniform prior.

For the upper information endpoint take

$$
z_{ac}=\epsilon/2,\qquad
z_{bd}=z_{de}=\epsilon/4,\qquad
z_{ab}=z_{ae}=0.
\tag{4.3}
$$

Here $(Bz)_{a,c,d}=\epsilon/2$ and $(Bz)_{b,e}=\epsilon/4$, all at most $1/5$ when $\epsilon\le2/5$. Theorem 3.1's fair-edge/singleton law has conditional entropy $2\epsilon$ and error $\epsilon$.

For the lower information endpoint an explicit construction with constant posterior error is required. Write $u=\epsilon\in[0,2/5]$. Give an output $q_{ac}$ mass

$$
\lambda=\frac1{5(1-u)},\qquad
v_a(q_{ac})=u,\quad v_c(q_{ac})=1-u.
\tag{4.4}
$$

This uses all $c$ mass and $u/[5(1-u)]$ of the $a$ mass. The remaining desired label masses are

$$
\ell_a=\frac{1-2u}{5(1-u)},\qquad
\ell_d=\frac15,\qquad
s_b=s_e=\frac15.
$$

Let

$$
L=\ell_a+\ell_d=\frac{2-3u}{5(1-u)},\qquad
R=\frac25,\qquad T=L+R=1-\lambda.
\tag{4.5}
$$

Both $L,R$ are positive in this parameter range. Moreover

$$
L-uT=\frac{(2-5u)(1-u)}{5(1-u)}\ge0,
\qquad
R-uT=\frac{2-6u+5u^2}{5(1-u)}>0.
\tag{4.6}
$$

Thus $u\le L/T\le1-u$. Define

$$
\theta=\frac{L/T-u}{1-2u}\in[0,1],\qquad
\pi_{ij}=\frac{\ell_i}{L}\frac{s_j}{R}
\quad(i\in\{a,d\},\ j\in\{b,e\}).
$$

For each such legal edge $ij$, use two outputs with respective masses $T\pi_{ij}\theta$ and $T\pi_{ij}(1-\theta)$, and posterior masses $(1-u,u)$ and $(u,1-u)$ in order $(i,j)$. Discard zero-mass outputs. Since $\sum_{ij}\pi_{ij}=1$, these outputs have total mass $T$. The total mass at label $i$ is

$$
\frac{\ell_i}{L}\,T\bigl(\theta(1-u)+(1-\theta)u\bigr)=\ell_i,
$$

and the total mass at label $j$ is $s_j$. With (4.4) this is exactly the uniform prior. Every posterior has smaller mass $u$, so $H(C\mid Q)=h(u)$ and categorical error $u$. At $u=0$ all positive posteriors reduce to singletons; at $u=2/5$ one orientation weight may vanish, and the same formulas remain defined.

Finally consider any finite joint tables $J_k(i,q_k)$ having this prior. A common finite source is given by

$$
\Pr(C=i,Q_1=q_1,\ldots,Q_m=q_m)
=\frac{\prod_{k=1}^mJ_k(i,q_k)}{p_i^{m-1}},
\tag{4.7}
$$

with zero-prior labels omitted if needed. Each projection has the specified joint law. In particular realize the two endpoints $Q_-,Q_+$ this way and append a finite independent bit $T_0$ with $\Pr(T_0=1)=t$. The deterministic readout $(T_0,Q_{T_0})$ has the same error $u$, satisfies (1.3), and has information $(1-t)I_-+tI_+$. This proves every point between the endpoints without treating a channel randomized relative to $C$ as an unspecified external randomizer. $\square$

## 5. Task weighting and unavoidable improvement

**定理 5.1（均匀五窗的权重盲点与均匀改进界）。** Suppose $p_i=1/5$ and impose (1.3). Put $\delta_i=1/5-r_i$. Then

$$
\delta_i\ge0,\qquad
\delta_b+\delta_c+\delta_e=\frac15+\delta_a+\delta_d,
\qquad \delta_c\ge\delta_a,
\qquad
\sum_i\delta_i\ge\frac15.
\tag{5.1}
$$

For every choice of $w_i\ge0$, the exact attained extrema are

$$
\boxed{
\min\sum_iw_i\delta_i=\frac15\min(w_b,w_c,w_e),
\qquad
\min\max_i\delta_i=\frac1{15}.
}
\tag{5.2}
$$

In particular the full indicator baseline plateau is impossible under (1.3), although a weighted objective can have zero forced improvement if any one of $w_b,w_c,w_e$ is zero.

Proof. Equation (5.1) is (3.2) after substitution. Its equality yields

$$
\sum_i\delta_i=\frac15+2(\delta_a+\delta_d)\ge\frac15.
$$

Let $w_*=\min(w_b,w_c,w_e)$. Nonnegativity gives

$$
\sum_iw_i\delta_i\ge w_*(\delta_b+\delta_c+\delta_e)\ge w_*/5.
$$

For each choice of $j\in\{b,c,e\}$ there is a feasible vector with $\delta_j=1/5$ and all other deficits zero. Explicit edge weights of Theorem 3.1 are

$$
\begin{array}{c|cc}
j&\text{first nonzero edge weight}&\text{second nonzero edge weight}\\ \hline
b&z_{ac}=1/5&z_{de}=1/5\\
c&z_{ab}=1/5&z_{de}=1/5\\
e&z_{ac}=1/5&z_{bd}=1/5
\end{array}
\tag{5.3}
$$

The fair-edge outputs have mass $2/5$ each and the remaining singleton output has mass $1/5$ at $j$. Taking a minimizing $j$ proves the first equality, also when weights vanish or tie.

For the second equality, (5.1) implies $\max_i\delta_i\ge(\delta_b+\delta_c+\delta_e)/3\ge1/15$. Attainment has

$$
\delta_a=\delta_d=0,\qquad
\delta_b=\delta_c=\delta_e=1/15.
$$

An explicit edge specification is

$$
z_{ac}=\frac2{15},\qquad z_{ab}=z_{ae}=\frac1{30},\qquad
z_{bd}=z_{de}=\frac1{10}.
\tag{5.4}
$$

The corresponding fair-edge outputs together have mass $4/5$, and singleton outputs at $b,c,e$ each have mass $1/15$. This realizes the displayed deficits and proves the minimax equality. These extrema concern task risks on this finite law; no training or sampling assumption is used. $\square$

## 6. Minimal probability of support relaxation

**定义 6.1（支撑违反概率）。** For a finite readout on the uniform five-label source, let

$$
\alpha=\sum_{q:\operatorname{supp}v(q)\text{ is neither a singleton nor an edge of }G}\lambda_q.
\tag{6.1}
$$

This is the probability of outputs violating (1.3), not the probability of an illegal source window or an illegal toggle.

**定理 6.2（完整指标平台的最小支撑放宽）。** Without requiring (1.3), impose $r_i=1/5$ for all five indicators. Then

$$
\boxed{\min\alpha=\frac15.}
\tag{6.2}
$$

The minimum is attained by a finite deterministic readout with categorical error $1/2$ and information $\log_25-1$.

Proof. The plateau criterion (2.3) forces all posterior coordinates to be at most $1/2$. Thus no singleton output is possible, and every output satisfying (1.3) is a fair edge. Every such edge assigns posterior mass $1/2$ to $L=\{a,d\}$. Since the prior mass of $L$ is $2/5$,

$$
\frac25
=\sum_{q\text{ satisfying }(1.3)}\lambda_q\frac12
 +\sum_{q\text{ violating }(1.3)}\lambda_q\Pr(C\in L\mid q)
\ge\frac{1-\alpha}{2}.
$$

Hence $\alpha\ge1/5$. For attainment use four outputs with the following posterior supports and output masses, each posterior uniform on its pair:

$$
\begin{array}{c|cccc}
\text{support}&ac&bd&de&be\\ \hline
\text{output mass}&2/5&1/5&1/5&1/5
\end{array}
\tag{6.3}
$$

The joint mass at each of $a,c$ is $1/5$, at $d$ is $1/10+1/10=1/5$, and at each of $b,e$ is $1/10+1/10=1/5$. Only $be$ is not an edge of $G$, so $\alpha=1/5$. Every coordinate posterior is at most $1/2$, proving the plateau; every output has categorical error $1/2$ and entropy one. The finite state construction in Definition 1.1 supplies deterministic readouts. $\square$

## 追加锚（本行以下为增补区）
