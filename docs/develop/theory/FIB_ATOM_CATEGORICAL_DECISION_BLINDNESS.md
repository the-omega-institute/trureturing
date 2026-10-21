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

## 7. Soft edge leakage, the complete risk polygon and positive-noise records

**定义 7.1（软边泄漏与同先验比较）。** Retain the five labels and graph of Definitions 1.1–1.2, with $p_i=1/5$, but do not impose (1.3). For a posterior $v$ put

$$
 m(v)=\max_i v_i,\qquad s_G(v)=\max_{ij\in E}(v_i+v_j),\qquad
 \ell_G=\mathbb E[1-s_G(v(Q))],\qquad D=\sum_i(1/5-r_i).
\tag{7.1}
$$

Thus $\ell_G$ is the minimum probability of missing the true label when the decision reports one legal edge; it is a bounded decision risk, rather than the hard support-violation probability $\alpha$ of Definition 6.1. Since every vertex belongs to an edge, $\ell_G=0$ is equivalent to (1.3). An active output means $\lambda_q>0$; a full-support law means $v_i(q)>0$ for every label and active output.

The edge decision uses gain $g(ij,k)=\mathbf1_{\{k\in\{i,j\}\}}$. This is an instance of the classical gain-function framework in Américo–Alvim–McIver, [*An Algebraic Approach for Reasoning About Information Flow*, §2](https://arxiv.org/html/1801.08090v4). Their §3.2 and Theorem 5.2 supply visible choice: when an independent finite selector is included in the observed output, posterior expected gains, and hence the risks here, interpolate linearly. The selector is part of the supplied source. Same-prior finite joint tables are put on a common finite carrier by (4.7), with deterministic projection readouts; this also applies to any finite collection constructed below. No single finite carrier for a continuum of parameter values is stipulated.

**定理 7.2（完整的软泄漏—分类风险多边形）。** Over all finite joint laws with this uniform prior, the exact attained region is

$$
\boxed{
 0\le\ell_G\le\frac35,\qquad
 \ell_G\le\epsilon\le
 \min\left\{\frac25+\ell_G,\frac{1+\ell_G}{2}\right\}.
}
\tag{7.2}
$$

Its vertices, in boundary order, are $(0,0),(0,2/5),(1/5,3/5),(3/5,4/5),(3/5,3/5)$. This is a two-dimensional projection; it does not specify an exact joint region for $(\ell_G,\epsilon,D)$ or for information $I$.

Proof. Every vertex has a neighbour, so $m\le s_G\le2m$. Also, writing $v_L=v_a+v_d$, every edge has one endpoint in $L=\{a,d\}$ and one in $R=\{b,c,e\}$, whence

$$
 s_G\le v_L+m,\qquad
 \mathbb Es_G\ge\max_{ij\in E}\mathbb E(v_i+v_j)=2/5.
\tag{7.3}
$$

Taking expectations gives all the inequalities in (7.2). In particular $s_G\le2m$ gives $\epsilon\le(1+\ell_G)/2$, while $s_G\le v_L+m$ gives $\epsilon-\ell_G\le2/5$.

For necessity to be sufficient, use the uniform five-state source and the following partitions. The readout reports the block containing $C$; a block of size $k$ has output mass $k/5$ and uniform posterior on that block.

| Readout | Partition blocks | $\ell_G$ | $\epsilon$ | $D$ |
| --- | --- | --- | --- | --- |
| $A$ | $a\mid b\mid c\mid d\mid e$ | $0$ | $0$ | $1$ |
| $B$ | $ac\mid bd\mid e$ | $0$ | $2/5$ | $1/5$ |
| $C_0$ | $ac\mid bde$ | $1/5$ | $3/5$ | $0$ |
| $U$ | $abcde$ | $3/5$ | $4/5$ | $0$ |
| $V$ | $ad\mid bce$ | $3/5$ | $3/5$ | $0$ |

For $C_0$, the triple $bde$ has maximal edge mass $2/3$; for $V$, both blocks are independent sets and their maximal edge masses are respectively $1/2$ and $1/3$. These verify the entries beyond the legal-edge cases already supplied by Theorem 3.1. The upper lines meet at $(1/5,3/5)$; the remaining bounding lines meet at the other displayed vertices, so the inequalities define precisely their convex hull. For any convex weights, append an independent five-valued selector $T$ to this common source and observe $(T,Q_T)$. The output reveals the selector, so both risks are the weighted averages. This constructs every point of the polygon on a finite source. For any finite collection of choices, (4.7) supplies a common finite carrier. The generic gain and interpolation tools are those attributed in Definition 7.1; the graph-specific inequalities and attainers yield the stated polygon. $\square$

**定理 7.3（全范围总改进下包络与平台阈值）。** For every $\ell\in[0,3/5]$,

$$
\boxed{\min_{\ell_G=\ell}D=\max\{0,1/5-2\ell\}.}
\tag{7.4}
$$

The minimum is attained by finite same-prior laws. The full indicator plateau $r_i=1/5$ for every $i$ is attainable at a specified leakage $\ell$ exactly when $1/10\le\ell\le3/5$.

Proof. Reusing the binary Bayes identity (2.3), at most one posterior coordinate exceeds $1/2$, hence

$$
 D=\mathbb E(2m(v(Q))-1)_+
 \ge\max\{0,1-2\epsilon\}
 \ge\max\{0,1/5-2\ell_G\}.
\tag{7.5}
$$

Let $H$ be the fair-pair witness (6.3), with output masses $2/5,1/5,1/5,1/5$ on $ac,bd,de,be$. Only $be$ is a nonedge; its posterior maximal edge mass is $1/2$. Therefore

$$
 (\ell_G,\epsilon,D,\alpha)(H)=(1/10,1/2,0,1/5).
\tag{7.6}
$$

For $0\le\ell\le1/10$, visible choice of $B$ and $H$, with weight $10\ell$ on $H$, has leakage $\ell$ and $D=(1-10\ell)/5$. For $1/10\le\ell\le3/5$, visible choice of $H$ and $U$, with weight $2\ell-1/5$ on $U$, has leakage $\ell$ and $D=0$. All weights lie in $[0,1]$ and all constituent priors are the same. Nonnegative individual improvements make $D=0$ equivalent to the full plateau. The bound and these attainers prove both statements. The hard threshold $\min\alpha=1/5$ on the plateau remains Theorem 6.2; (7.6) attains both thresholds, whose observables and numerical values differ. $\square$

**命题 7.4（严格正后验的不可达边界）。** Every finite full-support law satisfies

$$
 \ell_G>0,\qquad \epsilon>\ell_G,\qquad
 \epsilon-\ell_G<2/5.
\tag{7.7}
$$

If it is on the full indicator plateau, then $\ell_G>1/10$. Over arbitrary finite full-support plateau laws the infimum of $\ell_G$ is exactly $1/10$, and is not attained.

Proof. At any full-support posterior each edge omits positive mass, so $s_G<1$. A neighbour of a maximizer has positive mass, so $s_G>m$. Finally, for every edge $ij$ with $i\in L$, one has $v_i<v_L$ and $v_j\le m$, yielding $s_G<v_L+m$. Finite positive-weight averaging proves (7.7). On the plateau (2.3) gives $m\le1/2$, so $\epsilon\ge1/2$ and the last strict inequality forces $\ell_G>1/10$.

For the infimum, write $J_H(i,q)=\lambda_qv_i(q)$ for (6.3) and, for $0<\eta\le1$, set

$$
 J_{H,\eta}(i,q)=(1-\eta)J_H(i,q)+\eta\lambda_q/5.
\tag{7.8}
$$

This preserves both the prior and the output masses. Every posterior is $(1-\eta)v(q)+\eta p$, has full support and has maximum at most $(1-\eta)/2+\eta/5\le1/2$. It therefore remains on the plateau. Continuity of a maximum of finitely many linear functions gives $\ell_G(J_{H,\eta})\to\ell_G(H)=1/10$ as $\eta\downarrow0$. These laws share the same finite alphabet, and any finite subfamily has a common finite source by (4.7). This infimum concerns arbitrary finite joint laws; it is not an infimum or attainability claim for a restricted Gaussian preparation family. $\square$

**命题 7.5（风险的尖锐 TV 控制与硬支撑不连续）。** Let $J,J'$ be joint laws of $(C,Q)$ on the same finite alphabet and with the same uniform five-label prior. Use the convention of [the Gaussian record volume, Proposition 14.2](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md),

$$
 \Delta=\operatorname{TV}(J,J')=\sup_A|J(A)-J'(A)|
 =\tfrac12\sum_{i,q}|J(i,q)-J'(i,q)|.
$$

Then

$$
 |\ell_G(J)-\ell_G(J')|\le\Delta,\quad
 |\epsilon(J)-\epsilon(J')|\le\Delta,\quad
 |r_i(J)-r_i(J')|\le\Delta,\quad
 |D(J)-D(J')|\le2\Delta.
\tag{7.9}
$$

The constants are sharp, including with this fixed prior. By contrast $\alpha$ is discontinuous even at legal-support laws on a fixed finite output alphabet.

Proof. The classical bounded-expectation characterization of TV gives $|\mathbb E_Jf-\mathbb E_{J'}f|\le(b-a)\Delta$ for $a\le f\le b$: apply the event definition to the level sets of $(f-a)/(b-a)$ and integrate. Edge-miss, categorical error and each binary error are losses in $[0,1]$. For each fixed decision rule their risks differ by at most $\Delta$; taking the infimum over the same rules in both laws gives the first three bounds. This is the standard bounded-loss TV argument, used here inside the joint-law comparison, not as a new general result.

For the aggregate, use the gain-function representation from Definition 7.1 with actions $0,a,b,c,d,e$, where $g(0,k)=0$ and $g(i,k)=2\mathbf1_{\{k=i\}}-1$. Its optimal posterior gain is $(2m-1)_+$, so (7.5) identifies its expected optimum as $D$. Each fixed rule has gain in $[-1,1]$; the same TV argument and optimization give coefficient $2$, rather than a sum of five separate error bounds.

For sharpness, split the $ac$ output of $H$ into two equal outputs $q_+,q_-$, each with joint mass $1/10$ at $a$ and $c$. Transfer mass $t$ from $c$ to $a$ in $q_+$ and from $a$ to $c$ in $q_-$, where $0<t<1/10$, leaving the other outputs unchanged. The prior and output masses stay fixed, $\Delta=2t$, $D$ increases by $4t$, and $\epsilon$ and each of $r_a,r_c$ decrease by $2t$. Relabelling the five coordinates of this pair construction gives sharpness for each individual $r_i$. For edge-risk sharpness, start with two outputs each having joint mass $1/10$ at each label. Transfer $t$ from $d$ to $a$ in the first and from $a$ to $d$ in the second. Each output's maximal edge mass grows from $1/5$ to $1/5+t$, so $\ell_G$ decreases by $2t=\Delta$.

For discontinuity, take $J_B$ from Theorem 7.2 and apply the contamination formula (7.8) with its own output masses. This has the same prior and alphabet, and $\operatorname{TV}(J_B,J_{B,\eta})\le\eta$. At $\eta=0$, $\alpha=0$; at every $\eta>0$, all active posteriors have five-point support and $\alpha=1$. Nevertheless $\ell_G(J_{B,\eta})\to0$ by (7.9). A common finite source for each compared pair is supplied by (4.7). Thus hard support cannot be transferred through an arbitrarily small nonzero TV bound, whereas the soft risk can. $\square$

**假设 7.6（固定五种制备与共同量化器）。** Use the compact set $K_J$, preparations, normalized projected inputs, and unchanged apparatus of [the Gaussian record volume, Assumption 12.2 and §§13–14](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md). Fix five preparations $W_a,W_b,W_c,W_d,W_e\in K_J$ as explicit data. This is an externally assigned label-to-preparation map; neither injectivity nor a map from native three-bit atoms to physical preparations is assumed. Use uniform preparation labels, one externally fixed word $w=E_1\cdots E_t$ with $0\le t\le7$, one $\sigma>0$, and one fixed Borel map $\kappa:\mathbb R^{t+1}\to\mathcal Q$ to a finite alphabet. The same word, apparatus and quantizer are used for the original and projected-input laws. Write

$$
 \begin{aligned}
 P(i,A)&=\tfrac15\nu_w(W_i)(A),&
 P_N(i,A)&=\tfrac15\nu_{w,N}(W_i)(A),\\
 J(i,q)&=\tfrac15\nu_w(W_i)(\kappa^{-1}(q)),&
 J_N(i,q)&=\tfrac15\nu_{w,N}(W_i)(\kappa^{-1}(q)).
 \end{aligned}
\tag{7.10}
$$

Here $P,P_N$ are complete-record joint laws, and $J,J_N$ are their common quantized images. The finite label distribution is additional supplied data; it is not a probability distribution on every companion in $K_J$.

**命题 7.7（实际高斯源的联合律桥与精确支撑障碍）。** Under Assumption 7.6, let $t_N(W)$ and $\delta_N$ have the source's meanings in (13.1)–(13.3), and set

$$
 e_N=\frac15\sum_i\sqrt{t_N(W_i)}\le\delta_N.
$$

Then

$$
 \operatorname{TV}(J,J_N)\le\operatorname{TV}(P,P_N)
 \le e_N,
\qquad
 \begin{cases}
 |\ell_G(J)-\ell_G(J_N)|,\ |\epsilon(J)-\epsilon(J_N)|\le e_N,\\
 |r_i(J)-r_i(J_N)|\le e_N,\\
 |D(J)-D(J_N)|\le2e_N.
 \end{cases}
\tag{7.11}
$$

Both input families give strictly positive complete-pointer densities everywhere. Consequently, after discarding null bins, every posterior of both finite laws has full support. Each has $\alpha=1$, $\ell_G>0$ and $\epsilon>\ell_G$; if either is on the full indicator plateau, its leakage is strictly greater than $1/10$. Neither finite law can satisfy (1.3), irrespective of how small the nonzero approximation error is.

Proof. The source's Proposition 14.2 applies to each of the five fixed preparations and to this same complete fixed-word measurement, giving conditional TV at most $\sqrt{t_N(W_i)}$. Because the label sections are disjoint,

$$
 \operatorname{TV}(P,P_N)
 =\frac15\sum_i\operatorname{TV}(\nu_w(W_i),\nu_{w,N}(W_i))
 \le e_N.
\tag{7.12}
$$

The equality follows by the finite-label decomposition of total variation (or by integrating the absolute density difference on each section). The common measurable map $(i,z)\mapsto(i,\kappa(z))$ contracts TV. Proposition 7.5 now proves (7.11). No factor for labels, reads or bins is introduced: (7.12) averages with the actual prior, and the source already controls the complete record. The two finite laws also have a common finite deterministic-readout realization by (4.7); the unquantized pointer variable is not being declared finite.

For original inputs the source gives

$$
 \nu_w(W_i)=\mathcal N_{t+1}\left(L_w\mu(W_i),\tfrac12L_wL_w^T+\sigma^2 I\right).
\tag{7.13}
$$

The covariance is positive definite because $\sigma>0$, hence the density is strictly positive at every record. For projected inputs use exactly the source's (14.4):

$$
 p_{w,N}(z\mid W_i)=\int_{\mathbb R^{17}}|\psi_{W_i,N}(x)|^2
 \prod_{j=0}^t\frac{\exp(-(z_j-L_jx)^2/(2\sigma^2))}{\sqrt{2\pi\sigma^2}}\,dx>0.
\tag{7.14}
$$

The normalized input has integral one; the product is strictly positive for every $x,z$ and bounded above by $(2\pi\sigma^2)^{-(t+1)/2}$. Thus the integral is positive and finite for every $z$, even though the projected input need not be Gaussian. A quantizer bin is active precisely when it has positive Lebesgue measure. Every such bin has positive probability under every preparation in both families. Bayes' formula and the positive prior give full-support posteriors; Proposition 7.4 and Definition 6.1 give the asserted consequences.

For example, with $x_+=\max(x,0)$, valid transferred lower bounds include

$$
 \begin{aligned}
 \ell_G(J)&\ge(\ell_G(J_N)-e_N)_+,\\
 \epsilon(J)&\ge(\epsilon(J_N)-e_N)_+,\\
 D(J)&\ge\bigl(\max\{0,1/5-2\ell_G(J_N)\}-2e_N\bigr)_+.
 \end{aligned}
\tag{7.15}
$$

The same statements hold with $J,J_N$ exchanged. The last inequality follows from (7.4) and aggregate stability, or by substituting $\ell_G(J)\le\ell_G(J_N)+e_N$ into (7.4). These are bounds on the explicitly paired laws, not a way to replace either law by an unrelated abstract vertex witness.

The parameter $e_N$ measures input-approximation error relative to the original noisy apparatus. Sending it to zero does not send the observation noise $\sigma$ to zero, remove overlap between the five likelihoods, or drive either Bayes error to zero. The finite attainers in Theorems 7.2–7.3 and the full-support infimum in Proposition 7.4 have no asserted realization by these five Gaussian preparations. The bridge uses only unconditional, externally fixed-word, complete-record laws and one common quantizer; it yields no rare-event or exact-history conditioning bound, adaptive-word statement, trained-network attainment, native-atom encoding, process-dimension bound or physical-resource claim. The mathematical additions are the graph-specific soft-risk region and attainers, their full-support boundary, and their application to the cited preparation/record correspondence. Classical Bayes identities, posterior splitting, gain functions, visible choice and TV control are reused intermediate tools; no worldwide priority claim follows. $\square$

## 追加锚（本行以下为增补区）
