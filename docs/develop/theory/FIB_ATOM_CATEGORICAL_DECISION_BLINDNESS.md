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

## 8. Fixed a/d overlap and the attained improvement envelope

**定义 8.1（同侧两标签的联合质量重叠）。** Retain the uniform five-label prior, the graph $G$ and the finite-law notation of Definitions 1.1 and 7.1, without imposing (1.3). For the joint table $J(i,q)=\lambda_qv_i(q)$ define

$$
 o_{ad}(J)=\sum_q\min\{J(a,q),J(d,q)\}
 =\mathbb E\min\{v_a(Q),v_d(Q)\}.
\tag{8.1}
$$

Write $o=o_{ad}(J)$ and $\ell=\ell_G(J)$ when the law is understood. This is the overlap of the two joint-mass rows, each of mass $1/5$, rather than the overlap of two probability rows of mass one. The vertices $a,d$ comprise the smaller bipartition class $L$ of this particular graph. A full-support law has the meaning in Definition 7.1. The finite posterior realization and observed-selector constructions used below are precisely those of Definition 1.1 and Definition 7.1, with their cited posterior-splitting and gain-function tools.

**定理 8.2（固定重叠的精确可行域、下包络与严格正支撑）。** Over all finite joint laws with this uniform prior, the exact feasible overlap/leakage domain is

$$
 \boxed{0\le o\le\frac15,\qquad o\le\ell\le\frac25+o.}
\tag{8.2}
$$

At every pair in (8.2), the minimum total indicator improvement is attained and equals

$$
 \boxed{\min_{o_{ad}=o,\,\ell_G=\ell}D
 =\left(\frac15-2\ell+2o\right)_+.}
\tag{8.3}
$$

Here $x_+=\max\{0,x\}$. Restricting to finite full-support laws, the exact feasible domain is

$$
 \boxed{0<o\le\frac15,\qquad o<\ell\le\frac25+o,}
\tag{8.4}
$$

and the same minimum (8.3) is attained at every pair in (8.4). Each specified pair admits an attaining finite source with deterministic label and readout maps, at most six active outputs and at most thirty positive-mass states. At a fixed $o\in[0,1/5]$, the full indicator plateau is attainable exactly for

$$
 \frac1{10}+o\le\ell\le\frac25+o.
\tag{8.5}
$$

For every $0<o\le1/5$, all of (8.5), including its lower endpoint, is attainable with full support.

Proof. For a posterior $v$ put

$$
 h=\min(v_a,v_d),\qquad M=\max(v_a,v_d),\qquad
 m=\max_i v_i,\qquad s=s_G(v).
$$

Then $\mathbb Eh=o$, $\mathbb EM=2/5-o$ and $0\le o\le1/5$. Every edge contains one member of $L$ and one member of $R=\{b,c,e\}$. Moreover $b$ is adjacent to both $a$ and $d$. Thus, pointwise,

$$
 M+v_b\le s\le1-h,\qquad s\le M+m.
\tag{8.6}
$$

The middle bound holds because the other member of $L$, omitted by any edge, has mass at least $h$. Averaging the first two bounds gives

$$
 \frac35-o\le1-\ell\le1-o,
$$

which proves the necessary strip (8.2). Reusing (2.3), at most one coordinate can exceed $1/2$, so

$$
 D=\mathbb E(2m-1)_+\ge\max\{0,2\mathbb Em-1\}.
$$

The last inequality in (8.6) gives $\mathbb Em\ge3/5-\ell+o$. Consequently every law obeys (8.3) as a lower bound. It also gives the necessary categorical-risk inequality

$$
 \epsilon\le\frac25+\ell-o.
\tag{8.7}
$$

For simultaneous feasibility and attainment, first take parameters
$0\le o\le1/5$ and $0\le u\le1/10$. Use the following four output indices $(l,r)$ and output masses:

$$
 \begin{array}{c|cccc}
 (l,r)&(a,c)&(a,e)&(d,b)&(d,e)\\ \hline
 \lambda_{lr}&1/3&1/6&1/3&1/6.
 \end{array}
\tag{8.8}
$$

For an index $(l,r)$, let $l'$ be the other member of $L$ and prescribe its posterior by

$$
 v_l=\frac25-o,\qquad v_{l'}=o,\qquad
 v_r=\frac35-u,\qquad
 v_j=\frac u2\quad(j\in R\setminus\{r\}).
\tag{8.9}
$$

These are nonnegative coordinates summing to one. The output indices select each member of $L$ with total probability $1/2$ and each member of $R$ with total probability $1/3$. Hence the mean mass at either left label is
$\tfrac12(2/5-o)+\tfrac12o=1/5$, while the mean mass at any right label is
$\tfrac13(3/5-u)+\tfrac23(u/2)=1/5$. Thus the prior is uniform.

Every designated pair $(l,r)$ is an actual edge of $G$. At each of these posteriors,

$$
 h=o,\qquad M=\frac25-o,\qquad m=\frac35-u,\qquad
 s=v_l+v_r=1-o-u.
$$

Indeed $v_l\ge v_{l'}$, the designated right coordinate is maximal among all five coordinates, and its designated left neighbour realizes the upper bound $s\le M+m$. Call this law $F_{o,u}$. It satisfies

$$
 (o_{ad},\ell_G,\epsilon,D)(F_{o,u})
 =\left(o,o+u,\frac25+u,\frac15-2u\right).
\tag{8.10}
$$

Its posteriors have full support exactly when $o>0$ and $u>0$. In particular it attains the entire lower branch of (8.3), including $u=0$ and the plateau endpoint $u=1/10$.

For the upper leakage endpoint, take a two-output law $T_o$ with equal output masses and posteriors, in $(a,b,c,d,e)$ order,

$$
 \left(\frac25-o,\frac15,\frac15,o,\frac15\right),\qquad
 \left(o,\frac15,\frac15,\frac25-o,\frac15\right).
\tag{8.11}
$$

It has the uniform prior, and each posterior has $h=o$, $m=2/5-o$ and $s=3/5-o$: all right coordinates are $1/5$, and either possible maximizing left vertex has a neighbour. Therefore

$$
 (o_{ad},\ell_G,\epsilon,D)(T_o)
 =\left(o,\frac25+o,\frac35+o,0\right).
\tag{8.12}
$$

This law has full support exactly when $o>0$.

For $o+1/10\le\ell\le o+2/5$, reveal a selector choosing
$T_o$ with probability

$$
 \theta=\frac{\ell-o-1/10}{3/10}\in[0,1]
\tag{8.13}
$$

and $F_{o,1/10}$ with probability $1-\theta$. More explicitly, give the two disjoint groups of outputs joint masses
$\theta\lambda_q^{T}v_i^{T}(q)$ and
$(1-\theta)\lambda_q^{F}v_i^{F}(q)$, respectively, discarding outputs of zero mass. Both component priors are uniform. The observed selector preserves their posteriors, so $o_{ad},\ell_G,D$ are affine in these weights. The resulting law has the prescribed $(o,\ell)$ and $D=0$. This proves attainment throughout (8.2).

For each law just specified, the states $(i,q)$ of positive masses
$J(i,q)=\lambda_qv_i(q)$, with $C(i,q)=i$ and $Q(i,q)=q$, give the promised deterministic realization. The lower branch uses four outputs; the selector construction uses at most six. This is the finite splitting realization already attributed in Definition 1.1, with the selector included in the supplied finite carrier.

For necessity of (8.4), full support gives $h>0$ at every active output. Every edge also omits two positive right coordinates as well as the other left coordinate, so $s<1-h$. Finite positive-weight averaging gives $o>0$ and $\ell>o$. The other inequalities remain those of (8.2). Conversely, the lower-branch laws are full support whenever $o>0$ and $\ell-o=u>0$; for the remaining part of (8.4), both selector components have full support when $o>0$. This proves the exact full-support domain and attained minimum there. Finally, the individual improvements $1/5-r_i$ are nonnegative, so their sum vanishes exactly on the full indicator plateau. Equations (8.3), (8.10) and (8.13) prove (8.5) and its full-support assertion. $\square$

**推论 8.3（无条件包络与正支撑阈值的细化）。** Minimizing (8.3) over feasible overlaps at a fixed $\ell\in[0,3/5]$ recovers Theorem 7.3:

$$
 \min_{\ell_G=\ell}D=\left(\frac15-2\ell\right)_+.
\tag{8.14}
$$

For prescribed positive overlap, the plateau threshold is the attained value $1/10+o$, including among full-support laws. Over all finite full-support plateau laws the leakage infimum remains $1/10$ and is not attained, as in Proposition 7.4. The classification (8.2)–(8.4) concerns the feasible $(o,\ell)$ projection and the minimum of $D$ above each pair; it supplies neither a complete joint upper boundary for $D$ nor an all-risk region involving the individual $r_i$, $\epsilon$ or $I$.

Proof. At fixed $\ell$, feasible overlaps are
$\max\{0,\ell-2/5\}\le o\le\min\{1/5,\ell\}$. Since (8.3) is nondecreasing in $o$, its minimum is at the lower endpoint. For $\ell\le2/5$ this gives (8.14) directly; for $\ell>2/5$ both sides of (8.14) vanish. The attainers of Theorem 8.2 give equality. Full support forces $o>0$, so (8.5) forces $\ell>1/10$. Conversely $F_{o,1/10}$ is a full-support plateau law for every $o>0$ and has $\ell=1/10+o\downarrow1/10$ as $o\downarrow0$. $\square$

**假设 8.4（原始共同高斯记录与仅输入投影的配对）。** Retain exactly Assumption 7.6: five supplied original preparations $\rho_{W_i}$ with $W_i\in K_J$, uniform labels, one externally fixed word $w=E_1\cdots E_t$ with $0\le t\le7$, one fixed $\sigma>0$ and one common finite Borel quantizer $\kappa:\mathbb R^{t+1}\to\mathcal Q$. The original states are the preparations (12.3) of [the Gaussian record volume](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md); their normalized input projections are its (13.1). Both use the unchanged complete-record measurement of its Definition 14.1. In the notation of its Theorem 5.1 and Proposition 14.2, set

$$
 \begin{gathered}
 \mu_i=L_w\mu(W_i),\qquad
 \Sigma=\frac12L_wL_w^T+\sigma^2I_{t+1}>0,\\
 d=\sqrt{(\mu_a-\mu_d)^T\Sigma^{-1}(\mu_a-\mu_d)},\qquad
 g=\frac25\Phi(-d/2),\\
 \rho_N=\frac{\sqrt{t_N(W_a)}+\sqrt{t_N(W_d)}}5
 \le\frac25\delta_N,\qquad
 \gamma_N=(g-\rho_N)_+.
 \end{gathered}
\tag{8.15}
$$

Here $\Phi$ is the standard normal distribution function, and $t_N,\delta_N$ are the input-tail and uniform input-error quantities of the source's (13.1)–(13.3). The symbol $\rho_N$ in (8.15) is a scalar pairwise error bound, distinct from the input density operators $\rho_{W_i,N}$. The laws $J,J_N$ remain precisely the quantized joint laws (7.10).

**命题 8.5（实际记录重叠与各自平台的必要界）。** Under Assumption 8.4, the original and projected-input laws satisfy

$$
 \boxed{o_{ad}(J)\ge g,\qquad o_{ad}(J_N)\ge\gamma_N.}
\tag{8.16}
$$

In particular, each law separately obeys the necessary risk bounds

$$
 \begin{aligned}
 D(J)&\ge\left(\frac15-2\ell_G(J)+2g\right)_+,&
 \epsilon(J)&\le\frac25+\ell_G(J)-g,\\
 D(J_N)&\ge\left(\frac15-2\ell_G(J_N)+2\gamma_N\right)_+,&
 \epsilon(J_N)&\le\frac25+\ell_G(J_N)-\gamma_N.
 \end{aligned}
\tag{8.17}
$$

The inequalities of Theorem 7.2 also continue to apply to each law. A full indicator plateau of $J$ requires
$\ell_G(J)\ge1/10+g$. A full indicator plateau of $J_N$ requires

$$
 \ell_G(J_N)\ge\frac1{10}+\gamma_N
 \ge\frac1{10}+g-\rho_N
 \ge\frac1{10}+g-\frac25\delta_N.
\tag{8.18}
$$

After null bins are discarded, both laws have full support. Hence also
$\ell_G(J)>o_{ad}(J)\ge g>0$ and
$\ell_G(J_N)>o_{ad}(J_N)>0$. The plateau conditions above concern the plateau of the named law itself; no plateau implication between $J$ and $J_N$ is assumed. These are necessary conditions for the prescribed preparation families. The finite-law equality constructions in Theorem 8.2 assert no attainment within those families, native atom-to-preparation encoding, neural-training outcome or empirical conclusion. The projected-input law need not be Gaussian.

Proof. The original five complete-record laws are
$\nu_i=\mathcal N_{t+1}(\mu_i,\Sigma)$, with the same $\Sigma$ for every label. Use the classical equal-covariance total-variation identity stated by Devroye–Mehrabian–Reddad, [*The total variation distance between high-dimensional Gaussians*, arXiv:1810.08693v7, §2, equal-covariance passage](https://arxiv.org/html/1810.08693v7#S2), there attributed to Barsov–Ul’yanov, Theorem 1:

$$
 \operatorname{TV}(\nu_a,\nu_d)=2\Phi(d/2)-1,
 \qquad
 \int\min\{p_a(z),p_d(z)\}\,dz=2\Phi(-d/2).
\tag{8.19}
$$

This is a reused Gaussian identity, with the TV convention of Proposition 7.5. The functions $p_a,p_d$ here are complete-record densities, rather than label-prior coordinates. If $B_q=\kappa^{-1}(q)$, then

$$
 \begin{aligned}
 o_{ad}(J)
 &=\frac15\sum_q\min\left\{\int_{B_q}p_a,\int_{B_q}p_d\right\}\\
 &\ge\frac15\sum_q\int_{B_q}\min\{p_a,p_d\}
 =\frac25\Phi(-d/2)=g.
 \end{aligned}
$$

Thus a common quantizer can increase the row overlap; equality is not asserted for an arbitrary quantizer.

For the projection bound, write $K_i=\kappa_*\nu_w(W_i)$ and
$K_{i,N}=\kappa_*\nu_{w,N}(W_i)$, which are probability laws on the same finite alphabet. Since $\sum_q\min\{P(q),Q(q)\}=1-\operatorname{TV}(P,Q)$ for probability rows,

$$
 \begin{aligned}
 |o_{ad}(J_N)-o_{ad}(J)|
 &=\frac15\left|\operatorname{TV}(K_a,K_d)
       -\operatorname{TV}(K_{a,N},K_{d,N})\right|\\
 &\le\frac15\bigl(\operatorname{TV}(K_a,K_{a,N})
                    +\operatorname{TV}(K_d,K_{d,N})\bigr)\\
 &\le\frac{\sqrt{t_N(W_a)}+\sqrt{t_N(W_d)}}5=\rho_N.
 \end{aligned}
\tag{8.20}
$$

The first inequality is the TV triangle inequality in both directions. The second uses contraction under the common quantizer and [the Gaussian record volume, Proposition 14.2](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md). Only the two indicated preparations enter this estimate. Combining it with the original overlap bound and nonnegativity proves (8.16). Apply (8.3) and (8.7) directly to each finite law to obtain (8.17). Setting its own $D$ equal to zero proves the corresponding plateau condition and (8.18).

Proposition 7.7 proves full support for both laws from the positive original Gaussian densities and the positive Gaussian-pointer convolution (7.14) for projected inputs. The strict overlap/leakage statements now follow from (8.4); $g>0$ follows because $d$ is finite. This use of the projected law requires no Gaussianity of that law. The limit $\rho_N\to0$ holds at fixed original apparatus noise $\sigma>0$ and with the same complete fixed-word measurement; it approximates only the initial inputs. It does not remove that observation noise or identify a finite equality construction with a preparation in this family. All statements concern unconditional externally fixed-word laws and their common quantized images. $\square$

## 追加锚（本行以下为增补区）

## 9. Equal-covariance Gaussian plateaux and the exact copy threshold

**假设 9.1（均匀原标签与独立重复记录）。** Let $C$ be uniform on the five original labels $\{a,b,c,d,e\}$. For a positive integer $n$, conditional on $C=i$, observe

$$
 X_1,\ldots,X_n\ \overset{\mathrm{iid}}\sim\mathcal N_p(\mu_i,\Sigma),
 \qquad p\ge1,\quad \mu_i\in\mathbb R^p,\quad \Sigma=\Sigma^T>0.
\tag{9.1}
$$

The covariance is common to all labels and copies. Coincident means retain their separate labels and individual priors $1/5$; the affine hull of the means may have any dimension. Each repetition is an additional independent observation conditional on the same label. No legal-edge support condition (1.3) is imposed.

**定义 9.2（原始平台、均值簇与有限读出）。** Put $\bar X=n^{-1}\sum_{k=1}^nX_k$. Let $v_i^{(n)}$ be the posterior given the whole tuple, and define

$$
 r_i^{(n)}=\mathbb E\min\{v_i^{(n)},1-v_i^{(n)}\},\qquad
 \epsilon_n=\mathbb E(1-\max_i v_i^{(n)}).
\tag{9.2}
$$

The full raw indicator plateau means $r_i^{(n)}=1/5$ for all five labels. These are unweighted binary $0$–$1$ Bayes errors under the stated deployment prior, not balanced-resampling errors or an assertion about every scoring rule. A mean cluster consists of the labels with exactly the same mean; its multiplicity is their number. For any finite Borel quantizer $Q=\kappa_n(X_1,\ldots,X_n)$ common to the five labels, use $r_i(Q)$ and $\epsilon(Q)$ as in Definition 1.1. The quantizer may depend on the specified experiment and on $n$. Write

$$
 \langle x,y\rangle_{\Sigma^{-1}}=x^T\Sigma^{-1}y,\qquad
 h_e(\theta)=-\theta\ln\theta-(1-\theta)\ln(1-\theta),
 \quad 0<\theta<1.
\tag{9.3}
$$

Here $h_e$ uses natural logarithms, unlike $h$ in Definition 1.1.

**定理 9.3（五标签的穷尽平台分类与首个逃逸整数）。** Under Assumption 9.1 the full raw plateau holds for every positive integer $n$ precisely in either of the following permanent cases: there is one mean cluster, or there are exactly two distinct mean clusters of multiplicities $2$ and $3$. The only other configuration that can have a raw plateau is three distinct clusters with multiplicities $2,1,2$, whose singleton mean lies strictly between the two double-cluster means. Denote these means by

$$
 \mu_0=(1-\theta)\mu_-+\theta\mu_+,\qquad
 0<\theta<1,\qquad
 \Delta^2=\|\mu_+-\mu_-\|_{\Sigma^{-1}}^2>0.
\tag{9.4}
$$

In this configuration the exact criterion and first escaping copy number are

$$
 \boxed{\quad r_i^{(n)}=1/5\ \text{for all }i
 \iff n\le n_{\rm crit},\qquad
 n_{\rm crit}=\frac{2[\ln2+h_e(\theta)]}
 {\theta(1-\theta)\Delta^2},\qquad
 n_{\rm esc}=\lfloor n_{\rm crit}\rfloor+1.\quad}
\tag{9.5}
$$

Only the singleton indicator can improve in this case. Equality in (9.5) belongs to the plateau: if $n_{\rm crit}$ is an integer, escape starts at the next integer; if $n_{\rm crit}<1$, escape starts at $1$. Every configuration outside the permanent cases and (9.4) has an exposed singleton mean whose indicator strictly improves for every $n\ge1$. Endpoint coincidences $\theta=0,1$ merge the singleton with an endpoint and give the permanent $3+2$ case; if the endpoints coincide, all three means coincide. These degeneracies use the cluster classification, not division by zero in (9.5).

Within this experiment, the raw plateau is equivalent to the plateau of every finite common Borel quantizer. When the raw plateau fails, some two-bin common Borel quantizer retains a strict indicator improvement. This is an application of the mature binary Bayes/conditioning identities used in Proposition 2.1, not an additional generic comparison theorem. A constant quantizer always has the full plateau, including when the raw experiment escapes; no threshold is asserted for an arbitrary fixed quantizer.

Proof. The classical common-covariance Gaussian discriminants, as in Hastie–Tibshirani–Friedman, [*The Elements of Statistical Learning*, corrected twelfth printing, §4.3, equation (4.10), printed p.109](https://hastie.su.domains/ElemStatLearn/download.html), give here

$$
 \begin{aligned}
 \ell_i(x)&=n\langle\mu_i,x\rangle_{\Sigma^{-1}}
       -\tfrac n2\|\mu_i\|_{\Sigma^{-1}}^2,\\
 v_i^{(n)}(x)&=\frac{e^{\ell_i(x)}}{\sum_j e^{\ell_j(x)}},
 \qquad x=\bar X.
 \end{aligned}
\tag{9.6}
$$

Indeed expanding the product density cancels every term independent of the label, leaving (9.6); thus the full tuple has the same posterior as its mean. The equal priors cancel per original label, not per mean cluster. The identity (2.3) becomes

$$
 \frac15-r_i^{(n)}=\mathbb E(2v_i^{(n)}(\bar X)-1)_+.
\tag{9.7}
$$

All posteriors in (9.6) are continuous and the law of $\bar X$ has an everywhere positive density. Therefore the raw plateau is equivalent to $v_i^{(n)}(x)\le1/2$ for every $i,x$. A label in a cluster of multiplicity $m\ge2$ satisfies $v_i^{(n)}(x)\le1/m\le1/2$ for all $x,n$. If every cluster has multiplicity at least two, five labels allow exactly the two permanent cases stated above.

For a singleton mean that is a vertex of the convex hull of the distinct means, strictly separate that vertex from the convex hull of the others. Equivalently, for the whitened means $b_j=\Sigma^{-1/2}\mu_j$, there is a vector $u$ with $u^Tb_i>u^Tb_j$ for all other clusters. Along $\Sigma^{-1/2}x=tu$ as $t\to\infty$, (9.6) makes its posterior tend to one for each fixed $n>0$. It consequently exceeds $1/2$ on an open set of positive probability, giving strict improvement by (9.7). If there are at least two distinct means and no singleton vertex, at least two vertices must each have multiplicity at least two. They use at least four labels. Thus either they exhaust the clusters in the $2+3$ case, or the only remaining label is a singleton strictly inside their segment, giving exactly (9.4). This proves exhaustiveness, including lower-dimensional affine hulls.

For (9.4) set $d=\mu_+-\mu_-$, $R=n\Delta^2$, and $T=n\langle d,x-\mu_0\rangle_{\Sigma^{-1}}$. Since $d\ne0$, $T$ ranges over all real numbers. After dividing the endpoint likelihoods by the singleton likelihood, its posterior is $v_0^{(n)}=1/(1+F_n(T))$, where

$$
 \begin{aligned}
 F_n(T)&=2e^{-\theta T-\theta^2R/2}
        +2e^{(1-\theta)T-(1-\theta)^2R/2},\\
 T_*&=\ln\frac{\theta}{1-\theta}+\frac{1-2\theta}{2}R,\\
 \min_{T\in\mathbb R}F_n(T)
 &=F_n(T_*)
 =2\exp\!\left(h_e(\theta)-\tfrac12\theta(1-\theta)n\Delta^2\right).
 \end{aligned}
\tag{9.8}
$$

To verify the minimum, differentiate: $F_n''>0$, $F_n\to\infty$ at both ends, and $F_n'=0$ says that the second exponential divided by the first is $\theta/(1-\theta)$. Substitution gives (9.8). This is the two-coordinate log-sum-exp/entropy conjugacy of Boyd–Vandenberghe, [*Convex Optimization*, Example 3.25, printed p.93](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf), used as an intermediate tool. The condition $F_n\ge1$ everywhere is exactly (9.5). At equality the singleton reaches $1/2$ only on the hyperplane $T=T_*$, which has probability zero. Above the threshold it exceeds $1/2$ on a nonempty open slab, so the improvement is strict. Since $n_{\rm crit}$ is positive and finite, the integer and permanent-case assertions follow.

For the finite-readout assertions, the posterior given $Q$ is $\mathbb E[v_i^{(n)}\mid Q]$. Hence a raw plateau remains a plateau under every such quantizer. Conversely, if label $i$ improves, use the two bins of its Bayes decision,
$Q_i=\mathbf1_{\{v_i^{(n)}(\bar X)>1/2\}}$. On each bin the optimal binary action is constant, so $r_i(Q_i)=r_i^{(n)}<1/5$. A constant readout has posterior $1/5$ at every label. The quantifiers concern all finite quantizers or an experiment-dependent witness, not preservation of escape by an unspecified fixed readout. $\square$

**定理 9.4（对称分类风险与共同有限见证）。** In dimension one take $\Sigma=s^2$, $s>0$, and means $(-a,0,a)$ with multiplicities $(2,1,2)$, $a>0$. Put $q=\sqrt n\,a/s$. Then

$$
 \boxed{\epsilon_n=\frac{6-4\Phi(q/2)}5<\frac45,\qquad
 \text{full raw plateau}\iff\frac{q^2}{2}\le\ln4.}
\tag{9.9}
$$

The finite common readout reporting which of the three intervals

$$
 \bar X<-a/2,\qquad -a/2\le\bar X\le a/2,\qquad \bar X>a/2
\tag{9.10}
$$

contains the sample mean has exactly the same categorical Bayes error as the raw tuple. Throughout the plateau range in (9.9), it also has $r_i(Q)=1/5$ for every original label. Thus one finite joint law exhibits categorical improvement and the full unweighted indicator plateau simultaneously. This is an observation-law witness, not an asserted preparation tuple in the source model.

Proof. Equal original-label priors make a categorical Bayes rule choose the largest individual likelihood, rather than the cluster likelihood multiplied by its multiplicity. The three maximizing mean regions are (9.10); within either double cluster choose one fixed representative label. The conditional probabilities of its correct region at means $-a,0,a$ are respectively $\Phi(q/2)$, $2\Phi(q/2)-1$, $\Phi(q/2)$. Only one label per cluster is guessed, so the total correct probability is $(4\Phi(q/2)-1)/5$, proving the error formula. The same rule is a function of the finite readout (9.10), so its categorical risk equals the raw optimum; quantization cannot improve that optimum. Since $q>0$, $\Phi(q/2)>1/2$, giving the displayed strict categorical improvement. Substituting $\theta=1/2$ and $\Delta^2=4a^2/s^2$ in (9.5) gives $q^2/2\le\ln4$, including equality. The finite plateau then follows from Theorem 9.3. All finite $q$ give positive categorical error, and the error tends to $2/5$ as $q\to\infty$ because the duplicate labels remain indistinguishable. The existence of this common three-bin witness supplies no escape threshold for an arbitrary fixed quantizer. $\square$

**定理 9.5（原始固定词高斯源的条件代入）。** Supply five original preparations $W_i\in K_J$ exactly as in Assumptions 7.6 and 8.4, with uniform original labels, one externally fixed word $w=E_1\cdots E_t$, $0\le t\le7$, and fixed apparatus noise $\sigma>0$. For their complete original record laws set

$$
 p=t+1,\qquad \mu_i=L_wm_{W_i}=L_w\mu(W_i),\qquad
 \Sigma=\tfrac12L_wL_w^T+\sigma^2I_{t+1}.
\tag{9.11}
$$

For $n=1$, Theorem 9.3 applies to precisely this original observation. For $n>1$, it applies if each copy is produced by an independent preparation conditional on the same label, using that same word and apparatus. The experiment consumes $n$ independently prepared copies in total, each with its full record; the later copies are additional resources, not extra reads extracted from the first preparation. With the supplied means, its classification and threshold hold for the raw records, imply a plateau for every finite common quantization when the raw plateau holds, and guarantee an escaping two-bin quantization when it fails. The symmetric conclusion of Theorem 9.4 applies only if the supplied observation laws have its specified symmetric parameters; no such preparation attainer is asserted.

Proof. [The Gaussian record volume, Theorem 5.1 and Proposition 14.2](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md) give exactly $\nu_w(W_i)=\mathcal N_{t+1}(L_wm_{W_i},\Sigma)$, with $\Sigma\succeq\sigma^2I>0$ independent of $i$. Conditional independence of the separately prepared repetitions gives (9.1); correlations among the clock reads within one full record remain in $\Sigma$. The equal label prior is explicitly supplied, so (9.11) verifies every hypothesis of the preceding classification, with no prior on all of $K_J$ required.

The normalized projected-input laws of the source's §14 need not be Gaussian. Their TV approximation to the original laws does not supply this exact Gaussian plateau threshold or transfer a plateau equality between the two families. For each finite $n$, the original conditional product densities are everywhere positive; hence no zero-error categorical decision follows from escape, consistently with the finite-copy equivalence argument in the source's §33. This conditional substitution assumes the specified preparations and fixed protocol; it establishes no native atom encoding, preparation realization or cost, adaptive-word conclusion, unequal-prior or unequal-covariance extension, training gain, empirical truth or useful uniform positive error margin. The Gaussian discriminants, entropy conjugacy, Bayes partitions and exposed-vertex argument are mature intermediate tools. The five-label multiplicity classification, exact copy boundary and witness above are repo-derived application exposition, without a global-priority claim. $\square$

## 追加锚（本行以下为增补区）

## 10. Exact singleton gain, acquisition targets and inward-threshold retention

**假设 10.1（对称实验与已知律风险）。** Retain exactly the experiment of Theorem 9.4: five original labels with priors $1/5$, scalar means $(-a,0,a)$ of multiplicities $(2,1,2)$, common variance $s^2$, and $a,s>0$. Denote the singleton label by $0$. For a positive integer $n$, given one fixed label, the observations come from conditionally independent preparations as in (9.1), and

$$
 Y=\frac{\sqrt n\,\bar X}{s},\qquad
 q=\frac{\sqrt n\,a}{s},\qquad
 q_c=\sqrt{2\ln4},\qquad
 e=\frac{q^2}{2}-\ln4,\qquad
 B(q)=\frac15-r_0(q).
\tag{10.1}
$$

Here $r_0(q)$ is the singleton's binary $0$–$1$ Bayes risk for the full observation under its known law. Conditional on the three means, $Y$ has laws $\mathcal N(-q,1)$, $\mathcal N(0,1)$ and $\mathcal N(q,1)$, respectively. The same three laws define a continuous interpolation for real $q>0$; actual copy counts remain positive integers. Let $\phi$ and $\Phi$ be the standard normal density and distribution function.

The Bayes and conditioning identities of Proposition 2.1 and §9 are reused below. As mature statistical context, Audibert–Tsybakov, [*Fast learning rates for plug-in classifiers*, equation (1.1) and margin assumption (1.7)](https://arxiv.org/pdf/0708.2321), study classifier estimation regret and the posterior margin for a fixed experiment. Here the classifier is already Bayes optimal and $q$ changes the experiment; the local exponent below is not a training rate or a neural-learning exponent. The following is repo-derived application exposition of these mature tools, without a claim of literature novelty or global priority.

**定理 10.2（精确增益及其起始系数）。** For $0<q\le q_c$, $B(q)=0$. For $q>q_c$, set

$$
 z=z(q)=\frac{\operatorname{arcosh}(\exp(e))}{q}.
$$

Then

$$
 \boxed{B(q)=\frac{2\Phi(z)-1
 -4\bigl(\Phi(z-q)+\Phi(z+q)-1\bigr)}5.}
\tag{10.2}
$$

The function is continuous at $q_c$, strictly increasing on $(q_c,\infty)$, satisfies $0<B(q)<1/5$ at every finite $q>q_c$, and tends to $1/5$ as $q\to\infty$. Along the continuous interpolation, as $e\downarrow0$ through positive values,

$$
 \boxed{B(q)\sim C e^{3/2},\qquad
 C=\frac4{15q_c\sqrt\pi}.}
\tag{10.3}
$$

Proof. Equal priors per original label and (9.6) give the singleton posterior $v_0(y)=(1+4e^{-q^2/2}\cosh(qy))^{-1}$. Multiplying the positive-part identity (9.7) by the mixture density gives

$$
 \begin{aligned}
 D_q(y)&=\phi(y)-2\phi(y-q)-2\phi(y+q)
       =\phi(y)\bigl[1-e^{-e}\cosh(qy)\bigr],\\
 B(q)&=\frac15\int_{\mathbb R}(D_q(y))_+\,dy.
 \end{aligned}
\tag{10.4}
$$

Thus $D_q\le0$ everywhere when $e\le0$; at $e=0$ its sole zero is $y=0$. For $e>0$ its positive set is exactly $(-z,z)$. Integrating the three Gaussian densities on this interval proves (10.2), including the factor four from the two labels at each endpoint.

On $(q_c,\infty)$ the endpoints are smooth and $D_q(\pm z)=0$, so differentiating that finite-interval integral has no endpoint term and yields

$$
 B'(q)=\frac45\bigl[\phi(z-q)-\phi(z+q)\bigr]>0.
\tag{10.5}
$$

Indeed $(z+q)^2-(z-q)^2=4zq>0$. Positivity follows also from the positive integrand near zero, and
$B(q)\le[2\Phi(z)-1]/5<1/5$ for finite $z$. As $q\downarrow q_c$, $z\to0$ and (10.2) tends to zero. As $q\to\infty$, $\operatorname{arcosh}(\exp(e))=e+\ln2+o(1)$, hence $z=q/2-(\ln2)/q+o(q^{-1})$. Consequently $z\to\infty$, $z-q\to-\infty$ and $z+q\to\infty$, giving the stated limit in (10.2).

For the onset, put $t=qz=\operatorname{arcosh}(\exp(e))$. Taylor expansion of $\cosh t=\exp(e)$ at zero gives $t^2=2e+O(e^2)$, while $q=q_c+O(e)$ and $z\sim\sqrt{2e}/q_c$. Uniformly for $-1\le x\le1$,

$$
 \begin{aligned}
 1-e^{-e}\cosh(tx)&=e(1-x^2)+O(e^2),\\
 \phi(zx)&=\phi(0)(1+O(e)),\\
 B(q)&=\frac{ze\phi(0)}5
       \left[\int_{-1}^1(1-x^2)\,dx+O(e)\right]
       \sim\frac{4\sqrt2\phi(0)}{15q_c}e^{3/2}.
 \end{aligned}
\tag{10.6}
$$

Since $\phi(0)=(2\pi)^{-1/2}$, the coefficient is exactly (10.3). This is a local asymptotic, and does not supply a useful uniform positive gain as the threshold is approached. $\square$

**推论 10.3（给定正增益的最少独立取得次数）。** For each $0<\delta<1/5$, there is exactly one $q_\delta>q_c$ with $B(q_\delta)=\delta$. Under Assumption 10.1 the least permitted number of copies achieving $B(\sqrt n\,a/s)\ge\delta$ is

$$
 \boxed{n_\delta=\left\lceil (s/a)^2q_\delta^2\right\rceil.}
\tag{10.7}
$$

Equality at the continuous target achieves the target; no extra copy is required when $(s/a)^2q_\delta^2$ is an integer. Before integer rounding, the excess precision satisfies

$$
 e_\delta=\frac{q_\delta^2}{2}-\ln4
 \sim\left(\frac\delta C\right)^{2/3}
 \quad(\delta\downarrow0).
\tag{10.8}
$$

For $\delta=0$ the least allowed count is $1$; $\delta=1/5$ is unattainable at finite $n$. The count in (10.7) concerns independent acquisitions conditional on one label, and omits preparation, control and threshold-computation costs. It is neither a training-set size nor the number of repeated reads of one preparation.

Proof. Continuity, strict increase and the endpoint limits in Theorem 10.2 prove existence and uniqueness. For positive integer $n$, monotonicity gives $B(\sqrt n\,a/s)\ge\delta$ exactly when $n\ge(s/a)^2q_\delta^2$, proving the ceiling and its equality case. As $\delta\downarrow0$, $q_\delta\downarrow q_c$; substituting into (10.3) and inverting gives (10.8). The endpoint targets follow from $B\ge0$ and its strict finite-$q$ upper bound. Continuous interpolation and (10.8) introduce no fractional preparations and no asymptotic assertion about a ceiling's rounding error. $\square$

**定理 10.4（向内阈值误差下的量化增益保留）。** Fix $q>q_c$ and let the same binary Borel readout for all five labels be $Q_u=\mathbf1_{\{|Y|<u\}}$, where $0\le u\le z(q)$. Its singleton Bayes gain is exactly

$$
 \begin{aligned}
 G(q,u)&:=\frac15-r_0(Q_u)\\
 &=\frac{2\Phi(u)-1
 -4\bigl(\Phi(u-q)+\Phi(u+q)-1\bigr)}5,
 \qquad G(q,z)=B(q).
 \end{aligned}
\tag{10.9}
$$

If an inward placement error is explicitly assumed to satisfy $0\le z-u\le h<z$, then

$$
 G(q,u)\ge G(q,z-h).
\tag{10.10}
$$

In particular, for $0<\theta<1$, the known-law inequality $G(q,z-h)\ge\theta B(q)$ is sufficient to retain at least a fraction $\theta$ of the raw singleton gain for every placement obeying that error bound. Along $e\downarrow0$, if $u/z\to\rho\in[0,1]$, then

$$
 \boxed{\frac{G(q,u)}{B(q)}\longrightarrow
 \frac{3\rho-\rho^3}{2}.}
\tag{10.11}
$$

Thus placing $u=z/2$ retains asymptotically $11/16$ of the gain.

Proof. The signed difference of the joint masses for singleton versus nonsingleton on $A_u=(-u,u)$ is $\frac15\int_{A_u}D_q(y)\,dy\ge0$, since $A_u\subseteq(-z,z)$. Its difference on the complement is $-3/5-\frac15\int_{A_u}D_q<0$, because $\frac15\int_{\mathbb R}D_q=-3/5$. Hence the binary Bayes action based on $Q_u$ guesses singleton on its central bin and nonsingleton on its complement. At $u=0$ the central bin is null and only the latter action matters. Subtracting this risk from $1/5$ gives $G(q,u)=\frac15\int_{-u}^uD_q$, proving (10.9) for the quantized Bayes optimum, rather than merely for a proposed decision rule. Boundary points have zero probability.

On $0\le u\le z$, the integrand is nonnegative, so $G$ is nondecreasing in $u$ and (10.10) follows. For the ratio write $v=u/z$. The uniform expansion (10.6), now integrated on $[-v,v]$, gives uniformly for $0\le v\le1$,

$$
 \frac{G(q,u)}{B(q)}
 =\frac{2v-2v^3/3+O(e)}{4/3+O(e)}.
$$

Taking $v\to\rho$ proves (10.11), including both endpoints; at $\rho=1/2$ it equals $11/16$.

This retention statement assumes the stated inward threshold bound. A two-symbol output alphabet by itself establishes neither finite physical threshold precision nor a cheap implementation, and the law-dependent choice of $u$ supplies no guarantee for an arbitrary fixed quantizer. The conditional source substitution remains exactly Theorem 9.5, using [the Gaussian record volume, Theorem 5.1 and Proposition 14.2](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md): no preparation realizing these symmetric means is asserted, and Gaussianity of the original law supplies no Gaussianity for a projected-input law. The Gaussian experiment, existence of a finite readout and physical precision of that readout are separate claims. These known-law conclusions establish no native atom encoding, adaptive-word result, empirical or out-of-distribution performance, or training gain. $\square$

## 追加锚（本行以下为增补区）

## 11. 占位仿射限制下的平台与四角读出核

**假设 11.1（仿射原子编码）。** 在 §9 的五标签等先验、共同正定协方差 $\Sigma$ 和同标签条件独立记录合同下，另供占位仿射均值

$$
(\mu_0,\mu_1,\mu_2,\mu_3,\mu_{13})=(0,u,w,v,u+v),
\qquad u,v,w\in\mathbb R^D.
\tag{11.1}
$$

完整平台仍专指五个原标签各自的无权二元 $0$–$1$ Bayes 风险均为 $1/5$。以下将定理9.3直接应用于这个受四角仿射关系约束的子类，不重复证明一般五均值分类，也不由原生高斯记录自动推定（11.1）。

**定理 11.2（仿射子类的穷尽平台判据）。** 固定正整数复制次数 $\ell$，完整原始平台恰好发生于以下情形：

- $u=v=w=0$；
- 交换端点后可写为 $u=0$、$v\ne0$、$w=\theta v$，其中 $0\le\theta\le1$。若 $\theta=0$ 或 $1$，平台永久成立；若 $0<\theta<1$，还必须且只须

$$
\ell\le
\frac{2[\ln2+h_e(\theta)]}
{\theta(1-\theta)\|v\|_{\Sigma^{-1}}^2}.
\tag{11.2}
$$

第一种平台也永久成立；（11.2）等号属于平台。在严格内点构型超过该阈值时，中位标签判断严格改善；若均值几何不属于上述两类，则至少一个单标签判断在每个 $\ell\ge1$ 严格改善。

证明。先设 $u,v$ 均非零。若线性独立，四个底角 $0,u,v,u+v$ 为一个非退化平行四边形的顶点。若 $w$ 与其中一个重合，仍有其他单标签顶点；若 $w$ 是不同的新点，则它位于原凸包内时原四顶点仍在，位于原凸包外时它自身是单标签顶点。故总有一个单标签暴露顶点。

若两向量共线，取一个实坐标使它们为非零数 $a,b$。集合 $\{0,a,b,a+b\}$ 的最小值由分别选择两个负贡献唯一实现，最大值由分别选择两个正贡献唯一实现，所以两个端点各仅有一个底角标签。若 $w$ 在线段内，至多重复其中一个端点；若在原凸包外或离开该直线，则它自身为单标签顶点。因此该情形也不可能有完整平台。这里使用定理9.3的暴露顶点结论：在每个正复制次数下，其后验在一个正概率区域超过 $1/2$。

若 $u=v=0$ 而 $w\ne0$，$w$ 是单标签顶点。余下恰有一个方向为零，交换后设 $u=0,v\ne0$。四个底角分为均值 $0$ 的标签 $\{0,1\}$ 与均值 $v$ 的标签 $\{3,13\}$。$w\notin[0,v]$ 时它自身为单标签顶点；$w=0,v$ 时为永久 $3+2$ 簇；严格内点 $w=\theta v$ 时恰为定理9.3的 $2$–$1$–$2$ 构型。将其端点距离代入（9.5）即得（11.2），包括阈值等号和退化边界。$\square$

**命题 11.3（标签逃逸仍可与四角永久失明并存）。** 在（11.1）中，若任一正整数复制次数出现完整原始平台，则固定 $X,Y,Z$ 的四角概率族

$$
p_\kappa=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa)
\tag{11.3}
$$

被该记录实验永久消去：对每个 $\ell\ge1$，整组同标签记录律均不依赖 $\kappa$。反向不成立；平台逃逸也不推出 $\kappa$ 可识别。

证明。定理11.2强制 $u=0$ 或 $v=0$。设 $u=0$，则 $0,1$ 两标签具有同一个整组高斯产品律，$3,13$ 也具有同一个产品律；各簇的 $d=(1,-1,0,-1,1)$ 系数和为零，故组分布对 $\kappa$ 的导数为零。$v=0$ 同理。这个结论也可由[《记录单纯形与高阶相容》定理14.1](AURIC_FIB_ATOM_RECORD_SIMPLEX_AND_HIGHER_ORDER_COMPATIBILITY.md)在堆叠读出向量上直接获得。各组重新抽标签仍只产生这些相同律的独立乘积。

具体取一维 $u=0,v=2,w=1,\Sigma=1$，均值为 $(0,0,1,2,2)$。等先验处 $X=Y=2/5,Z=1/5,\kappa=1/5$；在同一均值纤维的全部 $0\le\kappa\le2/5$，

$$
p_\kappa=(\kappa,2/5-\kappa,1/5,2/5-\kappa,\kappa),\qquad
f_\kappa(r)=\tfrac25\phi(r)+\tfrac15\phi(r-1)+\tfrac25\phi(r-2).
\tag{11.4}
$$

单份密度及任意同标签组密度都与 $\kappa$ 无关；但在等先验参考点，（11.2）的阈值为 $4\ln2\in(2,3)$，所以第三份同标签记录起中位标签判断严格改善。若改取 $w=3$，仍有 $u=0$ 和四角失明，但 $w$ 是单标签端点，第一份记录即严格改善，表明四角失明不蕴含平台。$\square$

这些结论将两种目标放在同一个仿射实验中比较：判别一个抽中的原标签，与估计固定均值纤维上的总体概率关系，是不同任务。完整分布核、特定风险的平台及正信息下的取得成本分别由不同判据控制；有限标签可分类不等于总体概率可恢复。此处复用 §9 的一般平台分类，新增的是占位仿射约束下的排除几何及其与四角核的对应，不主张新的通用 Gaussian 判别工具、原生原子编码或物理制备实现。

## 追加锚（本行以下为增补区）
