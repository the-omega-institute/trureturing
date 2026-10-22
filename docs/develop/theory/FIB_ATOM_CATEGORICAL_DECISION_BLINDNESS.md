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
## 11. Off-axis Gaussian escape is exponentially faint

**假设 11.1（uniform five-original-label Gaussian experiment）。** Let the five original labels have prior $1/5$, covariance $I_2$, and means

$$
\mu_1=\mu_2=(-q,0),\qquad \mu_3=(0,b),\qquad
\mu_4=\mu_5=(q,0),
$$

where $q$ is fixed with $0<q<\sqrt{2\ln4}$ and $b>0$. Write $r_0(q,b)$ for the infimum binary zero--one risk for deciding whether the label is the singleton $3$ from one complete observation, and put

$$
B(q,b)=\frac15-r_0(q,b),\qquad
c(q)=\ln4-\frac{q^2}{2}>0.
$$

This is a continuous two-dimensional observation law; no preparation, quantizer, training, or physical-realization assertion is part of the assumption.

**定理 11.2（exact pointwise logarithmic gain）。** Under Assumption 11.1,

$$
\boxed{\displaystyle
\lim_{b\downarrow0} b^2\ln B(q,b)
=-\frac12\left(\ln4-\frac{q^2}{2}\right)^2.}
\tag{11.1}
$$

The conclusion is pointwise in the fixed $q$ and supplies neither a prefactor nor a statement at the critical value $q=\sqrt{2\ln4}$.

Proof. Let $x=(u,v)$ and let $\phi$ be the standard normal density. The singleton density and the two duplicated endpoint densities are

$$
 f_0(u,v)=\phi(u)\phi(v-b),\qquad
 f_\pm(u,v)=\phi(u\mp q)\phi(v).
$$

The signed Bayes gain is the positive part of the singleton prior density minus the aggregate competing prior density, hence the binary Bayes identity used in Proposition 2.1 gives

$$
 B(q,b)=\frac15\int_{\mathbb R^2}
 \bigl(f_0-2f_- -2f_+\bigr)_+\,du\,dv.
\tag{11.2}
$$

Factoring the common density gives the signed integrand

$$
 D_b(u,v):=f_0-2f_- -2f_+
 =\phi(u)\phi(v)
 \left[e^{bv-b^2/2}-4e^{-q^2/2}\cosh(qu)\right].
\tag{11.3}
$$

Set $A(u)=4e^{-q^2/2}\cosh(qu)$. Since $A(u)\ge A(0)=e^{c(q)}$, the positive region of $D_b$ is contained in

$$
 v>\frac{\ln A(u)+b^2/2}{b}
 \quad\Longrightarrow\quad
 v>\frac{c(q)}b+\frac b2.
\tag{11.4}
$$

As $D_b\le f_0$ pointwise, (11.2), (11.4), and the standard Gaussian-tail logarithmic asymptotic
$\lim_{x\to\infty}x^{-2}\ln\overline\Phi(x)=-1/2$ imply

$$
\limsup_{b\downarrow0} b^2\ln B(q,b)
\le -\frac{c(q)^2}{2}.
\tag{11.5}
$$

For the reverse inequality, fix $\varepsilon>0$. By continuity of $\ln\cosh(qu)$ at $u=0$, choose $\delta>0$ such that
$\ln A(u)\le c(q)+\varepsilon/2$ whenever $|u|\le\delta$. For all sufficiently small $b$, on the slab

$$
R_b=\left\{|u|\le\delta,\quad v\ge\frac{c(q)+\varepsilon}{b}\right\}
$$

we have $e^{bv-b^2/2}\ge e^{c(q)+\varepsilon-b^2/2}$ and therefore, for a constant $\kappa_\varepsilon>0$ independent of $b$,

$$
D_b(u,v)\ge \kappa_\varepsilon\,f_0(u,v)\qquad ((u,v)\in R_b).
\tag{11.6}
$$

This signed lower bound is essential: the probability of the positive region alone would not lower-bound the positive-part integral. Integrating (11.6) in (11.2) yields

$$
 B(q,b)\ge \frac{\kappa_\varepsilon}{5}
 \Pr\{|U|\le\delta\}\,
 \overline\Phi\!\left(\frac{c(q)+\varepsilon}{b}-b\right),
\tag{11.7}
$$

where $U\sim\mathcal N(0,1)$. Consequently,

$$
\liminf_{b\downarrow0} b^2\ln B(q,b)
\ge -\frac{(c(q)+\varepsilon)^2}{2}.
\tag{11.8}
$$

Letting $\varepsilon\downarrow0$ and combining (11.5) with (11.8) proves (11.1). $\square$

**推论 11.3（approximate blindness and the finite-law TV bridge）。** For every fixed $q$ in the range of Theorem 11.2,

$$
 B(q,b)=\exp\!\left[-\frac{c(q)^2}{2b^2}+o(b^{-2})\right],
\qquad b\downarrow0,
\tag{11.9}
$$

so the singleton binary risk remains within this exponentially small gain of its blind value $1/5$. This quantifies the approach to the $b=0$ plateau without asserting a derivative, a prefactor, or a uniform estimate in $q$.

If a finite common Borel quantizer is subsequently supplied for the same-prior experiment, its singleton gain $B_Q=1/5-r_0(Q)$ satisfies $0\le B_Q\le B(q,b)$ by conditioning. For two finite joint laws on that common alphabet, Proposition 7.5 gives $|B_Q-B'_Q|\le\operatorname{TV}(J,J')$; under the original/projected-input hypotheses of Proposition 7.7 this becomes $|B_Q-B'_{Q}|\le e_N$. Relative retention from these additive certificates requires a positive $B_Q$ and an error bound small relative to $B_Q$. An explicitly supplied lower bound making $B_Q$ comparable to $B(q,b)$, together with an error bound small relative to $B(q,b)$, also suffices. A constant quantizer has $B_Q=0$, so $\operatorname{TV}(J,J')=o(B(q,b))$ alone gives no relative-retention guarantee for an arbitrary quantizer. These are the existing same-prior soft-risk certificates applied to this gain; they do not transfer (11.1) to a projected law, imply a hard-support impossibility, or provide a native preparation attainer. $\square$

## 追加锚（本行以下为增补区）

## 12. Exact off-axis prefactor and a gain-preserving binary readout

**定义 12.1（fixed-law notation）。** Retain exactly Assumption 11.1: one complete two-dimensional observation, uniform prior on the five original labels, covariance $I_2$, means $(-q,0),(-q,0),(0,b),(q,0),(q,0)$, and fixed $0<q<\sqrt{2\ln4}$ while $b\downarrow0$. Write

$$
\begin{aligned}
 c&=c(q)=\ln4-q^2/2>0,\\
 L(u)&=c+\ln\cosh(qu),\\
 \phi(x)&=(2\pi)^{-1/2}e^{-x^2/2},\qquad
 \overline\Phi(x)=\int_x^\infty\phi(v)\,dv,\\
 E_b&=\exp\!\left(-\frac{c^2}{2b^2}\right),\qquad
 B(q,b)=\frac15-r_0(q,b).
\end{aligned}
\tag{12.1}
$$

The quantities $r_0$ and $B$ concern the known-law binary decision of label $3$ versus its complement. The five Gaussian labels here are the labels of this observation experiment; their specification does not construct a native recursive FIB classification or its preparations.

**定理 12.2（pointwise exact prefactor）。** Under Definition 12.1,

$$
 \boxed{B(q,b)\sim C(q)b^4E_b,\qquad
 C(q)=\frac{e^{c(q)/2}}{5\sqrt{2\pi}\,q\,c(q)^{5/2}}>0.}
\tag{12.2}
$$

Thus the power $\alpha=4$ is common to every fixed $q$ in the stated open interval. The equivalence is pointwise in $q$; it asserts no endpoint, joint-$q$ limit, uniform remainder or explicit finite-$b$ cutoff.

Proof. Reuse the signed density $D_b$ of (11.3) and its positive-part Bayes identity (11.2). For a scalar $\ell>0$, put

$$
\begin{aligned}
 t_b(\ell)&=\frac{\ell+b^2/2}{b},\\
 J_b(\ell)&=\int_{\mathbb R}\phi(v)
       [e^{bv-b^2/2}-e^\ell]_+\,dv\\
 &=\overline\Phi(t_b(\ell)-b)
       -e^\ell\overline\Phi(t_b(\ell)),\\
 B(q,b)&=\frac15\int_{\mathbb R}\phi(u)J_b(L(u))\,du.
\end{aligned}
\tag{12.3}
$$

Indeed, the bracket is positive exactly when $v>t_b(\ell)$, and $\phi(v)e^{bv-b^2/2}=\phi(v-b)$. Tonelli's theorem applies to the nonnegative integrand. This integrates the signed excess itself, including the cancellation between its two tails; the probability of the positive region would not determine its prefactor.

For $x>0$, let $R(x)=\overline\Phi(x)/\phi(x)$. The complementary-error-function expansion and real-positive remainder bound in [NIST DLMF §7.12(i), equation (7.12.1)](https://dlmf.nist.gov/7.12#i), with $\overline\Phi(x)=\tfrac12\operatorname{erfc}(x/\sqrt2)$, give

$$
 R(x)=x^{-1}-x^{-3}+O(x^{-5}).
$$

Its exact derivative identity, obtained by differentiating the defining quotient, gives

$$
 R'(x)=xR(x)-1=-x^{-2}+O(x^{-4}).
\tag{12.4}
$$

No differentiation of an asymptotic remainder is used. Fix $0<a<A<\infty$. Uniformly for $\ell\in[a,A]$ and $x\in[t_b(\ell)-b,t_b(\ell)]$, we have $x=\ell/b+O(b)$ and $x\ge a/(2b)$ for all sufficiently small $b$. The real-positive remainder estimate in (12.4) therefore gives, uniformly on these intervals,

$$
 -R'(x)=\frac{b^2}{\ell^2}(1+O(b^2)),\qquad
 R(t_b(\ell)-b)-R(t_b(\ell))
 =\int_{t_b(\ell)-b}^{t_b(\ell)}-R'(x)\,dx
 =\frac{b^3}{\ell^2}(1+O(b^2)).
\tag{12.5}
$$

The constants may depend on $a,A$, not on $\ell$ or $b$. Since

$$
 \phi(t_b(\ell)-b)=e^\ell\phi(t_b(\ell)),\qquad
 e^\ell\phi(t_b(\ell))
 =\frac1{\sqrt{2\pi}}
   \exp\!\left(-\frac{\ell^2}{2b^2}+\frac\ell2-\frac{b^2}{8}\right),
$$

(12.3) and (12.5) imply the compact-uniform estimate

$$
 J_b(\ell)=\frac{b^3}{\sqrt{2\pi}\,\ell^2}
       \exp\!\left(-\frac{\ell^2}{2b^2}+\frac\ell2\right)
       (1+O(b^2)),\qquad \ell\in[a,A].
\tag{12.6}
$$

In particular, the displacement $b/2$ in the threshold contributes the factor $e^{\ell/2}$.

To control the noncompact $u$-integral, choose a sufficiently small fixed $\delta>0$. The function $L$ is even, has its unique minimum $c$ at zero and is strictly increasing on $(0,\infty)$. Thus, with $m=L(\delta)>c$, we have $L(u)\ge m$ for $|u|\ge\delta$. The integral definition of $J_b$ shows it is nonincreasing in $\ell$. Consequently

$$
 0\le\int_{|u|\ge\delta}\phi(u)J_b(L(u))\,du
 \le J_b(m)
 \le\overline\Phi(m/b-b/2)
 =O\!\left(b\exp\!\left[-\frac{m^2}{2b^2}\right]\right).
\tag{12.7}
$$

For the last bound, $m/b-b/2>0$ for small $b$, and
$\overline\Phi(x)\le\phi(x)/x$ for $x>0$; this inequality follows by bounding $1\le v/x$ inside the tail integral. The factor $\exp(m/2-b^2/8)$ is bounded with $m$ fixed. Dividing (12.7) by $b^4E_b$ gives an upper bound of order $b^{-3}\exp(-(m^2-c^2)/(2b^2))$, which tends to zero. No compact-uniform Mills estimate is being applied to unbounded $L(u)$.

On $|u|\le\delta$, Taylor expansion gives

$$
 L(u)=c+\frac{q^2u^2}{2}+O(u^4).
\tag{12.8}
$$

Because $q>0$, shrink $\delta$ so that $L(u)-c\ge\kappa u^2$ there for some $\kappa>0$. On this interval $L$ lies in the compact positive interval $[c,L(\delta)]$, so (12.6) applies uniformly. After extracting $E_b$, its remaining local integral is

$$
 H_b=\int_{|u|\le\delta}\phi(u)L(u)^{-2}
       \exp\!\left(-\frac{L(u)^2-c^2}{2b^2}+\frac{L(u)}2\right)du.
$$

Set $u=by$, and extend the resulting integrand by zero outside $|y|\le\delta/b$. For each fixed $y$, (12.8) gives

$$
 \frac{L(by)^2-c^2}{2b^2}\longrightarrow\frac{cq^2y^2}{2}.
$$

The other factors converge to $\phi(0)c^{-2}e^{c/2}$. Moreover,

$$
 \frac{L(u)^2-c^2}{2b^2}
 =\frac{(L(u)-c)(L(u)+c)}{2b^2}
 \ge\frac{c\kappa u^2}{b^2}.
$$

The prefactor $\phi(u)L(u)^{-2}e^{L(u)/2}$ is bounded on $[-\delta,\delta]$. Hence a fixed constant times $e^{-c\kappa y^2}$ dominates the scaled integrand. Dominated convergence now yields

$$
\begin{aligned}
 \frac{H_b}{b}
 &\longrightarrow\phi(0)c^{-2}e^{c/2}
      \int_{\mathbb R}e^{-cq^2y^2/2}\,dy\\
 &=\frac{e^{c/2}}{q\,c^{5/2}}.
\end{aligned}
\tag{12.9}
$$

This is the local Gaussian scaling underlying the mature Watson and Laplace methods in [NIST DLMF §2.3(ii)](https://dlmf.nist.gov/2.3#ii) and [§2.3(iii)](https://dlmf.nist.gov/2.3#iii); the domination above supplies the needed integral justification in this experiment. By positivity and the uniform relative error in (12.6), the local contribution to (12.3) equals $b^3E_bH_b(1+O(b^2))/(5\sqrt{2\pi})$. Combining (12.7) and (12.9) proves (12.2), including the prior factor $1/5$. The factors $b^3$ from the signed tail difference and $b$ from localization in $u$ give the power four. These classical asymptotic tools are mature intermediates; their explicit prefactor for the specified five-label law is repo-derived application exposition, with no global-priority assertion. $\square$

**定理 12.3（an explicit common binary readout attains the raw singleton gain）。** Under Definition 12.1, for every $b>0$ use the same Borel function for all five labels,

$$
 A_b=\left\{(u,v):v>\frac{L(u)+b^2/2}{b}\right\},\qquad
 Q_b(u,v)=\mathbf1_{A_b}(u,v).
\tag{12.10}
$$

Let $\mathcal J_b$ denote the joint law of the original label and this binary output, and let $B_{Q_b}=1/5-r_0(Q_b)$. Then

$$
 B_{Q_b}=B(q,b)>0.
\tag{12.11}
$$

For any comparison law $\mathcal J'_b$ on the same label-output alphabet with the same uniform label prior, put $B'_{Q_b}=1/5-r_0(\mathcal J'_b)$. Then

$$
 \operatorname{TV}(\mathcal J_b,\mathcal J'_b)\le e_b
 \quad\Longrightarrow\quad
 |B'_{Q_b}-B(q,b)|\le e_b.
\tag{12.12}
$$

Proof. Continuity of $L$ makes $A_b$ Borel. By (11.3), it is exactly the positive set of $D_b$. The set is nonempty and open, and $D_b$ is strictly positive on it, so (11.2) gives $B(q,b)>0$. Since $f_0,f_-,f_+$ are probability densities, $\int D_b=1-2-2=-3$. The two unweighted signed bin masses and their prior-weighted counterparts are therefore

$$
\begin{aligned}
 \int_{A_b}D_b&=5B(q,b),&
 \int_{A_b^c}D_b&=-3-5B(q,b),\\
 \mathcal J_b(3,1)-\sum_{i\ne3}\mathcal J_b(i,1)&=B(q,b),&
 \mathcal J_b(3,0)-\sum_{i\ne3}\mathcal J_b(i,0)&=-\frac35-B(q,b).
\end{aligned}
\tag{12.13}
$$

For each bin the Bayes action chooses singleton exactly when its signed joint mass is positive. Equivalently, relative to always choosing nonsingleton, the optimal improvement is the sum of the positive signed bin masses. Thus bin $1$ contributes $B(q,b)$ and bin $0$ contributes zero, proving (12.11) for the quantized Bayes optimum. This uses the classical Bayes decision partition already underlying Proposition 2.1, inside this explicit observation law. The boundary graph has zero Gaussian probability, so its inclusion convention changes neither mass. Apply Proposition 7.5 to the two finite laws: their singleton risks differ by at most TV, and subtracting each from the common prior $1/5$ proves (12.12). If $\mathcal J'_b$ is supplied by a complete-record approximation, it must use the very same readout (12.10); data processing and the hypotheses of Proposition 7.7, when supplied, give one way to furnish such an $e_b$.

The readout depends on the known $q,b$ and an exact curved threshold. Its two-symbol output proves this decision's information retention, without establishing preparation availability, finite physical precision or low acquisition or computation cost. It supplies no retention claim for an arbitrary quantizer and no claim about the other four singleton decisions or the categorical optimum. $\square$

**推论 12.4（same-exponential-scale error budgets with their leading constants）。** Fix $q$ as in Definition 12.1, and suppose the comparison laws of Theorem 12.3 are supplied for small $b>0$ with

$$
 \operatorname{TV}(\mathcal J_b,\mathcal J'_b)\le e_b,
 \qquad e_b=d\,b^\beta E_b,\qquad d>0,\quad\beta\in\mathbb R,
\tag{12.14}
$$

where $d,\beta$ are fixed independently of $b$. With $C=C(q)$ from (12.2),

$$
 \frac{e_b}{B(q,b)}=\frac dC b^{\beta-4}(1+o(1)),\qquad
 \left|\frac{B'_{Q_b}}{B(q,b)}-1\right|
 \le\frac{e_b}{B(q,b)}.
\tag{12.15}
$$

If $\beta>4$, this certificate tends to zero, so $B'_{Q_b}/B(q,b)\to1$. If $\beta=4$, the certificate tends to $d/C$, and

$$
 \limsup_{b\downarrow0}
 \left|\frac{B'_{Q_b}}{B(q,b)}-1\right|\le\frac dC,
 \qquad
 \liminf_{b\downarrow0}\frac{B'_{Q_b}}{B(q,b)}
 \ge\max\!\left\{0,1-\frac dC\right\}.
\tag{12.16}
$$

In particular, $d<C$ certifies a positive limiting lower fraction; every fixed $0<\theta<1-d/C$ is retained for all sufficiently small $b$. If $\beta<4$, the right-hand certificate in (12.15) diverges and gives neither a vanishing relative-error certificate nor a positive retained fraction. A nonvanishing or diverging upper budget does not prove any actual degradation, and $d\ge C$ at $\beta=4$ does not imply that the gain is lost.

Proof. Divide (12.14)'s budget by the positive asymptotic (12.2) to obtain the first equality in (12.15); its second inequality is (12.12) divided by $B(q,b)>0$. A constant nonsingleton decision remains available for every $\mathcal J'_b$ with this prior, so $B'_{Q_b}\ge0$. Thus the additive certificate gives

$$
 \frac{B'_{Q_b}}{B(q,b)}
 \ge\max\!\left\{0,1-\frac{e_b}{B(q,b)}\right\}.
\tag{12.17}
$$

For $\beta>4$, the budget ratio tends to zero; for $\beta=4$, it tends to $d/C$, proving (12.16) and the eventual bound for each strictly smaller $\theta$. For $\beta<4$, it tends to infinity, leaving (12.17) with only zero as a lower certificate. In all regimes the choice $\mathcal J'_b=\mathcal J_b$ satisfies the budget while its actual risk discrepancy is zero. Hence the size of an upper bound alone cannot establish approximation failure or an attained loss. The pointwise asymptotic supplies no numerical finite-$b$ cutoff for any of these eventual statements without a quantitative remainder estimate.

These are consequences for the explicit known-law readout and supplied comparison laws. They neither identify a projected-input law with a Gaussian law nor assert a native preparation realizing these means. There is no endpoint or $q$-uniform estimate, physical-cost model, unknown-law training guarantee, empirical gain or out-of-distribution conclusion. $\square$

## 追加锚（本行以下为增补区）
## 13. Critical crossover for the five-label Gaussian singleton experiment

**定义 13.1（全参数已知律与临界量）。** Let $C$ be uniform on the five original labels $\{1,2,3,4,5\}$. For every $q>0$ and $b>0$, and each label $i$, the full class-conditional law is $X\mid(C=i)\sim\mathcal N_2(\mu_i,I_2)$, where the complete observation $X=(U,V)\in\mathbb R^2$ has means

$$
 \mu_1=\mu_2=(-q,0),\qquad \mu_3=(0,b),\qquad
 \mu_4=\mu_5=(q,0).
\tag{13.1}
$$

A measurable binary rule decides whether $C=3$ and incurs zero--one loss. Let $r_0(q,b)$ be the infimum of its expected loss and put

$$
 B(q,b)=\frac15-r_0(q,b),\qquad
 c(q)=\ln4-\frac{q^2}{2},\qquad q_c=\sqrt{2\ln4},\qquad
 \phi(v)=\frac{e^{-v^2/2}}{\sqrt{2\pi}}.
\tag{13.2}
$$

The family in (13.1) is defined for all $q>0$ and $b>0$; no one-sided restriction relative to $q_c$, rate assumption, smoothness assumption, or finite-$b$ remainder is part of this definition.

**定理 13.2（临界交叉的全路径极限）。** Define, for $\tau\in\mathbb R$,

$$
 H(\tau)=\frac{4}{15q_c\sqrt\pi}
       \int_{\tau}^{\infty}(v-\tau)^{3/2}\phi(v)\,dv.
\tag{13.3}
$$

Then $H(\tau)$ is finite and strictly positive for every real $\tau$. For every $\tau\in\mathbb R$ and every pair of sequences $b_n>0$, $q_n>0$ satisfying

$$
 b_n\longrightarrow0,\qquad \frac{c(q_n)}{b_n}\longrightarrow\tau,
\tag{13.4}
$$

one has

$$
 \frac{B(q_n,b_n)}{b_n^{3/2}}\longrightarrow H(\tau).
\tag{13.5}
$$

Thus the same $H$ covers paths approaching $q_c$ from either side. No uniform-in-$\tau$ estimate, quantitative finite-$b$ remainder, or matching theorem with the neighboring regimes is asserted.

**Proof.** Write

$$
 f_0(u,v)=\phi(u)\phi(v-b),\qquad
 f_-(u,v)=\phi(u+q)\phi(v),\qquad
 f_+(u,v)=\phi(u-q)\phi(v).
$$

The singleton joint density is $f_0/5$ and the complement joint density is $(2f_-+2f_+)/5$. The signed-density Bayes identity used in Proposition 2.1 therefore gives, for every $q,b>0$,

$$
 \begin{aligned}
 B(q,b)
 &=\frac15\int_{\mathbb R^2}(f_0-2f_--2f_+)_+\,du\,dv\\
 &=\frac15\int_{\mathbb R^2}\phi(u)\phi(v)
 \left[e^{bv-b^2/2}-e^{c(q)}\cosh(qu)\right]_+\,du\,dv.
 \end{aligned}
\tag{13.6}
$$

The positive set is Borel because the bracket is continuous, so the measurable Bayes rule used by this identity is available without any sign restriction on $c(q)$.

Fix an arbitrary pair of sequences satisfying (13.4), and write

$$
 \tau_n=\frac{c(q_n)}{b_n}.
$$

Since $c(q_n)=b_n\tau_n\to0$ and $q_n>0$, we have $q_n\to q_c$. In (13.6) make the exact substitution $u=\sqrt{b_n}\,y/q_n$. Then

$$
 \frac{B(q_n,b_n)}{b_n^{3/2}}
 =\frac1{5q_n}\int_{\mathbb R^2}F_n(y,v)\,dy\,dv,
\tag{13.7}
$$

where

$$
 F_n(y,v)=\phi\!\left(\frac{\sqrt{b_n}\,y}{q_n}\right)\phi(v)
 \frac{\left[e^{b_nv-b_n^2/2}-e^{b_n\tau_n}\cosh(\sqrt{b_n}\,y)\right]_+}{b_n}.
\tag{13.8}
$$

For fixed $y,v$, Taylor expansion and $\tau_n\to\tau$ give

$$
 F_n(y,v)\longrightarrow
 \phi(0)\phi(v)\left(v-\tau-\frac{y^2}{2}\right)_+.
\tag{13.9}
$$

We next give a single integrable bound on the whole $(y,v)$-plane. Choose $M\ge1$ so that $|\tau_n|\le M$ for all sufficiently large $n$, and also take $b_n\le1$. At a point where the positive part in (13.8) is nonzero, set

$$
 t=v-\frac{b_n}{2}-\tau_n,\qquad s=(v+M)_+.
$$

Positivity implies $e^{b_nt}>\cosh(\sqrt{b_n}y)\ge1$, hence $0<t\le s$. Using $\cosh z\ge1+z^2/2$ and $e^x-1\le xe^x$ for $x\ge0$ gives

$$
 \frac{y^2}{2}<\frac{e^{b_nt}-1}{b_n}\le t e^{b_nt}\le s e^s,
\tag{13.10}
$$

and

$$
 \frac{\left[e^{b_nv-b_n^2/2}-e^{b_n\tau_n}\cosh(\sqrt{b_n}y)\right]_+}{b_n}
 \le e^{M}\,s e^s.
\tag{13.11}
$$

Since $\phi(x)\le\phi(0)$, (13.10)--(13.11) imply $0\le F_n\le D$, where

$$
 D(y,v)=\phi(0)\phi(v)e^M s e^s
 \mathbf 1_{\{|y|\le\sqrt{2s}\,e^{s/2}\}},\qquad s=(v+M)_+.
\tag{13.12}
$$

Integrating first in $y$ shows

$$
 \int_{\mathbb R^2}D(y,v)\,dy\,dv
 =2\sqrt2\,\phi(0)e^M
   \int_{\mathbb R}\phi(v)s^{3/2}e^{3s/2}\,dv<\infty.
\tag{13.13}
$$

Indeed, the integrand vanishes for $v<-M$, and for $v\ge-M$ its exponential factor is bounded by a constant times $\exp(-v^2/2+3v/2)$, a Gaussian-integrable function. This is also explicit tail control for arbitrary expanding rectangles; no far-$u$ or far-$v$ contribution is discarded.

Dominated convergence in (13.7), together with $q_n\to q_c$, now yields

$$
 \lim_{n\to\infty}\frac{B(q_n,b_n)}{b_n^{3/2}}
 =\frac{\phi(0)}{5q_c}
   \int_{\mathbb R}\phi(v)
   \left[\int_{\mathbb R}\left(v-\tau-\frac{y^2}{2}\right)_+dy\right]dv.
\tag{13.14}
$$

For $a=v-\tau>0$,

$$
 \int_{\mathbb R}\left(a-\frac{y^2}{2}\right)_+dy
 =\int_{-\sqrt{2a}}^{\sqrt{2a}}\left(a-\frac{y^2}{2}\right)dy
 =\frac{4\sqrt2}{3}a^{3/2},
\tag{13.15}
$$

and the integral is zero for $a\le0$. Since $\phi(0)=1/\sqrt{2\pi}$, (13.14)--(13.15) are exactly (13.3)--(13.5). Gaussian moment integrability proves finiteness of (13.3), while the integrand is positive on $\tau+1<v<\tau+2$, proving strict positivity. The argument began with an arbitrary admissible sequence, so it establishes the full sequential assertion. $\square$

Dominated convergence and Gaussian moments are mature intermediate tools here. The particular coefficient and all-path statement for (13.1) are this repository's application derivation; they are not presented as a global originality or priority claim.

**定理 13.3（全参数的共同 Borel 二元读出）。** For every $q,b>0$, define

$$
 A_{q,b}=\left\{(u,v):v>
 \frac{c(q)+\ln\cosh(qu)+b^2/2}{b}\right\},\qquad
 Q_{q,b}(u,v)=\mathbf 1_{A_{q,b}}(u,v).
\tag{13.16}
$$

This is a Borel readout applied identically for all five labels, and its singleton Bayes gain satisfies

$$
 B_{Q_{q,b}}=B(q,b)>0.
\tag{13.17}
$$

If $\mathcal J_{q,b}'$ is any supplied comparison law on the same label--output alphabet, with the same uniform original-label prior, and $B_{Q_{q,b}}'$ denotes its singleton gain, then

$$
 \operatorname{TV}(\mathcal J_{q,b},\mathcal J_{q,b}')\le e_{q,b}
 \quad\Longrightarrow\quad
 \left|B_{Q_{q,b}}'-B(q,b)\right|\le e_{q,b}.
\tag{13.18}
$$

**Proof.** The threshold in (13.16) is continuous, hence $A_{q,b}$ is Borel, and (13.6) shows it is exactly the positive set of the signed density. It is nonempty and open, so (13.17)'s strict positivity follows from the positive Gaussian density on a nonempty open subset. Since the three component densities integrate to one,

$$
 \int_{\mathbb R^2}(f_0-2f_--2f_+)\,du\,dv=-3.
$$

Consequently the two unweighted signed bin masses and their prior-weighted versions are

$$
 \begin{aligned}
 \int_{A_{q,b}}(f_0-2f_--2f_+)&=5B(q,b),
 &\int_{A_{q,b}^c}(f_0-2f_--2f_+)&=-3-5B(q,b),\\
 \mathcal J_{q,b}(3,1)-\sum_{i\ne3}\mathcal J_{q,b}(i,1)&=B(q,b),
 &\mathcal J_{q,b}(3,0)-\sum_{i\ne3}\mathcal J_{q,b}(i,0)&=-\frac35-B(q,b).
 \end{aligned}
\tag{13.19}
$$

The binary Bayes action chooses the singleton exactly on bins with positive signed joint mass. Thus bin $1$ contributes $B(q,b)$ and bin $0$ contributes zero, proving (13.17) by the existing decision-partition argument. Proposition 7.5, applied to the two finite joint laws on $\{1,\ldots,5\}\times\{0,1\}$, gives (13.18). The boundary graph has zero Gaussian probability, so its inclusion convention does not alter either bin mass. This readout is parameter-dependent and exact; it supplies no retention statement for an arbitrary quantizer.

**推论 13.4（临界尺度的条件 TV 保留证书）。** Let $(q_n,b_n)$ satisfy (13.4), and apply the same parameter-dependent readout $Q_{q_n,b_n}$ to a supplied comparison law with the same original-label prior and binary output alphabet. Write its singleton gain as $B_n'$, and suppose the resulting joint laws obey

$$
 \operatorname{TV}(\mathcal J_{q_n,b_n},\mathcal J_{q_n,b_n}')\le e_n.
\tag{13.20}
$$

If $e_n=o(b_n^{3/2})$, then

$$
 \frac{B_n'}{B(q_n,b_n)}\longrightarrow1.
\tag{13.21}
$$

More generally, if $e_n\le d\,b_n^{3/2}$ eventually for a fixed $d\ge0$, then

$$
 \limsup_{n\to\infty}
 \left|\frac{B_n'}{B(q_n,b_n)}-1\right|\le\frac d{H(\tau)},\qquad
 \liminf_{n\to\infty}\frac{B_n'}{B(q_n,b_n)}
 \ge\max\left\{0,1-\frac d{H(\tau)}\right\}.
\tag{13.22}
$$

In particular, $d<H(\tau)$ gives a positive eventual retained fraction, and every fixed $0<\theta<1-d/H(\tau)$ is eventually certified. These are sufficient certificates for the respective Bayes optima under the supplied TV bound; they are neither necessary conditions nor an achieved approximation rate. They do not assert a comparison-law construction, training guarantee, or actual loss when an upper budget is loose.

**Proof.** Equation (13.18) gives $|B_n'-B(q_n,b_n)|\le e_n$. Divide by the positive quantity $B(q_n,b_n)$ and use (13.5), with $H(\tau)>0$. The little-$o$ case gives (13.21); the eventual bound gives the first inequality in (13.22). A constant nonsingleton action is always available under the common prior, so $B_n'\ge0$, which gives the second inequality. The stated fraction follows when $d<H(\tau)$. $\square$

The source correspondences are Proposition 2.1 and (11.2)--(11.3) for the signed Bayes identity, Theorem 10.2 for the on-axis onset context, Theorem 12.2 for the fixed-$q$ off-axis context, and Proposition 7.5 for the same-prior finite-law TV bound. The proof of Theorem 13.2 is direct and does not substitute a varying $q_n$ into the fixed-$q$ theorem. No native recursive-FIB realization, physical-cost claim, unknown-law learning, empirical benefit, formal certification, comparison-law approximation rate, or global originality claim follows.

## 追加锚（本行以下为增补区）

## 14. Relative crossover along unrestricted normalized offsets

**假设 14.1（全标签高斯族与相对尺度）。** Use the known-law binary singleton experiment of Definition 13.1: $C$ is uniform on the five original labels, and one complete observation $X=(U,V)$ conditional on $C=i$ has law $\mathcal N_2(\mu_i,I_2)$, with means $(-q,0),(-q,0),(0,b),(q,0),(q,0)$ in label order, for $q,b>0$. The target is $C=3$ versus its complement under measurable binary zero--one decision rules. Retain $r_0(q,b)$, $B(q,b)=1/5-r_0(q,b)$, $c(q)=\ln4-q^2/2$, $q_c=\sqrt{2\ln4}$, the standard normal density $\phi$, and $H$ from (13.2)--(13.3). For positive sequences $q_n\to q_c$ and $b_n\to0$, put

$$
 \tau_n=\frac{c(q_n)}{b_n},\qquad
 S_n=b_n^{3/2}H(\tau_n)>0.
\tag{14.1}
$$

No boundedness, convergence, monotonicity or additional rate restriction is imposed on $\tau_n$.

**定理 14.2（不受限归一化偏移的相对极限）。** Under Assumption 14.1, for every such pair of positive sequences,

$$
 \frac{B(q_n,b_n)}{S_n}\longrightarrow1.
\tag{14.2}
$$

**Proof.** Suppress sequence indices when proving estimates along a path. Write $c=b\tau$ and define, for all real $d$,

$$
 J_q(d)=\int_{\mathbb R}\phi(u)[e^d-\cosh(qu)]_+\,du,
 \qquad d_b(v)=b(v-\tau)-\frac{b^2}{2}.
\tag{14.3}
$$

For $d\le0$, $e^d\le1\le\cosh(qu)$, so $J_q(d)=0$. Factoring $e^c$ in the exact all-parameter signed Bayes identity (13.6) gives

$$
 B(q,b)=\frac{e^c}{5}\int_{\mathbb R}\phi(v)J_q(d_b(v))\,dv.
\tag{14.4}
$$

Restrict $q$ to a fixed compact neighborhood of $q_c$ contained in $(0,\infty)$, as is legitimate eventually along every path in Assumption 14.1. Uniformly for these $q$, put

$$
 A_q=\frac{4\sqrt2\,\phi(0)}{3q}.
$$

There are $\delta_0>0$ and $C<\infty$ such that

$$
 \left|J_q(d)-A_qd^{3/2}\right|\le C d^{5/2}
 \qquad(0<d\le\delta_0).
\tag{14.5}
$$

Indeed, with $w=qu$, the positive interval has endpoint
$a(d)=\operatorname{arcosh}(e^d)=\sqrt{2d}(1+O(d))$. On $|w|\le a(d)$,

$$
 e^d-\cosh w=d-\frac{w^2}{2}+O(d^2),\qquad
 \phi(w/q)=\phi(0)(1+O(d)),
$$

with uniform remainders. Integrating the leading parabola gives

$$
 \frac{\phi(0)}q
 \int_{-\sqrt{2d}}^{\sqrt{2d}}\left(d-\frac{w^2}{2}\right)dw
 =A_qd^{3/2}.
$$

The integrated Taylor errors are $O(d^{5/2})$; replacing $a(d)$ by $\sqrt{2d}$ contributes an error of that order or smaller. Also $A_q$ is bounded above and below by positive constants. In particular, $J_q(d)\le C d^{3/2}$ for sufficiently small positive $d$. For all $d\ge0$, the elementary bounds

$$
 0\le J_q(d)\le e^d,\qquad d^{3/2}\le M e^d,
 \qquad M=\sup_{d\ge0}d^{3/2}e^{-d}<\infty
\tag{14.6}
$$

will control the nonlocal part.

Define the positive quantities

$$
 I(\tau)=\int_\tau^\infty(v-\tau)^{3/2}\phi(v)\,dv,
 \qquad
 K_b(\tau)=\int_{\mathbb R}\phi(v)[d_b(v)]_+^{3/2}\,dv.
\tag{14.7}
$$

We first prove

$$
 K_b(\tau)=b^{3/2}I(\tau)(1+o(1))
\tag{14.8}
$$

along either $\tau\to+\infty$ or $\tau\to-\infty$, with $b\to0$ and $|b\tau|=|c|\to0$.

For $\tau\to+\infty$, set $x=v-\tau$ and $z=\tau x$. Then exactly

$$
 \begin{aligned}
 I(\tau)
 &=\phi(\tau)\tau^{-5/2}
   \int_0^\infty z^{3/2}e^{-z}e^{-z^2/(2\tau^2)}\,dz,\\
 b^{-3/2}K_b(\tau)
 &=\phi(\tau)\tau^{-5/2}
   \int_0^\infty(z-b\tau/2)_+^{3/2}e^{-z}e^{-z^2/(2\tau^2)}\,dz.
 \end{aligned}
\tag{14.9}
$$

Since $b\tau\to0$, both last integrals converge to the same strictly positive finite integral $\int_0^\infty z^{3/2}e^{-z}\,dz$, by domination with $z^{3/2}e^{-z}$. This proves the relative comparison (14.8). It also controls the positive tail after rescaling: the part $x>R/\tau$ is uniformly small in the normalized integrals as $R\to\infty$.

For $\tau=-L\to-\infty$, with $V\sim\mathcal N(0,1)$,

$$
 b^{-3/2}K_b(-L)=\mathbb E[(V+L-b/2)_+^{3/2}],
 \qquad I(-L)=\mathbb E[(V+L)_+^{3/2}].
\tag{14.10}
$$

After division by $L^{3/2}$, both integrands converge pointwise to $1$, since $b/L\to0$. For $L\ge1$ and $b\le1$ they are bounded by a fixed constant times $(1+|V|)^{3/2}$, which is integrable. Gaussian moment domination, controlling both tails of $V$, therefore gives

$$
 I(-L)\sim L^{3/2},\qquad K_b(-L)\sim(bL)^{3/2},
\tag{14.11}
$$

and proves (14.8) on this side as well.

We next justify replacing $J_q$ by (14.5) with an error relative to $K_b(\tau)$. For fixed $\delta>0$, define

$$
 T_\delta=\int_{\{d_b(v)>\delta\}}\phi(v)e^{d_b(v)}\,dv.
$$

Let $\overline\Phi(s)=\int_s^\infty\phi(v)\,dv$. Completing the Gaussian square gives the exact formula

$$
 T_\delta=e^{-b\tau}\overline\Phi\!\left(\tau+\frac\delta b-\frac b2\right).
\tag{14.12}
$$

By (14.6), this envelope bounds the nonlocal $J_q$ contribution and, up to the constant $M$, the nonlocal $d_b^{3/2}$ contribution. It suffices to show $T_\delta=o(K_b(\tau))$.

If $\tau\to+\infty$, (14.9) yields, eventually for a fixed $c_0>0$,

$$
 K_b(\tau)\ge c_0 b^{3/2}\phi(\tau)\tau^{-5/2}.
\tag{14.13}
$$

Put $h=\delta/b-b/2$. Eventually $h\ge\delta/(2b)$ and $\tau\ge1$. The Gaussian bound $\overline\Phi(s)\le\phi(s)/s$ for $s>0$, the identity
$\phi(\tau+h)/\phi(\tau)=\exp(-\tau h-h^2/2)$, and $e^{-b\tau}\le1$ give

$$
 T_\delta\le C\phi(\tau)
       \exp\!\left(-\frac{\delta^2}{8b^2}\right).
$$

Moreover $b\tau\to0$ implies $\tau\le1/b$ eventually. Hence

$$
 \frac{T_\delta}{K_b(\tau)}
 \le C b^{-3/2}\tau^{5/2}
       \exp\!\left(-\frac{\delta^2}{8b^2}\right)
 \le C b^{-4}\exp\!\left(-\frac{\delta^2}{8b^2}\right)
 \longrightarrow0.
\tag{14.14}
$$

The exponentially small factor $\phi(\tau)$ cancels before the remainder is estimated; the rare-tail denominator is explicitly controlled.

If $\tau=-L\to-\infty$, $bL\to0$ implies eventually

$$
 \frac\delta b-L-\frac b2\ge\frac\delta{2b},\qquad e^{bL}\le2.
$$

Equations (14.11)--(14.12) and the same Gaussian bound imply

$$
 T_\delta\le C\exp\!\left(-\frac{\delta^2}{8b^2}\right),\qquad
 \frac{T_\delta}{K_b(-L)}
 \le C b^{-3/2}\exp\!\left(-\frac{\delta^2}{8b^2}\right)
 \longrightarrow0,
\tag{14.15}
$$

where $L\ge1$ was used in the second inequality.

For fixed $0<\delta\le\delta_0$, apply (14.5) on $0<d_b(v)\le\delta$. Its integrated error is at most $C\delta K_b(\tau)$. On $d_b(v)>\delta$, (14.14) or (14.15) bounds both contributions by $o(K_b(\tau))$. The portion $d_b(v)\le0$ is zero. Dividing by $A_qK_b(\tau)$, taking the limit superior, and then sending $\delta\downarrow0$ proves

$$
 \int_{\mathbb R}\phi(v)J_q(d_b(v))\,dv
 =A_qK_b(\tau)(1+o(1))
\tag{14.16}
$$

with a relative error in both unbounded-offset regimes. Combining (14.4), (14.8) and (14.16), and using $e^c\to1$, $q\to q_c$ and $\phi(0)=1/\sqrt{2\pi}$, gives

$$
 \begin{aligned}
 \frac{B(q,b)}{b^{3/2}}
 &=\frac{e^c}{5}\frac{4\sqrt2\phi(0)}{3q}I(\tau)(1+o(1))\\
 &=\frac4{15q_c\sqrt\pi}I(\tau)(1+o(1))
 =H(\tau)(1+o(1)).
 \end{aligned}
\tag{14.17}
$$

The displacement $b^2/2$ is retained throughout: it produces the shift $b/2$ in (14.9)--(14.12). On the positive side its rescaled size is $b\tau/2=c/2\to0$; on the negative side its relative size is $b/(2L)\to0$. The coefficient includes the original singleton prior $1/5$, with both duplicate complement means counted twice in (13.6). The proof integrates the positive signed excess, so it preserves the cancellation in the Bayes identity.

It remains to cover bounded and oscillatory offsets. Gaussian moment domination makes $H$ continuous on every compact interval; its strict positivity gives a positive minimum there. If $\tau_n\to\tau_0\in\mathbb R$, Theorem 13.2 and its global bound (13.12) give $B(q_n,b_n)/b_n^{3/2}\to H(\tau_0)$, while $H(\tau_n)\to H(\tau_0)>0$. Thus (14.2) holds on each such subsequence. A compactness contradiction consequently gives the relative assertion on any bounded offset sequence. Every subsequence of an arbitrary real sequence $\tau_n$ has a further subsequence tending to a finite real number, $+\infty$, or $-\infty$. The preceding arguments give ratio limit $1$ in every case, proving (14.2) for the entire sequence, including paths oscillating between the regimes.

The reused inputs are the full model of Definition 13.1, the exact all-parameter identity (13.6), and Theorem 13.2 only for finite normalized offsets. The fixed-$q$ asymptotic of Section 12 is not used as a varying-$q$ theorem. The local $d^{3/2}$ kernel and the relative Gaussian-tail estimates supply the unrestricted-offset step. Taylor expansion, Gaussian moment domination and Laplace-type tail comparison are classical mechanisms; related standard methods are described in [DLMF §2.3](https://dlmf.nist.gov/2.3), [§2.4](https://dlmf.nist.gov/2.4) and [§7.12](https://dlmf.nist.gov/7.12). Equation (14.2) is a repo-derived application for the specified family, with no global priority assertion. It is a qualitative sequential limit: it supplies neither a numerical finite-$b$ cutoff nor a uniform quantitative remainder rate. $\square$

**推论 14.3（相对尺度下的条件联合 TV 保留）。** Under Assumption 14.1, use the actual parameter-dependent Borel sign readout $Q_{q_n,b_n}$ of (13.16), applied identically for all five original labels. Let $\mathcal J_n$ be its label--output joint law for the stated Gaussian experiment. Supply comparison joint laws $\mathcal J_n'$ on the same $\{1,\ldots,5\}\times\{0,1\}$ alphabet with the same uniform original-label prior, obtained using the same actual readout, and write their optimal binary singleton gains as $B_n'$. Suppose

$$
 \operatorname{TV}(\mathcal J_n,\mathcal J_n')\le e_n.
\tag{14.18}
$$

If $e_n=o(S_n)$, then $B_n'/B(q_n,b_n)\to1$. More generally, if $e_n\le dS_n$ eventually for a fixed $0\le d<1$, then

$$
 \limsup_{n\to\infty}
 \left|\frac{B_n'}{B(q_n,b_n)}-1\right|\le d,
 \qquad
 \liminf_{n\to\infty}\frac{B_n'}{B(q_n,b_n)}\ge1-d.
\tag{14.19}
$$

Every fixed fraction $0<\theta<1-d$ is therefore eventually retained. The limiting lower bound does not assert an eventual pointwise bound of exactly $1-d$.

**Proof.** Reuse (13.17)--(13.18): $B_{Q_{q_n,b_n}}=B(q_n,b_n)>0$ and $|B_n'-B(q_n,b_n)|\le e_n$. Divide by $B(q_n,b_n)$ and apply (14.2). The first error budget gives a vanishing relative discrepancy; the second gives the limsup bound in (14.19), which implies its liminf bound and every strictly smaller eventual fraction. This is the existing same-prior joint-TV algebra applied to the scale $S_n$ for unrestricted offsets. The comparison laws and their error bounds are supplied hypotheses; no approximation-law construction or achieved rate is established. In particular the conclusion concerns the common actual sign readout, not an arbitrary quantizer, and entails no native-FIB realization, training, empirical, physical-cost or formal-certification claim. $\square$

## 追加锚（本行以下为增补区）

## 15. Exact rational factor representations of the positive-noise decision law

**定义 15.1（有限有理五模式因子语言）。** In the coordinate order of [the foundational volume, Definition 2.1](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md), put

$$
 A=\{(x,y,z)\in\{0,1\}^3:xz=yz=0\}
   =\{000,100,010,110,001\}.
\tag{15.1}
$$

For each integer $n\ge1$, a network consists of labelled visible Boolean variables $v_1,\ldots,v_n$, any finite number $m\ge0$ of hidden Boolean variables, and finitely many factors $f_j:\{0,1\}^3\to\mathbb Q_{\ge0}$. Every factor sums to one over its complete three-bit table and vanishes outside $A$. Its scope is an ordered triple of actual visible or hidden variables; repetition and identification are permitted. If $a$ and $h$ are the visible and hidden assignments, its law is

$$
 P(a)=Z^{-1}\sum_{h\in\{0,1\}^m}\prod_j f_j((a,h)|_{\mathrm{scope}(j)}),
 \qquad
 Z=\sum_{a,h}\prod_j f_j((a,h)|_{\mathrm{scope}(j)})>0.
\tag{15.2}
$$

An empty product is one. In regime $W_+$ every factor is strictly positive on all five tuples of $A$; in regime $W_0$ additional zeros within $A$ are permitted. The only operations are the ordered scopes, factor multiplication, finite hidden summation and final normalization in (15.2). Constants, complemented literals, extra equality or disequality primitives, externally supplied unary or multivariate factors, and limits are absent. Network size may depend on the entire target law and is unbounded finite. Locally normalized tables are potentials in a globally normalized product; they have no supplied conditional-kernel or causal sampling interpretation.

For a labelled undirected graph $K$ with loops, write

$$
 \operatorname{Ind}(K)=\{a\in\{0,1\}^n:
 a_i a_j=0\text{ for every edge }\{i,j\}\text{ of }K\}.
\tag{15.3}
$$

A loop at $i$ thus forces $a_i=0$. Vertices here are Boolean coordinates, not the five labels that are vertices of the legal-toggle graph $G$ in (1.2).

**定理 15.2（严格正局部表的支撑与全部有理权重）。** For every $n\ge1$, a rational probability law on $\{0,1\}^n$ is representable in $W_+$ if and only if its support is $\operatorname{Ind}(K)$ for some labelled undirected graph $K$ with loops allowed. Every choice of positive rational masses on that support is included.

**Proof.** First record how the constructions use only the permitted tables. An unnormalized rational table $F$ with support contained in $A$ and positive table sum $N_F$ denotes the actual factor $F/N_F$. Normalizing all such tables multiplies the full assignment weight by the positive rational constant $\prod_F N_F^{-1}$, independent of the assignments; this constant cancels in (15.2).

Let $H=\mathbf1_A$, of table sum five. A fresh hidden variable $o$ with $H/5$ on scope $(o,o,o)$ is forced to zero, since $000\in A$ and $111\notin A$. This generates a zero internally. Scope $(u,u,w)$ for $H/5$ enforces $uw=0$ and has constant value $1/5$ on allowed pairs. Taking $u=w$ implements a loop.

For any positive rational binary table $B$, use the full ternary table

$$
 F_B(x,y,0)=B(x,y),\qquad F_B(0,0,1)=1,
 \qquad F_B=0\text{ outside }A.
\tag{15.4}
$$

Its five entries on $A$ are positive, and its table sum is positive rational. On scope $(u,w,o)$ it gives $B(u,w)$ before the constant normalization. Thus binary weights below are abbreviations for legal ternary factors. Likewise define

$$
 U_t(000)=U_t(100)=U_t(010)=U_t(001)=1,
 \qquad U_t(110)=t,
 \qquad U_t=0\text{ outside }A.
\tag{15.5}
$$

Its sum is $4+t$. Scope $(u,u,o)$ gives weight $1$ at $u=0$ and $t$ at $u=1$, before normalization. It is legal in $W_+$ for rational $t>0$, and in $W_0$ for rational $t\ge0$. These definitions specify even the table entries a repeated scope never visits.

For necessity, a factor on $(u,w,t)$ contributes edges $\{u,t\}$ and $\{w,t\}$ to a graph on all variables, retaining loops from repetitions. A complete assignment has positive weight exactly when its occupied variables form an independent set: these are precisely the two exclusions defining $A$. Let $K$ be the visible induced graph. A visible assignment violating an edge or loop of $K$ has no positive extension. Conversely, any assignment in $\operatorname{Ind}(K)$ extends positively by setting every hidden variable to zero. All edges with a hidden endpoint, including hidden loops, are then satisfied. A finite nonnegative hidden sum is positive exactly when some summand is positive, proving the support assertion. The complete all-zero assignment also proves $Z>0$. All masses are rational. This includes an empty factor set and duplicated scopes.

For sufficiency, first realize an arbitrary positive rational table $w$ on the full visible cube, up to a constant multiplier. We need the following finite identity, with $d$ the Hamming distance:

$$
 Lw(a)=1+\sum_{s\in\{0,1\}^n}c_s\varepsilon^{d(a,s)},
 \qquad L,c_s\in\mathbb Q_{>0},\quad
 \varepsilon\in\mathbb Q,\quad 0<\varepsilon<1.
\tag{15.6}
$$

Here is an explicit proof. Set $L=2/\min_a w(a)$, $r(a)=Lw(a)-1$, $\alpha=\min_a r(a)>0$, $\beta=\max_a r(a)$ and $\varepsilon=\alpha/(4n\beta)$. Then $0<\varepsilon\le1/(4n)$. The matrix $M_{a,s}=\varepsilon^{d(a,s)}$ is the $n$-fold tensor product of $\left(\begin{smallmatrix}1&\varepsilon\\\varepsilon&1\end{smallmatrix}\right)$, so its rational inverse is

$$
 (M^{-1})_{a,s}=\frac{(-\varepsilon)^{d(a,s)}}{(1-\varepsilon^2)^n}.
\tag{15.7}
$$

This follows by multiplying the two-by-two inverses coordinate by coordinate. Its absolute row sum is $(1-\varepsilon)^{-n}$ and its diagonal entry is $(1-\varepsilon^2)^{-n}\ge1$. Hence, for the maximum absolute row-sum norm,

$$
 \|M^{-1}-I\|_\infty=(1-\varepsilon)^{-n}-1
 \le\frac{n\varepsilon}{1-n\varepsilon}.
\tag{15.8}
$$

The inequality uses $(1-\varepsilon)^n\ge1-n\varepsilon>0$, the Bernoulli inequality obtained by induction. Put $c=M^{-1}r$. Since $n\varepsilon=\alpha/(4\beta)\le1/4$,

$$
 \|c-r\|_\infty
 \le\frac{n\varepsilon}{1-n\varepsilon}\beta
 \le\alpha/3,
 \qquad c_s\ge2\alpha/3>0.
\tag{15.9}
$$

Thus $c$ is rational and positive, and $Mc=r$ gives (15.6) exactly. No limiting operation is used.

Take the internally pinned $o=0$ and one fresh hidden selector $h_s$ for each word $s$. For every distinct selector pair impose the NAND constraint $H/5$ on $(h_s,h_s,h_t)$, taking each unordered pair once. Allowed selector assignments are precisely the all-zero assignment and assignments with one selector equal to one. Give selector $h_s$ the unary weight $c_s$ through (15.5) on $(h_s,h_s,o)$. For each coordinate $i$ use the positive binary table

$$
 B_{s,i}(h,a_i)=
 \begin{cases}
 1,&h=0,\\
 1,&h=1\text{ and }a_i=s_i,\\
 \varepsilon,&h=1\text{ and }a_i\ne s_i,
 \end{cases}
\tag{15.10}
$$

implemented by (15.4) on $(h_s,v_i,o)$. Selecting entries of a table using the fixed index $s_i$ does not complement a scope variable. Apart from the common positive scalar from the pin, NAND factors and local normalizations, the all-zero selector contributes $1$, and the assignment with only $h_s=1$ contributes $c_s\varepsilon^{d(a,s)}$. The hidden sum is therefore a positive rational constant times $Lw(a)$. All factors are positive on every tuple of $A$, and there are finitely many variables and factors.

Finally let $P$ have support $S=\operatorname{Ind}(K)$, and extend it to a positive rational full-cube table by $w(a)=P(a)$ on $S$ and $w(a)=1$ outside $S$. Construct the preceding network. Append $H/5$ on $(v_i,v_i,v_j)$ for every ordinary edge $\{i,j\}$, and on $(v_i,v_i,v_i)$ for every loop. Their product is a positive constant times $\mathbf1_S$. The visible marginal becomes $CLw(a)\mathbf1_S(a)=CLP(a)$ for a fixed positive rational $C$, with total mass $CL>0$. Global normalization gives $P$. This also covers $n=1$ and the singleton support consisting only of the all-zero word. $\square$

**定理 15.3（允许内部零点时的有限精确表示）。** For every $n\ge1$, every rational probability law on $\{0,1\}^n$, including laws with arbitrary zero entries, is representable in $W_0$ with the same operations as Definition 15.1.

**Proof.** Reuse the null-deleted Boolean relation from [the Boolean null-boundary source](../../../D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.lean):

$$
 \mathbf1_{A\setminus\{000\}}(x,y,z)>0
 \quad\Longleftrightarrow\quad z=\neg(x\lor y).
\tag{15.11}
$$

Indeed its four tuples are $100,010,110,001$, precisely the truth table of NOR. Dividing this indicator by four gives a legal rational $W_0$ factor. The support identity is reused; the weight construction below supplies the probability masses and normalizations.

For every word $s$, compute the indicator $e_s(a)=\mathbf1_{\{a=s\}}$ by an acyclic NOR circuit. Explicitly,

$$
 \operatorname{NOT}(x)=\operatorname{NOR}(x,x),\qquad
 \operatorname{AND}(x,y)=
 \operatorname{NOR}(\operatorname{NOR}(x,x),\operatorname{NOR}(y,y)).
\tag{15.12}
$$

Use literal $a_i$ for $s_i=1$ and the computed NOT of $a_i$ for $s_i=0$; join the $n\ge1$ literals by successive AND gates. Each gate has a fresh hidden output and uses (15.11) on its two actual input wires and output wire. Repeated inputs implement NOT; fanout is reuse of an actual variable. Thus no complemented literal or equality primitive is supplied. For $n=1$ the final indicator may already be a visible wire. For every visible assignment there is exactly one assignment of all gate-output variables satisfying all NOR factors, by evaluation in acyclic order.

Introduce the internally pinned $o=0$ from the proof of Theorem 15.2. For each $s$ append the normalized table $U_{P(s)}/(4+P(s))$ of (15.5) on $(e_s,e_s,o)$. On the unique gate-consistent hidden assignment the product, before the common local-normalization scalar, is

$$
 \prod_s\begin{cases}
 1,&e_s(a)=0,\\
 P(s),&e_s(a)=1
 \end{cases}=P(a),
\tag{15.13}
$$

because exactly one indicator is one. This includes $P(a)=0$, when the corresponding factor vanishes. Every other hidden assignment violates the pin or some NOR factor and contributes zero. All local sums are positive rational, including $4+P(s)$ when $P(s)=0$. Hence the visible marginal is $CP(a)$ with fixed rational $C>0$, its total is $C$, and normalization proves the claim. $\square$

**推论 15.4（正噪声平台律的同一联合分布表示）。** For each rational $0<\eta\le1$, the law $J_{H,\eta}$ of Proposition 7.4 and (7.8) has an exact finite rational $W_+$ representation, and also a $W_0$ representation, on five visible Boolean coordinates. These representations preserve its joint distribution and consequently its already established posteriors and decision risks.

**Proof.** The printed words in Definition 1.1 are ordered low--middle--high. Swapping the final two positions gives the foundational low--high--middle coordinates $(x,y,z)$, while a two-bit record encodes the four outputs:

$$
 \begin{aligned}
 (a,b,c,d,e)&\longmapsto(000,100,001,110,010),\\
 (ac,bd,de,be)&\longmapsto(00,01,10,11).
 \end{aligned}
\tag{15.14}
$$

These are bijections onto $A$ and $\{0,1\}^2$. In (6.3) each posterior is uniform on its displayed pair, and the output masses are $(2/5,1/5,1/5,1/5)$. Thus

$$
 J_{H,\eta}(i,q)=(1-\eta)J_H(i,q)+\eta\lambda_q/5>0
\tag{15.15}
$$

at all twenty label--record pairs, with rational entries. Transport the law by (15.14) to $(x,y,z,r_1,r_2)$ and set its mass to zero at every remaining five-bit word. Its support is exactly

$$
 A\times\{0,1\}^2=\operatorname{Ind}(K_*),\qquad
 E(K_*)=\{\{x,z\},\{y,z\}\},
\tag{15.16}
$$

where the two record vertices are isolated. Positivity is relative to these twenty points, not all thirty-two ambient words. Theorem 15.2 supplies the same normalized joint law in $W_+$, and Theorem 15.3 supplies it in $W_0$. The coordinate exclusion graph $K_*$ has coordinate vertices; it is not the five-label legal-toggle graph $G$. In particular the two-bit name of output $be$ neither adds a coordinate exclusion nor makes $be$ a legal edge of $G$.

The finite splitting construction of Definition 1.1, common-source coupling (4.7), and the Bayes and plateau calculations in Proposition 7.4 are reused. Exact equality of the joint laws preserves those conclusions without a new risk or approximation argument. Each rational $\eta$ may use its own finite network. Irrational $\eta$ and a single finite network for the parameter continuum are outside the rational assertion.

The construction is an abstract weighted-factor representation. It supplies no native recursive-FIB preparation, acquisition or learnability result, training mechanism, efficient inference or sampling, parameter compression, physical-cost bound, or achieved approximation. Local normalization does not turn the factors into directed conditional distributions.

The unweighted support operations are those of [the existing primitive-positive preservation framework](../../../D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.lean); the null-deleted NOR relation is the supplier in (15.11). Neither support result alone specifies arbitrary rational masses. The finite common-source sum-product eliminations of [the hidden-relations volume, C-59.2--C-59.5](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md) and [its continuation, C-60.1--C-60.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md) likewise distinguish support from chosen product activities; a restricted positive-activity family does not supply the unrestricted weight statement of Theorem 15.2.

As a primary exact-representation comparison, Gleb Smirnov, *Deep belief networks are exact*, [arXiv:2609.05572v1, Theorem 1.1 and Section 1](https://arxiv.org/html/2609.05572v1), represents strictly positive Boolean laws by finite sigmoid belief networks with real parameters. That directed conditional interface, its real weights and biases, and its strictly positive visible laws differ from (15.2), rational local tables and the structural zeros in (15.16); it supplies no step of these proofs. Likewise an exact finite pps construction must be distinguished from an omega closure or a language granted extra equality and unary factors: none of those extra operations is implicit in Definition 15.1. Theorems 15.2--15.3 and this correspondence are elementary repository-derived constructions, without a claim of global priority or exhaustive literature absence. Their proofs are ordinary mathematics and make no formal proof-shape or kernel-verification assertion. $\square$

## 追加锚（本行以下为增补区）

## 16. Exact local simulation by factors with a multiplicative face equality

**定义 16.1（底面乘法相等的严格正子语言）。** Retain the complete rational tables, ordered actual-variable scopes, permitted repetitions, finite hidden sums and global normalization of Definition 15.1. Let $W_{\mathrm{res}}$ be the sublanguage of $W_+$ in which every factor additionally satisfies

$$
 f(000)f(110)=f(100)f(010).
\tag{16.1}
$$

Thus every local table is normalized, strictly positive at each of the five tuples of $A$ in (15.1), and zero at the other three tuples. Equation (16.1) concerns the complete table even when its scope identifies variables and never visits some entries. All operations and the rational coefficient field remain those of Definition 15.1.

**命题 16.2（完整受限表与内部零钉）。** Define the normalized table $\mathsf H=\mathbf1_A/5$. For each $t\in\mathbb Q_{>0}$ define the complete normalized activity table $\mathsf V_t$ by

$$
 \begin{aligned}
 (\mathsf H(000),\mathsf H(100),\mathsf H(010),\mathsf H(110),\mathsf H(001))
 &=\frac{(1,1,1,1,1)}5,\\
 (\mathsf V_t(000),\mathsf V_t(100),\mathsf V_t(010),\mathsf V_t(110),\mathsf V_t(001))
 &=\frac{(1,t,1,t,1)}{3+2t},\\
 \mathsf H(101)=\mathsf H(011)=\mathsf H(111)
 &=\mathsf V_t(101)=\mathsf V_t(011)=\mathsf V_t(111)=0.
 \end{aligned}
\tag{16.2}
$$

Both belong to $W_{\mathrm{res}}$. A fresh hidden variable $o$ with the factor $\mathsf H$ on $(o,o,o)$ generates the pin $o=0$. On assignments obeying this pin, a factor $\mathsf V_t$ on $(u,o,o)$ implements the vertex activity $t^u$ up to its local normalization. For any two actual variables $a,b$, a factor $\mathsf H$ on $(a,a,b)$ implements the exclusion $ab=0$, also with its local normalization.

**Proof.** The table sums in (16.2) are $5/5=1$ and $(3+2t)/(3+2t)=1$. Each of their five allowed entries is positive rational. The two sides of (16.1) are $1/25$ for $\mathsf H$ and $t/(3+2t)^2$ for $\mathsf V_t$. These statements check every table entry independently of its later scope. Direct evaluation gives

$$
 \mathsf H(o,o,o)=\frac15\mathbf1_{\{o=0\}},\qquad
 \left.\mathsf V_t(u,o,o)\right|_{o=0}=\frac{t^u}{3+2t},\qquad
 \mathsf H(a,a,b)=\frac15\mathbf1_{\{ab=0\}}.
\tag{16.3}
$$

Indeed the diagonal triples are $000,111$, of which only $000$ lies in $A$, and $(a,a,b)\in A$ exactly when $ab=0$. The zero in the middle evaluation of (16.3) is the value of the actual variable $o$ under its pin; the scope itself remains $(u,o,o)$. Thus neither the activity nor the exclusion is an additional primitive. $\square$

**命题 16.3（任意正有理二元表的精确局部实现）。** Let $B=(b_{uv})_{u,v\in\{0,1\}}$ have four strictly positive rational entries. There is a finite product $\mathcal G_B(u,v,o,\xi)$ of tables from (16.2), with terminals $u,v$, one fresh zero variable $o$, and fresh hidden variables $\xi$, such that

$$
 \left.\sum_{\xi}\mathcal G_B(u,v,o,\xi)\right|_{o=0}
 =c_B b_{uv},\qquad c_B\in\mathbb Q_{>0}.
\tag{16.4}
$$

The pin for $o$ is counted separately. Every terminal assignment has a positive extension. The identity also holds after identifying the two terminals with the same actual variable.

**Proof.** Put

$$
 r=\frac{b_{00}b_{11}}{b_{10}b_{01}}>0.
\tag{16.5}
$$

In the following graphs, an edge $\{a,b\}$ denotes exactly the factor $\mathsf H$ on $(a,a,b)$, and an activity $t$ at a vertex $w$ denotes exactly a factor $\mathsf V_t$ on $(w,o,o)$. All internal vertices are fresh hidden variables. First calculate the terminal table $M$ of the finite hidden sum with the assignment-independent local normalization constants removed. Rows are indexed by $u=0,1$ and columns by $v=0,1$.

If $r=1$, take no edge and no internal vertex. Then

$$
 M=\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\tag{16.6}
$$

If $r>1$, use the path $u-p-v$, giving its hidden vertex $p$ activity $r-1\in\mathbb Q_{>0}$. At terminals $00$, summing over $p$ gives $1+(r-1)=r$. If either terminal is one, $p$ is forced to zero. Hence

$$
 M=\begin{pmatrix}r&1\\1&1\end{pmatrix}.
\tag{16.7}
$$

If $0<r<1$, set

$$
 \alpha=\frac2r-1>0,\qquad
 \beta=\frac{2(1-r)}r>0,
\tag{16.8}
$$

and use the path $u-p-q-v$ with hidden activities $\alpha$ at $p$ and $\beta$ at $q$. At terminals $00$, the permitted hidden words $(p,q)$ are $00,10,01$, contributing $1,\alpha,\beta$. At $10$, $p=0$ and $q$ is free; at $01$, $q=0$ and $p$ is free; at $11$, both are zero. Therefore

$$
 M=\begin{pmatrix}1+\alpha+\beta&1+\alpha\\1+\beta&1\end{pmatrix}
  =\begin{pmatrix}2(2-r)/r&2/r\\(2-r)/r&1\end{pmatrix}.
\tag{16.9}
$$

All three cases give positive rational entries, $M_{11}=1$, and $M_{00}M_{11}/(M_{10}M_{01})=r$. For (16.9) the ratio is exactly $[2(2-r)/r]/[2(2-r)/r^2]=r$. The strict cases use only strictly positive activities; the case $r=1$ uses neither a zero activity nor a limit of the other cases.

Put $s=M_{00}$ and append the two terminal activities

$$
 \lambda_u=\frac{b_{10}s}{b_{00}M_{10}},\qquad
 \lambda_v=\frac{b_{01}s}{b_{00}M_{01}},\qquad
 E_{uv}=\lambda_u^u\lambda_v^v M_{uv}.
\tag{16.10}
$$

Both activities are positive rational. Direct substitution at $00,10,01$ gives $E_{uv}=(s/b_{00})b_{uv}$. At $11$ the cross-ratio identity gives

$$
 E_{11}
 =\frac{b_{10}b_{01}s^2M_{11}}{b_{00}^2M_{10}M_{01}}
 =\frac{s}{b_{00}}\frac{b_{10}b_{01}r}{b_{00}}
 =\frac{s}{b_{00}}b_{11}.
\tag{16.11}
$$

Implement every listed activity, including both terminal activities, by (16.3). If the graph has $e$ edges and its complete list of activity parameters is $t_1,\ldots,t_k$, restoring every local normalization gives (16.4) with

$$
 c_B=\frac{s}{b_{00}}\,5^{-e}
       \prod_{i=1}^k(3+2t_i)^{-1}\in\mathbb Q_{>0}.
\tag{16.12}
$$

The edge counts are respectively $0,2,3$ in the three cases; their activity lists are respectively $(\lambda_u,\lambda_v)$, $(r-1,\lambda_u,\lambda_v)$ and $(\alpha,\beta,\lambda_u,\lambda_v)$. The common pin contributes no factor to $c_B$. All internal vertices zero give a positive summand for every terminal assignment, including $11$.

The equations are identities for the formal terminal bits before any scope substitution. Substituting the same actual variable for $u$ and $v$ preserves each identity pointwise. Terminal activities or edge scopes that then coincide remain separate permitted factors in the product. No equality factor is needed. In particular (16.4) is an implementation by normalized restricted ternary tables, rather than permission to supply $B$ as a binary factor. $\square$

**定理 16.4（逐因子模拟与有限网络的同律替换）。** Every individual $W_+$ factor on any ordered actual-variable scope has a finite $W_{\mathrm{res}}$ replacement whose effective table, conditional on one internally generated zero pin and after summing its fresh hidden variables, is a positive rational constant times the original factor. The constant is independent of all assignments to the original variables. Every finite $W_+$ network consequently has a finite $W_{\mathrm{res}}$ network with exactly the same normalized visible law, retaining its original variables and their identifications.

**Proof.** Let $f$ be any normalized rational table strictly positive on $A$ and zero outside $A$, without assuming (16.1). Define

$$
 b_{00}=f(000),\quad b_{10}=f(100),\quad
 b_{01}=f(010),\quad b_{11}=f(110),\qquad
 \tau=\frac{f(001)}{f(000)}\in\mathbb Q_{>0}.
\tag{16.13}
$$

This is a positive rational binary table $B$. On all eight formal triples,

$$
 f(x,y,z)=\mathbf1_A(x,y,z)\,b_{xy}\tau^z.
\tag{16.14}
$$

For $z=0$ this is the definition of $B$ on the four permitted triples. For $z=1$, the only permitted triple is $001$, where $b_{00}\tau=f(001)$. Off $A$ both sides vanish.

On the original scope $(x,y,z)$, replace $f$ by the product

$$
 \mathcal R_f(x,y,z,o,\xi)
 =\mathsf H(x,y,z)\,
   \mathcal G_B(x,y,o,\xi)\,
   \mathsf V_\tau(z,o,o).
\tag{16.15}
$$

Here $\mathcal G_B$ is the ternary-factor product of Proposition 16.3, with fresh internal variables $\xi$. Its notation introduces no binary primitive. By (16.3), (16.4) and (16.14),

$$
 \left.\sum_\xi\mathcal R_f(x,y,z,o,\xi)\right|_{o=0}
 =c_f f(x,y,z),\qquad
 c_f=\frac{c_B}{5(3+2\tau)}\in\mathbb Q_{>0}.
\tag{16.16}
$$

Each actual complete ternary table in (16.15) is $\mathsf H$ or some $\mathsf V_t$ and obeys (16.1). The unrestricted table $f$ is removed. Equation (16.16) holds pointwise on the complete three-bit cube, so it survives any identification among $x,y,z$, including all three equal. None of the unvisited entries of any replacement table is altered.

For a network with factors $f_1,\ldots,f_N$, introduce one common fresh $o$ and its single pin $\mathsf H(o,o,o)$. Use (16.15) for each factor, choosing pairwise disjoint sets $\xi_j$ of new internal variables, all disjoint from the original variables and $o$. The replacements may share any of their original terminals. Fix an assignment $b$ of all original visible and hidden variables, and let $b_j$ be its ordered triple at the $j$th original scope. On $o=0$ the only remaining variables shared between different replacements have already been fixed. Finite distributivity therefore gives

$$
 \begin{aligned}
 &\sum_{o,\xi_1,\ldots,\xi_N}
   \mathsf H(o,o,o)\prod_{j=1}^N\mathcal R_{f_j}(b_j,o,\xi_j)\\
 &\qquad=\frac15\prod_{j=1}^N
       \left(\left.\sum_{\xi_j}\mathcal R_{f_j}(b_j,o,\xi_j)\right|_{o=0}\right)
   =C\prod_{j=1}^N f_j(b_j),\qquad
 C=\frac15\prod_{j=1}^N c_{f_j}\in\mathbb Q_{>0}.
 \end{aligned}
\tag{16.17}
$$

The pin eliminates $o=1$ before the separate hidden sums are factored. Thus the common zero is counted once, while (16.12) and (16.16) count all edge, activity and original-scope normalization factors.

Now sum (16.17) over the original hidden variables. If $W(a)$ and $Z$ are the original unnormalized visible weights and their total, the replacement has

$$
 W'(a)=CW(a),\qquad Z'=CZ>0,\qquad
 P'(a)=\frac{W'(a)}{Z'}=\frac{W(a)}Z=P(a).
\tag{16.18}
$$

Every sum and product is finite and rational. In particular $Z'$ is finite, positive and rational. For $N=0$, all products over factors are empty and $C=1/5$; the additional pin alone multiplies the original weights by $1/5$, so (16.18) still holds. All repetitions, coincident scopes and original hidden-variable identifications have remained intact. The construction uses only the actual-variable scopes of (16.2), multiplication, finite hidden summation and final normalization; every parameter in it is positive rational. $\square$

**推论 16.5（受限语言不改变有理可见律分类）。** For every integer $n\ge1$, a rational probability law on $\{0,1\}^n$ is representable in $W_{\mathrm{res}}$ if and only if its support is $\operatorname{Ind}(K)$ for some labelled undirected graph $K$ with loops allowed. Every assignment of positive rational masses summing to one on that support is included, exactly as in Theorem 15.2.

**Proof.** A $W_{\mathrm{res}}$ network is a $W_+$ network, so necessity is the support assertion of Theorem 15.2. For sufficiency, use that theorem to obtain a finite rational $W_+$ network for the specified law and use Theorem 16.4 to replace it without changing its normalized visible law. This includes $n=1$, visible loops, the singleton all-zero support and empty original factor sets. The support proof and the arbitrary-weight construction of Theorem 15.2 are suppliers, rather than additional assertions proved here.

The local activity model is already given in [the hidden-relations volume, C-59.2--C-59.5](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md#59-带标号正活动环与局部四角问题), and its two-terminal finite path elimination is [the continuation, C-60.1--C-60.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md#60-外部路径的完整响应与五律). Those specified activity and path formulas supply the existing mechanism. Equations (16.6)--(16.12) choose positive rational path activities and terminal scalings for every positive rational binary table; (16.14)--(16.18) give the complete local simulation under the restricted normalized ternary interface.

For primary comparison, Bulatov--Dyer--Goldberg--Jerrum--McQuillan, [*The expressibility of functions on the Boolean domain, with applications to Counting CSPs*, arXiv:1108.5288v4, §2, equations (1)--(4) and Lemma 1](https://arxiv.org/pdf/1108.5288v4), define finite primitive product summation formulas with repeated scope variables and composition by disjoint bound variables. Their generated functional clone includes equality, and their separately defined $\mathrm{pps}_\omega$ closure permits limits. Bulatov--Goldberg--Jerrum--Richerby--Živný, [*Functional Clones and Expressibility of Partition Functions*, arXiv:1609.07377v2, §1.1, including footnote 2](https://arxiv.org/pdf/1609.07377v2), likewise distinguish finite functional clones from $\omega$-clones, over nonnegative real-valued functions with equality included. These cited interfaces do not themselves supply (16.15) using only the normalized rational ternary tables satisfying (16.1); no equality, unary factor or limit is imported from them. The real-parameter directed representation in Smirnov, [*Deep belief networks are exact*, arXiv:2609.05572v1, Theorem 1.1 and §1](https://arxiv.org/html/2609.05572v1), remains the different interface identified in Corollary 15.4. This is an elementary repository-derived exact-interface construction, without a claim of global originality or exhaustive literature absence. $\square$

**推论 16.6（既有正噪声平台律的受限同律表示）。** For every rational $0<\eta\le1$, the five-visible-bit encoding (15.14) of $J_{H,\eta}$ has a finite rational $W_{\mathrm{res}}$ representation with exactly the same joint distribution. Consequently its posteriors and decision risks already established in Corollary 15.4 are unchanged.

**Proof.** Corollary 15.4 supplies the finite rational $W_+$ representation of precisely this encoded joint law. Apply Theorem 16.4 to that network. Equation (16.18) preserves the entire visible distribution, and decoding by the same bijections (15.14) gives exactly $J_{H,\eta}$. Equality of these joint laws preserves their posteriors at positive-mass outputs and their decision risks; the posterior and risk calculations are those already used in Corollary 15.4. Each rational $\eta$ may use its own finite network, with the operations and interpretation of Definition 15.1 and the boundaries of Corollary 15.4. $\square$

## 追加锚（本行以下为增补区）
