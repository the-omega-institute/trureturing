# FIB atoms: multi-task information ledger

## 1. Common finite law and task coordinates

**定义 1.1（有限任务账本）。** Let $S$ be a finite probability space, $C:S\to\Sigma$ a label, $Q_A:S\to\mathcal Q_A$ a deterministic readout, and $(Y_d:S\to\mathcal Y_d)_{d\in D}$ a finite task family. All tasks and readouts in a comparison use this same law. For nonnegative weights $w_d$ with $W=\sum_dw_d>0$, put $\alpha_d=w_d/W$ and

$$
\begin{aligned}
e_d(A)&=\inf_{g:\mathcal Q_A\to\mathcal Y_d}\Pr(g(Q_A)\ne Y_d),\\
I_d(A)&=I(Y_d;Q_A),\\
\bar e(A)&=\sum_d\alpha_de_d(A),\qquad
\bar I(A)=\sum_d\alpha_dI_d(A).
\end{aligned}
$$

Entropy is in bits, $h(t)=-t\log_2t-(1-t)\log_2(1-t)$, and $0\log_20=0$. Zero-probability outputs are omitted from conditional distributions. A channel relative to $C$ is represented by finite states $(c,q)$ of masses $\Pr(C=c,Q=q)$; both $C$ and $Q$ are deterministic projections. Determinism of $Q$ on $S$ does not require $Q=f(C)$.

For a deterministic response task $F_d$, let $X_A$ be its completion domain at observation $A$. Define $x\sim_A^{F_d}x'$ when all required completion responses agree, and put

$$
\kappa_A(F_d)=|X_A/{\sim_A^{F_d}}|.
$$

The response quotient and its continuation conditions are those of [the task-partition Galois volume](FIB_TASK_PARTITION_GALOIS_AND_WHITEBOX.md) and [the observation-boundary algebra](OBSERVATION_BOUNDARY_ALGEBRA_MINIMAL_REALIZATION.md). The ledger consists of the capacity vector, risk vector and information vector; it does not identify these coordinates.

## 2. Binary envelopes used in the five-window ledger

**定义 2.1（五窗指标任务）。** Use the low-to-high convention of [the FIB ML volume, Definition 2.1](FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md):

$$
\Sigma=(a,b,c,d,e)=(000,100,010,101,001).
$$

The labels are respectively $\mathrm{null},2,3,2\,5,5$. Set $Y_i=\mathbf1_{\{C=i\}}$, $p_i=\Pr(C=i)$, $m_i=\min(p_i,1-p_i)$ and $r_i=e_i(A)$. The same definitions apply to any explicitly supplied binary derived task, with its own prior.

**数学引文（五窗账本所用的经典坐标与加权界）。** For every common finite law of Definition 2.1,

$$
0\le r_i\le m_i,\qquad
h(p_i)-h(r_i)\le I(Y_i;Q_A)\le h(p_i)-2r_i.
\tag{2.1}
$$

For any fixed binary prior $p$ and any $0\le u\le\min(p,1-p)$, both endpoints of the corresponding scalar interval are attained by finite deterministic-readout laws. This existence statement varies the finite law; it does not assert simultaneous endpoint attainment for a prescribed correlated task vector and common readout.

Writing $\bar H=\sum_i\alpha_ih(p_i)$ gives

$$
\boxed{
\bar H-\sum_i\alpha_ih(r_i)
\le\bar I\le\bar H-2\bar e,
\qquad
\bar H-h(\bar e)\le\bar I.
}
\tag{2.2}
$$

Proof. The scalar inequalities used here are classical binary entropy/error bounds; the error-to-entropy estimate $2u\le H(Y\mid Q)$ is the binary specialization of Hellman–Raviv, §III, equation (18), [DOI 10.1109/TIT.1970.1054466](https://doi.org/10.1109/TIT.1970.1054466), [primary text](https://ee.stanford.edu/~hellman/publications/07.pdf). For completeness of the parameter correspondence, write

$$
\eta(q)=\Pr(Y=1\mid Q=q),\qquad
\nu(q)=\min(\eta(q),1-\eta(q)).
$$

Then $u=\mathbb E\nu$, $I(Y;Q)=h(p)-\mathbb Eh(\nu)$ and $0\le\nu\le1/2$. Concavity and the chord on $[0,1/2]$ give

$$
2u\le\mathbb Eh(\nu)\le h(u).
\tag{2.3}
$$

The bound $u\le\min(p,1-p)$ follows by considering the two constant classifiers. It is a bound on the average error, not on each $\nu(q)$.

Here are finite joint laws attaining both endpoints. For the lower information endpoint, if $u<1/2$, let

$$
\theta=\frac{p-u}{1-2u}\in[0,1]
$$

and specify outputs $q_+,q_-$ with masses $\theta,1-\theta$ and posteriors $\eta(q_+)=1-u$, $\eta(q_-)=u$. The mean is $p$, every posterior error is $u$, and $H(Y\mid Q)=h(u)$. An output of zero mass is discarded. If $u=1/2$, feasibility forces $p=1/2$; one constant output has the required law.

For the upper information endpoint, give $(Y,Q)$ the nonzero entries

$$
\begin{array}{c|ccc}
 &q_*&q_1&q_0\\ \hline
Y=1&u&p-u&0\\
Y=0&u&0&1-p-u
\end{array}
\tag{2.4}
$$

All entries are nonnegative. The ambiguous output has mass $2u$ and posterior $1/2$, while the others reveal the label, so its conditional entropy is $2u$. At $u=0$ both constructions reveal $Y$ up to zero-mass outputs. At $p=0$ or $p=1$ feasibility forces $u=0$ and $I=0$. At $p=u=1/2$ the ambiguous output has mass one. These include all degenerate boundaries. A tagged mixture of the two joint laws, with a tag independent of $Y$ included in the output, retains prior $p$ and error $u$ and interpolates their informations. Its state is the finite triple $(Y,\text{tag},Q)$, so every intermediate value in the interval is also attained.

Strict concavity in (2.3) makes lower-information equality equivalent to constant posterior error; upper-information equality is equivalent to posterior errors in $\{0,1/2\}$. An erasure independent of $Y$, with erasure probability $u/\min(p,1-p)$, instead gives

$$
I=h(p)\left(1-\frac{u}{\min(p,1-p)}\right)
\tag{2.5}
$$

for a nondegenerate prior. This is an attainable value, not the upper envelope when $p\ne1/2$ and $u>0$. For example, masses

$$
\Pr(Y=1,Q=q_*)=1/5,\quad
\Pr(Y=0,Q=q_*)=1/5,\quad
\Pr(Y=0,Q=q_0)=3/5
$$

give $p=u=1/5$ and $I=h(1/5)-2/5>0$. Finally, multiply (2.1) by $\alpha_i$ and sum. Jensen gives $\sum_i\alpha_ih(r_i)\le h(\bar e)$, proving (2.2). $\square$

**数学引文（未归一权重与联合可达性）。** With the same hypotheses, the unnormalized form of (2.2) is

$$
\sum_iw_ih(p_i)-W h\!\left(\frac{\sum_iw_ir_i}{W}\right)
\le\sum_iw_iI(Y_i;Q_A)
\le\sum_iw_ih(p_i)-2\sum_iw_ir_i.
$$

These inequalities inherit only the coordinate-wise bounds. A simultaneous extremum must obey the common posterior simplex $\sum_i\Pr(C=i\mid Q_A)=1$. In particular, no product construction of separate indicator channels may replace that constraint. The graph-supported joint attainability conditions are given in [the categorical blindness volume](FIB_ATOM_CATEGORICAL_DECISION_BLINDNESS.md), Theorems 3.1–5.1.

## 3. One-hot correlation and categorical risk

**数学引文（五窗的经典冗余修正与风险坐标）。** For the five indicator tasks,

$$
\begin{aligned}
I((Y_i)_i;Q)&=I(C;Q),\\
\sum_iI(Y_i;Q)-I(C;Q)
&=T(p)-\mathbb E T(q(Q))\ge0,\\
T(v)&=-\sum_i(1-v_i)\log_2(1-v_i),
\end{aligned}
\tag{3.1}
$$

where $q_i(Q)=\Pr(C=i\mid Q)$. If $M=\max_iq_i$, the conditional categorical error is $1-M$ and

$$
\sum_i\min(q_i,1-q_i)=
\begin{cases}
1,&M\le1/2,\\
2(1-M),&M\ge1/2.
\end{cases}
\tag{3.2}
$$

Thus the sum of indicator risks and the categorical risk are distinct coordinates even under one common law.

Proof. The entropy expansion used here is the classical total-correlation identity, with total correlation in Watanabe's sense (*Information Theoretical Analysis of Multivariate Correlation*, 1960, [DOI 10.1147/rd.41.0066](https://doi.org/10.1147/rd.41.0066)):

$$
\begin{aligned}
\sum_iI(Y_i;Q)-I((Y_i)_i;Q)
&=\operatorname{TC}((Y_i)_i)-\operatorname{TC}((Y_i)_i\mid Q),\\
\operatorname{TC}(Z)&=\sum_iH(Z_i)-H(Z).
\end{aligned}
$$

The one-hot vector and $C$ determine each other. At a categorical law $v$, subtracting $H(v)$ from $\sum_ih(v_i)$ cancels the $-v_i\log_2v_i$ terms and leaves $T(v)$. Each summand of $T$ is concave, so $\mathbb ET(q(Q))\le T(p)$. If $M\le1/2$, all binary conditional errors equal $q_i$ and sum to one. Otherwise exactly one coordinate exceeds $1/2$; its error and the sum of the other errors both equal $1-M$. This proves (3.1)–(3.2).

For $p_i=1/5$ and $Q=C$, (3.1) specializes to

$$
\sum_iI(Y_i;C)=5h(1/5)>\log_25=I(C;C).
$$

The sign in (3.1) uses the one-hot constraint. For a general task vector it has no fixed sign: two identical fair-bit tasks revealed by $Q$ give information sum two and joint information one; two independent fair bits with only their XOR revealed give sum zero and joint information one. These are standard redundancy and synergy examples, not additional five-window results. $\square$

## 4. Refinement and positive ambiguity

**定义 4.1（细化）。** Suppose $Q_A=f(Q_B)$ on the same finite law. For the indicator tasks put

$$
\Delta r_i=r_i(A)-r_i(B),\qquad
\Delta I_i=I(Y_i;Q_B\mid Q_A).
$$

**数学引文（五窗细化所用的经典必要预算）。** Then $\Delta r_i\ge0$ and

$$
\sum_i\alpha_i\Delta r_i
\le\sqrt{\frac{\ln2}{2}\sum_i\alpha_i\Delta I_i}.
\tag{4.1}
$$

If two positive-mass states $s_0,s_1$ have the same $Q_A$ but different indicator labels $Y_i(s_0)\ne Y_i(s_1)$, that fibre contributes at least $\min(\Pr(s_0),\Pr(s_1))$ to $r_i(A)$.

Proof. The first inequality follows because every $Q_A$ classifier is also a $Q_B$ classifier. Apply the classical Pinsker inequality in nats,

$$
D_{\mathrm{KL}}(P\Vert R)\ge2\|P-R\|_{\mathrm{TV}}^2,
$$

to the conditional Bernoulli laws of $Y_i$ given $Q_B$ and $Q_A$. Its convention here is total variation $\frac12\sum|P-R|$; see M. S. Pinsker, *Information and Information Stability of Random Variables and Processes*, Holden-Day, 1964. The binary risk function $\min(t,1-t)$ is 1-Lipschitz. If $\eta_B=\Pr(Y_i=1\mid Q_B)$ and $\eta_A=\mathbb E(\eta_B\mid Q_A)$, this gives

$$
\Delta r_i\le\mathbb E|\eta_B-\eta_A|,
\qquad
\Delta I_{i,\mathrm{nats}}
\ge2\mathbb E|\eta_B-\eta_A|^2
\ge2(\Delta r_i)^2.
$$

Weighted Cauchy–Schwarz and conversion from nats prove (4.1). The ambiguity assertion is the positive-mass version of the fibre-separation criterion in [the task-partition Galois volume](FIB_TASK_PARTITION_GALOIS_AND_WHITEBOX.md): the smaller of the two total label masses in a fibre is at least the smaller displayed state mass. The same criterion applies to a specified future response $F_w$ after a legal continuation $w$, using $Y_i=F_w$ when that response is binary. $\square$

**定义 4.2（任务比较的范围）。** A comparison contract specifies the finite deployment law, targets, loss, allowed continuations, and cost function. Its coordinates may include

$$
\bigl((\kappa_A(F_d))_d,(e_d(A))_d,(I_d(A))_d,
\text{continuation closure},\text{cost}\bigr).
$$

Pareto comparison uses the declared direction of each coordinate. Exact response sufficiency means constancy of all required responses on readout fibres and descent of the required updates to the quotient, as in the cited task-partition and observation-boundary definitions. No identification of a neural-network state with this finite source, and no physical or training law, is an assumption of this ledger.

## 追加锚（本行以下为增补区）
