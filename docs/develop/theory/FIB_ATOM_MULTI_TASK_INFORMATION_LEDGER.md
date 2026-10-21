# FIB atoms: multi-task information ledger and the five-class risk frontier

This is an independent theory volume. It does not modify `FIBONACCI_ATOMIC_RELATION_GENERATION.md`. It connects the task-information and Bayes-risk geometry of the preceding volume with the five legal FIB window labels, the task-partition/white-box theory, and the recent record/readout boundary results on `dev`.

The central conclusion is that a model does not have one task-independent amount of useful information. A finite readout must be evaluated against a specified task family, probability law, loss, future operation set, and resource contract. The resulting ledger has structural capacity, Bayes risk, and mutual information as separate coordinates.

All mathematical arguments below are ordinary finite-model derivations. They are not Lean verification, a training experiment, a general neural-network theorem, or a physical FIB claim. The entropy unit is bits unless `ln` is written explicitly.

## 1. A task ledger rather than one information number

Let $D$ be a finite task index set. Fix one finite deployment law. For each $d\in D$, let $Y_d$ be a finite-valued target and let $Q_A$ be the readout obtained from an observed feature set $A$. The same $Q_A$ may be used for every task, but the tasks need not have the same marginal law or the same optimal decoder. The joint-law statements below require this common deployment law and the common readout.

For a deterministic finite task $F_d$, let

$$
\kappa_A(F_d)=|X_A/{\sim_A^{F_d}}|
$$

be the exact boundary capacity from the observation-boundary theory. Under a deployment probability law, write $e_d(A)$ for the Bayes zero-one risk of $Y_d$ from $Q_A$, and

$$
I_d(A)=I(Y_d;Q_A).
$$

A weighted ledger uses nonnegative weights $w_d$, with $W=\sum_d w_d>0$ and $\alpha_d=w_d/W$:

$$
\bar\kappa_A=(\kappa_A(F_d))_{d\in D},\qquad
\bar e(A)=\sum_d\alpha_d e_d(A),\qquad
\bar I(A)=\sum_d\alpha_d I_d(A).
$$

The vector $\bar\kappa_A$ is a zero-error structural certificate; $\bar e(A)$ and $\bar I(A)$ are distributional coordinates. None can be replaced by the other two. In particular, a nuisance feature may have large hidden-state mutual information and zero information about a chosen task, while an exact task readout may discard most of the hidden state.

## 2. The per-task risk-information envelope

First consider one binary task $Y\sim\operatorname{Bern}(p)$ with $0<p<1$. For a finite readout $Q$, put

$$
\eta(q)=\Pr(Y=1\mid Q=q),\qquad
r(q)=\min\{\eta(q),1-\eta(q)\},
$$

where zero-mass fibres are omitted. Then

$$
 e=\mathbb E[r(Q)],\qquad
I=H_2(p)-\mathbb E[h_2(r(Q))],
$$

and $0\le e\le m:=\min\{p,1-p\}$.

**定理 1（非平衡二元风险—信息包络）。**

For every finite readout,

$$
\boxed{
H_2(p)-h_2(e)\le I\le H_2(p)\left(1-\frac e m\right).
}
$$

The left endpoint is attained when the posterior error is constant. The right endpoint is attained by an erasure readout: reveal $Y$ with probability $1-\lambda$, erase it otherwise, and choose $\lambda=e/m$.

**证明。** The binary entropy is concave on $[0,1/2]$, so

$$
\mathbb E[h_2(r)]\le h_2(\mathbb E r)=h_2(e).
$$
The chord joining $(0,0)$ and $(m,H_2(p))$ lies below the concave graph on $[0,m]$, hence

$$
 h_2(r)\ge \frac{H_2(p)}m r.
$$
Taking expectations and subtracting from $H_2(p)$ gives the two bounds. The stated posterior forms give equality. $\square$

The weaker upper bound $I\le H_2(p)-2e$ is also valid because $H_2(p)/m\ge2$. The balanced case $p=1/2$ is sharp in the familiar form

$$
\boxed{1-h_2(e)\le I\le1-2e.}
$$

Thus mutual information fixes an interval of possible task risks. A BSC and a BEC can have the same $I$ and different $e$; the information number alone cannot rank their zero-one task quality.

## 3. Aggregating tasks with correct weights

Let each ledger coordinate be a nondegenerate binary task, and use the notation of Section 2. Define

$$
\bar H=\sum_d\alpha_d H_2(p_d),\qquad
\bar e=\sum_d\alpha_d e_d,\qquad
\bar I=\sum_d\alpha_d I_d.
$$

**定理 2（加权风险账本包络）。**

The coordinate-wise envelopes imply

$$
\boxed{
\bar H-\sum_d\alpha_d h_2(e_d)
\le \bar I
\le \bar H-\sum_d\alpha_d\frac{H_2(p_d)}{m_d}e_d,
}
$$

where $m_d=\min\{p_d,1-p_d\}$. Consequently,

$$
\boxed{
\bar H-h_2(\bar e)\le\bar I\le\bar H-2\bar e.
}
$$

If every task is balanced, then $\bar H=1$ and the preceding display becomes the balanced sandwich for the weighted ledger.

**证明。** Multiply Theorem 1 by $\alpha_d$ and sum. Concavity of $h_2$ gives $\sum_d\alpha_d h_2(e_d)\le h_2(\bar e)$, which yields the coarser lower bound. The upper bound uses $H_2(p_d)/m_d\ge2$. $\square$

The normalization is material. With unnormalized weights, the lower bound is

$$
\sum_d w_d I_d\ge \sum_d w_dH_2(p_d)-W h_2\!\left(\frac{\sum_d w_de_d}{W}\right),
$$

and the upper bound is $\sum_d w_dH_2(p_d)-2\sum_d w_de_d$. A formula that silently assumes $\sum_d w_d=1$ changes its scale.

## 4. Joint task information and total-correlation correction

Let $Y=(Y_d)_{d\in D}$ be the task vector. Define total correlation by

$$
\operatorname{TC}(Y)=\sum_d H(Y_d)-H(Y),
$$

and conditionally by

$$
\operatorname{TC}(Y\mid Q)=\sum_d H(Y_d\mid Q)-H(Y\mid Q).
$$

**定理 3（任务账本的总相关修正）。**

For every finite joint law,

$$
\boxed{
\sum_d I(Y_d;Q)-I(Y;Q)
=\operatorname{TC}(Y)-\operatorname{TC}(Y\mid Q).
}
$$

**证明。** Expand both mutual informations as entropy differences and group the unconditional and conditional terms:

$$
\begin{aligned}
\sum_d I(Y_d;Q)-I(Y;Q)
&=\sum_d[H(Y_d)-H(Y_d\mid Q)]-[H(Y)-H(Y\mid Q)]\\
&=\operatorname{TC}(Y)-\operatorname{TC}(Y\mid Q).
\end{aligned}
$$

$\square$

This is standard Shannon algebra; the new FIB use is to retain the correction in the task ledger. The sum of per-task informations is not a vector-task information by default.

Two finite witnesses show the two directions. If $Y_1=Y_2=U$ and $Q=U$ for a fair bit $U$, then

$$
I(Y_1;Q)+I(Y_2;Q)=2,qquad I((Y_1,Y_2);Q)=1.
$$

If $Y_1,Y_2$ are independent fair bits and $Q=Y_1\oplus Y_2$, then

$$
I(Y_1;Q)=I(Y_2;Q)=0,qquad I((Y_1,Y_2);Q)=1.
$$

The first is redundancy; the second is higher-order synergy. Therefore a scalar sum can overcount or undercount the information required by the joint task.

## 5. The five FIB labels are one-hot, not five balanced tasks

Let

$$
C\in\{\texttt{null},\texttt{2},\texttt{3},\texttt{2 5},\texttt{5}\}
$$

be the legal three-position FIB window label, and put $Y_d=\mathbf 1_{\{C=d\}}$. Then $\sum_dY_d=1$, so the five coordinates are mutually exclusive and cannot all have prior $1/2$.

The joint task vector carries exactly the categorical label:

$$
I((Y_d)_d;Q)=I(C;Q).
$$

Writing $p_d=\Pr(C=d)$ and $H_2^{\mathrm{cat}}(p)=-\sum_dp_d\log_2p_d$, its prior total correlation is

$$
\operatorname{TC}(Y)=\sum_d h_2(p_d)-H_2^{\mathrm{cat}}(p).
$$

For a posterior class vector $q=(q_d)_d$ in the five-simplex,

$$
\operatorname{TC}(q)=\sum_d h_2(q_d)-H_2^{\mathrm{cat}}(q)
=-\sum_d(1-q_d)\log_2(1-q_d).
$$

The right side is concave on the simplex. Jensen therefore gives

$$
\operatorname{TC}(Y\mid Q)\le\operatorname{TC}(Y),
$$

and hence the one-hot special case obeys

$$
\boxed{\sum_d I(Y_d;Q)\ge I(C;Q).}
$$

For a uniform five-label source with complete readout $Q=C$,

$$
\sum_d I(Y_d;Q)=5h_2(1/5)\approx3.60964,
\qquad
I(C;Q)=\log_2 5\approx2.32193.
$$

The excess is redundancy caused by the one-hot encoding, not extra task knowledge. Conversely, an unstructured multitask vector need not satisfy this sign; the XOR witness in Section 4 gives the opposite direction.

The weighted sum of the five binary risks is also not the five-class zero-one risk. At posterior class vector $q$, the categorical Bayes risk is $1-\max_d q_d$, whereas the sum of the five indicator risks is

$$
\sum_d\min\{q_d,1-q_d\}
=
\begin{cases}
1,&\max_d q_d\le1/2,\\
2(1-\max_d q_d),&\max_d q_d\ge1/2.
\end{cases}
$$

Thus the categorical risk and a one-hot risk ledger are related but distinct objectives; a report must name which one it optimizes.

A five-row ledger for the FIB window should therefore contain, for each label or derived relation task,

| task coordinate | exact capacity | Bayes risk | task MI | joint/vector relation | escape witness |
|---|---:|---:|---:|---|---|
| `null` | $\kappa_A(F_{\texttt{null}})$ | $e_{\texttt{null}}(A)$ | $I_{\texttt{null}}(A)$ | one-hot or derived | pair / continuation |
| `2` | $\kappa_A(F_{\texttt{2}})$ | $e_{\texttt{2}}(A)$ | $I_{\texttt{2}}(A)$ | one-hot or derived | pair / continuation |
| `3` | $\kappa_A(F_{\texttt{3}})$ | $e_{\texttt{3}}(A)$ | $I_{\texttt{3}}(A)$ | one-hot or derived | pair / continuation |
| `2 5` | $\kappa_A(F_{\texttt{2 5}})$ | $e_{\texttt{2 5}}(A)$ | $I_{\texttt{2 5}}(A)$ | joint relation | pair / continuation |
| `5` | $\kappa_A(F_{\texttt{5}})$ | $e_{\texttt{5}}(A)$ | $I_{\texttt{5}}(A)$ | one-hot or derived | pair / continuation |

The label `2 5` is a legal joint window and can carry a relation interaction such as the $b_1b_3$ coefficient in the five-point function expansion. That does not make it an XOR task, and it does not make the five one-hot rows independent. A joint relation must be assigned its own target and joint readout contract.

## 6. Conditional information is a risk-improvement budget

Suppose $A\subseteq B$ and $Q_A$ is a deterministic coarsening of $Q_B$. For each binary task put

$$
\Delta e_d=e_d(A)-e_d(B)\ge0,
\qquad
\Delta I_d=I(Y_d;Q_B\mid Q_A).
$$

**定理 4（加权增量预算）。**

When $\Delta I_d$ is measured in bits,

$$
\boxed{
\Delta\bar e
:=\sum_d\alpha_d\Delta e_d
\le
\sqrt{\frac{\ln2}{2}\sum_d\alpha_d\Delta I_d}.
}
$$

Equivalently, with conditional information in nats,

$$
\sum_d\alpha_d\Delta I_{d,\mathrm{nats}}
\ge \frac{2(\Delta\bar e)^2}{1}.
$$

**证明。** The binary conditional-information Pinsker bound gives

$$
\Delta I_{d,\mathrm{nats}}\ge2(\Delta e_d)^2.
$$

Multiply by $\alpha_d$ and sum. Weighted Cauchy–Schwarz gives

$$
\sum_d\alpha_d(\Delta e_d)^2\ge\left(\sum_d\alpha_d\Delta e_d\right)^2.
$$

Convert nats to bits to obtain the displayed inequality. $\square$

This is a necessary budget, not a converse: positive conditional information can leave zero-one risk unchanged when a refinement only sharpens posteriors on the same side of the decision boundary. The bound is for binary tasks; a multiclass version requires a separately stated finite-class loss and inequality.

## 7. Escape witnesses and white-box insufficiency

Let $S$ be a finite state space with positive deployment mass $\mu$, let $q:S\to Q$ be a finite readout, and let $Y:S\to\{0,1\}$ be a task.

**命题 5（正质量逃逸见证）。** If there are $s_0,s_1$ with

$$
q(s_0)=q(s_1),\qquad Y(s_0)=0,\qquad Y(s_1)=1,
$$

and $\mu(s_0),\mu(s_1)>0$, then every deterministic classifier using only $q$ has positive Bayes risk. More precisely, the conflicting fibre contributes at least

$$
\min\{\mu(s_0),\mu(s_1)\}
$$

to the total Bayes risk.

**证明。** The $q$-fibre containing the two states has positive mass on both labels. Its optimal constant decision incurs the smaller label mass in that fibre, which is at least the smaller of the two displayed masses. $\square$

This is a finite-readout insufficiency certificate. A zero-mass collision is not a deployment-risk witness. A positive task mutual information is a distributional statement and does not itself name a unique state pair. For dynamic white-boxity, replace $Y$ by a future response $F_w$ after a fixed legal continuation $w$; a pair with equal current readout and different $F_w$ is a dynamic escape witness.

Thus the correct ML claim is conditional: a representation is white-box for a declared task and operation family when its fibres are constant under all required current and future responses, and its updates descend to the quotient. An escape witness disproves that sufficiency for the declared contract. It does not by itself prove a statement about all architectures, all training runs, OOD data, or a different deployment measure.

## 8. What makes one model better than another

Fix a task family, deployment law, loss, allowed interventions, and resource accounting. A representation or model is better on this contract when it achieves a lower relevant risk or a stronger exact response quotient at no greater declared cost. The comparison is generally Pareto-valued:

$$
(\text{structural capacity},\ \text{task risks},\ \text{task informations},\ \text{dynamic closure},\ \text{cost}).
$$

There is no universal ordering by parameter count, mutual information, number of neurons, or number of FIB labels. The proof mechanism is visible in the preceding results:

- Theorem 1 permits equal information with unequal task risk.
- Theorem 3 permits a task-information sum to differ from vector-task information in either direction for a general task vector.
- Theorem 4 limits risk improvement by conditional information but does not make every informative refinement useful for zero-one loss.
- Proposition 5 turns a positive-mass same-readout/different-response pair into a concrete white-box counterexample.

This gives a proof-based answer to why models can be good or bad. A model is bad for a declared contract when it merges a response-distinguishable pair, spends information on an irrelevant nuisance, has insufficient dynamic state for the allowed update, or pays more resource for no Pareto improvement. It is good only relative to the same contract and after its claimed response quotient and risk coordinates are checked.

## 9. Relation to the current DEV theory and limits

The [task-partition Galois theory](FIB_TASK_PARTITION_GALOIS_AND_WHITEBOX.md) supplies the task-family/state-partition correspondence. The [observation-boundary algebra](OBSERVATION_BOUNDARY_ALGEBRA_MINIMAL_REALIZATION.md) supplies the minimal completion-response quotient and its compositional interface. The [FIB white-box volume](FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md) supplies the five legal windows, the `101` interaction direction, recursive seam states, and the distinction between a current prediction and a training-dynamic explanation. The [record/readout work](AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md) further requires moving readouts and history updates to be checked under their actual continuation contract.

The new synthesis is the quantitative ledger joining these layers:

$$
\boxed{
\text{response quotient}
\;+
\text{Bayes-risk coordinate}
\;+
\text{task MI coordinate}
\;+
\text{joint-correlation correction}
\;+
\text{escape witness}.
}
$$

It does not claim that a trained neural network has been extracted into the FIB quotient, that the ledger is a universal generalization bound, or that a smaller quotient automatically means lower memory, energy, or runtime. Those are separate contracts requiring evidence.

## 追加锚（本行以下为增补区）
