# FIB atoms: task information and Bayes escape risk

This volume continues the finite feature-lattice line behind the FIB atom and white-box certificate models. It is an independent theory volume. It does not change `FIBONACCI_ATOMIC_RELATION_GENERATION.md` and does not claim a continuous-network, training-dynamics, OOD, or physical FIB-R2 theorem.

The previous escape-risk coordinate is a signed mass on each observed fibre. The new question is whether mutual information can replace that task-relative coordinate. It cannot. The useful result is more precise: the two quantities are different Jensen gaps of the same posterior, they obey a sharp interval relation in the binary balanced case, and conditional information supplies a one-sided budget for a risk improvement.

All logarithms in this volume are base two unless `ln` is written explicitly. The state space and every feature alphabet are finite, the probability mass is normalized, and the loss is Bayes zero-one loss.

## 1. Finite task readouts and signed fibres

Let $S$ be a finite state space with mass $\mu$, let $Y:S\to\{0,1\}$ be a binary task, and let $Q_A:S\to U_A$ be the deterministic readout carried by an observed feature set $A$. Write

$$
M_A^+(u)=\sum_{Q_A(s)=u,\,Y(s)=1}\mu(s),\qquad
M_A^-(u)=\sum_{Q_A(s)=u,\,Y(s)=0}\mu(s),
$$

$$
m_A(u)=M_A^+(u)+M_A^-(u),\qquad
\sigma_A(u)=M_A^+(u)-M_A^-(u).
$$

Zero-mass fibres are omitted from conditional expressions. On every positive-mass fibre,

$$
\eta_A(u)=\Pr(Y=1\mid Q_A=u)
=\frac{M_A^+(u)}{m_A(u)}
=\frac{1}{2}\left(1+\frac{\sigma_A(u)}{m_A(u)}\right).
$$

The Bayes risk and task mutual information are

$$
 e(A)=\sum_u\min\{M_A^+(u),M_A^-(u)},
$$

$$
 I(A)=I(Y;Q_A)=H_2(p)-\sum_{m_A(u)>0}m_A(u)h_2(\eta_A(u)),
$$

where $p=\Pr(Y=1)$, $H_2(p)=h_2(p)$ is the prior binary entropy, and

$$
h_2(t)=-t\log_2 t-(1-t)\log_2(1-t),\qquad 0\log_2 0:=0.
$$

**定理 1（signed mass is the common coordinate）。**

For every finite task readout,

$$
\boxed{
 e(A)=\frac12\left(1-\sum_u|\sigma_A(u)|\right)
}
$$

and

$$
\boxed{
 I(A)=H_2(p)-\sum_{m_A(u)>0}m_A(u)
 h_2\!\left(\frac{1+\sigma_A(u)/m_A(u)}2\right).
}
$$

**证明。** The first identity uses $\min(a,b)=(a+b-|a-b|)/2$ and $\sum_um_A(u)=1$. The second substitutes the posterior expression into conditional entropy. Thus the signed norm alone determines Bayes risk, while mutual information also depends on the fibre masses and the posterior magnitudes. $\square$

This is the exact bridge to the finite FIB signature. It also marks the first failure of a tempting compression: there is no function of $\|\sigma_A\|_1$ alone that recovers $I(A)$. For example, at risk $1/4$ both a BSC with crossover $1/4$ and an erasure channel with erasure probability $1/2$ have $\|\sigma_A\|_1=1/2$, while their informations are respectively $1-h_2(1/4)$ and $1/2$.

## 2. The sharp binary risk--information interval

Assume now that $p=1/2$. Put $r_A(u)=\min\{\eta_A(u),1-\eta_A(u)\}$. Then $e(A)=\mathbb E[r_A(Q_A)]$ and $H(Y\mid Q_A)=\mathbb E[h_2(r_A(Q_A))]$.

**定理 2（sharp balanced binary sandwich）。**

For every finite readout,

$$
\boxed{
1-h_2(e(A))\le I(A)\le 1-2e(A).
}
$$

Both endpoints are sharp.

- Equality on the left holds when the posterior error $r_A$ is constant almost surely. A binary symmetric channel with crossover probability $e(A)$ is an extremizer.
- Equality on the right holds when $r_A$ takes only the values $0$ and $1/2$. An erasure channel is an extremizer.

**证明。** Concavity of $h_2$ gives

$$
\mathbb E h_2(r_A)\le h_2(\mathbb E r_A)=h_2(e(A)),
$$

which is the lower bound on $I$. The chord from $(0,0)$ to $(1/2,1)$ gives $h_2(t)\ge2t$ on $[0,1/2]$, hence $\mathbb E h_2(r_A)\ge2e(A)$ and the upper bound. Constant-error BSC posteriors attain the first equality; posterior errors $0$ and $1/2$ attain the second. $\square$

Equivalently, at fixed information $I$,

$$
\boxed{
 h_2^{-1}(1-I)\le e(A)\le\frac{1-I}{2}
}
$$

with the inverse taken on $[0,1/2]$. Information fixes an interval of task risks, not a task risk.

For a non-balanced prior, the corresponding safe form is

$$
H_2(p)-h_2(e(A))\le I(A)\le H_2(p)-2e(A),
$$

with $e(A)\le\min(p,1-p)$. The balanced statement is the one whose extremizers and endpoint interpretation are symmetric.

**推论 2.1（signed signature as TV and JS）。** In the balanced case, let $P_1$ and $P_0$ be the two conditional laws of $Q_A$ given $Y=1$ and $Y=0$. Then

$$
\|\sigma_A\|_1=\operatorname{TV}(P_1,P_0)=1-2e(A),\qquad
I(A)=\operatorname{JS}_2(P_1,P_0).
$$

Consequently Theorem 2 is the sharp Jensen--Shannon/total-variation interval

$$
1-h_2\!\left(\frac{1-\operatorname{TV}(P_1,P_0)}2\right)\le\operatorname{JS}_2(P_1,P_0)\le\operatorname{TV}(P_1,P_0).
$$

This is the cleanest information-theoretic reading of the FIB signed atom: its $L^1$ cancellation is total variation, while its posterior entropy defect is Jensen--Shannon information.

## 3. Equal information can encode unequal task quality

The sharp endpoints give a parameterized separation rather than a single nuisance example.

**定理 3（BSC/BEC equal-information separation）。**

Let $0<\varepsilon<1/2$. A balanced binary task observed through

- a BSC with crossover probability $\varepsilon$, and
- a BEC with erasure probability $\lambda=h_2(\varepsilon)$

has the same task mutual information,

$$
I_{\mathrm{BSC}}=1-h_2(\varepsilon)
=I_{\mathrm{BEC}},
$$

but risks

$$
 e_{\mathrm{BSC}}=\varepsilon,
\qquad
 e_{\mathrm{BEC}}=\frac{h_2(\varepsilon)}2>\varepsilon.
$$

**证明。** The BSC posterior error is constantly $\varepsilon$. The BEC reveals the label outside an erasure event, so its conditional entropy and error are respectively $\lambda$ and $\lambda/2$. The strict inequality is the strict concavity inequality $h_2(\varepsilon)>2\varepsilon$ for $0<\varepsilon<1/2$. $\square$

At $\varepsilon=1/4$, the common information is approximately $0.188722$ bits, while the risks are $0.25$ and approximately $0.405639$. The two channels realize the lower and upper endpoints of Theorem 2 at the same information level. A finite state model realizes both by coupling $(Y,Q_{\mathrm{BSC}},Q_{\mathrm{BEC}})$ on one finite state space and taking the two channel outputs as two deterministic feature maps. The two coordinates then share one actual implementation rather than merely two unrelated marginal examples.

The same mechanism produces a finite ordering reversal between feature candidates. Start with two parent fibres of mass $80/160$ each. In the first parent, the label fraction is $1/4$; candidate $A$ splits it into two mass-$40/160$ children with positive counts $5$ and $15$. In the second parent, the label fraction is $1/2$; candidate $B$ splits it into two mass-$40/160$ children with positive counts $16$ and $24$. Candidate $A$ has zero risk gain but conditional information gain

$$
\frac12\left[h_2(1/4)-\frac{h_2(1/8)+h_2(3/8)}2\right]
\approx0.031139,
$$

whereas candidate $B$ has risk gain $0.05$ and conditional information gain

$$
\frac12\left[1-h_2(0.6)\right]\approx0.014525.
$$

Thus information-gain ranking chooses $A$ while Bayes-risk ranking chooses $B$.

## 4. Information can increase without reducing zero-one risk

Risk is piecewise affine in the posterior; entropy is strictly concave. This difference survives every finite refinement.

**定理 4（same-side refinement）。**

A refinement can have strictly positive conditional mutual information while leaving Bayes risk unchanged. In a balanced example, take two parent fibres of equal mass with posteriors $1/4$ and $3/4$. Refine the first into equal children with posteriors $0,1/2$ and the second into equal children with posteriors $1/2,1$. Then

$$
 e_{\mathrm{coarse}}=e_{\mathrm{fine}}=1/4,
$$

but

$$
 I_{\mathrm{coarse}}=1-h_2(1/4)<1/2=I_{\mathrm{fine}}.
$$

**证明。** Each parent posterior is the average of its children. On either side of the decision boundary, $r(t)=\min(t,1-t)$ is affine, so the average risk is unchanged. Strict concavity of $h_2$ makes the conditional entropy strictly smaller after the nontrivial split. $\square$

The condition is geometric: a refinement earns zero 0--1 risk gain exactly when every old fibre is split without producing a net cancellation across the decision boundary. Information still rewards confidence sharpening inside one decision half-space.

## 5. Incremental information is a necessary budget for risk improvement

Let $Q_A$ be a deterministic coarsening of $Q_B$, as for $A\subseteq B$. Then $\eta_A=\mathbb E[\eta_B\mid Q_A]$. Let

$$
\Delta e=e(A)-e(B)\ge0,
\qquad
\Delta I=I(Y;Q_B\mid Q_A).
$$

**定理 5（conditional-information risk budget）。**

For every finite binary task and every such refinement,

$$
\boxed{
0\le\Delta e\le\sqrt{\frac{\ln2}{2}\,\Delta I}
}
$$

when $\Delta I$ is measured in bits. Equivalently, in nats,

$$
\Delta I_{\mathrm{nats}}\ge2(\Delta e)^2.
$$

**证明。** Write $r(t)=\min(t,1-t)$. The function $r$ is 1-Lipschitz, hence

$$
\Delta e
=\mathbb E[r(\eta_A)-r(\eta_B)]
\le\mathbb E|\eta_A-\eta_B|.
$$

The posterior conditional-information identity gives

$$
\Delta I_{\mathrm{nats}}
=\mathbb E\,D_{\mathrm{KL}}
\bigl(\operatorname{Bern}(\eta_B)\,\|\,\operatorname{Bern}(\eta_A)\bigr).
$$

Binary Pinsker yields $D_{\mathrm{KL}}\ge2(\eta_B-\eta_A)^2$. Jensen's inequality then gives

$$
\Delta e\le\sqrt{\mathbb E(\eta_B-\eta_A)^2}
\le\sqrt{\Delta I_{\mathrm{nats}}/2}.
$$

If $\eta_A$ is $0$ or $1$ on a fibre, the tower identity $\eta_A=\mathbb E[\eta_B\mid Q_A]$ forces $\eta_B=\eta_A$ almost surely on that fibre, so its KL and posterior-difference contributions are zero. Zero-mass fibres contribute nothing. $\square$

There is no converse of the form $\Delta e\ge\phi(\Delta I)$ with $\phi(t)>0$ for $t>0$: Theorem 4 has positive information gain and zero risk gain. Near the blind balanced posterior, a symmetric split $1/2\pm\delta$ has risk gain $\delta$ but information gain $1-h_2(1/2-\delta)\sim2\delta^2/\ln2$, so the quadratic scale is the correct local order.

## 6. Feature synergy and the task boundary

For independent fair bits $X_1,\ldots,X_n$ and the parity task $Y=\bigoplus_iX_i$, every proper subset readout is independent of $Y$:

$$
I(Y;X_A)=0,\qquad e(A)=1/2\quad(A\subsetneq\{1,\ldots,n\}),
$$

while the full readout satisfies

$$
I(Y;X_1,\ldots,X_n)=1,\qquad e(\{1,\ldots,n\})=0.
$$

Thus all lower-order information probes can miss a pure higher-order escape. This is the information-theoretic counterpart of the FIB XOR interaction. No submodularity, supermodularity, or greedy guarantee for task risk follows from finite refinement alone. Mutual-information submodularity requires extra conditional-independence hypotheses; parity violates them.

A separate distinction is between hidden-state information and task information. If $S=(Y,N)$ with independent nuisance $N$, then observing $N$ can have large $I(S;N)=H(N)$ while $I(Y;N)=0$ and $e(Y\mid N)=e(Y)$. When $H(Y)<H(N)$, observing the task label $Y$ carries less hidden-state information than observing the nuisance $N$, yet it gives zero task risk. Full-state information, representation size, and task information therefore answer different questions.

## 7. White-box interpretation and exact limits

The finite theory suggests a concrete white-box certificate for a task coordinate $d$:

1. expose the fibre mass $m_{d,A}$ and signed mass $\sigma_{d,A}$;
2. report the task posterior entropy and the Bayes-risk signature separately;
3. certify every claimed risk gain by a child-fibre sign cancellation across the task boundary;
4. use conditional mutual information only as a necessary information budget through Theorem 5;
5. test higher-order feature sets, because pairwise information can be zero in a genuinely synergistic relation.

The quantities are task- and measure-dependent. Zero-mass states are invisible to both finite expectations and must not be treated as certified structural absence. A structural escape relation can remain present while its chosen deployment measure assigns it no mass; conversely, a high-information nuisance coordinate can be irrelevant to the target. The theory gives no distribution-free statement about neural training, generalization, calibration, continuous supports, adversarial robustness, or the physical FIB realization.

### 7.1 The recursive five-class readout

For the three-position FIB window, the legal syntax has the five labels `null`, `2`, `3`, `2 5`, and `5`. The information bridge is applied to each label as a separate task coordinate $d$, with its own binary readout $Y_d$, mass $\mu$, and feature family $Q_A$. Thus one obtains five pairs

$$
(e_d(A),I_d(A))\quad(d\in\{\texttt{null},\texttt{2},\texttt{3},\texttt{2 5},\texttt{5}\}).
$$

The label `2 5` may carry genuine joint information even when the singleton coordinates `2` and `5` have zero information about that task, exactly as the parity witness in Section 6. The recursive five-class syntax supplies the candidate coordinates and their legal compositions; it does not identify the joint task law, the deployment mass, or a common vector mutual information. In particular,

$$
\sum_d I_d(A)\;\text{need not equal}\; I((Y_d)_d;Q_A).
$$

The two sides can coincide under extra structure, but equality cannot be assumed without an independence or joint-distribution argument.

The correct white-box report is therefore a five-row task table, each row carrying its signed fibre, risk, information, and higher-order witnesses.

The useful replacement for the slogan “more information means a better model” is the following bounded claim:

$$
\boxed{
\text{Task information is a budget; signed posterior geometry decides whether that budget crosses the task boundary.}
}
$$

The previously known finite escape-risk lattice supplies the geometry. This volume supplies its sharp binary information envelope, its equal-information separation, and its incremental budget law.

## 8. Research status and reusable boundary

The smallest nuisance-versus-target example is already covered by the repository's frozen equal-entropy and target-coverage results. The content here is the parameterized bridge: the signed-mass/posterior identity, the sharp two-sided binary interval with BSC/BEC extremizers, the risk-gain consequence of conditional information, and the finite ranking and synergy witnesses. These statements are finite mathematical claims; they are not Lean-kernel results in this volume.

The strongest reusable boundary is therefore:

$$
\text{MI can certify necessary information expenditure,}
\quad
\text{but only task-relative posterior sign geometry certifies zero-one escape improvement.}
$$

## 追加锚（本行以下为增补区）
