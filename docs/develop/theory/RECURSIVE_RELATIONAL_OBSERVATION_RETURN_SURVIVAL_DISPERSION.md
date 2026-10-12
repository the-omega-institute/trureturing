# Return survival dispersion on one acquired stopped circulation

## 1. The unchanged question and the new necessary relation

The statements below concern complete stopped probability laws and one common acquired circulation. They retain the original source and configuration-loss contract. Their scope is a necessary response relation and a restricted positive gap, rather than a decision of the unrestricted common-flow problem.

Fix one original prior supported on $\{1,2,3\}$, with all three masses positive. The complete common-flow problem is exactly [PAIR, Section 11]: both full endpoint coordinate boxes, both midpoint event means, both depth-3 configuration-loss bounds and both conditional residual equations must hold on the same phase marginals. Its zero-versus-positive decision remains unresolved here.

The new result concerns the probability weight attached to one synthetic noncompleting pair on an actual p-to-suspended edge. If the p emission is $u$ and that edge's suspended emission is $v$, this weight is $(1-u)v$. This is a property of the predictor and its acquired update, not the probability of the actual source returning. Define its mean absolute deviation on the one unweighted acquired edge flow as $D$. For every compatible pair in [PAIR, Definition 11.2], with its original three-depth objective $\mathcal J$,

$$
19\mathcal J+D>\frac9{160000}.
\tag{1.1}
$$

Thus a zero-level pair, if one exists, must have $D>9/160000$. This necessity holds for nonatomic as well as finite atomic pairs. The class in which the synthetic return weight is constant on its entire positive edge support has a positive common gap, even when both emission vectors vary and the actual return changes the p forecast. Its gap is not an unrestricted gap.

The proof gives a joint finite-word response relation before assuming any endpoint calibration. It uses the same stationary acquired path for the complete p words and the suspended event. This distinguishes it from the published constant-suspended-emission separator [HET] and the return-conserved-p-emission restriction [RETURN]. No additional independence between the path weights and completion weights, reversibility, irreducibility, mixing rate or fixed resource budget is assumed.

## 2. Original source, complete words and the one common carrier

**Definition 2.1 (original experiment).** Retain $m=2,d=1,\ell=2,n=4$ and $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$. One hidden $K$ is sampled before the first actual Read from the fixed prior $\mu$. Conditional on that same $K=k$, every paid seed and payload Read is independent, with alpha probability

$$
r_k=\frac{F_{k+1}}{F_{k+3}},\qquad
r_1=a=\frac13,\quad r_2=b=\frac25,\quad r_3=\frac38.
\tag{2.1}
$$

Equal seed pairs are paid rejections; alpha-beta accepts seed 0 and beta-alpha accepts seed 1. In payload phase p, alpha completes marker 0 and beta suspends. At suspension, alpha returns to p and beta completes marker 1. The third record is written before its latch. Fourth completion enters the matching original pendingStop, whose unique Stop delivers once; neither terminal permits Read.

The entire original finite control $C_0$ remains: both seeds, parser, selectors, bare fields, full marker tree, held $B,Q^+,Z$ records, write/latch flags, permissions, completion and Stop delivery. Both seeds, every marker triple, every positive finite seed-rejection history and every positive finite payload-return history are admissible. There is no source reset, new depth, future-event conditioning, extra observation, controller port or post-Stop operation.

Put $t_r=r(1-r)$ and

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta\quad(j\ge0).
$$

The p carrier consists of these finite words and its unique infinite noncompletion word. The suspended carrier consists of beta, all $\alpha w_{j,i}$ and its infinite noncompletion word. The original complete laws are

$$
\begin{aligned}
P_{p,r}(w_{j,0})&=rt_r^j,&
P_{p,r}(w_{j,1})&=(1-r)^2t_r^j,\\
P_{\beta,r}(\beta)&=1-r,&
P_{\beta,r}(\alpha w_{j,i})&=rP_{p,r}(w_{j,i}).
\end{aligned}
\tag{2.2}
$$

Their infinite masses are zero. The current-record renderer $I_c$ retains every future Read and inserts its original record, control, permission, completion and Stop blocks. Its inverse reads the letters back. It preserves complete-law TV and deletion of the next operation with its block [ST, Section 2.1]. The already acquired suspended beta is not a future Read.

At any positive finite actual history $h$, the unchanged target is the rendered posterior mixture with weights proportional to

$$
\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}.
\tag{2.3}
$$

Both counts include every paid rejection and partial parse. These posterior weights are analysis quantities, not runtime inputs. The phase domains are the full original $\mathcal H_p,\mathcal H_\beta$, including all finite fourth-segment returns; $\mathcal H_3$ alone is insufficient.

TV is the event-supremum convention, or half the countable $\ell^1$ distance on these carriers. An original observer has a fixed finite COMPLETE carrier, source-independent initialization and fixed time-homogeneous source-independent acquired-letter kernels. At every retained cut its decoder is the complete future generated by its synthetic emission rule and these very same update kernels. It reads its actual configuration only. The posterior, an analysis probability row, elapsed history and a continuous descriptor are not additional runtime inputs.

For a positive actual history $h$, let $\zeta_h$ be its actual configuration row, $D_z$ the own complete rendered law from configuration $z$, and $T_h$ the rendered posterior target in (2.3). The two risk orders are

$$
e_{\mathrm{conf}}(h)=\sum_z\zeta_h(z)\operatorname{TV}(D_z,T_h),
\qquad
e_{\mathrm{law}}(h)=\operatorname{TV}\left(\sum_z\zeta_h(z)D_z,T_h\right),
$$

$$
R_{j,s}(M)=\sup_{h\in\mathcal H_s}e_j(h),
\qquad j\in\{\mathrm{conf},\mathrm{law}\},\quad s\in\{p,\beta\}.
$$

Configuration loss therefore takes TV before averaging over configurations. A law-order or actual-history-average bound cannot replace it. COMPLETE includes $C_0$, installed tables and numerical representation, the program, selectors, active labels, all persistent randomness, sampler service states, workspace and output indices. Label count alone is not COMPLETE. Its separate phase configuration radii are supplied by [ST; CLIP]:

$$
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750}.
\tag{2.4}
$$

The terminal-only radii $13/266,9/266$ are different quantities. Actual-history-average loss is also a different objective.

**Definition 2.2 (compatible pair, reused).** Use the complete carriers $\Omega_p,\Omega_\beta$ in Definition 2.1. With $\lambda=4/15$, set

$$
\begin{aligned}
T_p(j)&=\{w_{n,i}:n\ge j,\ i\in\{0,1\}\}\cup\{\infty_p\},\\
T_\beta(j)&=\{\alpha w_{n,i}:n\ge j,\ i\in\{0,1\}\}\cup\{\infty_\beta\},\\
\mathcal K_p&=\{Q\in\mathcal P(\Omega_p):a\le Q(\alpha)\le b,
                         \ Q(T_p(j))\le\lambda^j\text{ for all }j\ge0\},\\
\mathcal K_\beta&=\{W\in\mathcal P(\Omega_\beta):a\le1-W(\beta)\le b,
                         \ W(T_\beta(j))\le b\lambda^j\text{ for all }j\ge0\}.
\end{aligned}
$$

These are exactly [PAIR, equations (11.1)–(11.2)]: normalized probability laws with the complete-law TV topology. The tail bounds force their infinite masses to zero, without deleting the infinite outcomes. For a p descriptor $Q$ and a suspended descriptor $W$, put

$$
u(Q)=Q(\alpha),\quad U(Q)=1-u(Q),\quad
v(W)=1-W(\beta),\qquad a\le u,v\le b.
$$

For measurable sets on the opposite complete carriers, define the normalized residuals

$$
\mathcal R_B(Q)(E)=\frac{Q(\beta E)}{U(Q)},\qquad
\mathcal R_A(W)(E)=\frac{W(\alpha E)}{v(W)}.
$$

Both are full probability laws; prefixing includes the corresponding infinite outcome and deletes exactly the next original operation block through $I_c$. Arbitrary descriptors need not have their residual in the opposite $\mathcal K$. Compatibility supplies that residual as a barycentre.

There are Borel probability flows $\Gamma_B$ on $\mathcal K_p\times\mathcal K_\beta$ and $\Gamma_A$ on the reversed product, with

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta.
$$

Their conditional residual equalities are

$$
\mathcal R_B(Q)=\int W\,B(Q,dW),\qquad
\mathcal R_A(W)=\int Q\,A(W,dQ)
\tag{2.5}
$$

almost surely, where $B,A$ are disintegrations of these very flows. The original equations condition on the entire input descriptor. Conditioning merely on an emission or on a residual projection is not substituted. In particular,

$$
\begin{aligned}
Q&=u(Q)\delta_\alpha+U(Q)\beta\int W\,B(Q,dW),\\
W&=(1-v(W))\delta_\beta+v(W)\alpha\int Q\,A(W,dQ),\\
\nu_pB&=\nu_\beta,\qquad \nu_\beta A=\nu_p.
\end{aligned}
\tag{2.6}
$$

Both marginals are unweighted acquired marginals. The factors $U,v$ occur in synthetic word generation only. All laws retain their infinite outcomes, of mass zero under the supplied uniform tail bounds. Disintegration and countable atom tests are supplied in [PAIR]; no new martingale-coupling theorem is claimed.

**Definition 2.3 (return weight and its dispersion).** On $\Gamma_B$ define

$$
Z(Q,W)=U(Q)v(W),\qquad
c=\int Z\,d\Gamma_B,\qquad
D=\int|Z-c|\,d\Gamma_B.
\tag{2.7}
$$

Always

$$
\frac15\le Z,c\le\lambda=\frac4{15}.
\tag{2.8}
$$

The constant-return-weight subfamily means $D=0$, equivalently $Z=c$ almost surely on this edge flow. It does not mean that the average return probability is constant merely after averaging the $B$ row. Nor does it mean that each recurrent component has its own possibly different constant. These weaker conditions are not covered by the subfamily conclusion.

For a finite table this statistic is exactly

$$
c=\sum_{x,y}\pi_xB_{xy}(1-u_x)v_y,
\qquad
D=\sum_{x,y}\pi_xB_{xy}|(1-u_x)v_y-c|.
\tag{2.9}
$$

If $D=0$, the synthetic return matrix satisfies

$$
\operatorname{diag}(1-u)B\operatorname{diag}(v)A=cBA.
\tag{2.10}
$$

The actual kernel is still $BA$. Equation (2.10) is a consequence of the edge condition, not a replacement for it.

Keep the complete configuration losses

$$
\mathcal L_p(T)=\int\operatorname{TV}(Q,T)\,d\nu_p,
\qquad
\mathcal L_\beta(T)=\int\operatorname{TV}(W,T)\,d\nu_\beta,
$$

and the unchanged objective

$$
\mathcal J=\max_{s\in\{p,\beta\},\ k\in\{1,2,3\}}
\bigl\{\mathcal L_s(P_{s,r_k})-\rho_s\bigr\}.
\tag{2.11}
$$

The positive installed masses do not disappear from the source. [CLIP, Proposition 2.3; PAID, Lemma 14.1] justify the pure-target supremum using positive finite paid histories in that one prior. They do not supply free pure-source experiments.

**Definition 2.4 (the retained zero face).** Let $j_c=\min_{\mathfrak C}\mathcal J$, with the supplied compact domain in Definition 2.2. The original question is whether $j_c=0$ or $j_c>0$. At zero level, and conversely under compatibility, its endpoint constraints are the complete coordinate boxes

$$
P_{s,a}(\omega)\wedge P_{s,b}(\omega)
\le D_s(\omega)\le
P_{s,a}(\omega)\vee P_{s,b}(\omega)
\quad\text{for every }\omega\in\Omega_s,\quad\nu_s\text{-almost surely},
$$

where $D_p=Q,D_\beta=W$, together with the two endpoint-event midpoint means specified in (3.1). They must hold alongside

$$
\mathcal L_p(P_{p,3/8})\le\rho_p,\qquad
\mathcal L_\beta(P_{\beta,3/8})\le\rho_\beta.
$$

The coordinate boxes include every completed word and the infinite outcome. All these constraints belong to the same unweighted phase marginals and both full-descriptor residual equations. Three installed depths do not imply finitely many forecast descriptors, and the original source parameter $n=4$ is neither a descriptor-support bound nor a COMPLETE cap. Theorem 4.1 uses fewer risk hypotheses to prove a necessary relation; the original decision retains all of them.

## 3. A joint response envelope on the descriptor analysis path

Define the supplied complete events and constants

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\},
$$

$$
C=\frac{11758471}{22781250},\qquad
H=\frac{5261}{6750},\qquad
q_* = P_{p,b}(w_{3,1})=\frac{1944}{390625}.
\tag{3.1}
$$

Here $C,H$ are the endpoint midpoint means. They are fixed by the original complete laws. For a general compatible pair put

$$
P=\int Q(E_p)\,d\nu_p,\quad
T=\int W(E_\beta)\,d\nu_\beta,\quad
q=\int Q(w_{3,1})\,d\nu_p,
\quad S(c)=1+c+c^2,
$$

$$
\begin{aligned}
F(c,x)&=1+c-\frac52c(1+c)
 \left(\frac{19}{15}-c-\frac{x}{S(c)}\right),\\
G(c,x)&=\frac{xc^3}{S(c)}.
\end{aligned}
\tag{3.2}
$$

**Theorem 3.1 (same-flow return-weight response).** Every compatible pair of Definition 2.2 satisfies

$$
T\ge F(c,P)-2D,
\qquad
q\ge G(c,P)-\frac D9.
\tag{3.3}
$$

These inequalities require neither endpoint boxes nor configuration-loss bounds. The two responses, $c$ and $D$ all belong to one pair of flows.

Proof. Start an alternating acquired analysis chain with $Q_0\sim\nu_p$ and use the kernels from (2.5):

$$
Q_0\xrightarrow{B}W_0\xrightarrow{A}Q_1
\xrightarrow{B}W_1\xrightarrow{A}Q_2\longrightarrow\cdots.
$$

The shared marginals make every finite window stationary under a shift of one full pair. This is the Markov analysis chain formed from the descriptor disintegrations of these two acquired law flows. Its finite-window distribution is independent of almost-everywhere choices of disintegration versions. It is not the original source conditioned on infinite noncompletion, an available runtime clock, or an assertion that the original hidden labels are Markov after projection to descriptors. Put

$$
U_i=1-u(Q_i),\quad V_i=v(W_i),\quad
Z_i=U_iV_i,\quad g_i=U_i(1-V_i),\quad m=\mathbb E U_0.
$$

In this notation $\mathbb E Z_i=c$, $\mathbb E|Z_i-c|=D$ and $0\le g_i\le4/9$. Iterating the conditional full-law recursions gives

$$
\int Q(w_{j,1})\,d\nu_p
 =\mathbb E\left[\left(\prod_{i=0}^{j-1}Z_i\right)g_j\right],
\qquad
T=\mathbb E[1-V_0+V_0g_1].
\tag{3.4}
$$

For each fixed finite word, all intermediate laws and kernels here are those in (2.6). Null exceptional inputs remain null along every finite stationary path. Thus (3.4) uses both conditional residual equations, not just their unconditioned barycentres. The equality follows by recursive substitution of the own complete laws. It requires no identification of the analysis chain's three-stage join with a particular original observer's hidden return coupling.

Since $Z_i,c\le\lambda$, product telescoping yields, for $j\ge1$,

$$
\left|\prod_{i=0}^{j-1}Z_i-c^j\right|
\le\lambda^{j-1}\sum_{i=0}^{j-1}|Z_i-c|.
$$

Multiplication by $g_j\le4/9$ and stationarity give

$$
\left|\int Q(w_{j,1})\,d\nu_p-c^j\mathbb E g_0\right|
\le\frac49j\lambda^{j-1}D.
\tag{3.5}
$$

No independence between the weight errors and $g_j$ is used. Also $g_0=U_0-Z_0$, so $\mathbb E g_0=m-c$ exactly. Summing (3.5) for $j=1,2$ and keeping $j=0$ unchanged gives

$$
|P-S(c)(m-c)|\le\frac{92}{135}D.
\tag{3.6}
$$

At $j=3$ the coefficient in (3.5) is $64/675$. Consequently

$$
q\ge \frac{Pc^3}{S(c)}
 -\left(\frac{92c^3}{135S(c)}+\frac{64}{675}\right)D.
$$

Using $c\le4/15$ and $S(c)\ge1$, the coefficient is at most

$$
\frac{49088}{455625}<\frac19,
$$

which proves the second inequality in (3.3).

For the suspended event, write $\delta_i=Z_i-c$. Since $V_i=(c+\delta_i)/U_i$ and $g_1=U_1-c-\delta_1$, the second identity in (3.4) becomes

$$
\begin{aligned}
T={}&1-c(1+c)\mathbb E(U_0^{-1})
 +c\mathbb E(U_1/U_0)\\
&-\mathbb E\left[\delta_0\frac{1+c-U_1}{U_0}\right]
 -\mathbb E[V_0\delta_1].
\end{aligned}
\tag{3.7}
$$

The first line has deliberately retained the actual ratio $U_1/U_0$. Its removal by a conditional-stationarity claim would be unjustified. Instead, bounded positive $U_0,U_1$ have the same marginal, so

$$
\mathbb E\log(U_1/U_0)=0,
\qquad \mathbb E(U_1/U_0)\ge1
\tag{3.8}
$$

by Jensen's inequality. The error coefficients obey

$$
0\le\frac{1+c-U_1}{U_0}\le\frac{10}{9},
\qquad 0\le V_0\le\frac25.
$$

Thus the total absolute error in the second line of (3.7) is at most $68D/45$. On $[L_0,H_0]=[3/5,2/3]$, the reciprocal chord gives

$$
\frac1t\le\frac{L_0+H_0-t}{L_0H_0},\qquad
\mathbb E(U_0^{-1})\le\frac52\left(\frac{19}{15}-m\right).
\tag{3.9}
$$

Combine (3.7)–(3.9), then use the lower bound for $m$ from (3.6). This yields

$$
T\ge F(c,P)
 -\left(\frac{68}{45}
  +\frac{5c(1+c)}{2S(c)}\frac{92}{135}\right)D.
$$

The function $c(1+c)/S(c)=1-1/S(c)$ increases with $c$. On (2.8),

$$
\frac{5c(1+c)}{2S(c)}\le\frac{190}{301}<\frac23.
$$

The last error coefficient is therefore at most $796/405<2$. This proves the first inequality in (3.3). All expectations are bounded, and all products refer to one stationary acquired chain. ∎

The source-specific content is the paired response (3.3), including its shared return-weight parameter. Product telescoping, Jensen's inequality and the reciprocal chord are mature tools consumed by that relation; they are not separately new general inequalities.

**Definition 3.2 (signed response charges on the same path).** On the chain in the proof of Theorem 3.1 put, for $j=1,2,3$,

$$
A_j=\mathbb E\left[
 \left(\prod_{i=0}^{j-1}Z_i-c^j\right)g_j\right],
\qquad A_P=A_1+A_2,
$$

$$
\begin{aligned}
J_U&=\mathbb E\frac{(U_0-3/5)(2/3-U_0)}{(2/5)U_0},\\
J_R&=\mathbb E(U_1/U_0)-1,\\
E_\beta^{\rm wt}
&=\mathbb E\left[\delta_0\frac{1+c-U_1}{U_0}\right]
  +\mathbb E[V_0\delta_1],\\
K_\beta&=E_\beta^{\rm wt}
  +\frac{5c(1+c)}{2S(c)}A_P,\\
K_3&=\frac{c^3}{S(c)}A_P-A_3.
\end{aligned}
\tag{3.10}
$$

Both $J_U$ and $J_R$ are nonnegative. The other quantities are signed, including $A_j$; replacing them by independently chosen moments changes the relation. These are finite-window functions of the descriptor kernels $B,A$ and their common marginal on the chain used in (3.4). They are not online counters or observations, and they are not defined by selecting an arbitrary hidden-label coupling with the same two pairwise law flows.

**Proposition 3.3 (exact signed paired balance).** Every compatible pair satisfies the exact identities

$$
\begin{aligned}
T-F(c,P)&=c(1+c)J_U+cJ_R-K_\beta,\\
q-G(c,P)&=-K_3.
\end{aligned}
\tag{3.11}
$$

Proof. Equation (3.4) gives $P=S(c)(m-c)+A_P$ and $q=c^3(m-c)+A_3$. The reciprocal chord difference is exactly

$$
\frac{19/15-t}{2/5}-\frac1t
=\frac{(t-3/5)(2/3-t)}{(2/5)t}.
$$

Hence $\mathbb E(U_0^{-1})=(5/2)(19/15-m)-J_U$. Substitute this into (3.7), retain $\mathbb E(U_1/U_0)=1+J_R$, and use $m=c+(P-A_P)/S(c)$. The first identity in (3.11) follows. The formula for $q$ gives the second. Nonnegativity of $J_U$ follows pointwise; that of $J_R$ is (3.8). No signed term is bounded or discarded in these identities. ∎

For example $A_1=\mathbb E[(Z_0-c)g_1]$ is a covariance. Higher $A_j$ also retain products of deviations and their correlation with the terminal completion weight. Dispersion alone does not determine their signs. Proposition 3.3 is used below to locate the signed obstruction that the unsigned estimate in Theorem 3.1 can leave open.

## 4. An evaluated endpoint separator with a free dispersion coordinate

**Theorem 4.1 (configuration excess versus return-weight dispersion).** For every compatible pair with the unchanged objective (2.11),

$$
19\mathcal J+D>\kappa_0:=\frac9{160000}.
\tag{4.1}
$$

The same inequality holds if $\mathcal J$ is replaced by the maximum of the four endpoint configuration excesses. The original three-depth objective remains (2.11); this stronger endpoint-only necessity does not discharge either depth-3 loss condition.

Proof. Write $e=\mathcal J\ge0$. The supplied endpoint events and their TV distances imply

$$
|P-C|\le e,\qquad |T-H|\le e.
\tag{4.2}
$$

For example, $P_{p,a}(E_p)-P\le\mathcal L_p(P_{p,a})\le\rho_p+e$ and $P-P_{p,b}(E_p)\le\rho_p+e$ give the first bound. The suspended bound is identical on its own event and same marginal.

The supplied coordinate triangle identity [CLIP, equation (3.6); PAIR, equation (11.29)] gives

$$
\int\sum_\omega
\operatorname{dist}\bigl(Q(\omega),
 [P_{p,a}(\omega)\wedge P_{p,b}(\omega),
  P_{p,a}(\omega)\vee P_{p,b}(\omega)]\bigr)\,d\nu_p
\le2e.
\tag{4.3}
$$

This includes the infinite outcome. At $w_{3,1}$ the larger endpoint is $b$, so (4.3) implies $q\le q_*+2e$. Configuration TV is necessary for this rowwise violation bound; a bound only on the averaged law is not its stated premise.

The $x$ coefficients in (3.2) obey

$$
0\le\partial_xF(c,x)<\frac23,
\qquad 0\le\partial_xG(c,x)=\frac{c^3}{S(c)}<\frac1{50}.
$$

Apply Theorem 3.1 and (4.2)–(4.3):

$$
F(c,C)\le H+\frac53e+2D,
\qquad
G(c,C)\le q_*+\frac{101}{50}e+\frac D9.
\tag{4.4}
$$

The first function in (4.4) strictly decreases with $c$ on $[1/5,4/15]$, and the second strictly increases. In detail,

$$
\partial_cF(c,C)
=-\frac{13}{6}-\frac43c+\frac{15}{2}c^2
 +\frac52C\frac{1+2c}{S(c)^2}.
$$

Use $C<13/25$, $S(c)\ge31/25$ and $1+2c\le23/15$. Dropping the negative linear term bounds this derivative above by

$$
-\frac{13}{6}+\frac{15}{2}\left(\frac4{15}\right)^2
 +\frac52\frac{13}{25}\frac{23}{15}\left(\frac{25}{31}\right)^2
=-\frac{1619}{4805}<0.
\tag{4.5}
$$

Also $\partial_cG(c,C)=Cc^2(3+2c+c^2)/S(c)^2>0$.

At the single rational cut $c_*=463/2000$, exact substitution gives

$$
F(c_*,C)-H-\frac1{2000}
=\frac{240148126954349}{3997150934400000000}>0,
$$

$$
G(c_*,C)-q_*-\frac1{160000}
=\frac{229682039051}{1873664500500000000}>0.
\tag{4.6}
$$

If $c\le c_*$, (4.4)–(4.6) imply $(5/3)e+2D>1/2000$, hence $(5/6)e+D>1/4000>9/160000$. If $c\ge c_*$, they imply $(101/50)e+D/9>1/160000$, hence $(909/50)e+D>9/160000$. Since $19>909/50$ and $e\ge0$, both cases give (4.1). They include every boundary value and exhaust (2.8). The proof used only the endpoint loss bounds, proving the last assertion as well. ∎

The numerical cut evaluates a newly derived response obstruction. It is not a retuning of the constant-suspended-emission or conserved-p-emission inequalities. Its dispersion coordinate measures an edge weight, rather than either emission's range or its increment on a return.

## 5. What is excluded inside the compact original problem

**Corollary 5.1 (zero-level survival cannot concentrate).** A compatible pair satisfying both full endpoint boxes, both midpoint means and both original depth-3 configuration bounds must satisfy

$$
D>\kappa_0.
\tag{5.1}
$$

For any sequence of compatible pairs whose original objectives tend to zero,

$$
\liminf_nD_n\ge\kappa_0.
\tag{5.2}
$$

Proof. The complete boxes, midpoint means and supported losses are the zero-level conditions of [PAIR, Section 11.8]. Both residual equations and the shared marginals remain part of compatibility. Thus $\mathcal J=0$, and (5.1) follows from Theorem 4.1. The same inequality gives $D_n>\kappa_0-19\mathcal J_n$, proving (5.2). ∎

**Corollary 5.2 (a positive evaluated gap on a closed subfamily).** Put

$$
\mathfrak C_d=\{(\Gamma_B,\Gamma_A)\in\mathfrak C:D\le d\},\qquad
j_d=\min_{\mathfrak C_d}\mathcal J\quad(d\ge0).
$$

These domains are nonempty and compact. They satisfy

$$
j_d\ge\max\left\{0,\frac{\kappa_0-d}{19}\right\},
\qquad
j_0\ge\frac9{3040000}>0.
\tag{5.3}
$$

Proof. On the compact law products, $Z$ is continuous and bounded. Under weak convergence of $\Gamma_B$, its mean $c$ converges. The uniform bound $\bigl||Z-c_n|-|Z-c|\bigr|\le|c_n-c|$ then proves continuity of $D$. Hence $\mathfrak C_d$ is closed in the compact domain supplied by [PAIR, Lemma 11.3]. A singleton generator with $u=v=a$ belongs to every $\mathfrak C_d$, proving nonemptiness. The same supplied lower semicontinuity of $\mathcal J$ gives the minimum. Equation (5.3) follows from Theorem 4.1 and nonnegativity. ∎

This class allows arbitrary nonconstant suspended emissions. Its condition is a restriction on the predictor's actual edge flow. It changes neither the source nor the risk objective. It is nevertheless a proper restricted observer problem: a positive $j_0$ does not prove $j_c>0$ on all of $\mathfrak C$.

In particular, constancy separately on recurrent components is not constancy on the entire positive edge support. The fair native endpoint-tag observer already has different return weights $2/9$ and $6/25$ on its two components. The corollary does not exclude that supplied two-depth attainer, and does not prove a separator for the componentwise-constant class.

**Corollary 5.3 (a zero pair requires one of two signed correlations).** At a zero-level compatible pair for the unchanged three-depth problem, the charges in (3.10) satisfy at least one of

$$
K_\beta>\frac1{2000},\qquad
K_3>\frac1{160000}.
\tag{5.4}
$$

More precisely, $c\le463/2000$ forces the first inequality and $c\ge463/2000$ forces the second. These are conditions on one joint path, not on two separately optimized product envelopes.

Proof. The zero face gives $P=C$, $T=H$ and $q\le q_*$. If $c\le c_*$, monotonicity and (4.6) give $F(c,C)-H>1/2000$. From the first exact identity in (3.11),

$$
K_\beta=F(c,C)-H+c(1+c)J_U+cJ_R>\frac1{2000},
$$

since both defects are nonnegative. If $c\ge c_*$, the second identity and (4.6) give $K_3=G(c,C)-q\ge G(c_*,C)-q_*>1/160000$. The two cases include equality at the cut. The full depth-3 losses are retained as hypotheses of the zero-level problem, but are not inferred from this necessary correlation alternative. ∎

The signed condition explains why a broad claim based only on nonzero emission ranges would fail. In the lower-$c$ regime the suspended response needs a positive weighted cancellation large enough to overcome two nonnegative balance defects. In the higher-$c$ regime the third-return completion needs a deficit relative to the common geometric reference. The same word coordinates and kernels must supply that cancellation or deficit while retaining both complete phase losses. This corollary is not a proof that either mechanism is impossible.

## 6. A full original-observer consequence with explicit clipping

An original observer may have emissions outside $[a,b]$, zero or unit emissions, transient configurations and noncompletion mass. Its direct return-weight statistic need not obey the regular bounds used in Theorem 3.1. The following statement specifies the analysis statistic that the supplied clipping comparison actually controls.

**Definition 6.1 (clipped edge span on the actual held-record fibre).** Use the original seed-1, marker-100 fibre of [PAIR, equations (1.3)–(1.4)]. Let $\mathcal E_B^*(M)$ contain every original p-to-suspended edge $(x,y)$ with positive acquired-beta transition probability from a p configuration reachable after a positive finite actual history on that fibre. The successor is also reachable, since the actual beta probability is positive at every supported depth. Write the original next-alpha emissions as $u_x,v_y$, and define

$$
\widehat u_x=[u_x]_{[a,b]},\qquad
\widehat v_y=[v_y]_{[a,b]},\qquad
\widehat z_{xy}=(1-\widehat u_x)\widehat v_y,
$$

$$
\mathcal S(M)=
\max_{(x,y)\in\mathcal E_B^*(M)}\widehat z_{xy}
-\min_{(x,y)\in\mathcal E_B^*(M)}\widehat z_{xy}.
\tag{6.1}
$$

The finite nonempty edge set is a semantic analysis set; it is not a new acquisition or controller port. Clipping in (6.1) is part of the definition. A claim about the span of the unmodified products would require another argument.

**Theorem 6.2 (original risk versus clipped return-weight span).** Every original finite COMPLETE observer on the fixed positive three-depth prior satisfies

$$
\frac{1159}{11}e(M)+\frac{\mathcal S(M)}2>\kappa_0,
\qquad
e(M)=\max_s\{R_{\mathrm{conf},s}(M)-\rho_s\}.
\tag{6.2}
$$

Consequently the original class with $\mathcal S(M)=0$ has

$$
e(M)>\frac{99}{185440000},\qquad
\inf_Me(M)\ge\frac{99}{185440000}.
\tag{6.3}
$$

An exact original common attainer must have $\mathcal S(M)>9/80000$. Every vanishing-excess sequence has $\liminf\mathcal S(M_n)\ge9/80000$.

Proof. Apply the initialized common paid-history extraction [PAID, Lemma 14.1] on that one fibre. It supplies the original acquired kernels and common rows $\pi B=\tau$, $\tau A=\pi$, with both supported pure-target configuration losses no greater than the corresponding original risks. Every positive stationary label and every positive edge from it belongs to Definition 6.1's reachable set. The extraction begins with the original source-independent initialization and paid histories, not a substituted stationary source.

Delete only zero-row labels by the supplied support-closed rule. Clip both emissions, retain these very kernels and rows, and regenerate both complete laws using them. Put $\varepsilon_s=R_{\mathrm{conf},s}(M)-\rho_s\ge0$ and $\widehat\varepsilon_s=\max_{k\in\{1,2,3\}}\widehat{\mathcal L}_s(P_{s,r_k})-\rho_s$, with $\widehat{\mathcal L}_s$ denoting the clipped table's configuration loss and $\widehat e=\max_s\widehat\varepsilon_s$. Explicitly that loss is $\sum_x\pi_x\operatorname{TV}(\widehat Q_x,P_{p,r_k})$ or $\sum_y\tau_y\operatorname{TV}(\widehat W_y,P_{\beta,r_k})$.

The endpoint coordinate identity on the extracted rows gives $\pi|u-\widehat u|\le2\varepsilon_p$ and $\tau|v-\widehat v|\le2\varepsilon_\beta$. The clipping coupling in [CLIP, equations (3.6)–(3.10)] applies directly to this closed stationary support, as also recorded in [HET, Section 2]. The clipped synthetic return kernel is bounded entrywise by $(4/15)BA$ and $\pi BA=\pi$. Thus the average complete-law changes are at most $(30\varepsilon_p+20\varepsilon_\beta)/11$ at p and $(12\varepsilon_p+30\varepsilon_\beta)/11$ at suspension, including any old noncompletion mass. Adding the extracted pure-target risk bounds gives

$$
\widehat\varepsilon_p\le\frac{41\varepsilon_p+20\varepsilon_\beta}{11},
\qquad
\widehat\varepsilon_\beta\le\frac{12\varepsilon_p+41\varepsilon_\beta}{11},
\quad
\widehat e\le\frac{61}{11}e(M).
\tag{6.4}
$$

This is one regular table with its own same-update laws. Its return weight uses exactly the clipped products in (6.1). If a scalar lies in an interval of width $s$, its mean absolute deviation is at most $s/2$, by the chord bound for distance from its mean. Thus this table has $\widehat D\le\mathcal S(M)/2$. Embed its two acquired flows into $\mathfrak C$ by [PAIR, equation (11.24)] and apply Theorem 4.1:

$$
\kappa_0<19\widehat e+\widehat D
\le\frac{1159}{11}e(M)+\frac{\mathcal S(M)}2.
$$

This proves (6.2); its remaining consequences follow by setting $\mathcal S=0$, setting $e=0$, or taking a lower limit, respectively. ∎

The conclusion concerns the original full-history risks and an explicitly clipped statistic on original reachable edges. It supplies no clipping-preservation theorem for an unmodified constant return product outside the regular interval. It assumes no hard marginalized-defect budget, and the comparison preserves neither a prescribed COMPLETE cap nor a total-resource allocation. Original transient configurations and every positive paid history remain in the original suprema.

## 7. A lawful nonconstant-emission member of the excluded class

**Proposition 7.1 (the new structural class is not vacuous).** There is one original-domain finite rational observer with constant return weight on all fourth-segment p-to-suspended edges, nonconstant emissions at both phases, positive acquired-return p-emission variation, positive complete-law return motion, positive alpha-edge decrease, distinct indexed paired-event readouts, nonnative acquired p residuals, and neither acquired interface a complete redraw.

Proof. On every original record fibre use two p labels and two suspended labels, with

$$
\pi=\tau=(1/2,1/2),\qquad
B=I,\qquad A=\begin{pmatrix}0&1\\1&0\end{pmatrix},
$$

$$
u_0=\frac13,\quad u_1=\frac25,\qquad
v_0=\frac7{20},\quad v_1=\frac7{18},\qquad c=\frac7{30}.
\tag{7.1}
$$

Both acquired flows preserve the fair rows. On the two positive $B$ edges, $(1-u_i)v_i=c$. Both suspended emissions lie strictly inside $(a,b)$ and are distinct, while $A$ changes the p emission by $1/15$ on every return. Put

$$
g_0=\frac{13}{30},\qquad g_1=\frac{11}{30}.
$$

The same-update complete p laws are explicitly

$$
Q_i(w_{j,0})=c^ju_{i+j\bmod2},\qquad
Q_i(w_{j,1})=c^jg_{i+j\bmod2},
$$

$$
W_i=(1-v_i)\delta_\beta+v_i\alpha Q_{1-i}.
\tag{7.2}
$$

At every $j$, the two p marker masses sum to $c^j(1-c)$. Summing the geometric series proves normalization and zero infinite mass; suspension then normalizes as well. These are laws of the one installed generator, not independently selected descriptors.

Complete-law return motion is at least $|Q_0(\alpha)-Q_1(\alpha)|=1/15$. On the suspended alpha edges, the two next-alpha changes are $u_1-v_0=1/20$ and $u_0-v_1=-1/18$. The expected decrease is therefore $1/36>0$. The mean suspended interior tent mass is $1/72>0$.

The p-event readout difference is

$$
Q_0(E_p)-Q_1(E_p)
=\frac1{15}(1-c+c^2)=\frac{739}{13500}>0.
$$

The suspended-event readouts are $467/600$ and $421/540$, whose difference in the latter direction is $7/5400>0$. Both acquired kernels have different deterministic rows; neither is a row-independent complete redraw.

Finally put $q_j=Q_0(w_{j,0})$. Then

$$
q_1^2-q_0q_2=c^2(b^2-a^2)=\frac{539}{202500}>0.
\tag{7.3}
$$

For any Borel native stopped-p mixture on $[a,b]$, these coordinates have the form $q_j=\int r[r(1-r)]^j\,d\zeta(r)$ and satisfy $q_1^2\le q_0q_2$ by Cauchy–Schwarz. Thus $Q_0$ is nonnative. Since an actual alpha edge from suspended label 1 has residual $Q_0$, the table does not belong to the class where every acquired p residual is native. The moment test is a mature way to locate this example, not a new general moment theorem. ∎

The example is not near-optimal and is not offered as a zero-level witness. Its role is to show that the newly excluded class contains nonconstant suspended emissions and lies outside the constant-suspension, return-conserved-p-emission, all-native-acquired-residual and complete-redraw structural classes. Positive values of previously necessary statistics are not claimed to jointly suffice for calibration.

**Proposition 7.2 (finite atomic and represented original realization).** The table (7.1) has a finite exact rational same-update implementation on the full original source and control, with all retained and service states charged to COMPLETE.

Proof. Invoke the original product realization [PAID, Lemma 2.1.1] with the table (7.1). Before the third latch retain the full $C_0$ and use fair synthesis. In the same original update, perform the third record write and latch first, then sample the source-independent fair private label. Use $B$ after actual p-beta and $A$ after actual suspended-alpha; use these same updates in synthetic generation. Completion clears private labels and enters precisely the original pendingStop, whose only legal Stop gives original delivery. Induction over operations preserves both seeds, every marker and held record, all paid rejections, all finite returns and all permissions on every original positive history. The actual label rows are $\pi,\tau$ throughout the fourth segment.

The deterministic acquired kernels need no random row service. All stochastic emission entries have common denominator $180$. Draw an eight-bit fair candidate, reject values at least $180$, and return alpha if its accepted value is below the threshold. The thresholds for $u_0,u_1,v_0,v_1$ are $60,72,63,70$; the fair latch can use one fresh bit directly. Accepted values are exactly uniform on $0,\ldots,179$ and each trial has positive acceptance probability, so this finite rejection service terminates almost surely and implements the exact rational probabilities. There is no retained attempt counter. Candidate bits, cursors, thresholds, selector, program, output fields and every service microstate are charged. Internal microstates carry the conditional continuation of that same service program and create no extra actual source-query cut or permission.

The two p laws and two suspended laws in (7.2), with their finite acquired edges, provide explicit finite atomic flow measures by [PAIR, equation (11.24)]. The represented samplers discharge the numerical condition for this example; no sampler for an arbitrary real atomic witness is inferred. Arbitrarily long source rejections, legal returns, synthetic words and internal rejection attempts still have no finite worst-case total-time or output-length bound. Physical source preparation, source Reads, random bits, computation, retained configuration and synthesis remain separate accounts. ∎

## 8. Source correspondence, literature and the remaining mathematical decision

**Mathematical citation 8.1 (covered supplies and the actual increment).** Repository sources below are taken at the immutable revision `a58c24900650d4a0b6022c5e2cf76f5f6f2f8271`. [PAIR, Section 11] supplies the normalized compact carriers, descriptor-conditioned residual equations, common marginals, all-shape regeneration, original infimum comparison, finite atomicity and represented-sampler boundary. [ST; CLIP; PAID] supply the original laws, current-record renderer, radii, endpoint events and coordinate identity, positive paid-history exposure, clipping and original product realization. These are credited suppliers, not new phase minima or new realization theorems.

The increment is Theorem 3.1's joint complete-word response controlled by dispersion of the actual edge's synthetic return weight, its evaluated separator in Theorem 4.1, the exact signed alternative in Corollary 5.3, and the clipped-span transfer in Theorem 6.2. The proof keeps the actual ratio $U_1/U_0$ until stationary Jensen and combines it with the exact identity $\mathbb E g_0=m-c$. It does not optimize an independent suspended marginal, normalize a killed kernel into a different actual source, or condition the original source on future completion. The rational example separates the resulting class from the published restrictions. The constants are sufficient and no sharpness claim is made.

[HET] assumes one constant suspended emission and retains arbitrary acquired kernels; its proof reduces to products of p emission complements. Here both emissions can vary, and the flat case fixes their product on the actual $B$ edge. [RETURN, Sections 9–10] controls p-emission changes across an actual full return; (2.7) instead concerns the p and suspended emissions on the first half of that return. The example has positive values of both supplied motion and emission-change statistics while its return-weight dispersion is zero. The two restrictions have different consumers and neither is substituted for the other.

[RETURN, Proposition 11.9, equations (11.34)–(11.37)] supplies a sharper distinction: two represented tables have identical full directional law flows and all-target phase configuration losses, but different actual three-stage law measures $\Xi$ and different return motion. Their conditionally independent descriptor join equals one of those measures and not the other. Here $c,D$ are statistics of $\Gamma_B$ itself; the signed charges are statistics of the specific alternating descriptor chain. Equality of the two descriptor flows determines these diagnostics and the complete-word recursion used here. It does not identify an original hidden-label $\Xi$, preserve its return motion, or provide a runtime observation of the diagnostics. Theorem 6.2 instead transfers only the clipped first-half edge products through the original reachability inclusion and unchanged extracted kernels.

[PAIR, Theorem 12.2 and Corollary 12.3] classify and exclude the synchronized four-coordinate endpoint-chord fibre. Proposition 12.4 supplies separately full-risk-feasible nonnative marginals that admit no common flow. [PAIR, Section 14] additionally supplies a quantitative complete-loss stability theorem and a necessary risk–four-moment-defect relation on this same compatible-pair domain. These are credited compatibility and quantitative obstruction results. The two event midpoint means in this volume are not the four synchronized emission/short-word coordinates of those theorems. Citation 8.1a gives their exact diagnostic and consumer; the return-weight response (3.3), signed alternative (5.4) and original clipped-span bound (6.2) have the different inputs and conclusions specified above.

**Mathematical citation 8.1a (the supplied quantitative four-moment obstruction).** On precisely the compatible Borel pair of Definition 2.2, retain the following [PAIR, Standing assumptions 12.1 and 14.1] diagnostics:

$$
\begin{aligned}
m_p&=\int u\,d\nu_p,&m_\beta&=\int v\,d\nu_\beta,\\
q_{\rm PAIR}&=\int Q(\beta\beta)\,d\nu_p,&
z_{\rm PAIR}&=\int W(\alpha\alpha)\,d\nu_\beta,\\
J_p^{\rm PAIR}&=\int(u-a)(b-u)\,d\nu_p,&
J_\beta^{\rm PAIR}&=\int(v-a)(b-v)\,d\nu_\beta,\\
M_B&=\int(u(Q)-v(W))^2\,d\Gamma_B,&
M_A&=\int(v(W)-u(Q))^2\,d\Gamma_A.
\end{aligned}
$$

In particular $q_{\rm PAIR}$ is the mean probability of $w_{0,1}=\beta\beta$; it is not this volume's $q$, the mean probability of $w_{3,1}$. The source's two directional affine defects and their sum are

$$
\begin{aligned}
D_B^{\rm PAIR}
 &=\frac{26}{15}-\frac{19}{15}(m_p+m_\beta)-2q_{\rm PAIR}
   =J_p^{\rm PAIR}+J_\beta^{\rm PAIR}+M_B,\\
D_A^{\rm PAIR}
 &=\frac{11}{15}(m_p+m_\beta)-\frac4{15}-2z_{\rm PAIR}
   =J_p^{\rm PAIR}+J_\beta^{\rm PAIR}+M_A,\\
S_{\rm PAIR}
 &=D_B^{\rm PAIR}+D_A^{\rm PAIR}
   =2J_p^{\rm PAIR}+2J_\beta^{\rm PAIR}+M_B+M_A\\
 &=\frac{22}{15}-\frac8{15}(m_p+m_\beta)-2q_{\rm PAIR}-2z_{\rm PAIR}\ge0.
\end{aligned}
$$

These exact identities are [PAIR, equations (12.6)–(12.7) and (14.1)]. They use both unweighted phase marginals and the respective descriptor-conditioned residual equations. The symbol $D$ in (2.7) remains the mean absolute deviation of $(1-u)v$ on $\Gamma_B$; neither directional defect nor $S_{\rm PAIR}$ is substituted for it.

[PAIR, Theorem 14.2] states that one weight

$$
\theta=\nu_p\{Q:u(Q)>(a+b)/2\}
$$

works for both phases and every normalized complete target. With

$$
H_{s,\theta}(T)
 =(1-\theta)\operatorname{TV}(P_{s,a},T)
   +\theta\operatorname{TV}(P_{s,b},T),
$$

its all-target bounds are

$$
|\mathcal L_p(T)-H_{p,\theta}(T)|\le\frac{540}{11}S_{\rm PAIR},
\qquad
|\mathcal L_\beta(T)-H_{\beta,\theta}(T)|\le\frac{1395}{22}S_{\rm PAIR}.
$$

Targets may put positive mass on infinite noncompletion. The descriptors remain the original normalized complete laws with their supplied tail control. No finite law marginal is assumed. The common weight is independent of the target; the comparison keeps TV inside each descriptor integral. At $S_{\rm PAIR}=0$, both flows and both marginals are exactly the synchronized native endpoint pair of [PAIR, Theorem 12.2], with common endpoint weight $\theta$, including $0$ and $1$.

[PAIR, Corollary 14.3] transports this comparison through the same original full-record renderer to every posterior target from a positive paid history under the once-sampled $K$. For an original stationary product the comparison integral is its original history configuration loss. For a general Borel pair it remains a mathematical integral, without asserting an installed observer. This stationary-product interpretation does not replace Theorem 6.2's initialized extraction, support closure, clipping and reachable-edge argument for an arbitrary original finite observer. Neither the common comparison weight nor the two law flows identifies the hidden three-stage return measure $\Xi$ or its variation. No posterior, clock, endpoint tag or continuous descriptor is added to the runtime interface.

For positive endpoint masses and any supported $k\ge3$, [PAIR, Corollary 14.4] gives

$$
\mathcal J+\frac{540}{11}S_{\rm PAIR}\ge\frac\eta4,
\qquad
\eta=\frac{14219478376}{318644812890625}.
$$

The present fixed positive support $\{1,2,3\}$ meets these hypotheses. In particular the simultaneous inequalities

$$
\mathcal J<\frac{1777434797}{318644812890625},
\qquad
S_{\rm PAIR}<\frac{19551782767}{172068198960937500}
$$

are excluded. The same corollary also excludes the same risk threshold together with

$$
\|\mathbf c_{\rm PAIR}-\mathbf c_{\rm PAIR}(\theta_0)\|_\infty
 <\frac{19551782767}{871812208068750000}
\quad\text{for some }\theta_0\in[0,1]
$$

is excluded, where

$$
\begin{aligned}
\mathbf c_{\rm PAIR}&=(m_p,m_\beta,q_{\rm PAIR},z_{\rm PAIR}),\\
\mathbf c_{\rm PAIR}(\theta_0)
 &=\bigl(a+(b-a)\theta_0,\ a+(b-a)\theta_0,\\
 &\hspace{1.2cm}(1-\theta_0)(1-a)^2+\theta_0(1-b)^2,
                 (1-\theta_0)a^2+\theta_0b^2\bigr).
\end{aligned}
$$

The coordinate exclusion consumes the displayed affine formula for $S_{\rm PAIR}$, whose coefficient absolute sum is $76/15$. These are the supplied evaluated chord-neighborhood thresholds, not an evaluated optimizer or an unrestricted positive risk-only gap. Away from this neighborhood $S_{\rm PAIR}$ is free. With only depths 1 and 2 supported, the fair native endpoint pair instead has $\mathcal J=S_{\rm PAIR}=0$; this does not meet the present three-depth hypotheses.

The zero predicates of the two diagnostics can be separated by the existing supplied examples, without selecting a different coupling. For the actual two positive $B$ edges of Proposition 7.1, $D=0$, while direct substitution in the definitions above gives

$$
J_p^{\rm PAIR}=0,\quad
J_\beta^{\rm PAIR}=\frac{47}{64800},\quad
M_B=\frac{13}{64800},\quad
M_A=\frac{181}{64800},\quad
S_{\rm PAIR}=\frac1{225}>0.
$$

Conversely, the fair native endpoint pair has $S_{\rm PAIR}=0$. Its two $B$-edge weights are $2/9$ and $6/25$, each of mass $1/2$, so

$$
c=\frac{52}{225},\qquad D=\frac2{225}>0.
$$

The latter pair is compatible on the same complete carriers, but is not a zero-level witness for the three-depth objective. These calculations distinguish the diagnostic zero sets; they assert no general quantitative dominance relation or feasibility criterion. The supplied PAIR theorem already establishes a necessary risk-defect relation and uniform complete-loss comparison. This volume's particular increment is the joint $F(c,P),G(c,P)$ response, signed same-path balances and clipped first-half-edge span consumer, rather than the general theme of a quantitative compatibility obstruction.

[REV, Chapter 14, Theorem 14.1] gives an exact all-word endpoint-box criterion for a three-label periodic reversible table with $A=I$ and $B$ a swap plus a fixed point. Its rational table satisfies the complete boxes, suspended midpoint, both interior costs and the retained decline and squared-return necessities, yet misses the p midpoint and fails the p-a risk bound. Its fixed-N companion inequality is conditional on a positive complementary p defect; the displayed table has the opposite sign. This does not supply a zero pair or an unrestricted separating certificate. Its linear chord defect, energy and decline functionals are different from the mean absolute deviation $D$ in (2.7). The periodic criterion and the failed sufficiency bridge are suppliers under their own hypotheses, rather than instances or replacements of (3.3)–(3.11).

[AURIC, Section 15] supplies future-response criteria for one specified finite output-resolved instrument. It does not recover an unknown instrument from these two means, provide an emission port or settle this common-flow feasibility problem. [SPARSE, Sections 10–15] supplies exact deterministic unit-call minimax for static finite ordered-tree history tasks, with its joint original-tree image and arbitrary-depth query coverage. Sections 20–24 additionally treat complete finite nominal installations, exact first-occurrence caches, vector-valued historical targets, unbounded literal addresses and a WS2S capacity criterion. They distinguish exact representation of a given installation from existence of a bounded-address replacement; the latter need not preserve that installation's sourcewise traces or costs. Proposition 23.3's reached-row replay requires the same deterministic installed table, static tree service and never-forgetting raw cache. The binary stopped source here has stochastic paid Reads under one sampled $K$, not that service. No bridge transports their capacity criterion, address bound, replay or unit-call optimum into this common-flow problem or its COMPLETE account.

**Mathematical citation 8.2 (one-sided exact realization and its preservation boundary).** [PAIR, Theorem 13.2] supplies a stronger conditional realization interface than requiring both input marginals to be finite. If a supplied compatible pair has $N$ distinct positive p-law atoms, it keeps that entire p marginal and gives a finite regular same-update table with at most $N^2+2N+q-1$ suspended labels. It may preserve any specified $q$ bounded Borel integrals on the suspended marginal and any Borel full-measure suspended constraint. The symmetric result exchanges phases. The construction matches unweighted moments to retain actual circulation and weighted residual moments to close both complete-law equations. The complete descriptors are the regenerated table's own laws, not finite-horizon fits.

For an actually supplied zero pair at the fixed support $\{1,2,3\}$ with finite p marginal, choose

$$
G=\{W:\text{every complete suspended coordinate lies in its endpoint box}\},
\qquad f_1(W)=W(E_\beta),\qquad
f_2(W)=\operatorname{TV}(W,P_{\beta,3/8}).
$$

Here $q=2$. The retained p marginal keeps its whole box, midpoint and all three configuration losses. The selected suspended laws remain in the whole box; matching $f_1$ keeps its midpoint and hence both endpoint losses, while matching $f_2$ keeps its depth-3 loss. Thus [PAIR, Corollary 13.4] gives a possibly different abstract finite zero table with

$$
|X|=N,\qquad |Y|\le N^2+2N+1.
$$

The exchanged map uses the p box, $Q(E_p)$ and $\operatorname{TV}(Q,P_{p,3/8})$. Consequently the existence of an abstract finite original common attainer is equivalent to the existence of some zero pair with either one finite law marginal. Both input marginals need not be finite. This is a conditional realization statement; this volume supplies no such zero pair.

For a chosen one-sided support cap $N$, [PAIR, Theorem 13.5] matches all three opposite target losses and equates the attained minimum on that branch to the attained table minimum with opposite label cap $N^2+2N+2$. It evaluates neither minimum and gives no $N$ known to contain an unrestricted optimizer. If $j_c=0$ and no abstract finite attainer exists, both law marginals of every zero pair are infinite, and both distinct-law counts tend to infinity along any regular vanishing-excess sequence. Absence only of a permitted effective sampler does not imply that abstract nonattainment condition.

Theorem 13.2 may replace the opposite marginal and both joint flows. Preservation of the retained marginal and selected opposite moments does not establish preservation of the old $\Gamma_B,\Gamma_A$, dispersion $D$, the collection of signed path charges in (3.10), or hidden actual return coupling. The diagnostics in this volume must be evaluated on the resulting pair's own flows and chain. Theorem 4.1 and Corollary 5.3 then apply to that resulting pair by their stated hypotheses. [PAIR, Theorem 11.8] realizes a pair with both finite marginals while preserving its two descriptor flows; [RETURN, Proposition 11.9] still prevents interpreting that two-flow preservation as hidden-return preservation.

[PAIR, Proposition 13.3] restores the full original histories, same-update kernels and source-independent latch sampler. It preserves the retained side's losses against every posterior target and the specified opposite pure-target losses. Opposite losses at each posterior mixture need not equal their old values; the full-history phase suprema are the supported pure-target suprema, which is the relevant risk correspondence. For arbitrary real nodes, weights and entries, permitted finitely represented exact samplers for the latch, both acquired kernels and emissions remain separate obligations. All numerical descriptions, active and service states, program, workspace, fresh bits, computation, acquired Reads, synthesis and output are charged. The label bounds preserve no fixed COMPLETE, hard-defect or worst-case work budget. Proposition 7.2 discharges representation only for its explicit rational nonattaining example.

[PAIR, Theorem 13.6] concerns a different countably infinite installed-support branch: a one-sided finite zero pair and strictly positive opposite accumulation-target slack imply abstract finite all-supported attainment. Saturated accumulation loss remains outside that theorem. Neither its support nor its strict-slack premise is substituted for the fixed three-depth question here.

**Mathematical citation 8.2a (bounded FIB supplier correspondence).** The comparison with [FIB-CHANGE; FIB-READOUT; FIB-FIELD; FIB-CLOCK; FIB-OCCLUSION; FIB-SYMMETRIC] concerns their listed mathematical constructions and governing applicability clauses. Graph integrability, calibrated static projections, output-resolved observation closure, quotient sufficiency and finite-dimensional stabilization are credited existing methods. The source-specific claims of Sections 3–7 do not acquire novelty from restating those methods.

There is an actual shared paired-recursion supplier. [FIB-OCCLUSION, Section 九 and Q4] and [FIB-FIELD, Q12] explicitly attribute to [PAIR, Sections 2–4] the finite-table equations

$$
\begin{aligned}
Q_x&=u_x\delta_\alpha+(1-u_x)\beta\sum_yB_{xy}W_y,\\
W_y&=(1-v_y)\delta_\beta+v_y\alpha\sum_xA_{yx}Q_x,\\
L&=\operatorname{diag}(1-u)B\operatorname{diag}(v)A,
\qquad g=\operatorname{diag}(1-u)B(1-v),\\
f&=g+Lg+L^2g,
\qquad h=1-v+\operatorname{diag}(v)Ag.
\end{aligned}
$$

Here $f_x=Q_x(E_p)$ and $h_y=W_y(E_\beta)$ are the entire configuration-indexed event arrays. The inverse fixes the same finite $A,B$, positive rows $\pi,\tau$ with $\pi B=\tau$, $\tau A=\pi$, regular emissions, and arrays satisfying the unprojected compatibility equations. It is an offline inverse within that known-kernel domain. This volume's $P=\pi f$ and $T=\tau h$ are only two scalar averages; neither the cited inverse nor a static second projection turns them into the full arrays, unknown acquired kernels or a compatible common-flow witness. The recursions are already the suppliers of (3.4), not an additional new result here.

The other correspondences and their missing maps are as follows.

| Supplier and exact compared clauses | Mathematical object supplied | Boundary for this complete stopped-flow problem |
| --- | --- | --- |
| FIB-CHANGE, 变化—场可积定理 and Q1–Q2, Q6–Q9 | A potential for abelian group increments on a connected underlying graph exists when every signed closed-walk increment sums to zero; calibrated five-state differences require common operator types and normalized feasible fibres. | An additive edge increment is not a probability residual barycentre. Formal reverse traversal supplies no legal reverse Read or waiting process. The compared statements give no map from their increments or static direction to the two residual equations, complete losses and acquired circulation in Definition 2.2. |
| FIB-READOUT, 未来输出闭包判据 and Q2–Q7 | For a fixed common linear instrument and the declared legal output words and tests, a feasible initial-law difference is invisible precisely when it annihilates the generated future-test space. Output branch masses and complete records are retained. | The fixed-initial-law seam direction and an acquired-kernel parameter change are different objects. Its Q7 retains the missing source, initial-state, kernel, test and word map; a larger block representation does not identify that map with the original five-state direction or preserve the present risk and resources. |
| FIB-FIELD, Q5–Q6, Q8–Q12 | Task-relative lumpability, fixed-generator observability, the attributed native Fibonacci phase/count future equivalence, and fixed-kernel indexed paired calibration. | Q8 retains the one sampled depth, every paid count, original renderer and legal active/pending/delivered domains. Its semantic phase/count summary is not a finite COMPLETE implementation. Q9 exhibits equal static and depth marginals with different joint future laws; separate marginals cannot supply this volume's joint flows. |
| FIB-CLOCK, 局部时钟核, 输出分辨未来闭包判据 and Q1–Q2, Q5–Q11, Q16 | A fixed known waiting-law mixture on five states, its signed four-corner response, and future closure under complete output-resolved marked subkernels. | Its survival variable belongs to a state-conditioned waiting law, not the discrete synthetic pair weight $Z=(1-u)v$. Waiting, output and successor require one joint marked kernel; separately specified marginals do not determine it. No waiting-law observation is present in the original stopped source or installed observer. |
| FIB-OCCLUSION, Section 九 and Q3–Q4 | The displayed PAIR recursions and an attributed inverse from both complete indexed arrays under fixed acquired kernels. | Q3 retains once-sampled $K$, positive paid histories, full records and matching Stop. Q4 limits the static/dynamic comparison to an analogy without a source/action/target/error/resource isomorphism. Compatibility of proposed arrays and a runtime readout are separate obligations. |
| FIB-SYMMETRIC, the finite-prefix blind-direction comparison and Q6, Q11–Q13 | Symmetric mixed differences, order defects, and fixed-carrier future visibility under a full legal observation contract. A block-diagonal comparison can encode two known models on a larger carrier. | Its Q6 distinguishes growing private-label dimension and acquired-kernel variation from one fixed five-state initial-law direction. Q11 preserves all outputs, records, Stop and consistent cylinder laws; Q12 distinguishes additive clock increments from probability kernels. These statements provide no native stopped-flow map or lawful resource-preserving replacement for the present observer. |

In the fixed five-state statements, the seam direction $d=(1,-1,0,-1,1)$ is a zero-total-mass initial-law direction. It is not this volume's dispersion $D$, the hidden depth $K$, or an unknown residual flow. Nonzero response along that direction requires feasible distinct initial laws and a fixed calibrated instrument; it does not itself generate a new observation permitted by Definition 2.1. The supplied native future equivalence likewise concerns semantic complete conditional laws on its own legal domain, rather than access to the depth, posterior or unbounded counts as finite runtime state.

These compared sections give no source/action/risk/resource map that would transfer their static seam, additive potential, waiting-law or fixed-dimensional closure statements into a zero pair or a universal exclusion in $\mathfrak C$. This is the scope of the comparison, not a theorem that such a map is impossible or a catalogue of all FIB results. It leaves the original once-sampled source, acquired/synthetic update identity, configuration-before-TV order, exact-sampler conditions and COMPLETE accounting exactly as in Definitions 2.1–2.4 and Citation 8.2. No detector, clock, causal or practical-performance conclusion is imported.

**Mathematical citation 8.3 (bounded primary-literature comparison).** The comparison is bounded to the stated primary versions and their relevant definitions and results; it supports attribution and method correspondence, not global originality. The source-specific response, signed cancellation condition and clipped original consumer are repository-local mathematical synthesis; generic coupling, quadrature, convexity and sampling remain credited tools.

- Leskela and Vihola [LV, Theorems 1.2–1.3] give convex-order/martingale-coupling equivalences for finite-first-moment vectors and measurable parameterized kernels. Finite complete-word projections here are bounded vectors, so their finite-dimensional hypotheses can be met. This mature coupling supplier does not itself establish two full descriptor-conditioned flows with these common marginals or the evaluated inequalities (3.3).
- Monras and Winter [MW, Section 2, Definition 5] study positive realizations of a prescribed stationary output process by nonnegative symbol matrices with stochastic sum and a stationary initial row. A positive realization alone does not impose this separate unweighted acquired circulation or configuration-before-TV endpoint losses. No positive-realization existence theorem is used to install a missing common-flow witness.
- Ferre, Rousset and Stoltz [FRS, Section 2, Assumptions 1–3] analyze long-time Feynman–Kac stability using a Lyapunov condition, minorization/irreducibility and local regularity. The killed-versus-unweighted distinction is a mature frame for (3.4). Their convergence hypotheses are not supplied for arbitrary $BA$ here, and no conclusion requiring them is borrowed. Our finite-word bounds use no actual-chain mixing.
- Chen and Kiefer [CK, Corollary 8] approximate TV for a given pair of labelled Markov-chain laws. That is a comparison of supplied laws, not synthesis or minimization over this unbounded collection of common finite carriers.
- Bayer and Teichmann [BT, Corollary 2] give positive finite quadrature on a specified measurable full set for an integrable finite-dimensional measurable feature map. This supplies the finite node selection used in [PAIR, Theorem 13.2], not the source-specific full-law closure or any survival-dispersion inequality. Its finite real nodes and weights are not a represented-sampler theorem.
- Zhao [Z, Sections 1.2–1.4] considers common row-stochastic controlled realizations of response menus, with multiple roots and one terminal effect, and distinguishes local, static and chronological realizations. Its finite-menu and rank-tight compiled-family hypotheses do not furnish the original stopped-source conditional residual equations or the required complete configuration losses. Its chronological-consistency distinction is relevant context; no additional control letter, root choice or compiler is imported.

**Definition 8.4 (retained frontier).** The full compact question still asks whether $j_c=0$ or $j_c>0$ for the one fixed original positive three-depth prior, retaining both full endpoint boxes, both midpoint means, both depth-3 configuration bounds and both descriptor-conditioned residual equations. This volume proves only that any zero pair must have a quantitatively nonconcentrated return-weight law. That law can have $D>\kappa_0$; the response envelope then leaves the zero alternative possible. The supplied [PAIR, Corollary 14.4] additionally requires $S_{\rm PAIR}\ge11\eta/2160$ at such a pair. Both diagnostics must be computed on the same compatible realization, and both necessary bounds leave that realization unconstructed and unexcluded.

To close the original decision one still needs either a source-faithful compatible pair meeting all six complete configuration bounds, or a certificate excluding every such pair without setting $D$ to zero. A precise next question is whether the endpoint faces and depth-3 losses prevent the two signed alternatives in Corollary 5.3 on their respective $c$ ranges, or permit a construction that supplies the required correlation. An unsigned first-moment deviation bound is insufficient. Such a proof must control those joint products on this same acquired path; separate moment extrema are not a witness or certificate.

If a zero pair is eventually obtained with either law marginal finite, [PAIR, Theorem 13.2 and Corollary 13.4] supplies an abstract finite zero table, with the selected boxes, midpoint and depth-3 losses retained as specified in Citation 8.2. If both marginals of that pair are infinite, this exact bridge does not apply automatically; a different one-sided finite or fully finite zero pair is not ruled out. General compatible zero pairs supply the finite positive-tolerance family of [PAIR, Corollary 11.7]. A permitted finitely represented exact sampler and the full COMPLETE accounting remain additional obligations for effective exact attainment. No finite exact optimizer, unrestricted positive gap, fixed-resource optimum, hard-defect preservation, practical performance gain, full-code whitebox impossibility, universal fivefold ML classification or completion of the broader four common-generator frontiers is claimed here.

## 9. References

- **PAIR:** [Paired calibration observability](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md), Sections 11–15, especially Theorem 14.2, Corollaries 14.3–14.4, and Theorem 15.1.
- **ST:** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), Sections 1–3.
- **CLIP:** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), Theorem 3.1 and Proposition 2.3.
- **PAID:** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), Lemmas 2.1.1 and 14.1.
- **HET:** [Suspended-emission heterogeneity](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SUSPENDED_EMISSION_HETEROGENEITY.md), Theorem 3.1.
- **RETURN:** [Acquired-return p-emission variation](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md), Sections 9–11, especially Proposition 11.9.
- **AURIC:** [Output-resolved instrument closure](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md), Section 15.
- **SPARSE:** [Sparse literal-history transport](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md), Sections 10–15 and 20–24.
- **REV:** [Reversible common-generator constraints](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md), Chapter 14.
- **FIB-CHANGE:** [变化优先关系场与可积性](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/AURIC_FIB_ATOM_CHANGE_FIRST_RELATIONAL_FIELD_AND_INTEGRABILITY.md), 变化—场可积定理 and governing Q1–Q2, Q6–Q9.
- **FIB-READOUT:** [隐藏接缝与因果读出闭包](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_SEAM_CAUSAL_READOUT_CLOSURE.md), 未来输出闭包判据 and governing Q2–Q7.
- **FIB-FIELD:** [局部钟场、因果场与纤维动力学](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_CLOCK_CAUSAL_FIELD_AND_FIBER_DYNAMICS.md), governing Q5–Q6 and Q8–Q12.
- **FIB-CLOCK:** [局部时钟核与输出分辨接缝可见性](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md), 局部时钟核, 输出分辨未来闭包判据 and governing Q1–Q2, Q5–Q11, Q16.
- **FIB-OCCLUSION:** [遮挡、第二投影与局部恢复](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/AURIC_FIB_ATOM_OCCLUSION_SECOND_PROJECTION_AND_LOCAL_RECOVERY.md), Section 九 and governing Q3–Q4.
- **FIB-SYMMETRIC:** [对称接缝、路径缺陷与 Fibonacci 层级](https://github.com/the-omega-institute/trureturing/blob/a58c24900650d4a0b6022c5e2cf76f5f6f2f8271/docs/develop/theory/AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md), finite-prefix blind-direction comparison and governing Q6, Q11–Q13.
- **LV:** Lasse Leskela and Matti Vihola, *Conditional convex orders and measurable martingale couplings*, [arXiv:1404.0999v3](https://arxiv.org/html/1404.0999v3), Theorems 1.2–1.3.
- **MW:** Alex Monras and Andreas Winter, *Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*, [arXiv:1412.3634v1](https://arxiv.org/html/1412.3634v1), Section 2.
- **FRS:** Grégoire Ferré, Mathias Rousset and Gabriel Stoltz, *More on the long time stability of Feynman-Kac semigroups*, [arXiv:1807.00390v3](https://arxiv.org/html/1807.00390v3), Section 2.
- **CK:** Taolue Chen and Stefan Kiefer, *On the Total Variation Distance of Labelled Markov Chains*, [arXiv:1405.2852v1](https://arxiv.org/html/1405.2852v1), Corollary 8.
- **BT:** Christian Bayer and Josef Teichmann, *The proof of Tchakaloff’s Theorem*, [arXiv:math/0502473v2](https://arxiv.org/html/math/0502473v2), Corollary 2.
- **Z:** Yixin Zhao, *Exact Local Optimality Does Not Compose: The Complexity of Chronological Realization*, [arXiv:2609.19707v2](https://arxiv.org/html/2609.19707v2), Sections 1.2–1.4.

## 10. Latest PAIR certificate boundary and native renderer correspondence

### 10.1 The selected PAIR certificate class

The appended PAIR result is read at the current immutable source revision `a58c24900650d4a0b6022c5e2cf76f5f6f2f8271`, in [PAIR15, Sections 15.1–15.6]. Its standing source is the same $m=2,d=1,\ell=2,n=4$ stopped experiment used in Definitions 2.1–2.4: one positive integer $K$ is sampled once, all paid seed rejections and finite returns remain in the record, the third write precedes its latch, fourth completion reaches the matching Stop, and the complete carriers retain the infinite noncompletion outcome. Actual and synthetic updates use the same source-independent acquired kernels. No posterior, clock, reset, completion-conditioned source, or extra runtime port is introduced.

PAIR15 studies a declared level-five certificate class. The complete coordinate boxes retain the level-five tail cell, all nonnegativity and normalization constraints, endpoint emission intervals, and the original tail bounds. Its loss coordinates are the complete-word/tail partition losses at levels $L\le5$, with the infinite outcome included in the tail cell. The selected dual allows arbitrary whole-input multipliers of the two scalar event residuals, degree-at-most-two marginal potentials in the displayed event coordinates, and finite nonnegative combinations of supported complete configuration losses. The normalized-residual-square extension uses squares of the normalized residual-event values. These are restricted certificate classes; they do not represent all degree-at-most-two functions of the complete word/tail vector.

Write

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\},
$$

and, for complete laws $Q,W$,

$$
 f(Q)=Q(E_p),\quad h(W)=W(E_\beta),\quad
 b_0(Q)=\frac{Q(w_{0,1})+Q(w_{1,1})}{U(Q)},\quad
 a_0(W)=\frac{\sum_{n=0}^2W(\alpha w_{n,1})}{v(W)}.
$$

The class tests the two residual differences $b_0(Q)-h(W)$ and $a_0(W)-f(Q)$, while its loss terms are the supported complete target losses. The full Chapter 11 residual equations remain coordinatewise equations on the complete carriers.

### 10.2 Exact rational pair and its certified properties

PAIR15 gives

$$
 u_0=\frac{1829}{5000},\quad U_0=\frac{3171}{5000},\quad
 v_0=\frac{46}{125},\quad d=\frac{13}{15000},
$$

$$
 t=\frac{78975}{2857232},\quad
 s_a=\frac12-t=\frac{1349641}{2857232},\quad
 s_b=\frac12+t=\frac{1507591}{2857232}.
$$

The p law starts from the endpoint mixture $s_aP_{p,a}+s_bP_{p,b}$ and changes only the four displayed coordinates. In particular,

$$
\begin{aligned}
Q(w_{0,0})&=u_0,\\
Q(w_{0,1})&=\frac{995}{2484},\\
Q(w_{2,1})&=\frac{19907803}{911250000},\\
Q(w_{1,1})&=\frac{72763013}{776250000},
\end{aligned}
$$

and every other finite p-word has mass $s_aP_{p,a}+s_bP_{p,b}$, with $Q(\infty_p)=0$. The suspended law is

$$
W=(1-v_0)\delta_\beta+v_0\,\alpha Q,
\qquad W(\infty_\beta)=0.
$$

The correction has total mass

$$
-d+t\bigl(2\rho_p-(b-a)\bigr)=0,
$$

so $Q$ is normalized, and the displayed formula normalizes $W$. The exceptional coordinates lie in their complete endpoint intervals; the unchanged coordinates are convex endpoint mixtures with the fixed tail order. The source tail checks are

$$
Q(T_p(1))=\frac{725441}{3105000}<\lambda,qquad
Q(T_p(2))=\frac{327003972413}{6026973750000}<\lambda^2,
$$

and for $j\ge3$ the endpoint mixture gives $Q(T_p(j))\le\lambda^j$. Since

$$
W(T_\beta(j))=v_0Q(T_p(j))\le b\lambda^j,
$$

all complete tails, including the zero-mass infinite outcomes, satisfy the original constraints.

Direct prefix deletion gives $\mathcal R_A(W)=Q$. The opposite residual $Z=\mathcal R_B(Q)$ has

$$
Z(\beta)=\frac{1243750}{1969191},qquad
1-Z(\beta)=\frac{725441}{1969191}\in[a,b],
$$

and PAIR15 checks every exceptional residual coordinate, the fixed tail order, and both residual tail bounds. Thus $Q,W$ lie in the full endpoint boxes and their residual projections, so every allowed level-five certificate sees a point in its declared domain.

The four scalar identities are

$$
 f(Q)=C,\qquad b_0(Q)=H,\qquad h(W)=H,\qquad a_0(W)=C.
$$

Thus the two selected residual-event equalities hold exactly: $b_0(Q)-h(W)=0$ and $a_0(W)-f(Q)=0$.

The endpoint coordinate identities therefore give the exact complete endpoint configuration losses $\rho_p$ and $\rho_\beta$ in the two directions. Every supported nonendpoint target lies in $[3/8,5/13]$. The complete-law bounds in PAIR15 are

$$
B_p=\frac{355994686242025987031}{26994670778880000000000}<\frac1{50},qquad
B_\beta=\frac{3515477241015883163647}{421791730920000000000000}<\frac1{75},
$$

and the supplied stopped-parser couplings give

$$
\operatorname{TV}(P_{p,r},P_{p,t})\le\frac{125}{57}|r-t|,qquad
\operatorname{TV}(P_{\beta,r},P_{\beta,t})\le\frac{107}{57}|r-t|.
$$

Because $5/13-3/8=1/104$,

$$
\operatorname{TV}(Q,P_{p,r})<\frac{6089}{148200}<\rho_p,qquad
\operatorname{TV}(W,P_{\beta,r})<\frac{4651}{148200}<\rho_\beta
$$

uniformly on the supported nonendpoint interval. Hence every complete configuration loss is within its radius before phase averaging; every coarser level-$L$ loss with $L\le5$ is no larger by partition contraction. This is a complete-law statement, not a finite-horizon approximation. The pair has exact rational coordinates but countably many unchanged word coordinates, and it is not by itself a finitely represented observer or sampler.

### 10.3 The no-separator result and the exact failed coordinate

At this pair, the directional point masses

$$
\widehat\Gamma_B=\delta_{(Q,W)},\qquad
\widehat\Gamma_A=\delta_{(W,Q)}
$$

have common unweighted phase marginals. Whole-input multipliers of the selected scalar residuals integrate to zero, marginal potentials cancel, the centered affine event terms vanish, and all supported loss terms are nonpositive because the endpoint losses equal their bounds while the interior losses are strictly below. Therefore any pointwise lower bounds in the selected event-output class obey

$$
\kappa_B+\kappa_A\le F_p(Q)+F_\beta(W)\le0.
$$

In the normalized-residual-square extension the two square contributions cancel exactly, with the same nonpositive loss conclusion. Thus no finite nonnegative combination of supported losses in this class, for any permitted $L\le5$, yields a positive summed separator. The pair also gives equality of the two scalar event laws, so scalar convex-order tests of those events cannot separate it.

The pair nevertheless fails the complete residual equation at the beta coordinate. PAIR15 computes

$$
Q(w_{0,1})-U_0W(\beta)=-\frac{97339}{388125000},
$$

and hence

$$
\mathcal R_B(Q)(\beta)-W(\beta)
=-\frac{97339}{246148875}\ne0.
$$

Consequently

$$
\operatorname{TV}(\mathcal R_B(Q),W)
\ge\frac{97339}{246148875}>0.
$$

The constant input test $\phi=1$ in the full residual equation already fails. Since both directional marginals are Dirac masses, their only coupling is the displayed point mass; no alternate coupling repairs this coordinate. The pair is therefore not compatible in the sense of Definition 2.2 and cannot be installed as an observer.

This exact failure has a narrow meaning. The pair satisfies full endpoint-box membership, all complete tails, both scalar event means, both selected residual-event equalities, the complete endpoint and supported interior loss bounds, and the selected no-separator test. It does not satisfy the unrestricted complete-coordinate residual vector. The failed bridge is therefore evidence that the selected event-output certificate class is too weak, not a no-go theorem for the full word/tail vector class. It supplies neither a compatible zero pair nor an infeasibility certificate for all compatible flows.

The candidate response theorem in Sections 3–5 uses the complete residual equations recursively on every coordinate, including the $w_{3,1}$ mass and the signed same-path balances. Those equations are stronger than the two scalar event equalities above. The PAIR15 pair cannot be substituted into that theorem, so its failed beta coordinate does not refute Theorem 3.1, Theorem 4.1, or Theorem 6.2. Conversely, the candidate's full-vector inequalities do not imply the PAIR15 no-separator statement for the selected event class.

### 10.4 Native full renderer and ordered-row correspondence

The native source modules provide a direct renderer and joint-law correspondence for the original experiment. In [NFR], `OriginalEvent`, `eventBlock`, and `eventBlocks` encode acquired, rejected, accepted, completed, written, latched, moved, held, and stopped events. `fullTranscript` records each legal operation prefix together with the current finite fields and its ordered event blocks. The theorem `full_event_reconstruction` recovers the finite fields and the original-view projection from these blocks. The write-before-latch record is therefore retained in the native transcript.

For a legal next operation, `full_delete_block` removes exactly that operation's event block and agrees with the transcript from the raw tail after the operation's read cost. The tail domain `ValidTail` contains both every legal finite completion word and the single noncompletion outcome. `fullRenderer` maps this domain to full transcripts, `full_renderer_all_paths` identifies every native stream with its stopped word or noncompletion tail, and `full_renderer_readback` recovers the raw tail. The resulting `full_renderer_tv` equality preserves event-supremum total variation, including the noncompletion outcome. These statements establish renderer and risk transport for the native source; they do not construct arbitrary $Q,W$, endpoint boxes, or acquired descriptor flows.

In [NJL], an observer is a finite carrier $Z$ with a projection to the native finite fields, an initial PMF, and one update PMF for every legal operation. Its `row` is the ordered product of those updates along an acquired operation list. The `privateKernel` uses only the row at the actual `cutHistory`, and

$$
\operatorname{actualLaw}(M,\mu,n)
=\operatorname{jointLaw}(\mu)\otimes_M\operatorname{privateKernel}(M,n).
$$

`ordered_history_factorization` factors a positive history, a fixed depth, a raw tail event, and a private state into the product of the prior mass, likelihood, ordered row mass, and same-depth raw-tail law. `conditional_history_product` and `sameK_private_tail` preserve the full ordered private row together with the posterior source law; they do not select a configuration in advance. `actual_row_refines` keeps the native fields, row update law, and prefix reconstruction at every legal cut.

The definitions `rawTarget`, `fullTarget`, `fullRisk`, and `rawRisk`, together with `native_history_risk_transport`, then give the exact correspondence

$$
\operatorname{fullTarget}
=\operatorname{rawTarget}\mathbin{\mathrm{map}}\,\operatorname{fullRenderer},
\qquad
\operatorname{fullRisk}=\operatorname{rawRisk},
$$

under the stated lawful-tail hypotheses. The equality is obtained before the full history supremum and after configuration-before-TV averaging. It is the native renderer/joint-law bridge relevant to Definition 2.1 and Theorem 6.2.

### 10.5 Native conditional laws versus the synthetic common flow

[FSR] and [NCC] supply the source-side conditional law. `jointLaw` samples one depth and an independent infinite raw source stream; `nativeEvent` is the exact legal-history event; `posterior` is the normalized same-$K$ depth law; `sameK_conditional_tail` keeps the unread source conditional on that event; and `drive_control` gives the native control transition. [FSR] additionally supplies `native_renderer_eq`, `wordLaw`, `wordMixture`, `posterior_word_law`, `residual_law_transport`, and `complete_original_recovery`, so finite words, complete rendered traces, posterior mixtures and phase recovery agree under the native renderer.

The common-flow objects of Definitions 2.2–2.4 have a different role. $Q,W$ are complete descriptor laws, $A,B$ are acquired descriptor disintegrations, and $\Gamma_A,\Gamma_B$ are unweighted stationary phase flows. Their synthetic generation uses $u(Q)$, $v(W)$ and the same acquired updates in the recursive residual equations. The native modules do not supply a map from an arbitrary pair of descriptor flows to an `Observer`, an initialized finite carrier, or a source-independent exact emission sampler. To turn a compatible flow into an original observer one must still supply the full renderer-preserving construction, initialization, same-update laws, latch and Stop permissions, all held records, and a represented sampler for every stochastic entry. A parameterized `actualLaw(M,\mu,n)` proves the native joint law for a given $M$; it does not invert a descriptor quotient or recover a hidden return measure $\Xi$.

This distinction also preserves [RETURN, Proposition 11.9]. Equal descriptor flows and equal full-history configuration risks can coexist with different three-stage hidden measures $\Xi$ and different return motion. The native ordered-row factorization transports the actual source/private law; it does not identify that hidden coupling from $Q,W,A,B$. The candidate's $c,D$ and signed charges remain statistics of its own descriptor flow and alternating analysis chain.

### 10.6 Resource and realization boundary

The native finite carrier $Z$ is an analysis/private carrier. In the original observer contract, COMPLETE still charges $C_0$, installed tables and all numerical representations, program and selectors, active labels, persistent randomness, sampler service states, workspace, acquired Reads, synthesis and output. A finite atomic mathematical law does not imply a finitely represented exact sampler. PAIR one-sided realization preserves selected bounded integrals and full-measure constraints but may change the opposite marginal, both flows, $D$, and the signed charges; it gives no fixed COMPLETE or worst-case time bound. Proposition 7.2 discharges representation only for its explicit rational table.

The full frontier is consequently unchanged. The compact problem still asks whether $j_c=0$ or $j_c>0$ for the fixed positive prior on $\{1,2,3\}$ while retaining both complete endpoint boxes, both midpoint means, both depth-3 configuration-loss bounds, and both full conditional residual equations on the same unweighted phase marginals. PAIR15 supplies neither a compatible zero witness nor a universal incompatibility proof. The remaining mathematical task is to construct a source-faithful common flow satisfying the full coordinate residuals, or to exclude every such flow while retaining the same source, renderer, risk order, and resource contract. No unrestricted positive gap, finite exact optimizer, fixed-resource optimum, full-code whitebox impossibility, universal ML classification, or completion of the broader common-generator frontiers follows.

The exact source identities for this correspondence are [PAIR15] `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md`, blob `cde64079ccbb84d26b7ef5892e874510d0852aee`; [NFR] `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.lean`, blob `6db63d58b8b33d33164d3c2ade6d54a67c7e157a`; [NJL] `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.lean`, blob `700c4516ac399da4e8963a3aca2258c8bcfc5107`; [FSR] `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.lean`, blob `e31bbd075e1614c8cbedfc3c3db650f5c2f12ce7`; and [NCC] `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl.lean`, blob `4c44f4a72fe6fb57fb1ab74984ee7f357eaad87d`. The corresponding rendered statements are attribution aids; the source statements above determine the correspondence and its limits.

## 追加锚（本行以下为增补区）
