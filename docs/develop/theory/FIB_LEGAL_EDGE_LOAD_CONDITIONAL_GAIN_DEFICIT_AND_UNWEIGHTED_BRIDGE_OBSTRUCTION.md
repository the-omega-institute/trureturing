# FIB harmonic-edge load: conditional gain deficits and an unweighted bridge obstruction

## 1. One legal law, its fields and its gains

**Definition 1.1 (Complete producer domain and open-path objective).** For every finite $N\ge1$, let

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,\ M_0,M_1\ge0,
\ A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.1}
$$

All entries are real. The row $\lambda$ and the matrices have dimensions $N$ and $N\times N$. For $\theta\in\Theta_N$, use the actual two-sided stationary joint law $J_\theta$ of hidden states $H_i$ and emitted bits $X_i$, whose finite interval masses are

$$
J_\theta(H_a=h_a,X_a=x_a,\ldots,X_b=x_b,H_{b+1}=h_{b+1})
=\lambda_{h_a}\prod_{i=a}^b M_{x_i}(h_i,h_{i+1}).
\tag{1.2}
$$

Its visible marginal is $P=P_\theta$, with $P([w]_a)=\lambda M_w\mathbf1$ and $M_w=M_{w_1}\cdots M_{w_n}$. Empty products are identities. The scalar condition in (1.1) makes $P(X_i=X_{i+1}=1)=0$; it does not impose entrywise $M_1^2=0$ on every presentation. Zero stationary masses, structural zeros, reducibility, periodicity and noncontractive boundaries remain in the domain. No positivity, mixing or unifilarity assumption is added.

For the objective retained in [Multiword, §1][MW], put

$$
\begin{aligned}
B_n&=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},\\
h_{\rm edge}(s,t)&=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\\
\Phi_n(\mu)&=\sum_{\{w,z\}\in E(\Gamma_n)}h_{\rm edge}(\mu_w,\mu_z),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad c_\star=\lim_n\kappa_n/n.
\end{aligned}
\tag{1.3}
$$

Here $\Gamma_n$ has every legal Hamming-one edge. Endpoint insertion uses $w_0=w_{n+1}=0$, without a first-to-last constraint. Zero masses delete neither words nor edges. All interval seams use (1.2), without identification of the two endpoints. Every coordinate below is an original emitted-bit integer coordinate.

**Definition 1.2 (Actual half-lines and erased-center defects).** All radii $r,R$ are nonnegative integers. Under this single $P$, define

$$
\begin{aligned}
\mathcal P&=\sigma(X_j:j\le-1),&\quad \mathcal F&=\sigma(X_j:j\ge1),\\
W_L(r)&=\sigma(X_{-r},\ldots,X_{-1}),&W_R(r)&=\sigma(X_1,\ldots,X_r),\\
\mathcal E&=\mathcal P\vee\mathcal F,&G_L(r)&=W_L(r)\vee\mathcal F,\qquad G_R(r)=\mathcal P\vee W_R(r),\\
q&=\mathbb E_P[X_0\mid\mathcal E],&p_L(r)&=\mathbb E_P[X_0\mid G_L(r)],\qquad p_R(r)=\mathbb E_P[X_0\mid G_R(r)].
\end{aligned}
\tag{1.4}
$$

The finite fields at $r=0$ are trivial. All conditional expectations are actual $[0,1]$ versions under $P$. Set

$$
e_L(r)=\mathbb E_P(q-p_L(r))^2,\qquad
e_R(r)=\mathbb E_P(q-p_R(r))^2,\qquad
\tau_P(R)=\sum_{r\ge R}(e_L(r)+e_R(r)).
\tag{1.5}
$$

Both forcing neighbors are retained when $r\ge1$. For these radii, on either neighbor-one event, $X_0=q=p_L(r)=p_R(r)=0$ almost surely, and both defects vanish there. At $r=0$ a missing forcing neighbor can contribute a defect and is retained in (1.5). Null fibers require no division and do not affect expectations.

**Definition 1.3 (Predictive gaps and opposite-half-line gains).** Write

$$
\begin{aligned}
u_L&=\mathbb E_P[X_0\mid\mathcal P],&u_{L,r}&=\mathbb E_P[X_0\mid W_L(r)],\\
u_R&=\mathbb E_P[X_0\mid\mathcal F],&u_{R,r}&=\mathbb E_P[X_0\mid W_R(r)],\\
d_L(r)&=\mathbb E_P(u_L-u_{L,r})^2,&d_R(r)&=\mathbb E_P(u_R-u_{R,r})^2,\\
J_L(\infty)&=\mathbb E_P(q-u_L)^2,&J_L(r)&=\mathbb E_P(p_L(r)-u_{L,r})^2,\\
J_R(\infty)&=\mathbb E_P(q-u_R)^2,&J_R(r)&=\mathbb E_P(p_R(r)-u_{R,r})^2.
\end{aligned}
\tag{1.6}
$$

$J_L$ is the squared-loss gain from adding the complete future to a left predictor; $J_R$ adds the complete past to a right predictor. For $x_+=\max(x,0)$ and $x_-=\max(-x,0)$, define

$$
s_L(r)=J_L(\infty)-J_L(r),\qquad s_R(r)=J_R(\infty)-J_R(r),\qquad
K_2(R)=\sum_{r\ge R}\bigl(s_L(r)_++s_R(r)_+\bigr).
\tag{1.7}
$$

Entropies use nats and $0\log0=0$. Put

$$
h_r=H_P(X_0\mid W_L(r)),\qquad h=H_P(X_0\mid\mathcal P),\qquad
a_r=h_r-h,\qquad \sigma_R=\sum_{k\ge R}a_k.
\tag{1.8}
$$

For stationary binary $P$, $H_P(X_0\mid W_R(r))=h_r$ and $H_P(X_0\mid\mathcal F)=h$. Indeed both finite conditional entropies are $\mathsf H_{r+1}-\mathsf H_r$, where $\mathsf H_n$ is the entropy of a length-$n$ visible block and $\mathsf H_0=0$. Their decreasing limits give the half-line equality. This equates Shannon gaps, not left and right Brier predictors or their squared moments.

## 2. The exact positive-deficit budget

**Theorem 2.1 (Conditional gain-deficit reduction).** For every $\theta\in\Theta_N$ and the actual law of Definition 1.1,

$$
\begin{aligned}
e_L(r)&=d_L(r)+s_L(r),&e_R(r)&=d_R(r)+s_R(r),\\
0\le d_L(r),d_R(r)&\le a_r/2,&s_L(r)_-&\le d_L(r),\quad s_R(r)_-\le d_R(r).
\end{aligned}
\tag{2.1}
$$

The unweighted entropy budget is finite:

$$
\sigma_0=I_P\bigl(\mathcal P;\sigma(X_j:j\ge0)\bigr)
\le H_{J_\theta}(H_0)\le\log N.
\tag{2.2}
$$

For every $R\ge0$, including extended nonnegative sums, the exact nonnegative remainder and its bounds are

$$
\begin{aligned}
\tau_P(R)&=K_2(R)+\sum_{r\ge R}
\bigl(\min\{e_L(r),d_L(r)\}+\min\{e_R(r),d_R(r)\}\bigr),\\
K_2(R)&\le\tau_P(R)\le K_2(R)+\sigma_R.
\end{aligned}
\tag{2.3}
$$

Consequently $\tau_P(0)<\infty$ if and only if $K_2(0)<\infty$. If a separate same-law argument, without an attainment hypothesis, establishes a deterministic finite bound

$$
K_2(R)\le B_2(R),\qquad B_2(R)\longrightarrow0,
\tag{2.4}
$$

for all sufficiently large $R$, then

$$
\tau_P(R)\le\eta_P(R):=\sigma_R+B_2(R)<\infty,
\qquad \eta_P(R)\longrightarrow0
\tag{2.5}
$$

on those radii. All omitted initial radii are finitely many bounded terms. Hypothesis (2.4) is additional; the theorem does not supply it for every finite producer.

Proof. Conditional expectation is orthogonal projection in $L^2(P)$ (Doob, *Stochastic Processes*). For nested fields $\mathcal A\subseteq\mathcal B$,

$$
\mathbb E\bigl(\mathbb E[X_0\mid\mathcal B]-\mathbb E[X_0\mid\mathcal A]\bigr)^2
=\mathbb E\mathbb E[X_0\mid\mathcal B]^2-\mathbb E\mathbb E[X_0\mid\mathcal A]^2.
\tag{2.6}
$$

Apply this established identity along the two paths $W_L(r)\subseteq\mathcal P\subseteq\mathcal E$ and $W_L(r)\subseteq G_L(r)\subseteq\mathcal E$. It gives

$$
\begin{aligned}
e_L(r)&=\mathbb E q^2-\mathbb E p_L(r)^2,&d_L(r)&=\mathbb E u_L^2-\mathbb E u_{L,r}^2,\\
J_L(\infty)&=\mathbb E q^2-\mathbb E u_L^2,&J_L(r)&=\mathbb E p_L(r)^2-\mathbb E u_{L,r}^2.
\end{aligned}
$$

Subtraction proves the left identity in (2.1). The right projection paths prove its right identity without a reversibility assumption. These are conditional Brier gains with the binary loss $(X_0-p)^2$; conditional scoring and squared posterior discrepancies are mature tools [Dawid–Lauritzen–Parry, §4.2, Example 4.4 and equation (14)][DLP]. The full-product strict-propriety implication under positive distributions is not needed on the no11 domain.

For nested binary posteriors $v=\mathbb E[X_0\mid\mathcal A]$ and $u=\mathbb E[X_0\mid\mathcal B]$, the entropy chain rule gives

$$
\mathbb E D\bigl(\operatorname{Ber}(u)\Vert\operatorname{Ber}(v)\bigr)
=H(X_0\mid\mathcal A)-H(X_0\mid\mathcal B).
\tag{2.7}
$$

For $0<v<1$, the divergence as a function of $u$ has second derivative $1/[u(1-u)]\ge4$, value zero and derivative zero at $u=v$. Thus $D(\operatorname{Ber}(u)\Vert\operatorname{Ber}(v))\ge2(u-v)^2$, including the limits $u=0,1$. On $v=0,1$, nesting forces $u=v$ almost surely. Applying (2.7) to the left predictors yields $d_L(r)\le a_r/2$. The block-entropy equalities in Definition 1.3 yield the same bound for $d_R(r)$. No positivity premise is used.

The finite hidden cut and entropy chain rules are reused information-theoretic facts (Cover–Thomas, *Elements of Information Theory*, Chapter 2). Under (1.2), conditioning on $H_0$ separates the emitted past from the emitted coordinates at and after zero. Data processing bounds their mutual information by $H_{J_\theta}(H_0)$. For a finite future block,

$$
I_P(\mathcal P;X_0,\ldots,X_{n-1})=\mathsf H_n-nh=\sum_{k=0}^{n-1}a_k.
\tag{2.8}
$$

The second equality follows by stationary conditional entropy chain rules. Increasing finite future blocks gives (2.2). Conditional entropies of the binary target converge by bounded conditional projection, so $a_r\ge0$ and $a_r\to0$. Since their sum is finite, $\sigma_R\to0$. Neither a hidden-state classification requirement nor a mixing assumption enters this argument.

For each side, $e=d+s\ge0$ and $d\ge0$ imply $s_-\le d$ and the scalar identity

$$
e=s_++\min\{e,d\}.
$$

Sum this nonnegative identity first over finitely many radii, then take increasing limits. The remainder is at most $\sum_{r\ge R}(d_L(r)+d_R(r))\le\sigma_R$, proving (2.3) without subtracting infinite series. This also proves the finiteness equivalence. Combining (2.4), (2.3) and $\sigma_R\to0$ gives (2.5). $\square$

The theorem pays $\sum_r(d_L(r)+d_R(r))$ and $\sum_r(s_L(r)_-+s_R(r)_-)$ by at most $\log N$. It isolates the unpaid positive deficit rather than showing it integrable. For example, the additional inequalities $J_L(r)\ge J_L(\infty)$ and $J_R(r)\ge J_R(\infty)$ at all sufficiently large radii would imply $\tau_P(R)\le\sigma_R$ there; those gain inequalities are not automatic.

The weighted allowance $\tau_P(R)\le\sum_{k\ge R}(k-R+1)a_k$ from [Entropy moment][EM] remains a sufficient supplier when its weighted moment is finite. Theorem 2.1 requires no weighted moment in its conditional conclusion. It establishes neither a finite-hidden law outside that supplier with verified finite $K_2(0)$ nor strict enlargement of verified supplier domains.

## 3. The deleted-center Shannon cut

**Definition 3.1 (Cut gains and their signed deficit).** Define remote fields $\mathcal L_r=\sigma(X_j:j<-r)$ and $\mathcal R_r=\sigma(X_j:j>r)$, and set

$$
\begin{aligned}
\chi_L(r)&=I_P(\mathcal L_r;\mathcal F\mid W_L(r)),&
\chi_R(r)&=I_P(\mathcal P;\mathcal R_r\mid W_R(r)),\\
b_L(r)&=H_P(X_0\mid G_L(r))-H_P(X_0\mid\mathcal E),&
b_R(r)&=H_P(X_0\mid G_R(r))-H_P(X_0\mid\mathcal E),\\
k_L(r)&=\sigma_{r+1}-\chi_L(r),&k_R(r)&=\sigma_{r+1}-\chi_R(r),\\
K_H(R)&=\sum_{r\ge R}\bigl(k_L(r)_++k_R(r)_+\bigr),&
\Gamma&=h-H_P(X_0\mid\mathcal E).
\end{aligned}
\tag{3.1}
$$

Mutual informations of half-line fields mean increasing finite-block limits. The finite cut in (2.2) bounds all the cut quantities used below; no entropy of an infinite record is subtracted from another infinite entropy.

**Proposition 3.2 (Exact cut identity and conditional Shannon allowance).** For either side $A=L,R$,

$$
\begin{aligned}
b_A(r)&=\sigma_r-\chi_A(r)=a_r+k_A(r),&0\le e_A(r)&\le b_A(r)/2,\\
k_L(r)&=\Gamma-I_P(X_0;\mathcal F\mid W_L(r)),&
k_R(r)&=\Gamma-I_P(X_0;\mathcal P\mid W_R(r)).
\end{aligned}
\tag{3.2}
$$

In particular $b_A(r)\le a_r$ is equivalent to $\chi_A(r)\ge\sigma_{r+1}$, a condition not implied by contiguous-present monotonicity. Moreover

$$
K_H(R)\le\sum_{r\ge R}(b_L(r)+b_R(r))\le K_H(R)+2\sigma_R,
\qquad \tau_P(R)\le\sigma_R+\tfrac12K_H(R).
\tag{3.3}
$$

A separately proved $K_H(R)\le B_H(R)<\infty$ with $B_H(R)\to0$ therefore supplies $\eta_P(R)=\sigma_R+B_H(R)/2$, without an attainment premise. This is an additional budget; the finite-hidden cut argument above does not establish it.

Proof. The stationary cut at $-r$ has the same information $\sigma_0$ as the cut at zero. Its chain rule and (2.8) give

$$
\begin{aligned}
I_P(\mathcal L_r;\sigma(X_j:j\ge0)\mid W_L(r))
&=\sigma_0-I_P(\mathcal L_r;W_L(r))\\
&=\sigma_0-\sum_{k<r}a_k=\sigma_r.
\end{aligned}
\tag{3.4}
$$

Split the target on the left into $\mathcal F$ and $X_0$. The resulting identity is $\sigma_r=\chi_L(r)+I_P(\mathcal L_r;X_0\mid G_L(r))=\chi_L(r)+b_L(r)$. Since $\sigma_r=a_r+\sigma_{r+1}$, this proves the first left identity. Also $H(X_0\mid G_L(r))=h_r-I(X_0;\mathcal F\mid W_L(r))$, proving the formula for $k_L$. Reversing the visible coordinates and using their equal block-entropy gaps proves the right identities; no reversed hidden kernel is required.

Apply (2.7) and its Bernoulli divergence bound to $q$ and $p_A(r)$ to obtain $e_A(r)\le b_A(r)/2$. From $b_A=a_r+k_A\ge0$, one has $k_A(r)_-\le a_r$ and $k_A(r)_+\le b_A(r)\le k_A(r)_++a_r$. Nonnegative summation proves (3.3).

Conditional co-information and the distinction between contiguous-present and erased-center conditioning are mature tools [Ara–James–Crutchfield, §§II.1–II.4][AJC]. Their signed information decomposition does not supply a sign for $k_A(r)$. In (3.4) the target includes $X_0$; in $\chi_A(r)$ it is deleted. Thus a contiguous-present monotonicity statement does not establish the stronger cut comparison in (3.2). Proposition 4.1 gives its same-law failure with both neighbors retained. $\square$

## 4. A fixed lawful radius-one obstruction

**Proposition 4.1 (The $p=3/5$ XOR certificate).** In the state order $(a_0,a_1,b_0,b_1)$, let

$$
\lambda=(1/5,3/10,1/5,3/10),\qquad
M_0=\begin{pmatrix}
0&0&2/5&0\\0&0&0&3/5\\1&0&0&0\\0&1&0&0
\end{pmatrix},\qquad
M_1=\begin{pmatrix}
0&0&0&3/5\\0&0&2/5&0\\0&0&0&0\\0&0&0&0
\end{pmatrix}.
\tag{4.1}
$$

This is one member of the previously studied four-state XOR family, with its complementary-spin tail mechanism reused in the fixed-state tail setting [Fixed-state tails][XOR]. The producer itself and its tail mechanism are not new constructions here. For its actual law $P$, $q=X_0$ almost surely, and the moments and gains at radius one are exactly

$$
\begin{aligned}
\mathbb E q^2&=6/25,\\
\mathbb E u_L^2=\mathbb E u_R^2=\mathbb E p_L(1)^2=\mathbb E p_R(1)^2&=3/25,\\
\mathbb E u_{L,1}^2=\mathbb E u_{R,1}^2&=36/475,\\
e_L(1)=e_R(1)=J_L(\infty)=J_R(\infty)&=3/25,\\
d_L(1)=d_R(1)=J_L(1)=J_R(1)&=21/475,\\
s_L(1)=s_R(1)&=36/475>0.
\end{aligned}
\tag{4.2}
$$

With $H_b(t)=-t\log t-(1-t)\log(1-t)$,

$$
h=\tfrac12H_b(3/5),\qquad h_1=\tfrac{19}{25}H_b(6/19),\qquad
b_L(1)=b_R(1)=h>a_1=h_1-h,
\tag{4.3}
$$

and

$$
e_L(1),e_R(1)>a_1/2,\qquad \chi_L(1),\chi_R(1)<\sigma_2.
\tag{4.4}
$$

These failed comparisons occur with both forcing neighbors retained and with the full opposite half-line. Nevertheless this fixed law has a finite actual tail. More precisely, for $\beta=2\sqrt6/5<1$,

$$
\tau_P(R)\le\frac{\beta^{\lfloor R/2\rfloor+1}}{2(1-\beta)}\longrightarrow0.
\tag{4.5}
$$

Proof. The rows of $M_0+M_1$ sum to one. Its incoming masses at $b_0,b_1$ are $(1/5)(2/5)+(3/10)(2/5)=1/5$ and $(1/5)(3/5)+(3/10)(3/5)=3/10$; the incoming $a$ masses equal the corresponding $b$ masses. Hence $\lambda A=\lambda$. Every one ends at a $b$ state, whose one row is zero, so $M_1^2=0$. Thus (4.1) is in the original $\Theta_4$. It is irreducible of period two, with positive stationary state masses. Some legal cylinders still have zero mass: $1001$ cannot place both ones on the same active parity. This does not remove that word from the objective.

To describe this same stationary joint law, take independent two-sided spins $S_k\sim\operatorname{Ber}(p)$, $p=3/5$, and an independent uniform phase $Z\in\{0,1\}$. Set

$$
X_{2k+Z}=S_k\mathbin\oplus S_{k+1},\qquad X_{2k+Z+1}=0.
\tag{4.6}
$$

At an active coordinate the state moves $a_{S_k}\to b_{S_{k+1}}$ with the indicated emitted parity; at a separator it moves $b_{S_{k+1}}\to a_{S_{k+1}}$ emitting zero. The state masses are precisely $\lambda$. Uniform phase and shift invariance of the independent spins give stationarity on the original bit clock, not on a substituted active-only clock.

Each complete visible half-line contains infinitely many active ones almost surely: disjoint spin pairs provide independent trials with positive one probability. It therefore identifies the active parity. Its adjacent spin parities determine the half-line spins up to complementation. The two candidates have limiting one frequencies $3/5$ and $2/5$; the strong law selects the actual candidate. At an active center the full past determines $S_0$ and the full future determines $S_1$, so the exterior determines $X_0=S_0\oplus S_1$. At a separator the center is already zero. This proves $q=X_0$.

At an active center, $X_{-1}=X_1=0$ are certain separators. Adding $X_{-1}$ to the complete future supplies no information about the independent $S_0$, so $p_L(1)=u_R$; directly, $p_R(1)=u_L$. At a separator, $u_L,u_R,p_L(1),p_R(1)$ vanish. The one-half-line predictor at an active center is $p$ or $1-p$ according as its known adjacent spin is zero or one. Thus

$$
\mathbb E q^2=\tfrac12\,2p(1-p)=6/25,\qquad
\mathbb E u_L^2=\mathbb E u_R^2
=\tfrac12\bigl((1-p)p^2+p(1-p)^2\bigr)=3/25.
\tag{4.7}
$$

Legality and stationarity give $P(X_{-1}=0)=P(X_1=0)=19/25$, and

$$
P(X_0=1\mid X_{-1}=0)=P(X_0=1\mid X_1=0)=6/19.
$$

On a neighbor-one fiber the predictor is zero. Therefore both radius-one predictive second moments are $(19/25)(6/19)^2=36/475$. Substitution in the projection identities of Theorem 2.1 proves every value in (4.2).

The complete past predicts a Bernoulli parity only on the active half of the coordinates, giving $h=H_b(p)/2$. The single-neighbor predictor gives the stated $h_1$. Since the whole-exterior entropy is zero and $p_L(1)=u_R$, $p_R(1)=u_L$, both erased-center entropy gaps are $h$.

Concavity yields $H_b(3/5)\ge(4/5)\log2$, whereas $H_b(6/19)\le\log2$. Hence $2h-h_1\ge(1/25)\log2>0$, proving $b_A(1)>a_1$. For the squared-loss comparison, Jensen's inequality gives

$$
H_b(3/5)\ge-\log\bigl((3/5)^2+(2/5)^2\bigr)=\log(25/13)\ge12/19.
$$

The last inequality follows from $\log t\ge2(t-1)/(t+1)$ for $t\ge1$. Also $\log2<7/10$, since the first four terms of the exponential series at $7/10$ sum to $12013/6000>2$. Thus

$$
a_1<\frac{133}{250}-\frac6{19}=\frac{1027}{4750}<\frac6{25}=2e_A(1).
\tag{4.8}
$$

This proves the first comparison in (4.4). The cut identity $b_A(1)=a_1+\sigma_2-\chi_A(1)$ proves the second.

For completeness, use the existing complementary-block tail mechanism on this same law. At an active center a radius-$r$ retained side contains $m=\lfloor r/2\rfloor$ adjacent active parities. The complete opposite half-line fixes the opposite endpoint spin. Therefore

$$
e_L(r)=e_R(r)=\tfrac12v_m,\qquad
v_m=\mathbb E\operatorname{Var}(S_0\mid S_{-m}\oplus S_{-m+1},\ldots,S_{-1}\oplus S_0).
\tag{4.9}
$$

The conditioning list is empty at $m=0$. The reversed spin block has the same law, giving the right equality only for this explicit example. Each parity block has two complementary spin completions of masses $a,b$. Its contribution to $v_m$ is $ab/(a+b)\le\sqrt{ab}/2$. Here $ab=[p(1-p)]^{m+1}$, and the $2^m$ complementary pairs give the reused bound $v_m\le[2\sqrt{p(1-p)}]^{m+1}/4=\beta^{m+1}/4$. These are deterministic expected variances, not random stability constants. Each $m$ corresponds to two bit radii, so summing (4.9) from $R$, with a possible extra term when $R$ is odd, proves (4.5). Since $24<25$, $\beta<1$; in particular $\tau_P(0)\le\beta/[2(1-\beta)]<\infty$. The example refutes the per-radius bridge, not fixed-law summability. $\square$

## 5. The existing response interface and the unchanged target

**Definition 5.1 (Multiword consumer).** For any actual stationary legal $P$, set

$$
q_i=\mathbb E_P[X_i\mid\sigma(X_j:j\ne i)],\qquad
q_{k,i}=\mathbb E_P[X_i\mid X_{i-k},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+k}],
$$

$$
\mathfrak d(P)=\mathbb E_P(X_0-q)^2,\qquad D_k(P)=\mathbb E_P(X_0-q_{k,0})^2.
\tag{5.1}
$$

The notation $\mathfrak d(P)$ is the stationary risk denoted $d(P)$ in [Multiword][MW], and is distinct from the predictive gaps $d_L,d_R$. Its established interface is $\mathfrak d(P)=\inf_kD_k(P)\le c_\star\le\bar c:=3-2\sqrt2$. For $C=[1,L]$, take a bounded $f:B_L\to\mathbb R$, $f_C=f(X_C)$, $F=\max_{B_L}|f|$, with actual nullity

$$
\mathbb E_P[f_C\mid\mathcal H_C]=0,\qquad \mathcal H_C=\sigma(X_j:j\notin C).
\tag{5.2}
$$

With $I_R=[1-R,L+R]$, define

$$
U_{R,k}(P,f)=\sum_{i\in I_R}\mathbb E_P[f_C(X_i-q_{k,i})^2].
\tag{5.3}
$$

All overlaps, endpoints and original block seams remain. Under $P_\theta$ the finite marginal on $[1-R-k,L+R+k]$ determines (5.3). Positive exterior atoms use their actual conditional ratios; zero-total atoms have zero contribution, and radius zero uses empty exterior words.

The established [Multiword, Theorem 3.1][MW] consumes a bound $\tau_P(R)\le\eta_P(R)$ proved without attainment. Under same-law attainment $\mathfrak d(P)=c_\star$, it gives

$$
|U_{R,k}(P,f)|\le F\eta_P(R)+2(L+2R)F\sqrt{\frac{c_\star}{k+1}}.
\tag{5.4}
$$

Thus an independently established budget (2.4) can be inserted as $\eta_P(R)=\sigma_R+B_2(R)$; the alternative verified Shannon budget in Proposition 3.2 can also be inserted. A verified strict violation with $\bar c$ in place of $c_\star$ implies $\mathfrak d(P)<c_\star$. This is reuse of the consumer, not a new response theorem. A deficit decomposition alone supplies neither a null direction nor a nonzero complete response. A law-dependent allowance also supplies no uniform allowance for a parameter family.

**Open Problem 5.2 (Full-domain finite attainment or separation).** Retain

$$
C_N=\sup_{\theta\in\Theta_N}\mathfrak d(P_\theta),\qquad
U_{N,k}=\max_{\theta\in\Theta_N}D_k(P_\theta).
\tag{5.5}
$$

The original question is whether some exact finite $\theta$ attains $c_\star$, or $C_N<c_\star$ for every finite $N$. The full-domain separation criterion retained in [Multiword, §9][MW] is

$$
\forall N\ge1\ \exists k,m\ge1:\qquad U_{N,k}<\kappa_m/(m+1).
\tag{5.6}
$$

Theorem 2.1 leaves the universal fixed-law tail obligation precisely at $K_2(0)<\infty$. No proof of that condition for every $\theta\in\Theta_N$, and no one fixed lawful finite producer with divergent $\tau_P(0)$, is given. A divergent sufficient weighted entropy moment would not alone prove actual-tail divergence. Proposition 4.1 is a finite-tail witness against the direct comparison, not a full-domain maximum estimate. Productive directions or other strict certificates for all remaining hypothetical finite attainers are separate obligations.

The mathematical addition to the weighted-moment formulation and the existing response interface is the exact conditional-budget reduction and the fixed-law radius-one failure of the unweighted bridge. Orthogonal projection, conditional Brier scoring, signed co-information, finite-cut entropy and the XOR producer/tail mechanism are attributed supporting steps. No universal positive-deficit integrability, exact finite attainer, all-$N$ strict separation, efficient constants or radii, hidden minimality, empirical machine-learning benefit or worldwide novelty is asserted.

[MW]: FIB_LEGAL_EDGE_LOAD_MULTIWORD_RESPONSE_STABILITY_AND_VANISHING_TAIL_CERTIFICATE.md
[EM]: FIB_LEGAL_EDGE_LOAD_ENTROPY_ERASURE_INFLUENCE_WEIGHTED_MOMENT.md
[XOR]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[DLP]: https://arxiv.org/html/1104.2224v2
[AJC]: https://arxiv.org/html/1507.00672v1

Doob: J. L. Doob, *Stochastic Processes*, conditional expectations and martingale convergence. Cover–Thomas: Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory*, Chapter 2, entropy chain rules and data processing. Dawid–Lauritzen–Parry: A. Philip Dawid, Steffen Lauritzen and Matthew Parry, *Proper Local Scoring Rules on Discrete Sample Spaces*. Ara–James–Crutchfield: Pooneh M. Ara, Ryan G. James and James P. Crutchfield, *The Elusive Present: Hidden Past and Future Dependency and Why We Build Models*.

## 追加锚（本行以下为增补区）
