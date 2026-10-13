# FIB harmonic-edge load: primitive component moment reduction and terminal-posterior KL

## 1. Law, entropy and erased-site quantities

**Definition 1.1 (Original lawful producer and clock).** For every finite $N\ge1$, let

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,\ M_0,M_1\ge0,
\ A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.1}
$$

The row $\lambda$ and matrices have dimensions $N$ and $N\times N$. For $\theta\in\Theta_N$, use its actual two-sided stationary marked joint $J=J_\theta$, with hidden state $H_i$ just before emitting $X_i$:

$$
J(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}).
\tag{1.2}
$$

Its visible law is $P=P_\theta$, with $P([w])=\lambda M_w\mathbf1$ and $M_\varnothing=I$. Equation (1.1) implies $P(X_iX_{i+1}=0)=1$ at every integer $i$. It does not require entrywise $M_1^2=0$ on states of zero stationary mass. Structural zeros, reducibility, periods, deterministic outputs and noncontractive marked products are allowed.

Every integer coordinate is one emitted bit. Finite paths have endpoint insertion convention $w_0=w_{n+1}=0$, without a first-to-last constraint. Ordered matrix products preserve every original seam. Conditioning and expectation always refer to this $J$ and its visible marginal $P$; a change of presentation does not change their meaning.

**Definition 1.2 (Entropy moments).** For any stationary finite-alphabet law $Z$, use natural logarithms and set

$$
\begin{aligned}
H_n(Z)&=H(Z_0,\ldots,Z_{n-1}),\qquad H_0(Z)=0,\\
h_k(Z)&=H(Z_0\mid Z_{-k},\ldots,Z_{-1})=H_{k+1}(Z)-H_k(Z),\\
h(Z)&=\lim_{k\to\infty}h_k(Z),\qquad a_k^Z=h_k(Z)-h(Z)\ge0,\\
R_n^Z&=\sum_{k\ge n}a_k^Z,\qquad
T_Z=\sum_{k\ge0}(k+1)a_k^Z=\sum_{n\ge0}R_n^Z,\\
\eta_Z^{\mathrm{ent}}(K)&=\sum_{n\ge K}R_n^Z
=\sum_{k\ge K}(k-K+1)a_k^Z.
\end{aligned}
\tag{1.3}
$$

All series are nonnegative extended quantities. The name transient information and its weighted entropy-gap expression are classical [CF]. Entropies expressed in bits must be multiplied by $\ln2$ here; the emitted-bit clock and squared losses are unchanged.

**Definition 1.3 (Actual erasure fields).** For the original binary law, write

$$
\begin{aligned}
q&=\mathbb E_P[X_0\mid\sigma(X_j:j\ne0)],\\
p_{L,r}&=\mathbb E_P[X_0\mid\sigma(X_{-r},\ldots,X_{-1},X_1,X_2,\ldots)],\\
p_{R,r}&=\mathbb E_P[X_0\mid\sigma(\ldots,X_{-2},X_{-1},X_1,\ldots,X_r)],\\
e_L(r)&=\mathbb E_P(q-p_{L,r})^2,\qquad e_R(r)=\mathbb E_P(q-p_{R,r})^2,\\
\tau_X(R)&=\sum_{r\ge R}(e_L(r)+e_R(r)).
\end{aligned}
\tag{1.4}
$$

Empty finite blocks are used at $r=0$. For $r\ge1$, both forcing neighbors are retained, so neighbor-one fibers contribute zero. At $r=0$ one forcing neighbor can be omitted, and no such cancellation is imposed. Null atoms have zero weight; versions there do not change any expectation. The entropy–erasure comparison of [EE] is the supporting estimate

$$
e_L(r),e_R(r)\le\tfrac12R_r^X,\qquad
\tau_X(R)\le\eta_X^{\mathrm{ent}}(R).
\tag{1.5}
$$

It retains the complete opposite half-line in each predictor, holds before any attainment hypothesis, and allows an infinite right side. No block-label or hidden-state error is identified with an erased-site defect.

## 2. Exact reduction to primitive marked components

**Theorem 2.1 (Moment reduction with finite label cost).** A fixed $\theta\in\Theta_N$ admits an equality-preserving reduction of its moment question to finitely many positive-weight primitive stationary marked block components. The precise accounting is as follows.

For any finite stationary finite-alphabet mixture $P=\sum_cw_cP_c$, $w_c>0$, $\sum_cw_c=1$, let $C$ be its actual mixture label and

$$
b_n=H(C\mid X_0,\ldots,X_{n-1}),\qquad
b_\infty=H(C\mid\sigma(X_j:j\ge0)).
$$

Then, with permanent label ambiguity explicitly removed,

$$
\begin{aligned}
R_n^P&=\sum_cw_cR_n^{P_c}+b_n-b_\infty,\\
T_P&=\sum_cw_cT_{P_c}+\sum_{n\ge0}(b_n-b_\infty).
\end{aligned}
\tag{2.1}
$$

These are equalities in $[0,\infty]$, even when some component moments diverge. If the $P_c$ are the visible laws of finitely many stationary irreducible finite marked chains, there are deterministic law-dependent constants $A_{\mathrm{lab}}<\infty$ and $0<\rho<1$ such that

$$
0\le b_n-b_\infty\le A_{\mathrm{lab}}(n+1)\rho^n.
\tag{2.2}
$$

Identical visible laws are grouped only for label learning; periodic hidden classes remain admissible.

For any integer $D\ge1$, set $Y_t=(X_{Dt},\ldots,X_{Dt+D-1})$. Its exact block entropy gaps obey

$$
a_k^Y=\sum_{j=Dk}^{Dk+D-1}a_j^X,\qquad
T_Y\le T_X\le D T_Y.
\tag{2.3}
$$

Choose $D$ divisible by the periods of all positive-mass closed hidden classes. There is then a stationary block mixture $Y\sim\sum_cw_cQ_c$, where each $Q_c$ has a finite marked presentation whose hidden transition matrix is primitive. Consequently

$$
T_X<\infty\quad\Longleftrightarrow\quad
T_{Q_c}<\infty\ \text{for every }c\text{ with }w_c>0.
\tag{2.4}
$$

The reduction includes every member of the original domain; it assumes neither positivity of all marked entries nor initial aperiodicity or unifilarity.

Proof. The entropy chain rule [CT] gives

$$
H_n(P)=\sum_cw_cH_n(P_c)+H(C)-b_n.
$$

The last two terms have bounded difference. Dividing by $n$ proves $h(P)=\sum_cw_ch(P_c)$. Taking consecutive differences yields

$$
a_k^P=\sum_cw_ca_k^{P_c}+b_k-b_{k+1}.
\tag{2.5}
$$

Every summand is nonnegative. Conditional entropy of a finite label converges along increasing fields, so $b_n\downarrow b_\infty$ and

$$
b_n-b_\infty=\sum_{k\ge n}(b_k-b_{k+1}).
$$

Nonnegative summation first gives the $R_n$ identity and then (2.1). In particular, no unproved boundary condition $n(b_n-b_\infty)\to0$ is used. Summing from any $K\ge0$ also gives

$$
\eta_P^{\mathrm{ent}}(K)=\sum_cw_c\eta_{P_c}^{\mathrm{ent}}(K)
+\sum_{n\ge K}(b_n-b_\infty).
\tag{2.6}
$$

To prove (2.2), let $G=g(C)$ identify exactly equal visible component laws. A stationary irreducible finite hidden path law is shift-ergodic even when periodic; its visible factor is ergodic. Distinct stationary ergodic visible laws have different cylinder probabilities and are distinguished almost surely by future word frequencies. Thus $G$ is measurable on the whole future. Within a group, the observation law is independent of $C$, conditional on $G$. Hence

$$
b_n=H(G\mid X_0,\ldots,X_{n-1})+H(C\mid G),\qquad
b_\infty=H(C\mid G).
\tag{2.7}
$$

This identifies the permanent ambiguity, including duplicate presentations, without demanding that $C$ itself become observable.

With one visible group, (2.7) makes the residual identically zero. Otherwise, for each pair of distinct groups choose one word with different probabilities. The resulting finite collection $\mathcal W$ gives distinct vectors $v_g=(P_g([w]))_{w\in\mathcal W}$. Their minimum pairwise sup-norm distance $\Delta$ is positive. A nearest-vector estimate $\widehat G_n$ based on empirical word frequencies is correct whenever every coordinate differs from its true value by less than $\Delta/3$.

Here is a deterministic probability bound for those deviations that does not require mixing. In one component, the supported marked-edge chain $(H_t,X_t,H_{t+1})$ is finite irreducible. Its supported length-$L$ window chain $Z_t$ is also finite irreducible: connect the last hidden endpoint of one supported window to the first endpoint of another, then append the target window. For a word $w$ of length $L$, its indicator is a bounded state function $f_w(Z_t)$ of this chain. Let $K_w$ and $\pi_w$ denote its transition and stationary row.

The finite-chain Poisson equation has a bounded real solution

$$
(I-K_w)g=f_w-\pi_w f_w.
$$

Indeed, eigenvalue $1$ is simple for a finite irreducible transition matrix; its range condition is precisely zero stationary mean. Other unit-circle eigenvalues do not obstruct this equation. With $m$ observed windows, the standard Poisson–martingale decomposition gives

$$
\sum_{t=0}^{m-1}(f_w(Z_t)-\pi_w f_w)
=g(Z_0)-g(Z_m)+\sum_{t=0}^{m-1}(g(Z_{t+1})-K_wg(Z_t)).
\tag{2.8}
$$

The last sum is a martingale with increments bounded by $2\|g\|_\infty$. If $G_w=\|g\|_\infty>0$ and $m\delta\ge4G_w$, Azuma's inequality [AZ] yields

$$
\Pr\left(\left|m^{-1}\sum_{t=0}^{m-1}f_w(Z_t)-\pi_wf_w\right|\ge\delta\right)
\le2\exp\left(-\frac{m\delta^2}{32G_w^2}\right).
\tag{2.9}
$$

The endpoint term has absolute value at most $2G_w$, which explains the threshold. If $g$ is constant, the centered indicator is zero and there is no deviation. Put $m=n-L+1$ and $\delta=\Delta/3$. A finite union over words and components, absorbing the finitely many short prefixes, gives $\Pr(\widehat G_n\ne G)\le A_0\rho^n$ for some deterministic $A_0<\infty$, $\rho<1$.

For $s=|G|\ge2$, Fano's inequality [CT] bounds

$$
H(G\mid X_0,\ldots,X_{n-1})
\le H_{\mathrm{bin}}(p_n)+p_n\ln(s-1),\qquad p_n=\Pr(\widehat G_n\ne G).
$$

For sufficiently large $n$, use $H_{\mathrm{bin}}(u)\le u\ln(1/u)+u$ and monotonicity of $u\ln(1/u)$ on $0\le u\le e^{-1}$. The exponential probability bound therefore gives (2.2), after increasing $A_{\mathrm{lab}}$ for the remaining $n$. This proof applies to exact real parameters and periodic chains. The related exponential discrimination result [KS, Proposition 1 and Theorem 4.7] requires singular whole-output laws; different stationary ergodic groups meet that condition. Unequal overlapping initial-state laws within one component need not meet it.

For blocking, stationarity gives $H_n(Y)=H_{Dn}(X)$ and $h(Y)=Dh(X)$. Consecutive differences give the first identity in (2.3). For $Dk\le j<D(k+1)$,

$$
k+1\le j+1\le D(k+1),
$$

so nonnegative summation gives both moment comparisons, also for infinite moments.

A finite stationary hidden chain has mass only on closed irreducible classes. Omitting zero-mass states in this analysis changes no cylinder of the actual law. A class of period $d$ splits into cyclic phases. For $d\mid D$, the restriction of $A^D$ to any one phase $S_c$ is irreducible and aperiodic, hence primitive: some power has every entry positive. This does not assert positivity of the individual marked matrices.

The corresponding weight and stationary row are

$$
w_c=\sum_{i\in S_c}\lambda_i>0,\qquad
\lambda_c(i)=\lambda_i/w_c\quad(i\in S_c).
$$

For a bit word $w$ of length $D$, its block-marked matrix is

$$
L_{c,w}=(M_w)_{S_c\times S_c},\qquad
\sum_{w\in\{0,1\}^D}L_{c,w}=(A^D)_{S_c\times S_c}.
\tag{2.10}
$$

These follow from finite Markov phase structure and distributivity. They specify the actual joint conditional on class and phase at $H_0$, observed at times $Dt$. Each $\lambda_c$ is stationary for its restricted $A^D$. The $Q_c$ are stationary under the block shift; a phase-conditioned law is not asserted stationary under a one-bit shift.

All block-internal and block-to-block no11 constraints are inherited from (1.2). Illegal or null words have zero mass. Block endpoints do not create new open-path endpoints. Applying (2.1)–(2.2) to these finite primitive block components, and then (2.3), proves (2.4). Reducibility and period costs therefore cannot independently cause a divergent fixed-law moment: such divergence must occur in a positive-weight primitive component obtained in (2.10). $\square$

## 3. Terminal learning and the original-bit allowance

**Theorem 3.1 (Fixed-cut KL supplier with its invisible slack).** Let $J$ be any actual finite stationary marked producer over a finite alphabet, $Z$ its output, and $U=H_0$ its hidden state at the initial cut. Put

$$
\mathcal F_n=\sigma(Z_0,\ldots,Z_{n-1}),\qquad
\mathcal F_\infty=\sigma(Z_j:j\ge0),
$$

$$
p_n(i)=\Pr_J(U=i\mid\mathcal F_n),\qquad
p_\infty(i)=\Pr_J(U=i\mid\mathcal F_\infty),\qquad
\ell_n=H_J(U\mid\mathcal F_n)-H_J(U\mid\mathcal F_\infty).
$$

The terminal posterior concerns the same initial state $U$ for every $n$, rather than the moving state $H_n$. Then

$$
\begin{aligned}
\ell_n&=\mathbb E_J D_{\mathrm{KL}}(p_\infty\Vert p_n),\\
\ell_n&=R_n^Z+I_J(U;Z_{n:\infty}\mid Z_{-\infty:n-1}),\\
0&\le R_n^Z\le\ell_n,\qquad
T_Z\le\sum_{n\ge0}\ell_n.
\end{aligned}
\tag{3.1}
$$

The conditioning notation $Z_{-\infty:n-1}$ includes the whole past and the prefix. Permanent hidden ambiguity $H_J(U\mid\mathcal F_\infty)$ is subtracted. The slack is nonnegative and can remain relevant when observations are sufficient for prediction but do not resolve hidden information.

Apply this construction separately to each actual primitive block joint in (2.10), with its initial cut state $U_c$, and write $\ell_{c,n}$ for its residual. Under the separate hypothesis

$$
\sum_{n\ge0}\ell_{c,n}<\infty\qquad\text{for every }c\text{ with }w_c>0,
\tag{3.2}
$$

the original erased-site quantities have the allowance, for $K=\lfloor R/D\rfloor$,

$$
\begin{aligned}
\tau_X(R)&\le\eta_X(R),\\
\eta_X(R)&:=D\left[\sum_cw_c\sum_{n\ge K}\ell_{c,n}
+\sum_{n\ge K}(b_n-b_\infty)\right]<\infty,\\
\eta_X(R)&\longrightarrow0\qquad(R\to\infty).
\end{aligned}
\tag{3.3}
$$

Here $b_n=H(C\mid Y_0,\ldots,Y_{n-1})$ uses the actual class-and-phase mixture of $Y$, and $b_\infty$ uses its whole future. Its label contribution is proved summable by Theorem 2.1, independently of (3.2). In particular,

$$
\sum_{n\ge K}(b_n-b_\infty)
\le A_{\mathrm{lab}}\rho^K\left(\frac{K+1}{1-\rho}+\frac{\rho}{(1-\rho)^2}\right).
\tag{3.4}
$$

Neither the proof of (3.1) nor the reduction supplies (3.2) universally.

For its conditional multiword application, fix $C_0=[1,L]$, $f_{C_0}=f(X_{C_0})$, $F=\max|f|<\infty$, under the original $P=P_\theta$, with

$$
\mathbb E_P[f_{C_0}\mid\sigma(X_j:j\notin C_0)]=0.
$$

Let $q_i$ be the full erased-site posterior at $i$ and $q_{r,i}$ its radius-$r$ counterpart under this same $P$, retaining all other sites in $[i-r,i+r]$. Define

$$
I_R=[1-R,L+R],\qquad
U_{R,r}(P,f)=\sum_{i\in I_R}\mathbb E_P[f_{C_0}(X_i-q_{r,i})^2],\qquad
S_P(f)=\sum_{i\in\mathbb Z}\mathbb E_P[f_{C_0}(X_i-q_i)^2].
$$

Under (3.2), the complete response is absolutely convergent. If this same law attains $c_\star$ of Definition 5.2, [MW, Theorem 3.1] gives

$$
|U_{R,r}(P,f)|\le F\eta_X(R)+2(L+2R)F\sqrt{\frac{c_\star}{r+1}}.
\tag{3.5}
$$

Proof. Set $\mathcal B=\sigma(Z_j:j<0)$ and $\mathcal V_n=\sigma(Z_j:j\ge n)$. The hidden cut screens $\mathcal B$ from $(\mathcal F_n,\mathcal V_n)$ given $U$. The standard finite-cut entropy bound [CT] therefore gives

$$
E_Z:=I_J(\mathcal B;\mathcal F_\infty)
=\sum_{k\ge0}a_k^Z\le H_J(U)<\infty.
\tag{3.6}
$$

For each finite $n$, the entropy chain rule and stationarity give $H(Z_{0:n-1}\mid\mathcal B)=nh(Z)$, so

$$
I_J(\mathcal B;\mathcal F_n)=H_n(Z)-nh(Z)=\sum_{k<n}a_k^Z.
$$

Increasing-field limits of mutual information give

$$
R_n^Z=I_J(\mathcal B;\mathcal V_n\mid\mathcal F_n).
\tag{3.7}
$$

Screening persists after conditioning on $\mathcal F_n$, and two expansions of $I_J(U,\mathcal B;\mathcal V_n\mid\mathcal F_n)$ yield

$$
\begin{aligned}
I_J(U;\mathcal V_n\mid\mathcal F_n)
&=I_J(\mathcal B;\mathcal V_n\mid\mathcal F_n)
+I_J(U;\mathcal V_n\mid\mathcal B,\mathcal F_n)\\
&=R_n^Z+I_J(U;\mathcal V_n\mid\mathcal B,\mathcal F_n).
\end{aligned}
\tag{3.8}
$$

The left side is exactly $\ell_n$. Each term is finite and nonnegative; finite-block chain rules followed by increasing-field limits justify the whole-half-line formula.

For the KL identity, $\mathbb E_J[p_\infty(i)\mid\mathcal F_n]=p_n(i)$. On an atom where $p_n(i)=0$, this forces $p_\infty(i)=0$ almost surely. Use $0\log0=0$ and the usual KL support convention. Conditional averaging gives

$$
\begin{aligned}
\mathbb E_J\sum_i p_\infty(i)(-\ln p_n(i))
&=\mathbb E_J\sum_i p_n(i)(-\ln p_n(i))=H_J(U\mid\mathcal F_n),\\
\mathbb E_J\sum_i p_\infty(i)(-\ln p_\infty(i))
&=H_J(U\mid\mathcal F_\infty).
\end{aligned}
$$

Nonnegative truncation justifies the cross-entropy identity at null coordinates. Both expectations are finite because $U$ is finite. Their difference proves (3.1); it is the standard conditional logarithmic-score/KL identity [CT], used here for the fixed initial cut. Summing (3.7)–(3.8) gives the moment bound.

To transfer to the original clock, write $R=DK+s$, $0\le s<D$. For every original gap index $j\ge R$, putting $k=\lfloor j/D\rfloor$ gives

$$
j-R+1\le D(k-K+1).
$$

Consequently (2.3) and nonnegativity imply

$$
\eta_X^{\mathrm{ent}}(R)\le D\eta_Y^{\mathrm{ent}}(K)
=D\left[\sum_cw_c\eta_{Q_c}^{\mathrm{ent}}(K)+\sum_{n\ge K}(b_n-b_\infty)\right].
$$

For each actual component, (3.1) gives $\eta_{Q_c}^{\mathrm{ent}}(K)\le\sum_{n\ge K}\ell_{c,n}$. Apply (1.5) to the original binary $X$, rather than to a phase posterior or block-erasure surrogate. This proves (3.3). Equation (3.4) sums (2.2). Finitely many integrable component residuals and the proved label cost have tails tending to zero.

The allowance is proved independently of attainment and concerns exactly the actual defects in [MW, equation (2.1)]. That source's exterior projection lemma gives absolute convergence of $S_P(f)$. Substituting (3.3) into its Theorem 3.1 gives (3.5). All expectations, full-posterior losses and finite posteriors belong to the same original-bit law. $\square$

**Assumption 3.2 (Expected-integrability boundary).** Condition (3.2) is an additional supplier assumption; its validity for all inherited finite primitive presentations remains unresolved. For a specified component, a deterministic expected bound $\ell_{c,n}\le C_c\alpha_c^n$, $0<\alpha_c<1$, or $\ell_{c,n}\le C_c(n+1)^{-1-\epsilon_c}$, $\epsilon_c>0$, suffices. No such bound is asserted for arbitrary components.

Finite-state posterior martingale convergence gives $p_n\to p_\infty$ and $0\le\ell_n\downarrow0$, with $\ell_n\le\ln|U|$. Those facts alone do not imply summability. An almost-sure rate with an uncontrolled random constant also does not supply the required expected bound. The nonnegative slack in (3.1) makes this a sufficient, presentation-dependent condition, rather than a necessary condition for finite visible $T_Z$.

Singular-output discrimination concerns the finite label problem of Theorem 2.1. Within a primitive component, output laws conditional on different initial states can overlap. In the edge-matrix setting of [DK, Lemma 2 and Proposition 11], the prefix likelihood ratio has a finite limit almost surely under its denominator law, and the zero-exponent event is the event of a positive limit. These qualitative statements do not themselves bound the expected KL settling residual by a summable sequence. They neither establish nor refute (3.2).

The same cited certificate detects any nonzero complete conditional-null response when this allowance vanishes, and a justified strict finite violation excludes that law's attainment. Equation (3.5) supplies no productive direction or sign for an arbitrary producer. There is no uniform-$N$ rate, efficiently acquired constant or effective radius assertion.

## 4. A primitive lawful obstruction to a finite predictive-state shortcut

**Proposition 4.1 (Infinite finite-history predictive orbit with finite moment).** The existing exact law of [MW, §4] at $t=10^{-100}$ has a primitive four-state hidden transition matrix, but infinitely many future-distinct finite-history beliefs. Its moment is nevertheless finite. Thus the primitive hidden dimension does not make its canonical reachable-belief prediction operator finite.

Proof. Use the existing law, without changing its parameter or output clock. Its relevant matrices and stationary row are

$$
\begin{gathered}
b=2/3,\quad q=1/3,\quad p=3/10+100t,\quad a=1-p,\quad Z=b+2p,\quad l=(b,p)/Z,\\
B=\begin{pmatrix}a-pt&pt\\b(1-t)&bt\end{pmatrix},\quad
C_0=\begin{pmatrix}t&1-t\\2t&1-2t\end{pmatrix},\quad D_0=\operatorname{diag}(p,q),\\
M_0=\begin{pmatrix}B&0\\C_0&0\end{pmatrix},\quad
M_1=\begin{pmatrix}0&D_0\\0&0\end{pmatrix},\quad
\lambda=(l,lD_0)=(b,p,bp,pq)/Z.
\end{gathered}
\tag{4.1}
$$

The stationary identities $\lambda M_0=(l,0)$ and $\lambda M_1=(0,lD_0)$, row sums, and $M_1^2=0$ give exactly the lawful joint (1.2). The positive free-to-free and tail-to-free transfers, positive event edges and a positive free-state self-loop make $A$ irreducible and aperiodic. This reuses the law's admissibility, rather than introducing a new producer or a slow-parameter family.

Here $0<p<q$ and $0<t<1/2$. Exact algebra gives

$$
\det B=bt(a-p)>0,\qquad
lB=\frac{(b-p(1+q)t,\ p(1+q)t)}{Z},\qquad
\det\begin{pmatrix}l\\lB\end{pmatrix}
=\frac{p(1+q)(b+p)t-bp}{Z^2}<0.
\tag{4.2}
$$

For the last sign, $b+p<1$ and $(1+q)t=(4/3)t<b$. All entries of $B$ are positive. Its discriminant is $(B_{11}-B_{22})^2+4B_{12}B_{21}>0$, and its trace and determinant are positive. Hence its two eigenvalues $\beta_1>\beta_2>0$ are distinct, while (4.2) says that $l$ is not an eigenrow.

Every $0^{n+1}$ has positive probability, and its current hidden belief is

$$
\frac{\lambda M_0^{n+1}}{\lambda M_0^{n+1}\mathbf1}
=\left(\frac{lB^n}{lB^n\mathbf1},0\right),\qquad n\ge0.
\tag{4.3}
$$

If two normalized free rows in (4.3) agreed at $n>m$, invertibility of $B^m$ would make $l$ an eigenrow of $B^{n-m}$. The distinct positive eigenvalues have distinct positive powers, so $B^{n-m}$ has exactly the same eigenrows as $B$. This contradicts (4.2). The rows are therefore pairwise distinct.

For a free belief $(u,1-u)$, the next-one probability is $up+(1-u)q$. Since $p\ne q$, distinct rows give distinct next-output probabilities and hence distinct future laws. Quotienting these reachable beliefs only by equality of future laws cannot turn this orbit into a finite set.

On the other hand, every row of $M_0$ reaches free state $1$ with positive mass. Thus every hidden-state pair is path-mergeable by the word $0$. The stationary irreducible edge-model theorem [TR, Definition 6, Lemma 5 and Theorem 2] supplies exponential entropy-gap convergence for this law. Its flag-block formulation requires a block length coprime to the hidden period and a flag for every target state; path-mergeability supplies such a block. It does not require this law itself to be flag-state. After converting entropy units and absorbing finitely many initial terms, there exist law-dependent $C<\infty$ and $0<\alpha<1$ with $a_k^X\le C\alpha^k$. Therefore $T_X\le C/(1-\alpha)^2<\infty$. The actual-tail estimate of [MW, Lemma 6.2] is also already available for this law. Neither rate is a new law or a universal supplier. $\square$

For this proposition, the relevant operator is the canonical mixed-state operator $W$ on reachable normalized rows $\lambda M_w/(\lambda M_w\mathbf1)$, whose transitions are induced by observed symbols [RC1, §IV]. The underlying hidden matrix $A$ and $W$ act on different state spaces. The spectral transient-information expression of [RC2, §III] uses $W$, in its stated spectral setting, with weights $(1-\beta)^{-2}$; [RC1, §VI.1] restricts its operator treatment to at most countably infinite spectrum. An infinite operator requires its own spectral and summability hypotheses. The finite primitive matrix $A$ does not identify $W$ with a finite matrix; a spectral proof must separately justify the applicable operator assumptions and sum interchanges.

The proposition concerns finite-prefix beliefs of this presentation. It does not prove infinitely many recurrent causal states, exclude every alternative finite presentation or finite representation of a selected statistic, or exhibit divergent $T_X$ or divergent actual erasure influence. Divergence of a sufficient entropy or hidden-learning bound would also require a separate argument before any actual-tail divergence conclusion.

## 5. Remaining mathematical questions and attribution

**Open Problem 5.1 (Primitive residual moment).** For every positive-weight primitive marked block joint inherited from (1.1) by (2.10), determine whether $\sum_nR_n^{Q_c}<\infty$. A sufficient stronger route is $\sum_n\mathbb E_{J_c}D_{\mathrm{KL}}(p_{c,\infty}\Vert p_{c,n})<\infty$; this is the unresolved hypothesis (3.2), not a proved universal theorem. If that stronger route fails, the exact slack (3.1) still leaves the visible moment to be determined. No fixed lawful finite producer with divergent visible moment is established here.

**Definition 5.2 (Original open-path optimization).** Let $B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\}$ and let $E(\Gamma_n)$ contain all unordered legal Hamming-one edges, with the endpoint convention of Definition 1.1. Put $\gamma(u,v)=uv/(u+v)$ for $u+v>0$ and $\gamma(0,0)=0$, and

$$
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}\gamma(\mu_w,\mu_z),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}\kappa_n/n.
$$

Use the stationary risk identity cited in [MW, §1]: $d(P)=\mathbb E_P(X_0-q)^2\le c_\star$. Define

$$
D_r(P)=\mathbb E_P(X_0-q_{r,0})^2,\qquad
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
$$

**Open Problem 5.3 (Unchanged finite-attainer or all-$N$ target).** Decide whether an exact finite $\theta$ attains $c_\star$, or $C_N<c_\star$ for every finite $N$. The complete-domain separation criterion cited in [MW, §9] is

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\kappa_m/(m+1).
$$

Even a universal solution of Open Problem 5.1 would supply only independent tail control for a response argument. It would not supply productive conditional-null directions for all remaining hypothetical finite attainers or strict bounds on the full-domain maxima. Structural-zero, zero-mass, reducible, periodic, null, forced, all-zero, endpoint and seam cases remain in this target.

The compound mathematical content is the ambiguity-subtracted finite-mixture and phase moment reduction, the fixed-cut expected terminal-posterior KL comparison with exact slack, and their original-bit conditional allowance. The canonical finite-history orbit calculation obstructs a particular finite-hidden spectral transfer. The entropy–erasure bridge belongs to [EE], the multiword response consumer and exact four-state law to [MW]. Entropy bookkeeping, finite hidden-cut information, phase structure, word-frequency identification, Poisson–martingale concentration and conditional KL scoring are supporting established mathematics. The cited spectral, discrimination and path-mergeability results are used only within their stated hypotheses. These attributions express a compound derivation and its boundaries, without literature-wide priority, hidden minimality, empirical learning benefit or completion of the original target.

[EE]: FIB_LEGAL_EDGE_LOAD_ENTROPY_ERASURE_INFLUENCE_WEIGHTED_MOMENT.md
[MW]: FIB_LEGAL_EDGE_LOAD_MULTIWORD_RESPONSE_STABILITY_AND_VANISHING_TAIL_CERTIFICATE.md
[CF]: https://arxiv.org/abs/cond-mat/0102181 "J. P. Crutchfield and D. P. Feldman, Regularities unseen, randomness observed: Levels of entropy convergence"
[CT]: https://doi.org/10.1002/047174882X "T. M. Cover and J. A. Thomas, Elements of Information Theory, second edition: entropy chain rules, conditional information, KL and Fano bounds"
[AZ]: https://doi.org/10.2748/tmj/1178243286 "K. Azuma, Weighted sums of certain dependent random variables"
[KS]: https://arxiv.org/html/1507.02314v2 "S. Kiefer and A. P. Sistla, Distinguishing Hidden Markov Chains"
[DK]: https://arxiv.org/html/2207.14088v2 "O. Darwin and S. Kiefer, On the Sequential Probability Ratio Test in Hidden Markov Models"
[TR]: https://arxiv.org/html/1211.6181v2 "N. F. Travers, Exponential Bounds for Convergence of Entropy Rate Approximations in Hidden Markov Models Satisfying a Path-Mergeability Condition"
[RC1]: https://arxiv.org/html/1705.08042v1 "P. M. Riechers and J. P. Crutchfield, Spectral Simplicity of Apparent Complexity, Part I: The Nondiagonalizable Metadynamics of Prediction"
[RC2]: https://arxiv.org/html/1706.00883v1 "P. M. Riechers and J. P. Crutchfield, Spectral Simplicity of Apparent Complexity, Part II: Exact Complexities and Complexity Spectra"

## 追加锚（本行以下为增补区）
