# FIB harmonic-edge load: entropy gaps and actual erased-center influence

## 1. One stationary law and the exact erased-center fields

**Definition 1.1 (Actual visible law and clock).** Let $P$ be a normalized, two-sided stationary probability law on $\{0,1\}^{\mathbb Z}$, and let $X_i$ be its coordinate variables. Every entropy, conditional expectation and information quantity below belongs to this same $P$. The integer index is the original emitted-bit clock. Write $X_{a:b}=(X_a,\ldots,X_b)$, taking this block to be empty when $a>b$. An empty block generates the trivial sigma-field. All sigma-fields may be completed under the law being used.

For integers $r,R\ge0$, define

$$
\begin{aligned}
\mathcal E_0&=\sigma(X_j:j\ne0),\\
\mathcal G_L(r)&=\sigma(X_{-r:-1},X_j:j\ge1),\\
\mathcal G_R(r)&=\sigma(X_j:j\le-1,X_{1:r}),\\
q&=\mathbb E_P[X_0\mid\mathcal E_0],\\
p_{L,r}&=\mathbb E_P[X_0\mid\mathcal G_L(r)],\qquad
p_{R,r}=\mathbb E_P[X_0\mid\mathcal G_R(r)],\\
e_L(r)&=\mathbb E_P[(q-p_{L,r})^2],\qquad
e_R(r)=\mathbb E_P[(q-p_{R,r})^2],\\
\tau_P(R)&=\sum_{r\ge R}\bigl(e_L(r)+e_R(r)\bigr).
\end{aligned}
\tag{1.1}
$$

These are the actual-tail fields of [Multiword, §2][MW] and [Predictive, Definition 1.2][PQ]. Each predictor retains its entire opposite half-line. The series has values in $[0,\infty]$. Conditional expectations have measurable $[0,1]$ versions; changes on null sets do not change any displayed quantity.

**Definition 1.2 (Original legal finite producer).** The legal shift is

$$
\mathcal X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\text{ for every }i\}.
$$

With the presentation convention of [Predictive, §1][PQ], for each finite $N\ge1$ retain the entire domain

$$
\Theta_N=\left\{(\lambda,M_0,M_1):
\begin{array}{l}
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\\
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\\
\lambda M_1^2\mathbf1=0
\end{array}\right\}.
\tag{1.2}
$$

Here $\lambda$ is a row and $M_x$ are $N\times N$ matrices. Put $M_w=M_{w_1}\cdots M_{w_n}$ and $M_\epsilon=I$. The actual stationary joint law and its visible marginal are

$$
\begin{aligned}
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_{a:b}=x_{a:b})
&=\lambda_{h_a}\prod_{i=a}^b M_{x_i}(h_i,h_{i+1}),\\
P_\theta([w]_a)&=\lambda M_w\mathbf1.
\end{aligned}
\tag{1.3}
$$

The stationary visible law is supported on $\mathcal X$. Structural zeros, zero stationary masses, reducibility, periodicity and noncontractive boundaries remain in $\Theta_N$. Entrywise $M_1^2=0$ is not imposed on unpruned presentations. The universal comparison below needs only Definition 1.1, without legality or a finite producer.

**Boundary 1.3 (Null, endpoint and forcing fibers).** Zero-total finite fibers have zero weight and require no likelihood division. A coarse conditional posterior equal to zero or one forces every refined conditional posterior to equal that same endpoint almost surely on that coarse event.

For a legal $P$, the full posterior $q$ is zero when either neighbor is one. For $r\ge1$, both fields in (1.1) retain both neighbors, so both defects vanish on these forcing events. At $r=0$, $\mathcal G_L(0)$ omits $X_{-1}$ and $\mathcal G_R(0)$ omits $X_1$. Only a forcing neighbor actually retained by the field forces its predictor to zero; no blanket vanishing of radius-zero defects follows from legality.

## 2. Entropy gaps and mature projection identities

**Definition 2.1 (Natural entropy units).** All logarithms are natural. Let

$$
b(t)=-t\log t-(1-t)\log(1-t),\qquad b(0)=b(1)=0,
$$

and define conditional entropy by $H_P(X_0\mid\mathcal A)=\mathbb E_P b(\mathbb E_P[X_0\mid\mathcal A])$. Put

$$
\begin{aligned}
h_k&=H_P(X_0\mid X_{-k:-1}),\qquad k\ge0,\\
h&=H_P(X_0\mid X_j:j\le-1)=\lim_{k\to\infty}h_k,\\
a_k&=h_k-h,\qquad
B_P(n)=H_P(X_{0:n-1}),\qquad B_P(0)=0.
\end{aligned}
\tag{2.1}
$$

Thus $h_0=H_P(X_0)$ and $a_k\ge0$. The sequence $h_k$ decreases. The infinite-field identity follows from bounded conditional-projection convergence and continuity of $b$ on $[0,1]$ [Probability][K]. Entropy chain rules and conditional mutual information are used in their standard finite-alphabet form [Information, §2.5][CT]; finite target variables conditioned on infinite fields are obtained by these same bounded limits.

**Lemma 2.2 (Identical forward and backward entropy gaps).** For every $k\ge0$,

$$
H_P(X_0\mid X_{1:k})=h_k=B_P(k+1)-B_P(k).
\tag{2.2}
$$

Consequently the stationary reversed visible process $Y_i=X_{-i}$ has exactly the entropy gaps $a_k$ of $P$.

Proof. The entropy chain rule and stationarity give

$$
\begin{aligned}
H_P(X_0\mid X_{-k:-1})
&=H_P(X_{-k:0})-H_P(X_{-k:-1})
=B_P(k+1)-B_P(k),\\
H_P(X_0\mid X_{1:k})
&=H_P(X_{0:k})-H_P(X_{1:k})
=B_P(k+1)-B_P(k).
\end{aligned}
$$

For $k=0$ both conditioning blocks are empty. Increasing-field limits give the common infinite conditional entropy $h$. This is a stationary block-entropy identity, without a time-reversibility assumption. $\square$

**Lemma 2.3 (Reused Bernoulli KL projection).** Let $Z$ be binary, let $\mathcal A\subseteq\mathcal B$ be sigma-fields under one probability law, and set $p=\mathbb E[Z\mid\mathcal A]$, $t=\mathbb E[Z\mid\mathcal B]$. If $\mathcal B=\sigma(\mathcal A,L)$ for a finite variable $L$, then

$$
2\mathbb E(t-p)^2
\le\mathbb E D\bigl(\operatorname{Ber}(t)\Vert\operatorname{Ber}(p)\bigr)
=I(Z;L\mid\mathcal A).
\tag{2.3}
$$

Proof. The equality is the standard conditional-relative-entropy formula [Information][CT]. The inequality is the Bernoulli specialization of the relative-entropy/total-variation inequality [Pinsker][PI]. To fix its natural-log constant, for $0<p<1$ the function

$$
D\bigl(\operatorname{Ber}(t)\Vert\operatorname{Ber}(p)\bigr)
=t\log(t/p)+(1-t)\log((1-t)/(1-p))
$$

has value and first derivative zero at $t=p$, and second derivative $1/[t(1-t)]\ge4$ for $0<t<1$. Integration and continuity at $t=0,1$ give $D\ge2(t-p)^2$. On $\{p=0\}$, the tower property and $t\ge0$ give $t=0$ almost surely; on $\{p=1\}$ they give $t=1$. Those fibers contribute zero with $D(\operatorname{Ber}(p)\Vert\operatorname{Ber}(p))=0$. Null fibers contribute nothing. This is a mature projection inequality, not an additional entropy-rate hypothesis. $\square$

## 3. The same-law lift to whole-half-line erasure

**Theorem 3.1 (Stationary entropy-to-actual-erasure comparison).** For every stationary binary law $P$ and every integer $r\ge0$,

$$
e_L(r)\le\frac12\sum_{k\ge r}a_k,\qquad
e_R(r)\le\frac12\sum_{k\ge r}a_k.
\tag{3.1}
$$

An infinite right side is allowed. Neither comparison assumes attainment, a finite hidden presentation, full support, irreducibility, mixing, unifilarity or recoverability of a hidden state.

Proof. Fix integers $s\ge r$ and $m\ge0$, and use the actual finite blocks

$$
W=X_{-r:-1},\qquad L_s=X_{-s:-r-1},\qquad V_m=X_{1:m}.
$$

Define, under the same $P$,

$$
q_{s,m}=\mathbb E_P[X_0\mid W,L_s,V_m],\qquad
p_{r,m}=\mathbb E_P[X_0\mid W,V_m].
$$

Lemma 2.3 gives

$$
2\mathbb E_P(q_{s,m}-p_{r,m})^2
\le I_P(X_0;L_s\mid W,V_m).
\tag{3.2}
$$

The entropy chain rule lifts this center information to the whole finite future block:

$$
\begin{aligned}
I_P(X_{0:m};L_s\mid W)
&=I_P(V_m;L_s\mid W)+I_P(X_0;L_s\mid W,V_m),\\
I_P(X_0;L_s\mid W,V_m)
&\le I_P(X_{0:m};L_s\mid W).
\end{aligned}
\tag{3.3}
$$

The nonnegative term in the first line is retained before taking the inequality. This step does not assert that arbitrary enlargement of a conditioning field increases conditional mutual information.

Enlarge only the remote-past variable, keeping the target $X_{0:m}$ and conditioning block $W$ fixed. Write $\mathcal L_\infty=\sigma(X_j:j\le-r-1)$. Since conditional entropy decreases under this enlargement,

$$
I_P(X_{0:m};L_s\mid W)
\le I_P(X_{0:m};\mathcal L_\infty\mid W).
\tag{3.4}
$$

The latter quantity has the exact chain-rule expansion

$$
\begin{aligned}
I_P(X_{0:m};\mathcal L_\infty\mid W)
&=H_P(X_{0:m}\mid W)-H_P(X_{0:m}\mid X_j:j\le-1)\\
&=\sum_{j=0}^{m}
\left[H_P(X_j\mid X_{-r:j-1})
-H_P(X_j\mid X_i:i\le j-1)\right]\\
&=\sum_{j=0}^{m}(h_{r+j}-h)
=\sum_{j=0}^{m}a_{r+j}.
\end{aligned}
\tag{3.5}
$$

For the first entropy in each summand, the already revealed coordinates form one contiguous past block of length $r+j$. For the second, the whole remote past and the revealed block form the entire past before $j$. Stationarity therefore supplies exactly $h_{r+j}$ and $h$. The entropy limits are legitimate because the target block is finite.

For fixed $m$, let $s\to\infty$. Bounded conditional projections converge in $L^2(P)$ to

$$
q_{\infty,m}=\mathbb E_P[X_0\mid X_j:j\le-1,\ X_{1:m}],
$$

whereas $p_{r,m}$ does not depend on $s$. Equations (3.2)–(3.5) and norm continuity give

$$
2\mathbb E_P(q_{\infty,m}-p_{r,m})^2
\le\sum_{j=0}^{m}a_{r+j}.
\tag{3.6}
$$

Now let $m\to\infty$. These two increasing projection families converge in $L^2(P)$ to exactly $q$ and $p_{L,r}$ in (1.1), respectively. Their difference converges in $L^2(P)$, so its squared norm converges. The nonnegative right sides increase to $\sum_{k\ge r}a_k$. This proves the left comparison while retaining the entire future.

Apply the same argument to the stationary visible process $Y_i=X_{-i}$. Its full exterior is $\mathcal E_0$, its left-truncated field is $\mathcal G_R(r)$, and its entropy gaps equal $a_k$ by Lemma 2.2. This proves the right comparison while retaining the entire past. No reversed hidden-model theorem is used.

The proof includes $r=0$ with $W$ empty, $s=r$ with $L_s$ empty, and $m=0$ with $V_m$ empty. The endpoint argument in Lemma 2.3 and bounded projection limits handle structural zeros and null fibers without divisions. $\square$

## 4. Weighted moments and quantitative allowances

**Theorem 4.1 (Weighted actual-tail comparison).** Define

$$
\eta_{H,P}(R)=\sum_{k\ge R}(k-R+1)a_k,\qquad
T_P=\sum_{k\ge0}(k+1)a_k.
\tag{4.1}
$$

For every stationary binary $P$ and every $R\ge0$,

$$
\tau_P(R)\le\eta_{H,P}(R).
\tag{4.2}
$$

Both sides may be infinite.

Proof. Adding (3.1) cancels the two factors $1/2$. Tonelli's theorem for nonnegative terms [Probability][K] gives

$$
\begin{aligned}
\tau_P(R)
&\le\sum_{r\ge R}\sum_{k\ge r}a_k\\
&=\sum_{k\ge R}\left(\sum_{r=R}^{k}1\right)a_k
=\sum_{k\ge R}(k-R+1)a_k.
\end{aligned}
$$

Thus no unproved absolute-convergence or boundary-rate assumption is used in the interchange. $\square$

**Corollary 4.2 (Additional finite weighted-moment hypothesis).** If $T_P<\infty$, then

$$
\tau_P(0)\le T_P,\qquad
\tau_P(R)\le\eta_{H,P}(R)\longrightarrow0.
\tag{4.3}
$$

Proof. Theorem 4.1 applies, and

$$
0\le\eta_{H,P}(R)\le\sum_{k\ge R}(k+1)a_k\longrightarrow0.
$$

This is a deterministic bound on expected squared influence. It needs no random prefactor or expectation-integrability deduction from an almost-sure rate. The hypothesis is a weighted entropy moment; it is not inferred from finite hiddenness. $\square$

**Corollary 4.3 (Exponential entropy-gap supplier).** Suppose the same actual $P$ has constants $C<\infty$ and $0<\alpha<1$ with $0\le a_k\le C\alpha^k$ for every $k\ge0$. Then

$$
\begin{aligned}
e_L(r),e_R(r)&\le\frac{C\alpha^r}{2(1-\alpha)},\\
\tau_P(R)&\le\frac{C\alpha^R}{(1-\alpha)^2},\qquad
T_P\le\frac{C}{(1-\alpha)^2}.
\end{aligned}
\tag{4.4}
$$

Proof. Sum the geometric tail in (3.1), and use $\sum_{j\ge0}(j+1)\alpha^j=(1-\alpha)^{-2}$ in (4.1). Both one-sided influences are included in the displayed tail constant. $\square$

**Corollary 4.4 (A nonexponential sufficient profile).** If $a_k\le C(k+1)^{-2-\delta}$ for $C<\infty$ and $\delta>0$, then $T_P<\infty$ and, for $R\ge1$,

$$
\tau_P(R)\le\eta_{H,P}(R)\le\frac{C}{\delta}R^{-\delta}.
\tag{4.5}
$$

Proof. Bound $(k-R+1)a_k\le C(k+1)^{-1-\delta}$ and compare the decreasing positive series with $\int_R^\infty x^{-1-\delta}\,dx$. The initial term is finite. This is a conditional entropy profile, without asserting its realization by a particular finite producer. $\square$

**Convention 4.5 (Bits).** If $a_k^{\mathrm{bits}}$ is defined using base-two entropy, then $a_k=(\log2)a_k^{\mathrm{bits}}$. Accordingly (3.1) has coefficient $(\log2)/2$ against the bit-entropy tail, and (4.2) has coefficient $\log2$ against its weighted bit-entropy sum. A bit-unit exponential constant $C_{\mathrm{bits}}$ becomes $C=(\log2)C_{\mathrm{bits}}$ in (4.4). The squared-loss units and the emitted-bit clock do not change.

## 5. Finite hiddenness supplies an unweighted budget

**Proposition 5.1 (Reused finite-cut information bound).** For an actual $\theta\in\Theta_N$, define $E_P=\sum_{k\ge0}a_k$. Then

$$
E_P
=I_{P_\theta}(X_{-\infty:-1};X_{0:\infty})
\le H_{J_\theta}(H_0)\le\log N.
\tag{5.1}
$$

This bounds excess entropy, without supplying the weighted condition $T_P<\infty$.

Proof. For every $n\ge1$, the standard entropy chain rule gives

$$
\begin{aligned}
I_P(X_{-\infty:-1};X_{0:n-1})
&=B_P(n)-nh
=\sum_{k=0}^{n-1}a_k.
\end{aligned}
$$

Increasing the finite future block gives the information of the two complete half-lines. Under the actual joint factorization (1.3), $H_0$ separates $X_{-\infty:-1}$ from $X_{0:\infty}$ conditionally. The standard data-processing bound therefore gives $I_P(\text{past};\text{future})\le H_{J_\theta}(H_0)$ [Information][CT]. No division by a zero stationary mass is involved, and the entropy of an $N$-valued variable is at most $\log N$. This mature finite-cut argument also holds for reducible and periodic stationary presentations. $\square$

**Proposition 5.2 (Classical transient information and the weight).** If $E_P<\infty$, the classical transient-information expression satisfies

$$
\sum_{n\ge0}\bigl(E_P+nh-B_P(n)\bigr)
=\sum_{k\ge0}(k+1)a_k=T_P
\tag{5.2}
$$

as an extended nonnegative identity.

Proof. Since $B_P(n)-nh=\sum_{k=0}^{n-1}a_k$, each summand on the left is $\sum_{k\ge n}a_k$. Nonnegative Tonelli summation yields the right side. This is the transient information of [Crutchfield–Feldman, §V, equation (63) and Proposition 12][CF], with their $h_\mu(L)-h_\mu$ equal to $a_{L-1}$ and their bit units converted to natural units. The quantity and its entropy interpretation are reused; the actual erased-center upper bound is the composite application in §§3–4. $\square$

**Limitation 5.3 (Missing weighted finiteness).** An unweighted summable sequence need not have a finite first weighted moment. Consequently (5.1) alone does not activate Corollary 4.2. Finiteness of $T_{P_\theta}$ for every member of every $\Theta_N$ is unresolved here. Failure of this sufficient moment condition would not itself imply divergence of $\tau_{P_\theta}(0)$, since (4.2) is only an upper bound. No fixed-$N$ uniform allowance is supplied.

## 6. A restricted Travers flag-block supplier

**Assumption 6.1 (Positive-mass irreducible component and flag block).** Consider a closed irreducible component of an actual finite producer that has positive stationary mass. Normalize its stationary row to $\pi$, restrict its marked matrices to this component, and denote its stationary visible law by $P_c$. All component states then have $\pi_i>0$. Let $d$ be the period of its hidden transition matrix $A_c$.

Assume there is an integer $n\ge1$ with $\gcd(n,d)=1$ such that, for every target state $j$, there is a length-$n$ word $w_j$ of positive $P_c$ probability satisfying

$$
(M_{w_j}\mathbf1)_i>0
\quad\Longrightarrow\quad
(M_{w_j})_{ij}>0
\qquad\text{for every component state }i.
\tag{6.1}
$$

This says that every state capable of emitting $w_j$ can reach $j$ on that same word. It permits other endpoints and branching. It is precisely the flag-state condition for the block presentation with marked matrices $M_w$, as in [Travers, Definitions 7–8][TR]. The block transition matrix is $A_c^n$; the coprimality condition preserves its irreducibility and stationary row. This block presentation is a supplier construction; every final tail radius still counts original emitted bits.

**Corollary 6.2 (Restricted entropy and actual-erasure rate).** Under Assumption 6.1, there exist law-dependent constants $C_c<\infty$ and $0<\alpha_c<1$ such that

$$
a_{c,k}\le C_c\alpha_c^k,\qquad
\tau_{P_c}(R)\le
\frac{C_c\alpha_c^R}{(1-\alpha_c)^2}\longrightarrow0.
\tag{6.2}
$$

These conclusions are independent of attainment.

Proof. [Travers, §2.2.1 and Theorem 2][TR] assumes a finite irreducible hidden chain in its stationary law. In its edge-emitting convention, the marked matrices are exactly those of this component. Its Theorem 2, using Theorem 1 and Lemma 6, gives a number $\rho_c<1$ with

$$
\limsup_{k\to\infty}a_{c,k}^{1/(k+1)}\le\rho_c
$$

on the original symbol clock. Here its length-$t$ entropy estimate $h(t)$ is our $h_{c,t-1}$. Changing entropy units does not change this root bound. Choose $\rho_c<\beta<\alpha_c<1$. For all sufficiently large $k$, $a_{c,k}\le\beta^{k+1}\le\alpha_c^k$. Increase a finite constant $C_c$ to cover the finitely many initial terms. Corollary 4.3 now gives (6.2). The entropy-rate theorem is reused, rather than reproved as an erasure theorem. $\square$

**Corollary 6.3 (Additional path-mergeability condition).** Suppose a positive-mass irreducible component satisfies: for every distinct state pair $i,j$ there are a common word $w$ and state $v$ such that $(M_w)_{iv}>0$ and $(M_w)_{jv}>0$. Then it satisfies the supplier in Corollary 6.2.

Proof. This is [Travers, Definition 6][TR]. Its Lemma 5 supplies a flag-state block of length relatively prime to the component period. Apply Corollary 6.2. The path-mergeability construction is a reused sufficient condition. $\square$

**Limitation 6.4 (Periodic and noncontractive scope).** Assumption 6.1 covers a periodic component only when the stated period-compatible flag block exists. It is not a consequence of finite hiddenness, legality or branching. In a hidden chain of period $d>1$, equal-length paths from two different cyclic classes preserve their distinct phase offsets, so they cannot reach the same state. Thus Corollary 6.3's all-pair path-mergeability condition cannot hold across those classes. This obstruction to that sufficient condition does not refute every period-compatible flag-block instance.

Components without the flag-block hypothesis remain covered by the universal comparisons (3.1) and (4.2), with possibly infinite bounds. Their weighted finiteness or another independent actual-tail supplier is still needed. No hidden-state identification, global matrix positivity, uniform-$N$ rate, efficient block length or numerical acquisition of $C_c,\alpha_c$ is asserted.

## 7. Transport across actual visible components

**Proposition 7.1 (Mixture transport with visible labels).** Suppose

$$
P=\sum_{c=1}^J w_cP_c,\qquad
J<\infty,\quad w_c>0,\quad\sum_cw_c=1,
\tag{7.1}
$$

where each $P_c$ is stationary binary. Assume there is a measurable label $Z\in\{1,\ldots,J\}$ such that $P_c(Z=c)=1$, and $Z$ is measurable, modulo $P$-null sets, from each of the two complete visible half-lines $\sigma(X_j:j\le-1)$ and $\sigma(X_j:j\ge1)$. Then

$$
\begin{aligned}
e_{L,P}(r)&=\sum_cw_ce_{L,P_c}(r),\\
e_{R,P}(r)&=\sum_cw_ce_{R,P_c}(r),\\
\tau_P(R)&=\sum_cw_c\tau_{P_c}(R).
\end{aligned}
\tag{7.2}
$$

If every positive-mass component has $T_{P_c}<\infty$, an independent vanishing allowance is

$$
\eta_P(R)=\sum_cw_c\sum_{k\ge R}(k-R+1)a_{c,k}.
\tag{7.3}
$$

If each component instead has the constants of Corollary 6.2, one may use

$$
\eta_P(R)=\sum_cw_c\frac{C_c\alpha_c^R}{(1-\alpha_c)^2}.
\tag{7.4}
$$

Proof. Every field $\mathcal E_0,\mathcal G_L(r),\mathcal G_R(r)$ contains a complete visible half-line, so it contains $Z$. For any one of these fields $\mathcal A$, choose the corresponding component posterior $p_c=\mathbb E_{P_c}[X_0\mid\mathcal A]$. Testing integrals on $D\in\mathcal A$ gives

$$
\int_D\sum_c\mathbf1_{\{Z=c\}}p_c\,dP
=\sum_cw_c\int_Dp_c\,dP_c
=\sum_cw_c\int_DX_0\,dP_c
=\int_DX_0\,dP.
$$

Thus the mixture posterior equals the appropriate component posterior on $\{Z=c\}$. Integrating squared differences gives the first two identities in (7.2); nonnegative summation gives the third. Corollary 4.2 gives (7.3), and Corollary 4.3 gives (7.4). Finitely many components make both allowances finite and vanishing under their respective hypotheses. $\square$

**Proposition 7.2 (When a finite producer supplies the labels).** For an actual stationary finite producer, its positive-mass hidden support decomposes into finitely many closed irreducible classes. Their stationary visible factors are ergodic under the one-bit shift, including periodic hidden classes. Merge classes inducing identical visible laws. The resulting distinct visible laws satisfy the label hypothesis of Proposition 7.1.

Proof. These are standard stationary finite-chain and ergodic-factor facts [Probability][K], with the same-law positive-support convention of [Predictive, §1][PQ]. Stationarity gives no outgoing positive transition from a positive-mass state to a zero-mass state; transient states carry no stationary mass. Taking the actual closed classes therefore decomposes the unchanged joint law, without a full-support assumption.

For each finite visible word, the ergodic theorem gives its limiting empirical frequency on either complete half-line, equal to its cylinder probability under that visible ergodic law. Distinct visible laws differ on a finite cylinder. Their vectors of limiting word frequencies therefore identify the visible component on both half-lines. A countable intersection over words provides measurable labels simultaneously. Periodicity does not prevent ergodicity of the stationary chain under the one-bit shift; no mixing or ergodicity of a block shift is substituted. Identical visible laws cannot be distinguished this way and are merged. $\square$

**Limitation 7.3 (Labels and coverage).** A hidden class label is not automatically a visible label, and a current hidden state or predictive class is not the label in Proposition 7.1. Without its measurable-label hypothesis, (7.2) cannot be obtained merely by averaging component posterior defects. Every retained component has actual positive mass. Zero-mass presentations contribute nothing and supply no rate for $P$. Every positive-mass component needs its own weighted moment or other actual allowance. An all-zero visible component has $a_{c,k}=e_{L,P_c}(r)=e_{R,P_c}(r)=0$; unverified components are not discarded.

## 8. The existing finite-certificate consumer

**Definition 8.1 (Exact consumer interface).** The input to [Multiword, Theorem 3.1][MW] is an independently justified same-law bound

$$
\tau_P(R)\le\eta_P(R)<\infty,\qquad \eta_P(R)\longrightarrow0,
\tag{8.1}
$$

for sufficiently large integer $R$, on the original emitted-bit clock and with exactly the fields (1.1). For a legal $P$, Corollary 4.2 or Proposition 7.1 supplies this input under its explicit additional hypotheses.

The consumer still requires a finite block $C=[1,L]$, a bounded direction $f_C=f(X_C)$ that is conditional-null under this same $P$,

$$
\mathbb E_P[f_C\mid\sigma(X_j:j\notin C)]=0,
$$

and a justified strict finite violation to certify that law's nonattainment. Its finite detectability conclusion additionally uses a nonzero complete response

$$
S_P(f)=\sum_{i\in\mathbb Z}
\mathbb E_P\!\left[f_C(X_i-\mathbb E_P[X_i\mid\sigma(X_j:j\ne i)])^2\right].
$$

The independent tail allowance ensures absolute convergence through [Multiword, Lemma 2.1][MW]. The finite statistic and its proof belong to that consumer and are not reproduced here. Finite marginals, overlapping observation windows, legal seams and zero-total fibers must still be evaluated under the candidate's actual law. Existence of a law-dependent allowance does not acquire usable constants or supply a productive response sign. An attained-law-only tail budget cannot replace (8.1) for an arbitrary candidate.

**Limitation 8.2 (Overlap boundary).** [Predictive, Theorems 2.3 and 3.3][PQ] supplies a different classification-to-actual-loss comparison and a restricted row-unifilar allowance. The entropy comparison here neither assumes that classification succeeds nor asserts that its flag-block domain strictly contains or is disjoint from that supplier or prior positive-word suppliers. Its composite contribution is (3.3)–(3.6): ordinary finite conditional information controls the actual whole-half-line posterior loss under one $P$, and the sum over radii produces the weighted allowance. Mature entropy chain rules, Bernoulli KL projection, transient information, ergodic component transport and Travers entropy rates are reused. No global priority, hidden minimality or empirical inference claim follows.

## 9. The original finite-attainer and all-$N$ gap

**Definition 9.1 (Unchanged original objective).** Retain the complete open-path words

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\}
$$

and all legal Hamming-one edges of their graph $\Gamma_n$. Endpoint insertion uses $w_0=w_{n+1}=0$; there is no first-to-last constraint. Let

$$
\begin{aligned}
g(s,t)&=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\\
\Phi_n(\mu)&=\sum_{\{w,v\}\in E(\Gamma_n)}g(\mu_w,\mu_v),\\
\kappa_n&=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_n\kappa_n/n.
\end{aligned}
$$

All-zero words, endpoint ones, structural zeros and zero-mass vertices remain. [Stationary, §2][S] supplies

$$
d(P)=\lim_n\Phi_n(P_n)/n
=\mathbb E_P(X_0-q)^2\le c_\star
$$

for every stationary legal $P$. Its full-support stationary attainer does not establish an exact finite hidden presentation.

**Open Problem 9.2 (Original arbitrary-finite alternative).** With the full domains (1.2), put

$$
\begin{aligned}
C_N&=\sup_{\theta\in\Theta_N}d(P_\theta),\\
q_{r,0}(P)&=\mathbb E_P[X_0\mid X_{-r:-1},X_{1:r}],\\
D_r(P)&=\mathbb E_P(X_0-q_{r,0}(P))^2,\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
\end{aligned}
$$

Still decide whether an exact finite producer attains $c_\star$, or whether $C_N<c_\star$ for every finite $N$. The compact-domain equivalence retained in [Multiword, Open Problem 9.1][MW] and [Predictive, Open Problem 6.1][PQ] is

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\kappa_m/(m+1).
\tag{9.1}
$$

The entropy allowance supplies neither an exact finite attainer nor these strict full-domain maxima. Productive actual conditional-null directions or other strict certificates covering all remaining hypothetical attainers are still missing. Universal weighted finiteness outside the specified suppliers, or an alternative proof of actual-tail summability, is also unresolved here. No fixed finite law with divergent actual tail is established. Slow convergence across a family is not such a law. The original zero-mass, reducible, periodic, noncontractive, seam, null and endpoint cases remain in this open target; no uniform-$N$ rate or original-target completion is claimed.

## 10. Citations

[Information][CT]: Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory*, second edition, §2.5 for entropy and mutual-information chain rules, and the chapters on entropy rates and data processing.

[Pinsker][PI]: Mark S. Pinsker, *Information and Information Stability of Random Variables and Processes*, relative entropy and total variation. Lemma 2.3 fixes the Bernoulli specialization and natural-log constant explicitly.

[Probability][K]: Olav Kallenberg, *Foundations of Modern Probability*, conditional expectation, martingale convergence, Tonelli's theorem, stationary Markov chains and the ergodic theorem.

[Crutchfield–Feldman][CF]: James P. Crutchfield and David P. Feldman, *Regularities Unseen, Randomness Observed: Levels of Entropy Convergence*, §V, equation (63) and Proposition 12. Their directly observed finite-order Markov synchronization interpretation is not extended to arbitrary hidden producers.

[Travers][TR]: Nicholas F. Travers, *Exponential Bounds for Convergence of Entropy Rate Approximations in Hidden Markov Models Satisfying a Path-Mergeability Condition*, §2.2.1, Definitions 6–8, Theorems 1–2 and Lemmas 5–6.

[CT]: https://onlinelibrary.wiley.com/doi/book/10.1002/047174882X
[PI]: #10-citations
[K]: https://doi.org/10.1007/978-3-030-61871-1
[CF]: https://arxiv.org/html/cond-mat/0102181
[TR]: https://arxiv.org/html/1211.6181v2
[S]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[MW]: FIB_LEGAL_EDGE_LOAD_MULTIWORD_RESPONSE_STABILITY_AND_VANISHING_TAIL_CERTIFICATE.md
[PQ]: FIB_LEGAL_EDGE_LOAD_PREDICTIVE_QUOTIENT_UNIFILAR_ERASURE_TAIL_AND_STRICT_SCOPE.md

## 追加锚（本行以下为增补区）
