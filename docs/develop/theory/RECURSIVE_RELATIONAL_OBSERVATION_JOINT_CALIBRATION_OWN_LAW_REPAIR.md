# Joint calibration repair by one pair of own-law generators

## 1. Complete laws and the unchanged source

**Assumption 1.1 (source and target family).** The source is the once-sampled
depth source of [PAIR, §§2, 11]. Its parameters are $(m,d,\ell,n)=(2,1,2,4)$.
One positive integer $K$ is drawn from one fixed finite or countable
probability prior $\mu$ before the first paid Read. Conditional on this same
$K$, seed and payload letters are independent, with alpha probability
$r_K=F_{K+1}/F_{K+3}$, where $F_0=0,F_1=1$. Assume
$\mu(1),\mu(2)>0$. Write

$$
a=r_1=\frac13,\qquad b=r_2=\frac25,\qquad \lambda=\frac4{15}.
\tag{1.1}
$$

Every supported depth remains a target. Both accepted seeds, all paid
equal-pair rejections and partial parses, all finite returns, the original
records and permissions, third write before latch, fourth completion and
its matching Stop are retained. The renderer $I_c$ at a fixed current-record
fibre inserts the original operation blocks and retains all future letters.
It is injective, preserves complete-law TV, and commutes with deletion of
the next operation and its block [PAIR, §2; PAID, Lemma 2.1.1].

**Definition 1.2 (the PAIR11 carriers).** Put

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta,
$$

$$
\begin{aligned}
\Omega_p&=\{w_{j,c}:j\ge0,\ c=0,1\}\cup\{\infty_p\},\\
\Omega_\beta&=\{\beta\}\cup
 \{\alpha w_{j,c}:j\ge0,\ c=0,1\}\cup\{\infty_\beta\},\\
T_p(j)&=\{w_{n,c}:n\ge j,\ c=0,1\}\cup\{\infty_p\},\\
T_\beta(j)&=\{\alpha w_{n,c}:n\ge j,\ c=0,1\}\cup\{\infty_\beta\}.
\end{aligned}
\tag{1.2}
$$

All subsets of each countable carrier are measurable, and
$d_s(D,D')=\operatorname{TV}(D,D')=\tfrac12\sum_\omega|D(\omega)-D'(\omega)|$.
The compact complete-law spaces are exactly

$$
\begin{aligned}
\mathcal K_p&=\{Q\in\operatorname{Prob}(\Omega_p):
 a\le Q(\alpha)\le b,\ Q(T_p(j))\le\lambda^j\ (j\ge0)\},\\
\mathcal K_\beta&=\{W\in\operatorname{Prob}(\Omega_\beta):
 a\le1-W(\beta)\le b,\ W(T_\beta(j))\le b\lambda^j\ (j\ge0)\}.
\end{aligned}
\tag{1.3}
$$

Their compactness and convexity are [PAIR, Lemma 11.1]. The tail bounds
force their infinite masses to vanish, without deleting the infinite
outcomes or conditioning on completion. Define

$$
\begin{aligned}
u(Q)&=Q(\alpha),& U(Q)&=1-u(Q),&v(W)&=1-W(\beta),\\
\mathcal R_B(Q)(E)&=Q(\beta E)/U(Q),&&
\mathcal R_A(W)(E)&=W(\alpha E)/v(W).
\end{aligned}
\tag{1.4}
$$

Prefixing includes the infinite outcomes. These residuals are normalized
probability measures on the full opposite carriers. A residual of an
arbitrary input need not lie in the opposite $\mathcal K_s$.

**Definition 1.3 (the exact compatible domain).** The domain $\mathfrak C$
consists of Borel probability edges $\Gamma_B$ on
$\mathcal K_p\times\mathcal K_\beta$ and $\Gamma_A$ on the reversed
product such that

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta,
\tag{1.5}
$$

and their conditional successor-law barycentres equal $\mathcal R_B(Q)$
given the entire $Q$, and $\mathcal R_A(W)$ given the entire $W$.
Equivalently, for every bounded Borel input test and every complete atom,

$$
\begin{aligned}
\int\phi(Q)[\mathcal R_B(Q)(\eta)-W(\eta)]\,d\Gamma_B&=0,\\
\int\psi(W)[\mathcal R_A(W)(\omega)-Q(\omega)]\,d\Gamma_A&=0.
\end{aligned}
\tag{1.6}
$$

This is [PAIR, Definition 11.2], including its infinite-coordinate tests.
The marginals are unweighted acquired marginals; $U,v$ are not inserted
into (1.5).

## 2. Supplied edges and descriptor-conditioned defects

**Definition 2.1 (input data).** Let $G_B,G_A$ be arbitrary Borel probability
measures on the same ordered products as $\Gamma_B,\Gamma_A$.
They are supplied analytical data. They need not satisfy (1.5) or (1.6).
Set

$$
\sigma_p=(G_B)_1,\quad \tau_\beta=(G_B)_2,\qquad
\sigma_\beta=(G_A)_1,\quad \tau_p=(G_A)_2.
\tag{2.1}
$$

Disintegrate on these compact metric spaces:

$$
G_B(dQ,dW)=\sigma_p(dQ)B_0(Q,dW),\qquad
G_A(dW,dQ)=\sigma_\beta(dW)A_0(W,dQ).
\tag{2.2}
$$

Versions at null inputs can be any Borel probability versions. Define

$$
\begin{aligned}
e_B&=\int d_\beta\left(\mathcal R_B(Q),\int W B_0(Q,dW)\right)d\sigma_p(Q),\\
e_A&=\int d_p\left(\mathcal R_A(W),\int Q A_0(W,dQ)\right)d\sigma_\beta(W).
\end{aligned}
\tag{2.3}
$$

Here the notation $d_s$ also denotes TV on the full probability simplex.
The norm is taken after conditioning on the entire outgoing descriptor
and before averaging over that descriptor. These values are independent
of conditional versions. Barycentres are defined coordinatewise;
countable summation proves normalization and measurability.

**Definition 2.2 (label transport and repair budget).** For Borel
probabilities $\xi,\zeta$ on $\mathcal K_s$, write

$$
\mathsf W_s(\xi,\zeta)=
 \min_{C\in\Pi(\xi,\zeta)}\int d_s(D,D')\,dC(D,D').
\tag{2.4}
$$

This is $W_1$ with complete-law TV as its ground metric, not TV between
the label distributions. Compactness and continuity of the cost give
attainment. On each ordered product use the sum of the two ground
metrics, and denote its $W_1$ by $\mathsf W_{p\beta}$ or
$\mathsf W_{\beta p}$. Put

$$
\begin{gathered}
m_\beta=\mathsf W_\beta(\tau_\beta,\sigma_\beta),\qquad
m_p=\mathsf W_p(\tau_p,\sigma_p),\\
x=e_B+m_\beta,\qquad y=e_A+m_p,\\
D_p=\frac{10x+4y}{11},\qquad
D_\beta=\frac{4x+6y}{11}.
\end{gathered}
\tag{2.5}
$$

All these quantities are finite. No access to an unknown device, unknown
law, independent descriptor sample, source reset or stationary trajectory
is an assumption of Definitions 2.1–2.2.

## 3. Joint balance and own-law repair

**Theorem 3.1 (one repair on the original input-label measures).** For every
pair in Definition 2.1 there are Borel probability kernels
$B:\mathcal K_p\to\operatorname{Prob}(\mathcal K_\beta)$ and
$A:\mathcal K_\beta\to\operatorname{Prob}(\mathcal K_p)$, and Borel maps
$F_p:\mathcal K_p\to\mathcal K_p$,
$F_\beta:\mathcal K_\beta\to\mathcal K_\beta$, with the following properties.

The label measures are exactly balanced:

$$
\sigma_pB=\sigma_\beta,\qquad \sigma_\beta A=\sigma_p.
\tag{3.1}
$$

The maps are the normalized own complete laws of these kernels with the
original input emission coordinates, so that at every input

$$
\begin{aligned}
F_p(Q)&=u(Q)\delta_\alpha+
 U(Q)\beta\int F_\beta(W)B(Q,dW),\\
F_\beta(W)&=(1-v(W))\delta_\beta+
 v(W)\alpha\int F_p(Q)A(W,dQ).
\end{aligned}
\tag{3.2}
$$

In particular $u(F_p(Q))=u(Q)$ and $v(F_\beta(W))=v(W)$. Their errors obey

$$
\int d_p(F_p(Q),Q)d\sigma_p\le D_p,\qquad
\int d_\beta(F_\beta(W),W)d\sigma_\beta\le D_\beta.
\tag{3.3}
$$

Define the balanced label edges and their generated-law pushforwards by

$$
\begin{aligned}
H_B&=\sigma_p\otimes B,& H_A&=\sigma_\beta\otimes A,\\
\widehat G_B&=(F_p,F_\beta)_\#H_B,&
\widehat G_A&=(F_\beta,F_p)_\#H_A.
\end{aligned}
\tag{3.4}
$$

Then $(\widehat G_B,\widehat G_A)\in\mathfrak C$, and

$$
\begin{aligned}
\mathsf W_{p\beta}(G_B,\widehat G_B)&\le m_\beta+D_p+D_\beta,\\
\mathsf W_{\beta p}(G_A,\widehat G_A)&\le m_p+D_p+D_\beta.
\end{aligned}
\tag{3.5}
$$

The generated marginals are $(F_p)_\#\sigma_p,(F_\beta)_\#\sigma_\beta$;
they need not equal the original descriptor marginals. The same maps and
kernels work for every normalized complete probability target $T$
simultaneously:

$$
\left|\int d_s(F_s(D),T)d\sigma_s(D)
            -\int d_s(D,T)d\sigma_s(D)\right|\le D_s,
\qquad s=p,\beta.
\tag{3.6}
$$

Targets with positive infinite mass are included. No deterministic
successor, finite-support, irreducibility, mixing or recurrence hypothesis
is required.

**Proof.** Choose optimal couplings $C_\beta$ of
$(\tau_\beta,\sigma_\beta)$ and $C_p$ of $(\tau_p,\sigma_p)$.
Disintegrate them as
$C_s(dD,dD')=\tau_s(dD)K_s(D,dD')$. Glue only the incoming label:

$$
\begin{aligned}
\Lambda_B(dQ,dW,dW')&=G_B(dQ,dW)K_\beta(W,dW'),\\
\Lambda_A(dW,dQ,dQ')&=G_A(dW,dQ)K_p(Q,dQ').
\end{aligned}
\tag{3.7}
$$

Their $(Q,W')$ and $(W,Q')$ marginals, respectively, have marginals
$(\sigma_p,\sigma_\beta)$ and $(\sigma_\beta,\sigma_p)$.
Take these to be $H_B,H_A$ and disintegrate to obtain $B,A$.
This is the one-coordinate case of the shadow construction of
Eckstein–Nutz, Definition 3.1 and Lemma 3.2 [EN]. The relevant spaces
are compact Polish with bounded metric, so their first moments are finite.
The unchanged coordinate uses its diagonal coupling. Directly from (3.7),

$$
\int d_\beta(W,W')d\Lambda_B=m_\beta,\qquad
\int d_p(Q,Q')d\Lambda_A=m_p.
\tag{3.8}
$$

These equalities also prove (3.1). Versions of $B,A$ on null outgoing
sets can be filled with a Dirac measure at any fixed opposite-space
descriptor, making them probability kernels everywhere.

Conditional Jensen for the half-$\ell^1$ norm gives

$$
\begin{aligned}
\widetilde e_B&:=\int d_\beta\left(\mathcal R_B(Q),\int W'B(Q,dW')\right)d\sigma_p
 \le e_B+m_\beta=x,\\
\widetilde e_A&:=\int d_p\left(\mathcal R_A(W),\int Q'A(W,dQ')\right)d\sigma_\beta
 \le e_A+m_p=y.
\end{aligned}
\tag{3.9}
$$

For example, condition $\Lambda_B$ on $Q$. Its old and new successor
barycentres differ in TV by at most the conditional mean of
$d_\beta(W,W')$. Integrating gives (3.9). This step retains the full
outgoing descriptor and does not replace (2.3) by a norm of an averaged
signed residual.

To construct the own laws without a path recurrence assumption, let $L$
act on bounded Borel functions on $\mathcal K_p$ by

$$
Lf(Q)=U(Q)\int v(W)\int f(Q')A(W,dQ')B(Q,dW),\qquad
g(Q)=U(Q)\int(1-v(W))B(Q,dW).
\tag{3.10}
$$

Then $L\mathbf1\le\lambda\mathbf1$ and $u+g+L\mathbf1=\mathbf1$.
Define

$$
F_p(Q)(w_{n,0})=(L^nu)(Q),\qquad
F_p(Q)(w_{n,1})=(L^ng)(Q),\qquad F_p(Q)(\infty_p)=0.
\tag{3.11}
$$

Every coordinate is nonnegative and Borel. Telescoping gives

$$
\sum_{n<N}L^n(u+g)=\mathbf1-L^N\mathbf1,
\qquad L^N\mathbf1\le\lambda^N\mathbf1.
\tag{3.12}
$$

Thus (3.11) is normalized and has p tail at depth $j$ exactly
$L^j\mathbf1$, at most $\lambda^j$. Define $F_\beta$ by the second
line of (3.2). Its tail is at most $v(W)\lambda^j\le b\lambda^j$;
it too is normalized, retains infinity with mass zero, and has the required
emission. Substitution into (3.11) proves the first line of (3.2).
Coordinate measurability implies TV-Borel measurability here: a ball's
distance function is a countable sum of measurable coordinates, and the
target metric spaces are separable. Consequently both maps have the
asserted codomains and measurability.

The recursions have a unique normalized solution. If two solutions have
supremum phase distances $z_p,z_\beta\le1$, (3.2) gives
$z_p\le(2/3)z_\beta$ and $z_\beta\le(2/5)z_p$; hence both vanish.
This contraction is due to synthetic stopping, even for reducible kernels.

Write $d_p^*,d_\beta^*$ for the two actual integrals in (3.3).
The original descriptor identities are
$Q=u(Q)\delta_\alpha+U(Q)\beta\mathcal R_B(Q)$ and their suspended
counterparts. Comparison with (3.2), then (3.1) and (3.9), gives

$$
d_p^*\le\frac23(x+d_\beta^*),\qquad
d_\beta^*\le\frac25(y+d_p^*).
\tag{3.13}
$$

The averaging uses the balanced **label** edges $H_B,H_A$:
for example $\int\!\int d_\beta(F_\beta(W),W)B(Q,dW)d\sigma_p=d_\beta^*$.
Solving the two inequalities, with $1-(2/3)(2/5)=11/15$, gives exactly
(3.3). The coefficient matrix is the already used two-phase contraction
matrix [REV, (17.12)]; the new inputs to it are the full-descriptor defects
plus the incoming marginal transport costs.

The two pushforwards in (3.4) share the stated generated marginals.
For each bounded Borel $\phi$ on $\mathcal K_p$ and complete atom $\eta$,
the first equation in (3.2), divided by its unchanged $U(Q)>0$, yields

$$
\int\phi(F_p(Q))
 [\mathcal R_B(F_p(Q))(\eta)-F_\beta(W)(\eta)]dH_B(Q,W)=0.
\tag{3.14}
$$

This is precisely the first test in (1.6) for $\widehat G_B$.
The other test follows from the second equation of (3.2).
The proof covers a many-to-one $F_p$ or $F_\beta$: (3.14) is conditioned
on the entire generated input law after pushforward, and never chooses an
inverse label or a successor of a representative of its fibre. There is
one common full-measure set for all complete coordinates, since there are
countably many. Thus the pair lies in the exact original $\mathfrak C$.

For (3.5), couple $(Q,W)$ under $G_B$ with
$(F_p(Q),F_\beta(W'))$ using $\Lambda_B$. Its cost is at most

$$
\int\bigl[d_p(Q,F_p(Q))+d_\beta(W,W')
                  +d_\beta(W',F_\beta(W'))\bigr]d\Lambda_B
 =d_p^*+m_\beta+d_\beta^*.
\tag{3.15}
$$

Use $\Lambda_A$ for the reversed product. Finally
$|d_s(F_s(D),T)-d_s(D,T)|\le d_s(F_s(D),D)$ for every complete target,
proving (3.6) with no target-dependent construction or exceptional set.
The same inequalities hold after any common measurable projection by TV
contraction; injective current-record rendering preserves the distances.
$\square$

## 4. Full supported-target risk and the seven-feature consumer

**Definition 4.1 (original losses before repair).** With
$t_r=r(1-r)$, the native complete laws are

$$
P_{p,r}(w_{n,0})=rt_r^n,\qquad
P_{p,r}(w_{n,1})=(1-r)^2t_r^n,\qquad
P_{\beta,r}=(1-r)\delta_\beta+r\alpha P_{p,r}.
\tag{4.1}
$$

Set $\rho_p=1116529/22781250$ and $\rho_\beta=239/6750$,
the original endpoint radii [PAIR, §§2, 11]. Define

$$
J_0=\max_{s=p,\beta}
 \left\{\sup_{k:\mu(k)>0}\int d_s(D,P_{s,r_k})d\sigma_s(D)-\rho_s\right\}.
\tag{4.2}
$$

The repaired functional $J(\widehat G)$ is the same expression with
$\widehat\nu_s=(F_s)_\#\sigma_s$. Configuration TV remains inside
every integral. Endpoint triangle inequality gives $J_0\ge0$ without
assuming compatibility of the input edges.

**Corollary 4.2 (all targets of the one installed prior).** The single
repair in Theorem 3.1 satisfies

$$
|J(\widehat G)-J_0|\le\max\{D_p,D_\beta\}.
\tag{4.3}
$$

For every original positive history, its normalized same-$K$ posterior
mixture is also a permissible complete target in (3.6), with the original
record renderer at that history. Formula (4.3) neither replaces the prior
by three points nor identifies a history's actual configuration row with
$\sigma_s$.

**Proof.** Apply (3.6) simultaneously to all supported targets and use
$|\sup f-\sup g|\le\sup|f-g|$, then the same inequality for the two-phase
maximum. The baselines do not change. Every normalized posterior mixture
is a probability law on the same complete carrier, so (3.6) applies
directly; injectivity of $I_c$ supplies the full-record statement. The
actual-history target and row are distinct objects, as in
[NATIVE, `conditional_history_product` and `native_history_risk_transport`].
$\square$

**Definition 4.3 (seven squared residuals on arbitrary edges).** For any
complete laws on the appropriate carriers put

$$
\begin{aligned}
f(Q)&=(Q(w_{0,1}),Q(w_{1,1}),Q(w_{2,1})),\\
g(W)&=(W(\beta),W(\alpha w_{0,1}),W(\alpha w_{1,1}),W(\alpha w_{2,1})),\\
V_0&=\int\|f(Q)-f(\mathcal R_A(W))\|_2^2dG_A(W,Q)\\
&\hspace{12mm}+\int\|g(W)-g(\mathcal R_B(Q))\|_2^2dG_B(Q,W),\\
H&=8m_\beta+6m_p+\frac{58}{3}D_p+26D_\beta.
\end{aligned}
\tag{4.4}
$$

These are the features of [SEVEN, Definition 2.1]. Outside $\mathfrak C$,
$V_0$ is a squared residual statistic, not a conditional variance.
For a compatible pair the residual barycentres are conditional feature
means, so the same expression is the sum $V$ of seven conditional
variance integrals.

**Theorem 4.4 (transported seven-feature exclusion).** The repair satisfies

$$
V(\widehat G)\le V_0+H.
\tag{4.5}
$$

If the fixed prior of Assumption 1.1 has at least one supported depth
$k_*\ge3$, then

$$
\boxed{J_0+\max\{D_p,D_\beta\}+\sqrt{V_0+H}\ge10^{-26}.}
\tag{4.6}
$$

This holds on the original finite or countable supported-target domain.
It does not require, or assert preservation of, the five additional boxes
of [RISK, Definition 1.3].

**Proof.** The normalization estimate needed here is already supplied by
[PAID, (17.7)]: for normalized $P,P'$ and an event $E$ of positive masses
$q,q'$, its conditional laws satisfy

$$
\max\{q,q'\}\operatorname{TV}(P(\cdot\mid E),P'(\cdot\mid E))
 \le\operatorname{TV}(P,P').
\tag{4.7}
$$

Indeed for $q\ge q'$ the $\ell^1$ difference restricted to $E$ is at
least $q\|P(\cdot\mid E)-P'(\cdot\mid E)\|_1-(q-q')$;
the complementary difference is at least $q-q'$. Adding and dividing by
two proves (4.7); interchange the laws for the other order. Consequently,
on (1.3), including all the residual coordinates,

$$
d_\beta(\mathcal R_B(Q),\mathcal R_B(Q'))\le\frac53d_p(Q,Q'),\qquad
d_p(\mathcal R_A(W),\mathcal R_A(W'))\le3d_\beta(W,W').
\tag{4.8}
$$

For four numbers in $[0,1]$,
$|(z-t)^2-(z'-t')^2|\le2(|z-z'|+|t-t'|)$.
Each atom evaluation is 1-Lipschitz for TV. Thus for the B integrand
$h_B(Q,W)=\|g(W)-g(\mathcal R_B(Q))\|_2^2$,

$$
|h_B(Q,W)-h_B(Q',W')|
 \le8d_\beta(W,W')+\frac{40}{3}d_p(Q,Q').
\tag{4.9}
$$

For $h_A(W,Q)=\|f(Q)-f(\mathcal R_A(W))\|_2^2$,

$$
|h_A(W,Q)-h_A(W',Q')|
 \le6d_p(Q,Q')+18d_\beta(W,W').
\tag{4.10}
$$

First integrate (4.9) on the coupling (3.7) from $G_B$ to $H_B$.
Only its successor changes, so this costs at most $8m_\beta$.
Then integrate it on the deterministic pushforward from $H_B$ to
$\widehat G_B$, which costs at most $8d_\beta^*+(40/3)d_p^*$.
For A the two costs are $6m_p$ and $6d_p^*+18d_\beta^*$.
Their sum is bounded by $H$, proving (4.5); in fact the same argument
bounds the absolute difference between the two residual statistics.

The pair $\widehat G$ belongs to the full original $\mathfrak C$.
[SEVEN, Convention 6.1 and Theorem 6.2] apply to exactly a fixed finite
or countable prior with both endpoint masses positive and some supported
$k_*\ge3$, without further boxes, support or successor conditions. They
give $J(\widehat G)+\sqrt{V(\widehat G)}\ge10^{-26}$.
Use (4.3), (4.5) and monotonicity of the square root to obtain (4.6).
The three-point case is included because $r_3=3/8$; the larger-prior
assertion uses the stated general-prior theorem in SEVEN §6, not an
extrapolation of its three-point Chapters 1–5 or the boxed RISK theorem.
$\square$

## 5. Nonzero complete-law defects and conditioning fibres

**Proposition 5.1 (four nonzero defects with a genuine own-law change).**
Let $c=3/8$, and write $Q_r=P_{p,r}$, $W_r=P_{\beta,r}$. Take

$$
G_B=\delta_{(Q_a,W_c)},\qquad G_A=\delta_{(W_b,Q_c)}.
\tag{5.1}
$$

All four quantities $e_B,e_A,m_\beta,m_p$ are positive. Theorem 3.1 gives
the unique singleton balanced kernels on outgoing labels $Q_a,W_b$.
Their generated laws are

$$
\begin{aligned}
\widehat Q(w_{n,0})&=\frac13\left(\frac4{15}\right)^n,&
\widehat Q(w_{n,1})&=\frac25\left(\frac4{15}\right)^n,\\
\widehat W&=\frac35\delta_\beta+\frac25\alpha\widehat Q.
\end{aligned}
\tag{5.2}
$$

They retain the input emissions and attain the allowed p tail bound
$\lambda^j$ for every $j$. In particular

$$
d_p(\widehat Q,Q_a)=\frac2{45}>0,
\qquad d_\beta(\widehat W,W_b)\ge\frac2{75}>0.
\tag{5.3}
$$

For this input the exact budgets are

$$
\begin{aligned}
x&=\frac{239}{3375},&
y&=\frac{468557036828959}{4777574400000000},\\
D_p&=\frac{1314364652828959}{13138329600000000}<\frac19,&
D_\beta&=\frac{694105734428959}{8758886400000000}<\frac1{12}.
\end{aligned}
\tag{5.4}
$$

Thus (3.6) gives nontrivial, simultaneous complete-target error bounds
for data having both balance and compatibility defects.

**Proof.** Native laws lie in (1.3), since $t_r\le6/25<4/15$.
Their residuals are $\mathcal R_B(Q_r)=W_r$ and
$\mathcal R_A(W_r)=Q_r$. Dirac-to-Dirac transport gives

$$
e_B=d_\beta(W_a,W_c),\quad m_\beta=d_\beta(W_c,W_b),\quad
e_A=d_p(Q_b,Q_c),\quad m_p=d_p(Q_c,Q_a).
\tag{5.5}
$$

The immediate alpha or beta coordinates prove positivity of every term.
For $r<s$ in $\{a,c,b\}$, the p marker-0 masses increase with $r$ at
every depth. The positive difference of marker-1 masses has exactly the
indices $0\le n\le N_p(r,s)$, where

$$
N_p(a,c)=2,\quad N_p(c,b)=3,\quad N_p(a,b)=2.
\tag{5.6}
$$

These thresholds follow by comparing
$((1-r)/(1-s))^2$ with $(t_s/t_r)^n$: the latter is strictly increasing,
and substitution at $N_p$ and $N_p+1$ gives the asserted threshold.
At suspension the positive differences are beta and the alpha-prefixed
marker-1 term with $n=0$ only for each of these three pairs, by the same
comparison with coefficient $r(1-r)^2$. Finite geometric sums give

$$
\begin{aligned}
d_p(Q_a,Q_c)&=\frac{11757103}{191102976},&
d_p(Q_c,Q_b)&=\frac{239546586871}{6553600000000},\\
d_\beta(W_a,W_c)&=\frac{599}{13824},&
d_\beta(W_c,W_b)&=\frac{1759}{64000}.
\end{aligned}
\tag{5.7}
$$

Adding the appropriate terms and using (2.5) proves (5.4). After transport,
each outgoing phase has one positive label; both repaired transitions are
forced. Their emissions are $a,b$, and their return probability is
$(1-a)b=4/15$, proving (5.2) and normalization.
For $Q_a-\widehat Q$ the only strictly positive coordinate is $w_{0,1}$:
its difference is $4/9-2/5=2/45$. Marker-0 coordinates agree at $n=0$
and favour $\widehat Q$ at $n\ge1$; marker-1 coordinates favour it at
$n\ge1$ because their successive ratio is multiplied by $6/5$.
This proves the exact p TV. At the suspended atom $\alpha\alpha$,
$W_b$ has mass $4/25$ and $\widehat W$ has mass $2/15$,
proving the other lower bound. $\square$

**Proposition 5.2 (averaging a residual before its norm loses a defect).**
There is an input B edge on (1.3) for which the averaged signed residual
is zero on every complete coordinate, but $e_B=1/6$.

**Proof.** Put $r=1/3$ and

$$
W_\pm=(1-r)\delta_\beta+
 r\left[\left(\frac12\pm\frac14\right)\delta_{\alpha\alpha}
       +\left(\frac12\mp\frac14\right)\delta_{\alpha\beta\beta}\right],
\quad Q_\pm=r\delta_\alpha+(1-r)\beta W_\pm.
\tag{5.8}
$$

Each $W_\pm$ has suspended emission $r$ and no depth-one suspended tail;
each $Q_\pm$ has p emission $r$, depth-one tail $2/9\le\lambda$ and
zero later tail. Hence all four descriptors lie in their required spaces.
Take $G_B=\tfrac12\delta_{(Q_+,W_-)}+\tfrac12\delta_{(Q_-,W_+)}$.
Its two conditional residual errors are $W_+-W_-$ and its negative,
so their signed average is zero. Their individual TV is $r/2=1/6$,
and (2.3) gives $e_B=1/6$. The input descriptors are distinct, so this
is cancellation across different full conditioning fibres. $\square$

## 6. Why balance repair is a different installation

**Theorem 6.1 (vanishing balance error does not control the old stationary row).**
For each rational $0<\varepsilon<1$ there is one two-label-per-phase
regular generator and input edges made from its own complete laws such
that $e_A=e_B=m_\beta=0$ and $m_p\le\varepsilon$, but every balanced
pair using its unchanged acquired kernels has p and suspended law
marginals at $W_1$ distance at least $1/15$ from the two outgoing input
marginals. Therefore no modulus tending to zero with these four defects
can replace Theorem 3.1 by a stationary-row claim for the unchanged
installation.

**Proof.** Label both phases by $0,1$. Take

$$
B_0=I_2,\qquad
A_\varepsilon=\begin{pmatrix}1-\varepsilon&\varepsilon\\0&1\end{pmatrix},
\qquad (u_0,u_1)=(v_0,v_1)=(a,b).
\tag{6.1}
$$

Let $Q_i,W_i$ be its own complete laws, constructed by the same normalized
series (3.10)–(3.12). All belong to (1.3),
$Q_1=P_{p,b},W_1=P_{\beta,b}$, and the two laws in each phase are
distinct by their emission coordinates. Use

$$
G_B=\delta_{(Q_0,W_0)},\qquad
G_A=(1-\varepsilon)\delta_{(W_0,Q_0)}+
              \varepsilon\delta_{(W_0,Q_1)}.
\tag{6.2}
$$

Both conditional residual equations hold exactly, so $e_A=e_B=0$.
The outgoing rows are $\sigma_p=\delta_{Q_0}$ and
$\sigma_\beta=\delta_{W_0}$. Thus $m_\beta=0$ and

$$
m_p=\varepsilon d_p(Q_0,Q_1)\le\varepsilon.
\tag{6.3}
$$

A stationary row $\pi$ for the unchanged acquired return kernel
$B_0A_\varepsilon=A_\varepsilon$ satisfies
$\pi_0=(1-\varepsilon)\pi_0$, so $\pi=\delta_1$.
Its suspended row is also $\delta_1$. Hence the only corresponding law
marginals are $\delta_{Q_1},\delta_{W_1}$, and their distances from the
input marginals are at least $|u_1-u_0|=|v_1-v_0|=1/15$.

The original-domain product construction [PAID, Lemma 2.1.1] can instead
be initialized at label 0 in its original third-write/latch update,
independently of the once-sampled $K$. After the actual positive history
of $n$ fourth returns, its p row is exactly

$$
\eta_n=(1-\varepsilon)^n\delta_0+
       [1-(1-\varepsilon)^n]\delta_1.
\tag{6.4}
$$

This follows by multiplying the same acquired kernels, not by weighting
by synthetic continuation. Every such finite history is allowed and
positive for the fixed original prior. Source conditioning leaves the
private ordered kernel row as in (6.4), by the source-independent product
construction, also expressed by [NATIVE, `conditional_history_product`].

The loss against the original supported complete target $P_{p,a}$ tends
along these rows to $\Delta=d_p(P_{p,b},P_{p,a})=2\rho_p>0$.
At the outgoing input row it is small: comparison of the state-0
recursions with the native $a$ pair gives

$$
d_p(Q_0,P_{p,a})\le
 \frac{2\varepsilon}{7+2\varepsilon}\Delta.
\tag{6.5}
$$

Indeed its p error is at most $(1-a)$ times its suspended error, while
the suspended error is at most
$a[(1-\varepsilon)d_p(Q_0,P_{p,a})+\varepsilon\Delta]$.
Solve the resulting scalar inequality. Thus even complete-target loss
at the designated outgoing row cannot stand for loss along all actual
rows. This statement uses one supported pure target as an analytical
test; it does not assert that every finite history has that pure posterior.

The repaired table on the positive outgoing labels has both transitions
fixed at label 0 and therefore generates $P_{p,a},P_{\beta,a}$.
It changes the acquired kernel $A_\varepsilon$. Equations (3.3) and
(3.6) concern that new table. No small-balance premise can identify the
two installations, as the stationary-row lower bounds show. $\square$

## 7. Finite rational labels and paid source correspondence

**Corollary 7.1 (finite rational repair and its precise representation premise).**
Suppose $G_B,G_A$ have finite support and rational edge weights, and the
emissions of all positive outgoing labels are rational. Then the balanced
kernels in Theorem 3.1 can be chosen with finite support and rational
entries, with the exact same error bounds. Zero outgoing weights can be
deleted. With these rational tables and latch row supplied as finite
represented data, the repaired own laws have a finite original-domain
product realization with the same acquired and synthetic update kernels.
For that new realization the full configuration risks satisfy

$$
R_{\mathrm{conf},s}\le
 \sup_{k:\mu(k)>0}\int d_s(D,P_{s,r_k})d\sigma_s(D)+D_s.
\tag{7.1}
$$

The rational existence assertion does not give an algorithm for comparing
arbitrary supplied real complete-law transport costs.

**Proof.** In each finite transport problem the coupling constraints form
a nonempty bounded rational polytope. A linear objective with arbitrary
real cost coefficients attains its minimum at some vertex. Each vertex
solves a full-rank subsystem of rational equalities and active coordinate
constraints, and is rational by Gaussian elimination. Thus rational
optimal $C_p,C_\beta$ exist even if selection among their vertices is not
effective from the descriptions of the complete laws.

For clarity, on the union of the relevant finite input and output labels,
write $g^B_{ij}=G_B(Q_i,W_j)$ and
$c^\beta_{jk}=C_\beta(W_j,W_k)$. The balanced B edge is

$$
h^B_{ik}=\sum_{j:\tau_\beta(j)>0}
               g^B_{ij}\frac{c^\beta_{jk}}{\tau_\beta(j)}.
\tag{7.2}
$$

Its outgoing row is $\sigma_p$ and incoming row is $\sigma_\beta$.
The reversed formula defines $h^A$. Divide by positive outgoing weights
to get the rational kernels. A zero incoming weight has a zero coupling
row and a zero incident input edge, so its omitted summand is exactly
zero, not a division convention. Balance prevents positive outgoing rows
from entering labels with zero opposite outgoing weight. Deleting those
labels changes no positive-row law, integral or bound.

Now apply [PAID, Definition 2.1 and Lemma 2.1.1] with period one, p row
$\sigma_p$, suspended row $\sigma_\beta$, these $B,A$, and the preserved
emission vectors. The latch samples the p row once in the original
third-write-before-latch update; it does not reset the source. All
pre-latch original controls, both seeds, paid rejections and records
remain. Completing letters clear private labels and preserve the matching
Stop. Induction with (3.1) gives exactly these rows at every actual
fourth-phase history. Its decoders are the own laws (3.2), so the supplied
supported-target risk identity [PAID, (2.3)] and (3.6) prove (7.1), also
for countable supported priors. It is one simultaneous installation,
not independently optimized phase machines.

To realize a rational categorical row, choose a common positive integer
denominator $N$, draw $k=\lceil\log_2 N\rceil$ independent fair private
bits, accept the integer if it is below $N$, and otherwise repeat; use
the prescribed integer intervals for the output. For $N=1$ no bits are
needed. For $N>1$ each trial accepts with probability $N/2^k>1/2$;
termination is almost sure, expected bit use is $k2^k/N<2k$, and no
deterministic trial bound is asserted. The sampler has a finite program
and finite partial-trial states, which belong to COMPLETE. Independent
emission and update services realize exactly their joint transition,
without source Reads within the private service.

The storage cost includes the rational table numerators and denominators,
table-selection control, original $C_0$, current p or suspended label,
sampler program and all its internal states, workspace and any persistent
random choices. A direct label representation needs
$\lceil\log_2 n_p\rceil$ or $\lceil\log_2 n_\beta\rceil$ bits at
the corresponding phase; this is only the label component of the total.
The stochastic rule does not need a runtime port holding a complete-law
descriptor, its TV distances, the source depth or its posterior.
Selecting and representing the rational repair and its cost bounds is a
separate offline data obligation. No preassigned hard total-state,
precision, work, random-bit, defect or acquisition budget is preserved.
$\square$

**Corollary 7.2 (effective cost evidence).** A finite represented repair
may instead supply any rational couplings with certified upper costs
$M_p,M_\beta$. Every bound remains valid after replacing $m_p,m_\beta$
by $M_p,M_\beta$.

**Proof.** Equations (3.8)–(3.15) use only the integrated costs of the
chosen couplings. All coefficients in the subsequent bounds are
nonnegative, so their certified upper bounds can be substituted. This
does not change the exact optimal-cost existence assertion in Theorem 3.1.
If neither complete-law costs nor upper bounds are supplied, finite
rationality alone supplies no evaluated error budget. $\square$

**Proposition 7.3 (an auxiliary repair is not an acquisition theorem).**
The hypotheses of Theorem 3.1 do not determine the acquired history row
of an unspecified original observer, a procedure for obtaining $G_A,G_B$
from that observer, or a statistical guarantee for estimates of (2.3).

**Proof.** Theorem 6.1 provides the same small-defect type of analytical
input with an unchanged original kernel whose later rows and stationary
row differ by a fixed amount; hence no inference identifying these rows
can hold under these hypotheses. More basically, Definitions 2.1–2.2
specify measures and no observation experiment, sample law, estimator or
confidence event. Any such conclusion requires an additional map from
an actual experiment to the supplied measures and its own accuracy and
cost hypotheses. Exact state identification, optimal readout error and
the existence of a represented generated law have different mathematical
premises [WHITEBOX, §§14–18, 51, 74–77; SLH, §§50–58].
$\square$

## 8. Mathematical suppliers and the remaining common-flow question

**Mathematical citation 8.1 (scope of transport suppliers).**
[EN, Definition 3.1 and Lemma 3.2] supply marginal transport by gluing on
Polish spaces with finite first moments. Here there are two factors,
$p=1$, the product metric is a sum, and one factor's coupling is diagonal.
All ground spaces are (1.3), so the hypotheses hold. The entropy assertion
in that lemma is not used. [AWR, Algorithm 2 and Lemma 7] give finite
nonnegative-matrix rounding to prescribed probability rows and columns,
with an $\ell^1$ error bound twice the sum of the marginal $\ell^1$
errors. That result is a finite marginal-repair supplier, not a
complete-law own-generation assertion. Its cost is distinct from (2.4).

[LV, Theorems 1.2–1.4] concern real vectors with finite first moments,
measurable families of such laws, and conditional martingale couplings.
Finite completed-word projections here are bounded vectors and satisfy
those integrability premises; those theorems alone do not give both
complete flows or (3.2). The prescribed-entire-marginal criterion in
[PAIR, Theorem 20.2] already supplies the full projected-convex-order
criterion for zero residual defect. Repair instead allows the generated
law marginals to move; it does not contradict that criterion.

In [BVP, §3, property (A)] weak-transport costs are lower bounded and
lower semicontinuous in the input and successor probability law, and
convex in the latter. The costs
$C_B(Q,\kappa)=d_\beta(\mathcal R_B(Q),\int Wd\kappa)$ and its A
counterpart satisfy these conditions: barycentring is continuous from
probabilities on compact $\mathcal K_s$ to complete TV, since finite
coordinate convergence plus the uniform geometric tails gives TV
convergence; residuals are continuous and TV is convex. This explains
the classical conditional-barycentre context of (2.3). No new generic
transport, disintegration or contraction principle is asserted.

**Mathematical citation 8.2 (source-specific premise boundaries).**
The joint repair (3.1)–(4.6) is a source-specific, repo-derived consequence;
the transport principles in citation 8.1 are literature-attested suppliers.
[PAIR, Theorem 11.4] regenerates already compatible flows; [PAIR,
Theorem 14.2] compares their full losses to an endpoint chord; [PAIR,
Proposition 17.1] supplies a complete-residual example inside prescribed
boxes. None of those premises permits arbitrary simultaneous violations
of balance and full-descriptor compatibility. [REV, Theorem 17.2] starts
inside $\mathfrak C$ and gives a deterministic comparison with conditional
barycentre preservation. Theorem 3.1 starts from arbitrary edges and
asserts neither such barycentre preservation nor a deterministic comparison.
[RETURN, §§11–15] additionally constrain actual return motion, whose
joint law is not determined by the two repaired descriptor edges.
[RISK, Theorem 2.1] requires its five boxes; only the full-domain exclusion
[SEVEN, Theorem 6.2] is used in Theorem 4.4.

[NATIVE] constructs the actual same-source joint law with ordered acquired
updates. [CONST] excludes sufficiently small endpoint excess under
constant suspended emissions on positive support. [RARE3] and [RAREABS]
bound capped rare-prior risks and absolute complete-history risks for
their specified native observer. Their original finite COMPLETE
representation and radius-identification premises cannot be replaced by
the analytical input in Definition 2.1. In particular no capped-history
estimate discards any supported target in (4.2).

The five-mode static-seam circulation and local-clock models of [STATIC,
§§2–3, 21], the legal joint-window fibres of [PYRAMID, §§14–18], and
the supplied waiting-kernel model of [CLOCK, Theorems 19–22] have different
state and observation carriers. No map identifying their probability
coordinates or clock readings with the complete descriptors (1.3) is
assumed. Their marginal-versus-joint distinctions do not supply such an
identification or the source-specific implication (3.1)–(4.6).

**Definition 8.3 (remaining zero-versus-positive problem).** For the fixed
original prior the common-flow objective remains

$$
j_c=\min_{\Gamma\in\mathfrak C}J(\Gamma).
\tag{8.1}
$$

When an interior depth is supported, (4.6) is a necessary joint inequality
for arbitrary proposed approximate edges. It supplies neither a pair at
$J=0$ nor a strictly positive lower bound for $j_c$ alone, because $V$
need not vanish. Finite exact attainment also requires the relevant
finite-support and representation premises [PAIR, §11; PAID, §§16–18].
The unrestricted common-flow alternative, lawful acquisition of the
analytical inputs and statistical control of their errors remain separate
mathematical obligations.

[PAIR]: RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md
[REV]: RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md
[SEVEN]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_WORD_BRANCHING_NECESSITY.md
[RISK]: RECURSIVE_RELATIONAL_OBSERVATION_SEVEN_FEATURE_RISK_TOLERANCE.md
[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[RETURN]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md
[WHITEBOX]: FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[STATIC]: AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md
[PYRAMID]: AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md
[CLOCK]: AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md
[NATIVE]: ../../../Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.md
[CONST]: ../../../Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator.md
[RARE3]: ../../../Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.md
[RAREABS]: ../../../Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorAbsoluteRisk.md
[EN]: https://arxiv.org/abs/2110.06798v3
[AWR]: https://arxiv.org/abs/1705.09634v2
[LV]: https://arxiv.org/abs/1404.0999v3
[BVP]: https://arxiv.org/abs/2003.05338v1

**Mathematical citation 8.4 (primary references).** [EN] S. Eckstein and
M. Nutz, *Quantitative Stability of Regularized Optimal Transport and
Convergence of Sinkhorn's Algorithm*, arXiv:2110.06798v3, Definition 3.1
and Lemma 3.2. [AWR] J. Altschuler, J. Weed and P. Rigollet,
*Near-linear time approximation algorithms for optimal transport via
Sinkhorn iteration*, arXiv:1705.09634v2, Algorithm 2 and Lemma 7.
[LV] L. Leskelä and M. Vihola, *Conditional convex orders and measurable
martingale couplings*, arXiv:1404.0999v3, Theorems 1.2–1.4.
[BVP] J. Backhoff-Veraguas and G. Pammer, *Applications of weak transport
theory*, arXiv:2003.05338v1, §3.

## 追加锚（本行以下为增补区）
