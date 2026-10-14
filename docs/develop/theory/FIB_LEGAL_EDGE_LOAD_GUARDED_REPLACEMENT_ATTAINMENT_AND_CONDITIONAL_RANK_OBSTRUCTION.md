# FIB harmonic-edge load: guarded replacement, attainment and conditional-rank obstruction

Finite independent replacement between two zero guards gives an exact identity for the original law's Brier losses, with nonnegative exterior penalties. Under the posterior band and square-root erasure summability, a loss cocycle that vanishes on every legal finite modification therefore implies attainment by that same law. For a finite hidden producer, actual conditional block factorizations impose a nonlinear discrepancy budget. Disjoint conditional blocks give additive lower bounds, with ordinary-rank determinants as sufficient detectors. The required discrepancy growth and the connection from hypothetical attainment to the strong zero-cocycle premise remain open. The arguments are ordinary mathematical proofs, without a kernel-verification claim.

## 1. Original objective, complete producer domain and supplied results

**Definition 1.1 (Complete open-path objective).** For $n\ge1$, retain

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

$B_0$ contains the empty word. The graph $\Gamma_n$ has all vertices in $B_n$ and every legal Hamming-one edge. An endpoint insertion uses $w_0=w_{n+1}=0$, without joining the endpoints. On the entire probability simplex put

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\quad
\Phi_n(\mu)=\sum_{\{u,v\}\in E(\Gamma_n)}h(\mu_u,\mu_v),\quad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
\tag{1.1}
$$

Zero masses do not remove vertices, edges or seam constraints. [Universal, Convention 1.3 and Lemma 2.1][U] supplies the positive finite optimizer $\pi_n=\pi^{(n)}$, its insertion inequalities, and the growth facts

$$
\Phi_n(\pi_n)=\kappa_n,\qquad
\tfrac13\pi_n(u)\le\pi_n(v)\le\pi_n(u)\quad(u\to v\text{ inserts one}),
\qquad nc_\star\le\kappa_n\le(n+1)c_\star,\qquad
\frac{\kappa_n}{n}\longrightarrow c_\star.
\tag{1.2}
$$

The ceiling $c_\star\le\bar c:=3-2\sqrt2<1/4$ is supplied in [Localization, Convention 1.3][L]. Uniqueness of $\pi_n$ is not needed here. These are the original finite optimizers, with all endpoint terms; no stationary or periodic optimizer is substituted.

**Definition 1.2 (Entire exact-real hidden domain).** For every finite $N\ge1$, use precisely [Universal, Definition 4.1][U]'s domain

$$
\Theta_N=\left\{(\lambda,M_0,M_1):
\begin{array}{l}
\lambda\ge0,\ \lambda\mathbf1=1,\ M_0,M_1\ge0,\\
A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0
\end{array}\right\}.
\tag{1.3}
$$

Here $\lambda$ is a row and $M_0,M_1$ are $N\times N$ exact-real matrices. Write $M_w=M_{w_1}\cdots M_{w_n}$ and $M_\varepsilon=I$, and let $[w]_a$ specify $X_a,\ldots,X_{a+|w|-1}=w$. The corresponding single actual stationary joint law, supplied by [Universal, Proposition 4.2][U], is

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P_\theta([w]_a)=\lambda M_w\mathbf1.
\tag{1.4}
$$

The visible marginal $P_\theta$ is supported on $\mathsf X$. Structural zeros, zero stationary masses, reducibility, periodicity and noncontractive presentations remain allowed. The scalar no11 condition is not replaced by entrywise $M_1^2=0$. Every seam uses the ordered product $\lambda M_uM_v\mathbf1$, without independence. The clock counts original emitted bits, with no regrouping or rescaling.

**Convention 1.3 (Original-law predictors and losses).** First let $P$ be any stationary Borel probability on $\mathsf X$; finite hidden structure is imposed only in §6. Let $P_n$ be its marginal on $[1,n]$. Set $(Tx)_i=x_{i+1}$, $\mathcal E_i=\sigma(X_j:j\ne i)$ and $F_i=\{X_{i-1}=X_{i+1}=0\}$. Choose a $[0,1]$ Borel exterior version of $q_0=\mathbb E_P[X_0\mid\mathcal E_0]$ and let $q_i=q_0\circ T^i$. Put

$$
\ell_i(x)=(x_i-q_i(x))^2,\qquad
q_{r,i}=\mathbb E_P[X_i\mid\sigma(X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r})],\qquad
D_r(P)=\mathbb E_P(X_0-q_{r,0})^2.
$$

The two-index $q_{0,i}$ denotes the prior mean, not the full exterior predictor $q_i$. [Universal, (1.5)][U] supplies

$$
D_r(P)\downarrow d(P)=\mathbb E_P\ell_0
=\lim_{n\to\infty}\frac{\Phi_n(P_n)}n\le c_\star.
\tag{1.5}
$$

Every loss evaluated after a modification is still this fixed function $\ell_i$ from $P$. A different measure used to integrate it does not redefine its predictor. Null finite fibers have arbitrary conditional versions and zero weighted contribution. A retained neighbor one forces the center posterior to zero; an omitted neighbor gives no such conclusion.

## 2. Band, erasure summability and the actual cocycle

**Definition 2.1 (Additional hypotheses).** The general-law results assume

$$
\mathsf B(P):\quad q_i=0\text{ on }F_i^c,\qquad
\tfrac14\le q_i\le\tfrac12\text{ on }F_i,
\quad P\text{-almost surely for every }i\in\mathbb Z,
\tag{2.1}
$$

and the following actual one-sided erasure condition:

$$
\begin{aligned}
p^L_j&=\mathbb E_P[X_0\mid X_{-j},\ldots,X_{-1},X_1,X_2,\ldots],&
e_L(j)&=\mathbb E_P(q_0-p^L_j)^2,\\
p^R_j&=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_j],&
e_R(j)&=\mathbb E_P(q_0-p^R_j)^2,\\
A_P&:=\sum_{j\ge0}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr)<\infty.
\end{aligned}
\tag{2.2}
$$

Each field retains the entire opposite half-line, also at $j=0$. In particular neither seam defect is discarded. [Universal, Theorem 3.1][U] makes the band necessary for attainment. No theorem here establishes (2.2) for every finite hidden law or every hypothetical attainer.

**Lemma 2.2 (Supplied surgery mechanism, with its general-law scope).** Let $C=[a,b]$, $L=b-a+1$, $Y=X_{C^c}$ and $\mu_C=\operatorname{law}_P(Y)$; choose Borel regular conditional masses $p_C(v;y)=P(X_C=v\mid Y=y)$. Exterior records lie in the projection of $\mathsf X$. A word $v\in B_L$ is compatible with $y$ when $y_{a-1}v_1=v_Ly_{b+1}=0$. Write $vy$ for its completion, $k(v)=\sum_i v_i$, and $Z_Cx=0^Lx_{C^c}$. Under the band (2.1), simultaneously for all finite intervals, almost every exterior satisfies

$$
p_C(0^L;y)\ge2^{-L},\qquad
3^{-k(v)}p_C(0^L;y)\le p_C(v;y)\le p_C(0^L;y)
\quad(v\text{ compatible}),
\tag{2.3}
$$

with zero mass on incompatible completions. Every measurable legal finite replacement is nonsingular for $P$. If also (2.2) holds, then with

$$
V_C(x)=\sum_{i\in\mathbb Z}|\ell_i(x)-\ell_i(Z_Cx)|,\qquad
B_L(P)=L+2(1+2^{L/2})A_P,
$$

one has $\mathbb E_PV_C\le B_L(P)<\infty$. There is a shift-invariant Borel conull set $\Omega\subseteq\mathsf X$, saturated under legal finite modifications, on which

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z))
\tag{2.4}
$$

is absolutely defined for every finitely differing pair. It is measurable, antisymmetric, additive on each finite-modification class and shift invariant. Any two fixed choices of original posterior versions give the same cocycle on a common saturated conull set.

Proof. This is [Localization, Theorem 3.1][L]'s construction. Its proof uses stationarity, the band and (2.2), but no hidden matrices. To make that general-law use explicit, the band gives, for every $H\in\mathcal E_i$,

$$
P(H,X_i=0)\ge\tfrac12P(H),\qquad
\tfrac13P(H,X_i=0)\le P(H,X_i=1)\le P(H,X_i=0)\quad(H\subseteq F_i).
$$

Condition on the exterior and successively specify the $L$ zeros. Then insert the nonadjacent ones of a compatible word, whose endpoint neighbors are zero when needed. Testing against every exterior event yields (2.3). This also includes $L=1$ and forced endpoints. Disintegration gives $(Z_C)_*P\le2^LP$; replacement by a fixed compatible $v$, restricted to its compatible exteriors, has density $\mathbf1_{\{X_C=v\}}/p_C(v;Y)$ there and is bounded by $2^L3^{k(v)}P$. The identity on incompatible exteriors makes a total nonsingular map. A measurable choice of a finite modification partitions into countably many interval-and-word choices, so it too preserves null sets. This support and domination argument uses only the band.

For an exterior site use the reduced predictor conditioning on the half-line outside $C$ containing that site, with the site itself omitted. This predictor is unchanged by $Z_C$. At distance $j$ from the left or right seam its mean squared difference from $q_i$ is respectively $e_R(j)$ or $e_L(j)$. Cauchy–Schwarz under $P$ and $(Z_C)_*P$ bounds the mean absolute posterior change by $(1+2^{L/2})\sqrt e$. Since $|(x-u)^2-(x-v)^2|\le2|u-v|$ on $\{0,1\}\times[0,1]^2$, summing both half-lines and the $L$ interior bounds proves the asserted $V_C$ estimate.

Take a Borel conull set where these bounds, conditional support statements and posterior identities hold for all intervals and sites. Intersect its inverse images under the countable monoid generated by shifts and all fixed legal interval replacements. Nonsingularity keeps the intersection conull, and composition makes it saturated. If $x,z$ differ only in $C$, then $Z_Cx=Z_Cz$ and

$$
\sum_i|\ell_i(x)-\ell_i(z)|\le V_C(x)+V_C(z)<\infty.
$$

Absolute convergence proves the cocycle identities; finite partial sums give measurability. Adding the countably many version-agreement sets before saturation proves the last assertion. This does not give one null set for an uncountable collection of all possible versions. $\square$

**Definition 2.3 (Strong zero).** Write $\mathsf Z_\Delta(P)$ when a saturated conull set as in Lemma 2.2 satisfies $\Delta_P(x,z)=0$ for every legal finitely differing pair in that set. This is an additional pathwise hypothesis.

The supplied first-order property is different: for $\mathcal H_C=\sigma(X_j:j\notin C)$ and $\mathbb E_P[f(X_C)\mid\mathcal H_C]=0$, the response $\sum_i\mathbb E_P[f(X_C)\ell_i]$ is absolutely convergent and zero under attainment; see [Localization, Convention 1.3 and Theorem 4.2][L]. Its conditional balances and [Two-word, Theorem 2.1][W]'s positive-pair exterior cancellation do not assert $\mathsf Z_\Delta(P)$. No implication from them, or from a rank bound, to strong zero is used.

## 3. Conditional Brier discrepancy on the legal completion graph

**Definition 3.1 (Boundary-conditioned finite score).** For $m\ge1$ and $a,b\in\{0,1\}$ put

$$
K_m^{a,b}=\{w\in B_m:aw_1=w_mb=0\}.
$$

Its graph contains every legal Hamming-one edge between these words. Deleting ones connects every vertex to $0^m$, including when the graph is a singleton. For a probability $p$ on $K=K_m^{a,b}$, let $p_i(w_{-i})$ be its single-site posterior. Forced singleton fibers have posterior zero; zero-total fibers have any version. For a strictly positive probability $r$ on $K$ define

$$
\begin{aligned}
\mathcal D_K(p\Vert r)
&=\sum_{i=1}^m\mathbb E_p\bigl(p_i(W_{-i})-r_i(W_{-i})\bigr)^2\\
&=\sum_{u\to v\text{ in }K}(p_u+p_v)
\left(\frac{p_v}{p_u+p_v}-\frac{r_v}{r_u+r_v}\right)^2.
\end{aligned}
\tag{3.1}
$$

A zero-total $p$ edge contributes zero without division. Let $\Phi_K(p)$ be the sum of $h(p_u,p_v)$ over this graph, so $\Phi_{B_m}=\Phi_m$.

**Lemma 3.2 (Projection and strict equality).** For the distributions just specified,

$$
\mathbb E_p\sum_{i=1}^m(W_i-r_i(W_{-i}))^2
=\Phi_K(p)+\mathcal D_K(p\Vert r),\qquad \mathcal D_K(p\Vert r)\ge0.
\tag{3.2}
$$

If both $p$ and $r$ are positive on $K$, equality $\mathcal D_K(p\Vert r)=0$ holds exactly when $p=r$.

Proof. Condition on $W_{-i}$ and expand the square around $p_i$. The cross term vanishes. The conditional variance, multiplied by that fiber's mass, is $h(p_u,p_v)$ for a free pair and zero for a forced singleton. Summing proves (3.2). Under positivity, zero discrepancy makes the two posteriors equal on every edge, hence $r_v/r_u=p_v/p_u$. Connectivity gives a constant ratio $r_w/p_w$ over $K$, and normalization makes it one. The singleton case has only one probability distribution. This establishes the equality case on the hard no11 domain itself. $\square$

**Lemma 3.3 (Band compactness floor).** Call $p$ band-compatible on $K$ when it is a probability satisfying $p_u/3\le p_v\le p_u$ on every insertion edge. These closed inequalities force positivity throughout $K$ and give

$$
p_{0^m}\ge|K|^{-1},\qquad
p_w\ge3^{-k(w)}p_{0^m}\ge\alpha_m:=6^{-m}.
\tag{3.3}
$$

Proof. Delete ones to see that every mass is at most $p_{0^m}$. Normalization gives the first inequality; insert them back to get the second. Use $|K|\le2^m$ and $k(w)\le m$ for the final bound. Thus band-compatible probabilities form a compact subset of the strictly positive simplex on $K$. Their free posteriors are exactly in $[1/4,1/2]$. $\square$

The projection identity and squared conditional discrepancy are mature conditional-scoring tools; [Dawid–Lauritzen–Parry, §4.2, Example 4.4 and (14)][DLP] gives this Brier score. That paper's full-product strict-propriety argument assumes everywhere-positive distributions. The graph argument above supplies the equality case needed for each constrained completion set, including forced fibers.

## 4. Independent guarded replacement and the exterior sign

**Definition 4.1 (One finite replacement coupling).** Fix $n\ge1$, $C=[0,n+1]$ and $L=n+2$. On the product probability space $P\otimes\nu$, let $X\sim P$, $W\sim\nu\in\mathcal P(B_n)$ independently. Keep $Y=X_{C^c}$ and set

$$
Z=R_{n,W}X=(0W0)Y,\qquad Q=Q_{n,\nu}=\operatorname{law}(Z).
\tag{4.1}
$$

Both guards belong to the replaced block. Consequently $Z$ is legal for every original exterior, and its joint $(Y,W)$ law is exactly $\mu_C\otimes\nu$. The auxiliary measure $Q$ need not be stationary or have a finite hidden presentation.

For almost every actual exterior set

$$
g_C(y)=P(X_0=X_{n+1}=0\mid Y=y),\qquad
r_n^y(w)=\frac{p_C(0w0;y)}{g_C(y)}.
\tag{4.2}
$$

These conditionals are from $P$, not from $Q$. Equation (2.3) gives $g_C\ge2^{-L}$ and positivity of $r_n^y$ on all $B_n$. On the exceptional exterior null set assign $r_n^y=\pi_n$; no conclusion depends on that choice. For $i\notin C$ choose a $[0,1]$ Borel version

$$
a_i^C=\mathbb E_P[X_i\mid\sigma(X_j:j\notin C,\ j\ne i)].
$$

It is a function of $Y$ without $Y_i$, so it has the same value before and after replacement. Define

$$
\begin{aligned}
E_C(P)&=\sum_{i\notin C}\mathbb E_P(q_i-a_i^C)^2,&
O_C(P,\nu)&=\sum_{i\notin C}\mathbb E_Q(q_i-a_i^C)^2,\\
G_C(P,\nu)&=\mathbb E_Q(q_0^2+q_{n+1}^2),&
\mathcal B_n(P,\nu)&=\mathbb E_{\mu_C}\mathcal D_{B_n}(\nu\Vert r_n^Y).
\end{aligned}
\tag{4.3}
$$

Every $q_i$ in these quantities is the fixed original-law function from Convention 1.3.

**Theorem 4.2 (Exact guarded identity).** For every stationary legal $P$ satisfying (2.1)–(2.2), and every $n,\nu$ as above, the cocycle difference is integrable, the nonnegative quantities in (4.3) are finite, and

$$
\mathbb E_{P\otimes\nu}\Delta_P(X,Z)
=(n+2)d(P)-\Phi_n(\nu)-\mathcal B_n(P,\nu)
-G_C(P,\nu)-E_C(P)-O_C(P,\nu).
\tag{4.4}
$$

This statement requires no finite hidden structure.

Proof. First justify support, versions and summation. Disintegration and (2.3) give the density

$$
\frac{dQ}{dP}(x)=
\begin{cases}\nu(w)/p_C(0w0;x_{C^c}),&x_C=0w0,\\0,&\text{otherwise},\end{cases}
\qquad Q\le K_nP,\qquad K_n:=2^{n+2}3^n.
\tag{4.5}
$$

Ratios are only used on the conull exterior set where their denominators are positive; elsewhere choose any version. Since $k(w)\le n$, the stated constant is sufficient for every $\nu$. It controls original posterior null sets under $Q$. By saturation, $X,Z\in\Omega$ almost surely in the coupling, and $Z_CX=Z_CZ$. Thus

$$
\mathbb E_{P\otimes\nu}\sum_i|\ell_i(X)-\ell_i(Z)|
\le\mathbb E_PV_C+\mathbb E_QV_C
\le(1+K_n)B_{n+2}(P)<\infty.
\tag{4.6}
$$

This is an estimate for each fixed $n$. It is not asserted uniform in $n$ or sublinear in the block length. No subtraction of two infinite loss totals is involved.

For an interior site $1\le i\le n$, condition the actual $P$ block kernel on the two guards and on all other middle bits. The defining conditional-expectation identity then gives

$$
q_i((0w0)y)=r_{n,i}^y(w_{-i}).
\tag{4.7}
$$

To justify the simultaneous reading, disintegrate each identity over $Y$ and the finitely many completions. Their strictly positive masses force it at every completion on a conull exterior set; take the countable intersection over intervals and sites. Hence (4.7) remains valid under (4.5), with the original $P$ versions. Under $Q$, $W$ has law $\nu$ independently of $Y$. Apply (3.2) on each exterior fiber to get

$$
\sum_{i=1}^n\mathbb E_Q\ell_i=\Phi_n(\nu)+\mathcal B_n(P,\nu).
\tag{4.8}
$$

The guards equal zero, so their losses sum to $G_C(P,\nu)$. The predictor from $\nu$ is used only to expand the square in (3.2); the scored predictor is still $q_i$ from $P$.

For an exterior site $i\notin C$, under $Q$ the inserted word is independent of $Y$. Given the other exterior coordinates and that word, the conditional mean of $Y_i$ is $a_i^C$. The $Q$ marginal of $Y$ is the original $\mu_C$. Two conditional projections therefore give

$$
\begin{aligned}
\mathbb E_Q\ell_i
&=\mathbb E_P(X_i-a_i^C)^2+\mathbb E_Q(q_i-a_i^C)^2,\\
\mathbb E_P\ell_i
&=\mathbb E_P(X_i-a_i^C)^2-\mathbb E_P(q_i-a_i^C)^2.
\end{aligned}
\tag{4.9}
$$

In the second line the reduced field is contained in $\mathcal E_i$. In the first, $q_i$ is measurable in the other coordinates under $Q$ as well as under $P$; it need not be the $Q$ conditional mean. Subtraction at this single site gives

$$
\mathbb E_Q\ell_i-\mathbb E_P\ell_i
=\mathbb E_P(q_i-a_i^C)^2+\mathbb E_Q(q_i-a_i^C)^2\ge0.
\tag{4.10}
$$

The sum of (4.10) over exterior sites is finite by (4.6), because each absolute difference of expectations is bounded by the corresponding coupled expected absolute difference. This proves finiteness of both exterior penalties and the required sign. Independently, the reduced field contains the outside half-line used in Lemma 2.2, so projection monotonicity gives

$$
E_C(P)\le\sum_{j\ge0}(e_L(j)+e_R(j))\le A_P.
\tag{4.11}
$$

Here the sites $-1-j$ and $n+2+j$ use $e_R(j)$ and $e_L(j)$, respectively. No analogous uniform estimate for $O_C$ is asserted. Finally (4.6) permits summing the coupled differences. The original losses on $C$ have expectation $(n+2)d(P)$ by stationarity; subtract (4.8), the guard losses and (4.10). This gives (4.4). $\square$

## 5. Strong zero implies actual attainment and a finite budget

**Theorem 5.1 (Sufficient strong endpoint).** If a stationary legal law satisfies $\mathsf B(P)$, $A_P<\infty$ and $\mathsf Z_\Delta(P)$, then this same law attains $d(P)=c_\star$.

Proof. In (4.4) take $\nu=\pi_n$. Its left side is zero by strong zero, and all four penalties are nonnegative. Thus $(n+2)d(P)\ge\kappa_n$ for every $n$. Dividing by $n+2$ and using (1.2) gives $d(P)\ge c_\star$. Equation (1.5) gives equality. Only scalar inequalities are passed to a limit; each finite replacement has its own integrability bound (4.6). $\square$

**Lemma 5.2 (Positive guard cost).** Under $\mathsf B(P)$ and the construction with $\nu=\pi_n$,

$$
G_C(P,\pi_n)\ge\frac1{24}.
\tag{5.1}
$$

Proof. Let $\rho=P(X_0=1)$. Stationarity and the band give

$$
\rho=\mathbb E_Pq_0\le\tfrac12P(F_0)
\le\tfrac12P(X_{-1}=0)=\tfrac12(1-\rho),
$$

so $1-\rho\ge2/3$. The optimizer's insertion inequalities imply $\pi_n(W_1=0)\ge1/2$ and $\pi_n(W_n=0)\ge1/2$: in each free endpoint fiber the one mass is no greater than the zero mass, and forced endpoints are zero. Under $Q$, the guard at zero is free on $\{Y_{-1}=0,W_1=0\}$, and the other on $\{W_n=0,Y_{n+2}=0\}$. Independence of $W$ and $Y$ gives their respective probabilities. Since $Q\ll P$, each free guard has $q_i^2\ge1/16$. Hence

$$
G_C(P,\pi_n)\ge\frac{1-\rho}{16}
\bigl[\pi_n(W_1=0)+\pi_n(W_n=0)\bigr]\ge\frac1{24}.
$$

For $n=1$ the two displayed word bits coincide, but the proof adds two expectations and requires no independence between them. $\square$

**Corollary 5.3 (Same-law discrepancy budget).** Under Theorem 5.1's hypotheses, for every $n\ge1$,

$$
\begin{aligned}
\mathcal B_n(P,\pi_n)+G_C(P,\pi_n)+E_C(P)+O_C(P,\pi_n)
&=(n+2)c_\star-\kappa_n,\\
\mathcal B_n(P,\pi_n)
&\le(n+2)c_\star-\kappa_n-\tfrac1{24}
\le2c_\star-\tfrac1{24}\le2\bar c-\tfrac1{24}.
\end{aligned}
\tag{5.2}
$$

Proof. Use Theorem 5.1 in (4.4), then (5.1) and $\kappa_n\ge nc_\star$. $\square$

The supplied attainment consequences now apply to this actual $P$: [Universal, Theorem 3.1][U] gives $nc_\star\le\Phi_n(P_n)$, and [Localization, Convention 1.3][L] supplies the attained-law projection and null-response bounds. These are consequences of Theorem 5.1, not premises assigned to a low-risk band example. The theorem neither constructs a strong-zero law nor proves its premise from attainment, first-order balance or finite rank. The budget alone is not asserted sufficient for attainment.

## 6. Actual hidden factorization, full exterior limit and compact relaxation

**Definition 6.1 (Probability flattening).** For a probability $r$ on $K_m^{a,b}$ extend it by zero to every binary word of length $m$. Its cut at $1\le k<m$ is the matrix

$$
\mathsf F_k(r)(s,t)=r(st),\qquad
s\in\{0,1\}^k,\quad t\in\{0,1\}^{m-k}.
$$

Every forbidden internal or boundary seam has its zero entry. Nonnegative rank $\operatorname{rank}_+$ is the least number of nonnegative rank-one summands.

**Theorem 6.2 (Conditional rank from the original matrices).** Impose $P=P_\theta$ for a fixed $\theta\in\Theta_N$ and assume the band. For every $n$, the actual guarded conditional $r_n^y$ in (4.2) is band-compatible and satisfies

$$
\operatorname{rank}_+\mathsf F_k(r_n^y)\le N\quad(1\le k<n)
\tag{6.1}
$$

for $\mu_C$-almost every exterior. This assertion itself does not require $A_P<\infty$ or strong zero.

Proof. Let $u=X_{[-m,-1]}$ and $v=X_{[n+2,n+1+m]}$ be finite adjacent exterior collars. Condition additionally on the guard event $H=\{X_0=X_{n+1}=0\}$. On a positive conditioning event the actual conditional mass is

$$
r_{n,m}^{u,v}(w)=
\frac{\lambda M_uM_0M_wM_0M_v\mathbf1}{Z_m(u,v)},\qquad
Z_m(u,v)=\sum_{z\in B_n}\lambda M_uM_0M_zM_0M_v\mathbf1>0.
\tag{6.2}
$$

For any binary split $w=st$, its numerator is

$$
\lambda M_uM_0M_sM_tM_0M_v\mathbf1
=\sum_{h=1}^N(\lambda M_uM_0M_s)_h(M_tM_0M_v\mathbf1)_h.
\tag{6.3}
$$

Thus the whole probability flattening is a sum of at most $N$ nonnegative rank-one matrices, with the positive normalizer absorbed into one factor. Illegal words or seams give actual zero cylinder probabilities. Their nonnegative scalar sums in (6.3) are zero without requiring entrywise $M_1^2=0$. Null collar events are not divided by.

Now work under $P^H=P(\cdot\mid H)$; $P(H)>0$ by (2.3). The increasing collar fields generate the full exterior field. Bounded conditional-expectation convergence, applied to each of the finitely many middle-word indicators, gives $r_{n,m}^{u,v}(w)\to r_n^Y(w)$ almost surely under $P^H$. The exterior marginal under this measure is

$$
d\mu_C^H(y)=\frac{g_C(y)}{P(H)}\,d\mu_C(y),\qquad g_C(y)\ge2^{-(n+2)}.
\tag{6.4}
$$

These exterior measures are equivalent. Consequently the coordinatewise limit is valid on a $\mu_C$-conull set, with the actual conditional versions in (4.2). This is a limit of increasing collars, not finite visible memory.

For a fixed finite matrix size, the probability matrices of nonnegative rank at most $N$ form a closed set. Indeed any such matrix can be written

$$
R=\sum_{h=1}^Nt_h a_hb_h^{\mathsf T},\qquad
t_h\ge0,\quad\sum_ht_h=1,
\tag{6.5}
$$

where each $a_h,b_h$ is a probability vector. Normalize each nonzero pair of nonnegative factors by its two coordinate sums and use their product as $t_h$; choose arbitrary probability factors at weight zero. The total matrix mass is one, so the weights sum to one. Conversely (6.5) has the required rank bound. Its parameter space is a compact product of finite simplexes and its image is continuous, hence compact and closed. Passing (6.3) to the limit proves (6.1), simultaneously over the finitely many cuts and countably many lengths.

Finally condition the integrated insertion inequalities from Lemma 2.2 on $Y$, both guards and all other middle bits. For each legal edge $u\to v$ this gives $p_C(0u0;y)/3\le p_C(0v0;y)\le p_C(0u0;y)$ almost surely. Division by the same positive $g_C(y)$ proves band compatibility, using only the band and conditional support. All statements concern the same matrices and joint law (1.4); no trimming, mixing or hidden-state minimality is used. $\square$

This is an $N$-term factorization for a probability flattening at a fixed actual exterior. It is not the context-by-word matrix $E_{\theta,L}$ of [Intrinsic, Theorem 2.2][I], with the general upper bound $\operatorname{rank}E_{\theta,L}\le N^2$. The latter tests linear conditional nullity. Neither its finite collar nor its annihilator turns a full posterior into a finite visible function.

**Definition 6.3 (Closed rank family and nonlinear minimum).** Let $\mathscr F_{N,m}^{a,b}$ be the band-compatible probabilities on $K_m^{a,b}$ for which every internal cut has nonnegative rank at most $N$. It is compact by (3.3), closed band inequalities and (6.5). It may be empty. For a band-compatible $p$ on $K_m^{a,b}$ put

$$
\delta_{N,m}^{a,b}(p)=\min_{r\in\mathscr F_{N,m}^{a,b}}
\mathcal D_{K_m^{a,b}}(p\Vert r),\qquad
\mathcal R_{N,n}=\delta_{N,n}^{0,0}(\pi_n),\qquad \min\varnothing:=+\infty.
\tag{6.6}
$$

All denominators on compatible edges have the positive floor (3.3), so the discrepancy is continuous and a nonempty minimum is attained. For $m=1$ there are no internal cuts. A singleton completion set has its unique probability and zero discrepancy. Unsupported complement slices have zero weight and no conditional denominator. For nonempty $\mathscr F$, strict equality in Lemma 3.2 gives $\delta(p)=0$ exactly when $p\in\mathscr F$; empty sets have the stated infinite value.

**Corollary 6.4 (Necessary finite-hidden budget).** If a fixed $\theta\in\Theta_N$ satisfies $\mathsf B(P_\theta)$, $A_{P_\theta}<\infty$ and $\mathsf Z_\Delta(P_\theta)$, then for every $n\ge1$,

$$
\mathcal R_{N,n}\le(n+2)c_\star-\kappa_n-\tfrac1{24}
\le2\bar c-\tfrac1{24}.
\tag{6.7}
$$

Proof. Theorem 6.2 puts $r_n^Y$ in the minimizing family almost surely, so $\mathcal B_n(P,\pi_n)\ge\mathcal R_{N,n}$. Apply (5.2). $\square$

**Proposition 6.5 (One-way common-transfer refinement).** Keep the same original pair $M=(M_0,M_1)$ for all lengths. For nonnegative boundary vectors $a,b$ with positive normalizer, first form probabilities on the full binary cube,

$$
t_{a,b,n}(w)=\frac{aM_0M_wM_0b}
{\sum_{z\in\{0,1\}^n}aM_0M_zM_0b},\qquad w\in\{0,1\}^n.
\tag{6.8}
$$

Let $\mathscr T_n(M)$ be the closure of this family in that full simplex, intersected with probabilities supported on $B_n$ and band-compatible there. This compact family contains every actual $r_n^y$ almost surely and is contained in $\mathscr F_{N,n}^{0,0}$. Therefore

$$
\mathcal R_{N,n}\le
\min_{r\in\mathscr T_n(M)}\mathcal D_{B_n}(\pi_n\Vert r)
\le\mathcal B_n(P,\pi_n),
\tag{6.9}
$$

and its middle quantity also obeys (6.7) under strong zero.

Proof. In (6.2) take $a=\lambda M_u$, $b=M_v\mathbf1$. Actual legality makes the full binary denominator in (6.8) equal the legal denominator in (6.2). The limit (6.4) puts the actual conditionals in the closure; their band and support give membership in the intersection. For arbitrary $a,b$, the untruncated full-cube probabilities still factor as in (6.3), so (6.5) preserves all cut bounds through closure and intersection. This proves both inclusions and (6.9). $\square$

The full-cube normalization in (6.8) is essential: arbitrary boundary vectors can give mass to paths invisible under the original stationary row. Deleting their illegal entries before normalization is not an operation known to preserve the factorization. Even the refined family only gives a necessary envelope; boundary vectors need not arise from one exterior process. The looser all-cut family guarantees neither a common nonnegative tensor representation with these state bounds, nor a stationary producer, nor common matrices across $n$. It is used only in the lower-bound direction.

## 7. Additive conditional-block discrepancies

**Theorem 7.1 (Disjoint-block accumulation under one optimizer).** Fix $N,n\ge1$ and disjoint nonempty intervals $C_1,\ldots,C_J\subseteq[1,n]$. For $W\sim\pi_n$, let $\eta=W_{[1,n]\setminus C_j}$ denote the entire complement of the indicated block and set

$$
p_j^\eta(w)=\pi_n(W_{C_j}=w\mid W_{[1,n]\setminus C_j}=\eta).
$$

Let $a_j(\eta),b_j(\eta)$ be the adjacent complement bits, using zero at an open endpoint of $[1,n]$. On every extendible complement the conditional is positive and band-compatible on $K_{|C_j|}^{a_j,b_j}$. Then

$$
\mathcal R_{N,n}\ge\sum_{j=1}^J
\mathbb E_{\pi_n}\delta_{N,|C_j|}^{a_j,b_j}(p_j^\eta).
\tag{7.1}
$$

Proof. If the whole-word minimizing family is empty, the left side is $+\infty$ and the inequality holds in the extended order. Otherwise fix any $r\in\mathscr F_{N,n}^{0,0}$. Both $r$ and $\pi_n$ are positive on every legal word, so they give positive probability to exactly the extendible complement words. For each such $\eta$, let $r_j^\eta$ be the corresponding conditional under this same $r$. Fixing the complement preserves all internal insertion ratios and the same two boundary constraints.

At an internal cut of $C_j$, fixing the prefix outside $C_j$ selects rows of the corresponding whole-word flattening, and fixing its outside suffix selects columns. Dividing this submatrix by the positive complement probability gives the conditional flattening. Restriction and positive scaling cannot increase nonnegative rank. Hence $r_j^\eta\in\mathscr F_{N,|C_j|}^{a_j,b_j}$.

For a site in $C_j$, conditioning on all other $n$ bits is exactly conditioning within this block given its complete complement. Disintegrating (3.1) at those sites therefore gives

$$
\sum_{i\in C_j}\mathbb E_{\pi_n}(\pi_{n,i}(W_{-i})-r_i(W_{-i}))^2
=\mathbb E_{\pi_n}\mathcal D_{K_{|C_j|}^{a_j,b_j}}(p_j^\eta\Vert r_j^\eta)
\ge\mathbb E_{\pi_n}\delta_{N,|C_j|}^{a_j,b_j}(p_j^\eta).
$$

The disjoint intervals count each site at most once; the omitted sites have nonnegative discrepancies. Sum, then minimize over $r$, to prove (7.1). Every reference conditional $p_j^\eta$ and every weight is from this one $\pi_n$; the comparison conditionals all come from the same candidate $r$. Blocks may be adjacent or dependent. Disjointness prevents double counting and asserts no independence. $\square$

In particular $p_j^\eta$ cannot be replaced by the stand-alone optimizer $\pi_{|C_j|}$ or by a limiting stationary law without an additional proved bridge. No such bridge is assumed.

## 8. Ratio coercivity and a sufficient determinant bound

**Lemma 8.1 (Finite discrepancy controls probability distance).** If $p,r$ are band-compatible on $K=K_m^{a,b}$, then

$$
\mathcal D_K(p\Vert r)\ge\frac{6^{-4m}}{2m}\|p-r\|_1^2.
\tag{8.1}
$$

Proof. Write $t_w=r_w/p_w$ and $\alpha=6^{-m}$. At an insertion edge $u\to v$, its exact contribution to (3.1) is

$$
\frac{(p_up_v)^2(t_u-t_v)^2}{(p_u+p_v)(r_u+r_v)^2}
\ge\alpha^4(t_u-t_v)^2,
\tag{8.2}
$$

because all compatible masses are at least $\alpha$ and both pair sums are at most one. Any two words can be joined by deleting ones and then inserting ones through $0^m$, in at most $2m$ edges. Removing repetitions gives a simple path. Cauchy–Schwarz on it yields

$$
(\max_wt_w-\min_wt_w)^2\le\frac{2m}{\alpha^4}\mathcal D_K(p\Vert r).
$$

Since $\sum_wp_wt_w=1$, the number one lies between the minimum and maximum ratios. Therefore $\|p-r\|_1=\sum_wp_w|1-t_w|\le\max t-\min t$, proving (8.1). If $K$ is a singleton, $p=r$ and the conclusion is immediate. $\square$

**Theorem 8.2 (Minor bound and its additive consumer).** Let $p$ be band-compatible on $K_m^{a,b}$. Select any $(N+1)\times(N+1)$ minor $A_p$ of an internal-cut flattening, retaining forbidden entries as zeros. Then

$$
\delta_{N,m}^{a,b}(p)\ge
\frac{6^{-4m}}{2m(N!)^2}|\det A_p|^2.
\tag{8.3}
$$

Consequently, for disjoint length-$m$ intervals as in Theorem 7.1, choose such a cut and minor for each supported complement, and obtain

$$
\mathcal R_{N,n}\ge\frac{6^{-4m}}{2m(N!)^2}
\sum_{j=1}^J\mathbb E_{\pi_n}|\det A_{p_j^\eta}|^2.
\tag{8.4}
$$

A selection may depend on the finite complement. A cut too small for the specified minor supplies no determinant contribution.

Proof. For $r\in\mathscr F_{N,m}^{a,b}$ the corresponding minor $A_r$ has determinant zero, since ordinary rank is at most nonnegative rank. In the permutation formula, telescope each difference of products of $N+1$ entries. All entries lie in $[0,1]$, so that product difference is bounded by the sum of its entry differences. Each matrix entry appears in $N!$ permutations. Hence

$$
|\det A_p|=|\det A_p-\det A_r|
\le N!\sum_{\text{minor entries}}|p-r|
\le N!\|p-r\|_1.
\tag{8.5}
$$

The selected entries correspond to distinct words in the flattening; forbidden entries are zero for both probabilities. Combine (8.5) with (8.1) and minimize over $r$. Empty families satisfy (8.3) by the infinite-minimum convention. Applying this pointwise in (7.1) proves (8.4). $\square$

A nonzero selected minor is sufficient to force a positive discrepancy. Vanishing of all these minors only bounds ordinary rank: nonnegative rank can be larger. Thus determinants do not characterize membership in $\mathscr F$, let alone actual stationary realizability. No minor value or conditional expectation is asserted here without its displayed hypothesis.

## 9. Conditional exclusion, growth obligation and the original question

**Corollary 9.1 (Conditional strong-endpoint exclusion).** If for a specified $N$ and some $n$ one establishes

$$
\mathcal R_{N,n}>2(3-2\sqrt2)-\tfrac1{24},
\tag{9.1}
$$

then no $\theta\in\Theta_N$ can simultaneously satisfy $\mathsf B(P_\theta)$, $A_{P_\theta}<\infty$ and $\mathsf Z_\Delta(P_\theta)$. A lower bound from (7.1) or (8.4) exceeding this threshold suffices.

Proof. Such a law would violate (6.7). More explicitly, for any actual $P=P_\theta$ satisfying the band and (2.2), without assuming strong zero, (4.4), (5.1) and Theorem 6.2 give

$$
\begin{aligned}
\mathbb E_{P\otimes\pi_n}\Delta_P(X,R_{n,W}X)
&\le(n+2)c_\star-\kappa_n-\tfrac1{24}-\mathcal R_{N,n}\\
&\le2\bar c-\tfrac1{24}-\mathcal R_{N,n}.
\end{aligned}
\tag{9.2}
$$

Existence of this actual law already makes its rank family nonempty and its discrepancy finite. If that family is empty, Theorem 6.2 directly rules out the assumed band law. Otherwise (9.1) makes (9.2) negative. The left side is the finite weighted sum over $w\in B_n$ of $\pi_n(w)\mathbb E_P\Delta_P(X,R_{n,w}X)$. Each term is integrable by (4.6) with $\nu=\delta_w$. At least one fixed word therefore has negative expectation and $\Delta_P(X,R_{n,w}X)<0$ on a set of positive actual probability. This contradicts strong zero and gives an actual finite-modification witness. It need not give an intrinsic-null direction or a nonzero first-order response. $\square$

**Open Problem 9.2 (Quantitative growth not supplied by rank alone).** For each intended $N$, prove (9.1), or an adequate common-transfer violation in (6.9), or construct an actual finite law satisfying the strong endpoint. None is supplied here. One sufficient growth statement would give fixed $m$, positive $\varepsilon,\beta$, and arbitrarily large $n$ with disjoint length-$m$ blocks satisfying $J\ge\beta n$ and

$$
\frac1J\sum_j\mathbb E_{\pi_n}|\det A_{p_j^\eta}|^2\ge\varepsilon.
\tag{9.3}
$$

Then (8.4) would diverge along those $n$ and eventually exceed the fixed threshold. Positivity, finite dimension, strict propriety, or a single nonzero minor do not prove (9.3). The conditionals in (9.3) still use the complete complement under the same $\pi_n$; no uniform bulk limit or lower bound is assumed. Failure of this relaxation to exclude the endpoint would not construct a common producer.

**Open Problem 9.3 (Unchanged finite-attainment alternative).** On the entire original domain (1.3), set

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
$$

Still decide whether some finite exact-real producer attains $c_\star$, or whether $C_N<c_\star$ for every finite $N$. [Universal, Theorem 6.2][U] gives attainment of $C_N$, $C_N=\inf_rU_{N,r}$ and the equivalence of the negative alternative with

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\kappa_m/(m+1).
\tag{9.4}
$$

Theorem 5.1 would turn an actual finite strong-zero producer into a positive answer. No such producer is constructed. Conversely, excluding strong zero would resolve (9.4) only after an upstream implication from hypothetical attainment or its first-order balances to strong zero, together with the needed summability, or another complete exclusion argument. Those bridges remain unproved. There is no claim that attainment implies a stronger rigidity property merely because that property would be useful.

The band and $A_P$ are explicit hypotheses of the present route, not changes to $\Theta_N$. For $N=1$, scalar legality gives $M_1=0$ and the all-zero visible law, which fails the free posterior band; this boundary observation does not replace the arbitrary-$N$ question. The arguments permit original stationary mixtures and never optimize separate components and combine them as one realization. No fixed-$N$ uniform margin, efficient radius, effective optimization algorithm, common family of minimizing matrices, or empirical learning benefit follows from these bounds.

## 10. Mathematical ownership and bounded primary comparison

The compound consumer consists of the exact independent replacement identity (4.4), the strong-zero implication in Theorem 5.1, and the conditional-rank budgets and accumulation in §§6–9. This is a synthesis relative to the supplied canonical results. The original domain, finite optimizers, growth bounds, actual-law correspondence and cocycle construction keep their source ownership; projection, matrix factorization, conditional convergence, compactness and the determinant expansion are mature tools. The rank discrepancy is nonlinear in a probability law and compares it with $\pi_n$; it is not a repackaging of an intrinsic annihilator or a finite-visible-memory exclusion.

| Source | Exact use and boundary |
| --- | --- |
| [Universal][U], Convention 1.3, Lemma 2.1, Theorem 3.1, Definition 4.1, Proposition 4.2 and Theorem 6.2 | Original optimizer and growth interfaces, actual $J_\theta/P_\theta$, necessary band and support, entire compact-domain separation equivalence. The finite optimizer and its original square-discrepancy identity remain supplied results. |
| [Localization][L], Definitions 2.1–2.2, Theorem 3.1, Convention 1.3 and Theorem 4.2 | Legal-surgery domination, square-root integrability and the original loss cocycle. Lemma 2.2 states the same proof's general stationary-law scope. The existing first-order conditional balances do not supply strong zero. |
| [Intrinsic][I], Theorems 2.2 and 3.2, Corollary 3.4 | Exact conditional-null collar and linear dual residual distinguish the earlier response interface from the probability cut-rank constraint. No productive sign is transferred. |
| [Two-word][W], Theorems 2.1 and 3.1 | Existing positive-pair exterior cancellation and finite response certificate. Their existence and productivity hypotheses are not replaced by the rank budget. |
| [Dawid, Lauritzen and Parry][DLP], arXiv:1104.2224v2, complete §4.2, including Examples 4.3–4.4 and (12)–(14) | Conditional Brier scoring and squared conditional discrepancy. Its strict-propriety argument uses everywhere-positive full-product laws; §3 provides the constrained-graph equality argument. No statistical-performance theorem is imported. |
| [Balle, Panangaden and Precup][BPP], arXiv:1501.06841v3, §§2.2 and 3.1 | Real weighted realizations and the explicit forward–backward product factorization. No positivity realization follows from real Hankel rank. The summable-series SVD, canonical-form, approximation and minimality results are not used: stationary cylinder probabilities have total mass one at every length, not over all finite words. Probability nonnegative-rank closure is proved in (6.5). |
| [Van Enter and Verbitskiy][EV], arXiv:1001.3122v1, §§2–3, Definition 4, Theorems 5–6 and §3.2's local-variational discussion | Exterior Shannon uncertainty and variations preserving the exterior marginal are a conceptual comparison. The specification conclusion adds a Gibbs hypothesis; no Shannon-to-Brier, Gibbs or isomorphism-invariance conclusion is used. The finite-state language in the isomorphism discussion concerns a finite alphabet, not a fixed hidden-state budget. |
| [Chazottes and Ugalde][CU], arXiv:0907.0528v4, §§2–3, especially Theorem 3.1 and its proof there | The stated theorem starts with a real Hölder potential on a full shift and a symbol amalgamation onto another full shift; its locally constant case retains those hypotheses. It does not establish the needed posterior regularity or $A_P$ for all scalar-no11 presentations with structural zeros. |

These primary passages support the indicated credits and restrictions only. They establish neither worldwide priority for this synthesis nor absence of another solution. The results here are handwritten mathematics, without a formal-verification, source-admission or original-target-completion claim.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[L]: FIB_LEGAL_EDGE_LOAD_EXTERIOR_LOCALIZATION_AND_ACTUAL_LOSS_COCYCLE_BALANCE.md
[I]: FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md
[W]: FIB_LEGAL_EDGE_LOAD_TWO_WORD_EXTERIOR_CANCELLATION_AND_VANISHING_CERTIFICATE.md
[DLP]: https://arxiv.org/html/1104.2224v2 "A. Philip Dawid, Steffen Lauritzen and Matthew Parry, Proper Local Scoring Rules on Discrete Sample Spaces"
[BPP]: https://arxiv.org/html/1501.06841v3 "Borja Balle, Prakash Panangaden and Doina Precup, A Canonical Form for Weighted Automata and Applications to Approximate Minimization"
[EV]: https://arxiv.org/html/1001.3122v1 "A. C. D. van Enter and Evgeny Verbitskiy, Erasure entropies and Gibbs Measures"
[CU]: https://arxiv.org/html/0907.0528v4 "Jean-Rene Chazottes and Edgardo Ugalde, On the preservation of Gibbsianness under symbol amalgamation"

## 追加锚（本行以下为增补区）
