# FIB harmonic-edge load: two-word exterior cancellation and a vanishing certificate

This volume gives ordinary mathematical proofs, without a Lean kernel claim. Its main result is exact cancellation of every exterior response for a positive two-word conditional-null direction. Applied to [Conditional Response][R], this removes the constant exterior allowance from its finite certificate. The five-state illustration also has a cheaper radius-two risk exclusion; that exclusion is not the reason for the general mechanism.

## 1. Complete domain and same-law interfaces

For $n\ge1$ retain the entire open-path word set and harmonic objective

$$
B_n=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},\qquad
h(s,t)=\begin{cases}st/(s+t)&s+t>0,\\0&s=t=0,\end{cases}
$$

$$
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad c_\star=\lim_n\kappa_n/n.
$$

$\Gamma_n$ has every legal Hamming-one edge, including endpoint insertions with the convention $w_0=w_{n+1}=0$. No first-to-last constraint is imposed. All-zero words, endpoint ones, every legal seam, and zero-mass vertices and edges remain present.

Let $P$ be one normalized Borel probability law on $X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\text{ for all }i\}$, with coordinates $X_i$. Set $\mathcal E_i=\sigma(X_j:j\ne i)$, choose $[0,1]$ Borel versions $q_i=\mathbb E_P[X_i\mid\mathcal E_i]$, and put $\ell_i=(X_i-q_i)^2$. For $r\ge0$, let $\mathcal F_{r,i}=\sigma(X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r})$ and $q_{r,i}=\mathbb E_P[X_i\mid\mathcal F_{r,i}]$; at $r=0$ this field is trivial. All expectations and versions below belong to this same $P$.

For stationary $P$, [Stationary, §2][S] supplies

$$
d(P)=\lim_n\Phi_n(P_n)/n=\mathbb E_P\ell_0=\inf_rD_r(P)\le c_\star,
\qquad D_r(P)=\mathbb E_P(X_0-q_{r,0})^2.
\tag{1.1}
$$

Neighbor-one fibers force the center and its posterior to zero. Zero-total finite fibers have zero weighted contribution and require no division. These identities retain the original endpoint terms and emitted-bit integer clock.

For any finite $N$, the full producer domain is [Universal, Definition 4.1][U]:

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,\ M_0,M_1\ge0,
\ A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.2}
$$

The matrices are $N\times N$, the row is $N$-dimensional, and entries are exact reals. Zero stationary masses, structural zeros, reducibility and periodicity are allowed. [Universal, Proposition 4.2][U] constructs one coherent two-sided stationary joint law with visible cylinders $P_\theta([w])=\lambda M_w\mathbf1$, where $M_w$ is the ordered letter product and $M_\varnothing=I$.

Two interfaces from [Conditional Response][R] are used only under their stated attainment hypothesis $d(P)=c_\star=c$: its Theorem 3.1 gives $S_P(f)=\sum_{i\in\mathbb Z}\mathbb E_P[f_C\ell_i]=0$ when $\mathbb E_P[f_C\mid\mathcal H_C]=0$, and its equation (2.2) gives

$$
0\le D_r(P)-c\le c/(r+1),\qquad c_\star\le\bar c:=3-2\sqrt2.
\tag{1.3}
$$

Here $C=[1,L]$ and $\mathcal H_C=\sigma(X_j:j\notin C)$. The growth ceiling is the ordinary bound cited in that supplier. No attained-law budget is assumed for an arbitrary candidate.

## 2. Positive two-word cancellation before attainment

**Theorem 2.1 (Common exterior law and actual posterior restrictions).** Let $P$ be any law on $X$, without stationarity or hidden-state assumptions. Take distinct $a,b\in B_L$ with events $E_a=\{X_C=a\}$, $E_b=\{X_C=b\}$ of positive probability, and $\alpha,\beta>0$. Define $f(a)=\alpha$, $f(b)=-\beta$, and $f(w)=0$ on every other $w\in B_L$. Suppose

$$
f_C=\alpha\mathbf1_{E_a}-\beta\mathbf1_{E_b},\qquad
\mathbb E_P[f_C\mid\mathcal H_C]=0.
\tag{2.1}
$$

Then the full exterior laws conditioned on $E_a$ and $E_b$ coincide, and

$$
\mathbb E_P[f_C\ell_i]=0\quad(i\notin C),\qquad
S_P(f)=\sum_{i=1}^L\mathbb E_P[f_C\ell_i],\qquad
\sum_{i\in\mathbb Z}|\mathbb E_P[f_C\ell_i]|\le LJ,
\quad J:=\alpha P(E_a)=\beta P(E_b)>0.
\tag{2.2}
$$

**Proof.** For every $H\in\mathcal H_C$, (2.1) gives $\alpha P(E_a\cap H)=\beta P(E_b\cap H)$. Taking $H=X$ proves the balance defining $J$. Division by the two positive masses proves equality of the exterior pushforward measures of $P(\cdot\mid E_a)$ and $P(\cdot\mid E_b)$; denote their common probability law by $\nu$ on exterior records $Y=(X_j)_{j\notin C}$.

Fix $i\notin C$ and set $\mathcal H_i^{\rm ext}=\sigma(Y_j:j\notin C,j\ne i)$. On either block event the block coordinates are constants, so the trace of $\mathcal E_i$ is exactly the field of the other exterior coordinates. Thus the restrictions of $q_i$ are represented by $\mathcal H_i^{\rm ext}$-measurable functions $q_i^a,q_i^b$ of $Y$. For every $G\in\mathcal H_i^{\rm ext}$, the actual defining conditional-expectation identity, tested on $E_a\cap\{Y\in G\}\in\mathcal E_i$, gives

$$
\int_G(Y_i-q_i^a)\,d\nu
=\frac1{P(E_a)}\int_{E_a\cap\{Y\in G\}}(X_i-q_i)\,dP=0.
$$

The same identity holds with $b$. Both restrictions are therefore versions of $\mathbb E_\nu[Y_i\mid\mathcal H_i^{\rm ext}]$. Uniqueness under the same $\nu$ gives $q_i^a=q_i^b$ almost surely, hence

$$
\mathbb E_P[\ell_i\mid E_a]=\mathbb E_P[\ell_i\mid E_b],\qquad
\mathbb E_P[f_C\ell_i]=J\bigl(\mathbb E_P[\ell_i\mid E_a]-\mathbb E_P[\ell_i\mid E_b]\bigr)=0.
$$

This includes $i=0,L+1$, regardless of the selected endpoint bits. It does not assert that $\ell_i$ is globally $\mathcal H_C$-measurable. Positive-event conditioning preserves every $P$-null exception; the common exterior pushforwards preserve the corresponding $\nu$-null exceptions. Countably many sites admit a simultaneous conull choice. For each interior site, $0\le\ell_i\le1$ gives $|\mathbb E_P[f_C\ell_i]|\le J$. Only $L$ terms remain, proving absolute convergence and (2.2). $\square$

The proof works unchanged for arbitrary binary laws on the countable product space; legality is needed for the FIB consumer, not for this probability identity. If a selected word has zero mass, (2.1) with positive coefficients forces both weighted masses to be zero. Then $f_C=0$ almost surely and cannot be productive. Equality of finite exterior laws suffices only because finite cylinders generate the entire exterior field and the measures extend uniquely.

## 3. The P8 finite certificate with no constant allowance

For a stationary law satisfying Theorem 2.1, put $F=\max(\alpha,\beta)$ and retain precisely the finite response of [Conditional Response, equation (4.1)][R]:

$$
T_{L,r}(P,f)=\sum_{i=1}^L\mathbb E_P[f_C(X_i-q_{r,i})^2].
\tag{3.1}
$$

**Theorem 3.1 (Necessary bound, strict certificate and finite detectability).** Under these pair hypotheses, attainment by this same law implies, for every integer $r\ge0$,

$$
|T_{L,r}(P,f)|\le2LF\sqrt{\frac{c_\star}{r+1}}.
\tag{3.2}
$$

Consequently any verified strict inequality

$$
|T_{L,r}(P,f)|>2LF\sqrt{\frac{\bar c}{r+1}}
\tag{3.3}
$$

implies $d(P)<c_\star$. Moreover, if the pair is productive, meaning $S_P(f)\ne0$, every sufficiently large finite $r$ satisfies (3.3), without an attainment assumption in this detectability statement.

**Proof.** Under attainment, the supplied zero-total-response theorem and (2.2) make the interior sum zero. Conditional projection and stationarity give

$$
\mathbb E_P(q_i-q_{r,i})^2=D_r(P)-c_\star.
$$

Using $|(x-u)^2-(x-v)^2|\le2|u-v|$ for $x\in\{0,1\}$ and $u,v\in[0,1]$, then Cauchy–Schwarz and (1.3), yields

$$
\left|T_{L,r}-S_P(f)\right|
\le2F\sum_{i=1}^L\mathbb E_P|q_i-q_{r,i}|
\le2LF\sqrt{D_r(P)-c_\star}
\le2LF\sqrt{\frac{c_\star}{r+1}}.
$$

This proves (3.2). Equation (3.3) contradicts it since $c_\star\le\bar c$, and (1.1) then gives strict nonattainment. For an arbitrary stationary pair law, increasing-field $L^2$ conditional projection gives $q_{r,i}\to q_i$. The same loss bound and the finite interior sum give $T_{L,r}\to S_P(f)$. If $|S_P(f)|>0$, eventually $|T_{L,r}|>|S_P(f)|/2$ while the threshold in (3.3) is smaller than $|S_P(f)|/2$. Thus a finite violation exists. $\square$

For $P=P_\theta$, all of (3.1) is determined by actual cylinder probabilities in $[1-r,L+r]$. On a positive-mass radius-$r$ exterior atom with words $u,v$, its posterior is $\lambda M_uM_1M_v\mathbf1/(\lambda M_uAM_v\mathbf1)$. At zero denominator it may be set to zero; forced atoms have zero numerator. Empty words handle $r=0$. Overlap of the block and windows is retained when integrating $f_C$.

[Conditional Response, equations (4.2)–(4.3)][R] allow $Fc+2LF\sqrt{c/(r+1)}$ for general null directions. Theorem 2.1 removes exactly the exterior $Fc$ allowance for this subclass. Finite $T_{L,r}$ is not identified with total $S_P(f)$: their equality is only a limit unless separately proved. Detectability gives neither a rate nor a uniform or efficient radius, and nullity alone gives no productive sign.

## 4. Sufficient conditions owned by the actual producer

**Proposition 4.1 (Actual contexts, proportional matrices and guards).** Fix any $\theta\in\Theta_N$, distinct $a,b\in B_L$ with positive actual masses, and $\alpha,\beta>0$. Put $\Delta=\alpha M_a-\beta M_b$. Then the pair condition (2.1) is equivalent to

$$
\lambda M_u\Delta M_v\mathbf1=0\quad\text{for all finite binary words }u,v,
\tag{4.1}
$$

including empty words and every seam. In particular $\Delta=0$ is sufficient. Equivalently, (4.1) says $r\Delta c=0$ on the actual spaces $\mathcal R=\operatorname{span}\{\lambda M_u\}$ and $\mathcal O=\operatorname{span}\{M_v\mathbf1\}$.

**Proof.** Complete contiguous left and right exterior cylinders have expectation against $f_C$ equal to the left side of (4.1), under the single supplied joint law. Events with missing exterior coordinates are sums of such cylinders, with each unspecified letter replaced by $A$. Empty sides and illegal completions are included; the latter have zero actual probability. Cylinder extension proves (2.1), and testing (2.1) on the complete cylinders proves the converse. Bilinearity gives the span formulation. $\square$

These two spaces are generated already by words of length at most $N-1$. Indeed, the cumulative row spans start at $\operatorname{span}\{\lambda\}$ and satisfy $\mathcal R_{k+1}=\mathcal R_k+\mathcal R_kM_0+\mathcal R_kM_1$. A plateau makes the span invariant and permanent; otherwise dimension increases from one to at most $N$. The column spans obey the analogous recursion. This gives a finite verification condition for a specified producer, without guaranteeing a pair or an efficient way to find it.

One optional sufficient construction is a positive-mass legal guard $y$ with $M_y=vw\ne0$ of rank one, where $v,w\ge0$. For distinct equal-length interiors $u,u'$ whose guarded words are legal, set $s_u=wM_uv$ and $s_{u'}=wM_{u'}v$. If both scalars are positive, then

$$
M_{yuy}=s_u vw,\qquad M_{yu'y}=s_{u'}vw,
\qquad f(yuy)=s_{u'},\quad f(yu'y)=-s_u.
$$

The guarded masses are $s_uP_\theta([y])$ and $s_{u'}P_\theta([y])$, so positivity and balance follow. All other legal words have coefficient zero. Rank one is not required by (4.1), and no rank-one guard is asserted to exist for every finite producer. A multiword matrix dependence supplies neither a two-word pair nor productivity. After producing a pair, a nonzero actual interior total or a strict (3.3) remains a separate obligation.

## 5. A short exact L5 illustration and its cheaper exclusion

Use the free/tail constructor of [Five-state Slice, §2][V], with the following specified base law, for $0\le t\le10^{-6}$:

$$
K=\begin{pmatrix}7/10+9t/40&3/20&3/20-9t/40\\2/3&1/6&1/6\\2/3-t&1/6&1/6+t\end{pmatrix}
=\begin{pmatrix}a&u\\q&G\end{pmatrix},\qquad
\pi=(20/29,9/58,9/58),\quad \eta=10/19.
$$

In state order $(1,2,3,2',3')$, $M_0$ has rows $(a,u,0,0)$, two zero rows, and the last two rows of $K$ padded by two zeros; $M_1$ has just entries $(2,4)=(3,5)=1$. Take $\lambda=(10/19,9/76,9/76,9/76,9/76)$. The base entries are positive, rows sum to one, and detailed balance with $\pi$ holds. With $b=9/29$, direct multiplication gives $\lambda=(\pi,\pi_2,\pi_3)/(1+b)$, $A\mathbf1=\mathbf1$, $M_1^2=0$, $\lambda M_0=(\pi K,0,0)/(1+b)$ and $\lambda M_1=(0,0,0,\pi_2,\pi_3)/(1+b)$. Thus $\theta_t\in\Theta_5$ on the emitted-bit clock; write $P_t=P_{\theta_t}$ and $\mathbb E_t=\mathbb E_{P_t}$. Every legal word has a positive path using state $3$ for a one, $3'$ for its following zero and state $1$ for other zeros, including initial zeros, final ones and all-zero words.

Put $v=(a,0,0,q_2,q_3)^{\mathsf T}$, $w=(a,u_2,u_3,0,0)$ and $z=uq=1/5-3t/10+9t^2/40$. Direct products give $M_{00}=vw$, $wM_0=aw$, $w\mathbf1=1$, $\lambda v=\eta$, and

$$
M_{00000}=a^3vw,\qquad M_{00100}=zvw,
\qquad f(00000)=z,\quad f(00100)=-a^3,\quad f=0\text{ on all other }B_5.
$$

The two masses are $\eta a^3,\eta z$, and $J=\eta a^3z>0$. Proposition 4.1 proves actual full-law conditional nullity. Theorem 2.1 cancels all exterior sites, including $0,6$; the entire response is $JH_t$, where

$$
H_t=\sum_{i=1}^5\bigl(\mathbb E_t[\ell_i\mid00000]-\mathbb E_t[\ell_i\mid00100]\bigr).
\tag{5.1}
$$

At $t=0$, the visible law is exactly [TwoStep, Definition 2.1][T]: after $00$ and $10$ its next-one probabilities are $3/10$ and $1/3$, and after a one it forces zero; its stationary pair row is $(10/19,9/38,9/38)$. Define a local function $g_i=0$ on forced fibers and $g_i=p_{xy}$ on free fibers, where $x=X_{i-2},y=X_{i+2}$ and

$$
(p_{00},p_{01},p_{10},p_{11})=(200/543,100/247,100/247,50/113),
\qquad (R_{00},R_{01},R_{10},R_{11})=(200/343,100/147,100/147,50/63).
$$

At zero, $uG=u/3$, $Gq=q/3$ and $G^2=(50/63)aqu$. Together with $M_{00}=vw$ these imply all four matrix identities $M_{x010y}(0)=R_{xy}M_{x000y}(0)$. Arbitrary farther exterior products preserve them. Finite-window conditioning followed by increasing-field convergence identifies $g_i$ as the actual full posterior at zero, consistently with [TwoStep, Proposition 2.4][T].

For the actual $t$ law, put $s=6t$. Entrywise $(1-s)M_x(0)\le M_x(t)\le(1+s)M_x(0)$ for both letters. Nonnegative multiplication gives the corresponding $n$-factor word bounds. In any radius-$r$ exterior atom with $r\ge2$, keep all farther factors at $t$ and compare only the central five factors. Its actual insertion odds lie between $R_{xy}/U$ and $R_{xy}U$, where $U=((1+s)/(1-s))^5$. For $s\le1/100$, binomial expansion and Bernoulli's inequality give $(1+s)^5\le1+6s$, $(1-s)^5\ge1-5s$, and $U\le1+12s$. Since $R_{xy}<1$ and odds-to-probability is 1-Lipschitz,

$$
|q_{r,i}(P_t)-g_i|\le72t\quad(r\ge2),\qquad |q_i(P_t)-g_i|\le72t\quad P_t\text{-almost surely}.
\tag{5.2}
$$

The latter follows by conditional convergence under $P_t$ itself, with a common conull set for all integer sites. Zero-total atoms are not divided by and forced fibers remain zero. Thus (5.2) uses a globally specified comparison function, not an untransferred almost-sure version from another law.

For the complete reference calculation set $p_0=200/543$, $p_1=100/247$, $p_2=50/113$. Conditional on $00000$, the left exterior pair $(-1,0)$ has masses $(49,30,21)/100$ at $(00,01,10)$; the right pair $(6,7)$ has $(49,21,30)/100$. These follow from the stationary pair products entering and leaving $00$. The same exterior law holds under $00100$. The center difference is $2p_0-1$. Each neighbor difference is $(7/10)p_0^2+(3/10)p_1^2$, because the second word forces its loss to zero. Each endpoint difference is $(49/100)(p_0^2-p_1^2)+(21/100)(p_1^2-p_2^2)$; the remaining exterior case forces zero on both words. Hence all five terms give

$$
H_0=2p_0-1+\frac{119}{50}p_0^2+\frac1{25}p_1^2-\frac{21}{50}p_2^2
<-\frac{134287}{10^7}<-\frac1{100},
\tag{5.3}
$$

using $p_0<369/1000$, $p_1<405/1000$, $p_2>442/1000$. Both endpoint terms are included.

Each comparison loss $(X_i-g_i)^2$, $1\le i\le5$, lies in $[0,1]$ and depends only on the nine coordinates $[-1,7]$. Conditional on either block word, every such nine-word mass ratio between $P_t$ and $P_0$ lies between $(1-s)^9/(1+s)^5$ and $(1+s)^9/(1-s)^5$. The bounds $(1+s)^9\le1+10s$, $(1-s)^9\ge1-9s$ put these ratios in $[1-16s,1+16s]$. Each comparison expectation therefore changes by at most $96t$. Equation (5.2) changes each actual squared loss by at most $144t$. There are ten conditional expectations, giving

$$
|H_t-H_0|\le2400t,\qquad H_t<-19/2500,\qquad S_{P_t}(f)<-19J/2500<0
\quad(0<t\le10^{-6}).
\tag{5.4}
$$

This is the actual total response, with absolute sum at most $5J$, rather than an identification of a finite $T$ with $S$. It consumes Theorem 3.1's finite-detectability conclusion. No numerical program or rate assertion is needed.

**Cheaper radius-two exclusion of the same interval.** Write $W=d(P_0)=D_2(P_0)=\frac1{38}(1372/543+588/247+63/113)$, as proved in [TwoStep, Theorem 3.1][T]. Monotonicity and homogeneity of $h$ applied to the five-word product bounds give

$$
d(P_t)\le D_2(P_t)\le(1+6t)^5W\le(1+36t)W
<\frac{1093}{7600}+\frac9{10^6}<\frac{14383}{100000}.
\tag{5.5}
$$

Here $W\le1/4$ and $W<1093/7600$ follow respectively from coordinate risk and the bounds $1372/543<25268/10000$, $588/247<23806/10000$, $63/113<5576/10000$; their integer cross-product margins are $524,82,88$.

For a strictly stronger actual comparator, take the legal-pair chain $\widehat Q$ on $(00,01,10)$ with transition rows $(7/10,3/10,0)$, $(0,0,1)$, $(33/50,17/50,0)$ and stationary row $(11/21,5/21,5/21)$. Row sums and direct multiplication verify normalization and stationarity; all legal transitions are positive. Its actual full-word center ratio cancels the same three transition factors as in [TwoStep, Proposition 2.4][T], independently of farther coordinates. Thus its full posterior equals its radius-two posterior, not merely a proxy. The four center-zero five-word masses have numerators $(3773,1617,1617,693)$ and center-one masses $(2178,1122,1122,578)$, all over $21000$, from this one pair law. Consequently

$$
d(\widehat Q)=\frac1{21000}\left(\frac{8217594}{5951}+\frac{3628548}{2739}+\frac{400554}{1271}\right)
>\frac{15103}{105000}>\frac{14383}{100000},\qquad d(\widehat Q)\le c_\star.
\tag{5.6}
$$

The three summands exceed $13808/10,13247/10,3151/10$, with positive cross-product differences $4532,1947,619$. Equations (5.5)–(5.6) already exclude the entire stated interval, including zero, without response analysis. This rational instantiation supports the overlap comparison, not an optimality or separate novelty claim. The illustration's response carries additional information but is not necessary for its nonattainment or new whole-domain coverage.

## 6. Attribution, boundaries and the unchanged open quantifier

The contribution is `repo-derived`: Theorem 2.1's full-law posterior restriction and Theorem 3.1's removal of the constant term are a synthesis relative to the inspected suppliers. [Stationary][S] owns the risk identity and projection tools; [Universal][U] owns the entire producer domain and actual-law correspondence; [Conditional Response][R] owns attained-law zero response and its budget. [Five-state Slice][V] supplies the free/tail constructor and rank-one $00$ algebra, and [TwoStep][T] supplies the reference law and finite-order grouping. Their numerical class bounds are not transferred to a different base stationary row.

The conditional Brier score and squared posterior discrepancy are `literature-attested` in [Dawid–Lauritzen–Parry][DLP], *Proper Local Scoring Rules on Discrete Sample Spaces*, arXiv:1104.2224v2, §4.2, especially Example 4.4 and equation (14). Its full-product strict-propriety argument assumes everywhere-positive distributions; that argument is not imported into the no11 domain. [Van Enter–Verbitskiy][EV], *Erasure entropies and Gibbs Measures*, arXiv:1001.3122v1, Definition 4 and Theorems 5–6, gives exterior Shannon uncertainty; Theorem 6 adds a Gibbs hypothesis. Neither these inspected passages nor the cited supplier interfaces supplies universal productive pairs. The ordinary proofs here use conditional-expectation uniqueness and squared-loss projection directly. This bounded comparison makes no worldwide novelty or exhaustive literature claim.

All original zero masses, structural zeros, reducible and periodic laws remain in (1.2). The cancellation theorem has no mixing, finite-memory or rank hypothesis; the guarded construction is only sufficient. Positive pair existence and a nonzero interior response remain distinct gaps beyond the exhibited producer. There is no universal pair existence, hidden-minimality conclusion, efficient-radius guarantee or empirical machine-learning benefit.

**Open Problem 6.1 (Original arbitrary-finite attainment).** With $C_N=\sup_{\theta\in\Theta_N}d(P_\theta)$ and $U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta)$, still decide whether some exact finite $\theta$ attains $c_\star$, or whether $C_N<c_\star$ for every finite $N$. By [Universal, Theorem 6.2][U], the latter is equivalent to

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\kappa_m/(m+1).
$$

A pair-conditional certificate or this proper five-state family does not bound that full compact-domain maximum. To use this route on every hypothetical finite attainer requires an actual positive exterior-equivalent pair with productive interior response, or another proved response mechanism; matrix dimension counting supplies neither. The arbitrary-finite problem remains open.

[S]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[R]: FIB_LEGAL_EDGE_LOAD_CONDITIONAL_NULL_RESPONSE_AND_FINITE_CERTIFICATE.md
[T]: FIB_LEGAL_EDGE_LOAD_TWO_STEP_BULK_SEPARATION.md
[V]: FIB_LEGAL_EDGE_LOAD_REVERSIBLE_FIVE_STATE_SLICE_UNIFORM_SEPARATION.md
[DLP]: https://arxiv.org/html/1104.2224v2
[EV]: https://arxiv.org/html/1001.3122v1

## 追加锚（本行以下为增补区）
