# FIB harmonic-edge load: uniform separation of a reversible five-state slice

## 1. Original objective and actual exterior risk

**Definition 1.1 (Complete open-word problem).** For every integer $n\ge1$, put

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\}.
$$

Let $\Gamma_n$ contain all vertices of $B_n$ and all legal Hamming-one edges.
There is no constraint joining the first and last coordinates. In testing an
insertion, take $w_0=w_{n+1}=0$. On the entire probability simplex define

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\qquad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
$$

All-zero words, legal endpoint ones, every legal seam, and zero-mass vertices
and edges remain in this domain. Write $c_\star=\lim_n\kappa_n/n$.

**Convention 1.2 (Same-law risk and supplied identities).** Let $P$ be one
normalized two-sided stationary probability law on

$$
X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

Write $X_i$ for its coordinate variables, $[w]$ for any translated interval
cylinder, and $P_n$ for its actual length-$n$ marginal. For integers $r\ge1$, set

$$
\begin{aligned}
\mathcal E_0&=\sigma(X_j:j\ne0),\qquad F=\{X_{-1}=X_1=0\},\\
\mathcal F_r&=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r),\\
q_P&=\mathbb E_P[X_0\mid\mathcal E_0],\qquad
D_r(P)=\mathbb E_P[(X_0-\mathbb E_P[X_0\mid\mathcal F_r])^2].
\end{aligned}
$$

[Stationary, §2][S] supplies, without a support or memory assumption,

$$
\begin{aligned}
d(P)&:=\lim_{n\to\infty}\Phi_n(P_n)/n
=\mathbb E_P[(X_0-q_P)^2]=\inf_{r\ge1}D_r(P)\le c_\star,\\
D_r(P)&=\sum_{\substack{u,v\in B_r\\u_r=v_1=0}}
h(P([u0v]),P([u1v])),\qquad
nc_\star\le\kappa_n\le(n+1)c_\star.
\end{aligned}
\tag{1.1}
$$

Neighbor-one fibers force $X_0=0$ and contribute zero. Zero-total fibers
also contribute zero, with no division by their mass. The identity between
the open-word density and the full exterior risk includes the original
endpoint contributions; it also holds along $n=3N$.

**Definition 1.3 (Complete finite producer domain).** For $N\ge1$, retain the
entire domain of [Universal, Definition 4.1][U]:

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
\ M_0,M_1\ge0,\ A=M_0+M_1,\ A\mathbf1=\mathbf1,
\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.2}
$$

Here $M_0,M_1$ are $N\times N$ matrices, $\lambda$ is an $N$-component row,
and all entries are exact real numbers. Structural zeros, stationary zero
masses, reducibility and periodicity are allowed.
For $M_w=M_{w_1}\cdots M_{w_n}$, [Universal, Proposition 4.2][U] constructs
one coherent stationary joint law whose visible cylinders are
$P_\theta([w])=\lambda M_w\mathbf1$.

**Convention 1.4 (Actual comparison witness).** Let $Q$ be the stationary
legal-pair law of [TwoStep, Definition 2.1 and Proposition 2.2][T], with pair
states $(00,01,10)$, transition matrix and stationary row

$$
T=\begin{pmatrix}7/10&3/10&0\\0&0&1\\2/3&1/3&0\end{pmatrix},\qquad
\xi=(10/19,9/38,9/38).
$$

Its actual full-exterior risk is

$$
W=d(Q)=\frac1{38}\left(\frac{1372}{543}
+\frac{588}{247}+\frac{63}{113}\right),\qquad
W>\frac{23}{160}+\frac1{76000},\quad W\le c_\star,\quad
\kappa_n\ge nW\ (n\ge1).
\tag{1.3}
$$

These are [TwoStep, Propositions 2.4 and Theorems 3.1, 4.1][T] together with
(1.1). In particular, the identification $d(Q)=W$ has full-exterior
justification: on a free fiber, changing the center in any exterior window
of radius at least two changes precisely three transition factors. The
ratio is independent of all farther coordinates and has values
$200/343,100/147,100/147,50/63$ in context order $00,01,10,11$.
Conditional projection convergence therefore gives the same posterior in
$\mathcal E_0$. The corresponding lower and upper five-bit masses have
numerators $(343,200),(147,100),(147,100),(63,50)$ over $1900$; their harmonic
sum is $W$. Thus (1.3) compares actual risks under the original objective.

## 2. Reversible base kernels and the output clock

**Definition 2.1 (Specified reversible class).** Fix

$$
\pi=(7/10,3/20,3/20),\qquad R=\{2,3\}.
$$

Let $\mathcal K$ be all entrywise nonnegative $3\times3$ matrices $K$ with
$K\mathbf1=\mathbf1$, $\pi_iK_{ij}=\pi_jK_{ji}$ for every $i,j$, and
$K_{13}=3/20$. No rank, strict entry positivity, irreducibility or
aperiodicity condition is added. Let $J$ be the inclusion of coordinates
$2,3$, $E=JJ^\mathsf T$ and $D=I_3-E$. In state order $(1,2,3,2',3')$ define

$$
M_0(K)=\begin{pmatrix}DK&0_{3\times2}\\J^\mathsf TK&0_{2\times2}\end{pmatrix},\qquad
M_1=\begin{pmatrix}0_{3\times3}&J\\0_{2\times3}&0_{2\times2}\end{pmatrix},
$$

$$
b=\pi(R)=3/10,\qquad
\lambda=\frac{(\pi,\pi J)}{1+b}
=(7/13,3/26,3/26,3/26,3/26),\qquad
\theta_K=(\lambda,M_0(K),M_1).
\tag{2.1}
$$

Write $P_K=P_{\theta_K}$ for the visible output law. A free state $1$ emits
$0$ and advances by $K$; a free state in $R$ emits $1$ into its own tail;
each tail emits $0$ and advances by $K$. Risk is measured per emitted bit,
with stationary row $\lambda$, rather than per base transition with row $\pi$.

**Proposition 2.2 (Complete parameterization and admissibility).** The class
$\mathcal K$ consists exactly of

$$
K(\rho,\tau)=\begin{pmatrix}
1-\rho&\rho-3/20&3/20\\
\frac{14}{3}(\rho-3/20)&1-\frac{14}{3}(\rho-3/20)-\tau&\tau\\
7/10&\tau&3/10-\tau
\end{pmatrix},
\tag{2.2}
$$

where

$$
\frac3{20}\le\rho\le\frac{51}{140},\qquad
0\le\tau\le\min\left\{\frac3{10},\,
1-\frac{14}{3}(\rho-3/20)\right\}.
\tag{2.3}
$$

Every $\theta_K$ belongs to the original $\Theta_5$, and
$P_K([1])=3/13$.

Proof. The first row sum gives $K_{12}=\rho-3/20$ and $K_{11}=1-\rho$.
Detailed balance forces $K_{21}=(14/3)K_{12}$, $K_{31}=7/10$, and
$K_{32}=K_{23}=\tau$. The remaining row sums give (2.2).
Nonnegativity gives precisely (2.3); conversely these inequalities make
every entry nonnegative, every row sum one, and every detailed balance
identity valid. In particular $\pi K=\pi$.

For $A=M_0(K)+M_1$, direct block multiplication gives

$$
A\mathbf1=\mathbf1,\qquad M_1^2=0,\qquad
\lambda M_0(K)=\frac{(\pi K,0)}{1+b},\qquad
\lambda M_1=\frac{(0,\pi J)}{1+b}.
$$

Thus $\lambda A=\lambda$ and $\lambda\mathbf1=1$. The joint-law construction
in [Universal, Proposition 4.2][U] applies, including all legal endpoints
and seams. Its one-bit mass is $\lambda M_1\mathbf1=b/(1+b)=3/13$.

The boundary $\rho=3/20,\tau=0$ is included: states $2,2'$ form a closed
period-two class, each with stationary mass $3/26$, while $1,3,3'$ form
another closed class. No mixing or ergodicity assumption is needed for this
stationary law or for the risk bound below. $\square$

**Definition 2.3 (Complete epsilon curve).** For real $\epsilon$ put
$v=(-3/14,1,0)^\mathsf T$ and

$$
K^\epsilon_{ij}=\pi_j(1+\epsilon v_iv_j)
=\begin{pmatrix}
7/10+9\epsilon/280&3/20-9\epsilon/280&3/20\\
7/10-3\epsilon/20&3(1+\epsilon)/20&3/20\\
7/10&3/20&3/20
\end{pmatrix}_{ij}.
\tag{2.4}
$$

Use exactly the constructor (2.1), denoting its triple by $\theta_\epsilon$
and its law, whenever admissible, by $P_\epsilon$.

**Proposition 2.4 (Feasible curve and endpoint scope).** One has

$$
\theta_\epsilon\in\Theta_5\quad\Longleftrightarrow\quad
-1\le\epsilon\le14/3.
\tag{2.5}
$$

On this complete interval $K^\epsilon\in\mathcal K$, with the exact
correspondence

$$
\rho=3/10-9\epsilon/280\in[3/20,93/280],\qquad \tau=3/20.
\tag{2.6}
$$

Every $P_\epsilon$ is full-support on the legal words and ergodic. At
$\epsilon=-1$ the entry $K_{22}$ is zero; at $\epsilon=14/3$ the entries
$K_{12},K_{21}$ are zero. Both endpoints and $\epsilon=0$ are retained.

Proof. Since $\pi v=0$, row sums and stationarity hold algebraically for all
real $\epsilon$, and detailed balance follows from
$\pi_iK^\epsilon_{ij}=\pi_i\pi_j(1+\epsilon v_iv_j)$.
Nonnegativity of $K_{22}$ requires $\epsilon\ge-1$ and that of $K_{21}$
requires $\epsilon\le14/3$; these inequalities make every other entry
nonnegative. All three rows of $K$ occur in $M_0(K)$, so a negative entry
cannot be concealed by the constructor. This proves (2.5), and substitution
proves (2.6).

For every feasible $\epsilon$, $K_{11}\ge187/280$ and
$K_{13}=K_{23}=K_{32}=K_{33}=3/20$, $K_{31}=7/10$.
Free $3$ reaches tail $3'$, which reaches every free state; free $1$ reaches
free $3$, and free $2$ reaches tail $2'$, which reaches free $3$.
Thus the five-state chain is irreducible, with a positive self-loop at $1$.
Its stationary visible factor is ergodic, using the finite-chain fact in
[Universal, Theorem 5.1][U]. Every legal word has a positive path using free
$3$ for each $1$, tail $3'$ for its following forced $0$, and free $1$ for
all other zeros. The positive initial masses and the displayed transitions
also handle an initial $0$, a final $1$, and all-zero words.

At $\epsilon=0$ all rows of $K$ equal $\pi$, giving the first-order visible
chain with $0\to1$ probability $3/10$ and $1\to0$ probability one. The
feasible negative branch is not discarded by imposing positive
semidefiniteness. Indeed, for a base-state column $f$,
$K^\epsilon f=\mathbf1(\pi f)+\epsilon v\sum_i\pi_iv_if_i$;
$\pi v=0$ and $\sum_i\pi_iv_i^2=51/280$ give the $L^2(\pi)$ eigenvalues
$1,51\epsilon/280,0$. Thus positive semidefiniteness would restrict (2.5)
to $[0,14/3]$. $\square$

## 3. Four actual fibers and one uniform certificate

**Lemma 3.1 (Same-law five-bit masses).** For every $K\in\mathcal K$ set

$$
a=1-\rho,\quad \eta=7/13,\quad m=3/7,\quad
u=(\rho-3/20,3/20),\quad q=\frac{14}{3}u^\mathsf T,\quad C=K_{RR},
$$

$$
z=uq=\frac{14}{3}\rho^2-\frac75\rho+\frac{21}{100}.
\tag{3.1}
$$

For $x,y\in\{0,1\}$, let $s_{xy}=P_K([x000y])$ and
$t_{xy}=P_K([x010y])$. These are the two center completions of the same
radius-two exterior atom. Their exact masses are

| Context $xy$ | $s_{xy}/\eta$ | $t_{xy}/\eta$ |
| --- | --- | --- |
| $00$ | $a^3$ | $z$ |
| $01$ | $a^2\rho$ | $\rho-z$ |
| $10$ | $a^2\rho$ | $\rho-z$ |
| $11$ | $a\rho^2$ | $m-2\rho+z$ |

In particular the table is independent of $\tau$, and
$D_2(P_K)=\sum_{x,y}h(s_{xy},t_{xy})$.

Proof. In the free/tail block order, direct multiplication gives

$$
M_0^2=f w,\qquad
f=(a,0,0,q_2,q_3)^\mathsf T,\qquad
w=(a,u_2,u_3,0,0),\qquad
\lambda f=\eta,\quad w\mathbf1=1,\quad wM_0=aw.
$$

Consequently $P_K([0^j])=\eta a^{j-2}$ for $j\ge2$.
Subtracting the left and right extensions of the actual zero cylinders
gives $s_{00}=P_K([0^5])$,
$s_{01}=s_{10}=P_K([0^4])-P_K([0^5])$, and
$s_{11}=P_K([0^3])-2P_K([0^4])+P_K([0^5])$. This proves the lower column;
the equalities use stationarity, without any assumption of seam independence.

For the upper column put $\omega=\pi_R/\pi_1=(3/14,3/14)$.
Detailed balance gives $\omega_jq_j=u_j$, while $C\mathbf1=\mathbf1-q$.
The same word products give

$$
\begin{aligned}
P_K([1])&=\eta m,\\
P_K([101])&=\eta\omega C\mathbf1=\eta(m-\rho),\\
P_K([10101])&=\eta\omega C^2\mathbf1
=\eta\sum_{j\in R}\omega_j(1-q_j)^2
=\eta(m-2\rho+z).
\end{aligned}
$$

The middle equality on the last line uses detailed balance within $R$.
Legality forces both neighbors of a center $1$ to be zero. Thus
$t_{11}=P_K([10101])$,
$t_{01}=t_{10}=P_K([101])-P_K([10101])$, and
$t_{00}=P_K([1])-2P_K([101])+P_K([10101])$, proving the upper column.
All entries are actual nonnegative cylinder masses, also at the boundary
of (2.3). The remaining exterior atoms force the center to zero, so (1.1)
gives the asserted $D_2$ formula, including zero-total fibers. $\square$

**Theorem 3.2 (Uniform actual-risk separation on the larger class).** For
every $K\in\mathcal K$, including every boundary case of (2.3),

$$
d(P_K)\le D_2(P_K)\le B:=\frac{328609787}{2288000000}
=\frac{23}{160}-\frac{290213}{2288000000}<W\le c_\star.
\tag{3.2}
$$

In particular, uniformly over this class,

$$
W-d(P_K)\ge W-B>
\frac1{76000}+\frac{290213}{2288000000}>0.
\tag{3.3}
$$

Proof. Choose the original-exterior measurable predictor

$$
g=\mathbf1_F\left(\frac7{20}+\frac{X_{-2}+X_2}{25}\right).
$$

Conditional expectation is the least-squares projection, as used in
[Stationary, §2][S] and [Universal, Lemma 1.4][U]. For this same $P_K$,

$$
\mathbb E_{P_K}(X_0-g)^2
=d(P_K)+\mathbb E_{P_K}(q_{P_K}-g)^2,
\qquad d(P_K)\le D_2(P_K)\le\mathbb E_{P_K}(X_0-g)^2.
\tag{3.4}
$$

This holds for stationary reducible or periodic laws as well. No finite
window is used as a lower bound on $d$, and $g$ is not asserted to be the
posterior. On forced fibers both $X_0$ and $g$ are zero.

To compute the remaining loss, write $c=7/20$ and $t=1/25$.
Lemma 3.1 gives the center-zero contribution, divided by $\eta$, as

$$
a^3c^2+2a^2\rho(c+t)^2+a\rho^2(c+2t)^2
=(1-\rho)(c^2+4ct\rho+2t^2\rho+2t^2\rho^2).
$$

The center-one contribution, divided by $\eta$, is

$$
\begin{aligned}
&z(1-c)^2+2(\rho-z)(1-c-t)^2
+(m-2\rho+z)(1-c-2t)^2\\
&\hspace{1em}=m(1-c-2t)^2+[4(1-c)t-6t^2]\rho+2t^2z.
\end{aligned}
$$

Substituting (3.1) therefore yields the exact loss

$$
\mathbb E_{P_K}(X_0-g)^2=\eta H(\rho),\qquad
H(\rho)=\frac{229613}{875000}+\frac{1331}{50000}\rho
-\frac{77}{1875}\rho^2-\frac2{625}\rho^3.
\tag{3.5}
$$

Completing the square gives the exact identity

$$
H(\rho)=\frac{299}{1120}-\frac{290213}{1232000000}
-\frac{77}{1875}\left(\rho-\frac{3993}{12320}\right)^2
-\frac2{625}\rho^3.
\tag{3.6}
$$

For example, the quadratic maximum increment is
$(1331/50000)^2/[4(77/1875)]=5314683/1232000000$, and
$299/1120-229613/875000=15923/3500000$;
$15923\cdot352-5314683=290213$ verifies the constant in (3.6).
Every admissible $\rho$ is positive. Dropping the nonnegative square and
cubic terms in (3.6), and multiplying by $\eta=7/13$, proves the bound $B$.
Finally (1.3) proves $B<W$ and the margin (3.3). The predictor, all masses,
and both projection identities concern the original $P_K$. $\square$

**Corollary 3.3 (Restricted finite separation pair).** With the parameter
domain (2.3) unchanged,

$$
\max_{K\in\mathcal K}D_2(P_K)\le B
<\frac{1200}{1201}\frac{23}{160}
<\frac{1200}{1201}W\le\frac{\kappa_{1200}}{1201}.
\tag{3.7}
$$

Proof. The parameter domain is compact and $D_2$ is continuous by its
finite-cylinder formula, so the maximum exists. The first strict inequality
in (3.7) is equivalent to
$1200\cdot290213-328609787=19645813>0$. The remaining inequalities follow
from (1.3). Thus radius two and length $1200$ supply an original-target
finite upper certificate on this whole restricted producer class.
This maximum is over $\mathcal K$, not over all of $\Theta_5$. $\square$

## 4. Complete epsilon exclusion and its original scope

**Corollary 4.1 (Full feasible epsilon family).** For every exact real
$\epsilon\in[-1,14/3]$, the original triple $\theta_\epsilon$ lies in
$\Theta_5$ and

$$
d(P_\epsilon)\le D_2(P_\epsilon)\le B<W\le c_\star,
\qquad D_2(P_\epsilon)<\kappa_{1200}/1201.
\tag{4.1}
$$

Consequently no member improves the actual witness $W$ or attains
$c_\star$. The larger class in Theorem 3.2 is proper, and includes the
reducible periodic-component example in Proposition 2.2.

Proof. Apply Proposition 2.4 and Theorem 3.2. The two structural-zero
endpoints and the rank degeneration $\epsilon=0$ lie in the stated domain.
The larger class contains $K(3/20,0)$, whereas every kernel on the epsilon
curve has $K_{23}=3/20$; hence it is not merely the same parameter curve.
The conclusion depends only on the visible law, and therefore also holds
for any other admissible representation of that same law, including a
representation padded with zero-stationary-mass states. $\square$

**Proposition 4.2 (A new exclusion beyond the radius-one comparison).** The
original radius-one upper value for this curve is

$$
D_1(P_\epsilon)=\frac3{13}\frac{196+9\epsilon}{316+9\epsilon}.
\tag{4.2}
$$

At the feasible endpoint $\epsilon=14/3$ it exceeds $W$, while (4.1)
excludes the entire curve, including this endpoint. For every nonzero
feasible $\epsilon$, the curve also lies outside the event-independent
renewal class of [Renewal, Definition 5.1][R].

Proof. Summing the two columns of Lemma 3.1 gives
$P_\epsilon([000])=\eta a$ and $P_\epsilon([010])=3/13$.
Their harmonic term is $21a/[13(7a+3)]$, which becomes (4.2) by (2.4).
At the upper endpoint,
$D_1=357/2327>3/20$, since $7140>6981$. Meanwhile
$1372/543<253/100$, $588/247<239/100$, and $63/113<56/100$ give
$W<137/950<3/20$. Thus the uniform radius-two result supplies an exclusion
that this radius-one comparison does not give.

For the renewal comparison, set
$t_2=3/10+3\epsilon/20$ and $t_3=3/10$, the two row sums of $K^\epsilon_{RR}$.
The event cylinders in the proof of Lemma 3.1 give, with $p=3/13$,

$$
P_\epsilon([101])=\frac p2(t_2+t_3),\qquad
P_\epsilon([10101])=\frac p2(t_2^2+t_3^2),\qquad
\Gamma_{10,01}(P_\epsilon)
:=P_\epsilon([10101])P_\epsilon([1])-P_\epsilon([101])^2
=\frac{81\epsilon^2}{270400}.
$$

The last quantity is positive exactly for $\epsilon\ne0$, so the
event-independence hypothesis of that supplied renewal exclusion fails.
These supporting cylinder identities locate the restricted exclusion;
they do not imply optimality or hidden-state minimality. $\square$

**Open Problem 4.3 (Unchanged arbitrary-finite attainment).** For the
complete domains (1.2), put

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
$$

Does some finite $N$ and $\theta\in\Theta_N$ satisfy $d(P_\theta)=c_\star$,
or does every finite $N$ satisfy $C_N<c_\star$? By
[Universal, Theorem 6.2][U], the latter alternative is equivalent to

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\kappa_m/(m+1).
\tag{4.3}
$$

Theorem 3.2 proves a uniform original-risk obstruction only for the fixed
$\pi$, reversible, $K_{13}=3/20$ constructor class (2.1). It does not bound
$U_{5,2}$, exclude arbitrary reversible kernels or arbitrary finite
producers, or give an exact finite attainer. Releasing $\pi$, $K_{13}$ or
the constructor requires another justified mass inequality. Structural
zeros, stationary zero masses, reducibility and periodicity remain in
(4.3). The five states in (2.1) count this presentation, without asserting
minimal producer dimension or any equality with observer resources.

The conditional-null route of [Conditional Response, §§3–5][C] still needs
a productive same-law witness for every hypothetical finite attainer:
existence of a matrix null direction alone does not imply a nonzero total
response or its strict finite certificate. No such general productivity
claim follows from (3.7). The exact function $\epsilon\mapsto d(P_\epsilon)$
and its maximizing parameter are also undetermined here; their evaluation
is unnecessary for the complete exclusion (4.1).

[S]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[T]: FIB_LEGAL_EDGE_LOAD_TWO_STEP_BULK_SEPARATION.md
[R]: FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md
[C]: FIB_LEGAL_EDGE_LOAD_CONDITIONAL_NULL_RESPONSE_AND_FINITE_CERTIFICATE.md

## 追加锚（本行以下为增补区）
