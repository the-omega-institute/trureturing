# FIB harmonic-edge load: intrinsic null kernel, dual residual and presentation obstruction

This source supplies an exact finite interface for actual block-conditional
nullity, an exact dual criterion for the existing finite response certificate,
and a lawful obstruction to bounded searches in a stronger matrix kernel.
It gives ordinary mathematical proofs, without Lean kernel verification.
The arbitrary-finite attaining-law problem remains open.

## 1. Original domain and existing consumers

**Definition 1.1 (Complete legal objective).** For integers $n\ge1$, let

$$
\begin{aligned}
B_n&=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},\\
X&=\{x\in\{0,1\}^{\mathbb Z}:x_jx_{j+1}=0\ (j\in\mathbb Z)\}.
\end{aligned}
$$

$B_0$ contains the empty word. The graph $\Gamma_n$ contains all of $B_n$
and every legal Hamming-one edge, with no first-to-last constraint. Testing
an endpoint insertion uses $w_0=w_{n+1}=0$. On the whole probability simplex,

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\qquad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
$$

[Growth, Theorems 3.2 and 5.2][G] own these maxima and
$c_\star=\lim_n\kappa_n/n$, with
$nc_\star\le\kappa_n\le(n+1)c_\star$. Its elementary ceiling is
$c_\star\le\bar c:=3-2\sqrt2<1/4$. No code-dependent decimal certificate
is used here. Zero masses retain their original vertices and edges.

**Definition 1.2 (One actual finite producer).** For $N\ge1$, use the entire
domain of [Universal, Definition 4.1 and Proposition 4.2][U]:

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
\ M_0,M_1\ge0,\ A=M_0+M_1,\ A\mathbf1=\mathbf1,
\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
$$

$\lambda$ is a row and the matrices are $N\times N$. Write
$M_w=M_{w_1}\cdots M_{w_{|w|}}$, with $M_\varepsilon=I$. The supplier's
coherent two-sided stationary joint law is

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P_\theta([w])=\lambda M_w\mathbf1.
$$

$[w]$ denotes the cylinder at $[1,|w|]$; stationarity permits translation.
All objects below use this same $J_\theta$ and its visible marginal
$P=P_\theta$. Zero stationary masses, structural zeros, reducibility,
periodicity and noncontractive presentations remain allowed. The no11
condition is an actual cylinder condition; it need not imply entrywise
$M_1^2=0$ in an untrimmed presentation. Seams use ordered joint products.

**Convention 1.3 (Actual posteriors and supplied response).** Put

$$
\begin{aligned}
\mathcal E_i&=\sigma(X_j:j\ne i),&q_i&=\mathbb E_P[X_i\mid\mathcal E_i],\\
\mathcal F_{r,i}&=\sigma(X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r}),
&q_{r,i}&=\mathbb E_P[X_i\mid\mathcal F_{r,i}],\\
\ell_i&=(X_i-q_i)^2,&D_r(P)&=\mathbb E_P[(X_0-q_{r,0})^2].
\end{aligned}
$$

At $r=0$ the field is trivial. [Stationary, §2][S] owns
$D_r(P)\downarrow d(P)=\mathbb E_P\ell_0=\lim_n\Phi_n(P_n)/n\le c_\star$.
Every conditional mean is a $[0,1]$ version under its own actual law.
Positive finite fibers use their actual conditional probabilities; null
fibers have arbitrary versions and zero weighted contribution. A retained
neighbor equal to one forces a finite posterior to zero. A radius-zero
posterior is the prior mean and has no such forcing information.

For $C=[1,L]$, $L\ge1$, let $\mathcal H_C=\sigma(X_j:j\notin C)$,
$f_C=f(X_C)$ and $F=\|f\|_\infty$ for $f\in\mathbb R^{B_L}$.
[Conditional Response, Theorem
3.1][R] consumes the actual hypothesis $\mathbb E_P[f_C\mid\mathcal H_C]=0$.
Under same-law attainment it proves absolute convergence and
$S_P(f)=\sum_{i\in\mathbb Z}\mathbb E_P[f_C\ell_i]=0$.
Its §3 matrix bridge supplies the sufficient condition
$K_f:=\sum_{w\in B_L}f(w)M_w=0$; no necessity is supplied by that bridge.
The exact kernel below supplies the theorem's full direction hypothesis.

## 2. Exact intrinsic nullity from a finite exterior collar

**Definition 2.1 (Collar and intrinsic kernel).** For a specified
$\theta\in\Theta_N$ and $L\ge1$, set $n=N-1$ and

$$
\begin{aligned}
\mathcal C_{n,L}&=\sigma(X_{1-n},\ldots,X_0,X_{L+1},\ldots,X_{L+n}),\\
E_{\theta,L}((u,v),w)&=\lambda M_uM_wM_v\mathbf1=P([uwv]),
\quad u,v\in\{0,1\}^n,\ w\in B_L,\\
\mathcal K_L(P)&=\{f\in\mathbb R^{B_L}:\mathbb E_P[f_C\mid\mathcal H_C]=0\}.
\end{aligned}
$$

The collar is empty when $n=0$. Its rows include every binary collar word,
including illegal concatenations, with their actual zero probabilities.

**Theorem 2.2 (Exact collar iff on the entire finite domain).** For every
$N\ge1$, $\theta\in\Theta_N$, $L\ge1$ and $f\in\mathbb R^{B_L}$,

$$
\mathbb E_P[f_C\mid\mathcal H_C]=0
\quad\Longleftrightarrow\quad E_{\theta,L}f=0
\quad\Longleftrightarrow\quad
\mathbb E_P[f_C\mid\mathcal C_{N-1,L}]=0.
\tag{2.1}
$$

Proof. The last equivalence follows from the actual finite collar atoms:
their integrals against $f_C$ are precisely the coordinates of
$E_{\theta,L}f$. Null atoms give the equation zero without division.
Full-exterior nullity implies these equations by integration.

For the converse, use the classical finite linear-realization spaces

$$
\mathscr R_t=\operatorname{span}\{\lambda M_a:|a|\le t\},\qquad
\mathscr O_t=\operatorname{span}\{M_b\mathbf1:|b|\le t\},
$$

where $a,b$ range over all binary words. They satisfy

$$
\mathscr R_{t+1}=\mathscr R_t+\mathscr R_tM_0+\mathscr R_tM_1,\qquad
\mathscr O_{t+1}=\mathscr O_t+M_0\mathscr O_t+M_1\mathscr O_t.
$$

Each starts in nonzero dimension one. A plateau is permanent because the
space is then invariant under both generators. In an $N$-dimensional
ambient space, both sequences therefore stabilize by $t=N-1$.
Write $\mathscr R_\infty$ and $\mathscr O_\infty$ for their final spaces.

Exactly length-$n$ words already span these final spaces. Indeed, for
$|a|,|b|\le n$, stationarity and row normalization give

$$
\lambda M_a=\lambda A^{n-|a|}M_a,\qquad
M_b\mathbf1=M_bA^{n-|b|}\mathbf1.
$$

Expanding the powers of $A=M_0+M_1$ pads rows on the left and columns on
the right into length-$n$ words. Hence $E_{\theta,L}f=0$ implies
$rK_fo=0$ for every $r\in\mathscr R_\infty$ and
$o\in\mathscr O_\infty$. In particular,

$$
\lambda M_aK_fM_b\mathbf1=0
\qquad\text{for every finite binary }a,b.
\tag{2.2}
$$

This scalar is the integral of $f_C$ against the event specifying the
adjacent left word $a$ and right word $b$. Every finite exterior cylinder
is a finite disjoint union of such events after unspecified coordinates
between it and $C$ are filled and summed. Equation (2.2) thus gives zero
integral on the entire finite exterior cylinder algebra. Since $f_C$ is
bounded, uniqueness of finite signed measures, or the bounded monotone
class theorem, extends that identity to $\mathcal H_C$. This is full
conditional nullity. No support, unifilarity or mixing assumption entered.
$\square$

**Corollary 2.3 (Law invariance and existing consumers).** If finite
presentations $\theta$ and $\theta'$ generate the same $P$, then for every
$L\ge1$ their collar kernels and annihilators coincide:

$$
\ker E_{\theta,L}=\ker E_{\theta',L}=\mathcal K_L(P),\qquad
\operatorname{range}(E_{\theta,L}^{\mathsf T})
=\operatorname{range}(E_{\theta',L}^{\mathsf T})=\mathcal K_L(P)^\perp.
\tag{2.3}
$$

Proof. Theorem 2.2 identifies each kernel with the same actual conditional
identity. The finite-dimensional annihilator identity gives the row spaces.
$\square$

The matrices and collar sizes can differ. The equation $K_f=0$ remains
a sufficient, presentation-dependent subspace of this kernel. In contrast,
every $E_{\theta,L}$-null direction is accepted by [Conditional Response,
Theorem 3.1 and §4][R]. In particular its already supplied argument gives,
with $F=\|f\|_\infty$, under hypothetical same-law attainment,

$$
\left|\sum_{i=1}^L\mathbb E_P[f_C(X_i-q_{r,i})^2]\right|
\le Fc_\star+2LF\sqrt{c_\star/(r+1)}.
$$

This is an application of that consumer, with exact nullity supplied by
(2.1). The collar bound tests a specified $f,L$; it gives no posterior
localization, finite visible memory, smallest collar, efficient productive
radius or hidden-state minimality. For example the permitted $N=1$
all-zero law has the empty collar; its kernel simply requires
$f(0^L)=0$. Unsupported words remain coordinates with no actual loss.

## 3. Actual finite loss and its dual residual

**Definition 3.1 (Finite loss vector).** Fix $P=P_\theta$, $L\ge1$ and
integers $R,r\ge0$. Put $I_R=[1-R,L+R]\cap\mathbb Z$ and

$$
\begin{aligned}
v_{L,R,r}(w)&=\sum_{i\in I_R}
\mathbb E_P[\mathbf1_{\{X_C=w\}}(X_i-q_{r,i})^2],\\
U_{R,r}(P,f)&=f\mathbin{\cdot}v_{L,R,r},\\
a_{L,R,r}(P)&=\max_{f\in\mathcal K_L(P),\ \|f\|_\infty\le1}
|f\mathbin{\cdot}v_{L,R,r}|.
\end{aligned}
$$

These are finite quantities from the actual marginal on
$[1-R-r,L+R+r]$. On a positive radius-$r$ exterior atom $u,v$, the finite
posterior is
$\lambda M_uM_1M_v\mathbf1/(\lambda M_uAM_v\mathbf1)$.
Zero denominators contribute zero; empty words handle $r=0$.
Every block/window overlap is retained. This defines no infinite response
of a word indicator.

**Theorem 3.2 (Exact finite dual residual).** For every original
$\theta\in\Theta_N$ and every $L,R,r$ as above,

$$
a_{L,R,r}(P)=
\min_{z\in\operatorname{range}(E_{\theta,L}^{\mathsf T})}
\|v_{L,R,r}-z\|_1.
\tag{3.1}
$$

Proof. Write $K=\mathcal K_L(P)$ and $v=v_{L,R,r}$. For $z\in K^\perp$
and $f\in K$ with $\|f\|_\infty\le1$,
$|f\cdot v|=|f\cdot(v-z)|\le\|v-z\|_1$. This proves one direction.
The functional $f\mapsto f\cdot v$ on $K$, endowed with the inherited
infinity norm, has norm $a_{L,R,r}$. Finite-dimensional Hahn–Banach extends
it to $\mathbb R^{B_L}$ with the same norm. Represent the extension by a
vector $b$; infinity/one norm duality gives $\|b\|_1=a_{L,R,r}$.
Then $v-b\in K^\perp$, giving the reverse inequality and a minimizing
representative. The kernel unit ball is compact, so its maximum is
attained. Use (2.3) to identify the annihilator. These are classical norm
and annihilator tools; the substitution is the actual loss/context pair.
$\square$

**Convention 3.3 (Independent actual tail and existing certificate).** Use
the actual one-sided defects of [Multiword, §2][M]:

$$
\begin{aligned}
p^L_j&=\mathbb E_P[X_0\mid X_{-j},\ldots,X_{-1},X_1,X_2,\ldots],\\
p^R_j&=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_j],\\
e_L(j)&=\mathbb E_P(q_0-p^L_j)^2,\qquad
e_R(j)=\mathbb E_P(q_0-p^R_j)^2,\\
\tau_P(R)&=\sum_{j\ge R}(e_L(j)+e_R(j)).
\end{aligned}
$$

The entire opposite half-line stays in each field, including at $j=0$.
A full forced center does not make a reduced defect zero if its forcing
neighbor has been omitted. Suppose a finite nonnegative allowance
$\tau_P(R)\le\eta_P(R)$ is justified independently of attainment.
[Multiword, Theorem 3.1][M] then consumes actual-null $f$ and certifies
$d(P)<c_\star$ whenever

$$
|U_{R,r}(P,f)|>
F B_{L,R,r}(P),\qquad
B_{L,R,r}(P):=\eta_P(R)+2(L+2R)\sqrt{\bar c/(r+1)}.
\tag{3.2}
$$

The finite identity (3.1) needs no tail hypothesis or unifilarity.

**Corollary 3.4 (Exact existence of the specified strict certificate).**
With the independent allowance in Convention 3.3, a direction
$f\in\mathcal K_L(P)$ with $F>0$ satisfying (3.2) exists if and only if

$$
\operatorname{dist}_1
\bigl(v_{L,R,r},\operatorname{range}(E_{\theta,L}^{\mathsf T})\bigr)
>B_{L,R,r}(P).
\tag{3.3}
$$

Proof. Normalize any witnessing direction by $F$ and apply (3.1).
Conversely a maximizing direction for $a>B_{L,R,r}\ge0$ is nonzero;
normalizing it to infinity norm one gives a strict witness. This is exactly
the existing certificate's threshold, at the specified $L,R,r$. $\square$

Null coordinates have both zero loss and zero context entries, so they
create no residual. A nontrivial kernel can still have residual zero.
Law invariance applies to (3.1) because both $v$ and $K^\perp$ depend on
the same $P$. No separate posterior table or optimization program is used.

## 4. Full-response norm only with summable actual tails

**Proposition 4.1 (Tail-qualified norm limit).** Fix $P=P_\theta$ and
$L\ge1$. Suppose independently that $\tau_P(0)<\infty$ and that finite
allowances $\tau_P(R)\le\eta_P(R)$ satisfy $\eta_P(R)\to0$. For
$f\in\mathcal K_L(P)$, define
$S_P(f)=\sum_{i\in\mathbb Z}\mathbb E_P[f_C\ell_i]$ and put

$$
\gamma_L(P)=\max_{f\in\mathcal K_L(P),\ \|f\|_\infty\le1}|S_P(f)|.
$$

Then this is the norm of a bounded linear functional, and

$$
|a_{L,R,r}(P)-\gamma_L(P)|
\le\eta_P(R)+2(L+2R)\sqrt{D_r(P)-d(P)},\qquad
\gamma_L(P)=\lim_{R\to\infty}\lim_{r\to\infty}a_{L,R,r}(P).
\tag{4.1}
$$

Proof. [Multiword, Lemma 2.1][M] gives, for each actual-null direction,
the exterior projection identity
$\mathbb E_P[f_C\ell_i]=-\mathbb E_P[f_C(q_i-p_i)^2]$ outside $C$,
where $p_i$ conditions on the exterior half-line containing $i$, except
$i$. It bounds the absolute omitted sum outside $I_R$ by $F\tau_P(R)$.
Thus $S_P$ converges absolutely on this kernel, with total absolute sum
at most $F(L+\tau_P(0))$, and is bounded and linear there.

For each retained site, actual projection gives
$\mathbb E_P(q_i-q_{r,i})^2=D_r(P)-d(P)$. Since
$|(x-a)^2-(x-b)^2|\le2|a-b|$ for $x,a,b\in[0,1]$,

$$
|U_{R,r}(P,f)-S_P(f)|
\le F\eta_P(R)+2(L+2R)F\sqrt{D_r(P)-d(P)}.
$$

This holds uniformly on the kernel unit ball. Taking norms proves the
inequality in (4.1). For fixed $R$, the finite sums with $q_{r,i}$ converge
to those with $q_i$, uniformly on that ball by the same estimate. Their
norm limit differs from $\gamma_L$ by at most $\eta_P(R)$. Then let
$R\to\infty$. Compactness of the unit ball gives the stated maximum.
$\square$

Consequently $\gamma_L(P)>0$ is exactly existence of a nonzero full
response at this length. Under these tail hypotheses, [Multiword,
Theorem 3.1][M]'s detectability result supplies some finite strict
certificate. Its converse is not established here: a strict finite
certificate contradicts a hypothetical attainer's projection budget as
well as its zero response. It cannot be identified with $S_P(f)\ne0$.
The full responses of nonnull word indicators are never defined or summed;
only finite vectors and their restrictions to $\mathcal K_L(P)$ are used.

[Predictive Quotient, Theorem 2.3, Proposition 3.2 and Theorem 3.3][QT]
supplies one existing allowance:
for each fixed finite row-unifilar law it bounds both actual
defects by $D\rho^{\lfloor j/\ell\rfloor}$ and supplies
$\eta_P(R)=2D\ell\rho^{\lfloor R/\ell\rfloor}/(1-\rho)$, with law-dependent
$D\ge0$, $\ell\ge1$ and $0\le\rho<1$; the single-class case has zero
defects. When $\rho=0$, use $0^0=1$. Its direct finite-pair proof includes
reducible and periodic presentations. This is a reused allowance, without
a productive sign.
Another independently proved summable actual tail is equally admissible.
General nonunifilar summability, a fixed-$N$ uniform allowance, and an
uncontrolled simultaneous $R,r$ limit are not consequences of (3.1).

## 5. Lawful bounded row-unifilar presentation obstruction

**Theorem 5.1 (History register at each prescribed bound).** For every
finite row-unifilar $\theta\in\Theta_N$ and every prescribed integer
$m\ge1$, there is a row-unifilar $\widehat\theta\in\Theta_{\widehat N}$
with $\widehat N\le N|B_m|$ and $P_{\widehat\theta}=P_\theta$ such that,
for every $1\le\ell\le m$ and every $f\in\mathbb R^{B_\ell}$,

$$
\sum_{w\in B_\ell}f(w)\widehat M_w=0
\quad\Longrightarrow\quad
f(w)=0\ \text{whenever }P_\theta([w])>0.
\tag{5.1}
$$

Every such direction has zero actual finite and full response.

Proof. Row-unifilarity means each row of each $M_x$ has at most one
positive successor. Write its symbol probability as $p_h(x)$ and that
successor as $\delta(h,x)$ only when $p_h(x)>0$. Inside the same stationary
$J_\theta$, set

$$
U_i=X_{[i-m,i-1]},\qquad Y_i=(H_i,U_i),\qquad
\widehat\lambda(h,u)=(\lambda M_u)_h.
$$

Retain precisely pairs of positive stationary mass. Conditional on
$Y_i=(h,u)$, the actual marked transition emits $x$ with probability
$p_h(x)$ and goes to $(\delta(h,x),\operatorname{shift}(u,x))$.
Markov factorization of $J_\theta$ justifies the transition even though
the register records past emissions.

Any positive transition out of a positive-mass pair has positive actual
stationary incoming mass at its target, so the retained set is closed.
An illegal seam from such a pair would give positive actual probability
to adjacent ones, contradicting the original law. All retained rows
therefore sum to one. The displayed masses are normalized and stationary
because $Y$ is a stationary function of the original joint process.
This proves a lawful finite marked presentation; its output cylinders
are unchanged, so its $11$ cylinder remains zero. No irreducibility,
aperiodicity or full visible support is required.

After any emitted word $w$ of length $\ell\le m$, every possible final
register has last $\ell$ coordinates equal to $w$. Different words have
disjoint sets of final columns. In a zero matrix sum, a positive entry
of $\widehat M_w$ can therefore cancel with no other word coefficient.
If $P([w])>0$, the nonnegative cylinder product guarantees such a positive
entry, so its coefficient is zero. Thus $f(X_{[1,\ell]})=0$ almost surely.
Every finite response term and every full-response summand is zero.
$\square$

The quantifiers are $\forall\theta\ \forall m\ \exists\widehat\theta$
obstructing all lengths through that $m$. The presentation and state
count may grow with $m$. This proves neither one fixed presentation
obstructing every length nor a fixed-$N$ budget-preserving obstruction.
It does not rule out longer matrix-null directions, quotient-first or
minimal-realization searches. Adding a visible register to a hidden
state also does not make that state a function of finite visible history.

## 6. Covered reference comparison showing strictness

Use exactly the already covered order-two law $Q$ in [Completeness,
Convention 4.1][C] and [Multiword, §§6–7][M]. Its pair states are
$A=00$, $B=01$, $C=10$, stationary masses
$(10/19,9/38,9/38)$, and marked transitions

$$
A\xrightarrow{0,\,7/10}A,\quad A\xrightarrow{1,\,3/10}B,\quad
B\xrightarrow{0,\,1}C,\quad C\xrightarrow{0,\,2/3}A,\quad
C\xrightarrow{1,\,1/3}B.
$$

The same law has the lawful last-six-bit presentation on all $B_6$,
with mass $Q([u])>0$ at $u$, next-symbol probabilities determined by its
last two bits, and shift/append update. Stationary incoming flow is the
actual seven-word marginal summed over its initial bit. The inherited
Fibonacci count gives $|B_6|=F_8=21$. The proof of Theorem 5.1 applies
directly, so every matrix-null direction of lengths one through six is
zero on actual support in this presentation.

Set $a=7/10$, $h=(3/10)(2/3)=1/5$ and use the single-pair part of
[Multiword, Lemma 7.1][M]:

$$
f(000000)=-ah=-7/50,\qquad f(001000)=a^4=2401/10000,
\qquad f(w)=0\text{ otherwise}.
$$

In the three-state presentation,
$M_{001000}=(h/a^3)M_{000000}$, hence $K_f=0$ and
$f\in\mathcal K_6(Q)$. In the 21-state presentation these two nonzero
transfers end in different register columns, so their matrix sum is
nonzero. Its collar kernel still contains this same $f$ by Theorem 2.2.

The productive sign is inherited at $Q$ only. Its actual radius-two free
posterior values are $A_0=200/543$, $B_0=100/247$, $D_0=50/113$, according
to the sum of the distance-two bits, and its forced posterior is zero.
Their proportional transfers balance the entire exterior distributions,
and the two words share their first and last two bits. Thus every exterior
local loss cancels, including both seams. [Multiword, Lemma 7.1][M]'s
single-pair calculation gives

$$
J=16807/950000>1/60,\qquad
H=2A_0-1+\frac{289}{100}A_0^2-\frac{38}{100}B_0^2
-\frac{51}{100}D_0^2<-1/40,\qquad S_Q(f)=-JH>1/2400.
$$

The actual order-two posterior localization also gives
$\tau_Q(2)=0$. Consequently $U_{2,r}(Q,f)=S_Q(f)$ for $r\ge2$.
At the symbolic finite choice $r=10^{12}$, $F<1$ and $\bar c<1/4$
make $F B_{6,2,r}<1/100000$, so the existing finite certificate detects
this intrinsic direction. No large-window evaluation is involved.

The law, posterior table, sign and nonattainment are already covered.
The added conclusion is strictness of the stronger recorded-presentation
restriction. The existing future-output quotient of [Predictive Quotient,
Proposition 3.2][QT] removes this register:
histories with the same last pair have the same future law, and the
three last pairs have distinct next-one probabilities. It recovers the
three-state presentation and its matrix-null direction. This example
therefore proves no obstruction to a quotient-first search and transfers
no productive sign to an unknown remaining law.

## 7. Mathematical ownership and the remaining productive gap

**Attribution 7.1 (Existing results and classical tools).**

| Supplier or framework | Exact use and boundary |
| --- | --- |
| [Stationary][S], §2; [Universal][U], §§2–6 | Actual harmonic/Brier risk, original producer joint law, all zero fibers, necessary attainer support and posterior band, component reduction and compact fixed-$N$ separation. These retain their source ownership. |
| [Conditional Response][R], Theorem 3.1 and §4 | Actual conditional-null zero response and attained-law projection budget. Theorem 2.2 supplies its semantic hypothesis; its response theorem is reused. |
| [Multiword][M], Lemma 2.1, Theorem 3.1 and §§6–7 | Exterior projection, finite certificate and detectability, and the covered reference law/posterior/sign. Their tail and sign hypotheses remain separate. |
| [Predictive Quotient][QT], Theorem 2.3, Proposition 3.2 and Theorem 3.3 | Fixed-law row-unifilar actual one-sided tail allowance; no uniform rate or productive sign. No general nonunifilar summability is imported. |
| [Nonattainment][N], Theorem 1.5; [Completeness][C], Theorem 1.4; [Renewal][P7], §§4–9 | Existing visible-memory, renewal/reset and effective-three-state results remain distinct from arbitrary finite hidden-state coverage. |
| [Balle, Panangaden and Precup, *A Canonical Form for Weighted Automata and Applications to Approximate Minimization*][BPP], arXiv:1501.06841v3, §§2.2, 3.1 | `literature-attested`: classical finite weighted realization and reachable/observable factorization. Its summable-series SVD, approximation and minimality results are not used: stationary cylinder masses total one at each length. |
| [Boyd and Vandenberghe, *Convex Optimization*][BV], Appendix A.1.6 | `literature-attested`: finite dual norms and infinity/one duality. Hahn–Banach extension and the annihilator identity are classical; no optimization or statistical benefit is asserted. |
| [Dawid, Lauritzen and Parry, *Proper Local Scoring Rules on Discrete Sample Spaces*][DLP], arXiv:1104.2224v2, §§4.2.1–4.2.2, Example 4.4, equation (14) | `literature-attested`: conditional Brier scoring. The everywhere-positive full-product argument is not transferred to hard no11; actual legal-fiber projection identities are reused. |
| [Travers and Crutchfield, *Asymptotic Synchronization for Finite-State Sources*][TC], arXiv:1011.1581v2, Theorem 1 and Proposition 3 | `literature-attested`: strongly connected unifilar, probabilistically distinct synchronization background. [Predictive Quotient, Theorem 3.3][QT] owns the broader reducible/periodic allowance; synchronization gives no productive response. |
| This source, Theorems 2.2, 3.2, Corollaries 2.3, 3.4, Proposition 4.1 and Theorem 5.1 | `repo-derived`: the exact same-law direction/certificate interface and its bounded presentation obstruction. The classical tools and covered reference sign are not separate new discoveries. |

The mathematical contribution is this interface relative to the supplied
results. No worldwide priority or exhaustive absence claim is
made. There are no mathematical programs, experiments, Lean checks or
empirical machine-learning claims supporting these ordinary proofs.

**Open Problem 7.2 (Unchanged arbitrary-finite target).** With the entire
original $\Theta_N$, set
$C_N=\sup_{\theta\in\Theta_N}d(P_\theta)$ and
$U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta)$. Still decide whether some
finite exact producer attains $c_\star$, or whether $C_N<c_\star$ for every
finite $N$. [Universal, Theorem 6.2][U] owns the equivalence of the latter
with

$$
\forall N\ge1\ \exists r,k\ge1:\qquad
U_{N,r}<\kappa_k/(k+1).
$$

The response route still needs some $\gamma_L(P)>0$, or a strict finite
residual exceeding its justified allowance, for each intended remaining
law. Exact nullity, positive kernel dimension, cross-event dependence
and a summable tail do not supply that escape. No whole row-unifilar
exclusion, new attaining-law coverage, fixed-$N$ uniform margin or
original all-$N$ completion follows. A lawful candidate with every
$\gamma_L=0$ would obstruct the full-response route on that law; it would
prove neither attainment nor failure of every finite budget certificate.
The separately scoped protected-branch/cycle posterior-defect package
is not a theorem of this volume, and no implication from balanced cycles
to productive response is proved here.

[G]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[S]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[R]: FIB_LEGAL_EDGE_LOAD_CONDITIONAL_NULL_RESPONSE_AND_FINITE_CERTIFICATE.md
[M]: FIB_LEGAL_EDGE_LOAD_MULTIWORD_RESPONSE_STABILITY_AND_VANISHING_TAIL_CERTIFICATE.md
[QT]: FIB_LEGAL_EDGE_LOAD_PREDICTIVE_QUOTIENT_UNIFILAR_ERASURE_TAIL_AND_STRICT_SCOPE.md
[N]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md
[C]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_COMPLETENESS.md
[P7]: FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md
[BPP]: https://arxiv.org/html/1501.06841v3
[BV]: https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf
[DLP]: https://arxiv.org/html/1104.2224v2
[TC]: https://arxiv.org/html/1011.1581v2

## 追加锚（本行以下为增补区）
