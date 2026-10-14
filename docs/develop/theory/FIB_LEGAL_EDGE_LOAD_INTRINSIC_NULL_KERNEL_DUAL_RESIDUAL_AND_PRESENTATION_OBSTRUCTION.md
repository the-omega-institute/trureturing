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

## 8. Legal interference, information Laplacian and shortest phase-readout depth

The finite objective in Definition 1.1 also measures the sensitivity of a
specified coherent experiment. This chapter gives the complete map: legal
word pairs become two-mode interference blocks; their harmonic weights
become a classical Fisher matrix; the same weights are conductances of a
conditional-resampling chain. A separate pulse construction reads coherences
beyond those blocks and gives an exact depth within its stated menu.

Throughout this chapter, $n\ge1$ is finite and $p=(p_u)_{u\in B_n}$ is one
actual probability vector. Whenever risk, phase sensitivity and resampling
are compared, they use this same $p$. It may be a specified finite marginal
of an actual law, but no stationary extension or attaining producer is
assumed. The coherent controls below are an explicit additional mathematical
menu. Their availability is an assumption of the experiment, not a consequence
of a native replacement rule, a geometric drawing or a classical transition
matrix. All derivations here are ordinary mathematical proofs.

### 8.1. The legal graph, its labels and the geometric distinction

**Definition 8.1 (Words, operation edges and occupancy coordinates).** Use
$B_n$ and $\Gamma_n$ from Definition 1.1. Put
$D_n=|B_n|=F_{n+2}$, where $F_0=0$, $F_1=1$ and
$F_{k+2}=F_{k+1}+F_k$. An operation edge changes exactly one bit while
remaining in $B_n$. Write $E_n=|E(\Gamma_n)|$ and orient each site-$i$ edge
$e=(u,v)$ by $u_i=0$, $v_i=1$. In the three-bit window the labels are

$$
0=000,\qquad 1=100,\qquad 2=010,\qquad 3=001,\qquad 13=101.
\tag{8.1}
$$

These labels denote occupied positions, not integer values of binary words.
The exact correspondence to [Boundary Calculus][BC8] is

$$
(0,1,2,3,13)_{\rm here}\longleftrightarrow
(0,2,3,5,25)_{\rm BC}.
\tag{8.2}
$$

Thus the middle mass $p_2$ here is its $p_3$, and the joint mass $p_{13}$
here is its $p_{25}$. The latter is the scalar called $\kappa$ in that
source's probability fiber. It is distinct from the graph maximum
$\kappa_n$ in Definition 1.1.

The Fibonacci vertex and edge counts are supplied by [Word Recovery,
Theorem 2.1(C), equation (2.4), and §3.1][WR8] and by [Mollard,
Propositions 1.1–1.2][Mol8]. The map is their no-consecutive-ones string
set to $B_n$, their dimension to $n$, and their Fibonacci cube to
$\Gamma_n$, with no periodic first-to-last condition. In this notation,

$$
E_n=\sum_{u\in B_n}\sum_{i=1}^n u_i
=\sum_{i=1}^n F_iF_{n-i+1}
=\frac{nF_{n+1}+2(n+1)F_n}{5}.
\tag{8.3}
$$

The deletion interpretation explains the first equality: every one of a
legal word can be deleted, and every edge has exactly one endpoint with
that extra one. The site-$i$ factorization in Mollard's Remark 1.3 counts
left words ending in zero and right words beginning in zero, yielding the
second equality. These classical counts retain their supplier ownership;
no word-discrimination error bound from Word Recovery is needed here.
Its operational discrimination model has $n=3N$; only its elementary
counting calculation is reused, while Mollard supplies (8.3) for every
$n\ge1$.

**Proposition 8.2 (Distance and the five-edge window).** For all
$u,v\in B_n$, the shortest operation-graph distance is their Hamming distance:

$$
\operatorname{dist}_{\Gamma_n}(u,v)
=|\{i:u_i\ne v_i\}|.
\tag{8.4}
$$

In the window (8.1), the operation edges are exactly
$0\! -\!1$, $0\! -\!2$, $0\! -\!3$, $1\! -\!13$ and $3\! -\!13$.
The graph is connected, with a four-edge bottom cycle and the middle
vertex attached through $0$.

Proof. Every single edge changes one bit, so any path must change each
coordinate where $u$ and $v$ differ. For the reverse inequality identify a
word with its set of occupied positions. Delete $u\setminus v$ in any
order, reaching $u\cap v$. Deletions preserve legality. Then insert
$v\setminus u$ in any order; every intermediate occupied set is a subset
of the legal set $v$. This path changes each differing bit once. This is the standard isometric
Fibonacci-cube property noted in Mollard's introduction; the argument
here gives its explicit legal paths. Listing
the Hamming-one pairs of the five words gives the displayed edge set.
$\square$

Under (8.2), [Boundary Calculus, §3, Definition 3.1 and Mathematical
Citation 3.2][BC8] supplies the convex square pyramid with base vertices
$0,1,13,3$ and apex $2$. It has four base edges and four apex edges, hence
eight geometric edges. In particular the geometric edge $2\! -\!13$
joins $010$ and $101$, whose Hamming distance is three. Its §10,
Definition 10.1 and Theorem 10.2 supplies the separate five-edge flip graph.
This is an exact consumption of its two defined constructions: geometric
incidence supplies no allowed gate, and the pulse menu will follow the
flip relation rather than the eight-edge convex skeleton.

### 8.2. An explicit local coherent-control menu

**Definition 8.3 (Legal Hilbert space and conditional pulses).** Embed
occupancies in $(\mathbb C^2)^{\otimes n}$ and take

$$
\mathcal K_n=\operatorname{span}\{|u\rangle:u\in B_n\},\qquad
N_i=|1\rangle\langle1|_i,\qquad P_i=I-N_i.
\tag{8.5}
$$

Operators on unmentioned sites are identities. Set $P_0=P_{n+1}=I$.
For a generator phase $\beta\in\mathbb R/(2\pi\mathbb Z)$, let

$$
\begin{aligned}
H_i(\beta)&=P_{i-1}
\bigl(e^{i\beta}|1\rangle\langle0|_i
      +e^{-i\beta}|0\rangle\langle1|_i\bigr)P_{i+1},\\
R_i(\beta,t)&=\exp(-itH_i(\beta)).
\end{aligned}
\tag{8.6}
$$

The menu permits each such single-position pulse, sequential compositions,
and a final measurement in the complete word basis of $\mathcal K_n$.
A setting specifies every pulse position, phase, angle and order. Where a
position is chosen randomly, its label is recorded. The final word is
recorded in full. The operator uses the center and at most its two neighbors;
this locality statement does not bound the degree of $\Gamma_n$ by three.

**Lemma 8.4 (Invariant legal space and two-state blocks).** Every pulse
preserves $\mathcal K_n$. For an oriented site-$i$ edge $e=(u,v)$, its block
in the ordered basis $|u\rangle,|v\rangle$ is

$$
H_i(\beta)\big|_e=
\begin{pmatrix}0&e^{-i\beta}\\e^{i\beta}&0\end{pmatrix},\qquad
R_i(\beta,t)\big|_e=
\begin{pmatrix}
\cos t&-i\sin t\,e^{-i\beta}\\
-i\sin t\,e^{i\beta}&\cos t
\end{pmatrix}.
\tag{8.7}
$$

All other legal vertices are fixed by this pulse.

Proof. A legal one at $i$ has zero neighbors, so its deletion is enabled.
Insertion into a zero is enabled precisely when both existing neighbors
are zero; at an endpoint the missing neighbor contributes the identity.
Every enabled flip is therefore another legal word. If a neighbor is one,
the two projectors kill the action and the pulse is the identity. A word
has at most one partner for a flip at this fixed site. The site-$i$ edges
thus form disjoint two-state blocks. Squaring each displayed Hamiltonian
block gives $I$, so its exponential has (8.7). On a blocked vertex the
Hamiltonian is zero. This proves the block description and invariance.
$\square$

For $n=1$, both boundary projectors are identities, $B_1=\{0,1\}$ and
there is one ordinary two-state block. A zero entry of an initial law
does not delete a basis vector from $\mathcal K_n$. Subsequent pulses may
populate that legal mode. No intermediate measurement is part of the
depth protocols below.

### 8.3. Edge quadratures and resolved quantum effects

**Proposition 8.5 (Basis phase, pulse phase and edge reconstruction).**
For the oriented edge $e=(u,v)$, define the measurement-basis phase
$\alpha$ by

$$
|\pm_\alpha;e\rangle
=\frac{|u\rangle\pm e^{-i\alpha}|v\rangle}{\sqrt2}.
\tag{8.8}
$$

At a fixed site these pairs, together with the original blocked vertices,
form a complete orthonormal basis. Its measurement is implemented by a
pulse followed by word measurement with

$$
\beta=-\alpha-\frac\pi2,\qquad t=\frac\pi4:
\quad \text{final bit zero is }+,\quad\text{final bit one is }-.
\tag{8.9}
$$

For any density matrix $\rho$ on $\mathcal K_n$, write
$p_u=\rho_{uu}$ and $c_{uv}=\rho_{uv}$. The resolved probabilities satisfy

$$
q_{\pm,e}^{\alpha}
=\frac{p_u+p_v}{2}\pm\operatorname{Re}(e^{-i\alpha}c_{uv}),
\qquad
c_{uv}=\frac12\bigl[
(q_{+,e}^{0}-q_{-,e}^{0})
+i(q_{+,e}^{\pi/2}-q_{-,e}^{\pi/2})\bigr].
\tag{8.10}
$$

Proof. The pairs are orthonormal on disjoint blocks. From (8.7),

$$
R_i(\beta,\pi/4)^\dagger|u\rangle
=\frac{|u\rangle+i e^{i\beta}|v\rangle}{\sqrt2}
=|+_\alpha;e\rangle,
\qquad
R_i(\beta,\pi/4)^\dagger|v\rangle
=-e^{i\alpha}|-_\alpha;e\rangle.
$$

The last scalar has modulus one and leaves the projector unchanged.
Taking the two projector expectations gives (8.10). At $\alpha=0$ the
difference is $2\operatorname{Re}c_{uv}$; at $\alpha=\pi/2$ it is
$2\operatorname{Im}c_{uv}$. This also checks the orientation and sign.
$\square$

One complete word-basis setting gives every diagonal entry. For each of
the $n$ positions, the two settings $\alpha=0,\pi/2$ give both quadratures
of every edge at that position simultaneously. Hence $2n+1$ settings
recover all diagonal and legal-edge entries as an exact-probability
identifiability statement. This counts settings, not preparations or
samples. Different edges at the same site have different outside words.
Keeping only the mean of the measured bit sums their differences and
cannot recover each $c_{uv}$ separately.

The actual resolved experiment has quantum branches and effects. With
$\Pi_w=|w\rangle\langle w|$ and
$V_{i,\alpha}=R_i(-\alpha-\pi/2,\pi/4)$, put

$$
\begin{aligned}
K_{i,w}^{\alpha}&=\Pi_wV_{i,\alpha},&
\mathcal I_{i,w}^{\alpha}(\rho)
 &=K_{i,w}^{\alpha}\rho(K_{i,w}^{\alpha})^\dagger,\\
E_{i,w}^{\alpha}&=(K_{i,w}^{\alpha})^\dagger K_{i,w}^{\alpha}
 =V_{i,\alpha}^\dagger\Pi_wV_{i,\alpha},&
\Pr(i,w)&=\frac1n\operatorname{Tr}(\rho E_{i,w}^{\alpha})
\end{aligned}
\tag{8.11}
$$

when $i$ is independently uniform. Each branch is completely positive,
its trace is its event probability, and $\sum_wE_{i,w}^{\alpha}=I$.
Thus the sum of branch maps is trace preserving. The pair $(i,w)$ is an
actual output record; retaining it supplies the individual quantities in
(8.10). Discarding that record or replacing it by a single mean is a
change of observation.

Here is the precise classical correspondence to [Output-Resolved
Instrument, §15, Definition 3.1 and Theorem 15.1][OR8]. On a diagonal
input $\rho=\sum_xp_x\Pi_x$, the branch (8.11) reduces to the nonnegative
matrix

$$
M_{i,w}^{\alpha}(x,y)
=\mathbf1_{\{y=w\}}\,|(V_{i,\alpha})_{wx}|^2.
\tag{8.12}
$$

Its state set is $B_n$, action is $(i,\alpha)$, output is $w$, input is the
row $p$, and terminal test for a record probability is the constant one.
Then $pM_{i,w}^{\alpha}\mathbf1$ is exactly that branch probability.
For a sequence with measurements after the actions, products of these
matrices give the supplier's classical record words. Its invariant-space
criterion applies to each resolved $M_{a,o}$ under precisely these
hypotheses. Its §16 counterexample explains why closing only their summed
kernels need not close recorded futures.

For an arbitrary coherent input, (8.12) omits the cross terms
$(V_{i,\alpha})_{wu}\rho_{uv}
\overline{(V_{i,\alpha})_{wv}}$. A nonnegative classical matrix is not a
coherent carrier; the CP branches and effects in (8.11) supply the actual
extension. In a sequence without intermediate measurements the effect
is instead $U^\dagger\Pi_wU$ for the whole unitary product $U$. Inserting
measured branches between its pulses would change that experiment.

The posterior qualification of [Output-Resolved Instrument, §17 and its
editorial boundary Q5][OR8] also has an exact limited use. On a feasible
classical affine family $p_s=p_0+s d$ with a nondegenerate prior $\Pi$,
a resolved event has likelihood $Q(s)=a+s b$, where
$b=dM_\omega g$, and requires
$\mathbb E_\Pi Q(s)>0$. Bayes' formula then gives the supplier's update

$$
\mathbb E[s\mid E]-\mathbb E[s]
=\frac{b\operatorname{Var}_\Pi(s)}{\mathbb E_\Pi Q(s)}.
\tag{8.13}
$$

The map can use the five-word fiber with $s=p_{13}$ and its actual
feasible interval, using (8.2). It never requires that a unit shift of
$s$ be feasible. For coherent phase families the likelihood is instead
$\operatorname{Tr}(\rho_sE)$; it need not be affine in $s$, so (8.13) is
not transferred to them. Null events have no ordinary normalized
posterior, and exact-probability reconstruction does not supply exact
finite-sample knowledge.

### 8.4. Pure phase propagation and a separate purity certificate

**Theorem 8.6 (Exact pure-state ambiguity on positive support).** Suppose

$$
|\psi\rangle=\sum_{u\in B_n}\sqrt{p_u}\,e^{-i\theta_u}|u\rangle,
\qquad \sum_up_u=1,
\qquad S=\{u:p_u>0\}.
\tag{8.14}
$$

Let the induced graph $\Gamma_n[S]$ have $c\ge1$ connected components.
The diagonal and edge observations determine every relative phase within
each component. Modulo a global phase, the remaining ambiguity is exactly
$(S^1)^{c-1}$. In particular, this pure-state family is identifiable up
to global phase exactly when $S$ is connected.

Proof. For an edge whose two endpoints are in $S$,

$$
z_{uv}:=\frac{c_{uv}}{\sqrt{p_up_v}}
=e^{i(\theta_v-\theta_u)},\qquad z_{vu}=\overline{z_{uv}}.
\tag{8.15}
$$

Choose a root in each component. Multiplying the oriented $z$ factors
along a path determines $e^{i(\theta_v-\theta_{\rm root})}$ for every
vertex reached. Products around cycles equal one because the phase
differences telescope, so the path choice is immaterial for the actual
compatible pure data. Conversely, if two phase assignments have the same
edge factors, their difference modulo $2\pi$ is constant across every
edge, hence on each component. Each component constant can be changed
independently without altering any measured edge; cross-component
coherences of the pure state change but are unmeasured by this static
menu. Removing the one common global phase leaves $c-1$ circle parameters.
$\square$

This consumes the polarization and nonzero-vertex propagation mechanism
of [Alexeev, Bandeira, Fickus and Mixon, §2, equations (2.4)–(2.6)][ABFM8].
Their coefficient vector maps to the occupied-mode amplitudes; their
vertex frame vectors map to the coordinate vectors $|u\rangle$; their
oriented graph maps to $\Gamma_n[S]$. Their relative coefficient phase
is the conjugate of (8.15) if written in the order $\overline{\psi_u}\psi_v$;
this convention change reverses each oriented factor and leaves path
propagation equivalent. Their three roots-of-unity intensity combinations
and our two quadrature differences are two polarization readouts of the
same complex cross term. Both require nonzero endpoint amplitudes before
normalization. Their full-spark spanning-component argument and their
expander/noise hypotheses are not supplied by this coordinate graph and
are not used as guarantees here. In particular their work is not an
arbitrary mixed-state low-rank completion theorem for these observations.

**Proposition 8.7 (PSD saturation certifies rank one on connected support).**
Let $\rho$ be any positive semidefinite trace-one matrix, with diagonal
$p$ and positive support $S$. If $S$ is connected and every edge inside
$S$ satisfies

$$
|\rho_{uv}|^2=p_up_v,
\tag{8.16}
$$

then $\rho$ has rank one. This gives a purity certificate distinct from
assuming (8.14).

Proof. Positive semidefiniteness gives a Gram representation of $\rho$ by
vectors $g_u$ with squared norms $p_u$; choose either inner-product
convention consistently. The Cauchy–Schwarz inequality gives
$|\rho_{uv}|^2\le p_up_v$. For two positive norms, equality implies that
the two Gram vectors are proportional. The equalities (8.16), propagated
along connected paths, make all $g_u$ with $u\in S$ proportional. If
$p_u=0$, then $g_u=0$. Equivalently, the two-by-two principal minors give
$|\rho_{uv}|^2\le p_up_v=0$ for every $v$, so every zero-diagonal row and
column vanishes. All nonzero Gram vectors therefore span one line and
the trace-one matrix has rank one. $\square$

For a singleton $S$, the zero-row argument already makes the state its
single basis projector, with no relative phase; (8.16) is vacuous. The
support of a trace-one state is never empty. When the support has several
components, saturation along their internal edges makes each component's
Gram vectors collinear but does not make different components collinear.
Thus it does not certify global purity. An edge with a zero endpoint has
no normalized phase or argument. Experimental saturation with errors
would need an additional quantitative certificate; the exact statement
above alone supplies none. Unknown mixed-state purity cannot be inferred
by silently applying Theorem 8.6.

### 8.5. The mixed-state blind space is physically realized

**Proposition 8.8 (Linear kernel and density-matrix ambiguity).** For the
full edge menu of Proposition 8.5, the real linear observation space on
Hermitian $D_n\times D_n$ matrices has dimension $D_n+2E_n$. Its kernel
has real dimension

$$
D_n^2-D_n-2E_n.
\tag{8.17}
$$

The kernel consists precisely of Hermitian matrices with zero diagonal
and zero entries on every legal edge. Every such matrix is traceless.

Proof. A Hermitian matrix has $D_n$ independent real diagonal entries and
one independent complex entry for each unordered pair of distinct
vertices, giving real dimension $D_n^2$. Formula (8.10) supplies the real
and imaginary coordinates of every edge independently. Conversely all
measured probabilities are linear combinations of these coordinates
and the diagonals, including blocked-vertex outcomes. The diagonal
coordinate forms and the two forms per edge are independent, since they
occupy disjoint matrix entries. Rank-nullity proves (8.17); zero diagonal
implies zero trace. On trace-one matrices the observed affine dimension
is $D_n-1+2E_n$, while the blind tangent dimension is unchanged.
$\square$

The supplier counts (8.3) give the following concrete sizes:

| $n$ | $D_n$ | $E_n$ | Blind real dimension |
| --- | --- | --- | --- |
| $3$ | $5$ | $5$ | $10$ |
| $6$ | $21$ | $38$ | $344$ |
| $9$ | $89$ | $235$ | $7362$ |

These values follow directly from the displayed formulas, rather than
from a sample or an asymptotic inference. They also have a genuine PSD
meaning. If $u,v$ are a nonedge, take
$A=|u\rangle\langle v|+|v\rangle\langle u|$. It is Hermitian,
traceless, belongs to the observation kernel and has operator norm one.
For $0<\delta<1/D_n$,

$$
\rho_\pm=\frac{I}{D_n}\pm\delta A
\tag{8.18}
$$

are distinct strictly positive density matrices with identical diagonal
and edge measurements: their two affected eigenvalues are
$1/D_n\pm\delta$, and the others are $1/D_n$. In the five-word window
one may use the nonedge $010,101$. Thus the mixed ambiguity is not merely
an abstract signed direction outside the physical state set.

At $n=1$, $D_1=2$ and $E_1=1$, so the kernel dimension is zero; the two
quadratures and diagonal are complete qubit tomography. Already at
$n=2$ there is the nonedge $10,01$ and a two-real-dimensional kernel.
Pure connected-support recovery, a rank-one saturation certificate and
arbitrary mixed-state tomography are different tasks. The first two
can hold when the third fails.

### 8.6. A four-corner phase read from parallel edges

**Proposition 8.9 (Positive bottom-face phase).** In the five-word window,
suppose $p_0,p_1,p_3,p_{13}>0$ and the state is pure as in (8.14). Then

$$
\chi=\theta_0-\theta_1-\theta_3+\theta_{13}
=\arg\bigl(c_{1,13}\,\overline{c_{0,3}}\bigr)
\pmod{2\pi}.
\tag{8.19}
$$

Both coherences on the right are oriented flips of the high position,
with its bit changing from zero to one. They are recovered separately
from the same two high-position quadrature settings because their
outside words are retained.

Proof. The two phases from (8.15) are $\theta_{13}-\theta_1$ and
$\theta_3-\theta_0$. Subtracting them gives (8.19); their positive
moduli permit taking the argument. Adding $2\pi$ to any representative
phase does not change the displayed class, and reversing a coherence
orientation conjugates that factor. $\square$

The bottom cycle itself is $0\to1\to13\to3\to0$. Its normalized
product is

$$
z_{0,1}z_{1,13}z_{13,3}z_{3,0}=1.
$$

Thus $\chi$ compares two parallel oriented edges, rather than being a
nonzero Wilson-loop holonomy of these pure-state edge phases. If a
bottom mass is zero, the corresponding coherence is zero and (8.19)
does not define its argument. The middle mass need not be positive for
this bottom-face calculation. No mixed-state interpretation of the
$\theta$ variables is imposed.

### 8.7. Actual erasure risk becomes a local information Laplacian

**Proposition 8.10 (Finite erasure consumes the harmonic objective).**
Draw one word $U\in B_n$ from the actual law $p$, erase its bit at $i$,
and retain all its other bits. With
$\mathcal F_i=\sigma(U_j:j\ne i,\ 1\le j\le n)$, the squared prediction
risk is

$$
R_i(p)=\mathbb E_p\bigl[(U_i-\mathbb E_p[U_i\mid\mathcal F_i])^2\bigr]
=\sum_{e\text{ at }i}h(p_u,p_v),\qquad
\sum_{i=1}^nR_i(p)=\Phi_n(p).
\tag{8.20}
$$

Proof. Fix an outside word. If it has two legal completions $u,v$,
orient them with $u_i=0$, $v_i=1$ and put $T=p_u+p_v$. For $T>0$, their
conditional probabilities are $p_u/T,p_v/T$, and their Bernoulli
variance is $(p_u/T)(p_v/T)$. The event has mass $T$, so its contribution
is $p_up_v/T=h(p_u,p_v)$. A single legal completion has variance zero.
If $T=0$ the conditional version is immaterial and its weighted
contribution is zero. These fibers partition the law, and every graph
edge belongs to exactly one site. This proves both equalities. $\square$

The edge function, objective and finite-fiber identity are the existing
ones of Definition 1.1 and [Stationary, §2, equations (2.1)–(2.3)][S].
The exact substitution is its finite probability vector $\mu=p$, its
site contribution $\Phi_{n,i}=R_i$, and its two completion masses
$(s,t)=(p_u,p_v)$. This application uses all other bits of a finite word.
It does not replace that field by the double-infinite exterior
$\mathcal E_i$ of Convention 1.3. No equality with its stationary loss
$d(P)$, no finite-state attainment and no answer to Open Problem 7.2
follows from (8.20). At $n=1$ the outside record is empty, so
$R_1=p_0p_1$ as required by the single edge and normalization.

**Theorem 8.11 (Local classical Fisher matrix).** Fix known $p$ and the
pure phase family (8.14), locally at the reference where all occupied
modes have the same phase. On each independent preparation choose $i$
uniformly from $1,\ldots,n$, use the basis phase $\alpha=\pi/2$ of
Proposition 8.5, and retain $(i,w)$. In the fixed mode-phase coordinates
$e_u$, define

$$
\begin{aligned}
w_{uv}&=h(p_u,p_v),\\
L_p&=\sum_{\{u,v\}\in E(\Gamma_n)}
w_{uv}(e_u-e_v)(e_u-e_v)^{\mathsf T},\\
J_p&=\frac4nL_p.
\end{aligned}
\tag{8.21}
$$

Then $J_p$ is exactly the local classical Fisher matrix per preparation,
and

$$
J_p[f]:=f^{\mathsf T}J_pf
=\frac4n\sum_{\{u,v\}}h(p_u,p_v)(f_u-f_v)^2,
\qquad
\operatorname{tr}J_p=\frac8n\Phi_n(p).
\tag{8.22}
$$

Proof. Along $\theta_u=t f_u$, an oriented edge has

$$
q_{\pm,e}(t)=\frac T2
\pm\sqrt{p_up_v}\sin(t(f_v-f_u)),\qquad T=p_u+p_v.
$$

At $t=0$, if $T>0$, $q_{\pm,e}=T/2$ and
$q'_{\pm,e}=\pm\sqrt{p_up_v}(f_v-f_u)$. Its two outcomes contribute

$$
\frac{(q'_{+,e})^2}{q_{+,e}}
+\frac{(q'_{-,e})^2}{q_{-,e}}
=4h(p_u,p_v)(f_v-f_u)^2.
$$

When one endpoint has mass zero both derivatives vanish. When both
masses are zero the outcomes have probability identically zero in this
fixed-$p$ family; omit them from the Fisher sum, equivalently assign
zero contribution. Blocked-vertex probabilities are fixed $p_u$ and
have derivative zero. In the joint experiment the site label has
probability $1/n$ independent of $t$, so these block contributions are
averaged with that factor. Applying the calculation to every real
$f$ determines the quadratic form and matrix (8.21). Finally
$\operatorname{tr}(e_u-e_v)(e_u-e_v)^{\mathsf T}=2$ for each edge,
giving the trace formula. $\square$

This is a local experiment at a supplied same-phase reference with
known amplitudes and a fixed measurement phase. It does not calibrate
an arbitrary unknown collection of phases for free. Away from that
reference the probabilities and their denominators must be reevaluated;
(8.21) is not asserted as a global constant Fisher matrix. The quantity
is classical information of this particular resolved measurement, not
quantum Fisher information or an optimization over every possible
measurement. Keeping the site label is what permits the average of the
individual information matrices in this proof.

**Corollary 8.12 (Null directions and the existing trace maximum).**
On the positive support $S$, the kernel of $J_p$ consists exactly of
functions constant on each connected component of $\Gamma_n[S]$.
If coordinates are indexed by all of $B_n$, add arbitrary values at
zero-amplitude vertices. In the same fixed coordinate basis,

$$
\Phi_n(p)=\frac n8\operatorname{tr}J_p,
\qquad
\max_{p\in\mathcal P(B_n)}\operatorname{tr}J_p
=\frac8n\kappa_n.
\tag{8.23}
$$

Proof. Every summand of the quadratic form is nonnegative and has
positive weight precisely when both endpoints lie in $S$. Its sum
vanishes precisely when all such endpoint values agree. Connected paths
then give the component constants, while every edge at a zero-amplitude
coordinate has weight zero. The trace equality is (8.22), and maximizing
it uses exactly the existing objective and domain of Definition 1.1.
For existence, $0\le h(s,t)\le(s+t)/4$ makes $h$ continuous even at
$(0,0)$; its finite sum is continuous on the compact simplex. $\square$

The all-constant direction is the global phase gauge. On $S$ the other
component constants are the local version of the global ambiguity of
Theorem 8.6 for the static diagonal-and-edge menu. Arbitrary phase
coordinates on zero amplitudes have no physical state variation. This
agreement of kernels does not constrain what longer coherent controls
can read. The trace in (8.23) uses the specified Euclidean coordinates
$e_u$; it changes under general reparametrization. Maximizing it is not
maximizing the weakest direction, a spectral gap or information over
all quantum experiments.

### 8.8. The same conductances in relaxation and quantum sensitivity

**Proposition 8.13 (Conditional resampling and its Dirichlet form).**
On the positive support $S$ of the same $p$, define

$$
(\mathscr L_pf)(u)
=\sum_{\substack{v\in S\\\{u,v\}\in E(\Gamma_n)}}
\frac{p_v}{p_u+p_v}\,[f(v)-f(u)].
\tag{8.24}
$$

This is the generator that refreshes each position at unit rate from its
conditional law given all other bits of the finite word. It is reversible
with stationary law $p$ and Dirichlet form

$$
\begin{aligned}
\mathcal E_p(f,f)
&=-\langle f,\mathscr L_pf\rangle_p
=\sum_{\{u,v\}\in E(\Gamma_n)}h(p_u,p_v)(f_u-f_v)^2\\
&=\sum_{i=1}^n
\mathbb E_p\operatorname{Var}_p(f(U)\mid\mathcal F_i),
\qquad
J_p[f]=\frac4n\mathcal E_p(f,f).
\end{aligned}
\tag{8.25}
$$

Zero-amplitude states are excluded from this chain, and zero-weight edges
contribute zero to the sum over all legal vertices.

Proof. At a positive two-completion fiber $u,v$, resampling position $i$
from $u$ changes to $v$ with probability $p_v/(p_u+p_v)$. A one-completion
fiber, including a fiber with only one positive mass, makes no change.
The rates in (8.24) are nonnegative and have zero row sum. Their
stationary flow on each oriented edge is

$$
p_u\frac{p_v}{p_u+p_v}
=p_v\frac{p_u}{p_u+p_v}=h(p_u,p_v),
$$

which proves detailed balance. Pair the two oriented terms in
$-\langle f,\mathscr L_pf\rangle_p$; together they give exactly
$h(p_u,p_v)(f_u-f_v)^2$ per unordered edge. The conditional variance on
that fiber is $p_up_v(f_u-f_v)^2/(p_u+p_v)^2$ and its event mass is
$p_u+p_v$. Summing fibers gives the second form in (8.25). The final
identity is (8.22). $\square$

**Proposition 8.14 (Pure quantum information and the gap ratio).** For
$|\psi_t\rangle=\sum_u\sqrt{p_u}e^{-itf_u}|u\rangle$, the quantum Fisher
information of the scalar parameter $t$ is

$$
\mathcal Q_p[f]=4\operatorname{Var}_p(f),\qquad
J_p[f]\le\mathcal Q_p[f].
\tag{8.26}
$$

If $S$ is connected and $|S|\ge2$, define the resampling spectral gap by

$$
\gamma(p)=\inf_{\operatorname{Var}_p(f)>0}
\frac{\mathcal E_p(f,f)}{\operatorname{Var}_p(f)}.
$$

Then $\gamma(p)>0$ and the exact weakest-direction comparison is

$$
\inf_{\mathcal Q_p[f]>0}\frac{J_p[f]}{\mathcal Q_p[f]}
=\frac{\gamma(p)}n.
\tag{8.27}
$$

Proof. The pure-state derivative formula supplied by [Paris, §4.1,
equations (26)–(27)][Paris8] is

$$
\mathcal Q_p[f]
=4\bigl(\langle\dot\psi_t|\dot\psi_t\rangle
-|\langle\psi_t|\dot\psi_t\rangle|^2\bigr).
\tag{8.28}
$$

Here the supplier's scalar parameter is $t$ and its selfadjoint generator
is $F=\sum_uf_u\Pi_u$, with $|\psi_t\rangle=e^{-itF}|\psi_0\rangle$.
Directly, $|\dot\psi_t\rangle=-iF|\psi_t\rangle$,
$\langle\dot\psi_t|\dot\psi_t\rangle=\sum_up_uf_u^2$ and
$\langle\psi_t|\dot\psi_t\rangle=-i\sum_up_uf_u$. Substitution proves
$\mathcal Q_p[f]=4\operatorname{Var}_p(f)$ and fixes the normalization.
If an SLD is used, the pure-state relation is
$L_t=2\dot\rho_t=2(|\dot\psi_t\rangle\langle\psi_t|
+|\psi_t\rangle\langle\dot\psi_t|)$; indeed differentiation of
$\rho_t^2=\rho_t$ verifies the defining SLD equation. No expanded SLD
with a missing factor is used.

For each $i$, the law of total variance gives
$\mathbb E_p\operatorname{Var}(f\mid\mathcal F_i)
\le\operatorname{Var}_p(f)$. Sum these $n$ inequalities and apply
(8.25) to get $J_p[f]\le4\operatorname{Var}_p(f)$. The ratio in (8.27)
is therefore exactly $\mathcal E_p(f,f)/(n\operatorname{Var}_p(f))$.
To see positivity, subtract the mean and minimize on the set
$\sum_up_uf_u=0$, $\sum_up_uf_u^2=1$. It is a nonempty compact sphere
in a finite-dimensional space when $|S|\ge2$. A zero minimum would,
by (8.25) and connectedness, be a constant function; its mean-zero and
unit-variance requirements exclude this. The positive minimum is
$\gamma(p)$. $\square$

A singleton support has $\mathscr L_p=0$, $J_p=0$ and $\mathcal Q_p=0$
for every $f$. There is no direction with positive variance, so the
gap ratio (8.27) is undefined, rather than a quotient $0/0$. For a
support with at least two components, a function taking different
constants on them has positive variance and zero energy. The global
variational gap is then zero; gaps within individual components answer
separate restricted questions.

The resampling chain, diagonal phase evolution and resolved measurement
are three distinct processes sharing the quadratic form (8.25). The
chain has one unit refresh rate per site, whereas the experiment chooses
one site per preparation. This accounts for the factor $1/n$. Neither
(8.24) nor its gap is a Schmidt kernel, a predictive-memory identity or
a physical dissipative realization. The conditional laws, variances
and coherent amplitudes all come from the same finite $p$; separately
optimized laws cannot be substituted into different sides of (8.27).

### 8.9. Connected identifiability can have arbitrarily weak sensitivity

**Example 8.15 (A positive five-word bottleneck).** Let
$0<\varepsilon<1/2$ and, in (8.1), set

$$
p_0=\varepsilon,\qquad p_2=\frac12,\qquad
p_1=p_3=p_{13}=t_\varepsilon
:=\frac{1/2-\varepsilon}{3}.
\tag{8.29}
$$

These five probabilities sum to one and are strictly positive. Set
$f_2=1$ and $f_u=0$ on the other four modes. Then

$$
\mathcal Q_p[f]=1,\qquad
J_p[f]=\frac{4\varepsilon}{3(1+2\varepsilon)}\longrightarrow0,
\tag{8.30}
$$

while

$$
\Phi_3(p)=
\frac{2\varepsilon t_\varepsilon}{\varepsilon+t_\varepsilon}
+\frac{\varepsilon}{1+2\varepsilon}+t_\varepsilon
\longrightarrow\frac16,
\qquad
\operatorname{tr}J_p\longrightarrow\frac49.
\tag{8.31}
$$

Derivation. The variable $f(U)$ is Bernoulli with mass $1/2$ at one, so
$4\operatorname{Var}_p(f)=1$. Only the edge $0\! -\!2$ changes $f$,
and its conductance is
$h(\varepsilon,1/2)=\varepsilon/(1+2\varepsilon)$. Equation (8.22) with
$n=3$ gives (8.30). The two edges $0\! -\!1$, $0\! -\!3$ contribute
the first term of (8.31), the middle edge contributes the second, and
the edges $1\! -\!13$, $3\! -\!13$ each contribute
$h(t_\varepsilon,t_\varepsilon)=t_\varepsilon/2$. As
$\varepsilon\downarrow0$, $t_\varepsilon\to1/6$, proving the two limits.

Every positive-$\varepsilon$ support is connected and therefore has exact
pure identifiability. Nevertheless the specified direction has vanishing
local classical information, and (8.27) gives
$\gamma(p)/3\le4\varepsilon/[3(1+2\varepsilon)]$.
The middle vertex's only connector is $0$. At $\varepsilon=0$ the
positive support splits into the isolated middle vertex $2$ and the
connected bottom path $1\! -\!13\! -\!3$. Its relative component phase
is then a genuine null direction. This displays both the positive
ill-conditioned limit and its disconnected endpoint; a nonzero limiting
trace does not bound the weakest direction away from zero.

For a scalar locally unbiased estimator of $t$ at the same-phase
reference, using $N$ independent preparations of exactly the experiment
in Theorem 8.11 and treating all other parameters as known, the regular
classical Cramér–Rao bound is

$$
\operatorname{Var}(\widehat t)
\ge\frac{1}{N J_p[f]}
=\frac{3(1+2\varepsilon)}{4N\varepsilon}.
\tag{8.32}
$$

The conditions are differentiable outcome probabilities on their fixed
positive support, differentiation through the finite outcome sum, finite
estimator variance, and local unbiasedness
$\mathbb E_0\widehat t=0$,
$\left.\partial_t\mathbb E_t\widehat t\right|_0=1$.
For completeness the product-experiment score has mean zero and variance
$N J_p[f]$. Differentiating the local-unbiasedness equation gives
$\operatorname{Cov}_0(\widehat t,\text{score})=1$; Cauchy–Schwarz proves
(8.32). This is the scalar regular bound used in [Paris, §2,
equations (1)–(2)][Paris8], with its preparation count mapped to $N$.
It is a bound for this protocol, not for every quantum measurement.
It gives neither finite-sample exact phase knowledge nor a claim that
an unbiased estimator saturating it exists at each finite $N$.

### 8.10. Exact shortest pulse depth for any specified coherence

**Definition 8.16 (Depth in the single-position menu).** A depth-$m$
setting is a product

$$
U=R_{i_m}(\beta_m,t_m)\cdots R_{i_1}(\beta_1,t_1),
\tag{8.33}
$$

with no intermediate measurement and with a final full word measurement.
The rightmost factor acts first. Phases, angles and repeated positions
are arbitrary within this menu. Depth counts sequential pulse calls;
it does not count simultaneous gates, preparations or settings. A
coherence $\rho_{uv}$ enters the probability of outcome $w$ with complex
coefficient $U_{wu}\overline{U_{wv}}$, paired with its conjugate term.
A nonzero coefficient means a suitable real or imaginary variation of
that coherence can change that probability.

**Theorem 8.17 (Exact depth equals Hamming distance).** For any distinct
$u,v\in B_n$, put $d=|\{i:u_i\ne v_i\}|$. The minimum depth, within
Definition 8.16, at which some final outcome probability has a nonzero
coefficient of $\rho_{uv}$ is exactly $d$.

Proof of the lower bound. If fewer than $d$ pulses occur, at least one
differing site $j$ is never pulsed. For $i\ne j$, $H_i(\beta)$ commutes
with $N_j$: a neighbor factor is diagonal at $j$, and otherwise the
operators have disjoint supports. Thus the whole product commutes with
$N_j$. Since $u_j\ne v_j$, their evolved states remain in orthogonal
occupation sectors at $j$. For every complete final word $w$, at least
one of $U_{wu},U_{wv}$ is zero. The cross coefficient therefore vanishes.
The argument allows arbitrary angles, phases and repetitions at the
other sites.

Proof of attainment. Write the occupied sets as $u,v$, put
$D=u\mathbin{\triangle}v$ and $K=u\cap v$, and identify $K$ with its
legal word. Choose any fixed order of the $d$ sites in $D$, pulse each
once at angle $\pi/4$, and measure outcome $K$. Starting from $u$, any
path contributing to $U_{Ku}$ must delete each initial one in
$u\setminus K$ and must leave each initial zero in $D$ unchanged.
A site is never pulsed again, so any other choice at that site prevents
the final word from being $K$. The contributing path is unique.

Along it all changes are deletions, so every intermediate occupied set
is a subset of the legal set $u$. Every deletion is enabled and has
nonzero factor $-i e^{-i\beta_i}/\sqrt2$. A zero that stays zero has
factor $1/\sqrt2$ if enabled and factor one if blocked. Their product
is nonzero. Exactly the same reasoning from $v$ proves $U_{Kv}\ne0$.
Uniqueness excludes cancellation between different paths. Consequently
$U_{Ku}\overline{U_{Kv}}\ne0$ after $d$ pulses, proving attainment and
the theorem. $\square$

This attainment uses only legal modes and does not restrict intermediates
to the support of the input density matrix. In particular, an initially
zero-probability mode can be part of either deletion path. A disconnected
positive support blocks the static phase propagation of Theorem 8.6,
but does not block all control in $\mathcal K_n$. The lower bound is
specific to sequential single-position pulses and final word measurement;
it is not a lower bound for arbitrary gates, ancillas, intermediate
measurements, parallel circuits or general laboratory protocols. A
nonzero, known cross coefficient establishes sensitivity, without a
uniform lower bound on its size or statistical conditioning.

### 8.11. An exact phase cycle isolates a mixed coherence

**Theorem 8.18 (Finite character projection and mixed completeness).**
Fix distinct legal $u,v$, $D=u\triangle v$, $K=u\cap v$ and the same
single-use order of $D$ as in Theorem 8.17. Use angle $\pi/4$ at every
site, independently choose the generator phases

$$
\beta_i\in\{0,2\pi/3,4\pi/3\}\quad(i\in D),
\tag{8.34}
$$

and record the final probability $P_K(\boldsymbol\beta)$. There are
$3^d$ settings, each of depth $d$. Known, nonzero coefficients $a_u,a_v$
determined by that order give, for every density matrix $\rho$,

$$
\rho_{uv}
=\frac{
3^{-d}\displaystyle\sum_{\boldsymbol\beta}
\exp\!\left(i\sum_{i\in D}(u_i-v_i)\beta_i\right)
P_K(\boldsymbol\beta)
}{a_u\overline{a_v}}.
\tag{8.35}
$$

Thus diagonal measurement together with these pair protocols is
informationally complete for arbitrary mixed states on $\mathcal K_n$.

Proof. Sites outside $D$ are never flipped. Any initial word $w$ with a
nonzero transition amplitude to $K$ must therefore agree with $K$
outside $D$. Let $W_K$ be the set of all such legal words. Conversely,
for each $w\in W_K$, the unique path to $K$ deletes its initial ones
in $D$ and keeps its initial zeros there. This path is legal and all
its factors are nonzero, by the same deletion reasoning as above.

Let $m_w=\sum_{i\in D}w_i$, and let $r_w$ count positions whose
conditional flip block is enabled when their pulse is reached on that
path. This includes all $m_w$ deletions and any enabled zeros which
stay zero. Formula (8.7) gives the exact amplitude

$$
U_{Kw}(\boldsymbol\beta)
=a_w\exp\!\left(-i\sum_{i\in D}w_i\beta_i\right),
\qquad a_w=(-i)^{m_w}2^{-r_w/2}\ne0.
\tag{8.36}
$$

The enabled/blocked pattern depends on $w$ and the selected order but
not on the phases. A word outside $W_K$ has zero amplitude. Expanding
the actual Born probability, without discarding any mixed-state entry,
therefore gives

$$
P_K(\boldsymbol\beta)
=\sum_{w,z\in W_K}a_w\overline{a_z}\rho_{wz}
\exp\!\left(-i\sum_{i\in D}(w_i-z_i)\beta_i\right).
\tag{8.37}
$$

Write $\omega=e^{2\pi i/3}$. The exact character average obeys

$$
\frac13\sum_{k=0}^2\omega^{k\ell}
=\begin{cases}1,&\ell\equiv0\pmod3,\\0,&\ell\not\equiv0\pmod3.
\end{cases}
\tag{8.38}
$$

Multiplying (8.37) by the character in (8.35) and averaging independently
at each site leaves only pairs satisfying
$w_i-z_i\equiv u_i-v_i\pmod3$ for every $i\in D$.
Both differences lie in $\{-1,0,1\}$, whose three residues modulo three
are distinct, so the congruence means equality. Every site of $D$ has
$u_i-v_i=1$ or $-1$. It therefore fixes $(w_i,z_i)$ to $(u_i,v_i)$.
Outside $D$, both words must equal $K$, which already equals both $u$
and $v$ there. The unique surviving pair is $(w,z)=(u,v)$.
The numerator of (8.35) is consequently $a_u\overline{a_v}\rho_{uv}$,
and its denominator is nonzero. This proves the formula. Taking one
representative of every unordered distinct pair, and using Hermitian
conjugacy plus the diagonals, recovers the entire density matrix.
$\square$

The phases in (8.34)–(8.37) are generator phases $\beta$, not the
measurement-basis phases $\alpha$ of (8.8). The three-point character
identity is classical finite Fourier orthogonality; it is not a new
phase-retrieval theorem. The application here supplies its exact
single-use legal paths, frequencies and nonzero normalization, so that
other coherences present in an arbitrary mixed state are removed rather
than assumed absent.

The diagonal entries need no off-diagonal division, so they use the
original word measurement instead of a depth-zero version of (8.35).
Zero input populations do not alter the known unitary coefficients
$a_w$; PSD may already force some target coherences to zero. Formula
(8.35) remains an exact matrix identity, including those cases.
Its $3^d$ settings count is per target pair. It gives neither an
efficient total-setting count nor a sample-complexity bound. Small
$|a_u\overline{a_v}|$ amplifies empirical errors, and exact probability
values are mathematical inputs to the inversion, not quantities
obtained from finitely many samples without uncertainty.

### 8.12. A phase hidden from every one- and two-pulse setting

**Example 8.19 (The separated three-bit superposition).** In $\mathcal K_3$,
take the pure state

$$
|\psi_\varphi\rangle
=\frac{|010\rangle+e^{i\varphi}|101\rangle}{\sqrt2}.
\tag{8.39}
$$

Its complete diagonal law is $p_2=p_{13}=1/2$, all other masses zero,
independent of $\varphi$. Every legal-edge coherence is zero because
neither endpoint pair lies in its two-point support. Those two modes
have Hamming distance three. Theorem 8.17 therefore makes every final
probability independent of $\varphi$ for every one- or two-pulse setting
in Definition 8.16, not only for the two quadrature settings at a site.

A concrete depth-three setting is

$$
U_\beta
=R_3(0,\pi/4)R_1(0,\pi/4)R_2(\beta,\pi/2),
\tag{8.40}
$$

where the rightmost pulse acts first. Its two amplitudes at the initially
zero-probability legal mode $000$ are

$$
(U_\beta)_{000,010}=-\frac{i e^{-i\beta}}2,
\qquad
(U_\beta)_{000,101}=-\frac12.
\tag{8.41}
$$

Derivation. On $010$, the first pulse deletes the center with factor
$-i e^{-i\beta}$. To finish at $000$, the next two pulses must keep the
zero at sites one and three, each with factor $1/\sqrt2$.
On $101$, the center pulse is blocked by its occupied neighbors and
acts as the identity. The next pulse deletes site one with factor
$-i/\sqrt2$, and the final pulse deletes site three with the same
factor. Each path is the only path producing this final word.
This proves (8.41), including its signs.

The probability of $000$ is therefore

$$
P_{000}(\beta)
=\frac18\left|-i e^{-i\beta}-e^{i\varphi}\right|^2
=\frac{1+\sin(\varphi+\beta)}4.
\tag{8.42}
$$

The two generator settings $\beta=0$ and $\beta=\pi/2$ give
$\sin\varphi=4P_{000}(0)-1$ and
$\cos\varphi=4P_{000}(\pi/2)-1$. Together they recover $\varphi$ modulo
$2\pi$ from exact probabilities. This example has a specified
one-parameter pure family, so two settings suffice; they are not an
alternative completeness proof for arbitrary mixed states. It illustrates
both the sharp lower bound and the permitted use of an initially empty
legal mode. The phase convention in (8.40) is again $\beta$ of the
Hamiltonian, with no substitution of a basis angle $\alpha$.

### 8.13. Exact supplier correspondence and scope of the result

The contribution of this chapter is the concrete finite-law application
and its specified legal control construction. The following
correspondences identify which hypotheses are supplied and which
conclusions are actually consumed. Classical graph counting,
polarization, Gram equality, Fisher theory, reversible-chain energy,
Cramér–Rao and finite Fourier orthogonality are not reissued as new
discoveries.

| Actual supplier | Parameter and hypothesis map | Consumed conclusion and retained boundary |
| --- | --- | --- |
| Definition 1.1; [Growth, Lemma 3.1 and Theorems 3.2, 5.2][G] | Its entire finite legal simplex is $\mathcal P(B_n)$ here; its masses are $p$ and its edge function is $h$, including $(0,0)$. | The existing $\Phi_n$ and $\kappa_n$ become (8.22)–(8.23). The growth constant and stationary attaining-law question are not inferred from this local information identity. |
| [Stationary, §2, equations (2.1)–(2.3)][S] | Its finite two-completion masses are $(p_u,p_v)$; its $\Phi_{n,i}(p)$ is $R_i(p)$ with all other bits of this finite word retained. | Actual harmonic/Brier fiber risk is consumed in (8.20). Its double-infinite exterior and martingale limits retain their different conditioning fields. |
| [Word Recovery, Theorem 2.1(C), (2.4), §3.1][WR8]; Michel Mollard, *Edges in Fibonacci cubes, Lucas cubes and complements*, arXiv:2102.04086v1, Propositions 1.1–1.2 and Remark 1.3 | Their open-boundary no11 strings, dimension $n$, Fibonacci convention and Hamming-one edges map exactly to $B_n,D_n,\Gamma_n,E_n$. | Only vertex/edge counts are consumed in (8.3) and (8.17). Lucas cyclic seams, graph irregularity and word-discrimination bounds are not transferred. |
| [Boundary Calculus, §3, §10 and §13][BC8] | The five labels map by (8.2); its geometric coordinates are $(u_1,u_3,u_2)$ here. Its explicit coherent-control requirement is supplied here by (8.6) and its output carrier by $\mathcal K_n$. | Its pyramid and operation graph are distinct existing objects. Its §13 warning that ordinary channel names omit cross-branch phases is respected by specifying each Hamiltonian and phase. Its Pauli/tree representation is not identified with occupancy pulses. |
| [Output-Resolved Instrument, §§15–17, editorial Q3, Q5][OR8] | On diagonal input, states $x,y\in B_n$, action $(i,\alpha)$, output $w$, terminal test $1$ and branch matrix are precisely (8.12). Positive event normalization and feasible affine parameters are retained in (8.13). | Resolved branch probabilities and the resolved-versus-averaged distinction are consumed. Coherent inputs require (8.11); nonnegative matrices carry no phase. The affine posterior criterion is not asserted for trigonometric phase likelihoods. |
| Boris Alexeev, Afonso S. Bandeira, Matthew Fickus and Dustin G. Mixon, *Phase Retrieval with Polarization*, arXiv:1210.7752v2, §2, (2.4)–(2.6) | Coordinate amplitudes and coordinate frame vectors give the vertex coefficients; orienting their conjugate cross product reverses (8.15). Only positive endpoint amplitudes allow normalization. | Polarization and path propagation are consumed in (8.10), (8.15). Their full-spark spanning, expander pruning and quantitative stability conditions are not assumed, and no arbitrary mixed-state completion theorem is credited to them. |
| Matteo G. A. Paris, *Quantum Estimation for Quantum Technology*, arXiv:0804.2981v3, §2, (1)–(3), (7)–(8); §4.1, (26)–(27) | Its pure unitary family is $e^{-itF}|\psi_0\rangle$, $F=\sum_uf_u\Pi_u$, and its independent preparation count is $N$. The scalar regular, locally unbiased setting of (8.32) is explicit. | The pure QFI normalization and scalar estimation bound are consumed, with direct derivative and score proofs here. No multiparameter attainability or finite-sample saturation is imported. |
| Samuel L. Braunstein and Carlton M. Caves, *Statistical distance and the geometry of quantum states*, Physical Review Letters 72, 3439–3443, DOI [10.1103/PhysRevLett.72.3439][BCaves8] | Historical quantum statistical-distance/Fisher attribution, also cited in Paris's quantum-measurement comparison. | The formulas used here are Paris's formulas and their direct specialization. This Braunstein–Caves citation supplies historical attribution, without a separate numbered-formula dependency. |
| Classical PSD Gram representation, reversible finite Markov chains and finite character orthogonality | Finite Hermitian $\rho\ge0$ gives Gram vectors; the same positive $p$ gives detailed balance $p_ur_{uv}=h(p_u,p_v)$; binary differences lie in $\{-1,0,1\}$ for the three-point characters. | The explicit proofs (8.16), (8.25), (8.38) apply these tools. Their generic mechanisms retain classical ownership; the occupancy maps and legal-path coefficients are the concrete application. |

The results give exact identifiability within the supplied menu and local
information at its specified reference. They do not certify a native
command, physical apparatus, coherence reference, laboratory error rate
or hardware implementation. Settings, independent preparations and
sequential pulse depth remain different resources. The static menu
recovers arbitrary pure connected-support phases but has the mixed blind
space (8.17); the longer phase-cycle menu is mixed-state complete, with
no efficiency or uniform stability claim. All zero fibers, zero-amplitude
coordinates, singleton supports and the $n=1$ experiment remain within
the stated cases. The finite-risk identity and its information
interpretation leave Open Problem 7.2 unchanged.

[BC8]: AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md
[OR8]: AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md
[WR8]: FIB_ATOM_WHITEBOX_CORRELATED_WORD_RECOVERY.md
[Mol8]: https://arxiv.org/abs/2102.04086v1
[ABFM8]: https://arxiv.org/abs/1210.7752v2
[Paris8]: https://arxiv.org/abs/0804.2981v3
[BCaves8]: https://doi.org/10.1103/PhysRevLett.72.3439

## 追加锚（本行以下为增补区）

## 9. Target resistance, optimal four-corner ports and conjugate information cost

The resolved experiment of Chapter 8 allows a target-specific question:
which phase contrast can be estimated, and how should the sampling budget
be assigned to its legal ports? The answer depends on the contrast as well
as on the graph. The four-corner contrast has an optimal one-endpoint
readout, while another contrast on the same five modes requires all three
ports. A fixed-reference probability–phase family then makes the cost of
estimating two conjugate coordinates explicit, including an exact
finite-sample design.

All results in this chapter are ordinary mathematical applications in the
specified finite experiment. The probability law, coherent reference,
measurement menu and independent preparations are supplied assumptions.
The scalar called $\kappa$ below is a joint probability, not the graph
maximum $\kappa_n$ of Definition 1.1.

### 9.1. The calibrated law and the recorded port experiment

**Definition 9.1 (Positive law, phases and budget).** Fix finite $n\ge1$,
the full no11 word set $B_n$ of Definition 1.1, and one known law
$p_u>0$ with $\sum_{u\in B_n}p_u=1$. Use the legal Hilbert space of
Definition 8.3 and the negative-phase convention

$$
|\psi_\theta\rangle=\sum_{u\in B_n}\sqrt{p_u}\,e^{-i\theta_u}|u\rangle.
\tag{9.1}
$$

A same-phase reference is supplied. Choose its common phase to be zero,
so $\theta^0=0$; all phase coordinates below are real local lifts near
this reference. This choice removes no relative phase nuisance direction.
Fix $\eta_i\ge0$ with $\sum_{i=1}^n\eta_i=1$. On each of $N\ge1$
independent preparations, choose a site independently with probability
$\eta_i$ and record that choice.

At site $i$ use the resolved quadrature instrument of Chapter 8. Its
two-mode blocks are precisely the legal pairs $e=(u,v)$ with
$u_i=0,v_i=1$ and all other bits equal. Their basis is

$$
|\pm_{\pi/2};e\rangle
=\frac{|u\rangle\pm e^{-i\pi/2}|v\rangle}{\sqrt2}.
\tag{9.2}
$$

A word which cannot be paired at this site is a blocked singleton and
has its own recorded outcome. Thus the record is either $(i,e,+)$,
$(i,e,-)$ or $(i,w,\mathrm{blocked})$. No sign, edge, selected site or
blocked word is discarded.

For the pulse notation of Definition 8.3, the same basis is obtained
with $R_i(\beta_{\rm pulse},t)=\exp(-itH_i(\beta_{\rm pulse}))$,
$\beta_{\rm pulse}=-\alpha-\pi/2=-\pi$ modulo $2\pi$, and $t=\pi/4$.
Here

$$
H_i(\beta_{\rm pulse})
=P_{i-1}\bigl(e^{i\beta_{\rm pulse}}|1\rangle\langle0|
+e^{-i\beta_{\rm pulse}}|0\rangle\langle1|\bigr)_iP_{i+1},
\quad P_0=P_{n+1}=I.
\tag{9.3}
$$

The final bit zero records $+$ and bit one records $-$ on its pair,
as in Chapter 8. The bit order, generator phase and negative state
phase therefore refer to one instrument. This additional coherent
menu is not supplied by the classical no11 grammar alone.

**Proposition 9.2 (Joint likelihood and weighted information).** Put
$T_e=p_u+p_v$ and $\Delta_e=\theta_v-\theta_u$. The actual one-sample
joint probabilities are

$$
\begin{aligned}
q_\theta(i,e,\pm)
 &=\eta_i\left(\frac{T_e}{2}
       \pm\sqrt{p_up_v}\sin\Delta_e\right),\\
q_\theta(i,w,\mathrm{blocked})&=\eta_i p_w.
\end{aligned}
\tag{9.4}
$$

At the supplied reference the score vector $s=\nabla_\theta\log q_\theta|_0$
has values

$$
s(i,e,\pm)=\pm\frac{2\sqrt{p_up_v}}{T_e}(e_v-e_u),
\qquad s(i,w,\mathrm{blocked})=0.
\tag{9.5}
$$

Define the positive-edge set $E_\eta$ by $\eta_i>0$ at the edge's site,
and put

$$
g_e=\eta_i\frac{p_up_v}{p_u+p_v},\qquad
L_\eta=\sum_{e\in E_\eta}g_e(e_u-e_v)(e_u-e_v)^{\mathsf T}.
\tag{9.6}
$$

Then the one-sample Fisher matrix is

$$
\mathbb E_0s=0,\qquad
J_\eta=\mathbb E_0ss^{\mathsf T}=4L_\eta.
\tag{9.7}
$$

Proof. The density entry is
$\rho_{uv}=\sqrt{p_up_v}e^{i(\theta_v-\theta_u)}$.
The resolved probability from Chapter 8 is
$T_e/2\pm\operatorname{Re}(e^{-i\alpha}\rho_{uv})$; at
$\alpha=\pi/2$ its second term is the displayed sine. Multiplying by
the actual setting probability gives (9.4). For any site the disjoint
pairs and blocked words partition $B_n$, so their probabilities sum
to $\eta_i$, and summing sites gives one.

For $\eta_i>0$, every retained outcome is strictly positive at the
reference. Differentiating (9.4) and dividing by $\eta_iT_e/2$ gives
(9.5). Opposite signs cancel in the score mean. For each pair their
two second moments add to

$$
\eta_i T_e\frac{4p_up_v}{T_e^2}
(e_v-e_u)(e_v-e_u)^{\mathsf T}
=4g_e(e_u-e_v)(e_u-e_v)^{\mathsf T}.
$$

Blocked scores contribute zero. A site with $\eta_i=0$ is omitted
from the sample alphabet; no logarithm or division is taken on its
zero-budget events. This proves (9.7). $\square$

For uniform $\eta_i=1/n$, $L_\eta=L_p/n$, where $L_p$ is the
unweighted-site Laplacian of Chapter 8. Thus (9.7) is exactly its
$J=4L_p/n$, with no change of sample unit. The identity holds at the
calibrated same-phase reference. Away from it, (9.4) remains the
likelihood but its Fisher matrix need not equal $4L_\eta$.

### 9.2. Which targets are estimable, and the exact reference estimator

**Definition 9.3 (Full phase-gradient local unbiasedness).** Fix
$\ell\in\mathbb R^{B_n}$ with $\sum_u\ell_u=0$ and define the
local phase contrast $\tau_\ell(\theta)=\ell^{\mathsf T}\theta$.
An estimator is locally unbiased at the supplied reference if

$$
\mathbb E_0\widehat\tau=\tau_\ell(0),\qquad
\left.\frac{\partial}{\partial\theta_u}
\mathbb E_\theta\widehat\tau\right|_0=\ell_u
\quad\text{for every }u\in B_n.
\tag{9.8}
$$

The statistic and its reference coefficients are held fixed in taking
these derivatives. This is the full gradient condition, including every
phase nuisance direction, rather than unbiasedness along one chosen
curve. The common phase is harmless precisely because $\sum\ell=0$.
Here $p$ is fixed and calibrated; unknown probability parameters would
require a separately specified statistical model.

Let $\mathcal C_\eta$ be the connected components of the graph with
all vertices $B_n$ and only edges $E_\eta$, including isolated vertices.
Define the extended target resistance by

$$
R_\eta(\ell)=
\begin{cases}
\ell^{\mathsf T}L_\eta^+\ell,
 &\displaystyle\sum_{u\in C}\ell_u=0
       \text{ for every }C\in\mathcal C_\eta,\\
+\infty,&\text{otherwise}.
\end{cases}
\tag{9.9}
$$

The superscript $+$ denotes the Moore–Penrose pseudoinverse. Its
quadratic form is used as a resistance only on the stated feasible
domain.

**Theorem 9.4 (Estimability and finite-$N$ saturation).** A finite-variance
estimator satisfying (9.8) exists if and only if $\ell$ is balanced on
every component in (9.9). In that case every such estimator satisfies

$$
\operatorname{Var}_0\widehat\tau
\ge\frac{R_\eta(\ell)}{4N}.
\tag{9.10}
$$

Writing $Y_1,\ldots,Y_N$ for the complete independent records, equality
is attained by the fixed-reference statistic

$$
\widehat\tau_\ell
=\tau_\ell(0)+\frac1N\sum_{r=1}^N
\ell^{\mathsf T}J_\eta^+s(Y_r).
\tag{9.11}
$$

Proof. For real $x$,

$$
x^{\mathsf T}L_\eta x
=\sum_{e=(u,v)\in E_\eta}g_e(x_u-x_v)^2.
\tag{9.12}
$$

All retained conductances are positive. Thus $\ker L_\eta$ consists
exactly of functions constant on each positive-edge component.
Symmetry gives
$\operatorname{im}L_\eta=(\ker L_\eta)^\perp$, which is precisely
the component-balance condition. The same statements hold for
$J_\eta=4L_\eta$.

To see necessity directly in the experiment, shift $\theta$ by
$t1_C$ on a component. Every observed edge difference and every
blocked probability in (9.4) is unchanged. The derivative of any
estimator's expectation in this direction is zero, whereas (9.8)
requires $\sum_C\ell$. Hence an unbalanced target is not locally
estimable. The obstruction is an actual likelihood invariance,
not merely an inability to invert a matrix.

For a balanced target let $v=J_\eta^+\ell$ and
$S_N=\sum_rs(Y_r)$. Finite support and positivity at the reference
justify differentiating expectations. The score identity gives

$$
\mathbb E_0S_N=0,\quad
\mathbb E_0S_NS_N^{\mathsf T}=NJ_\eta,\quad
\mathbb E_0[(\widehat\tau-\tau_\ell(0))S_N]=\ell.
\tag{9.13}
$$

For nonzero $\ell$, set $A=\ell^{\mathsf T}J_\eta^+\ell>0$.
Pairing the last identity with $v$ and applying Cauchy–Schwarz gives

$$
A^2\le\operatorname{Var}_0\widehat\tau\,
      N v^{\mathsf T}J_\eta v
=N A\,\operatorname{Var}_0\widehat\tau.
$$

Since $J_\eta^+=L_\eta^+/4$, this is (9.10).
For (9.11), the mean is $\tau_\ell(0)$ and its expectation gradient is

$$
J_\eta J_\eta^+\ell=\ell.
\tag{9.14}
$$

This computation differentiates the sampling law, not the fixed
reference score. Independence gives variance $A/N$, proving equality.
If $\ell=0$, the target is identically zero and the constant estimator
has variance zero; the division by $A$ is unnecessary. $\square$

For an unbalanced target the algebraic number
$\ell^{\mathsf T}L_\eta^+\ell$ is still finite, but it is not the
variance coefficient of an unbiased target estimator. Equation (9.9)
assigns infinite extended resistance to this case. The estimator
(9.11) uses the supplied $p$, measurement reference and reference
score. It asserts exact local finite-sample saturation, not global
unbiasedness or calibration-free estimation.

### 9.3. Target flow in the same legal network

**Proposition 9.5 (Flow form of the phase-target coefficient).** Orient
each positive edge $e=(u,v)$ arbitrarily, with incidence column
$b_e=e_u-e_v$, so a positive flow has divergence $+j_e$ at its tail
and $-j_e$ at its head. Let $B$ collect these columns and
$G=\operatorname{diag}(g_e)$. For component-balanced $\ell$,

$$
L_\eta=BGB^{\mathsf T},\qquad
R_\eta(\ell)
=\min_{Bj=\ell}\sum_{e\in E_\eta}\frac{j_e^2}{g_e}.
\tag{9.15}
$$

An optimizer is

$$
x=L_\eta^+\ell,\qquad j^*=GB^{\mathsf T}x.
\tag{9.16}
$$

Proof. The incidence product is (9.6), and
$Bj^*=L_\eta L_\eta^+\ell=\ell$. Its energy is

$$
(j^*)^{\mathsf T}G^{-1}j^*
=x^{\mathsf T}L_\eta x
=x^{\mathsf T}\ell
=\ell^{\mathsf T}L_\eta^+\ell.
$$

Every other feasible flow is $j^*+z$ with $Bz=0$. The cross term is

$$
(j^*)^{\mathsf T}G^{-1}z=x^{\mathsf T}Bz=0,
$$

so its energy is that of $j^*$ plus
$z^{\mathsf T}G^{-1}z\ge0$. This proves the minimum and its unique
flow, including disconnected graphs when the sources are balanced
component by component. If a component is unbalanced, summing $Bj$
over that component always gives zero, so no flow is feasible and
the empty infimum is $+\infty$, in accord with (9.9). $\square$

For $\ell=e_u-e_v$ with $u\ne v$ in the same component, (9.15) is
the ordinary effective resistance between those vertices. Different
components give infinite resistance, while $u=v$ gives zero.
This is the classical electrical flow principle applied to the
statistical conductances (9.6). The flows and potentials are
mathematical variables; they do not certify physical currents or
a circuit implementation of the coherent experiment.

### 9.4. Grounding, Kron reduction and which source may be eliminated

**Proposition 9.6 (Retained-target reduction of the information network).**
Consider a connected positive-edge network from (9.6), or one of its
connected components. Partition its vertices into a nonempty retained
boundary $\mathcal B$ and an interior $\mathcal I$. If
$\mathcal I\ne\varnothing$, then $L_{\mathcal I\mathcal I}$ is
positive definite, and define

$$
L_{\rm red}
=L_{\mathcal B\mathcal B}
 -L_{\mathcal B\mathcal I}L_{\mathcal I\mathcal I}^{-1}
                         L_{\mathcal I\mathcal B}.
\tag{9.17}
$$

For each boundary potential $x$,

$$
x^{\mathsf T}L_{\rm red}x
=\min_y
\begin{pmatrix}x\\y\end{pmatrix}^{\mathsf T}
L\begin{pmatrix}x\\y\end{pmatrix},
\qquad
y_*=-L_{\mathcal I\mathcal I}^{-1}L_{\mathcal I\mathcal B}x.
\tag{9.18}
$$

For a retained target $\ell=(\ell_{\mathcal B},0)$ with
$\sum_{\mathcal B}\ell_{\mathcal B}=0$,

$$
\ell_{\mathcal B}^{\mathsf T}L_{\rm red}^+\ell_{\mathcal B}
=\ell^{\mathsf T}L^+\ell.
\tag{9.19}
$$

Proof. Extend any interior vector $y$ by zero on the boundary.
Its full network energy is $y^{\mathsf T}L_{\mathcal I\mathcal I}y$.
If this is zero, every positive edge has equal endpoint values.
Connectivity of the full graph makes the extension constant, and
the nonempty zero boundary makes it zero. Thus nonzero $y$ has
strictly positive energy. This argument does not assume that the
induced interior graph is connected.

Completion of the square gives

$$
\begin{aligned}
\begin{pmatrix}x\\y\end{pmatrix}^{\mathsf T}
L\begin{pmatrix}x\\y\end{pmatrix}
&=x^{\mathsf T}L_{\rm red}x\\
&\quad+(y+L_{\mathcal I\mathcal I}^{-1}L_{\mathcal I\mathcal B}x)^{\mathsf T}
L_{\mathcal I\mathcal I}
(y+L_{\mathcal I\mathcal I}^{-1}L_{\mathcal I\mathcal B}x),
\end{aligned}
\tag{9.20}
$$

which proves (9.18). In particular $L_{\rm red}$ is positive
semidefinite. Its kernel consists of constant boundary values:
zero minimized energy forces a constant extension on the connected
full graph, and a constant boundary has the constant extension.
Thus its range is the zero-sum boundary subspace.

For completeness this Schur matrix is again a loopless Laplacian.
The grounded inverse has nonnegative entries. Indeed, if
$L_{\mathcal I\mathcal I}y=f\ge0$ had a negative minimum in the
zero-boundary extension, then at an interior minimizing vertex all
terms $g(y_i-y_j)$ are nonpositive. Their sum can be nonnegative
only if every neighbor shares the minimum. Repeating along a path
to the boundary contradicts its value zero. Hence $y\ge0$.
The off-diagonal entries of
$L_{\mathcal B\mathcal I}L_{\mathcal I\mathcal I}^{-1}
 L_{\mathcal I\mathcal B}$ are nonnegative, so those of
$L_{\rm red}$ are nonpositive. The full row-sum equations also give
$L_{\rm red}1=0$. This identifies its effective nonnegative
conductances without any interior-connectivity premise.

Now put $x=L_{\rm red}^+\ell_{\mathcal B}$ and extend it by
$y_*$. The block equations give

$$
L\begin{pmatrix}x\\y_*\end{pmatrix}
=\begin{pmatrix}\ell_{\mathcal B}\\0\end{pmatrix}.
$$

Any two solutions of this equation differ by a constant. Since
$\ell$ sums to zero, pairing with $\ell$ removes that constant:
the full energy coefficient is
$\ell^{\mathsf T}L^+\ell
=\ell_{\mathcal B}^{\mathsf T}x$.
This is (9.19). $\square$

If the interior is empty, set $L_{\rm red}=L$ and do no elimination.
A singleton boundary has reduced matrix $[0]$ and admits only the
zero balanced retained target, so (9.19) gives zero. An empty
boundary is excluded from grounding: the full Laplacian is singular,
and there is no retained nonzero target; no inverse of that full
matrix is asserted. In a disconnected network the same construction
may be used on individual components with a nonempty retained
boundary, and estimability still requires balance on each component.

These are the Dirichlet-energy and source-free forms of Kron
reduction. Dörfler–Bullo [Kron9], equation (2.1), Lemma 2.1 and
Theorem 3.9, equation (3.14), supply the classical Schur and
resistance framework; the target map here is $Q=L$, retained
vertices $\alpha=\mathcal B$, and injected vector $\ell$.
The proof above includes the singleton boundary separately from
their at-least-two-retained-vertices setting.

As a concrete application, if vertex $0$ is connected to $1,2,3$
with conductances $a,b,c\ge0$ and $S=a+b+c>0$, eliminating its
potential contributes

$$
g^{\rm added}_{12}=\frac{ab}{S},\qquad
g^{\rm added}_{13}=\frac{ac}{S},\qquad
g^{\rm added}_{23}=\frac{bc}{S}.
\tag{9.21}
$$

Existing edges are added to these conductances. To see the formula,
the eliminated block is $[S]$ and its boundary coupling is
$(-a,-b,-c)^{\mathsf T}$; its Schur correction has off-diagonal
entries $-ab/S,-ac/S,-bc/S$, with matching row sums. A zero numerator
creates no edge; $S=0$ is an isolated ungrounded vertex and this
division is not made.

Equation (9.19) requires zero internal source. More generally
$L_{\mathcal I\mathcal B}x+L_{\mathcal I\mathcal I}y
=\ell_{\mathcal I}$ gives a boundary source
$\ell_{\mathcal B}
 -L_{\mathcal B\mathcal I}L_{\mathcal I\mathcal I}^{-1}\ell_{\mathcal I}$
and additional source terms in the energy. Consequently vertex
$0$ cannot be deleted by the source-free rule for the four-corner
target below, whose $d_0=1$. The reduction minimizes an information
quadratic form; it is neither deletion of recorded observations
nor restoration of an internal quantum state. Its added edges are
effective statistical couplings, not newly available gates.

### 9.5. The four-corner target and its exact optimal ports

**Definition 9.7 (Fixed fiber and its existing score).** For $n=3$ use
the order $(0,1,2,3,13)$ of (8.1) and put

$$
d=(1,-1,0,-1,1)^{\mathsf T},\qquad
\chi=d^{\mathsf T}\theta
=\theta_0-\theta_1-\theta_3+\theta_{13}.
\tag{9.22}
$$

The corresponding probability fiber at fixed $(X,Y,Z)$ is

$$
p(\kappa)
=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).
\tag{9.23}
$$

On its strictly positive interval the Fisher coefficient is

$$
I_\kappa=\sum_s\frac{d_s^2}{p_s}
=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}.
\tag{9.24}
$$

This is the existing HiddenRelations C-4.1–C-4.6 construction [Hidden9].
Its mode score is $S_s=d_s/p_s$, with
$\mathbb E_pS=0$ and $\mathbb E_pS^2=I_\kappa$.
For the retained function space
$\operatorname{span}(1,x,y,z)$ and target $w=xy$, its orthogonal
residual is

$$
h_s=\frac{d_s}{p_sI_\kappa}=\frac{S_s}{I_\kappa},
\qquad \|h\|_p^2=I_\kappa^{-1}.
\tag{9.25}
$$

The label map from Boundary Calculus §4 is exactly (8.2):
$p_{25}$ there is $\kappa=p_{13}$ here. Neither the residual
function $h_s$ nor the probability parameter $\kappa$ changes
Definition 1.1's two-mass function $h(s,t)$ or its maximum $\kappa_n$.
The phase target (9.22) uses the same vector $d$, but is a different
statistical task from estimating the probability parameter.

**Theorem 9.8 (Four-corner resistance).** For any strictly positive
five-mode law and any site budget,

$$
R_\eta(d)=
\begin{cases}
I_\kappa/(\eta_1+\eta_3),&\eta_1+\eta_3>0,\\
+\infty,&\eta_1=\eta_3=0.
\end{cases}
\tag{9.26}
$$

Thus the optimal budget puts no mass on the middle port. Every
split between the two endpoint ports has the same optimal target
coefficient $I_\kappa$, including either single-endpoint design.

Proof. Orient the bottom edges as
$(0\to1,0\to3,1\to13,3\to13)$ and the leaf as $0\to2$.
The source at vertex $2$ is zero, so its sole incident flow is zero
whenever that edge is present. Solving the four remaining
divergence equations gives all bottom flows

$$
(j_{01},j_{03},j_{1,13},j_{3,13})
=(t,1-t,t-1,-t),\qquad t\in\mathbb R.
\tag{9.27}
$$

For example the divergences at $0,1,3,13$ are
$t+(1-t)=1$, $-t+(t-1)=-1$,
$-(1-t)-t=-1$, and $-(t-1)+t=1$.
The site-$1$ edges carry $t,-t$; the site-$3$ edges carry
$1-t,t-1$. Since $h(p_u,p_v)^{-1}=p_u^{-1}+p_v^{-1}$,
their energies, when both endpoint budgets are positive, add to

$$
I_\kappa\left(\frac{t^2}{\eta_1}
              +\frac{(1-t)^2}{\eta_3}\right).
\tag{9.28}
$$

Completion of the square, or differentiation of this strictly
convex quadratic, gives
$t=\eta_1/(\eta_1+\eta_3)$ and minimum
$I_\kappa/(\eta_1+\eta_3)$. Proposition 9.5 then gives (9.26).

If $\eta_1>0,\eta_3=0$, the absent site-$3$ edges require $t=1$.
The surviving pairs $(0,1)$ and $(3,13)$ carry $1,-1$ and
have energy $I_\kappa/\eta_1$. Each pair has opposite total
source; vertex $2$ has source zero whether isolated or connected
by the middle edge. Thus component balance holds, even when
the graph is disconnected. The case $\eta_1=0,\eta_3>0$
uses $t=0$ and the pairs $(0,3),(1,13)$, with the same conclusion.
This argument does not divide by a zero budget.

If both endpoint budgets vanish, only $(0,2)$ can remain;
vertices $1,3,13$ are isolated with nonzero target coefficients.
Theorem 9.4 makes the target unestimable. Finally
$\eta_1+\eta_3=1-\eta_2\le1$, proving the allocation claim.
$\square$

A single endpoint can therefore be sufficient for this particular
contrast without identifying all four independent relative phases.
The four-corner expression compares two parallel edge phases; as
in Chapter 8, it is not a nonzero holonomy of exact vertex differences
around a closed graph cycle.

### 9.6. An explicit one-endpoint count estimator

**Proposition 9.9 (Counts, all phase nuisances and sine bias).** Choose
$\eta_1=1$. Let $n_{(u,v,\pm)}$ count the indicated site-$1$ outcome
among all $N$ samples, retaining the blocked word $2$ as well.
At $\theta^0=0$ the statistic

$$
\widehat\chi
=\frac{n_{(3,13,+)}-n_{(3,13,-)}}{2N\sqrt{p_3p_{13}}}
-\frac{n_{(0,1,+)}-n_{(0,1,-)}}{2N\sqrt{p_0p_1}}
\tag{9.29}
$$

has mean zero, full phase expectation gradient $d$, and variance
$I_\kappa/(4N)$.

Proof. On one sample define $W$ to be
$+1/(2\sqrt{p_3p_{13}})$ or its negative on the respective
$(3,13,+)$ or $(3,13,-)$ outcome;
on $(0,1,+)$ use $-1/(2\sqrt{p_0p_1})$ and on
$(0,1,-)$ its negative. Put $W=0$ on the blocked outcome.
Then $\widehat\chi=N^{-1}\sum_rW_r$ and (9.4) gives its exact mean

$$
\mathbb E_\theta\widehat\chi
=\sin(\theta_{13}-\theta_3)-\sin(\theta_1-\theta_0).
\tag{9.30}
$$

At zero this vanishes. Differentiating with respect to all five
coordinates gives $(1,-1,0,-1,1)$, including zero response in every
phase direction orthogonal to $d$. At the reference each signed
pair contribution has mean zero. The two pairs are mutually
exclusive on one sample, so their product is zero and their
covariance is zero. Their second moments give

$$
\mathbb E_0W^2
=\frac{p_3+p_{13}}{4p_3p_{13}}
 +\frac{p_0+p_1}{4p_0p_1}
=\frac{I_\kappa}{4}.
\tag{9.31}
$$

Equivalently, for categorical counts
$\operatorname{Cov}(n_a,n_b)=N(q_a\delta_{ab}-q_aq_b)$;
the signed means cancel its cross terms here. Independence of
preparations divides (9.31) by $N$. Equation (9.30) also displays
why this fixed calibrated statistic is not globally unbiased for
the linear phase contrast. $\square$

### 9.7. The single-target quantum benchmark

**Theorem 9.10 (Quantum bound for a specified phase contrast).** For
the positive law (9.1), any regular locally unbiased estimator of
$\tau_\ell$ from a parameter-independent POVM on
$|\psi_\theta\rangle^{\otimes N}$ satisfies

$$
\operatorname{Var}_0\widehat\tau_\ell
\ge \frac1{4N}\sum_u\frac{\ell_u^2}{p_u}.
\tag{9.32}
$$

Local unbiasedness is required in all phase directions as in (9.8).
The measurement may act jointly on the $N$ product copies.
Regularity here means differentiable dominated likelihoods with
square-integrable reference scores, differentiation of the relevant
expectations under the integral, and no omitted first-order mass
outside the reference score support.

Proof. Suppose first $\ell\ne0$, and set
$A_\ell=\sum_u\ell_u^2/p_u>0$. Restrict the model to the actual
one-parameter path

$$
\theta_u(t)=t\,\ell_u/p_u,\qquad
G_\ell=\sum_u(\ell_u/p_u)|u\rangle\langle u|.
\tag{9.33}
$$

At the reference,
$\langle G_\ell\rangle=\sum_u\ell_u=0$ and
$\langle G_\ell^2\rangle=A_\ell$. The horizontal derivative
$|\dot\psi\rangle=-iG_\ell|\psi_0\rangle$ has squared norm $A_\ell$,
so the pure-state QFI is $4A_\ell$, using the normalization of
Chapter 8 and Paris [Paris9], equations (26)–(27).
The target derivative along the same path is
$\dot\tau_\ell=A_\ell$, not one.

For the product state the derivative is the sum of the $N$
single-slot derivatives. Different slots are orthogonal because
$\langle\psi_0|\dot\psi\rangle=0$, so its squared norm is
$NA_\ell$ and its QFI is $4NA_\ell$.
This calculation requires independent product preparations;
it makes no restriction to separate measurements.

One can check the measurement comparison directly. Represent the
POVM by a positive density $M(y)$ against a dominating measure.
For reference product vector $\Psi$ and derivative $\dot\Psi$,
put $q=\langle\Psi|M|\Psi\rangle$. Positivity gives

$$
|\langle\Psi|M|\dot\Psi\rangle|^2
\le q\,\langle\dot\Psi|M|\dot\Psi\rangle.
$$

Since $\dot q=2\operatorname{Re}\langle\Psi|M|\dot\Psi\rangle$,
integration over $q>0$ gives classical path information at most
$4\|\dot\Psi\|^2=4NA_\ell$. At a zero-density event positivity
forces the cross term to vanish; regular scores omit it rather
than assign a limiting nonregular information value.
For continuous outcomes a concrete dominating measure and the
differentiation conditions are detailed in Proposition 9.16 below.

The scalar score identity for the estimator gives
$\operatorname{Cov}_0(\widehat\tau_\ell,S_t)=A_\ell$.
Cauchy–Schwarz therefore yields
$V F_t\ge A_\ell^2$, and the information upper bound gives
$V\ge A_\ell/(4N)$. If $F_t=0$, the nonzero covariance requirement
is impossible. If $\ell=0$, the target is constant zero and the
bound is simply $V\ge0$, attained by that constant. $\square$

For $\ell=d$, $A_\ell=I_\kappa$. The full-budget endpoint
estimator (9.29) attains (9.32), so it is optimal even against
regular collective POVMs on the same product preparations.
Combining (9.10) and its saturation with (9.32) also gives
$R_\eta(\ell)\ge A_\ell$ for every component-balanced target in
this calibrated menu. The reciprocal pair
$I_\kappa$ for the probability coordinate and $4/I_\kappa$
for the efficient phase coordinate describes two single-target
information scales. It does not yet grant their simultaneous
attainment on the same samples.

### 9.8. A different target on the same five-mode graph

**Proposition 9.11 (A target that needs all three ports).** Let
$p_s=1/5$ for all five modes, and consider

$$
\beta_{\rm target}=\theta_2-\theta_{13},\qquad
\ell_\beta=e_2-e_{13}.
$$

This symbol is unrelated to the pulse phase in (9.3).
If all $\eta_1,\eta_2,\eta_3$ are positive, then

$$
R_\eta(\ell_\beta)
=\frac5{\eta_1}+\frac{10}{\eta_2}+\frac5{\eta_3}.
\tag{9.34}
$$

Under $\eta_1+\eta_2+\eta_3=1$, its minimum and unique allocation are

$$
R_{\min}=30+20\sqrt2,\qquad
\eta_1=\eta_3=\frac1{2+\sqrt2},\qquad
\eta_2=\sqrt2-1.
\tag{9.35}
$$

If any of the three budgets is zero, the target is unestimable.

Proof. Each positive site-$i$ edge has conductance $\eta_i/10$.
Any unit source at $2$ and sink at $13$ sends unit flow along
the leaf $2\to0$, at energy $10/\eta_2$.
Between $0$ and $13$, the two bottom paths are
$0\to1\to13$ and $0\to3\to13$. Each has series resistance
$10/\eta_1+10/\eta_3$. If the first carries $t$ and the second
$1-t$, their energy is that common resistance times
$t^2+(1-t)^2$, minimized at $t=1/2$.
This gives the parallel contribution $5/\eta_1+5/\eta_3$
and proves (9.34) without an additional circuit hypothesis.

For positive $c=(5,10,5)$, Cauchy–Schwarz gives

$$
\left(\sum_i\frac{c_i}{\eta_i}\right)\left(\sum_i\eta_i\right)
\ge(\sqrt5+\sqrt{10}+\sqrt5)^2=30+20\sqrt2.
$$

Equality requires $\eta_i$ proportional to $\sqrt{c_i}$;
normalization gives (9.35). Strict positivity of all $c_i$
makes that allocation unique.

When $\eta_2=0$, vertex $2$ is isolated with target coefficient
one. When $\eta_1=0$, positive remaining edges cannot connect
$13$ to the component containing $2$; the former can connect
only to $1$ and the latter only through $0$ and $3$.
When $\eta_3=0$ the symmetric separation holds. Removing still
more edges cannot repair these separations. Theorem 9.4 therefore
excludes all zero-budget boundary cases. $\square$

This example also exposes the danger of using an unrestricted
pseudoinverse. At $(\eta_1,\eta_2,\eta_3)=(1/2,0,1/2)$,
vertex $2$ is isolated and the bottom is a four-cycle of common
conductance $1/20$. Its three nonzero Laplacian eigenvalues are
$1/10,1/10,1/5$; vertex symmetry makes every bottom diagonal
entry of $L^+$ equal to

$$
\frac14(10+10+5)=\frac{25}{4}.
$$

The isolated row of $L^+$ is zero, so
$\ell_\beta^{\mathsf T}L^+\ell_\beta=25/4$.
Nevertheless $R_\eta(\ell_\beta)=+\infty$, and no estimator
satisfies the target's full local gradient. The finite algebraic
number has projected away the very component offset being asked
for.

The quantum coefficient in (9.32) for this target is
$A_{\ell_\beta}=1/p_2+1/p_{13}=10$. Define the efficiency of this
restricted menu as the quantum variance lower bound divided by
the minimum variance it attains. Its best value is

$$
\frac{10}{30+20\sqrt2}=3-2\sqrt2.
\tag{9.36}
$$

The four-corner target has efficiency one on the same graph.
Thus graph geometry alone does not select an optimal port:
the target divergence determines which paths matter.

### 9.9. Higher-order local phase targets on legal independent sets

**Definition 9.12 (An integer alternating coordinate).** Let
$\varnothing\ne T\subseteq\{1,\ldots,n\}$ be an independent set
of the path, and let $k=|T|\ge1$. Identify legal words with their
occupied sets. Define

$$
d_T(I)=
\begin{cases}
(-1)^{k-|I|},&I\subseteq T,\\
0,&I\not\subseteq T,
\end{cases}
\qquad
\Phi_T=\sum_{I\subseteq T}(-1)^{k-|I|}\theta_I,
\tag{9.37}
$$

$$
I_T=\sum_{I\subseteq T}\frac1{p_I},\qquad
P_T=\sum_{I\subseteq T}p_I.
\tag{9.38}
$$

The binomial sum gives $\sum_I d_T(I)=(1-1)^k=0$.
Thus $p+\epsilon d_T$ is normalized and remains strictly positive
for sufficiently small $|\epsilon|$; its scalar probability
Fisher coefficient at $\epsilon=0$ is $I_T$.

The alternating vector is exactly the column for the moment
$\mu_T$ in the inverse transform of HiddenRelations C-28.5.1:
its coefficient at $p_I$ is $(-1)^{|T|-|I|}$ when $I\subseteq T$.
The supplier's position count $N$ maps to this chapter's word
length $n$, not its sample count $N$. For a proper subset
$A\subsetneq T$,

$$
\sum_I d_T(I)1_{\{A\subseteq I\}}
=\sum_{A\subseteq I\subseteq T}(-1)^{k-|I|}
=(1-1)^{k-|A|}=0.
\tag{9.39}
$$

If $A$ contains a position outside $T$, the sum is also zero.
This consumes the existing lower-moment-preserving probability
direction; the new task here is to read its phase coordinate.

**Theorem 9.13 (One selected site attains the phase-target benchmark).**
For any $i\in T$, putting all budget on site $i$ makes $\Phi_T$
locally estimable in all phase directions and gives

$$
R_{\eta_i=1}(d_T)=I_T,\qquad
\min\operatorname{Var}_0\widehat\Phi_T=\frac{I_T}{4N}.
\tag{9.40}
$$

The minimum agrees with the quantum single-target lower bound,
even allowing regular joint measurements on $N$ independent copies.
Moreover

$$
I_TP_T\ge4^k,\qquad
\operatorname{Var}_0\widehat\Phi_T
\ge\frac{4^{k-1}}{NP_T}.
\tag{9.41}
$$

Proof. For every $J\subseteq T\setminus\{i\}$, both $J$ and
$J\cup\{i\}$ are legal. Since $T$ has no adjacent positions,
inserting $i$ is permitted even at the endpoints of the word.
The site-$i$ matching pairs these two vertices, and

$$
d_T(J\cup\{i\})=-d_T(J).
$$

A vertex outside the subsets of $T$ has coefficient zero; its
site-$i$ partner, if present, is also outside those subsets.
Every other pair and every blocked singleton therefore has
total source zero. This proves component balance on the full
graph, not just on a selected subgraph.

Orient a relevant edge from $J$ to $J\cup\{i\}$ and assign
$j_e=d_T(J)\in\{-1,1\}$. Assign zero to every other site-$i$
edge. A matching has no cycles, so this is the unique feasible
flow. Its energy is

$$
\sum_{J\subseteq T\setminus\{i\}}
\left(\frac1{p_J}+\frac1{p_{J\cup\{i\}}}\right)
=\sum_{I\subseteq T}\frac1{p_I}=I_T.
$$

Propositions 9.5 and Theorem 9.4 now give (9.40), including
exact finite-$N$ reference-score attainment. An explicit
one-sample statistic is
$-d_T(J)/(2\sqrt{p_Jp_{J\cup\{i\}}})$ on that pair's $+$
outcome and its negative on $-$, with zero on all other
outcomes. Its mean is

$$
-\sum_{J\subseteq T\setminus\{i\}}d_T(J)
\sin(\theta_{J\cup\{i\}}-\theta_J).
$$

At the reference its full gradient is $d_T$ and its second
moment is $I_T/4$. Averaging independent samples gives the
same variance directly. All nonrelevant outcomes remain in
the record and are assigned zero, not postselected away.

Since $\sum_I d_T(I)^2/p_I=I_T$, Theorem 9.10 proves quantum
optimality. Finally Cauchy–Schwarz on the $2^k$ positive
subset probabilities gives

$$
\left(\sum_{I\subseteq T}p_I\right)
\left(\sum_{I\subseteq T}p_I^{-1}\right)
\ge\left(\sum_{I\subseteq T}1\right)^2=4^k.
$$

Equality requires all $p_I$, $I\subseteq T$, equal. Combining
with (9.40) proves (9.41). $\square$

For $k=1$ this is the ordinary phase difference between the
empty word and one occupied site; the proof includes $n=1$.
For $T=\{1,3\}$ it recovers $d$ and the endpoint designs above.
The bound refers to the fixed integer coefficient coordinate
(9.37), with all other phase directions unconstrained nuisance
directions. Rescaling $\Phi_T$ rescales its variance bound;
a prior restricting the nuisance family changes the estimation
problem. The exponential coefficient in (9.41) is a local
sample cost for that specified coordinate. One legal pulse
per preparation suffices for this readout under the added
menu. That does not implement the separate task of changing
probabilities while preserving lower moments, nor prove a
universal exponential computation or physical-time bound.

### 9.10. A fixed-reference probability–phase family

**Definition 9.14 (Shared calibration and actual four-corner angle).**
Fix a strictly positive five-mode law $\bar p$, put
$\kappa_0=\bar p_{13}$, and define

$$
I_0=\sum_s\frac{d_s^2}{\bar p_s},\qquad
a_s=\frac{d_s}{\bar p_sI_0},\qquad
p_s(\kappa)=\bar p_s+(\kappa-\kappa_0)d_s.
\tag{9.42}
$$

Here $a_s$ is fixed once and for all at $\bar p$.
It is not recomputed at the moving value $\kappa$.
Writing $\delta=\kappa-\kappa_0$, the positive domain is

$$
-\min(\bar p_0,\bar p_{13})<\delta
 <\min(\bar p_1,\bar p_3).
\tag{9.43}
$$

The middle mass stays $\bar p_2>0$, normalization is preserved,
and the three occupancies $(X,Y,Z)$ stay fixed as in (9.23).
For real local $\chi$ near zero set

$$
|\psi(\kappa,\chi)\rangle
=\sum_s\sqrt{p_s(\kappa)}\,e^{-i\chi a_s}|s\rangle.
\tag{9.44}
$$

Since $\sum_s d_sa_s=1$, its actual four-corner angle is
$d^{\mathsf T}\theta=d^{\mathsf T}(\chi a)=\chi$.
Also $\sum_s\bar p_sa_s=0$.
The coefficients $a_s$ are the residual (9.25) at the
reference, with the same label and probability-fiber map.
They are not new adjustable probability parameters.

The negative-phase convention agrees with Boundary Calculus
Definitions 15.9–15.11 [Boundary9]. Its chosen dimensionless
projected two-form is

$$
\Omega=\sum_s d\theta_s\wedge dp_s.
\tag{9.45}
$$

On the normalized sphere its common-phase direction has zero
pairing with normalized probability variations; after the
stated phase quotient it is well-defined. Here the pullback
can be computed without a quotient assertion:
$d\theta_s=a_s\,d\chi$ and $dp_s=d_s\,d\kappa$, hence

$$
\Omega|_{(9.44)}
=\left(\sum_sa_sd_s\right)d\chi\wedge d\kappa
=d\chi\wedge d\kappa.
\tag{9.46}
$$

In the Hilbert convention conjugate-linear in the first slot,
the form is $2\operatorname{Im}\langle\delta_1\psi|
\delta_2\psi\rangle$ on horizontal vectors. With negative
state phases its $d\theta\wedge dp$ sign is as displayed.
HiddenRelations C-13–C-14 uses positive exponent phases;
its angle $\Phi$ is $-\chi$ under this map, so its sign
cannot be carried over without that change. The selected
scale in (9.45) contains no physical clock or action constant.

**Proposition 9.15 (Horizontal derivatives and their complex relation).**
At $(\kappa,\chi)=(\kappa_0,0)$, in the mode basis,

$$
u:=\partial_\kappa\psi
=\left(\frac{d_s}{2\sqrt{\bar p_s}}\right)_s,\qquad
v:=\partial_\chi\psi
=\left(-\frac{i\,d_s}{I_0\sqrt{\bar p_s}}\right)_s
=-\frac{2i}{I_0}u.
\tag{9.47}
$$

They are horizontal, and

$$
\langle\psi|u\rangle=\langle\psi|v\rangle=0,\qquad
\|u\|^2=\frac{I_0}{4},\quad
\|v\|^2=\frac1{I_0},\quad
\langle u|v\rangle=-\frac i2.
\tag{9.48}
$$

The pure-state QFI matrix in coordinates $(\kappa,\chi)$ is

$$
H=\begin{pmatrix}I_0&0\\0&4/I_0\end{pmatrix}.
\tag{9.49}
$$

Proof. Differentiate the square root in (9.44) in $\kappa$
and the fixed exponential in $\chi$. This gives (9.47);
there is no derivative of $a_s$. The two horizontal
identities follow from $\sum_sd_s=0$. Taking the indicated
finite sums gives (9.48). The pure-state information formula
is $H_{ab}=4\operatorname{Re}
(\langle\partial_a\psi|\partial_b\psi\rangle
-\langle\partial_a\psi|\psi\rangle
 \langle\psi|\partial_b\psi\rangle)$.
Substitution proves (9.49). $\square$

The metric coefficients $I_0/4$ and $1/I_0$ are exactly
HiddenRelations C-14.1–C-14.2 at this reference, after
$\Phi=-\chi$. Its varying optimal phase lift
$d_s/(p_sI_\kappa)$ is consumed only at $p=\bar p$;
(9.44) uses the frozen values (9.42) throughout its
neighborhood. The real off-diagonal entry of $H$ vanishes,
but the nonzero imaginary inner product in (9.48) remains.
It cannot be discarded as evidence of simultaneous
measurement compatibility.

### 9.11. The two-parameter information budget for arbitrary joint POVMs

**Proposition 9.16 (Direct complex-tangent bound).** In the fixed family
(9.44), take $N$ independent identical preparations and any
parameter-independent POVM on their full product space.
Suppose its local likelihood and scores satisfy the regularity
conditions of Theorem 9.10. Let $F$ be its classical Fisher matrix
at $(\kappa_0,0)$. Then

$$
\frac{F_{\kappa\kappa}}{NI_0}
+\frac{I_0F_{\chi\chi}}{4N}\le1.
\tag{9.50}
$$

This includes nonseparable collective measurements and regular
continuous outcome spaces.

Proof. Start with one copy and define the unit horizontal vector
$e=2u/\sqrt{I_0}$. Then

$$
\partial_\kappa\psi=\frac{\sqrt{I_0}}2e,\qquad
\partial_\chi\psi=-\frac{i}{\sqrt{I_0}}e,\qquad
\langle\psi|e\rangle=0.
\tag{9.51}
$$

For a discrete positive effect $M$ put
$q=\langle\psi|M|\psi\rangle$ and
$z=\langle\psi|M|e\rangle$. The derivative identities are

$$
\partial_\kappa q=\sqrt{I_0}\operatorname{Re}z,\qquad
\partial_\chi q=\frac2{\sqrt{I_0}}\operatorname{Im}z.
\tag{9.52}
$$

The sign in the second equation follows from
$\operatorname{Re}(-iz)=\operatorname{Im}z$ and the negative
state-phase convention. Positivity of the two-dimensional
compression of $M$ gives

$$
|z|^2\le q\,\langle e|M|e\rangle.
\tag{9.53}
$$

On $q>0$, the sum of its normalized Fisher contributions is
$(\operatorname{Re}z)^2/q+(\operatorname{Im}z)^2/q=|z|^2/q$.
Summing (9.53) over the POVM and using $\sum M=I$ gives one.

For an arbitrary outcome measurable space, write its POVM as
$M(A)$ and take the finite scalar measure
$\mu(A)=\operatorname{tr}M(A)$ on the finite-dimensional
Hilbert space. Every matrix entry has a Radon–Nikodym density;
these entries form a positive matrix $m(y)$ almost everywhere,
with $\int m(y)\,d\mu(y)=I$.
Set $q(y)=\langle\psi|m(y)|\psi\rangle$ and
$z(y)=\langle\psi|m(y)|e\rangle$.
The same formulas hold almost everywhere and the sums become
integrals. The regular score is $(\partial_aq)/q$ on
$\{q>0\}$, with

$$
F_{ab}=\int_{\{q>0\}}
\frac{(\partial_aq)(\partial_bq)}q\,d\mu.
\tag{9.54}
$$

At $q=0$, positivity implies $m(y)^{1/2}\psi=0$ and hence
$z=0$; such points contribute no reference score term.
Equations (9.52)–(9.53) give integrability of the information
terms and the same upper bound. For use in Cramér–Rao
identities we additionally require differentiation under the
likelihood and estimator integrals and square-integrable
scores, as stated. A zero outcome whose probability emerges
only to second order does not receive an extra
direction-dependent limiting Fisher value. Nonregular
procedures using such limits are not covered by this local
score claim.

For $N$ copies put $\Psi=\psi^{\otimes N}$ and define

$$
e_N=\frac1{\sqrt N}\sum_{r=1}^N
\psi^{\otimes(r-1)}\otimes e\otimes\psi^{\otimes(N-r)}.
\tag{9.55}
$$

Each summand has norm one, and two distinct summands have inner
product zero because $\langle\psi|e\rangle=0$.
Also each is orthogonal to $\Psi$. Therefore $e_N$ is unit and
horizontal, while direct product differentiation gives

$$
\partial_\kappa\Psi=\frac{\sqrt{NI_0}}2e_N,\qquad
\partial_\chi\Psi=-i\sqrt{\frac N{I_0}}e_N
=-\frac{2i}{I_0}\partial_\kappa\Psi.
\tag{9.56}
$$

For any joint effect, now acting on the entire product space,
set $q=\langle\Psi|M|\Psi\rangle$ and
$z=\langle\Psi|M|e_N\rangle$.
Its two derivatives are
$\sqrt{NI_0}\operatorname{Re}z$ and
$2\sqrt{N/I_0}\operatorname{Im}z$.
Consequently the two normalized contributions in (9.50)
again sum to $|z|^2/q$, bounded by
$\langle e_N|M|e_N\rangle$. Integration gives one.
This proves (9.50) for the full joint POVM, without factoring
it into one-copy measurements. $\square$

The relevant geometric fact is one complex horizontal tangent
line, with the two real parameter derivatives related by (9.56).
The ambient one-copy state space here has dimension five.
Gill–Massar [GM9], Theorem I, equation (27), gives the
pure-state bound $\operatorname{tr}(H^{-1}I^N)\le N(D-1)$
for a $D$-dimensional system, including collective measurements.
Their §V.A–B develops rank-one refinement and product-copy
derivatives. That theorem at ambient $D=5$ does not by itself
give the right-hand side one in (9.50). Nor can a single-copy
statement with an asserted ambient $D=2$ stand in for the
joint proof. Here (9.51)–(9.56) establish exactly the required
two-real-dimensional tangent relation and its persistence on
all $N$ product copies. The general information tradeoff
retains its classical quantum-estimation attribution.

### 9.12. The resulting joint variance obstruction

**Theorem 9.17 (Full-gradient local variance tradeoff).** Let
$(\widehat\kappa,\widehat\chi)$ have finite positive variances
$V_\kappa,V_\chi$ under a measurement covered by Proposition 9.16.
Require, in the family (9.44),

$$
\mathbb E_0
\begin{pmatrix}\widehat\kappa\\\widehat\chi\end{pmatrix}
=\begin{pmatrix}\kappa_0\\0\end{pmatrix},\qquad
\left.\frac{\partial(\mathbb E\widehat\kappa,
                    \mathbb E\widehat\chi)}
{\partial(\kappa,\chi)}\right|_0=I_2.
\tag{9.57}
$$

Thus each estimator has derivative zero in the other parameter's
direction. Then

$$
\frac1{NI_0V_\kappa}
+\frac{I_0}{4NV_\chi}\le1,\qquad
V_\kappa V_\chi\ge\frac1{N^2}.
\tag{9.58}
$$

Proof. With $S_\kappa,S_\chi$ the scores of the full record,
regularity and (9.57) give

$$
\begin{aligned}
\operatorname{Cov}_0(\widehat\kappa,S_\kappa)&=1,&
\operatorname{Cov}_0(\widehat\kappa,S_\chi)&=0,\\
\operatorname{Cov}_0(\widehat\chi,S_\chi)&=1,&
\operatorname{Cov}_0(\widehat\chi,S_\kappa)&=0.
\end{aligned}
\tag{9.59}
$$

In particular $F_{\kappa\kappa},F_{\chi\chi}>0$, since otherwise
a score of variance zero could not have covariance one.
Two scalar Cauchy–Schwarz inequalities give

$$
V_\kappa F_{\kappa\kappa}\ge1,\qquad
V_\chi F_{\chi\chi}\ge1.
$$

They remain necessary even when the other parameter is unknown.
They neither invert $F$ nor assume a zero off-diagonal entry.
Insert the reciprocal lower bounds for its diagonals into
(9.50) to obtain the first inequality in (9.58).

For the product define positive dimensionless numbers

$$
a=NI_0V_\kappa,\qquad b=\frac{4N}{I_0}V_\chi.
$$

Then $1/a+1/b\le1$, so $a+b\le ab$.
Also $a+b\ge2\sqrt{ab}$, hence $ab\ge4$.
Since $ab=4N^2V_\kappa V_\chi$, the product bound follows.
Equality in this last bound requires $a=b=2$. $\square$

No assumption about the covariance of the estimators removes
these necessary scalar bounds. Simultaneously obtaining the
two separate single-target variances $1/(NI_0)$ and
$I_0/(4N)$ would instead give normalized reciprocal sum two
and product $1/(4N^2)$, contradicting (9.58).
The constants concern this normalization of $\kappa,\chi$
and the number of independent copies. They do not assert a
universal Planck constant, a physical time cost, or a new
uncertainty law for arbitrary observables.

### 9.13. Exact finite-sample designs and the marginal variance region

**Proposition 9.18 (Two resolved settings and their information).**
In (9.44) one full mode measurement has information
$\operatorname{diag}(I_0,0)$ at the reference.
One site-$1$ endpoint quadrature measurement with all outcomes
retained has information $\operatorname{diag}(0,4/I_0)$.
Independently selecting the first setting with a fixed known
probability $t\in[0,1]$, and recording that selection, gives

$$
F_t=\begin{pmatrix}tI_0&0\\0&(1-t)4/I_0\end{pmatrix}
\tag{9.60}
$$

per preparation.

Proof. Full mode probabilities are $p_s(\kappa)$ and are
independent of $\chi$, so their reference scores are
$(d_s/\bar p_s,0)$; summing their squares gives the first
matrix. For the endpoint quadrature, each observed pair
has $d_u+d_v=0$ and the blocked word $2$ has $d_2=0$.
Differentiate its likelihood

$$
q_{\kappa,\chi}(e,\pm)
=\frac{p_u(\kappa)+p_v(\kappa)}2
 \pm\sqrt{p_u(\kappa)p_v(\kappa)}
       \sin\bigl(\chi(a_v-a_u)\bigr).
\tag{9.61}
$$

At $(\kappa_0,0)$ the $\kappa$ derivative vanishes in every
outcome: the derivative of the total pair mass is zero and
the amplitude derivative multiplies $\sin0$. This uses the
fixed $a$ of (9.42). The $\chi$ derivative is
$\pm\sqrt{\bar p_u\bar p_v}(a_v-a_u)$, and

$$
a_v-a_u
=-\frac{d_u}{I_0}
  \left(\frac1{\bar p_u}+\frac1{\bar p_v}\right).
$$

Thus that pair's $\chi$ information is

$$
4\frac{\bar p_u\bar p_v}{\bar p_u+\bar p_v}(a_v-a_u)^2
=\frac4{I_0^2}
 \left(\frac1{\bar p_u}+\frac1{\bar p_v}\right).
$$

The pairs $(0,1)$ and $(3,13)$ cover all four nonzero
coefficients, so their sum is $4/I_0$.
The blocked outcome has both derivatives zero.
The cross information is zero because the $\kappa$ score
is zero throughout this setting.

For recorded setting $A$ or $B$, the joint probabilities are
$tq_A$ and $(1-t)q_B$. The setting law is independent of the
parameters, so its logarithmic derivative is zero, and the
Fisher matrix is the weighted sum of the two conditional
matrices. This proves (9.60). At $t=0$ or one the unused
setting is removed from the alphabet. $\square$

**Theorem 9.19 (Randomized and integer allocations).** For every
integer $N\ge1$ and every real $0<t<1$, choose the settings
independently on all $N$ preparations with the recorded law
of Proposition 9.18. Let $s_t(Y)$ be the two-component
one-sample score evaluated at $(\kappa_0,0)$ and held fixed.
Then

$$
\begin{pmatrix}\widehat\kappa\\\widehat\chi\end{pmatrix}
=\begin{pmatrix}\kappa_0\\0\end{pmatrix}
 +F_t^{-1}\frac1N\sum_{r=1}^Ns_t(Y_r)
\tag{9.62}
$$

satisfies the complete two-parameter gradient (9.57), and

$$
\operatorname{Cov}_0
\begin{pmatrix}\widehat\kappa\\\widehat\chi\end{pmatrix}
=\frac1N F_t^{-1},\qquad
V_\kappa=\frac1{NtI_0},\quad
V_\chi=\frac{I_0}{4N(1-t)}.
\tag{9.63}
$$

A deterministic allocation has these same formulas when
$m=Nt$ is an integer with $1\le m\le N-1$, using $m$
full mode samples and $N-m$ endpoint samples.
The product minimum $1/N^2$ is attained by randomized
$t=1/2$ for every $N\ge1$, and by deterministic equal
allocation when $N$ is even.

Proof. For the recorded single-sample experiment,
$\mathbb E_0s_t=0$,
$\mathbb E_0s_ts_t^{\mathsf T}=F_t$, and the expectation
Jacobian of the fixed score is $F_t$.
Independence therefore makes the mean of (9.62) the reference,
its Jacobian $F_t^{-1}F_t=I_2$, and its covariance
$F_t^{-1}F_tF_t^{-1}/N=F_t^{-1}/N$.
This is an exact finite-sum argument, not an asymptotic
normality or a parameter-free efficient-estimation assertion.

More explicitly, let $U=d_s/\bar p_s$ on a full mode outcome
$s$, and let $V$ be the endpoint $\chi$ score from (9.61).
The scores in the mixed experiment are
$(U,0)$ when setting $A$ is drawn and $(0,V)$ when $B$
is drawn. Equation (9.62) is therefore

$$
\widehat\kappa
=\kappa_0+\frac{\sum_{r:A_r}U_r}{NtI_0},
\qquad
\widehat\chi
=\frac{I_0\sum_{r:B_r}V_r}{4N(1-t)}.
\tag{9.64}
$$

The denominators use the fixed design probabilities and
total $N$, not the random numbers of draws of each setting.
An empty sum is zero. In particular the events that all
samples use $A$, or all samples use $B$, have probabilities
$t^N$ and $(1-t)^N$ and are retained. On them one reported
coordinate equals its reference value. Their contributions
are included in the expectation, gradient and variance
calculations above; no division by zero observed counts
or postselection is needed. This covers $N=1$ as well.

For a deterministic schedule, use instead

$$
\widehat\kappa
=\kappa_0+\frac1{mI_0}\sum_{r=1}^{m}U_r,\qquad
\widehat\chi
=\frac{I_0}{4(N-m)}\sum_{r=1}^{N-m}V_r.
\tag{9.65}
$$

The first set of scores has variance $I_0$ and expectation
gradient $(I_0,0)$; the second has variance $4/I_0$ and
gradient $(0,4/I_0)$. The two sets are independent. Thus
(9.65) has Jacobian $I_2$ and variances
$1/(mI_0)$ and $I_0/[4(N-m)]$, exactly (9.63) for
$t=m/N$. A deterministic sample count cannot realize an
arbitrary real $Nt$. In particular $N=1$ has no
deterministic schedule using both settings.

Finally the product in (9.63) is
$1/[4N^2t(1-t)]$, minimized at $t=1/2$ with value $1/N^2$.
The reciprocal inequality (9.58) is an equality for every
$0<t<1$. $\square$

For $t=0$ the $\kappa$ score is zero and for $t=1$ the
$\chi$ score is zero. In either case (9.59) rules out
joint local unbiasedness with finite variances. Individual
single-target tasks remain available. The retained
$(X,Y,Z)$ are fixed in this joint model; (9.57) makes no
claim that a $\kappa$ estimator is unbiased in additional
unspecified probability nuisance directions.
The phase count estimator (9.29), by contrast, already
has its full phase gradient in the larger fixed-$p$ model.

**Corollary 9.20 (Exact marginal variance-pair region with external noise).**
If independent, parameter-free classical output randomization
is allowed, the complete set of finite positive marginal
variance pairs of regular locally unbiased estimators at
this reference, over the measurements allowed in
Proposition 9.16, is

$$
\mathcal V_N=
\left\{(V_\kappa,V_\chi)\in(0,\infty)^2:
\frac1{NI_0V_\kappa}+\frac{I_0}{4NV_\chi}\le1\right\}.
\tag{9.66}
$$

This statement concerns the two marginal variances, not
a characterization of all attainable covariance matrices.

Proof. Necessity is Theorem 9.17; independent classical
randomization can be incorporated in the POVM outcome,
so it does not avoid the bound.
For sufficiency, take a proposed pair in (9.66). The interval

$$
\frac1{NI_0V_\kappa}\le t
\le1-\frac{I_0}{4NV_\chi}
\tag{9.67}
$$

is nonempty, and every member is strictly between zero
and one because both variances are finite and positive.
Choose one such fixed $t$. Theorem 9.19 gives variances
$v_\kappa=1/(NtI_0)\le V_\kappa$ and
$v_\chi=I_0/[4N(1-t)]\le V_\chi$.
Independently of all data, settings and each other, draw
two symmetric signs $\epsilon_\kappa,\epsilon_\chi$
with probabilities $1/2,1/2$. Add the noises

$$
Z_\kappa=\sqrt{V_\kappa-v_\kappa}\,\epsilon_\kappa,\qquad
Z_\chi=\sqrt{V_\chi-v_\chi}\,\epsilon_\chi
\tag{9.68}
$$

to the respective estimates, taking a zero noise when its
coefficient is zero. Their laws are fixed constants of
the design and the supplied reference, independent of
the unknown $(\kappa,\chi)$. Each has mean zero for every
parameter, so all local expectation derivatives remain
those in (9.57). Independence adds precisely the desired
variance deficits, with no cross covariance. This realizes
the proposed pair. $\square$

No fixed upper bound on the magnitude of this optional
output noise is imposed across designs. It is explicit
classical randomization, not an extra quantum preparation
or a hidden source of parameter information. The construction
realizes each marginal pair, here with zero covariance;
it asserts nothing about realizing a separately prescribed
nonzero covariance. Estimator outputs are real numbers and
need not lie in the physical parameter interval on every
sample. Clipping them to that interval would require
rechecking local unbiasedness.

### 9.14. Exact suppliers and applicability of the target geometry

The results above use established information, electrical
network and pure-state estimation tools inside a specific
legal-word experiment. Their source-specific content is the
target map, the endpoint and higher-order designs, the
different-target allocation, and the fixed-family
finite-sample tradeoff. Generic Fisher identities, Schur
complements, flow minimization and quantum Cramér–Rao
bounds retain their existing ownership.

| Supplier and actual passage | Parameter and hypothesis correspondence | Consumed result and boundary |
| --- | --- | --- |
| This volume, Definition 1.1 and Chapter 8 | Full finite $B_n$, legal Hamming-one edges, same positive law $p$, negative phases and the resolved quadrature basis; the pulse phase map is (9.3). | Equations (9.4)–(9.7) extend the existing uniform-site information identity to recorded probabilities $\eta_i$. They do not reissue legal-edge discovery or assume a stationary attaining producer. |
| [HiddenRelations][Hidden9], C-4.1–C-4.6, C-13.1–C-14.2 | $(0,1,2,3,13)$, fixed occupancies $(X,Y,Z)$, $d=(1,-1,0,-1,1)$, score $d_s/p_s$, information $I_\kappa$, residual $d_s/(p_sI_\kappa)$; its positive-phase angle maps to $-\chi$. | Equations (9.23)–(9.25), (9.42) and the reference metric (9.48). Its full-mode probability information is used with identity observation; its classical conditional-score loss formula is not a source of coherent phase access. The residual lift is fixed at $\bar p$ in the two-parameter model. |
| [HiddenRelations][Hidden9], C-28.1.2, C-28.2.2–C-28.2.3 and C-28.5.1–C-28.6 | Its legal position sets $\Sigma_N$ map to $B_n$ with its $N=n$; inverse-moment column $\mu_T$ maps exactly to (9.37). | Existing alternating lower-moment-preserving probability directions are consumed in (9.39). The local phase readout uses the additional Chapter 8 instrument, not a classical higher-order exchange operation. |
| [Boundary Calculus][Boundary9], §4, §10, Definitions 15.9–15.11 | Old labels $(0,2,3,5,25)$ map by (8.2); $\kappa=p_{25}=p_{13}$, $(X,Y,Z)=(\mathbb E u_1,\mathbb E u_3,\mathbb E u_2)$; negative phases and the selected two-form are (9.45). | Probability-fiber and operation-graph correspondence; the pullback (9.46). Its geometric pyramid, chosen Hamilton flow and physical-time cautions remain distinct from the estimation sample budget. |
| [FiveModeMixedCoordinates][Coordinates9], existing definitions of hidden direction and Fisher coefficient; [SchurMinimum][Schur9], existing Schur quadratic minimum | The five coordinates have the same order and $d$; the Schur blocks map to $A=L_{\mathcal B\mathcal B}$, $B=L_{\mathcal B\mathcal I}$, $C=L_{\mathcal I\mathcal I}$, with real matrices included in the complex setting. | Existing algebraic interfaces, with grounded positivity supplied by the full-graph energy proof here. The code's probability log-cross-ratio coordinate is not the phase $\chi$. This chapter asserts ordinary proofs and no newly checked formal application. |
| Florian Dörfler and Francesco Bullo, *Kron Reduction of Graphs with Applications to Electrical Networks*, arXiv:1102.2950v1, equations (1.2), (2.1), Lemma 2.1, Theorem 3.9 equation (3.14); [existing Library entry][KronLibrary9] | Symmetric connected loopless $Q=L$; retained vertices $\alpha=\mathcal B$; source-free eliminated coordinates mean $\ell_{\mathcal I}=0$. The primary at-least-two boundary hypothesis is used in its stated domain, while singleton and empty cases are handled explicitly above. | Classical Schur reduction and pair resistance preservation underpin (9.17)–(9.21). Nonzero eliminated sources require the affine correction, so vertex $0$ is retained for $d_0=1$. Reduced statistical edges supply no gates. |
| Nicolas Boumal, Amit Singer, P.-A. Absil and Vincent D. Blondel, *Cramér–Rao bounds for synchronization of rotations*, arXiv:1211.1621v2, §2 Assumptions 1–3, Theorem 5.4 equation (5.23), §6 equations (6.17)–(6.23) | Their vertices index unknown rotations; $SO(2)$ is the scalar phase analogy, with their rotation dimension two and their vertex count corresponding to $|B_n|$. Their smooth positive, independent isotropic edge-noise law is not (9.4). | Literature background for Laplacian-shaped information and resistance. Resolved categorical edge events within one sample are mutually exclusive, not independent noisy rotation observations, so no synchronization theorem is imported to prove (9.7), global phase calibration or finite-$N$ saturation. Their general manifold curvature qualifications are not discarded. |
| Matteo G. A. Paris, *Quantum Estimation for Quantum Technology*, arXiv:0804.2981v3, §2 equations (1)–(8), §4.1 equations (26)–(27) | Pure unitary scalar path generated by $G_\ell$, mean generator zero, independent product count $N$, and regular locally unbiased scalar estimator; target derivative is $A_\ell$. | QFI $4\operatorname{Var}G_\ell$ and the scalar comparison in (9.32). The actual product derivative and direct POVM inequality are given here. No finite-$N$ or multiparameter attainability is imported from a general scalar bound. |
| Richard D. Gill and Serge Massar, *State estimation for large ensembles*, arXiv:quant-ph/9902063v2, §IV Theorem I equation (27), §V.A–B equations (33)–(45) | Their pure-state collective setting applies to product preparations; the ambient one-copy dimension is five here. Equations (9.51)–(9.56) additionally establish one complex tangent direction for this specific two-parameter submodel. | Information-tradeoff and rank-one refinement background. Bound (9.50) is proved directly for arbitrary regular joint POVMs, not inferred by declaring the ambient state to be a qubit. Their mixed-state separable bound and asymptotic estimator assertions are not used for (9.62). |

For orientation, the conditional-null response and finite-certificate
supplier [Conditional9] concerns an actual two-sided stationary law,
its exterior conditional expectations and possible finite hidden
presentations. Its $\Phi_n$ uses the same harmonic edge function,
but its source perturbations and stationary attainment hypotheses
are not assumptions of this finite coherent experiment. Neither
a target flow nor an optimal readout settles its arbitrary finite
producer question or this volume's Open Problem 7.2.

All target-resistance statements keep component balance or explicitly
use infinite extended resistance. All finite-sample attainments
refer to a supplied strictly positive calibration and a local
reference, with complete recorded outcomes and the stated nuisance
gradients. Real allocation fractions at arbitrary finite $N$ use
independent recorded random settings; deterministic schedules use
integer counts. The collective upper bound keeps both product
preparations and the exact proportional tangent relation. These
are ordinary mathematical source applications, without claims of
global unbiasedness, unknown-reference calibration, native
physical menus, hardware realization, or originality of the
general tools.

[Hidden9]: AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md
[Boundary9]: AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md
[Conditional9]: FIB_LEGAL_EDGE_LOAD_CONDITIONAL_NULL_RESPONSE_AND_FINITE_CERTIFICATE.md
[Coordinates9]: ../../../D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.lean
[Schur9]: ../../../D5/S3/Quantum/Matrix/SchurMinimum.lean
[KronLibrary9]: ../../../Library/GraphInvariants/dorflerbullo2013kron.md
[Kron9]: https://arxiv.org/abs/1102.2950v1
[Boumal9]: https://arxiv.org/abs/1211.1621v2
[Paris9]: https://arxiv.org/abs/0804.2981v3
[GM9]: https://arxiv.org/abs/quant-ph/9902063v2

## 追加锚（本行以下为增补区）
## 10. Relation overlap, highest-order chains and common phase-readout ports

### 10.1. Legal moment directions and the supplied inverse

**Definition 10.1 (Selected relation coordinates).** Fix $n\ge1$ and identify
$B_n$ with all independent subsets of the path $[n]$, including $\varnothing$.
Write $d_n=|B_n|=F_{n+2}$, with $F_0=0,F_1=1$. For every legal $T$ put

$$
m_T(I)=1_{\{T\subseteq I\}},\qquad
d_T(I)=(-1)^{|T|-|I|}1_{\{I\subseteq T\}},\qquad
\mu_T(p)=\sum_{I\in B_n}p_I m_T(I).
\tag{10.1}
$$

These are the moment functions and inverse columns supplied by
[Correlation, §23.2][Correlation10]. Its $\Gamma_n,T',S',D_{T'}$ map to
$B_n,T,S,d_T$ here; its signed measure $D_{T'}$ is identified with its
coordinate column on the finite set $B_n$. In particular, for all legal
$S,T$, including the empty set, its Boolean-interval calculation reads

$$
\sum_{I\in B_n}m_S(I)d_T(I)=
\begin{cases}
\displaystyle\sum_{S\subseteq I\subseteq T}(-1)^{|T|-|I|}
 =(1-1)^{|T\setminus S|},&S\subseteq T,\\
0,&S\not\subseteq T,
\end{cases}
=\delta_{ST}.
\tag{10.2}
$$

Here the zero-exponent value is one. Every subset of a legal $T$ is legal,
which is the precise Boolean interval needed in this sum; the whole
independent-set poset need not be a Boolean lattice. The supplier's inverse
and counting formulas therefore apply without changing the domain:

$$
p=\sum_{T\in B_n}\mu_T(p)d_T,\qquad
p_I=\sum_{\substack{T\in B_n\\I\subseteq T}}
(-1)^{|T|-|I|}\mu_T(p).
\tag{10.3}
$$

The counting correspondence sends a legal $a$-tuple
$i_1<\cdots<i_a$ to $i_j-(j-1)$ in $[n-a+1]$, giving
$\binom{n-a+1}{a}$ sets of size $a$. Splitting words by the last bit gives
$d_n=d_{n-1}+d_{n-2}$ with $d_0=1,d_1=2$, hence $F_{n+2}$.
Taking $S=\varnothing$ in (10.2) shows that every nonempty $d_T$ has
total mass zero. The empty column has mass one and is excluded from the
probability perturbations below. For $n=3$, in the order
$(\varnothing,\{1\},\{2\},\{3\},\{1,3\})$, the column is exactly
$d_{\{1,3\}}=(1,-1,0,-1,1)^{\mathsf T}$ of Definition 9.7.

Choose $r\ge1$ distinct nonempty legal sets $T_1,\ldots,T_r$, and let
$D$ be the $d_n\times r$ matrix with columns $d_{T_j}$. Choose one known
reference probability $p^0$ strictly positive on every $I\in B_n$. Set

$$
P=\operatorname{diag}(p^0_I),\qquad
\mathcal U=\{\xi\in\mathbb R^r:p^0+D\xi>0\},\qquad
p^\xi=p^0+D\xi.
\tag{10.4}
$$

The inequality is entrywise. This is an open convex domain containing zero,
and every $p^\xi$ has total mass one. Formula (10.2) gives, exactly,

$$
\mu_{T_j}(p^\xi)=\mu_{T_j}(p^0)+\xi_j,\qquad
\mu_S(p^\xi)=\mu_S(p^0)\quad
(S\notin\{T_1,\ldots,T_r\}).
\tag{10.5}
$$

Thus the selected moments vary independently while every other moment is
fixed. Indeed, pairing $Dc=0$ with each $m_{T_j}$ gives $c_j=0$.
Consequently $D$ has full column rank and $r\le d_n-1$. This is exact
consumption of the existing inverse, not an additional assumption of
independence for overlapping statistical scores.

### 10.2. All-pair Fisher overlap on the positive fiber

**Theorem 10.2 (Overlap matrix for the selected moments).** For a full-mode
observation $I$ with law $p^\xi$, the reference score, as a column in
$\mathbb R^r$, and its Fisher matrix are

$$
s(I)=\frac{D_{I,\cdot}^{\mathsf T}}{p^0_I},\qquad
\mathbb E_0s=0,\qquad
G=\mathbb E_0ss^{\mathsf T}=D^{\mathsf T}P^{-1}D>0.
\tag{10.6}
$$

For any two of the selected sets $S,T$ their entry is

$$
G_{ST}=(-1)^{|S|+|T|}
\sum_{I\subseteq S\cap T}\frac1{p^0_I}.
\tag{10.7}
$$

In particular every entry is nonzero. If $S\cap T=\varnothing$ it is
$(-1)^{|S|+|T|}/p^0_\varnothing$. At the uniform reference,

$$
G_{ST}=d_n(-1)^{|S|+|T|}2^{|S\cap T|},\qquad
\operatorname{Corr}_0(s_S,s_T)
=(-1)^{|S|+|T|}2^{-|S\mathbin{\triangle}T|/2}.
\tag{10.8}
$$

Proof. Differentiating $\log p^\xi_I$ at zero gives (10.6). Its mean
vanishes by the zero column sums of $D$. For $c\ne0$,
$c^{\mathsf T}Gc=\sum_I(Dc)_I^2/p^0_I>0$ by full column rank and
positivity. A summand in $G_{ST}$ can be nonzero only for
$I\subseteq S\cap T$. On this intersection its numerator is
$(-1)^{|S|+|T|-2|I|}=(-1)^{|S|+|T|}$. No cancellation occurs, and the
empty subset always contributes. At $p^0_I=1/d_n$ there are
$2^{|S\cap T|}$ terms. The diagonal entries are $d_n2^{|S|}$ and
$d_n2^{|T|}$; their geometric mean yields (10.8). $\square$

Here overlap is an inner product of two scores of the same probability
experiment. The common empty-word term is a positive-probability event,
not a zero-probability event. A change to orthogonal score coordinates,
for example by $G^{-1/2}$, mixes the specified moment labels. Neither
the nonzero entries nor such a change of coordinates defines a physical
interaction between positions. Complex amplitudes and phase observations
are additional structures, introduced in §10.6.

### 10.3. The even highest-order chain and its classical inverse

**Theorem 10.3 (Highest-order overlap on an even path).** Let $n=2k$,
$k\ge1$, and take all maximum independent sets, indexed from $0$ to $k$:

$$
T_j=\{1,3,\ldots,2j-1\}\ \cup\
\{2j+2,2j+4,\ldots,2k\},\qquad 0\le j\le k.
\tag{10.9}
$$

Empty pieces in this expression are omitted. There are exactly $k+1$
such sets, each of size $k$, and
$|T_i\cap T_j|=k-|i-j|$. For their uniform-reference Fisher matrix,

$$
G=d_n2^k K,\qquad K_{ij}=2^{-|i-j|},\qquad
G^{-1}=\frac{B}{3d_n2^k},
\tag{10.10}
$$

where the only nonzero entries of the symmetric matrix $B$ are

$$
B_{00}=B_{kk}=4,\qquad
B_{jj}=5\ (1\le j\le k-1),\qquad
B_{j,j+1}=B_{j+1,j}=-2\ (0\le j<k).
\tag{10.11}
$$

For $k=1$ there are two endpoint entries and no interior entry.

Proof. If $a_1<\cdots<a_k$ is legal, the compressed positions
$b_\ell=a_\ell-(\ell-1)$ form a $k$-element subset of $[k+1]$.
Exactly one position $j+1$ is missing. Before that gap $a_\ell=2\ell-1$;
after it $a_\ell=2\ell$, which gives (10.9). There cannot be $k+1$
occupied positions in a path of length $2k$, since they would need
at least $2k+1$ places. For $i\le j$, the common odd positions number
$i$ and the common even positions number $k-j$, proving the intersection
formula. Formula (10.8) now gives $G=d_n2^kK$.

The inverse is the classical Kac–Murdock–Szegö inverse specialized to
order $k+1$ and parameter $\rho=1/2$. In George Fikioris,
*Spectral properties of Kac-Murdock-Szegö matrices with a complex
parameter*, [Theorem 2.1(i)][KMS10], the matrix of order $m\ge2$ is
$K_m(\rho)=(\rho^{|a-b|})$, and for $\rho\ne\pm1$ its inverse has
endpoint diagonal $1$, interior diagonal $1+\rho^2$ and adjacent
entries $-\rho$, all divided by $1-\rho^2$. The correspondence is
$m=k+1$, $a=i+1$, $b=j+1$; multiplication by the external scale
$d_n2^k$ gives (10.10).

For completeness, the product at this parameter can be checked directly.
In the first column,
$(KB)_{i0}=4K_{i0}-2K_{i1}$ is $3$ at $i=0$ and zero for $i\ge1$;
the last column is symmetric. In an interior column $j$,

$$
(KB)_{ij}=-2K_{i,j-1}+5K_{ij}-2K_{i,j+1}.
\tag{10.12}
$$

At $i=j$ it equals $-1+5-1=3$. At $i<j$, factor
$2^{-(j-i)}$ to obtain $-4+5-1=0$; at $i>j$ the reflected
calculation gives zero. Thus $KB=3I_{k+1}$, including the two-column
case where only the endpoint calculation is present. $\square$

For $n=6$, $k=3$, $d_6=F_8=21$, the sets are
$246,146,136,135$, where each string lists occupied positions, and

$$
G=21\begin{pmatrix}
8&4&2&1\\4&8&4&2\\2&4&8&4\\1&2&4&8
\end{pmatrix},\qquad
G^{-1}=\frac1{504}\begin{pmatrix}
4&-2&0&0\\-2&5&-2&0\\0&-2&5&-2\\0&0&-2&4
\end{pmatrix}.
\tag{10.13}
$$

These values follow by substitution in (10.10). The chain index records
the location of the missing compressed position. Adjacency of these
indices is not adjacency of physical positions in the original path.

The odd case has a different top layer. On $n=2k+1$, $k\ge0$, a maximum
independent set has $k+1$ positions. Compression now sends it to a
$(k+1)$-element subset of $[k+1]$, so it is uniquely
$\{1,3,\ldots,2k+1\}$. Its uniform top-layer information is the scalar
$d_n2^{k+1}$. This includes $n=1$, whose information is $4$.
There is no even-style top chain on odd lengths; $n=0$ has no nonempty
target and is outside the selected-family assumptions.

### 10.4. Dual readouts and the minimum phase profile

**Theorem 10.4 (Matrix duality on the selected fiber).** Under Definition
10.1 set

$$
W=P^{-1}DG^{-1},\qquad h(I)=W_{I,\cdot}^{\mathsf T}.
\tag{10.14}
$$

Then

$$
D^{\mathsf T}W=I_r,\qquad
(p^0)^{\mathsf T}W=0,\qquad
W^{\mathsf T}PW=G^{-1},\qquad
\mathbb E_{p^\xi}h=\xi.
\tag{10.15}
$$

At the reference $\operatorname{Cov}_0h=G^{-1}$. Among all centered
linear readout matrices $\widetilde W$ satisfying
$\mathbb E_{p^\xi}\widetilde W_{I,\cdot}^{\mathsf T}=\xi$ for
every $\xi\in\mathcal U$, this covariance is minimal in Loewner order.
For any $\Phi\in\mathbb R^r$, the constraints

$$
D^{\mathsf T}\theta=\Phi,\qquad (p^0)^{\mathsf T}\theta=0
\tag{10.16}
$$

have the unique minimum-$P$-norm solution
$\theta=W\Phi$, with minimum squared norm $\Phi^{\mathsf T}G^{-1}\Phi$.

Proof. The first three equalities in (10.15) follow by multiplying
(10.14), using $D^{\mathsf T}P^{-1}D=G$ and $D^{\mathsf T}\mathbf1=0$.
For the fourth,
$W^{\mathsf T}(p^0+D\xi)=\xi$. Since $\mathcal U$ is an open
neighborhood of zero, an alternative readout has the stipulated mean
exactly when $(p^0)^{\mathsf T}\widetilde W=0$ and
$D^{\mathsf T}\widetilde W=I_r$. Write $\widetilde W=W+Z$.
Then $D^{\mathsf T}Z=0$, $(p^0)^{\mathsf T}Z=0$ and

$$
W^{\mathsf T}PZ=G^{-1}D^{\mathsf T}Z=0,\qquad
\operatorname{Cov}_0(\widetilde h)=G^{-1}+Z^{\mathsf T}PZ
\succeq G^{-1}.
\tag{10.17}
$$

Because $P>0$, equality of the covariance matrices forces $Z=0$.
For (10.16), $W\Phi$ is feasible. Every feasible $\theta$ can be written
$W\Phi+z$ with $D^{\mathsf T}z=0$ and $(p^0)^{\mathsf T}z=0$.
The same orthogonality gives

$$
\theta^{\mathsf T}P\theta
=\Phi^{\mathsf T}G^{-1}\Phi+z^{\mathsf T}Pz.
\tag{10.18}
$$

Strict positivity forces $z=0$ at the minimum. $\square$

The $P$-norm is the probability-weighted quadratic size of the phase
profile; (10.18) does not define physical energy. Off reference the exact
mean identity still holds, but the covariance is

$$
\operatorname{Cov}_{p^\xi}h
=W^{\mathsf T}\operatorname{diag}(p^\xi)W-\xi\xi^{\mathsf T},
\tag{10.19}
$$

which is not asserted to be constant. For $r=1$, with column $d_T$,
$G=I_T=\sum_{I\subseteq T}1/p^0_I$ and
$h(I)=d_T(I)/(p^0_I I_T)$. The $n=3,T=\{1,3\}$ instance is precisely
the fixed-fiber score and dual residual in Definition 9.7 and (9.42):
$\xi=\kappa-\kappa_0$, $I_T=I_0$, $W_I=d_I/(\bar p_I I_0)$.
The reference $p^0$ maps to that $\bar p$, with its occupancies fixed.
For several targets the inverse in (10.14) is the full inverse of $G$;
replacing it by independent diagonal reciprocals would violate
$D^{\mathsf T}W=I_r$ whenever $r>1$, by (10.7).

### 10.5. Neighboring relation labels in the dual top-chain readout

**Corollary 10.5 (Three-column formula for the dual).** For the uniform
even top chain of Theorem 10.3, writing $W_j$ for the $j$th column,
one has

$$
\begin{aligned}
W_0&=\frac{4d_{T_0}-2d_{T_1}}{3\,2^k},\\
W_j&=\frac{-2d_{T_{j-1}}+5d_{T_j}-2d_{T_{j+1}}}{3\,2^k},
 &&1\le j\le k-1,\\
W_k&=\frac{4d_{T_k}-2d_{T_{k-1}}}{3\,2^k}.
\end{aligned}
\tag{10.20}
$$

Proof. At the uniform law $P^{-1}=d_nI$. Therefore (10.14) and (10.10)
give $W=DB/(3\,2^k)$, whose columns are (10.20). For $k=1$ both
endpoint formulas apply and the interior range is empty. $\square$

The score matrix has no zero overlap entry, but inversion combines only
neighboring relation columns. These two statements concern different
matrices. The sparse formula in relation labels neither makes $h(I)$
a function of one path position nor supplies a sparse physical operation.

### 10.6. A chosen conjugate family with negative phases

**Definition 10.6 (Calibrated amplitude completion).** Supply the legal
Hilbert space with orthonormal basis $|I\rangle$, $I\in B_n$, and
introduce independent local real angle coordinates $\Phi\in\mathbb R^r$.
Keep the matrix $W$ fixed at the reference (10.14), and define

$$
|\psi(\xi,\Phi)\rangle
=\sum_{I\in B_n}\sqrt{p^0_I+(D\xi)_I}\,
 \exp[-i(W\Phi)_I]|I\rangle,\qquad \xi\in\mathcal U.
\tag{10.21}
$$

All geometric and information matrices below are at $(\xi,\Phi)=(0,0)$
unless explicitly stated otherwise. The amplitudes in (10.21) are
additional to the probability model. The phases use local real lifts;
no periodic identification of the chosen $W\Phi$ chart is assumed.

**Proposition 10.7 (Canonical form and reference tangent matrices).**
The actual relation angles in (10.21) are
$D^{\mathsf T}\theta=\Phi$. For the negative-phase normalization

$$
\lambda=\sum_Ip_I\,d\theta_I,\qquad
\Omega=-d\lambda=\sum_I d\theta_I\wedge dp_I,
\tag{10.22}
$$

the pullback on all of $\mathcal U$ times the local angle chart is
$\sum_{j=1}^r d\Phi_j\wedge d\xi_j$. At the reference, the columns of the
probability and phase derivative matrices are

$$
A=\tfrac12P^{-1/2}D,\qquad
C=-iP^{-1/2}DG^{-1}.
\tag{10.23}
$$

They are horizontal to $\psi_0=(\sqrt{p^0_I})_I$. Their Hermitian Gram
matrix and symmetric logarithmic derivative quantum Fisher matrix are

$$
\begin{pmatrix}
A^\dagger A&A^\dagger C\\C^\dagger A&C^\dagger C
\end{pmatrix}
=
\begin{pmatrix}
G/4&-iI_r/2\\iI_r/2&G^{-1}
\end{pmatrix},\qquad
H=4\operatorname{Re}
\begin{pmatrix}
A^\dagger A&A^\dagger C\\C^\dagger A&C^\dagger C
\end{pmatrix}
=
\begin{pmatrix}G&0\\0&4G^{-1}\end{pmatrix}.
\tag{10.24}
$$

Proof. Formula (10.15) gives $D^{\mathsf T}W\Phi=\Phi$.
Since $dp=D\,d\xi$ and $d\theta=W\,d\Phi$, substitution in (10.22)
gives the coefficient $W^{\mathsf T}D=I_r$ for the pullback.
This computation is valid throughout the positive chart and does not
differentiate $W$. At the reference, differentiation of square roots
and exponentials gives (10.23).
The inner products with $\psi_0$ are
$\tfrac12\mathbf1^{\mathsf T}D=0$ and
$-i\mathbf1^{\mathsf T}DG^{-1}=0$, respectively.
Multiplication gives all four Gram blocks in (10.24).
For a normalized pure state with horizontal derivatives $v_a$,
$\partial_a\rho=|v_a\rangle\langle\psi|+|\psi\rangle\langle v_a|$.
The symmetric logarithmic derivative
$2(|v_a\rangle\langle\psi|+|\psi\rangle\langle v_a|)$
therefore gives $H_{ab}=4\operatorname{Re}\langle v_a|v_b\rangle$,
which proves the last identity. $\square$

The sign and scale in (10.22) consume [Symplectic, Definition 35.12 and
Proposition 35.13][Symplectic10]: its $\Gamma_n$ is $B_n$, its $D_T$
is $d_T$, its moment $\mu_{T_j}$ is $\mu_{T_j}(p^0)+\xi_j$ and its
angle $\Phi_{T_j}$ is the actual $j$th component of $D^{\mathsf T}\theta$.
All other moments are fixed; other relation angles can vary as dictated
by the chosen lift $W\Phi$. The supplier uses $\exp(-i\theta_I)$ and
projective-line symplectic area $2\pi$, exactly the convention above.
Its full phase-torus coordinates are not identified with an arbitrary
globally periodic $W$ lift.

The pure-state tangent formalism is the one in Keiji Matsumoto,
*A new approach to the Cramer-Rao type bound of the pure state model*,
[§3, equations (7)–(16), and Theorem 5][Matsumoto10].
His horizontal SLD lifts $l_a$ map here to twice the columns of
$(A,C)$; his $J^S=\operatorname{Re}L^\dagger L$ maps to $H$.
The purely imaginary cross block is relevant to joint estimation;
it is not a cross block of classical Fisher information for every
measurement. Inverting $H$ uses the full matrices $G^{-1}$ and $G/4$,
rather than reciprocals of their separate diagonal entries.

### 10.7. A directional matrix budget for arbitrary joint measurements

**Theorem 10.8 (Conjugate Fisher budget on independent pure copies).**
Take $N\ge1$ identical independent copies of (10.21), and any fixed,
parameter-independent positive operator-valued measure (POVM) on their
full product Hilbert space. At the reference let $F$ be its regular
classical Fisher matrix, partitioned by $(\xi,\Phi)$. Then

$$
F_{\xi\xi}+\tfrac14G F_{\Phi\Phi}G\preceq NG.
\tag{10.25}
$$

This includes collective measurements. The reference-score convention
uses only outcomes of positive reference density. For subsequent
estimator inequalities assume square-integrable scores and valid
differentiation under both likelihood and estimator integrals.

Proof. For each real $v\in\mathbb R^r$ consider the two directions
$\delta\xi=v$ and $\delta\Phi=Gv/2$. Their one-copy horizontal tangents
are, by (10.23),

$$
a=Av=\tfrac12P^{-1/2}Dv,\qquad
b=C(Gv/2)=-ia,\qquad
4\|a\|^2=v^{\mathsf T}Gv.
\tag{10.26}
$$

For one positive effect $M$, put
$q=\langle\psi_0|M|\psi_0\rangle$ and
$z=\langle\psi_0|M|a\rangle$. The two directional probability
derivatives are $2\operatorname{Re}z$ and $2\operatorname{Im}z$;
the second sign uses $\operatorname{Re}(-iz)=\operatorname{Im}z$.
Cauchy–Schwarz for $M^{1/2}$ gives

$$
|z|^2\le q\,\langle a|M|a\rangle.
\tag{10.27}
$$

On $q>0$, the sum of the two directional Fisher contributions is
$4|z|^2/q\le4\langle a|M|a\rangle$. Summing effects gives
$4\|a\|^2$. No assumption about other tangent directions was used.

For $N$ copies write $\Psi=\psi_0^{\otimes N}$ and

$$
a_N=\sum_{\nu=1}^N
 \psi_0^{\otimes(\nu-1)}\otimes a\otimes
 \psi_0^{\otimes(N-\nu)},\qquad b_N=-ia_N.
\tag{10.28}
$$

Different summands are orthogonal because
$\langle\psi_0|a\rangle=0$. Hence
$\langle\Psi|a_N\rangle=0$ and $\|a_N\|^2=N\|a\|^2$.
Product differentiation gives exactly these tangents.
Apply (10.27) with $\Psi,a_N$ to an arbitrary joint effect, without
factoring that effect into one-copy effects. Summation yields

$$
v^{\mathsf T}F_{\xi\xi}v+
(Gv/2)^{\mathsf T}F_{\Phi\Phi}(Gv/2)
\le4\|a_N\|^2=Nv^{\mathsf T}Gv.
\tag{10.29}
$$

Since this holds for all real $v$, it is (10.25).

For a general measurable outcome space, use the finite control measure
$\nu(E)=\operatorname{Tr}M(E)$ on the product space of dimension $d_n^N$.
Every matrix entry of $M$ is dominated by $\nu$; its Radon–Nikodym
densities form a positive matrix $m(y)$ almost everywhere, satisfying
$\int m(y)\,d\nu(y)=I$. Positivity follows by testing a countable dense
set of vectors, and the normalization follows entrywise. Put
$q(y)=\langle\Psi|m(y)|\Psi\rangle$ and
$z(y)=\langle\Psi|m(y)|a_N\rangle$. Finite-dimensional smooth state
derivatives give the displayed first-derivative formulas under the
integral; the trace density supplies an integrable bound.
Inequality (10.27) holds almost everywhere and gives integrability of
the score squares. The Fisher entries are

$$
F_{\alpha\beta}=
\int_{\{q>0\}}
\frac{(\partial_\alpha q)(\partial_\beta q)}q\,d\nu.
\tag{10.30}
$$

At $q=0$, positivity gives $m(y)^{1/2}\Psi=0$, so $z=0$ and both
first derivatives vanish. These outcomes have no reference-score
contribution. Integration of (10.27) proves (10.29) again.
Probabilities emerging to second order do not receive a
direction-dependent limiting Fisher value in (10.30). $\square$

The cross blocks $F_{\xi\Phi}$ can be nonzero; (10.25) does not discard
or set them to zero. Richard D. Gill and Serge Massar,
*State estimation for large ensembles*, [Theorem I, equation (27),
and §V.A–B][GM10], give pure-state information tradeoffs and
product-copy tangent methods. Their ambient-dimension bound is
$\operatorname{tr}(H^{-1}F)\le N(d_n-1)$ here. It is not the directional
matrix assertion (10.25). The proof above supplies the actual relation
$b_N=-ia_N$ for each $v$ in this model and never substitutes an ambient
dimension of two or an unproved restriction of the joint POVM.
The corresponding claim for collective measurements on mixed inputs
does not follow from this argument.

### 10.8. The weighted joint estimation cost

**Theorem 10.9 (Full-gradient local joint error).** Suppose a regular
measurement as in Theorem 10.8 admits finite-covariance estimators
$\widehat\xi,\widehat\Phi$ with reference means zero and full local
expectation Jacobian $I_{2r}$ in the family (10.21). In particular, each
estimate has zero expectation derivative in the other parameter block.
Let their reference marginal covariance blocks be $\Sigma_\xi$ and
$\Sigma_\Phi$. Then

$$
\operatorname{Tr}(G\Sigma_\xi)
+4\operatorname{Tr}(G^{-1}\Sigma_\Phi)\ge\frac{4r}{N}.
\tag{10.31}
$$

Proof. Use positive symmetric square roots of $G$ and standardize by

$$
u=G^{1/2}\xi,\qquad v=2G^{-1/2}\Phi.
\tag{10.32}
$$

The corresponding estimates retain the full identity Jacobian.
The transformed Fisher blocks are
$F_{uu}=G^{-1/2}F_{\xi\xi}G^{-1/2}$ and
$F_{vv}=\tfrac14G^{1/2}F_{\Phi\Phi}G^{1/2}$.
Thus (10.25) becomes $F_{uu}+F_{vv}\preceq NI_r$.
For each coordinate $j$, the scalar score identity and Cauchy–Schwarz
give

$$
1=\mathbb E_0[\widehat u_j S_{u_j}],\qquad
\operatorname{Var}_0\widehat u_j\ge\frac1{(F_{uu})_{jj}},
\qquad
\operatorname{Var}_0\widehat v_j\ge\frac1{(F_{vv})_{jj}}.
\tag{10.33}
$$

Here the scores are those of the whole $N$-copy outcome law, so its
$F$ already includes the sample count. A zero denominator makes
the score zero almost surely and contradicts the identity with one;
then joint local estimability with finite covariance is impossible.
When both are positive, writing $a=(F_{uu})_{jj}$,
$b=(F_{vv})_{jj}$ gives
$a+b\le N$ and $1/a+1/b\ge4/(a+b)\ge4/N$.
Sum over $j$ and use
$\operatorname{Cov}\widehat u=G^{1/2}\Sigma_\xi G^{1/2}$,
$\operatorname{Cov}\widehat v=4G^{-1/2}\Sigma_\Phi G^{-1/2}$
to obtain (10.31). $\square$

Only marginal variances enter this trace, but neither classical
cross Fisher blocks nor cross covariance blocks have been assumed zero
in the proof. The weights specify a dimensionless total error in these
coordinates; they do not assert a universal physical uncertainty
normalization for arbitrary choices of relation units.

### 10.9. Calibrated global readout and exact finite-sample attainment

**Proposition 10.10 (Two full-mode settings).** At the supplied reference,
setting $A$ measures the basis $|I\rangle$. Introduce, as an additional
global calibrated operation,

$$
\Pi_0=|\psi_0\rangle\langle\psi_0|,\qquad
U_\star=\Pi_0+i(I-\Pi_0).
\tag{10.34}
$$

Setting $B$ first applies $U_\star$ and then measures the same full-mode
basis. Its availability is an extra measurement assumption. The
one-copy information matrices, in the order $(\xi,\Phi)$, are

$$
F_A=\begin{pmatrix}G&0\\0&0\end{pmatrix},\qquad
F_B=\begin{pmatrix}0&0\\0&4G^{-1}\end{pmatrix}.
\tag{10.35}
$$

Proof. The orthogonal projectors $\Pi_0,I-\Pi_0$ sum to the identity,
so $U_\star^\dagger U_\star=I$.
It fixes $\psi_0$ and multiplies every horizontal vector by $i$.
In setting $A$ the probabilities are $p^\xi_I$, independent of $\Phi$,
and (10.6) gives scores $(s(I),0)$.
For setting $B$, at the reference,
$U_\star A=iA$ and $U_\star C=P^{-1/2}DG^{-1}$.
The first derivative of a Born probability in a direction $x$ is
$2\operatorname{Re}(\sqrt{p^0_I}\,x_I)$.
Therefore its probability derivatives are zero in $\xi$ and
$2(DG^{-1})_{I,\cdot}$ in $\Phi$.
The resulting score is $(0,2h(I))$, with covariance
$\operatorname{diag}(0,4G^{-1})$ by (10.15). All reference probabilities
are $p^0_I>0$, so the two likelihoods are regular there. $\square$

Both settings read all their respective target directions
simultaneously. In particular the phase block is $4G^{-1}$, with its
full correlations. Formula (10.34) specifies a unitary on the entire
legal space; it is not identified with a single site operation of
Definition 9.1 or assigned a depth in that menu.

**Theorem 10.11 (Recorded random settings attain the matrix cost).**
For any real $0<t<1$ and any integer $N\ge1$, independently choose
setting $A$ with probability $t$ on each copy and otherwise choose $B$;
record both the setting and the complete mode. Then

$$
F_t=N\begin{pmatrix}tG&0\\0&4(1-t)G^{-1}\end{pmatrix}
\tag{10.36}
$$

is the exact reference Fisher matrix. The fixed-reference estimates

$$
\widehat\xi=\frac{G^{-1}}{Nt}\sum_{\nu:A_\nu}s(I_\nu),\qquad
\widehat\Phi=\frac{G}{4N(1-t)}\sum_{\nu:B_\nu}2h(I_\nu)
\tag{10.37}
$$

have full local Jacobian $I_{2r}$, zero reference means, and

$$
\Sigma_\xi=\frac{G^{-1}}{Nt},\qquad
\Sigma_\Phi=\frac{G}{4N(1-t)},\qquad
\operatorname{Cov}_0(\widehat\xi,\widehat\Phi)=0.
\tag{10.38}
$$

At $t=1/2$, (10.31) is attained for every $N\ge1$.

Proof. The observed-setting likelihood is $tq_A(I)$ or
$(1-t)q_B(I)$; $t$ is parameter independent. Its scores are exactly
the two block vectors in the proof of Proposition 10.10. Their means
are zero and their covariance is the one-copy version of (10.36).
Independence multiplies it by $N$. If $S_N$ is the joint vector score
evaluated at the reference, (10.37) is $F_t^{-1}S_N$.
Differentiating the sampling law while holding this statistic fixed
gives expectation Jacobian $F_t^{-1}F_t=I_{2r}$.
Its covariance is $F_t^{-1}F_tF_t^{-1}=F_t^{-1}$, proving (10.38).
Equivalently, each one-copy product of an $A$ contribution and a $B$
contribution is zero, and contributions from different copies have
zero cross expectation by independence. This explains the vanishing
cross covariance for this particular construction.
The weighted trace equals
$r/[Nt]+r/[N(1-t)]$, whose minimum is $4r/N$ at $t=1/2$. $\square$

The denominators in (10.37) use the fixed design probabilities and
total $N$. They never divide by the observed random setting counts.
Empty sums are zero. The events with no $A$ observations or no $B$
observations, of probabilities $(1-t)^N$ and $t^N$, are included in the
expectations above, so the assertion includes $N=1$.

For a deterministic schedule with $m$ copies assigned to $A$,
$1\le m\le N-1$, the independent score calculation instead gives

$$
F_{\rm det}=\operatorname{diag}(mG,4(N-m)G^{-1}),\qquad
\widehat\xi=\frac{G^{-1}}m\sum_A s,\quad
\widehat\Phi=\frac{G}{4(N-m)}\sum_B2h.
\tag{10.39}
$$

It attains (10.38) only with $t=m/N$. Balanced deterministic allocation
requires even $N$, and $N=1$ has no deterministic two-setting allocation.
At $t=0$ or $t=1$ one entire score block vanishes, precluding joint
local unbiasedness with finite covariance.

The two-basis method has its primary precedent in Nan Li, Christopher
Ferrie, Jonathan A. Gross, Amir Kalev and Carlton M. Caves,
*Fisher-symmetric informationally complete measurements for pure
states*, [equation (18) and Supplemental Material §II,
(A.10)–(A.13)][FisherSymmetric10]. Their dimension is $d=d_n$ and
their fiducial $|0\rangle$ is $\psi_0$. Choose a real orthonormal
completion of $\psi_0$; the original mode basis has strictly positive
fiducial overlaps $\sqrt{p^0_I}$. Their two bases differ by a quarter
turn of the fiducial component, equivalently a relative quarter turn
of the orthogonal complement as in (10.34). Their setting probabilities
$p_\chi,p_\tau$ map to $t,1-t$. Conjugating the imaginary-coordinate
convention accounts for the negative phases here and leaves Fisher
information unchanged. Their full pure-state tangent dimension is
$2d_n-2$; our $2r$ directions form the specified subspace (10.23).
The score computation and fixed-reference statistics above establish
the exact finite-$N$ application, including its recorded random design.

### 10.10. The separate full-phase nuisance task

**Definition 10.12 (All mode phases unknown).** Fix a positive calibrated
law $p$ on all $B_n$ and put $P=\operatorname{diag}p$,
$G=D^{\mathsf T}P^{-1}D$. In this section and §§10.11–10.13 the state is

$$
|\psi_\theta\rangle=\sum_I\sqrt{p_I}e^{-i\theta_I}|I\rangle,\qquad
\Phi(\theta)=D^{\mathsf T}\theta,
\tag{10.40}
$$

where every mode phase may vary in a local real chart. The reference is
the supplied same-phase point $\theta=0$ for the site menu. A target
estimator has mean zero there and the full expectation derivative

$$
\left.\frac{\partial}{\partial\theta}
\mathbb E_\theta\widehat\Phi\right|_0=D^{\mathsf T}.
\tag{10.41}
$$

This is a task with all phase nuisance directions; its phase vector is
not restricted to $W\Phi$. The common phase is immaterial because
$D^{\mathsf T}\mathbf1=0$. The probability law is fixed; no probability
nuisance gradient is part of (10.41).

The recorded site menu is exactly Definition 9.1 and Proposition 9.2,
with the same legal matching pairs, blocked outcomes, negative phases
and calibrated quadrature basis. For fixed probabilities
$\eta_i\ge0$, $\sum_i\eta_i=1$, its one-copy information is

$$
J_\eta=4L_\eta,\qquad
L_\eta=\sum_i\eta_iL_i,\qquad
L_i=\sum_{\substack{e=(u,v)\\\text{legal site-}i\text{ pair}}}
\frac{p_up_v}{p_u+p_v}(e_u-e_v)(e_u-e_v)^{\mathsf T}.
\tag{10.42}
$$

The correspondences to (9.4)–(9.7) are identity maps for $p,\theta,\eta$,
the complete record $(i,e,\pm)$ or $(i,w,\mathrm{blocked})$, and sample
count $N$. No new outcome erasure or instrument is introduced.

**Theorem 10.13 (Quantum target matrix with all phase nuisances).**
For a regular fixed POVM on $N$ identical independent copies of
(10.40), every estimator satisfying (10.41) with finite covariance obeys

$$
\operatorname{Cov}_0\widehat\Phi\succeq\frac{G}{4N}.
\tag{10.43}
$$

The same bound holds at any supplied phase reference, with the target
and its local gradient evaluated there. If the global calibrated
setting (10.34) is allowed, it attains the whole matrix (10.43) at the
same-phase reference under the full nuisance condition (10.41).

Proof. Let $a\in\mathbb R^r$ be nonzero and set
$\ell=Da$, $f=P^{-1}\ell$, $A_\ell=\ell^{\mathsf T}P^{-1}\ell$.
Then $\sum_Ip_If_I=\sum_I\ell_I=0$ and
$\sum_Ip_If_I^2=A_\ell=a^{\mathsf T}Ga>0$.
On the actual subpath $\theta=tf$,
$a^{\mathsf T}\Phi(\theta)=tA_\ell$.
The horizontal state derivative is $-i\sqrt p\,f$, with squared
norm $A_\ell$. On $N$ copies the squared norm is $NA_\ell$ by
the orthogonality of distinct differentiated factors.
For any effect, the derivative has the form
$2\operatorname{Re}\langle\Psi|M|\dot\Psi\rangle$.
Inequality (10.27), with $\dot\Psi$ in place of $a_N$, bounds the
scalar Fisher information by $4NA_\ell$, also for continuous
outcomes by (10.30). Full local unbiasedness gives derivative
$A_\ell$ for $a^{\mathsf T}\widehat\Phi$ along this subpath.
The scalar score identity yields

$$
a^{\mathsf T}\operatorname{Cov}_0(\widehat\Phi)a
\ge\frac{A_\ell^2}{4NA_\ell}
=\frac{a^{\mathsf T}Ga}{4N}.
\tag{10.44}
$$

If that scalar information is zero, its required nonzero derivative
is impossible. The case $a=0$ is immediate. This proves (10.43)
in every real direction. At another supplied phase reference the
diagonal phase factors do not change the derivative norm or this proof.
This is also the exact scalar application of Theorem 9.10 with its
contrast $\ell=Da$, not only with individual columns $d_T$.

To verify simultaneous attainment in the larger nuisance model,
use $\psi_0=\sqrt p$ in (10.34). In an arbitrary phase direction $g$,
write $c=p^{\mathsf T}g$. The state derivative decomposes as
$-ic\psi_0-i\sqrt p\,(g-c\mathbf1)$.
After $U_\star$ it is
$-ic\psi_0+\sqrt p\,(g-c\mathbf1)$, so the mode score in that
direction is $2(g_I-c)$. Thus the full phase score vector at outcome
$I$ is $2(e_I-p)$. Use the statistic

$$
X(I)=\frac{D_{I,\cdot}^{\mathsf T}}{2p_I},\qquad
\widehat\Phi=\frac1N\sum_{\nu=1}^N X(I_\nu).
\tag{10.45}
$$

Its mean is $D^{\mathsf T}\mathbf1/2=0$ and its one-copy
covariance is $G/4$. Its full expectation Jacobian is

$$
\sum_Ip_I\,\frac{D_{I,\cdot}^{\mathsf T}}{2p_I}
\,2(e_I-p)^{\mathsf T}
=D^{\mathsf T}-D^{\mathsf T}\mathbf1\,p^{\mathsf T}
=D^{\mathsf T}.
\tag{10.46}
$$

Independence proves the asserted covariance and all nuisance
derivatives. At a different supplied reference, a fixed diagonal
calibration reduces to the same calculation. $\square$

When $p=p^0$, restriction of (10.41) to $\theta=W\Phi$ gives
Jacobian $D^{\mathsf T}W=I_r$, and (10.45) becomes the phase-only
instance of (10.37). Conversely, an identity Jacobian only along
$W\Phi$ does not imply (10.41); the larger task needs (10.46).
This explains why the two tasks have the same optimal covariance
value without equating their nuisance spaces.

### 10.11. Exactly which site budgets attain one relation benchmark

**Theorem 10.14 (Single-target support criterion).** In the full-phase
task of Definition 10.12, fix a nonempty legal $T$ and write

$$
f_T=P^{-1}d_T,\qquad I_T=d_T^{\mathsf T}P^{-1}d_T
=\sum_{I\subseteq T}p_I^{-1}.
\tag{10.47}
$$

For the recorded site menu (10.42), its quantum target value
$I_T/(4N)$ is attainable with the full phase gradient $d_T$ if and
only if $\operatorname{supp}\eta\subseteq T$.
In that case $L_\eta f_T=d_T$ and $R_\eta(d_T)=I_T$.
If any positive budget lies outside $T$, every finite-variance
full-gradient estimator, when one exists, has variance strictly
larger than $I_T/(4N)$. Failure of component balance means no such
estimator exists.

Proof. The vector $f=f_T$ has $p$-mean zero and
$p$-variance $I_T$. For $i\in T$, every $J\subseteq T\setminus\{i\}$
is paired legally with $J\cup\{i\}$, since $T$ is independent.
Their coefficients in $d_T$ are opposite. If $d_T(u)=a$ and
$d_T(v)=-a$ on such a pair, its Laplacian contribution at $u$ is

$$
\frac{p_up_v}{p_u+p_v}
\left(\frac a{p_u}+\frac a{p_v}\right)=a.
\tag{10.48}
$$

The contribution at $v$ is $-a$. Every other site-$i$ pair has both
coefficients zero, and no supported word is blocked at $i$.
Therefore $L_if=d_T$ on all vertices, including all zero-coefficient
and blocked vertices. When $\operatorname{supp}\eta\subseteq T$,
summing gives $L_\eta f=d_T$.
Thus $d_T$ is in the image of $L_\eta$, equivalently it is balanced
on every positive-edge component. Moreover
$L_\eta^+d_T$ differs from $f$ by a vector in $\ker L_\eta$.
Pairing that difference with $d_T$ gives zero, so

$$
d_T^{\mathsf T}L_\eta^+d_T=d_T^{\mathsf T}f=I_T.
\tag{10.49}
$$

Theorem 9.4, with its $\ell=d_T$ and the same $p,\eta,N$, gives
the full-gradient reference-score estimator and variance $I_T/(4N)$.
This extends the one-site sufficient construction of Theorem 9.13
to all budgets supported in $T$.

For necessity, let $\mathcal E_i$ be the partition that retains all
bits except bit $i$ in this finite experiment. Its fibers are exactly
the legal site-$i$ pairs and blocked singletons. The conditional
variance identity underlying Proposition 8.13 becomes

$$
f^{\mathsf T}L_if
=\mathbb E_p\operatorname{Var}(f\mid\mathcal E_i)
=I_T-\mathbb E_p\bigl(\mathbb E_p[f\mid\mathcal E_i]\bigr)^2.
\tag{10.50}
$$

Indeed, on a pair of masses $a,b$, its contribution is
$ab(f_u-f_v)^2/(a+b)$, and on a singleton it is zero; summing
gives the first equality. The second follows from $\mathbb E_pf=0$.
For $i\in T$, the conditional mean on every fiber is zero by opposite
coefficients, in agreement with (10.48). For $i\notin T$, each
fiber contains at most one subset of $T$. In particular the fiber
with all other bits zero is the legal pair
$\{\varnothing,\{i\}\}$, and its conditional mean is

$$
\frac{p_\varnothing f(\varnothing)+p_{\{i\}}f(\{i\})}
{p_\varnothing+p_{\{i\}}}
=\frac{(-1)^{|T|}}{p_\varnothing+p_{\{i\}}}\ne0.
\tag{10.51}
$$

Its probability is strictly positive. Thus the conditional-mean
square in (10.50) is strictly positive. More generally any blocked
singleton carrying a nonzero coefficient would also contribute to
that square; blocked modes cannot be dropped. Consequently
$f^{\mathsf T}L_if<I_T$ for every $i\notin T$, whereas
$f^{\mathsf T}L_if\le I_T$ for all sites. Any positive outside
budget therefore gives $Q_\eta:=f^{\mathsf T}L_\eta f<I_T$.

On the admissible subpath $\theta=tf$, the target derivative is $I_T$
and the menu Fisher information on $N$ copies is $4NQ_\eta$.
If $Q_\eta>0$, the scalar score inequality forces

$$
\operatorname{Var}_0\widehat\Phi_T
\ge\frac{I_T^2}{4NQ_\eta}>\frac{I_T}{4N}.
\tag{10.52}
$$

If $Q_\eta=0$, its zero score contradicts the required derivative
$I_T>0$. Separately, if the target is unbalanced on a positive-edge
component, the likelihood invariance in Theorem 9.4 excludes a
full-gradient estimator, even if $Q_\eta>0$.
These alternatives exhaust the cases and prove necessity. $\square$

Both strict positivity on every legal word and $T\ne\varnothing$
are used: the former makes (10.51) a positive-probability obstruction,
and the latter makes $d_T$ a nonzero contrast of total mass zero.
The zero-budget sites supply no events. A pseudoinverse number for
an unbalanced target is not a finite attainable resistance.

### 10.12. The common-port criterion for a family of targets

**Theorem 10.15 (Simultaneous optimum if and only if a common site
exists).** For the distinct nonempty targets $T_1,\ldots,T_r$ and a
fixed recorded site budget $\eta$, the full-phase task admits a
locally unbiased vector estimator with

$$
\operatorname{Cov}_0\widehat\Phi=\frac{G}{4N}
\tag{10.53}
$$

if and only if

$$
\operatorname{supp}\eta\subseteq\bigcap_{j=1}^rT_j.
\tag{10.54}
$$

In particular some site budget attains (10.53) if and only if that
intersection is nonempty.

Proof. Equality of the covariance matrices implies, on every
diagonal, $\operatorname{Var}_0\widehat\Phi_j=G_{jj}/(4N)
=I_{T_j}/(4N)$. Condition (10.41) supplies each full target gradient.
Theorem 10.14 forces $\operatorname{supp}\eta\subseteq T_j$ for
each $j$, proving necessity.

Conversely assume (10.54). Formula (10.48) holds columnwise for every
site in the budget, hence

$$
L_\eta P^{-1}D=D.
\tag{10.55}
$$

All columns are therefore in $\operatorname{im}L_\eta$ and are balanced
on every component, including isolated vertices.
Let $J_\eta=4L_\eta$ and use the exact reference score $s_\theta(Y)$
of (9.5) on the complete one-copy record. Define

$$
\widehat\Phi=\frac1N\sum_{\nu=1}^N
D^{\mathsf T}J_\eta^+s_\theta(Y_\nu).
\tag{10.56}
$$

Its mean is zero and its full expectation Jacobian is
$D^{\mathsf T}J_\eta^+J_\eta=D^{\mathsf T}$, since each column
of $D$ is in the image. The difference
$P^{-1}D-L_\eta^+D$ has columns in $\ker L_\eta$ by (10.55).
Pairing with $D$ removes those columns, so

$$
D^{\mathsf T}L_\eta^+D=D^{\mathsf T}P^{-1}D=G.
\tag{10.57}
$$

Using $\mathbb E_0s_\theta s_\theta^{\mathsf T}=J_\eta$ and
independence, (10.56) has covariance
$D^{\mathsf T}J_\eta^+D/N=G/(4N)$. This is the matrix version of
the same reference-score estimator in Theorem 9.4, with every nuisance
derivative checked. Finally a probability budget has nonempty support.
Such a support can lie in the intersection exactly when the intersection
contains a site, in which case all budget may be placed there. $\square$

The off-diagonal entries of $G$ remain present in (10.53);
simultaneous attainment does not make the target errors independent.
An empty common intersection is a restriction of this recorded site
menu. It is not an intrinsic incompatibility of the phase targets under
all quantum measurements: Theorem 10.13 supplies their simultaneous
full-gradient optimum under the additional global setting.

### 10.13. A quantitative loss for the two alternating highest targets

**Theorem 10.16 (Alternating-target obstruction and efficiency).**
Let $n=2k$, $k\ge1$, with uniform $p_I=1/d_n$, and retain the two
alternating maximum sets
$T_0=\{2,4,\ldots,2k\}$ and $T_k=\{1,3,\ldots,2k-1\}$.
They are disjoint, so no site budget attains the two quantum target
variances simultaneously, and hence none attains the whole $k+1$-target
maximum-set chain simultaneously. Put $I_\star=d_n2^k$ and
$f_T=P^{-1}d_T$ for either target. Define

$$
\epsilon_i(T)=\frac{f_T^{\mathsf T}L_if_T}{I_\star},\qquad
\epsilon_\eta(T)=\sum_i\eta_i\epsilon_i(T).
\tag{10.58}
$$

Then

$$
\epsilon_i(T)=
\begin{cases}
1,&i\in T,\\
1/4,&i\notin T,\ i\in\{1,2k\},\\
1/8,&i\notin T,\ 1<i<2k.
\end{cases}
\tag{10.59}
$$

The last case has an empty range when $k=1$.
Every budget obeys
$\epsilon_\eta(T_0)+\epsilon_\eta(T_k)\le5/4$.
If both targets have finite-variance full-gradient estimators in
the same menu experiment, at least one satisfies

$$
\operatorname{Var}_0\widehat\Phi_T
\ge\frac85\,\frac{I_\star}{4N}.
\tag{10.60}
$$

If either target fails component balance, it has no such estimator;
its extended target resistance is infinite.

Proof. Disjointness and Theorem 10.15 prove the first assertion.
Each $f_T$ equals $d_n d_T$, and
$d_T^{\mathsf T}P^{-1}d_T=d_n2^k=I_\star$.
For $i\in T$, Theorem 10.14 gives
$f_T^{\mathsf T}L_if_T=I_\star$.
For $i\notin T$, let $b$ be the number of neighbors of $i$ lying in $T$.
An edge with exactly one supported endpoint has that endpoint
$J\subseteq T$, with all $b$ neighbors omitted, and its other endpoint
is $J\cup\{i\}$. These are all legal and are all the nonzero
energy-contributing site-$i$ edges. There are $2^{k-b}$ choices of $J$.
On each edge the conductance is $1/(2d_n)$ and the potential difference
has squared magnitude $d_n^2$, contributing $d_n/2$.
All other pairs have both potentials zero. A supported but blocked
word has no edge contribution at this site. Hence

$$
f_T^{\mathsf T}L_if_T
=\frac{d_n}{2}\,2^{k-b},\qquad
\epsilon_i(T)=2^{-b-1}.
\tag{10.61}
$$

For an alternating target, an outside endpoint has $b=1$ and an
outside interior site has $b=2$. This proves (10.59), including
$n=2$, which has only endpoints.

Every site belongs to exactly one of $T_0,T_k$. Thus the sum of
its two efficiencies is $1+1/4=5/4$ at an endpoint, and
$1+1/8=9/8$ in the interior. Averaging with $\eta$ proves the
sum bound; consequently at least one of the two efficiencies is
at most $5/8$. Along that target's actual subpath $\theta=tf_T$
the derivative of $\Phi_T$ is $I_\star$, and its Fisher information
is $4NI_\star\epsilon_\eta(T)$. Applying the scalar score inequality
gives

$$
\operatorname{Var}_0\widehat\Phi_T
\ge\frac{I_\star}{4N\epsilon_\eta(T)}
\ge\frac85\,\frac{I_\star}{4N}.
\tag{10.62}
$$

This argument applies to every estimator with the full target gradient
when it exists. When a component is unbalanced, the component-shift
invariance of the observed likelihood gives nonexistence instead,
as specified in Theorem 9.4. $\square$

**Corollary 10.17 (Six-position values and the limitation of a ray
calculation).** For $n=6$, the two alternating targets each have
$I_\star=21\cdot8=168$ and individual quantum variance $42/N$.
For every site budget, either a target is not fully locally estimable,
or at least one of the two variances is at least $336/(5N)$.
Assigning equal budget to the two endpoint sites makes both efficiencies
in (10.58) equal to $5/8$, but it does not in general attain the
full-nuisance variance bound.

Proof. The numerical values are the substitutions
$I_\star/(4N)=168/(4N)$ and
$(8/5)\,42/N=336/(5N)$ in Theorem 10.16.
With $\eta_1=\eta_{2k}=1/2$, each alternating target receives efficiency
one from its own endpoint and $1/4$ from the opposite endpoint,
so its mean efficiency is $5/8$.

For every supported $J\subseteq T_0$, the right endpoint $2k$ is
always unblocked, belongs to the budget, and reverses $d_{T_0}$
when toggled. It pairs the source coefficients within each component,
so $T_0$ is balanced; the left endpoint gives the analogous pairing
for $T_k$. Both targets are therefore estimable in this budget.
Nevertheless equality in the scalar subpath bound would require
the reference estimate to be proportional to the subpath score.
For target $T_0$, that statistic has full gradient proportional to
$L_\eta f_{T_0}$. Its proportionality could be the required
$d_{T_0}$ only if $L_\eta f_{T_0}$ were a scalar multiple of $d_{T_0}$.
At the unsupported singleton $\{1\}$, the site-$1$ edge to
$\varnothing$ contributes
$-\tfrac14d_{T_0}(\varnothing)\ne0$ to $L_\eta f_{T_0}$,
whereas the site-$2k$ contribution is zero there.
Thus this vector is not proportional to $d_{T_0}$.
Reflection proves the same for $T_k$, including $k=1$.
Consequently the endpoint efficiency equality alone does not supply
equality in (10.62) under the full gradient condition. $\square$

The constant in (10.60) is a proved lower factor for this one-site
recorded menu. No exact minimax allocation or optimal full-nuisance
value is inferred from it. Sequential multi-operation experiments
have a different likelihood and are outside this menu bound.

### 10.14. Supplier correspondence and primary mathematical attributions

**Convention 10.18 (Scope of the mathematical applications).** The
preceding results use the following exact correspondences. Existing
inverse transforms, scalar target bounds and classical matrix structures
retain their indicated sources; the relation-specific conclusions are
the combinations proved above.

| Source | Objects and hypotheses used here | Consequence and limit |
| --- | --- | --- |
| [Correlation §23.2][Correlation10] | $\Gamma_n=B_n$, $D_{T'}=d_T$, $\mu_{T'}=\mu_T$, all legal subsets including $\varnothing$; its named HiddenRelations C-28 suppliers give the complete inverse. | (10.2)–(10.5), independent columns and the legal-set count; no phase experiment follows from this classical inverse. |
| [Symplectic §35.13][Symplectic10] | $\psi_I=\sqrt{p_I}e^{-i\theta_I}$, $\mu_{T_j}=\mu^0_{T_j}+\xi_j$, $\Phi_{T_j}=d_{T_j}^{\mathsf T}\theta$; positive chart and symplectic area $2\pi$. | The sign and scale in (10.22), restricted by $\theta=W\Phi$; the supplier's complete torus is distinct from this local chosen lift. |
| This volume, Definition 9.7, (9.42) and Definition 9.14 | $n=3$, $T=\{1,3\}$, $(\varnothing,1,2,3,13)$, $d=(1,-1,0,-1,1)$, $\xi=\kappa-\kappa_0$, $p^0=\bar p$, $G=I_0$, $W_I=d_I/(\bar p_I I_0)$, $\Phi=\chi$. | The existing fixed-fiber score, residual and negative-phase conjugate model are the scalar instance of (10.14) and (10.21). Several targets require $G^{-1}$. |
| This volume, Proposition 8.13, Definition 9.1, Proposition 9.2 and Theorem 9.4 | Same full positive $p$, site-$i$ legal fibers, resolved signs and blocked modes, fixed recorded $\eta$, full nuisance gradient, same iid count $N$. | $J_\eta=4L_\eta$, the conditional-variance identity, component balance and exact reference-score saturation used in (10.49) and (10.56); no erased record is substituted. |
| This volume, Theorems 9.10 and 9.13 | Scalar contrast $\ell=Da$ for arbitrary real $a$, or $\ell=d_T$ for a single nonempty target; regular POVMs on independent pure copies. | (10.44) consumes the arbitrary-contrast bound; the one-site sufficiency is extended to the support iff and common-port iff, keeping all phase nuisance directions. |
| Fikioris, [Theorem 2.1(i)][KMS10] | Matrix order $m=k+1\ge2$, $\rho=1/2$, external scale $d_n2^k$. | The classical tridiagonal inverse in (10.10); its indices label maximum relations, not the sites of the legal path. |
| Matsumoto, [§3 and Theorem 5][Matsumoto10] | Smooth local pure model, SLD lifts $l_a=2\partial_a\psi$ at the horizontal reference, $J^S=H$; full model parameters number $2r$. | Pure tangent/QFI and imaginary-Gram compatibility background. Phase-only derivatives have real Gram; the probability–phase family has the imaginary cross block (10.24). |
| Gill–Massar, [Theorem I and §V.A–B][GM10] | Ambient dimension $d_n$, $N$ identical independent pure states, possibly collective measurements. | Information tradeoff background; (10.26)–(10.30) separately prove the stronger directional statement required here. No collective mixed-input extension is used. |
| Li–Ferrie–Gross–Kalev–Caves, [equation (18), Supplemental §II][FisherSymmetric10] | $d=d_n$, fiducial $\psi_0$, positive overlaps $\sqrt{p^0_I}$, two real/imaginary quadratures, setting probabilities $t,1-t$. | The two-basis construction underlies (10.34)–(10.38); arbitrary finite $N$ with real $t$ uses recorded random settings. It does not establish availability within the restricted site menu. |

### 10.15. Distinct conclusions and support boundaries

Theorem 10.2 concerns overlap of classical probability scores.
Theorem 10.8 concerns competition between probability and conjugate
phase information in the chosen pure family (10.21), for all regular
joint measurements on independent copies.
Theorems 10.14–10.16 concern a specified site menu in the different
full-phase nuisance task (10.40).
Their matrices share $D,P,G$, but their sample spaces, parameter
constraints and allowed measurements have been specified separately.
In particular, the absence of a common optimal site cannot be used
to strengthen (10.25) for unrestricted measurements.

The empty word is a shared statistical reference with mass
$p_\varnothing>0$. Its inverse mass in (10.7) is neither a zero-event
singularity nor a physical energy or gravitational source.
All inverse-$P$ statements require full positive support. At a boundary
with some $p_I=0$, one must specify the actual support, allowed
two-sided tangents and reference score regularity afresh; deleting
denominators or assigning limiting Fisher values does not extend these
theorems. Likewise the fixed-reference identities do not assert that
their covariance matrices remain constant away from the reference.

The general tools cited in §10.14 are used with their stated hypotheses.
The selected-relation overlap, top-chain substitutions, dual lift,
directional budget, common-port equivalence and alternating-target
loss are ordinary mathematical applications with the proofs above.
They concern neither a stationary attaining producer nor the arbitrary
finite-producer question in Open Problem 7.2. All its hypotheses and
its unresolved status are separate from the finite calibrated models
of this chapter.

[Correlation10]: AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md#232-层析及奇偶应用所用的已有观察坐标
[Symplectic10]: SYMPLECTIC_PREDICTIVE_COMPLETION.md#3513-长路径关系矩与共轭差分相位
[KMS10]: https://arxiv.org/abs/1804.08140v1
[Matsumoto10]: https://arxiv.org/abs/quant-ph/9711008v1
[GM10]: https://arxiv.org/abs/quant-ph/9902063v2
[FisherSymmetric10]: https://arxiv.org/abs/1507.06904v2

## 追加锚（本行以下为增补区）
