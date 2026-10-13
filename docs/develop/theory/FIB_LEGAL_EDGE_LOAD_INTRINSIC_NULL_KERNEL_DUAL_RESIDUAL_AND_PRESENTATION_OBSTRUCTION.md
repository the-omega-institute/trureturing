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
