# Finite-word branching is necessary for common stopped-law calibration

## 1. The fixed source and complete-law question

**Convention 1.1 (the original experiment).** Fix one prior $\mu$ supported
exactly on $\{1,2,3\}$, with each mass positive. The source parameters are
$m=2,d=1,\ell=2,n=4$. One $K$ is sampled before the first paid Read.
Conditional on this same $K=k$, all seed and payload letters are independent,
with alpha probabilities $r_1=a=1/3$, $r_2=b=2/5$, $r_3=3/8$.
Equal seed pairs remain two paid rejections, and both unequal accepted seeds
remain. At phase p, alpha completes marker 0 and beta suspends. At suspension,
alpha returns to p and beta completes marker 1. The third record is written
before its latch; fourth completion enables its matching original Stop.
Pending and delivered terminals permit no Read.

The original finite control retains the parser, both seeds, selectors, all
marker words and prefixes, bare and held $B,Q^+,Z$ fields, write and latch
flags, permissions, completion and delivery. All positive finite paid
rejection, partial-parse and return histories remain in the domain. The
current-record renderer $I_c$ retains every future letter and inserts its
original operation block; its inverse reads those letters. It preserves
complete-law TV and deletion of an operation with its block, including the
infinite noncompletion outcome. These are the interfaces of [PAIR, Section
2 and Section 11.1] and [PAID, Definition 1.2 and Lemma 2.1.1].

Initialization and acquired-letter kernels are source-independent. Synthetic
generation uses those same kernels, from the actual complete configuration.
COMPLETE charges original control, labels, programs, installed numerics,
selectors, addresses, sampler states, workspace, output cursors and persistent
randomness. The posterior and configuration probability row are analysis
objects, not readable registers. No clock, source reset or new observation
is introduced below.

**Definition 1.2 (complete laws and the unchanged compatible domain).** Put
$t_r=r(1-r)$ and

$$
w_{n,0}=(\beta\alpha)^n\alpha,\qquad
w_{n,1}=(\beta\alpha)^n\beta\beta.
$$

Let $\Omega_p$ consist of these words and $\infty_p$; let $\Omega_\beta$
consist of beta, all $\alpha w_{n,c}$ and $\infty_\beta$. The native laws are

$$
P_{p,r}(w_{n,0})=rt_r^n,\qquad
P_{p,r}(w_{n,1})=(1-r)^2t_r^n,\qquad
P_{\beta,r}=(1-r)\delta_\beta+r\alpha P_{p,r}.
\tag{1.1}
$$

Their infinite masses are zero. With $\lambda=4/15$, use precisely the
normalized descriptor spaces of [PAIR, (11.1)--(11.2)]:

$$
\begin{aligned}
T_p(j)&=\{w_{n,c}:n\ge j,\ c=0,1\}\cup\{\infty_p\},\\
T_\beta(j)&=\{\alpha w_{n,c}:n\ge j,\ c=0,1\}\cup\{\infty_\beta\},\\
\mathcal K_p&=\{Q:a\le Q(\alpha)\le b,\ Q(T_p(j))\le\lambda^j\},\\
\mathcal K_\beta&=\{W:a\le1-W(\beta)\le b,\
 W(T_\beta(j))\le b\lambda^j\}.
\end{aligned}
\tag{1.2}
$$

Here $Q,W$ are probability laws and every displayed tail bound is required
for all $j\ge0$. The spaces carry complete-law TV. Write

$$
u(Q)=Q(\alpha),\quad v(W)=1-W(\beta),\quad
\mathcal R_B(Q)=\frac{Q(\beta\,\cdot)}{1-u(Q)},\quad
\mathcal R_A(W)=\frac{W(\alpha\,\cdot)}{v(W)}.
\tag{1.3}
$$

A compatible pair is a pair of Borel probability flows
$\Gamma_B$ on $\mathcal K_p\times\mathcal K_\beta$ and $\Gamma_A$ on
the reversed product, with common unweighted marginals

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta,
\tag{1.4}
$$

and disintegrations satisfying the full-measure equations

$$
\mathcal R_B(Q)=\int W\,B(Q,dW),\qquad
\mathcal R_A(W)=\int Q\,A(W,dQ).
\tag{1.5}
$$

The conditioning in (1.5) is on the entire input descriptor. Equivalently,
each coordinate residual integrates to zero against every bounded Borel
input test. Every complete atom, including infinity, is tested. Denote this
unchanged compact domain by $\mathfrak C$. Synthetic continuation factors
occur in (1.3), not in the acquired marginals (1.4).

**Definition 1.3 (configuration losses and the full zero face).** Retain

$$
\rho_p=\frac{1116529}{22781250},\quad
\rho_\beta=\frac{239}{6750},\quad
\mathcal J=\max_{s\in\{p,\beta\},\ k\in\{1,2,3\}}
 \left\{\int\operatorname{TV}(D_s,P_{s,r_k})\,d\nu_s-\rho_s\right\},
\tag{1.6}
$$

where $D_p=Q,D_\beta=W$. TV is taken before configuration averaging.
Put $E_p=\{w_{0,1},w_{1,1},w_{2,1}\}$ and
$E_\beta=\{\beta,\alpha w_{0,1}\}$. The supplied endpoint triangle
identity [PAIR, Section 11.8] says that $\mathcal J=0$ requires both complete
coordinate boxes

$$
P_{s,a}(e)\wedge P_{s,b}(e)\le D_s(e)
 \le P_{s,a}(e)\vee P_{s,b}(e)
\quad\text{for every complete atom }e,\quad\nu_s\text{-a.s.},
\tag{1.7}
$$

and both means

$$
\int Q(E_p)d\nu_p=M_p=\frac{11758471}{22781250},\qquad
\int W(E_\beta)d\nu_\beta=M_\beta=\frac{5261}{6750}.
\tag{1.8}
$$

Conversely, (1.7)--(1.8) give the four endpoint losses. The two additional
depth-3 losses in (1.6) remain necessary. The original value is
$j_c=\min_{\mathfrak C}\mathcal J$ [PAIR, Theorem 11.5]. No additional
condition introduced below is a premise of this unrestricted value.

## 2. Seven conditional variances

**Definition 2.1 (the finite successor features).** Define

$$
f(Q)=\bigl(Q(w_{0,1}),Q(w_{1,1}),Q(w_{2,1})\bigr),
\qquad
g(W)=\bigl(W(\beta),W(\alpha w_{0,1}),
 W(\alpha w_{1,1}),W(\alpha w_{2,1})\bigr).
\tag{2.1}
$$

The same expressions evaluate $f,g$ on arbitrary probability laws on their
respective carriers. For the original flows set

$$
\begin{aligned}
V_A&=\int\|f(Q)-f(\mathcal R_A(W))\|_2^2\,d\Gamma_A(W,Q),\\
V_B&=\int\|g(W)-g(\mathcal R_B(Q))\|_2^2\,d\Gamma_B(Q,W),\\
V&=V_A+V_B,\qquad \mathfrak C_7=\{\Gamma\in\mathfrak C:V=0\}.
\end{aligned}
\tag{2.2}
$$

Compatibility makes these sums of conditional variances. They measure
random variation among individual successor forecasts around their input's
full residual. They are not variances of the residual across inputs, of
synthetic return weights, or of actual source letters. They are not extra
data supplied to an observer. Zero $V$ means that these seven scalar
equalities hold on the two edges; it does not require equality of entire
successor laws.

The complete-successor graph class of [REV, (16.5)] satisfies $V=0$.
Proposition 4.1 below proves strict inclusion even among rational represented
observers with both full boxes. There is no finite-support restriction in
$\mathfrak C_7$.

**Theorem 2.2 (finite-feature equality forces full endpoint calibration).**
Every pair in $\mathfrak C_7$ satisfying both boxes (1.7) obeys

$$
\mathcal D:=\int Q(E_p)d\nu_p
 -\kappa\int W(E_\beta)d\nu_\beta-\zeta\le0,
\quad
\kappa=\frac{1116529}{806625},\qquad
\zeta=-\frac{151298}{268875}.
\tag{2.3}
$$

Equality holds if and only if, for one $\theta\in[0,1]$, the original flows are

$$
\begin{aligned}
\Gamma_B&=(1-\theta)\delta_{(P_{p,a},P_{\beta,a})}
             +\theta\delta_{(P_{p,b},P_{\beta,b})},\\
\Gamma_A&=(1-\theta)\delta_{(P_{\beta,a},P_{p,a})}
             +\theta\delta_{(P_{\beta,b},P_{p,b})}.
\end{aligned}
\tag{2.4}
$$

Thus the conclusion concerns the original complete laws and both original
flows, although only seven edge variances were assumed zero. Either event
midpoint in (1.8), in addition to equality in (2.3), forces $\theta=1/2$.

**Proof.** Use the disintegrations of this one compatible pair to form the
stationary analysis path

$$
W_0\xrightarrow{A}Q_0\xrightarrow{B}W_1
 \xrightarrow{A}Q_1\xrightarrow{B}W_2\longrightarrow\cdots,
\qquad W_0\sim\nu_\beta.
\tag{2.5}
$$

This is the descriptor-disintegration chain, not a prescribed original
hidden triple. Both unweighted balances imply stationarity. Countably many
null exceptions can be removed simultaneously along the forward path.
Write $u_t=u(Q_t)$, $v_t=v(W_t)$,
$h_n(t)=Q_t(w_{n,1})$, and $c_t=h_0(t)$. From $V=0$ one has exactly

$$
\begin{aligned}
W_t(\alpha w_{n,1})&=v_t h_n(t) &&(0\le n\le2),\\
c_t&=(1-u_t)(1-v_{t+1}),\\
h_{n+1}(t)&=(1-u_t)W_{t+1}(\alpha w_{n,1}) &&(0\le n\le2).
\end{aligned}
\tag{2.6}
$$

The first line uses the three A features; the last two use the four B
features. These are equalities on the sampled edges, obtained from zero
nonnegative squared integrals. No full residual is replaced by an individual
successor law on an untested coordinate.

Define $x_t=v_tc_t/(1-v_t)$. All denominators are positive. Combining
(2.6), then iterating only the indicated finite range, gives

$$
h_n(t)=c_t\prod_{j=1}^n x_{t+j}\quad(0\le n\le3),
\qquad
W_t(\alpha w_{1,1})=v_tc_tx_{t+1}.
\tag{2.7}
$$

For example $(1-u_t)v_{t+1}c_{t+1}=c_tx_{t+1}$. This proves the
induction in (2.7). No such product formula is asserted for $n>3$.

Here and below use the constants from [REV, (16.11)]

$$
\ell=\frac29,\quad L=\frac6{25},\quad G=\frac9{25},\quad
T=\frac{16}{729},\quad q=\frac{1944}{390625},\quad
d_0=\frac{2341664383}{41527474875}>0.
\tag{2.8}
$$

The suspended boxes for its marker-one words at indices 0 and 1 imply

$$
\frac{18}{125}\le v_tc_t\le\frac4{27},\qquad
\frac8{243}\le v_tc_tx_{t+1}\le\frac{108}{3125}.
$$

Taking ratios gives $\ell\le x_{t+1}\le L$; stationarity also gives
this at time 0. The p boxes at indices 0, 2 and 3, using (2.7), imply

$$
c_t\ge G,\qquad c_tx_{t+1}x_{t+2}\le T,\qquad
c_tx_{t+1}x_{t+2}x_{t+3}\le q.
\tag{2.9}
$$

For $X=(x_0,x_1,x_2,x_3)$ set

$$
\begin{aligned}
U(X)&=\min\{T/(x_1x_2),q/(x_1x_2x_3)\},\\
F(X)&=U(X)(1+x_1+x_1x_2)
 -\kappa\frac{U(X)(1+x_0)}{U(X)+x_0}-\zeta,\\
\psi(t)&=F(t,t,t,t).
\end{aligned}
\tag{2.10}
$$

Two supplied algebraic conclusions apply on the entire cube $[\ell,L]^4$.
First, [REV, (16.21)--(16.26)] proves that $F(X)-x_0x_1$ is bounded
continuous supermodular after coordinate clipping. For any four variables
with the same marginal distribution, its comonotonic comparison therefore
gives

$$
\mathbb EF(X)\le\mathbb E\psi(x_0)
 -\tfrac12\mathbb E(x_1-x_0)^2.
\tag{2.11}
$$

Second, [REV, (15.13)--(15.20)] gives $\psi\le0$, with zero set exactly
$\{\ell,L\}$. These are algebraic and scalar-distribution suppliers:
their cube, seam at $x_3=q/T$, and equal-marginal hypotheses hold here.
The deterministic complete-successor hypothesis of REV Theorem 16.2 is
not used as a theorem premise.

For the actual path, (2.6)--(2.7) also give

$$
Q_0(E_p)=c_0(1+x_1+x_1x_2),\qquad
W_0(E_\beta)=\frac{c_0(1+x_0)}{c_0+x_0}.
\tag{2.12}
$$

The derivative of their chord difference with respect to $c_0$ is at least

$$
1+\ell+\ell^2-
 \kappa\frac{L(1+L)}{(G+\ell)^2}=d_0
\quad\text{on }[c_0,U(X)],
\tag{2.13}
$$

because $G\le c_0\le U(X)$. Thus (2.11) proves the precise inequality

$$
\mathcal D\le\mathbb E\psi(x_0)
 -\tfrac12\mathbb E(x_1-x_0)^2
 -d_0\mathbb E[U(X)-c_0]\le0.
\tag{2.14}
$$

If $\mathcal D=0$, all three nonnegative slacks vanish. Stationarity
then gives, simultaneously at every time, either an $\ell$ orbit with
$x_t=\ell,c_t=4/9$, or an $L$ orbit with $x_t=L,c_t=9/25$.
The identities $v_t=x_t/(c_t+x_t)$ and
$c_t=(1-u_t)(1-v_{t+1})$ force respectively

$$
u_t=v_t=a\ \text{for all }t,
\quad\text{or}\quad u_t=v_t=b\ \text{for all }t.
\tag{2.15}
$$

It remains to recover untested words without a full pathwise product
assumption. The original phase marginals are supported on the two emission
classes $u=r$ and $v=r$, and both original edge flows join only matching
classes, by (2.15). On each class the full conditional equations (1.5)
have constant emissions $r$. Their alpha and completing-beta coordinates
are $r$ and $1-r$. Induction through those full equations yields, at every
input in a common full-measure set,

$$
Q(w_{n,0})=rt_r^n,\qquad Q(w_{n,1})=(1-r)^2t_r^n,
\qquad W=(1-r)\delta_\beta+r\alpha Q.
\tag{2.16}
$$

For the last identity the coordinate induction has identified every Q in
that class with the same native law. Infinite masses are zero by (1.2),
and the finite masses in (2.16) sum to one. Thus the complete laws are
native, and common marginals give the same mixture weight in both flows.
This proves (2.4). Its converse follows from the native recursions and the
endpoint chord identity. The two event endpoint values at each phase are
distinct, so either midpoint gives weight $1/2$. $\square$

The mature expectation comparison in (2.11) can equivalently be supplied
by Côté--Wang, *On convex order and supermodular order without finite mean*,
[Proposition 6 and Definition 3(iii)](https://arxiv.org/html/2502.17803v3).
The clipped test is bounded continuous, so it belongs to their bounded
right-continuous supermodular class. No comparison for arbitrary unbounded
tests, and no equality case from that literature theorem, is used.

## 3. The early-branching exclusion and original histories

**Corollary 3.1 (zero excess requires one of the seven variances).** For
the fixed positive three-depth prior,

$$
\mathcal J=0\ \Longrightarrow\ V>0.
\tag{3.1}
$$

More precisely, the restricted value

$$
j_7:=\min_{\Gamma\in\mathfrak C_7}\mathcal J(\Gamma)>0
\tag{3.2}
$$

exists. The minimum ranges over the whole $\mathfrak C_7$, with no box
constraint, finite-support bound, reversibility or eventual-tail hypothesis.
No numerical value of $j_7$ is asserted.

**Proof.** If $V=0$ and $\mathcal J=0$, the four endpoint configuration
losses give (1.7)--(1.8). Since $M_p=\kappa M_\beta+\zeta$,
Theorem 2.2 forces the fair matched endpoint pair. For its p marginal the
depth-3 target $R=P_{p,3/8}$ violates the budget. Explicitly,

$$
R(w_{3,1})-P_{p,b}(w_{3,1})
=\frac{344076471}{6553600000000}=:\delta_3>0.
\tag{3.3}
$$

The b endpoint is the upper endpoint at this coordinate. The supplied
coordinate triangle identity therefore gives

$$
\tfrac12\operatorname{TV}(P_{p,a},R)
+\tfrac12\operatorname{TV}(P_{p,b},R)
\ge\rho_p+\tfrac12\delta_3>\rho_p.
\tag{3.4}
$$

This one violated loss suffices; the suspended depth-3 budget has not been
removed from (1.6). Formula (3.3) is the existing complete-word gap [REV,
(16.41)], not a new optimized constant.

For (3.2), [PAIR, Lemmas 11.1 and 11.3] supply compactness of
$\mathfrak C$ and continuity of each complete-coordinate residual.
Consequently $V$ is continuous under weak convergence of the two flows,
so $\mathfrak C_7$ is closed and compact. A native singleton makes it
nonempty. The finite maximum (1.6) is continuous and nonnegative. Its
attained minimum is positive by the zero exclusion. This last compactness
argument is a supplied method applied after the new exclusion, not an
independent mathematical contribution. $\square$

**Theorem 3.2 (a regular original-observer consequence).** Let $M$ be an
original finite COMPLETE observer of Convention 1.1. On the seed-1,
marker-100 held-record fibre of [PAID, Lemma 14.1], suppose:

1. all reachable fourth-phase synthetic emissions belong to $[a,b]$;
2. every positive acquired p-beta edge has the same four features $g$ as
   its input's full B residual;
3. every positive acquired suspended-alpha edge has the same three
   features $f$ as its input's full A residual.

Features are pulled back through the appropriate current-record renderer.
These hypotheses concern the union of reachable returned configurations;
they do not require a stationary actual-history row. Then

$$
\max\{R_{\mathrm{conf},p}(M)-\rho_p,
       R_{\mathrm{conf},\beta}(M)-\rho_\beta\}\ge j_7>0.
\tag{3.5}
$$

**Proof.** PAID Lemma 14.1 supplies one support-closed finite table,
with the original acquired kernels, positive rows $\pi,\tau$ satisfying
both unweighted balances, copied complete decoders, and all supported
configuration losses bounded by those original risks. Its positive labels
are reachable on the stated fibre. Deleting zero-row labels creates no
new edge. Hence assumptions 1--3 survive this restriction exactly.

Regular survival gives the copied laws (1.2). Push the same two acquired
flows to these laws. The full same-update cylinder equations give (1.5),
and both balances give (1.4). The feature equalities on each retained edge
give $V=0$. Coincident descriptors cause no difficulty: equal input laws
have the same residual feature values, so merging them preserves the edge
equalities. Configuration-before-TV integrals are unchanged by this
pushforward. Corollary 3.1 then gives (3.5).

PAID's common rows arise from positive finite paid histories concentrating
the posterior at each supported depth, followed by a Cesàro return-row
limit. They are the same rows for all three targets. The records, both
seeds, partial parses, original writes, permissions and matching Stop
remain through the copied decoders and $I_c$. No synthetic continuation
weight is inserted into those actual rows. $\square$

The regularity hypothesis in Theorem 3.2 is explicit. Same-kernel clipping
can change the selected own-law features, so an arbitrary observer with
zero or unit emissions is not covered merely because it has the
unclipped feature property. No preservation theorem for that property
under clipping is asserted. There is no prescribed total-resource or
hard marginalized-defect budget in (3.5).

## 4. Genuine branching can be delayed beyond every chosen finite depth

**Proposition 4.1 (a rational family strictly beyond residual graphs).**
For every integer $N\ge3$ there is one rational regular stationary table,
with $2N+3$ labels at each phase, whose own laws satisfy both full boxes
(1.7) and $V=0$, but whose complete-law B successors genuinely branch.
Its A successors are deterministic. Its two branch successors agree on
both completed-word coordinates $w_{n,c}$ for every $n<N$ after removing
their initial alpha, and differ at $\alpha w_{N,0}$.

The table has a represented finite COMPLETE realization on every original
record fibre, under the original exact fair-bit service convention. It is
not a zero-excess witness. The count $2N+3$ is a label count, not a total
COMPLETE minimum or a returned-cut minimum.

**Proof.** Put

$$
u_*=\frac{73}{200},\quad v_* =\frac{46}{127},\quad
\varepsilon=\frac1{100000},\quad v^*=v_*+\varepsilon.
\tag{4.1}
$$

The labels are $o$ and $(\sigma,j)$ for $\sigma\in\{-1,1\}$,
$0\le j\le N$. Take $A=I$. The B transition from $o$ chooses
$(\sigma,0)$ with probability $1/2$; each arm advances deterministically
from $j$ to $j+1$, and $(\sigma,N)$ returns to $o$. Set

$$
\begin{aligned}
u_o&=u_*,& v_o&=v_*,\\
u_{\sigma,j}&=u_*,&v_{\sigma,j}&=v_* &&(j<N),\\
u_{\sigma,N}&=u_*+\sigma\varepsilon,&v_{\sigma,N}&=v^*.
\end{aligned}
\tag{4.2}
$$

The positive row

$$
\pi_o=\frac1{N+2},\qquad
\pi_{\sigma,j}=\frac1{2(N+2)},\qquad \tau=\pi
\tag{4.3}
$$

satisfies $\pi B=\pi$ by checking the centre, the first arm nodes and
each remaining arm node. Also $\tau A=\pi$. All entries are rational.

Let $L_{ij}=(1-u_i)B_{ij}v_j$ and
$c_i=(1-u_i)\sum_jB_{ij}(1-v_j)$. The own complete laws are

$$
Q_i(w_{n,0})=(L^nu)_i,\quad Q_i(w_{n,1})=(L^nc)_i,
\qquad W_i=(1-v_i)\delta_\beta+v_i\alpha Q_i.
\tag{4.4}
$$

Here $u+c+L\mathbf1=\mathbf1$ and $L\mathbf1\le\lambda\mathbf1$.
The telescoping identity
$\sum_{n<M}L^n(u+c)=\mathbf1-L^M\mathbf1$ proves normalization,
the tail bounds (1.2) and zero infinite masses. Thus these are full laws
of one table, not independently assigned coordinates. Their same-update
recursions and (4.3) give both original compatible flows.

We verify every endpoint coordinate. Write $u_-=u_*-\varepsilon$,
$u_+=u_*+\varepsilon$, $v_-=v_*$, $v_+=v^*$. Each positive edge weight
$(1-u_i)v_j$ and each completion weight $c_i$ satisfy respectively

$$
z_-=(1-u_+)v_-\le(1-u_i)v_j\le(1-u_-)v_+=z_+,
\qquad
c_-=(1-u_+)(1-v_+)\le c_i\le(1-u_-)(1-v_-)=c_+.
\tag{4.5}
$$

In particular $\ell<z_-\le z_+<L$ and $a<u_-\le u_+<b$.
Iteration of the positive matrix gives

$$
u_-z_-^n\le Q_i(w_{n,0})\le u_+z_+^n,\qquad
c_-z_-^n\le Q_i(w_{n,1})\le c_+z_+^n.
\tag{4.6}
$$

The marker-zero bounds and their suspended multiples lie between
$a\ell^n,bL^n$ and $a^2\ell^n,b^2L^n$, respectively, for every $n$.
For an explicit small rational enclosure in the marker-one checks, put

$$
\underline z=\frac{22999}{100000},\quad
\overline z=\frac{23001}{100000},\quad
\underline c=\frac{40498}{100000},\quad
\overline c=\frac{40501}{100000},\quad
\underline v=\frac{3622}{10000},\quad
\overline v=\frac{36222}{100000}.
\tag{4.7}
$$

Substitution in (4.1) gives strict lower and upper enclosures for the
corresponding quantities in (4.5). With
$a_n=(4/9)\ell^n$, $b_n=(9/25)L^n$, rational multiplication gives

$$
\begin{array}{c|c|c}
\text{indices}&\text{lower margin}&\text{upper margin}\\\hline
n=0,1,2,3&
\underline c\,\underline z^n-\min(a_n,b_n)>10^{-5}&
\max(a_n,b_n)-\overline c\,\overline z^n>10^{-5}\\
n=0,1&
\underline v\,\underline c\,\underline z^n-\min(aa_n,bb_n)>10^{-5}&
\max(aa_n,bb_n)-\overline v\,\overline c\,\overline z^n>10^{-5}.
\end{array}
\tag{4.8}
$$

All entries in this finite table are explicit rational inequalities; for
example its tight p index 3 has lower margin greater than $49/10^6$ and
upper margin greater than $48/10^6$. For p, the endpoint ordering is fixed
from index 3 onward. The lower and upper enclosing sequences in (4.8)
then multiply by $\underline z>\ell$ and $\overline z<L$, so induction
proves all later p boxes. The suspended ordering is fixed from index 1
onward, and the same induction proves all its later marker-one boxes.
The suspended beta coordinate is boxed by $v_i\in[a,b]$; the infinite
coordinates have already been handled. This proves the full boxes for
every $N$, without checking a truncated replacement problem.

There is only one nondeterministic B row. Its two successors are
$W_{+,0}$ and $W_{-,0}$. Starting at the corresponding Q labels, all
transitions are deterministic up to arm position $N$. The first $N$
emissions $u$ coincide, and all v values encountered through that position
also coincide between the two arms, including their common $v^*$.
Consequently (4.4) gives

$$
Q_{+,0}(w_{n,c})=Q_{-,0}(w_{n,c})\quad(n<N,\ c=0,1),
\tag{4.9}
$$

whereas

$$
Q_{+,0}(w_{N,0})-Q_{-,0}(w_{N,0})
=2\varepsilon(1-u_*)^Nv_*^{N-1}v^*>0.
\tag{4.10}
$$

Both successor W laws have completing-beta mass $1-v_*$ and have the
same selected marker-one coordinates because $N\ge3$. Their full
residual mean is their equal mixture. Thus the B features have zero
conditional variance, while all other B rows and all A rows are
deterministic. This proves $V=0$ after pushing the label flows to complete
descriptors, even if any unneeded labels happen to share a descriptor.

The full B dispersion of [REV, (16.5)] is nevertheless positive:

$$
d_B\ge\frac{\pi_o}{2}\operatorname{TV}(W_{+,0},W_{-,0})>0.
\tag{4.11}
$$

Indeed the centre residual is their mean and each distance to that mean
is half their mutual TV. Its mass is positive; merging coincident inputs
does not change this integral, since equal input laws have equal complete
residuals. Formula (4.10), multiplied by $v_*$, witnesses different W
laws. Hence the pair is outside the full residual-graph class.

To realize the table on the original source, retain the full $C_0$, use
fair synthesis before the third latch, and sample (4.3) independently in
the same update after the third write and latch. Apply B after acquired
p-beta and A after acquired suspended-alpha, identically in synthesis.
Complete and Stop using the original control. Both balances keep the
rows $\pi,\tau$ at every positive fourth-segment history, on every record
fibre. This is [PAID, Lemma 2.1.1] with all its source hypotheses retained.

For each fixed N all primitives are rational. A finite common denominator
permits exact categorical sampling by a bounded candidate drawn from fresh
fair bits, rejection above that denominator, and deterministic workspace
cleanup before return. All code, installed integers, selectors, candidates,
cursors and service states are charged. The same update service is used
after acquired and synthetic letters; independent emission bits are used
when synthesis needs them. No source Read is used by a private service.
Almost-sure service return is not a finite worst-case bit or work bound.
This supplies a represented finite observer, without identifying its
label count with total COMPLETE. Corollary 3.1 gives positive excess for
every member, so none supplies the original zero face. $\square$

## 5. Correspondence and the remaining common-flow relation

**Citation 5.1 (source-relative content and supplied mathematics).** The
repository references below bind the same immutable source snapshot:

- [PAIR](https://github.com/the-omega-institute/trureturing/blob/997e72a221b4754c0a3f96612a3fda0b78bc9593/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md),
  Sections 11, 13 and 18.
- [REV](https://github.com/the-omega-institute/trureturing/blob/997e72a221b4754c0a3f96612a3fda0b78bc9593/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md),
  Sections 15--16, especially (15.13)--(15.20) and (16.21)--(16.26).
- [PAID](https://github.com/the-omega-institute/trureturing/blob/997e72a221b4754c0a3f96612a3fda0b78bc9593/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md),
  Lemmas 2.1.1 and 14.1.
- [RETURN](https://github.com/the-omega-institute/trureturing/blob/997e72a221b4754c0a3f96612a3fda0b78bc9593/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md),
  Sections 12--15.
- [SURVIVAL](https://github.com/the-omega-institute/trureturing/blob/997e72a221b4754c0a3f96612a3fda0b78bc9593/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RETURN_SURVIVAL_DISPERSION.md),
  Proposition 3.3 and Corollary 5.3.

Theorem 2.2 is a source-relative extension of the REV certificate to a
properly larger, genuinely branching domain. Its additional argument is
the finite-edge derivation (2.6)--(2.7) and recovery of all untested words
from the original conditional equations at equality. Proposition 4.1
shows that finite-feature determinism cannot be identified with full-law
determinism, even under both complete boxes and represented original
realization. Its arbitrary delay is unbounded across the family, while
each member remains finite. These deductions are repo-derived; no global
priority assertion is made.

The scalar supermodularity, diagonal rational certificate, endpoint
geometry, positive-word gap, complete-law compactness, common-row extraction
and exact rational service convention are credited suppliers, not new
standalone results. Finite-state branching and delayed distinguishability
are mature constructions; their role here is to satisfy the original
common-flow, all-coordinate-box and finite-feature equations simultaneously.

The martingale-coupling equivalences of Leskelä--Vihola,
*Conditional convex orders and measurable martingale couplings*,
[Theorems 1.2--1.4](https://arxiv.org/html/1404.0999v3), apply to integrable
finite-dimensional projections and conditional kernels. The bounded
features in (2.1) meet that integrability premise. Those results do not
turn positive conditional variance into zero, identify a sampled successor
with its barycentre, or supply the original two complete-law flows.
No new general convex-order or coupling theorem is claimed here.

REV16 excludes $d_A+d_B=0$; the new exclusion concerns $V=0$ and includes
the pairs (4.1)--(4.11) with $d_B>0$. PAIR18 instead assumes finite p
support and an eventual exact averaged endpoint-root recurrence. No such
recurrence is assumed here. In fact Proposition 4.1's finite-p full-box
pairs cannot satisfy that recurrence: PAIR18 would force native endpoint
descriptors, whereas all their emissions are strictly interior. RETURN15
minimizes returned-cut configurations for a separately prescribed admissible
finite triple; the analysis chain (2.5) is not asserted to equal an arbitrary
such triple. No returned-cut or total-resource optimality follows.

**Open problem 5.2 (the unrestricted original decision).** The question
$j_c=0$ versus $j_c>0$ remains on all of $\mathfrak C$. A zero pair, if
one exists, must have $V>0$ in addition to the published SURVIVAL signed
same-path cancellation requirements. The new statement does not say which
interface or which of the seven coordinates must have positive variance,
does not assert that all seven do, and does not give a numerical variance
floor or a positive unrestricted risk gap.

For general branching, (1.5) gives conditional averages, while (2.6)
requires the seven variances to vanish. Without that requirement, the
finite product identity (2.7) is unavailable. Its lost signed correlations
must coexist with both full boxes, both midpoint means, both depth-3
configuration losses and both full residual equations on the same phase
marginals. This is the remaining relation; independently optimized
variances, marginals or path products do not answer it.

A full compatible zero witness or a full-domain exclusion is still needed.
PAIR11's finite atomicity criterion and PAIR13's one-sided finite-support
results retain their own hypotheses. Exact represented attainment
additionally needs permitted samplers for every resulting primitive.
Neither the restricted minimum $j_7$ nor the represented family in
Proposition 4.1 supplies an unrestricted finite attainer, a fixed COMPLETE
optimum, a universal ML classification or a practical performance claim.

## 追加锚（本行以下为后续增补区）

## 6. An evaluated seven-feature tradeoff on the full compatible domain

**Convention 6.1 (the fixed prior and the unchanged two flows).** In this
chapter fix any one original finite or countable installed prior $\mu$
with $\mu(1),\mu(2)>0$, and assume that $\mu(k_*)>0$ for at least one
$k_*\ge3$. The rates are $r_k=F_{k+1}/F_{k+3}$, with the Fibonacci
convention giving $r_1=a=1/3$ and $r_2=b=2/5$. All other source,
history, control and same-update conditions of Convention 1.1 remain.
In particular K is sampled once; the prior is not changed when a target
is tested. This is the general-prior domain of [PAIR6, Section 11.1].

Use precisely the carriers, spaces, full conditional residual equations
and common unweighted marginals (1.2)--(1.5). Those definitions do not
depend on the size of the prior's support. For an arbitrary Borel pair
$\Gamma=(\Gamma_B,\Gamma_A)\in\mathfrak C$, write

$$
\mathcal J_\mu(\Gamma)=
\max_{s\in\{p,\beta\}}
\left\{\sup_{k:\mu(k)>0}
 \int\operatorname{TV}(D_s,P_{s,r_k})\,d\nu_s-\rho_s\right\}.
\tag{6.1}
$$

This is exactly [PAIR6, (11.9)], retaining every supported target and TV
inside the configuration integral. For the three-depth prior of Chapters
1--5 it agrees with (1.6). The seven functions and their two variance
integrals are exactly (2.1)--(2.2), evaluated on these same original flows;
write $V=V_A+V_B$. No box, event-mean, finite-support, reversibility,
common-rate or deterministic-successor condition is added to
$\mathfrak C$.

**Theorem 6.2 (an evaluated joint risk and seven-variance exclusion).**
For every prior and every compatible pair of Convention 6.1,

$$
\boxed{\quad \mathcal J_\mu(\Gamma)+\sqrt{V(\Gamma)}\ge10^{-26}.\quad}
\tag{6.2}
$$

Thus an explicit modulus is $\omega(t)=\sqrt t$ on $t\ge0$, with
coefficient one and constant $\eta=10^{-26}$. In particular a pair with
$\mathcal J_\mu=0$ must satisfy $V\ge10^{-52}$, and no pair has simultaneously
$\mathcal J_\mu<5\cdot10^{-27}$ and $V<2.5\cdot10^{-53}$.
For a compatible family with $\mathcal J_\mu(\Gamma_n)\to0$ under this
same fixed prior, $\liminf_n V(\Gamma_n)\ge10^{-52}$; existence of such
a family is not asserted. On the original three-depth $V=0$ class, this
also evaluates a lower bound $j_7\ge10^{-26}$ for (3.2).

**Proof.** Put $e=\mathcal J_\mu$, $s=\sqrt V$ and
$\varepsilon=e+s$. Endpoint triangle geometry gives $e\ge0$.
If $\varepsilon>1$, (6.2) is immediate, so assume $\varepsilon\le1$.
All expectations below belong to the same finite analysis path obtained
from the given two flows. All $L^1$ norms mean $\mathbb E|\cdot|$ on
that path. Retain $\ell,L,G,T,q,\kappa,\zeta,d_0$ from (2.3),
(2.8), and $M_p,M_\beta$ from (1.8). In particular

$$
M_p=\kappa M_\beta+\zeta,\qquad
\kappa<\frac75,\qquad d_0>\frac1{20},\qquad
\rho_p>\frac1{25}.
\tag{6.3}
$$

First pay for departures from the endpoint boxes. For either phase define

$$
\Delta_s(D)=\sum_{\omega\in\Omega_s}
 \operatorname{dist}\left(D(\omega),
 [P_{s,a}(\omega)\wedge P_{s,b}(\omega),
  P_{s,a}(\omega)\vee P_{s,b}(\omega)]\right).
\tag{6.4}
$$

The supplied coordinate triangle identity [PAIR6, (5.7)] gives, for each
complete law D,
$\Delta_s(D)=\operatorname{TV}(D,P_{s,a})+
\operatorname{TV}(D,P_{s,b})-2\rho_s$.
Both endpoints occur in (6.1), hence

$$
\mathbb E\Delta_p(Q)\le2e,\qquad
\mathbb E\Delta_\beta(W)\le2e.
\tag{6.5}
$$

The endpoint-positive events have values
$P_{s,a}(E_s)=M_s+\rho_s$ and
$P_{s,b}(E_s)=M_s-\rho_s$. The pointwise TV tests on these events,
applied to the two endpoint budgets, also give

$$
|\mathbb E Q(E_p)-M_p|\le e,\qquad
|\mathbb E W(E_\beta)-M_\beta|\le e.
\tag{6.6}
$$

Neither (6.5) nor (6.6) assumes exact boxes or exact calibration. The
means in (6.6) are endpoint-event means, not immediate-emission means.

Disintegrate the original flows as in (1.5), and integrate their kernels
to form the finite path

$$
W_0\xrightarrow A Q_0\xrightarrow B W_1\xrightarrow A Q_1
 \xrightarrow B W_2\xrightarrow A Q_2\xrightarrow B W_3
 \xrightarrow A Q_3,\qquad W_0\sim\nu_\beta.
\tag{6.7}
$$

Both common unweighted marginals imply that each A edge has law
$\Gamma_A$ and each B edge has law $\Gamma_B$. Each same-phase
descriptor, and each translated path segment of a given length, therefore
has the same distribution wherever it occurs in (6.7). No independent
choices of the two phase marginals have been made. This finite kernel
integral is an analysis coupling, not an installed random tape or a new
observation service.

Write $u_i=u(Q_i)$, $v_i=v(W_i)$,
$h_n(i)=Q_i(w_{n,1})$, $k_n(i)=W_i(\alpha w_{n,1})$, and
$c_i=h_0(i)$. The beta coordinate of the full B equation gives

$$
c(Q)=(1-u(Q))\int(1-v(W))B(Q,dW),\qquad
G\le c_i\le\frac49.
\tag{6.8}
$$

These bounds follow from the original emission interval $[a,b]$ and hold
at positive e. Define the errors, on the indicated edges, by

$$
\begin{aligned}
a_{n,i}&=k_n(i)-v_i h_n(i) &&(0\le n\le2),\\
b_{0,i}&=c_i-(1-u_i)(1-v_{i+1}),\\
b_{n+1,i}&=h_{n+1}(i)-(1-u_i)k_n(i+1) &&(0\le n\le2).
\end{aligned}
\tag{6.9}
$$

Each $a_{n,i}$ is $-v_i$ times the corresponding A feature discrepancy.
Each $b_{j,i}$ is $-(1-u_i)$ times the corresponding B discrepancy.
The seven squared integrals in (2.2) and Cauchy--Schwarz consequently give

$$
\|a_{n,i}\|_1\le\frac25s,\qquad
\|b_{j,i}\|_1\le\frac23s.
\tag{6.10}
$$

Here and below an index is used only where its path segment exists.
Put

$$
x_i=\frac{v_ic_i}{1-v_i},\qquad
p_n(i)=c_i\prod_{j=1}^n x_{i+j},\qquad p_0(i)=c_i.
\tag{6.11}
$$

The original emission bounds and (6.8) imply
$9/50\le x_i\le8/27<1/3$. Let
$d_i=c_iv_{i+1}/(1-v_{i+1})\le8/27$.
Then $p_{n+1}(i)=d_ip_n(i+1)$, and direct substitution from (6.9)
gives the error identity

$$
\begin{aligned}
h_{n+1}(i)-p_{n+1}(i)
={}&b_{n+1,i}+(1-u_i)a_{n,i+1}\\
&-\frac{v_{i+1}}{1-v_{i+1}}b_{0,i}h_n(i+1)
 +d_i\bigl(h_n(i+1)-p_n(i+1)\bigr).
\end{aligned}
\tag{6.12}
$$

Since $0\le h_n\le1$, its first three terms have total $L^1$ norm
at most $(62/45)s$. Starting with zero error at $n=0$, the geometric
sum is bounded by
$(62/45)/(1-8/27)=186/95<2$. Thus

$$
\begin{aligned}
\|h_n(i)-p_n(i)\|_1&\le2s &&(1\le n\le3,\ i+n\le3),\\
\|k_0(i)-v_ic_i\|_1&\le\frac25s,\\
\|k_1(i)-v_ic_ix_{i+1}\|_1&\le\frac65s &&(i<3).
\end{aligned}
\tag{6.13}
$$

This is a finite product estimate with errors; it asserts no pathwise
product representation at later words.

Next clip only these auxiliary real numbers:
$z_i=\min\{L,\max\{\ell,x_i\}\}$, and put
$R_x=\mathbb E|x_i-z_i|$, independent of i by stationarity.
Let
$I_0=[18/125,4/27]$ and $I_1=[8/243,108/3125]$, the suspended
endpoint intervals for $k_0,k_1$. Their extreme ratios are
$\ell=\inf I_1/\sup I_0$ and $L=\sup I_1/\inf I_0$.
For $y>0,x\ge0$ one has

$$
y\operatorname{dist}(x,[\ell,L])
 \le\operatorname{dist}(yx,I_1)+L\operatorname{dist}(y,I_0).
\tag{6.14}
$$

For $x>L$, expand $y(x-L)=(yx-\sup I_1)+L(\inf I_0-y)$.
For $x<\ell$, expand
$y(\ell-x)=(\inf I_1-yx)+\ell(y-\sup I_0)$.
Each term is bounded above by the respective distance, using
$\ell\le L$; inside the interval the left side is zero.
Apply (6.14) with $y=v_ic_i\ge3/25$ and $x=x_{i+1}$.
The two coordinate distances for $k_0,k_1$ have sum at most
$\Delta_\beta(W_i)$, while distance to an interval is 1-Lipschitz.
Equations (6.5), (6.13) give

$$
R_x\le\frac{25}{3}
 \left(2e+\left(\frac65+L\frac25\right)s\right)
 =\frac{50}{3}e+\frac{54}{5}s\le20\varepsilon.
\tag{6.15}
$$

Both $x_i$ and $z_i$ are at most $1/3$. Telescoping a product of
$n\le3$ factors costs at most $n(1/3)^{n-1}R_x\le R_x$ in
expectation, without any independence assumption. Consequently

$$
\left\|h_n(i)-c_i\prod_{j=1}^n z_{i+j}\right\|_1
 \le2s+\frac49R_x\le12\varepsilon
 \quad(1\le n\le3,\ i+n\le3).
\tag{6.16}
$$

No descriptor or flow has been clipped. Set $Z=(z_0,z_1,z_2,z_3)$,
and reuse the scalar envelope and certificate (2.10):

$$
\begin{aligned}
U(Z)&=\min\{T/(z_1z_2),q/(z_1z_2z_3)\},\\
H(c,Z)&=c(1+z_1+z_1z_2)
 -\kappa\frac{c(1+z_0)}{c+z_0}-\zeta,\\
F(Z)&=H(U(Z),Z),\qquad \psi(t)=F(t,t,t,t).
\end{aligned}
\tag{6.17}
$$

On the whole cube $[\ell,L]^4$, $G\le U\le4/9$.
The p endpoint upper bounds at $h_2,h_3$ are T and q.
Their positive excesses have sum at most $\Delta_p(Q_0)$.
Since $\ell<1$, the two denominators in U are at least $\ell^3$.
Taking the positive part, using the maximum defining $(c_0-U)_+$,
and applying (6.5), (6.16) yields

$$
\begin{aligned}
\mathbb E(c_0-U)_+
&\le\ell^{-3}\mathbb E\left[
 (c_0z_1z_2-T)_++(c_0z_1z_2z_3-q)_+\right]\\
&\le\ell^{-3}(24\varepsilon+2e)
 \le\frac{729}{8}\,26\varepsilon\le2500\varepsilon.
\end{aligned}
\tag{6.18}
$$

In particular the actual $c_0$ is not assumed to lie below U.
Equation (6.16) bounds the $L^1$ error in replacing $Q_0(E_p)$ by
$c_0(1+z_1+z_1z_2)$ by $24\varepsilon$.
Also

$$
(1-v_0)+v_0c_0=\frac{c_0(1+x_0)}{c_0+x_0}.
$$

For $G\le c\le4/9$ and $9/50\le x\le8/27$, the absolute x
derivative of $c(1+x)/(c+x)$ is
$c(1-c)/(c+x)^2\le(1/4)/(G+9/50)^2<1$.
The clipped value lies in this same interval. Thus (6.13), (6.15) give

$$
\left\|W_0(E_\beta)-\frac{c_0(1+z_0)}{c_0+z_0}\right\|_1
 \le\frac25s+R_x\le21\varepsilon.
\tag{6.19}
$$

Using (6.3), (6.6), the errors $24\varepsilon$ and
$21\varepsilon$, and
$24+21\kappa+1+\kappa<60$, we obtain
$\mathbb EH(c_0,Z)\ge-60\varepsilon$.
On $G\le c\le4/9$ and the entire cube, differentiation gives

$$
d_0\le\partial_cH
 =1+z_1+z_1z_2-\kappa\frac{z_0(1+z_0)}{(c+z_0)^2}
 \le1+L+L^2<\frac43.
\tag{6.20}
$$

Both c and U are in this interval. Integration in c therefore gives
$H(c_0,Z)\le F(Z)-d_0(U-c_0)_++(4/3)(c_0-U)_+$.
The bounded continuous supermodular certificate [REV6,
(16.21)--(16.26)] applies to the four equally distributed $z_i$:

$$
\mathbb EF(Z)\le\mathbb E\psi(z_0)
 -\frac12\mathbb E(z_1-z_0)^2.
\tag{6.21}
$$

Its test is the coordinate-clipped extension of $F(Z)-z_0z_1$.
The four variables may be dependent. The certificate and the bounded-test
comonotonic comparison are scalar suppliers; no complete-successor graph
or periodic-table hypothesis is required here. The supplied diagonal
certificate has $\psi\le0$. Combining (6.18)--(6.21) gives the
quantitative slack bound

$$
\mathbb E[-\psi(z_0)]+\frac12\mathbb E(z_1-z_0)^2
 +d_0\mathbb E(U-c_0)_+\le4000\varepsilon,
\tag{6.22}
$$

since $60+(4/3)2500<4000$.

We now evaluate a diagonal coercivity constant. Write
$h=q/T=177147/781250$. On $[\ell,h]$, [REV6, (15.13)--(15.20)]
supplies $\psi=N_{\rm LL}/d_{\rm LL}$ with

$$
N_{\rm LL}\le-\frac{17674}{10^{12}}[1-(1-X)^8],\qquad
X=\frac{t-\ell}{h-\ell},\qquad
d_{\rm LL}=2t^2(T+t^3)^2.
$$

On $[h,L]$ it supplies $\psi=N_{\rm HH}/d_{\rm HH}$ with

$$
N_{\rm HH}\le-\frac{26733}{10^{12}}(1-X^8),\qquad
X=\frac{t-h}{L-h},\qquad
d_{\rm HH}=2t^4(q+t^4).
$$

These are the diagonal restrictions of the supplied two-variable Bernstein
bounds, not a new polynomial certificate. Their positive denominators obey

$$
\begin{aligned}
d_{\rm LL}&<2(1/4)^2(9/400+1/64)^2<1/5000,\\
d_{\rm HH}&<2(1/4)^4(1/200+1/256)<1/10000,\\
0<h-\ell&=31823/7031250<1/200,\\
0<L-h&=10353/781250<1/50.
\end{aligned}
$$

Use $1-(1-X)^8\ge X$ and $1-X^8\ge1-X$ on $[0,1]$.
The resulting slopes are at least
$17674\cdot5000\cdot200/10^{12}>1/100$ and
$26733\cdot10000\cdot50/10^{12}>1/100$, respectively. Hence

$$
-\psi(t)\ge\frac1{100}\operatorname{dist}(t,\{\ell,L\})
 \quad(\ell\le t\le L).
\tag{6.23}
$$

Equations (6.18), (6.22), (6.23), $d_0>1/20$ and
$\sqrt{8000}<90$ now yield

$$
\begin{aligned}
\mathbb E\operatorname{dist}(z_0,\{\ell,L\})&\le400000\varepsilon,\\
\mathbb E|z_1-z_0|&\le90\sqrt\varepsilon,\\
\mathbb E|c_0-U|&\le82500\varepsilon.
\end{aligned}
\tag{6.24}
$$

Only two statistics are needed for the final original-risk test.
Let $\xi\in\{\ell,L\}$ be a nearest endpoint to $z_0$, with a
fixed choice on a tie. Write $\widehat r=a$ at $\xi=\ell$ and
$\widehat r=b$ at $\xi=L$, and let
$c_\xi=(1-\widehat r)^2$.
Set $A_0=90\sqrt\varepsilon$, $B_0=400000\varepsilon$.
Stationarity and the triangle inequality imply

$$
\mathbb E|z_j-\xi|\le jA_0+B_0\quad(0\le j\le3).
\tag{6.25}
$$

The function U is 2-Lipschitz in each of its last three coordinates:
on either active branch its nonzero partial derivative has absolute value
$U/z_j\le(4/9)/\ell=2$, and the two branches agree at $z_3=h$.
Moreover $U(\xi,\xi,\xi,\xi)=c_\xi$. Consequently

$$
\mathbb E|c_0-c_\xi|\le
82500\varepsilon+2\sum_{j=1}^3(jA_0+B_0)
=2482500\varepsilon+1080\sqrt\varepsilon=:D_0.
\tag{6.26}
$$

Put $S_r=P_{p,r}(E_p)$ and $f_3(r)=P_{p,r}(w_{3,1})$.
At an endpoint, $r(1-r)=\xi$, so
$S_{\widehat r}=c_\xi(1+\xi+\xi^2)$ and
$f_3(\widehat r)=c_\xi\xi^3$.
All z and $\xi$ are at most $L<1/4$ and $c_\xi<1/2$.
For the event polynomial, its c coefficient is below $3/2$, and
the remaining difference is bounded by
$(1/2)(2|z_1-\xi|+|z_2-\xi|)$.
For the triple product, use coefficient at most one for c and
$(1/2)\sum_{j=1}^3|z_j-\xi|$ for its remaining difference.
Together with (6.16) these give

$$
\begin{aligned}
\|Q_0(E_p)-S_{\widehat r}\|_1
 &\le24\varepsilon+\tfrac32D_0+2A_0+\tfrac32B_0,\\
\|Q_0(w_{3,1})-f_3(\widehat r)\|_1
 &\le12\varepsilon+D_0+3A_0+\tfrac32B_0.
\end{aligned}
\tag{6.27}
$$

Since $0\le\varepsilon\le1$, both right sides are at most
$K_0\sqrt\varepsilon$, where $K_0=5000000$.
Indeed their respective coefficients after replacing
$\varepsilon$ by $\sqrt\varepsilon$ are $4325574$ and $3083862$.
There is no assertion that the entire law is close to an endpoint, nor
any bound on untested successor branching.

Choose one actually supported $k_*\ge3$ and put $r=r_{k_*}$,
$R=P_{p,r}$ and $S=R(E_p)$. The uniform original-rate word gap
[PAIR6, (12.10)] supplies

$$
\delta_r:=f_3(r)-q\ge
\frac{14219478376}{318644812890625}>\frac1{25000}.
\tag{6.28}
$$

The last comparison is exact: multiplying its numerator by 25000 and
subtracting its denominator gives $36842146509375>0$.
The supplier applies because every original $r_k$ with $k\ge3$ lies in
$[3/8,5/13]$. Depth 3 is not introduced when it is unsupported.

Let $\theta=\Pr(\xi=L)$. Since
$S_a=M_p+\rho_p$ and $S_b=M_p-\rho_p$, (6.6), (6.27) imply

$$
|\theta-1/2|\le\frac{e+K_0\sqrt\varepsilon}{2\rho_p}.
\tag{6.29}
$$

The complete word $w_{3,1}$ is outside $E_p$. For each sample with
$\xi=\ell$, use the pointwise test
$\operatorname{TV}(Q_0,R)\ge Q_0(E_p)-R(E_p)$.
For each sample with $\xi=L$, use instead

$$
\operatorname{TV}(Q_0,R)\ge
 R(E_p\cup\{w_{3,1}\})-Q_0(E_p\cup\{w_{3,1}\}).
$$

The selector $\xi$ can depend on both $W_0$ and $Q_0$; each inequality
holds pointwise, so it only selects a valid analytic lower bound.
It is not an input-measurable observer classifier and does not have to be
one. Averaging the left side still gives exactly the original
$\mathcal L_p(R)=\int\operatorname{TV}(Q,R)d\nu_p$.
Equation (6.27) therefore yields

$$
\mathcal L_p(R)\ge
(1-\theta)(S_a-S)+\theta(S-S_b+\delta_r)
 -2K_0\sqrt\varepsilon.
\tag{6.30}
$$

At $\theta=1/2$ the affine expression is
$\rho_p+\delta_r/2$. Its slope is $2(S-M_p)+\delta_r$, whose
absolute value is at most 3 since $S,M_p\in[0,1]$ and
$0<\delta_r\le1$. The target R is retained in (6.1), so
$\mathcal L_p(R)\le\rho_p+e$. Combining (6.29)--(6.30) gives

$$
\begin{aligned}
\frac{\delta_r}{2}
&\le\left(1+\frac3{2\rho_p}\right)e
 +\left(2+\frac3{2\rho_p}\right)K_0\sqrt\varepsilon\\
&\le\left(\frac{77}{2}+\frac{79}{2}\,5000000\right)
 \sqrt\varepsilon
 \le200000000\sqrt\varepsilon.
\end{aligned}
\tag{6.31}
$$

Together with (6.28), this implies
$\sqrt\varepsilon>1/(50000\cdot200000000)=10^{-13}$.
Thus $\varepsilon>10^{-26}$ in the considered case, proving the
non-strict bound (6.2). Its stated consequences follow directly from
nonnegativity and continuity of the square root. $\square$

**Mathematical citation 6.3 (the new joint estimate and its original
consumer).** The reference names for this chapter denote the following
immutable mathematical sources:

- [PAIR6](https://github.com/the-omega-institute/trureturing/blob/d36419c3785202d0152ec553eb8b362faa7e7a10/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md),
  Definition 11.2, Sections 11.4--11.8, (12.10), Chapter 14 and
  (20.13)--(20.15).
- [REV6](https://github.com/the-omega-institute/trureturing/blob/d36419c3785202d0152ec553eb8b362faa7e7a10/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md),
  (15.13)--(15.20), (16.21)--(16.26), Chapters 17--18.
- [PAID6](https://github.com/the-omega-institute/trureturing/blob/d36419c3785202d0152ec553eb8b362faa7e7a10/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md),
  Lemmas 2.1.1 and 14.1.

The unsupplied quantitative relation is the finite product transport
(6.12)--(6.16), paying the original risk's box errors, followed by the
slack and two-statistic bounds (6.18)--(6.27) on that same joint path.
They permit a direct original-risk consumer (6.30), without reconstructing
an entire comparison law. The result is a repo-derived ordinary
mathematical deduction. Endpoint geometry, Cauchy--Schwarz, the scalar
certificate, its Bernstein numerators and the supported-word gap are
credited inputs. No optimality or global priority assertion is made.

The expectation comparison used in (6.21) is the bounded right-continuous
supermodular comparison of Côté--Wang, *On convex order and supermodular
order without finite mean*, [Proposition 6 and Definition
3(iii)](https://arxiv.org/html/2502.17803v3). Its input here is a bounded
continuous clipped function on $\mathbb R^4$ and four identical
marginals. It supplies no quantitative equality stability; (6.22)--(6.27)
give the needed source-specific estimate. Leskelä--Vihola,
*Conditional convex orders and measurable martingale couplings*,
[Theorems 1.2--1.4](https://arxiv.org/html/1404.0999v3), concerns integrable
finite-dimensional vectors and their conditional couplings. The bounded
features satisfy that integrability condition, but those results do not
supply the seven-feature risk inequality or replace either complete
residual equation. Here both full flows are given, so no new martingale
coupling theorem is needed.

PAIR6 Chapter 14 already controls complete losses using the different
four-moment defect $2J_p+2J_\beta+M_A+M_B$. REV6 Chapters 17--18 already
compare complete-law branching with a graph-class risk minimum. Neither
input is replaced by the seven features in those statements. The present
finite-coordinate argument directly controls the two statistics needed
by (6.30); it requires neither a seven-feature upper bound for total-law
branching nor a new generator. Proposition 4.1 retains its delayed-branching
meaning. The qualitative exclusion and compactness argument of Corollary
3.1 supply no evaluated positive-variance neighborhood by themselves.

For correspondence with original operations, PAIR6 (11.24) pushes one
regular stationary table's two acquired flows to exactly the descriptors
used here, preserving the conditional full residuals, both unweighted
rows and configuration-before-TV losses. Feature discrepancies computed
on those label edges have exactly the integrals (2.2) after pushforward,
including when labels share a descriptor. PAID6 Lemma 14.1 supplies
common rows from positive finite paid histories for the same installed
finite or countable prior, with every supported depth retained. The
renderer and copied control preserve both seeds, paid rejections, partial
parses, held and written records, the third write before latch, fourth
completion, permissions, noncompletion and matching Stop. PAID6 Lemma
2.1.1 uses source-independent initialization and the same acquired and
synthetic update whenever an appropriate finite table is realized.
These are supplied interfaces, not a realization of the analytic path
(6.7). No artificial source reset or free persistent random tape is used.

A direct falsifier for (6.2) would be one pair satisfying both full
descriptor-conditioned equations and both common unweighted marginals,
with the stated installed support, whose exact all-supported objective
and seven variances obey $\mathcal J_\mu+\sqrt V<10^{-26}$.
Matching finitely many residual coordinates, or separately choosing two
feasible marginals, does not meet that condition. The nonendpoint-support
hypothesis is essential: for endpoint-only support, the supplied fair
matched native pair (2.4) has both exact full residuals, $V=0$ and
$\mathcal J_\mu=0$. Its zero excess follows from averaging the two endpoint
distances at each phase, not from exchanging TV and expectation.

The bound calibrates how close finite successor features can be to their
own residuals while the same flows approach all original target budgets.
It does not identify which of the seven coordinates has a positive floor.
It leaves $\mathcal J_\mu=0$ with $V\ge10^{-52}$ possible, supplies no
zero pair or vanishing family, and therefore does not decide the
unrestricted zero-versus-positive $j_c$ of Open problem 5.2. Finite
atomicity, finite exact attainment, permitted exact sampling and charged
COMPLETE remain separate obligations. Transport of this V from an
arbitrary unclipped observer through a comparison or clipping construction
is not proved; such a construction can change its own-law features,
marginals and actual return triples. No fixed resource or hard-defect
budget is asserted to be preserved.

## 追加锚（本行以下为后续增补区）
