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
