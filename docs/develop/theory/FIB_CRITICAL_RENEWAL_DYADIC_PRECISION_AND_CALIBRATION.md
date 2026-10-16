# Critical renewal testing: dyadic precision and midpoint calibration

## 1. Fixed laws and distinct resources

**Definition 1.1 (Parameters and mathematical correspondence).** Fix an
integer $r\ge1$, a real $c>0$ and $0<\alpha<1/2$. All constants below may
depend on this fixed triple. The common parameter $q=e^{-s}$ is known,
with $s>0$, and the two promised positive shapes are exactly

$$
F_0(k)=k^{2r-1},\qquad F_1(k)=k^{2r-1}+c k^{r-1}\quad(k\ge1).
\tag{1.1}
$$

Write [C] for
[RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_RENEWAL_LOGARITHMIC_FRONTIER.md][C].
Its Definitions 1.1–1.3 specify this same pair and resource contract;
Definition 3.1 supplies the capped phase reader, Theorem 4.1 its normalized
one-gap estimates, and Definition 5.1 its phase/evidence table. Its
Theorems 5.1, 6.1 and 7.1 already give the counted controller, complete
finite-budget order and eventual budget-growth criterion with unrestricted
real transition probabilities. The result here is a quantitative bridge
to finite dyadic rows and controlled midpoint calibration, retaining the
same listed configurations. The complete-budget frontier is used at its
existing scope, with its existing converse attribution.

Logarithms without a subscript are natural; $\mathrm e=\exp(1)$.
All claims concern the exact positive pair (1.1), rather than a tail
envelope or a class obtained by changing its normalizers.

**Definition 1.2 (Stationary first wait and subsequent complete gaps).**
For $i\in\{0,1\}$ put

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,&
f_i(k)&=F_i(k)q^k/Z_i(q)\quad(k\ge1),& f_i(0)&=0,\\
S_i(u)&=\sum_{k\ge u}f_i(k)\quad(u\ge0),&
\mu_i&=\sum_{k\ge1}(k+1)f_i(k),\\
\beta_i&=\frac{\sum_{k\ge1}k(k+1)f_i(k)}{2\mu_i}.
\end{aligned}
\tag{1.2}
$$

Draw $\tau$ with $\mathsf P_i(\tau=u)=S_i(u)/\mu_i$ for every integer
$u\ge0$. Independently draw iid $K_n\sim f_i$, $n\ge1$. The visible bits
$X_0,X_1,\ldots$ have ones exactly at

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{h=1}^n(K_h+1)\quad(n\ge1).
\tag{1.3}
$$

All other bits are zero. Thus $K_n$ counts zeros and $K_n+1$ includes
the closing one. The first wait is stationary and is not an iid $K_n$;
$S_i(0)=S_i(1)=1$, so $\tau=0$ is included. Nonnegative summation gives
$\sum_{u\ge0}S_i(u)=\mu_i$ and $\mathbb E_i\tau=\beta_i$. All fixed
polynomial moments are finite for $0<q<1$. These are precisely [C,
Definition 1.2]; the equilibrium-renewal correspondence there is
$S_2=K+1$, $S_1=\tau+1$ in Zamparo's notation.

**Definition 1.3 (One common direct dyadic table).** A table is chosen
before observation using the known $(q,r,c,\alpha)$ and a finite budget.
It has the same initialization and the same two input-conditioned rows
under both labels. It may retune with these parameters, without continuity
and without a common table across different $q$. For an integer $B\ge1$,
every installed probability is an integer multiple of $2^{-B}$, including
zero and one. Each nonterminal configuration reads exactly the next
actual bit and applies its installed stochastic row directly. Fresh
transition randomness is independent of the source and preceding fresh
randomness. Entry into $d_i$ internally emits label $i$ and stops.

Every mutable retained distinction counts in the complete persistent
configuration set: initialization, both labels, registers, control phases,
work buffers, retained seeds and random consequences. The observation is
one uninterrupted consecutive history (1.3). There is no additional
source-age, elapsed-time, read-count, horizon, program-counter, gap-length,
archive, random-tape or true-label input; no reset, skipped bit or free
complete-gap observation. A row formula specifies immutable entries and
provides no runtime arithmetic workspace. This restricts the probability
alphabet of [C, Definition 1.3] while keeping its complete-state and
actual-read contract.

If the consumed prefix is $X_0,\ldots,X_{T-1}$, its paid length is $T$.
Both error bounds, both almost-sure stops and both finite paid means
always refer to this one selected table. In particular, compliance means

$$
\mathsf P_0(D=1)\le\alpha,\quad
\mathsf P_1(D=0)\le\alpha,\quad
\mathsf P_i(T<\infty)=1,\quad \mathbb E_iT<\infty\quad(i=0,1).
\tag{1.4}
$$

**Definition 1.4 (Separate resource coordinates).** The complete
configuration count $M$, installed probability precision $B$, immutable
table description length, offline midpoint accuracy and paid time $T$
are distinct quantities. An offline midpoint of dyadic precision $Q$
and an offline parameter input of precision $P$ do not become runtime
registers. Thresholds, grid spacing and integer jump destinations are
fixed table-design data. If a different realization retains a precision
counter, arithmetic workspace, calibration value, residual, horizon,
seed, coin buffer or pending action, all its resulting complete
configurations must be counted separately. The direct stochastic-row
model does not supply a serial fair-coin realization or a physical
storage theorem.

## 2. Exact inherited premises

**Assumption 2.1 (Source and phase estimates from [C]).** Use the positive
constants $s_*,z_-,C_\mu,C_\beta$ of [C, equation (2.3)] and
$\eta\in(0,1)$, $D_0,D_1,C_1,C_2,V_0>0$ of [C, Theorem 4.1]. Choose
once $s_0\in(0,1)$ inside the neighborhoods of [C, Theorems 4.1, 5.1
and 6.1], with

$$
s_0\le\min\{\eta/2,s_*/2,1/2\}.
\tag{2.1}
$$

This choice precedes every cap, budget, precision and calibration choice.
Throughout the main statements $0<s<s_0$ and $J\ge1$ is any integer with
$s2^J\le\eta$. Set

$$
L=2^J,\qquad I=s^{2r}J,\qquad \delta=J/L^r.
\tag{2.2}
$$

The phase set is $\mathcal Z_J=\{1,\ldots,J,\dagger\}$. With initial
phase one, its zero matrix $R$ and reward vector $v$ are exactly [C,
Definition 3.1]:

$$
\begin{aligned}
R(j,j)&=1-2^{-j},& R(j,j+1)&=2^{-j}\quad(1\le j<J),\\
R(J,J)&=1-2^{-J},&R(J,\dagger)&=2^{-J},&R(\dagger,\dagger)&=1,\\
v_j&=2^{-rj}\quad(1\le j\le J),&&v_\dagger=0.
\end{aligned}
\tag{2.3}
$$

All unlisted matrix entries are zero. Conditional on the actual gap
$K=k$, the terminal phase has law $\mathbf e_1R^k$, and $V=v_z$ is its
one terminal reward. Put

$$
m_i=\mathbb E_iV
 =\frac{\sum_{k\ge1}F_i(k)e^{-sk}\mathbf e_1R^kv}{Z_i(e^{-s})},
\qquad \theta=(m_0+m_1)/2,\qquad \Delta=m_1-m_0.
\tag{2.4}
$$

The inherited estimates, for both exact source laws, are

$$
\begin{gathered}
Z_i(e^{-s})\ge z_-s^{-2r},\quad
\mu_i\le C_\mu/s,\quad 1+\beta_i\le C_\beta/s,\\
D_0I\le\Delta\le D_1I,\quad
0\le m_i\le C_1s^{2r}L^r,\quad \mathbb E_iV^2\le C_2I,\\
0\le V,\theta\le2^{-r},\qquad 0<\delta\le1/2.
\end{gathered}
\tag{2.5}
$$

For $x=v_z-\theta$, the ideal adjacent-grid increment $U$ takes
$\delta\lfloor x/\delta\rfloor$ and
$\delta(\lfloor x/\delta\rfloor+1)$ with probabilities giving mean $x$.
The exact source-normalized assertion [C, Theorem 4.1, equations
(4.3)–(4.4)] is

$$
\mathbb E_0U=-\Delta/2,\qquad
\mathbb E_1U=\Delta/2,\qquad
|U|\le1,\qquad \mathbb E_iU^2\le V_0I.
\tag{2.6}
$$

These are premises reused from [C], including its signed normalization
in equation (4.6) and its coarse-grid noise estimate (4.12). No independent
per-scale observations or independence of $K$ and $V$ is assumed. The
phase occupation theorem and the complete-budget converse retain their
original attribution; they are not additional results asserted here.

**Definition 2.2 (Unchanged threshold).** Keep the constants of [C,
Definition 5.1], writing $K_{\rm count}$ for its constant $K$:

$$
\lambda=\min\{1,D_0/(2\mathrm e V_0)\},\qquad
A=\frac{\log(1/\alpha)}\lambda,\qquad
K_{\rm count}=4A+4,\qquad H=\lceil A/\delta\rceil.
\tag{2.7}
$$

For later bounds put

$$
\kappa=\frac12-\frac1{4\mathrm e}>0,\qquad
C_{\rm fp}=C_\beta+
 \frac{C_\mu(A+3/2)}{\kappa D_0}.
\tag{2.8}
$$

## 3. Every configured row

**Definition 3.1 (Calibrated midpoint and finite-probability update).**
Choose an immutable $\widehat\theta\in[0,2^{-r}]$ and numbers
$\gamma,\epsilon\ge0$ with $|\widehat\theta-\theta|\le\gamma$.
For every phase, including $\dagger$, put

$$
\widehat t_z=(v_z-\widehat\theta)/\delta,\qquad
\widehat n_z=\lfloor\widehat t_z\rfloor,\qquad
\widehat p_z=\widehat t_z-\widehat n_z.
\tag{3.1}
$$

Choose $p_{B,z}\in[0,1]\cap2^{-B}\mathbb Z$ satisfying
$|p_{B,z}-\widehat p_z|\le\epsilon$. The unabsorbed one-gap increment
$U_B$, conditional on its terminal phase $z$, is

$$
U_B=\begin{cases}
\delta\widehat n_z,&\text{with probability }1-p_{B,z},\\
\delta(\widehat n_z+1),&\text{with probability }p_{B,z}.
\end{cases}
\qquad \chi=\gamma+\delta\epsilon.
\tag{3.2}
$$

The integer destinations and probabilities are selected from the two
promised laws before observation and installed identically under both
labels. In particular $\widehat\theta$ is not selected using the unknown
true source label.

**Definition 3.2 (Complete table and persistent state set).** Retain
exactly the configurations of [C, Definition 5.1]: $w,d_0,d_1$ and all

$$
(a,z),\qquad a\in\mathbb Z,\quad -H<a<H,\quad z\in\mathcal Z_J.
\tag{3.3}
$$

Initialize in $w$. For every integer $u$ set

$$
\Gamma(u)=\begin{cases}
d_1,&u\ge H,\\
d_0,&u\le-H,\\
(u,1),&-H<u<H.
\end{cases}
\tag{3.4}
$$

Every bit row is specified below.

| Configuration and read bit | Successors and probabilities |
| --- | --- |
| $w$, zero | $w$ with probability one |
| $w$, one | $(0,1)$ with probability one |
| $(a,j)$, zero, $1\le j<J$ | $(a,j)$ with probability $1-2^{-j}$; $(a,j+1)$ with probability $2^{-j}$ |
| $(a,J)$, zero | $(a,J)$ with probability $1-2^{-J}$; $(a,\dagger)$ with probability $2^{-J}$ |
| $(a,\dagger)$, zero | $(a,\dagger)$ with probability one |
| $(a,z)$, one, every $z\in\mathcal Z_J$ | $\Gamma(a+\widehat n_z)$ with probability $1-p_{B,z}$; $\Gamma(a+\widehat n_z+1)$ with probability $p_{B,z}$ |
| $d_0$, either bit | $d_0$ with probability one |
| $d_1$, either bit | $d_1$ with probability one |

Coincident destinations have their probabilities added. The label rows
specify unused future inputs; entry into a label already stops. Tick
rows following zero zeros are specified even when unreachable because
$K\ge1$. Nonterminal ticks reset the phase to one without resetting
the source. After phase death, every subsequent zero still performs its
paid read and holds in $(a,\dagger)$ until the actual closing one.

The only active retained distinctions are the finite integer coordinate
$a$ and phase $z$. Neither the real proof score nor a count of gaps,
reads, zero holding times or precision bits is a retained field. The
threshold comparison and jumps in (3.4) denote installed successors;
they are not runtime arithmetic subroutines or additional work phases.
The complete listed count is

$$
M_J=3+(2H-1)(J+1)
 =3+\bigl(2\lceil A2^{rJ}/J\rceil-1\bigr)(J+1).
\tag{3.5}
$$

All listed configurations count, regardless of reachability or probability.

## 4. Uniform perturbation theorem

**Theorem 4.1 (Dyadic rows and calibrated midpoint on one implementation).**
Under Assumption 2.1, for every allowed $s,J$, every integer $B\ge J$
and every choice in Definition 3.1 satisfying

$$
\chi\le\frac{D_0I}{4\mathrm e},
\tag{4.1}
$$

the single table of Definition 3.2 has all probabilities in
$2^{-B}\mathbb Z$ and meets every condition (1.4). Its exact count
is (3.5), with $M_J\le K_{\rm count}2^{rJ}$. For its actual one-gap
increment, write

$$
b_i=\mathbb E_iU_B-(m_i-\theta),\qquad \sigma_0=-1,\quad\sigma_1=1.
\tag{4.2}
$$

The signs $\sigma_i$ orient the proof only. The following bounds all
concern this same installed table:

$$
\begin{gathered}
|b_i|\le\chi,\qquad
\sigma_i\mathbb E_iU_B\ge\Delta/2-\chi\ge\kappa\Delta>0,\\
\left|\bigl(\mathbb E_1U_B-\mathbb E_0U_B\bigr)-\Delta\right|
 \le2\delta\epsilon,\qquad
\mathbb E_1U_B-\mathbb E_0U_B>0,\\
|U_B|\le1,\qquad
\operatorname{Var}_i(U_B)\le\mathbb E_iU_B^2
 \le V_0I+2\chi\le\left(V_0+\frac{D_0}{2\mathrm e}\right)I,\\
\mathbb E_0 e^{\lambda U_B}\le1,\qquad
\mathbb E_1 e^{-\lambda U_B}\le1.
\end{gathered}
\tag{4.3}
$$

If $G_B$ is the number of completed post-first-tick gaps through
absorption, then

$$
\begin{aligned}
\mathbb E_iG_B&\le\frac{A+3/2}{\kappa\Delta},\\
\mathbb E_iT&=1+\beta_i+\mu_i\mathbb E_iG_B\\
&\le\frac{C_\beta}s+
 \frac{C_\mu(A+3/2)}{\kappa D_0}\frac{s^{-(2r+1)}}J,\\
\max_i\mathbb E_iT&\le C_{\rm fp}\frac{s^{-(2r+1)}}J.
\end{aligned}
\tag{4.4}
$$

The neighborhood $s_0$ and constants are fixed before all caps, budgets
and calibrated tables. No assertion of unbiased finite-probability
rounding is required.

Proof. First, $B\ge J$ makes each $2^{-j}$ and its complement exactly
$B$-bit dyadic for $j\le J$. The deterministic rows, installed tick
probabilities and their complements have the same property. Summing
probabilities at merged successors preserves it. The reader therefore
has exactly the zero matrix $R$: conditional on every actual $K=k$,
its terminal phase law is still $\mathbf e_1R^k$. Only the tick update
has changed. Both labels use precisely these rows.

For the error estimates, let $U(x)$ denote ideal adjacent-grid rounding
of $x$ at spacing $\delta$, for $x\in[-2^{-r},2^{-r}]$. Its endpoints
are $\ell=\delta\lfloor x/\delta\rfloor$ and $\ell+\delta$.
Both lie in $[-1,1]$, since $|x|\le1/2$ and $\delta\le1/2$.
For $\varsigma\in\{-1,1\}$ define

$$
F_\varsigma(x)=\mathbb E e^{\varsigma\lambda U(x)},\qquad
W(x)=\mathbb E U(x)^2.
\tag{4.5}
$$

On each grid cell $F_\varsigma$ is the linear interpolant of
$e^{\varsigma\lambda u}$ at its endpoints. Its slope has absolute
value at most $\mathrm e\lambda$, by the mean-value theorem,
$\lambda\le1$ and the endpoint bound. The interpolants agree at grid
points, so they are continuous there. Partitioning an interval at its
finitely many grid crossings proves the global bound

$$
|F_\varsigma(x)-F_\varsigma(y)|
 \le\mathrm e\lambda|x-y|.
\tag{4.6}
$$

Likewise $W$ is the continuous linear interpolant of $u^2$. Its slope
on a cell is $\ell+(\ell+\delta)$, of absolute value at most two.
Thus $|W(x)-W(y)|\le2|x-y|$ throughout this interval. These bounds
apply across changed floor cells, as well as at a grid boundary.

At phase $z$, changing the center from $\theta$ to $\widehat\theta$
changes $x=v_z-\theta$ by at most $\gamma$. At the new center, changing
the upper-endpoint probability by at most $\epsilon$ changes the mean
by at most $\delta\epsilon$, the exponential expectation by at most
$\mathrm e\lambda\delta\epsilon$, and the second moment by at most
$2\delta\epsilon$. The last two statements follow by multiplying
the probability error by the difference of the two endpoint function
values. Combining these observations gives, conditional on each phase,
an exponential error at most $\mathrm e\lambda\chi$ and a second-moment
error at most $2\chi$. Averaging over either unchanged terminal-phase
law preserves the bounds. In particular,

$$
\begin{aligned}
\left|\mathbb E_i e^{\varsigma\lambda U_B}
      -\mathbb E_i e^{\varsigma\lambda U}\right|
 &\le\mathrm e\lambda\chi,\\
\left|\mathbb E_iU_B^2-\mathbb E_iU^2\right|&\le2\chi.
\end{aligned}
\tag{4.7}
$$

This comparison uses the actual gap/phase joint law. It adds no
unconditional $\delta^2$ noise per gap and assumes no independence
between a reward and its duration.

Write $h_z=p_{B,z}-\widehat p_z$, so $|h_z|\le\epsilon$. The actual
conditional mean, including its possible bias, is exactly

$$
\mathbb E(U_B\mid z)=v_z-\widehat\theta+\delta h_z,
\qquad
\mathbb E_iU_B=m_i-\widehat\theta+\delta\mathbb E_i h_z.
\tag{4.8}
$$

Consequently $b_i=\theta-\widehat\theta+\delta\mathbb E_i h_z$ has
absolute value at most $\chi$. The common displacement
$\theta-\widehat\theta$ cancels on subtracting the two means; hence
the contrast error is at most $2\delta\epsilon$, rather than requiring
the weaker $2\chi$. Since $D_0I\le\Delta$, (4.1) gives
$\chi\le\Delta/(4\mathrm e)$. It follows that both oriented drifts
are at least $\kappa\Delta$ and that the contrast is at least
$\Delta-2\delta\epsilon\ge\Delta(1-1/(2\mathrm e))>0$.
The support bound applies also at the new center, proving $|U_B|\le1$;
(2.6) and (4.7) prove the second-moment and variance bounds.

For clarity, the strictly negative ideal exponential margin used here
is [C, equation (5.12)]. It follows internally from (2.6): for
$|u|\le1$, Taylor's integral remainder gives

$$
e^{\lambda u}\le1+\lambda u+
 \frac{\mathrm e}{2}\lambda^2u^2.
\tag{4.9}
$$

Under source zero, (2.7) yields

$$
\mathbb E_0 e^{\lambda U}
 \le1-\lambda\Delta/2+(\mathrm e/2)\lambda^2V_0I
 \le1-\lambda D_0I/4.
\tag{4.10}
$$

The same inequality holds under source one for $e^{-\lambda U}$.
Equation (4.7) consumes at most this margin because
$\mathrm e\lambda\chi\le\lambda D_0I/4$. This proves both actual
exponential inequalities in (4.3), for the very probabilities already
used for the drift bounds.

Next establish finite absorption before using any infinite stopping
limit. On an analytical continuation of the same source history, use
the iid post-first-tick gaps and independent fresh phase/tick randomness
to form iid potential pairs $(K_n,U_{B,n})$. These pairs are independent
of $\tau$, but their two coordinates need not be independent. The phase
resets to one at each nonterminal tick, and its tick-increment law is
independent of $a$. Thus the potential process agrees with the installed
table until it exits. Let $\mathcal F_n$ contain $\tau$ and the first
$n$ whole gap/coin blocks. Put, for proof purposes only,

$$
S_0^{\rm sc}=0,\qquad S_n^{\rm sc}=\sum_{h=1}^nU_{B,h},\qquad
G_B=\inf\{n\ge1:|S_n^{\rm sc}|\ge H\delta\}.
\tag{4.11}
$$

Before exit the retained evidence coordinate is $S_n^{\rm sc}/\delta$;
at exit $\Gamma$ emits exactly the corresponding boundary label.
The score and its terminal overshoot are proof variables, not extra
configurations or a stopping-time decoder. For every finite $m$,

$$
|S_{G_B\wedge m}^{\rm sc}|\le H\delta+1
 \le A+3/2.
\tag{4.12}
$$

Here $H\delta\le A+\delta$ and each increment has magnitude at most one.
The inclusion event $\{G_B\ge n\}$ lies in $\mathcal F_{n-1}$.
Finite conditional expectation therefore gives, with
$d_i=\sigma_i\mathbb E_iU_B\ge\kappa\Delta$,

$$
\begin{aligned}
\mathbb E_i[\sigma_i S_{G_B\wedge m}^{\rm sc}]
 &=\sum_{n=1}^m\mathbb E_i[
   \mathbf1_{\{G_B\ge n\}}\sigma_iU_{B,n}]\\
 &=d_i\sum_{n=1}^m\mathsf P_i(G_B\ge n)
 =d_i\mathbb E_i(G_B\wedge m)\le A+3/2.
\end{aligned}
\tag{4.13}
$$

Monotone convergence proves
$\mathbb E_iG_B\le(A+3/2)/(\kappa\Delta)<\infty$, and hence
$G_B<\infty$ almost surely under both labels. Every gap and the first
wait are almost surely finite. Actual stopping is therefore almost
surely finite as well. This argument does not presume that the rounded
transition graph retains an ideal absorption property.

Under source zero,
$\exp(\lambda S_{G_B\wedge m}^{\rm sc})$ is a nonnegative
supermartingale starting at one; under source one use
$\exp(-\lambda S_{G_B\wedge m}^{\rm sc})$. The conditional inequalities
follow from (4.3) for the next independent block on the event not yet
stopped, and equality holds after stopping. Bound (4.12) gives a common
upper bound $\exp(\lambda(A+3/2))$. The already proved finite $G_B$
allows bounded convergence, so the terminal exponential expectations
are at most one. At the respective wrong exits their values are at
least $\exp(\lambda H\delta)$. Consequently

$$
\mathsf P_0(D=1),\ \mathsf P_1(D=0)
 \le e^{-\lambda H\delta}\le e^{-\lambda A}=\alpha.
\tag{4.14}
$$

This is the bounded-stopped exponential-supermartingale argument
corresponding to [C, equations (5.11)–(5.13)]; neither sign $\sigma_i$
is an executable source-label input.

For actual payment there is the pathwise identity

$$
T=1+\tau+\sum_{n=1}^{G_B}(K_n+1).
\tag{4.15}
$$

It includes every initial zero, the initial one, every phase-holding
zero, all zeros after phase death and the final closing one. This table
has no terminal partial interval, because it stops directly at a tick;
the general competitor contract still charges such partial intervals
when a different table undertakes them. Since $\{G_B\ge n\}$ is
measurable before block $n$, it is independent of its next $K_n$.
Tonelli gives

$$
\begin{aligned}
\mathbb E_i\sum_{n=1}^{G_B}(K_n+1)
 &=\sum_{n\ge1}\mathbb E_i[
    \mathbf1_{\{G_B\ge n\}}(K_n+1)]\\
 &=\mu_i\sum_{n\ge1}\mathsf P_i(G_B\ge n)
 =\mu_i\mathbb E_iG_B.
\end{aligned}
\tag{4.16}
$$

No independence of the deciding increment from its own interval is
used. This is the predictable completed-gap payment of [C, equations
(5.14)–(5.15)], now for the implemented stopping law. Combining it with
(2.5) and (4.13) proves the first three lines of (4.4) and finite paid
means. For every allowed cap,

$$
I=s^{2r}J\le s^{2r}L^r\le\eta^rs^r\le1.
\tag{4.17}
$$

Thus $C_\beta/s\le C_\beta s^{-(2r+1)}/J$, yielding the last line.

Finally, direct counting gives exactly (3.5). The threshold, grid and
phase set have not changed, so [C, equation (5.17)] applies unchanged:
using $H\le AL^r/J+1$, $J+1\le2J$ and $J+1\le L^r$,

$$
M_J\le3+(2AL^r/J+1)(J+1)
 \le3+4AL^r+L^r\le(4A+4)L^r.
\tag{4.18}
$$

Changed floors can change installed tick destinations but introduce no
configuration. This completes every assertion. $\square$

**Corollary 4.2 (Comparison of explicit upper bounds).** The explicit
gap-count upper in Theorem 4.1 is $1/(2\kappa)=2\mathrm e/(2\mathrm e-1)$
times the ideal upper $2(A+3/2)/\Delta$ in [C, Theorem 5.1]. This
comparison does not bound the ratio of the two actual mean stopping
times.

Proof. Divide the two displayed upper bounds. They are upper bounds
for different stopping laws, so this division alone gives no comparison
of the actual expectations. $\square$

## 5. Explicit sufficient precision

**Theorem 5.1 (Sufficient $B_0,Q_0$ and a midpoint certificate).** For
every allowed $s,J$, it suffices to choose integers

$$
\begin{aligned}
B&\ge B_0(s,J):=
 \max\left\{J,\left\lceil
 \log_2\frac{8\mathrm e}{D_0s^{2r}2^{rJ}}
 \right\rceil\right\},\\
Q&\ge Q_0(s,J):=
 \max\left\{r,\left\lceil
 \log_2\frac{8\mathrm e}{D_0s^{2r}J}
 \right\rceil\right\}.
\end{aligned}
\tag{5.1}
$$

Take a dyadic $\widehat\theta\in[0,2^{-r}]$ of denominator dividing
$2^Q$ with $|\widehat\theta-\theta|\le2^{-Q}$ and set

$$
p_{B,z}=2^{-B}\lfloor2^B\widehat p_z\rfloor.
\tag{5.2}
$$

Such a midpoint exists, for instance the downward $Q$-bit rounding of
$\theta$. The resulting table satisfies Theorem 4.1. More generally,
with $B\ge B_0$ any certified midpoint in the stipulated interval with

$$
|\widehat\theta-\theta|\le\frac{D_0s^{2r}J}{8\mathrm e}
\tag{5.3}
$$

is sufficient with (5.2). The certificate is an absolute error bound for
the known mathematical laws, not empirical calibration of an unknown
parameter. If each of two mean approximations has absolute error at
most $\gamma$, their average has midpoint error at most $\gamma$.

Proof. Because $Q\ge r$, both endpoints of $[0,2^{-r}]$ are on the
$Q$-bit grid. Downward rounding stays in that interval and has error
less than or equal to $2^{-Q}$. Formula (5.2) stays in $[0,1]$ and has
error at most $2^{-B}$, including $\widehat p_z=0$. From (5.1),

$$
\delta2^{-B}\le\frac{D_0I}{8\mathrm e},\qquad
2^{-Q}\le\frac{D_0I}{8\mathrm e}.
\tag{5.4}
$$

The sum is the allowance (4.1), and $B\ge J$ preserves the phase rows.
The same argument uses (5.3) directly in place of the second inequality.
For approximate means, the triangle inequality bounds the error of
their average by the average of their errors. $\square$

**Definition 5.2 (Existence rounding and effective calibration).** Exact
downward rounding of an arbitrary known real specifies an existing
midpoint; it does not by itself give a uniform effective procedure for
deciding equality to a dyadic boundary. An effective calibrator may
instead choose any certified dyadic approximation satisfying (5.3).
The precision $Q$ prices an offline value, not an additional denominator
for the installed probability rows and not a retained runtime field.
The finite midpoint expression and the effective-parameter distinction
are given in Theorem 6.1.

**Corollary 5.3 (Orders of the sufficient precisions).** Uniformly over
all allowed caps, $B_0,Q_0=O(\log(1/s))$. For any fixed $J\ge1$,

$$
B_0=2r\log_2(1/s)+O(1).
\tag{5.5}
$$

At the full allowed cap $J=\lfloor\log_2(\eta/s)\rfloor$,

$$
B_0=r\log_2(1/s)+O(1),\qquad
Q_0=2r\log_2(1/s)-\log_2J+O(1).
\tag{5.6}
$$

These are sufficient bounds for this construction. They assert neither
least precision nor a necessary precision-versus-state tradeoff.

Proof. Allowed caps obey $1\le J\le\log_2(\eta/s)$, and each logarithm
in (5.1) is at most $2r\log_2(1/s)$ plus a fixed constant. This proves
the uniform upper orders. For fixed $J$, the second argument of the
maximum defining $B_0$ eventually dominates its fixed first argument,
giving (5.5). At full cap, $J=\log_2(1/s)+O(1)$ and
$rJ=r\log_2(1/s)+O(1)$. Substitution in the logarithms in (5.1), with
ceilings changing them by at most one, gives (5.6); the maximum with
$J$ preserves the stated $B_0$ formula also for $r=1$. The $Q_0$
logarithm eventually dominates $r$. $\square$

## 6. Finite calibration formulas and known-parameter accuracy

**Theorem 6.1 (Finite rational midpoint and effective-parameter boundary).**
For each finite $J$ keep the matrix and vector (2.3), and define

$$
\mathcal D_q=q\frac{d}{dq},\qquad
C(q)=qR(\operatorname{Id}-qR)^{-1},\qquad
C_m(q)=\mathcal D_q^m C(q),\qquad
z_m(q)=\mathcal D_q^m\frac q{1-q}.
\tag{6.1}
$$

Then the exact means in (2.4), for every $0<q<1$, are

$$
\begin{aligned}
m_0&=\frac{\mathbf e_1C_{2r-1}(q)v}{z_{2r-1}(q)},\\
m_1&=\frac{\mathbf e_1\bigl(C_{2r-1}(q)+cC_{r-1}(q)\bigr)v}
 {z_{2r-1}(q)+cz_{r-1}(q)}.
\end{aligned}
\tag{6.2}
$$

They and $\theta=(m_0+m_1)/2$ are finite rational expressions in $q,c$
with dyadic matrix/vector coefficients, and their stipulated denominators
do not vanish. For computably supplied $q,c$ they allow finite certified
interval evaluation to any prescribed positive absolute tolerance.
For arbitrary known reals this is an existence and calibration
specification; it supplies neither a uniform effective encoding of
noncomputable parameters nor a bit-operation complexity bound.

Proof. Stochasticity gives $\|R^k\|_\infty=1$. Hence for $0<q<1$
the matrix Neumann series converges, proves invertibility, and yields

$$
C(q)=\sum_{k\ge1}q^kR^k.
\tag{6.3}
$$

On every compact interval below one and above zero the series obtained
by any fixed number of derivatives is uniformly absolutely convergent:
its terms are bounded by a fixed polynomial in $k$ times a geometric
sequence. Termwise Euler differentiation therefore gives

$$
C_m(q)=\sum_{k\ge1}k^m q^kR^k,\qquad
z_m(q)=\sum_{k\ge1}k^m q^k.
\tag{6.4}
$$

Substitution of the exact shapes (1.1) in (2.4) proves (6.2). The scalar
normalizers are strictly positive, and $\operatorname{Id}-qR$ is
invertible. Matrix inversion, finitely many derivatives and arithmetic
give finite rational expressions. Since all powers $2^{-j}$ and
$2^{-rj}$ are dyadic, the claimed coefficient description follows.

For computable $q,c$, refine their certified rational intervals until
the $q$ interval lies inside $(0,1)$ and the nonzero denominators have
interval bounds separated from zero. This eventually succeeds by the
nonvanishing just proved and continuity. Further interval refinement
then evaluates the finite rational expression to any positive requested
tolerance. A sufficiently fine dyadic approximation, clipped to
$[0,2^{-r}]$, supplies a certificate of the form (5.3), without deciding
an exact floor equality of the true midpoint. This finite evaluation
argument puts no uniform bound on the cost of obtaining parameter
intervals, derivatives or the desired tolerance. $\square$

**Theorem 6.2 (Optional $s$-input accuracy at a fixed design cap).** Keep
$c$ fixed and exact. Use $B_m=\mathrm e(m+1)!2^{m+1}$ from [C,
Theorem 3.2, equation (3.4)] and $z_-$ from its equation (2.3). Define

$$
\begin{aligned}
C_K&=\frac{(1+c)B_{2r}}{z_-(1-2^{-(r+1)})},\\
C_{\rm cal}&=(3/2)^{2r-1}
 \left[C_1C_\mu+(3\eta/2)C_K\right],\\
\rho&=\min\left\{\frac s2,
 \frac{D_0sJ}{16\mathrm e C_{\rm cal}L^r}\right\}.
\end{aligned}
\tag{6.5}
$$

For any $\widehat s>0$ with $|\widehat s-s|\le\rho$,

$$
|\theta(\widehat s,J)-\theta(s,J)|\le\frac{D_0I}{16\mathrm e}.
\tag{6.6}
$$

If an approximation to $\theta(\widehat s,J)$ has additional absolute
error at most $D_0I/(16\mathrm e)$, clipping it to $[0,2^{-r}]$ gives
total midpoint error at most $D_0I/(8\mathrm e)$. Combined with $B_0$
this meets Theorem 4.1. The cap $J$, error budgets and allowed-cap
condition here are stated in terms of the true $s$; this assertion
alone does not certify a design that chooses all its caps, budgets or
constants from uncertain input.

Proof. The upper occupation proof in [C, Theorem 3.2, equations
(3.9)–(3.10)] drops $e^{-uk}$. Consequently its upper

$$
A_j^{(m)}(u)\le B_m2^{j(m+1)}
\tag{6.7}
$$

holds for every $u>0$, regardless of $u2^J\le\eta$. This cutoff-free
upper, $F_i(k)\le(1+c)k^{2r-1}$ and the normalizer lower in [C,
equation (2.3)] imply, for every $0<u<s_*$ at this fixed $J$,

$$
\begin{aligned}
m_i(u,J)&\le C_1u^{2r}L^r,\\
\mathbb E_{i,u}[VK]
 &\le\frac{1+c}{z_-}u^{2r}
    \sum_{j=1}^J2^{-rj}B_{2r}2^{j(2r+1)}
 \le C_Ku^{2r}L^{r+1}.
\end{aligned}
\tag{6.8}
$$

The first constant is the same $C_1$ in [C, equation (4.10)]; its
proof uses only this upper, so the extension does not assert a contrast
lower beyond the permitted cutoff. The second geometric sum is at most
$L^{r+1}/(1-2^{-(r+1)})$. Differentiation of the normalized source law
at fixed $J$ gives

$$
\frac{d}{du}m_i(u,J)
 =-\mathbb E_{i,u}[VK]+m_i(u,J)\mathbb E_{i,u}K.
\tag{6.9}
$$

Indeed the unnormalized terms have derivative $-k$ times themselves,
and differentiating the denominator supplies the second term. All such
derivatives are justified by locally dominated polynomial-geometric
sums. The phase law conditional on $K$ is fixed as $u$ varies.
Using $\mathbb E_{i,u}K\le\mu_i(u)\le C_\mu/u$ in (6.8) yields

$$
\left|\frac{d}{du}m_i(u,J)\right|
 \le u^{2r-1}L^r\left[C_1C_\mu+C_KuL\right].
\tag{6.10}
$$

The same bound holds for the midpoint derivative, by averaging the two
absolute bounds. For every intermediate $u$ between $s$ and $\widehat s$,
$s/2\le u\le3s/2<s_*$ by (2.1), and $uL\le3\eta/2$.
Equation (6.10) is therefore at most
$C_{\rm cal}s^{2r-1}L^r$. Integrating over an interval of length at
most $\rho$ proves (6.6). Adding the evaluation error gives twice the
right side. Clipping cannot increase distance to $\theta(s,J)$, which
lies in the clipping interval. This proves the total-error assertion.
It uses (5.3) directly and does not identify that split error budget
with the separate exact-midpoint $Q$-bit prescription. $\square$

**Corollary 6.3 (Optional dyadic $q$-input accuracy).** With the same
fixed-$J$ interpretation, it suffices that

$$
|\widehat q-q|\le q\rho/2.
\tag{6.11}
$$

Then $0<\widehat q<1$ and $\widehat s=-\log\widehat q$ meets
Theorem 6.2. In particular a certified dyadic input with absolute
error at most $2^{-P}$ suffices when

$$
P\ge\left\lceil\log_2\frac2{q\rho}\right\rceil.
\tag{6.12}
$$

The displayed sufficient input precision is
$(r+1)\log_2(1/s)-\log_2J+O(1)$ at full cap, and
$\log_2(1/s)+O(1)$ for fixed $J$. It is separate from $B$ and $Q$.

Proof. Since $\rho\le s/2$ and $s<1$, (6.11) gives
$\widehat q\ge q/2>0$. Also
$1-q=q(e^s-1)\ge qs>q\rho/2$, so the input cannot cross one.
The derivative of $\log$ on the interval between $q$ and $\widehat q$
has magnitude at most $2/q$. Thus

$$
|-\log\widehat q-s|\le2|\widehat q-q|/q\le\rho.
\tag{6.13}
$$

Condition (6.12) ensures (6.11). For fixed $J$, (6.5) makes $\rho$
a fixed positive multiple of $s$, up to its minimum with $s/2$.
At full cap $L^r$ is within fixed positive factors of $s^{-r}$ and
$J\asymp\log(1/s)$, so the second branch eventually determines $\rho$
and $\rho\asymp s^{r+1}J$. Since $q=e^{-s}$ stays bounded away from
zero, the two orders follow. These are deterministic sufficient input
bounds with exact fixed $c$, not an unknown-$q$ testing or estimation
result. $\square$

**Theorem 6.4 (Literal immutable-table description upper).** Number all
$M_J$ configurations of Definition 3.2. A literal description of their
two bit rows uses at most

$$
2M_J\left[2\lceil\log_2M_J\rceil+B+1\right]
\tag{6.14}
$$

bits, plus a header specifying the format, dimensions and distinguished
states. This is a description upper for an immutable dyadic table.
It is neither a minimal encoding nor a lower bound on storage or on
complete runtime configurations.

Proof. Each row has at most two successor indices and one numerator
in $\{0,\ldots,2^B\}$. Each successor needs
$\lceil\log_2M_J\rceil$ bits and the numerator needs $B+1$ bits;
its complementary probability is inferred. A deterministic row may
repeat its successor. There are two rows per configuration, including
the two labels, giving (6.14). The installed indices and probabilities
already specify all midpoint-dependent consequences; $Q$, $P$ and the
midpoint itself need not be runtime fields or additional row entries.
This accounting makes no assertion that a direct stochastic row can
be executed with serial coins without further configuration or time
cost. $\square$

## 7. Transfer of the existing complete-budget result

**Assumption 7.1 (The credited complete-budget interfaces).** Write
$\mathfrak A_M(e^{-s},\alpha)$ for the unrestricted-probability class
of [C, Definition 1.3], with the same complete-state, common-table,
stationary-wait and paid-read contract. Put

$$
\begin{aligned}
b&=1-2\alpha,\\
L_M&=\max\left\{1,
 \left\lceil\left(\frac{2c(M-2)}b\right)^{1/r}\right\rceil\right\},\\
\Psi(s,M)&=\frac{s^{-(2r+1)}}{1+\log\min\{L_M,1/s\}}.
\end{aligned}
\tag{7.1}
$$

The inherited converse is [C, Definition 2.2 and Theorem 6.1]: a fixed
$C_->0$ satisfies, for every finite integer $M\ge2$, every compliant
competitor and each $i$,

$$
\mathbb E_iT\ge C_-\Psi(s,M)\quad(0<s<s_0).
\tag{7.2}
$$

It retains [C]'s credit to the renewal state/read source, Theorem 11.2
and Open problem 11.3, including its finite-configuration, normalized
entropy and actual tick-price premises. It covers arbitrary stochastic
retuning, initial randomization, arbitrarily small positive edges and
partial-gap stopping under the full contract. No new converse is assumed
from the shape of the particular table in Section 3.

Also reuse exactly [C, Theorem 6.1, equations (6.2)–(6.4)]. With
$M_0=\lceil K_{\rm count}2^r\rceil$, for every finite $M\ge M_0$
the immutable cap choice

$$
J=\left\lfloor\log_2
 \min\{(M/K_{\rm count})^{1/r},\eta/s\}\right\rfloor
\tag{7.3}
$$

satisfies $J\ge1$, $s2^J\le\eta$, $K_{\rm count}2^{rJ}\le M$ and

$$
1+\log\min\{L_M,1/s\}\le C_3J
\tag{7.4}
$$

for a fixed $C_3>0$. These are existing uniform budget-selection
statements, rather than newly derived frontiers.

**Theorem 7.2 (Precision-provisioned dyadic subclass).** For every
$0<s<s_0$ and finite integer $M\ge M_0$, choose $J$ by (7.3), any
$B\ge B_0(s,J)$ and a midpoint meeting (5.3), with rows (5.2).
The resulting one common dyadic table has at most $M$ complete
configurations and satisfies

$$
\max_i\mathbb E_iT\le C_{\rm fp}C_3\Psi(s,M).
\tag{7.5}
$$

Every compliant dyadic table with at most $M$ configurations still obeys
(7.2). Thus the existing complete-budget order transfers to dyadic
tables when sufficient transition precision and midpoint accuracy are
available. This statement does not characterize a separately imposed
insufficient joint $(M,B)$ budget.

Proof. The inherited selection facts ensure that Theorems 4.1 and 5.1
apply and that their unchanged state count is at most $M$. By (7.4),
$C_{\rm fp}s^{-(2r+1)}/J\le C_{\rm fp}C_3\Psi(s,M)$, proving
the upper on one common table. Dyadic tables are a subclass of the
unrestricted competitors in Assumption 7.1, so its lower applies
unchanged. No selection argument or universal lower is being claimed
as a new result. $\square$

**Corollary 7.3 (Inherited eventual-growth criterion with sufficient
precision).** Let $M(s)\ge2$ be any finite integer-valued function,
without monotonicity or regularity assumptions. When finite dyadic
precision and calibration may be provisioned as in Theorem 7.2, the
following conditions are equivalent:

1. There are $C_T<\infty$ and $s_1>0$ such that for every $0<s<s_1$
   there exists one common compliant dyadic table at budget $M(s)$
   with both paid means at most $C_Ts^{-(2r+1)}/\log(\mathrm e/s)$.
2. The same statement holds for one fixed $i_\star\in\{0,1\}$ in the
   paid upper, while still requiring both risks, both almost-sure stops
   and both finite paid means for each chosen table.
3. There are $\varepsilon_*>0$ and $s_2>0$ such that
   $\log(1+M(s))\ge\varepsilon_*\log(1/s)$ for every $0<s<s_2$.

Each neighborhood is restricted to $s<1$ and the budget function's
domain. The equivalence is the precision-provisioned transfer of [C,
Theorem 7.1], not a new necessary state-growth or precision theorem.

Proof. Condition 1 implies 2. Any tables in condition 2 are admissible
unrestricted tables, so necessity in [C, Theorem 7.1] implies condition
3 with all opposing compliance conditions retained. Conversely,
condition 3 makes $M(s)\ge M_0$ eventually. The same theorem, equation
(7.2), supplies $c_*>0$ with
$1+\log\min\{L_{M(s)},1/s\}\ge c_*\log(\mathrm e/s)$ eventually.
Theorem 7.2 then provides dyadic tables satisfying condition 1 with
$C_T=C_{\rm fp}C_3/c_*$. This reasoning applies to every sufficiently
small $s$, including oscillating budgets and discontinuous retuning.
$\square$

**Corollary 7.4 (Full cap and sufficient exponents).** With sufficient
precision, the full cap $J_s=\lfloor\log_2(\eta/s)\rfloor$ has exactly
$M_{J_s}$ listed configurations, at most $K_{\rm count}(\eta/s)^r$,
and both paid means of order at most
$s^{-(2r+1)}/\log(\mathrm e/s)$. Every fixed positive polynomial budget
exponent also suffices for this paid order, with a constant depending
on that exponent; the construction's exponent $r$ is not necessary.

Proof. The count follows from Theorem 4.1 and $2^{J_s}\le\eta/s$;
$J_s\asymp\log(\mathrm e/s)$ gives its paid upper. For any
$\zeta>0$, $M(s)=\lceil s^{-\zeta}\rceil$ satisfies condition 3 of
Corollary 7.3, for example with any fixed $0<\varepsilon_*<\zeta$.
Its budget-selected cap, not necessarily its full cap, therefore gives
the same paid order. This reuses [C, Corollary 7.2] with the added
precision provision. $\square$

## 8. Boundary instances and construction-specific failures

**Theorem 8.1 ($J=1$ and all grid boundaries).** Theorem 4.1 includes
$J=1$, $L=2$, $\delta=2^{-r}$ and exact count $M_1=4H+1$. Its
sufficient precisions are (5.1) with these values, in particular

$$
B_0(s,1)=\max\left\{1,
 \left\lceil\log_2\frac{8\mathrm e}{D_0s^{2r}2^r}\right\rceil\right\}.
\tag{8.1}
$$

This cap has no growing logarithmic gain. Grid equalities,
$\widehat p_z=0$, changed integer floors, the dead phase and merged
successors require no exclusion from the theorem.

Proof. Substitute $J=1$ in (2.2), (3.5) and (5.1). The paid upper
is $C_{\rm fp}s^{-(2r+1)}$, without a growing $J$ denominator.
At an exact grid point the ideal adjacent-grid law puts probability
zero on its upper endpoint. Formula (5.2) keeps this zero; the more
general perturbation theorem permits any admissible error there.
The interpolants (4.5) agree at each grid point and their global
Lipschitz bounds cross any number of changed floors. They include
$v_\dagger=0$. Merging two successors only adds their probabilities
and does not change the law of the emitted label or retained successor.
The potential unabsorbed increments remain valid proof variables even
when their exits merge at the same label. All zero and one rows are
specified, including unreachable input edges; none is deleted from the
count. These observations verify every listed boundary case. $\square$

**Theorem 8.2 (Failure of fixed-$B$ nearest rounding for this table).**
Fix $J=1$ and any integer $B\ge1$. Keep the exact ideal midpoint
$\theta$ and the threshold $H$ of (2.7), and replace each ideal tick
probability by its nearest $B$-bit dyadic probability. For every
sufficiently small $s>0$ this rounded table stops almost surely with
finite paid mean under both sources but emits label one under both.
In particular $\mathsf P_0(D=1)=1$. This is a failure of this specific
rounding prescription, not a necessary precision lower for all dyadic
controllers.

Proof. At $J=1$ there is a live phase of reward $\delta=2^{-r}$ and a
dead phase of reward zero. Conditional on $K=k$, the live probability
is $2^{-k}$. Hence

$$
a_i:=\mathsf P_i(z=1)=\mathbb E_i2^{-K}>0,\qquad
m_i=\delta a_i>0.
\tag{8.2}
$$

The fixed-cap upper in (2.5) implies $m_i\to0$ and thus
$\theta/\delta\to0$ as $s\downarrow0$. For sufficiently small $s$,

$$
0<\theta/\delta<2^{-(B+1)}.
\tag{8.3}
$$

Write $a=\theta/\delta$. In the live phase the normalized ideal input
is $1-a$, of floor zero; in the dead phase it is $-a$, of floor minus
one. In both cases the upper-endpoint probability is $1-a$. By (8.3)
its unique nearest $B$-bit dyadic is one, with no tie at a rounding
boundary. Consequently the live increment becomes $+\delta$ and the
dead increment becomes zero. The $J=1$ zero probabilities are already
exact for $B\ge1$.

All increments are nonnegative. Each completed gap supplies an iid
live indicator with success probability $a_i>0$, since the phase
restarts at one and fresh randomness is independent across gaps.
The table reaches evidence $+H$ after $H$ live successes. To see
finite mean directly, each waiting number of gaps for the next success
has tail $(1-a_i)^n$, so its mean is
$\sum_{n\ge0}(1-a_i)^n=1/a_i$. Independence of the successive blocks
gives $\mathbb E_iG=H/a_i<\infty$, and $G<\infty$ almost surely.
The predictable payment proof (4.15)–(4.16) applies to these same blocks,
giving $\mathbb E_iT=1+\beta_i+\mu_iH/a_i<\infty$.
There is no negative exit, so the emitted label is one with probability
one under either source. This proves the risk failure despite finite
stopping and despite the row error $a\to0$. It imposes no restriction
on other table designs or alternative rounding rules. $\square$

**Theorem 8.3 (An inadequately centered instance).** In the same $J=1$
construction, setting $\widehat\theta=0$ gives the identical risk
failure even with exact adjacent-grid probabilities. Thus finite
stopping and small probability-rounding error do not replace a
midpoint guarantee relative to the shrinking signal.

Proof. The live normalized input is now one, of floor one and
fractional part zero. Its increment is $+\delta$ deterministically.
The dead input is zero, of floor and fractional part zero, and its
increment is zero. These are exactly the increments in Theorem 8.2,
so its live-success and predictable-payment argument proves finite
paid stopping and label one under both laws. In particular the tick
probability error can be zero while source-zero risk is one.
The actual midpoint error is $\gamma=\theta$, which is not covered by
the robustness allowance: since $m_0>0$,
$\theta=(m_0+m_1)/2>\Delta/2\ge D_0I/2>D_0I/(4\mathrm e)$.
Conversely, $\gamma=\epsilon=0$ in Theorem 4.1 recovers exactly the
ideal table and its centered means and moments. $\square$

**Theorem 8.4 (A supplied finite table with exact dyadic rows).** The
84-configuration table in [C, Proposition 8.1], with
$r=c=1$, $q=1/2$, $J=2$, $\theta=1/4$, $\delta=1/2$ and its
specified threshold $H=14$, is exactly representable with $B=2$ and
the same complete configurations. Its separate risks below $1/10$
and its finite paid means are the assertions of that proposition.

Proof. Its zero probabilities are $1/2$, $1/4$ and their complements,
and its tick probabilities are zero, $1/2$ or one. They all belong
to $2^{-2}\mathbb Z$. Thus its installed rows are unchanged and so
are its laws, configurations, risks and paid means. This use of the
supplied finite instance does not place $s=\log2$ in the endpoint
neighborhood, and the conservative sufficient $B_0$ is not a necessity
claim for it. $\square$

## 9. Attribution and unresolved mathematical boundaries

**Definition 9.1 (Sources of the statements and methods).** The
finite-precision/calibration bridge of Theorem 4.1, its sufficient
installation bounds, the fixed-cap input-accuracy bound and the
construction-specific failures are repository-derived ordinary
deductions. No worldwide priority assertion accompanies this
composition. The source correspondence is as follows.

| Source | Exact use and boundary |
| --- | --- |
| [C], Definitions 1.1–1.3, 3.1 and 5.1; Theorems 3.2, 4.1 and 5.1 | Identical positive pair, known common $q$, stationary first wait, exact terminal phase law, normalized signal and moments, threshold and complete configurations. The source-specific estimates are inherited premises; the changed-law absorption, risks and paid means are proved here for the calibrated dyadic rows. |
| [C], Definition 2.2, Theorems 6.1 and 7.1, Corollary 7.2 | Existing unrestricted complete-budget lower/upper and eventual-growth criterion. The converse retains its credit to the renewal state/read source, Theorem 11.2 and Open problem 11.3. Section 7 transfers these results with precision provision and adds no universal lower. |
| [C], Definition 1.1 and Definition 9.1, correspondence to critical multiscale renewal attainment, Theorems 9.1–9.2 | Logarithmic paid attainment already has a prior multiscale construction. Neither that attainment nor the stronger counted all-budget frontier of [C] is a new conclusion of this volume. |
| Philippe Flajolet, *Approximate Counting: A Detailed Analysis*, BIT 25, 113–134, Section 1, as cited in [C, Definition 3.1 and Definition 9.1] | The classical base-two Morris phase increments $j$ with probability $2^{-j}$. Its approximate-count analysis alone supplies neither the source-normalized contrast nor the dyadic-calibration theorem. |
| Lu Xia, Martijn Anthonissen, Michiel Hochstenbach and Barry Koren, *Improved stochastic rounding*, arXiv:2006.00489v1, Section 3, as cited in [C, Theorem 4.1 and Definition 9.1] | Classical distance-proportional adjacent-grid rounding gives the ideal form. Finite-probability rounding here may be biased; its quantitative error is explicitly controlled rather than identified with ideal unbiasedness. |
| Marco Zamparo, *Renewal model for dependent binary sequences*, arXiv:2108.11293v2, Theorem 2.1, as cited in [C, Definition 1.2 and Definition 9.1] | The equilibrium first-interval correspondence uses $K+1$ and $\tau+1$. It provides no free gap port, hidden countdown or configuration bound. |
| Steven R. Howard, Aaditya Ramdas, Jon McAuliffe and Jasjeet Sekhon, *Exponential line-crossing inequalities*, arXiv:1808.03204v5, Section 2.3, Lemma 1, as cited in [C, Theorem 5.1 and Definition 9.1] | The classical exponential-supermartingale method is used with the actual gap/coin conditional law. The finite-drift and bounded-limit proof is included in Theorem 4.1. It supplies no free observation or state count. |
| Finite generating-function differentiation and predictable stopped summation | The matrix Neumann series in Theorem 6.1 and the nonnegative predictable sum (4.16) are standard methods used inside the new deductions. They do not assume duration/increment independence or assert offline complexity. |

**Definition 9.2 (Interpretation of the resource bounds).** Counting the
same $M_J$ complete configurations does not identify $B$, $Q$, $P$ or
immutable table length with that count. An index alphabet of size $M_J$
can be encoded using $\lceil\log_2M_J\rceil$ mutable bits, but this
encoding fact is not an optimum-controller theorem, a compression
lower bound or a physical memory benefit. Theorem 6.4 is a literal
description upper, and Theorem 7.2 presumes adequate precision rather
than settling joint resource optimization.

The positive pair, normalized common law, known-$q$ retuning, one
source-blind table and complete actual-read payment remain hypotheses
of every transfer. Proof indices and analytical continuations are not
additional observation histories. Serial coins, hardware arithmetic,
physical spacetime and neural or empirical learning performance are
outside this direct finite stochastic-table statement.

**Open problem 9.3 (Joint states, precision and paid time).** The joint
$(M,B,T)$ frontier, least sufficient or necessary transition precision,
least midpoint and parameter-input precision, sharp leading constants,
minimum nonempty budget and exact finite-budget optimum remain
unsettled here. Theorems 5.1 and 6.2 give sufficient allowances;
Theorems 8.2–8.3 diagnose two particular prescriptions. They do not
give a universal necessary precision rate. The exponent $r$ of the
full-cap count remains sufficient, and the inherited eventual criterion
permits every fixed positive polynomial budget exponent when the paid
constant may depend on it.

**Open problem 9.4 (Effective and additional observation models).**
Uniform offline bit-operation bounds, finite effective designs for
arbitrary noncomputable parameters, adaptation to unknown $q$, one
$q$-independent table and empirical calibration sample complexity are
not supplied. The fixed-$J$ input lemma controls only the stated
midpoint perturbation with fixed exact $c$ and budgets expressed using
true $s$. Any serial fair-coin, retained-buffer, hardware or learning
model needs its own complete-configuration and acquisition-cost bridge.

**Open problem 9.5 (Other sources and broader recovery).** No result
is transferred to sparse, signed or oscillating perturbations, mere
upper envelopes, changing $r,c,\alpha$ or additional observation and
workspace contracts. The required normalized contrast, occupation and
implementation estimates would have to be proved for each such
extension. The native-tree exact rate and the broader minimal-relations,
internal-observer and mutual-recovery questions of [C, Open problem 9.4]
retain their separate unresolved conclusions.

[C]: RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_RENEWAL_LOGARITHMIC_FRONTIER.md

## 追加锚（本行以下为增补区）
