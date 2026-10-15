# Critical renewal observation: a counted logarithmic frontier

## 1. Scope and fixed experiment

**Definition 1.1 (Parameters and the claimed resource order).** Fix an integer
$r\ge1$, a real $c>0$ and a risk allowance $0<\alpha<1/2$. Set
$d=2r-1$ and $a=d+1=2r$. All constants and endpoint neighborhoods below concern
these fixed parameters; none is asserted uniform as they vary. Logarithms
without a subscript are natural. The common known parameter is $q=e^{-s}$,
where $s>0$. The positive shapes are exactly

$$
F_0(k)=k^{2r-1},\qquad
F_1(k)=k^{2r-1}+c k^{r-1}\qquad(k\ge1).
\tag{1.1}
$$

For an integer configuration budget $M\ge2$, put

$$
\begin{aligned}
b&=1-2\alpha,\\
L_M&=\max\left\{1,
  \left\lceil\left(\frac{2c(M-2)}b\right)^{1/r}\right\rceil\right\},\\
\Psi(s,M)&=\frac{s^{-(2r+1)}}{1+\log\min\{L_M,1/s\}}
\qquad(0<s<1).
\end{aligned}
\tag{1.2}
$$

Theorem 5.1 constructs one common actual-bit observer with
$O(2^{rJ})$ complete configurations and both paid means
$O(s^{-(2r+1)}/J)$, simultaneously for every integer $J\ge1$ with
$s2^J\le\eta$, on one fixed neighborhood. Theorem 6.1 matches (1.2) for
every sufficient finite budget. Theorem 7.1 characterizes eventual budget
growth for the full logarithmic order.

The universal lower bound and its necessary budget condition are credited
to [the public renewal source, Theorem 11.2 and Open problem 11.3][SOURCE].
The public [critical multiscale attainment source][MULTISCALE],
Theorems 9.1–9.2, already proves logarithmic paid attainment for this same
positive pair and the same complete actual-bit resource contract: for
$sL\le\eta$ it gives
$M\le C(L+2)/(s^r\sqrt{H_L})$ and both paid means at most
$Cs^{-(2r+1)}/H_L$, with its fixed-$\theta$ corollary. Its Section 10
leaves minimum state and the full all-budget frontier open, and its lower
discussion is conditional attribution. That ordinary public source is
fallible and is not independent verification of this manuscript.

The contribution retained here is the different stronger resource and
quantifier statement: the finite phase reader and its source-normalized
occupation estimates, the evidence rounding and complete paid
implementation yield the explicitly counted $O(2^{rJ})$ table, a uniform
upper for every sufficient finite budget, and the eventual
positive-polynomial budget criterion. These are ordinary mathematical
proofs, not Lean kernel validation. The category/lattice existence result
from [MULTISCALE] is credited rather than claimed as a new discovery. The
native-tree exact-rate problem and the broader minimal-relations,
internal-observer and mutual-recovery programme retain their separate
unresolved goals.

**Definition 1.2 (Full stationary source law).** For $i\in\{0,1\}$ define

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,&
f_i(k)&=F_i(k)q^k/Z_i(q)\quad(k\ge1),& f_i(0)&=0,\\
S_i(u)&=\sum_{k\ge u}f_i(k)\quad(u\ge0),&
\mu_i&=\sum_{k\ge1}(k+1)f_i(k),\\
\beta_i&=\frac{\sum_{k\ge1}k(k+1)f_i(k)}{2\mu_i}.
\end{aligned}
\tag{1.3}
$$

Draw the first forward wait $\tau$ with

$$
\mathsf P_i(\tau=u)=S_i(u)/\mu_i\qquad(u=0,1,2,\ldots).
\tag{1.4}
$$

Independently draw $K_1,K_2,\ldots$ iid with law $f_i$. The one bits of
$X_0,X_1,\ldots$ occur at

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{h=1}^n(K_h+1)\quad(n\ge1);
\tag{1.5}
$$

all other bits are zero. Thus $K_h$ counts zeros between ticks, and
$K_h+1$ counts a whole interval through its closing tick. The first wait
is not an iid gap. In particular $S_i(0)=S_i(1)=1$, and the possibility
$\tau=0$ is included.

All these sums and all fixed polynomial moments are finite for $0<q<1$.
Nonnegative summation gives
$\sum_{u\ge0}S_i(u)=\mu_i$ and $\mathbb E_i\tau=\beta_i$.
For the stationarity convention, the analytical countdown to the next tick
decreases by one at positive values and draws $K\sim f_i$ at zero. Its
stationary mass is $\pi_i(u)=S_i(u)/\mu_i$, since
$\pi_i(u+1)+\pi_i(0)f_i(u)=\pi_i(u)$, including $u=0$.
The observer is given only the bits, never this countdown. This is the
equilibrium convention of [SOURCE, Definitions 2.1–2.2][SOURCE]; in
[Zamparo, Theorem 2.1][ZAMPARO] the correspondence is
$S_2=K+1$ and $S_1=\tau+1$.

**Definition 1.3 (Complete configurations and compliance).** At selected
known $q$ and finite $M$, one source-blind stochastic observer is used
under both labels, with the same initialization and bit-transition table.
It may retune with $(q,r,c,\alpha,M)$, without continuity or a common table
across different $q$. Immutable real transition probabilities have
unrestricted precision. Fresh update coins are independent of the source
and of previous fresh randomness.

Every mutable retained distinction belongs to one of at most $M$ complete
persistent configurations: initialization, registers, control and working
phases, work buffers, retained random consequences or seeds, and both
internally emitted labels. A nonterminal configuration undertakes a read
of the next actual bit; entry into a label emits that label and stops.
Any admissible more general action representation may be composed into
the same-budget read-ready normal form of [SOURCE, Lemma 3.2][SOURCE].

The only observations are one uninterrupted consecutive history from
(1.5). There is no hidden source age, elapsed-time or read-count input,
program counter, archive, random tape, separate history, source reset,
free gap, skipped bit, probability response, true-label port or
stopping-time decoder. All mutable information is counted. Fixed formulas
for a transition row specify immutable entries of a finite table; they
do not license uncounted arithmetic workspace during its execution.

If the read prefix is $X_0,\ldots,X_{T-1}$, the paid cost is $T$.
It includes every initial zero and tick, every failed suffix and holding
interval, and any terminal partial interval. Write
$\mathfrak A_M(e^{-s},\alpha)$ for the tables meeting all six conditions

$$
\begin{gathered}
\mathsf P_0(D=1)\le\alpha,\qquad
\mathsf P_1(D=0)\le\alpha,\\
\mathsf P_0(T<\infty)=\mathsf P_1(T<\infty)=1,\\
\mathbb E_0T<\infty,\qquad \mathbb E_1T<\infty.
\end{gathered}
\tag{1.6}
$$

Both paid means in every constructive claim concern the same selected
table. This is the complete contract of [SOURCE, Definition 3.1][SOURCE].

## 2. Source estimates and the inherited converse

**Definition 2.1 (Scalar supplier and exact normalization).** Put

$$
R_m(s)=\sum_{k\ge1}k^m e^{-sk},\qquad
g(s)=\frac{R_{r-1}(s)}{R_{2r-1}(s)}.
\tag{2.1}
$$

The fixed-source estimates in [SOURCE, Lemma 2.3][SOURCE] give

$$
\begin{aligned}
Z_i(e^{-s})&=(2r-1)!s^{-2r}(1+O(s)),\\
g(s)&=\frac{(r-1)!}{(2r-1)!}s^r+O(s^{r+1}),\\
\mu_i&=2r/s+O(1),\qquad
\beta_i=(2r+1)/(2s)+O(1).
\end{aligned}
\tag{2.2}
$$

Consequently choose, once, $s_*\in(0,1)$ and positive constants
$z_-,z_+,G_*,C_\mu,C_\beta$ such that, for both $i$ and $0<s<s_*$,

$$
z_-s^{-2r}\le Z_i(e^{-s})\le z_+s^{-2r},\qquad
g(s)\le G_*s^r,\qquad
\mu_i\le C_\mu/s,\qquad 1+\beta_i\le C_\beta/s.
\tag{2.3}
$$

These estimates can also be read directly from
$R_0(s)=1/(e^s-1)$ and
$R_m=(-d/ds)^mR_0$. The remainder $R_0(s)-1/s$ is analytic at zero,
so the leading powers and their moment quotients have controlled
remainders. No source change or tail-envelope inference occurs here.

The normalization identity used in the new proof is exact:

$$
Z_1=(1+cg)Z_0,\qquad
f_1(k)-f_0(k)=
\frac{c\,[k^{r-1}-g(s)k^{2r-1}]e^{-sk}}{Z_1}.
\tag{2.4}
$$

The signed subtraction in (2.4) remains part of every contrast estimate.

**Definition 2.2 (Credited lower and its scope).** Theorem 11.2 of
[SOURCE][SOURCE] supplies $s_->0$ and $A_->0$, depending only on
$(r,c,\alpha)$, with

$$
\forall\,0<s<s_-\quad\forall\,M\ge2\quad
\forall\,\mathcal A\in\mathfrak A_M(e^{-s},\alpha)\quad
\forall\,i\in\{0,1\}:
\mathbb E_i^{\mathcal A}T\ge A_-\Psi(s,M).
\tag{2.5}
$$

Here and below budgets are finite integers. The constants and neighborhood
precede every budget and design. The converse includes arbitrary
stochastic retuning, arbitrarily small positive edges, initial
randomization and partial-gap stopping, with every opposing compliance
condition still imposed. It is not restricted to the construction below.

The relevant supplier interfaces are its finite-configuration hitting
comparison, normalized clipped-gap entropy and actual tick price.
For completeness, the clipped law is the probability distribution
$a_i^L$ on $\{1,\ldots,L,\star\}$ with $a_i^L(k)=f_i(k)$ for $k\le L$
and $a_i^L(\star)=\sum_{k>L}f_i(k)$. Set
$D_i(s,L)=\sum_z a_i^L(z)\log(a_i^L(z)/a_{1-i}^L(z))$.
All its masses are positive. The initial comparison and forest allowance
can be taken as

$$
r_{\rm init}(s)=c\frac{R_r(s)+R_{r-1}(s)}
                         {R_{2r}(s)+R_{2r-1}(s)},\qquad
\chi_{M,L}=
\frac{(1+c/(L+1)^r)^{M-2}-1}{(1+c/(L+1)^r)^{M-2}+1}.
$$

In its notation the finite-parameter inequality is

$$
b\le r_{\rm init}(s)+\chi_{M,L}
  +\sqrt{D_i(s,L)(1+c)s\mathbb E_iT/2},
\tag{2.6}
$$

where $r_{\rm init}(s)=O(s^r)$,
$\chi_{M,L}\le (M-2)c/[2(L+1)^r]$, and the exact clipped-law entropy obeys

$$
D_i(s,L)\le C_Ds^{2r}
  \bigl[1+\log\min\{L,1/s\}\bigr].
\tag{2.7}
$$

Choose the supplier neighborhood so $r_{\rm init}\le b/4$ and set
$L=L_M$. Then $\chi_{M,L_M}\le b/4$, and squaring (2.6) yields (2.5).
The entropy interface uses a common bit-table kernel averaged over actual
gaps, finite-path entropy on live epochs and a harmonic terminal function;
it does not require an auxiliary comparison chain to terminate.
Its tick-price interface conditions on the entire actual prefix and
independent coins, including the equilibrium initial wait and terminal
partial reads. Those are the reasons its lower applies to the full
class in Definition 1.3. Equations (2.6)–(2.7) and (2.5) are inherited
results, not new converse theorems of this volume.

The same source gives

$$
L_M\le C_LM^{1/r}
\tag{2.8}
$$

for a fixed $C_L\ge1$, and proves that $M=2$ is an empty compliant
class: the two labels exhaust the configurations, and a common initial
label cannot satisfy both risks below one half. Nonemptiness at larger
budgets will be supplied here only at a sufficient threshold.

## 3. A finite phase reader and its occupation weights

**Definition 3.1 (Capped Morris phase).** For an integer $J\ge1$ let
$\mathcal Z_J=\{1,\ldots,J,\dagger\}$, where $\dagger$ is the dead phase.
The zero-transition matrix $R$ starts in phase one and has rows

$$
\begin{aligned}
R(j,j)&=1-2^{-j},&R(j,j+1)&=2^{-j}\quad(1\le j<J),\\
R(J,J)&=1-2^{-J},&R(J,\dagger)&=2^{-J},\\
R(\dagger,\dagger)&=1.
\end{aligned}
\tag{3.1}
$$

All unlisted entries are zero. Each actual read zero performs this one
stochastic transition. The reward at a closing tick is

$$
v_j=2^{-rj}\quad(1\le j\le J),\qquad v_\dagger=0.
\tag{3.2}
$$

If the actual gap has $K=k$ zeros, its terminal phase law is $e_1R^k$.
Let $V$ denote the resulting reward and define the immutable means

$$
m_i=\mathbb E_iV
  =\frac1{Z_i}\sum_{k\ge1}F_i(k)e^{-sk}e_1R^kv,
\qquad \theta=(m_0+m_1)/2,\qquad \Delta=m_1-m_0.
\tag{3.3}
$$

The series converges because $R$ is stochastic and $v$ is bounded.
It specifies a finite-table design from known $q$ and the two promised
laws. It is not a runtime query or true-label response. The phase reader
is the base-two Morris counter defined in [Flajolet, Section 1][FLAJOLET],
capped at $J$ with an explicitly counted dead state. Approximate-count
accuracy alone is not the estimate needed here; the following occupation
bound supplies the actual source interface.

**Theorem 3.2 (Uniform discounted phase occupation).** For each fixed
integer $m\ge0$ there are explicit positive constants

$$
b_m=\frac{3e^{-6}}{2^{m+3}},\qquad
B_m=e(m+1)!2^{m+1}
\tag{3.4}
$$

with this property. In the uncapped phase chain, let $\mathcal T_1=0$
and $\mathcal T_j$ be its entrance zero count into phase $j$.
For $j\ge1$, define

$$
A_j^{(m)}(s)=\mathbb E
  \sum_{k=\max\{1,\mathcal T_j\}}^{\mathcal T_{j+1}-1}
    k^m e^{-sk}.
\tag{3.5}
$$

If $s2^j\le\eta\le1$, then

$$
b_m2^{j(m+1)}\le A_j^{(m)}(s)
  \le B_m2^{j(m+1)}.
\tag{3.6}
$$

The bounds are independent of $s,j,J$; the capped chain has these same
occupations for all its live phases $j\le J$.

Proof. Only for describing the phase-chain law, let $W_u$ be independent
geometric variables on $\{1,2,\ldots\}$ with success probability $2^{-u}$.
Then $\mathcal T_j=\sum_{u<j}W_u$ and
$\mathcal T_{j+1}=\mathcal T_j+W_j$. Fresh per-zero coins give exactly
this holding-time law. The observer does not draw or store a countdown
$W_u$; its only phase state is the current member of $\mathcal Z_J$.

Write $\ell=2^j$. Since
$\mathbb E\mathcal T_j=\sum_{u<j}2^u=\ell-2\le\ell$,
Markov's inequality gives
$\mathsf P(\mathcal T_j\le4\ell)\ge3/4$.
Independently,

$$
\mathsf P(W_j\ge\ell)=(1-1/\ell)^{\ell-1}\ge e^{-1}.
\tag{3.7}
$$

For the last inequality, integrate $1/(1-x)$ to obtain
$\log(1-x)\ge-x/(1-x)$ at $x=1/\ell$.
On the intersection of these two events, the $\ell/2$ integers

$$
\mathcal T_j+\ell/2,\ldots,\mathcal T_j+\ell-1
\tag{3.8}
$$

are in phase $j$, are at least one, and lie between $\ell/2$ and
$5\ell$. Each contributes at least $(\ell/2)^m e^{-5\eta}$.
The expected sum is therefore at least
$(3/4)e^{-1}(\ell/2)^{m+1}e^{-5\eta}$, proving the stated lower constant
uniformly for $\eta\le1$. This argument also covers $j=1$ and $m=0$.

For the upper bound, let $p=m+1\ge1$. A geometric variable with mean
$\ell_u=2^u$ satisfies, for $t\ge0$,

$$
\mathsf P(W_u>t)=(1-1/\ell_u)^{\lfloor t\rfloor}
  \le e\,e^{-t/\ell_u}.
\tag{3.9}
$$

The tail integral gives
$\mathbb EW_u^p\le e p!\ell_u^p$.
The triangle inequality in $L^p$ yields

$$
\|\mathcal T_{j+1}\|_p
 \le(e p!)^{1/p}\sum_{u=1}^j2^u
 \le2(e p!)^{1/p}\ell.
\tag{3.10}
$$

The nonnegative sum in (3.5) is at most
$\mathcal T_{j+1}^{m+1}$ after dropping the exponential. Thus (3.10)
proves its upper constant. Capping changes only what follows phase $J$;
it changes none of the events of occupying a phase $j\le J$ after $k$
zeros. $\square$

## 4. Exact source contrast and a coarse evidence grid

**Theorem 4.1 (One-gap signal, moments and rounding).** For the fixed
source there exist $\eta\in(0,1)$ and positive constants
$D_0,D_1,C_1,C_2,V_0$, chosen before every $s,J$, such that on (2.3),
for every integer $J\ge1$ with $s2^J\le\eta$, putting

$$
L=2^J,\qquad I=s^{2r}J,\qquad \delta=J/L^r,
\tag{4.1}
$$

the reward in Definition 3.1 satisfies

$$
\begin{gathered}
D_0 I\le\Delta\le D_1 I,\qquad
0\le m_i\le C_1s^{2r}L^r,\qquad
\mathbb E_iV^2\le C_2 I,\\
0\le V,\theta\le2^{-r},\qquad 0<\delta\le1/2.
\end{gathered}
\tag{4.2}
$$

For each possible terminal phase $z$, put

$$
t_z=(v_z-\theta)/\delta,\qquad
n_z=\lfloor t_z\rfloor,\qquad p_z=t_z-n_z.
\tag{4.3}
$$

With a fresh coin, let the score increment $U$ be
$\delta n_z$ with probability $1-p_z$, and $\delta(n_z+1)$ with
probability $p_z$. Under the two actual gap laws, respectively,

$$
\mathbb E_0U=-\Delta/2,\qquad
\mathbb E_1U=\Delta/2,\qquad
|U|\le1,\qquad \mathbb E_iU^2\le V_0 I.
\tag{4.4}
$$

All estimates concern the same reward and same centered update.

Proof. Let
$P_j(k)=\mathsf P(\mathcal T_j\le k<\mathcal T_{j+1})$.
The terminal reward after $k$ zeros has mean
$h(k)=\sum_{j=1}^J2^{-rj}P_j(k)$.
Theorem 3.2 and nonnegative summation give

$$
\sum_{k\ge1} k^m e^{-sk}P_j(k)=A_j^{(m)}(s).
\tag{4.5}
$$

Insert (2.4) into $\sum_k(f_1(k)-f_0(k))h(k)$. Exactly,

$$
\Delta=\frac c{Z_1}
 \left\{\sum_{j=1}^J2^{-rj}A_j^{(r-1)}
       -g(s)\sum_{j=1}^J2^{-rj}A_j^{(2r-1)}\right\}.
\tag{4.6}
$$

In particular the source normalizer has not disappeared. The positive
sum lies between $b_{r-1}J$ and $B_{r-1}J$. Set

$$
C_* = \frac{B_{2r-1}}{1-2^{-r}}.
\tag{4.7}
$$

The second occupation sum is at most
$B_{2r-1}\sum_{j=1}^J2^{rj}\le C_*L^r$.
Choose $\eta\in(0,1)$ sufficiently small that

$$
G_*C_*\eta^r\le b_{r-1}/2.
\tag{4.8}
$$

Then the whole subtracted term in (4.6) is at most $b_{r-1}/2$.
For every $J\ge1$, its braces lie between $b_{r-1}J/2$ and
$B_{r-1}J$. Thus one may take

$$
D_0=cb_{r-1}/(2z_+),\qquad D_1=cB_{r-1}/z_-.
\tag{4.9}
$$

The same neighborhood and $\eta$ work for every cap.

Because $F_i(k)\le(1+c)k^{2r-1}$, (4.5) also gives

$$
\begin{aligned}
m_i&\le\frac{1+c}{z_-}s^{2r}
   \sum_{j=1}^J2^{-rj}B_{2r-1}2^{2rj}
   \le C_1s^{2r}L^r,\\
\mathbb E_iV^2&\le\frac{1+c}{z_-}s^{2r}
   \sum_{j=1}^J2^{-2rj}B_{2r-1}2^{2rj}
   = C_2s^{2r}J,
\end{aligned}
\tag{4.10}
$$

with $C_1=(1+c)C_*/z_-$ and $C_2=(1+c)B_{2r-1}/z_-$.
Exactly one phase is occupied at a terminal tick. The second line squares
that one terminal reward; it is not a sum of independent per-scale
observations. Bounds on $V$ and $\theta$ follow from (3.2), while
$J2^{-rJ}\le J2^{-J}\le1/2$ for all $J\ge1$.

For any real $x$, adjacent-point rounding at spacing $\delta$ satisfies

$$
\mathbb E(U\mid x)=x,\qquad
\operatorname{Var}(U\mid x)=\delta^2p(1-p)\le\delta|x|,
\qquad |U|\le|x|+\delta.
\tag{4.11}
$$

Here $n=\lfloor x/\delta\rfloor$ and $p=x/\delta-n$. Unbiasedness and
the variance formula are elementary properties of classical stochastic
rounding, as in [Xia et al., Section 3][ROUNDING]. For the last variance
bound, when $|x|<\delta$ the cell adjoins zero and the variance is
$|x|(\delta-|x|)$. Otherwise it is at most
$\delta^2/4\le\delta|x|$. This covers negative inputs and grid points.

Use $x=V-\theta$ and condition on the actual terminal phase. Its means
are exactly $m_i-\theta$, giving the two drifts in (4.4). Jensen for the
equal mixture of the two reward laws gives $\theta^2\le C_2 I$.
Consequently

$$
\begin{aligned}
\mathbb E_i(V-\theta)^2&\le4C_2 I,\\
\delta\mathbb E_i|V-\theta|
 &\le\delta(m_i+\theta)\le2C_1s^{2r}J=2C_1 I,\\
\mathbb E_iU^2&\le(4C_2+2C_1)I.
\end{aligned}
\tag{4.12}
$$

Take $V_0=4C_2+2C_1$. Finally
$|V-\theta|\le2^{-r}\le1/2$ and $\delta\le1/2$ imply $|U|\le1$.
The noise estimate depends on the small average absolute score, not an
unconditional noise allowance $\delta^2$ for every gap. This is why the
coarse factor $J$ in the grid preserves the logarithmic signal. $\square$

## 5. The entire actual-bit table

**Definition 5.1 (Threshold and every persistent configuration).** Fix
the constants of Theorem 4.1, and choose once

$$
\lambda=\min\{1,D_0/(2eV_0)\}>0,\qquad
A=\frac{\log(1/\alpha)}\lambda,\qquad
K=4A+4.
\tag{5.1}
$$

At a selected $s,J$ as in Theorem 4.1 put

$$
H=\lceil A/\delta\rceil=\lceil A2^{rJ}/J\rceil.
\tag{5.2}
$$

The state set consists of $w,d_0,d_1$ and every pair

$$
(e,z),\qquad e\in\mathbb Z,\quad -H<e<H,\quad
z\in\mathcal Z_J.
\tag{5.3}
$$

Initialize in $w$ under both source laws. Every nonlabel state reads the
next actual bit. Entry into $d_i$ immediately emits $D=i$ and stops.
The label rows on unused future bits fix that label. For any integer $u$
define the immutable successor map

$$
\Gamma(u)=
\begin{cases}
d_1,&u\ge H,\\
d_0,&u\le-H,\\
(u,1),&-H<u<H.
\end{cases}
\tag{5.4}
$$

The complete bit-transition rows are the following. In the zero row
at $J$, advancement means entry into $\dagger$.

| Current configuration and bit | Successors and probabilities |
| --- | --- |
| $w$, zero | $w$ with probability one |
| $w$, one | $(0,1)$ with probability one |
| $(e,j)$, zero, $1\le j<J$ | $(e,j)$ with probability $1-2^{-j}$; $(e,j+1)$ with probability $2^{-j}$ |
| $(e,J)$, zero | $(e,J)$ with probability $1-2^{-J}$; $(e,\dagger)$ with probability $2^{-J}$ |
| $(e,\dagger)$, zero | $(e,\dagger)$ with probability one |
| $(e,z)$, one, every $z\in\mathcal Z_J$ | $\Gamma(e+n_z)$ with probability $1-p_z$; $\Gamma(e+n_z+1)$ with probability $p_z$ |
| $d_0$, either bit | $d_0$ with probability one |
| $d_1$, either bit | $d_1$ with probability one |

If two listed destinations coincide, their probabilities add. This
defines every row, including tick inputs after zero zeros, which are
unreachable under $K\ge1$. The integer $n_z$, probability $p_z$ and map
$\Gamma$ are immutable entries specified by (4.3)–(5.4). The tick performs
one direct stochastic transition, with no pending update or work phase.
Nonterminal ticks reset the counted phase coordinate to one; they do
not reset the source. After phase death every subsequent zero remains
a paid read until the actual closing tick.

The only retained active information is the integer $e$ and finite phase
$z$. No real score, scale-selection register, gap index, exact gap length,
source countdown, clock, tape, seed, archive, action index or workspace
is retained. A fresh coin's only retained consequence is its successor
configuration, already in (5.3). All listed states, including states with
small probability or unused input edges, count. The exact listed count is

$$
M_J=3+(2H-1)(J+1).
\tag{5.5}
$$

**Theorem 5.1 (Counted critical controller, both risks and both paid
means).** There exist one $s_0>0$ and a positive $C$, depending only on
$(r,c,\alpha)$, such that for every $0<s<s_0$ and every integer $J\ge1$
with $s2^J\le\eta$, the single common table of Definition 5.1 meets all
six conditions (1.6). Its complete listed count and paid means satisfy

$$
M_J=3+(2\lceil A2^{rJ}/J\rceil-1)(J+1)
 \le K2^{rJ},\qquad
\max_i\mathbb E_iT\le C\frac{s^{-(2r+1)}}J.
\tag{5.6}
$$

If $G$ is its number of completed post-first-tick gaps through absorption,
then under each source

$$
\mathbb E_iG\le\frac{2(A+3/2)}\Delta<\infty,\qquad
\mathbb E_iT=1+\beta_i+\mu_i\mathbb E_iG.
\tag{5.7}
$$

The constants and neighborhood precede all $J$ and budgets.

Proof. Every row is stochastic and stays in the declared set. Under source
$i$, the law of a complete gap together with its fresh phase and tick
coins gives the pair $(K,U)$ of Theorem 4.1. Independent successive source
gaps and fresh coins give iid potential pairs $(K_n,U_n)$ after the first
paid tick, independent of $\tau$. The actual run consumes a stopped
prefix of these pairs. This is an analytical continuation on the same
source history, not a source reset or another observation stream.
It has no independence between $U_n$ and its own $K_n$.

Let $\mathcal F_n$ contain $\tau$ and the first $n$ complete gap/coin
blocks. The phase begins at one for every nonterminal gap; its zero
probabilities and tick increment do not depend on $e$. Thus conditional
on $\mathcal F_{n-1}$, the next potential $(K_n,U_n)$ has exactly its
original joint law. No independent histories for different phases or
scales are asserted: all phase occupations in Section 4 describe one
mark from one gap.

For proof variables only, put $S_0=0$, $S_n=\sum_{h=1}^nU_h$ and

$$
G=\inf\{n\ge1:|S_n|\ge H\delta\}.
\tag{5.8}
$$

Before $G$, the table's evidence is exactly $e=S_n/\delta$.
At $G$ the appropriate label is emitted directly. The final overshoot
in $S_G$ is not an additional state or a decoder from stopping time.
Since $|U_n|\le1$, at every finite $m$,

$$
|S_{G\wedge m}|\le H\delta+1\le A+3/2.
\tag{5.9}
$$

Write $\sigma_0=-1$, $\sigma_1=1$ only to orient the proof toward its
correct label. The inclusion event $\{G\ge n\}$ belongs to
$\mathcal F_{n-1}$. By (4.4), finite conditional expectation gives

$$
\mathbb E_i[\sigma_i S_{G\wedge m}]
 =\sum_{n=1}^m\mathbb E_i[
    \mathbf1_{\{G\ge n\}}\sigma_i U_n]
 =\frac\Delta2\mathbb E_i(G\wedge m)
 \le A+3/2.
\tag{5.10}
$$

Monotone convergence on the middle term proves the first bound in (5.7)
and $G<\infty$ almost surely under both labels. Every individual gap
and $\tau$ is almost surely finite, so actual bit stopping is almost
surely finite too. Termination has been established using finite sums
before any infinite-horizon stopping limit.

For $|u|\le1$ and $0<\lambda\le1$, Taylor's integral remainder gives

$$
e^{\lambda u}\le1+\lambda u+(e/2)\lambda^2u^2.
\tag{5.11}
$$

Under source zero, (4.4) and (5.1) imply

$$
\mathbb E_0e^{\lambda U}
 \le1-\lambda\Delta/2+(e/2)\lambda^2V_0 I
 \le1-\lambda D_0 I/4\le1.
\tag{5.12}
$$

Under source one the identical estimate holds for
$\mathbb E_1e^{-\lambda U}$. Therefore
$e^{\lambda S_{G\wedge m}}$ under source zero and
$e^{-\lambda S_{G\wedge m}}$ under source one are nonnegative
supermartingales starting at one. Their conditional inequalities use
the full $\mathcal F_{m-1}$, not a conditional iid-bit assumption.
This is the classical exponential-supermartingale method; compare
[Howard et al., Section 2.3, Lemma 1][VILLE].

The already established finite $G$ and the deterministic bound (5.9)
permit bounded convergence. At the wrong exit the corresponding
exponential is at least $e^{\lambda H\delta}$. Hence separately

$$
\mathsf P_0(D=1)\le e^{-\lambda H\delta}\le\alpha,
\qquad
\mathsf P_1(D=0)\le e^{-\lambda H\delta}\le\alpha.
\tag{5.13}
$$

This proof supplies both risks on the one common table; no true-label
sign is used by that table.

Pathwise, it reads the first wait and first tick and stops on a subsequent
read closing tick. Therefore

$$
T=1+\tau+\sum_{n=1}^G(K_n+1).
\tag{5.14}
$$

All suffixes after phase death, holding gaps, failed observations and the
terminal interval are in this sum. The construction has no terminal
partial interval because it completes every undertaken gap. For payment,
$\{G\ge n\}\in\mathcal F_{n-1}$ is independent of the next $K_n$.
Tonelli and this predictable inclusion, not independence of a duration
from its own score or deciding event, give

$$
\mathbb E_i\sum_{n=1}^G(K_n+1)
 =\sum_{n\ge1}\mu_i\mathsf P_i(G\ge n)
 =\mu_i\mathbb E_iG.
\tag{5.15}
$$

Thus the second identity in (5.7) is exact and both paid means are finite.
This is the completed-gap payment interface of
[SOURCE, equations (9.9)–(9.10)][SOURCE], with continuation proved for
the present table. By (2.3), (4.2) and (5.7),

$$
\mathbb E_iT\le\frac{C_\beta}s
 +\frac{2C_\mu(A+3/2)}{D_0s^{2r+1}J}.
\tag{5.16}
$$

Uniformly for the allowed caps, $J\le2^{rJ}=L^r$ and
$s^{2r}J\le s^{2r}L^r\le\eta^rs^r\le1$ when $s<1$.
The first term is absorbed into the second order, proving the upper in
(5.6) on any fixed $s_0\le s_*$ with $s_0\le1$.

Finally, $H\le AL^r/J+1$, $J+1\le2J$ and $J+1\le L^r$ give

$$
\begin{aligned}
M_J&\le3+(2AL^r/J+1)(J+1)\\
   &\le3+4AL^r+L^r\le(4A+4)L^r=KL^r.
\end{aligned}
\tag{5.17}
$$

This counts the entire phase/evidence product, waiting state and two
labels, without deleting any improbable or unreachable configuration.
For $J=1$, $\delta=2^{-r}$ and the table is the alive/dead geometric
survival mark with midpoint up/down/hold updates; the exact count is
$4H+1$. It has no growing logarithmic gain. Higher $J$ contributes through
the single terminal reward's occupation law, while the coarser grid
removes the factor $J$ from the final configuration bound. $\square$

## 6. One neighborhood before every sufficient finite budget

**Theorem 6.1 (Uniform critical frontier).** There are $s_0\in(0,1)$,
$C_-,C_+>0$ and a finite integer $M_0$, depending only on the fixed
$(r,c,\alpha)$, with the following quantifiers:

$$
\begin{gathered}
\forall\,0<s<s_0\quad\forall\,M\ge2\quad
\forall\,\mathcal A\in\mathfrak A_M(e^{-s},\alpha)\quad
\forall\,i\in\{0,1\}:\quad
\mathbb E_i^{\mathcal A}T\ge C_-\Psi(s,M),\\[1mm]
\forall\,0<s<s_0\quad\forall\,M\ge M_0\quad
\exists\,\mathcal A_{s,M}\in\mathfrak A_M(e^{-s},\alpha):\quad
\max_i\mathbb E_i^{\mathcal A_{s,M}}T\le C_+\Psi(s,M).
\end{gathered}
\tag{6.1}
$$

The lower line of reasoning is inherited (2.5); the new simultaneous upper
is the counted construction. No budget-dependent shrinking of $s_0$ is
permitted or needed.

Proof. Keep $K,\eta$ and the constants of Theorem 5.1. Choose
$M_0=\lceil K2^r\rceil$ and shrink a single $s_0$ inside the source,
upper and lower neighborhoods, with $s_0\le\eta/2$. These choices all
precede $M$. For every $M\ge M_0$ and $s<s_0$ set

$$
y=\min\{(M/K)^{1/r},\eta/s\},\qquad
J=\lfloor\log_2 y\rfloor.
\tag{6.2}
$$

Then $y\ge2$, $J\ge1$, $2^J\le\eta/s$ and
$K2^{rJ}\le M$. Theorem 5.1 gives the required common compliant table.
Here $J$ is a cap selected for the immutable table; it is never a runtime
epoch, read or gap counter.

Put $x=\min\{M^{1/r},1/s\}$ and
$C_0=\max\{K^{1/r},\eta^{-1}\}\ge1$. Each argument of this minimum is
at most $C_0$ times its counterpart in $y$, so $x\le C_0y$.
Equation (2.8) implies

$$
\min\{L_M,1/s\}\le C_Lx\le C_LC_0y<C_LC_0\,2^{J+1}.
\tag{6.3}
$$

Therefore, using $J\ge1$,

$$
1+\log\min\{L_M,1/s\}
 \le 1+\log(C_LC_0)+(J+1)\log2\le C_3J
\tag{6.4}
$$

for a fixed positive $C_3$. The upper $Cs^{-(2r+1)}/J$ from (5.6)
is consequently at most $CC_3\Psi(s,M)$. Take $C_+=CC_3$ and retain
$C_-=A_-$ from (2.5). This covers the entire capped and uncapped budget
range, without an assumption of small $sM^{1/r}$. $\square$

**Corollary 6.2 (Separate and common-table infima).** For $M\ge M_0$,
define

$$
\mathfrak m_i(s,M)=\inf_{\mathcal A\in\mathfrak A_M(e^{-s},\alpha)}
  \mathbb E_i^{\mathcal A}T,\qquad
\mathfrak m_{\max}(s,M)=\inf_{\mathcal A\in\mathfrak A_M(e^{-s},\alpha)}
  \max_i\mathbb E_i^{\mathcal A}T.
\tag{6.5}
$$

On the neighborhood of Theorem 6.1, each of these three quantities belongs
to $[C_-\Psi(s,M),C_+\Psi(s,M)]$, uniformly over every sufficient finite
$M$. Equivalently their order is

$$
\frac{s^{-(2r+1)}}{1+\log\min\{M,1/s\}},
\tag{6.6}
$$

up to fixed source/risk constants. These are order statements, not
sharp constants or claims of attained exact infima.

Proof. The lower holds for each mean of every competitor, and hence for
their maximum and each infimum. The one simultaneous upper makes the
class nonempty and bounds all three infima. No distinct source-optimized
machines have been combined.

To compare denominators, for $M\ge4$,
$L_M\ge(cM/b)^{1/r}$, and for $M=2,3$ the bound $L_M\ge1$ applies.
Together with (2.8), choose constants $0<c_L\le1\le C_L$ such that
$c_LM^{1/r}\le L_M\le C_LM^{1/r}$ for every $M\ge2$.
The logarithms of the minima with $1/s$ then differ by at most fixed
additive constants. Both actual denominators are at least one, so they
are comparable multiplicatively. Moreover, for $M\ge2$, $s<1$,

$$
\frac1r\bigl[1+\log\min\{M,1/s\}\bigr]
\le1+\log\min\{M^{1/r},1/s\}
\le1+\log\min\{M,1/s\}.
\tag{6.7}
$$

These give (6.6). $\square$

## 7. Exact eventual budget-growth quantifiers

**Theorem 7.1 (Necessary and sufficient logarithmic budget growth).**
Let $M(s)$ be any finite integer-valued budget function on
$(0,\bar s)$, with $M(s)\ge2$ and no monotonicity or regularity hypothesis.
The following three conditions are equivalent:

1. There exist $0<C_T<\infty$ and $s_1>0$ such that for every
   $0<s<s_1$ one can select a common compliant
   $\mathcal A_s\in\mathfrak A_{M(s)}(e^{-s},\alpha)$ with
   $\max_i\mathbb E_i^{\mathcal A_s}T
    \le C_Ts^{-(2r+1)}/\log(e/s)$.
2. There exist one fixed $i_\star\in\{0,1\}$, $0<C_T<\infty$ and
   $s_1>0$ such that for every $0<s<s_1$ one can select a common
   compliant $\mathcal A_s$ at that budget with
   $\mathbb E_{i_\star}^{\mathcal A_s}T
    \le C_Ts^{-(2r+1)}/\log(e/s)$.
3. There exist $\varepsilon>0$ and $s_2>0$ such that
   $\log(1+M(s))\ge\varepsilon\log(1/s)$ for every $0<s<s_2$.

All neighborhoods in these conditions are restricted to $s<\min\{\bar s,1\}$.
Condition 2 still requires both risks, both almost-sure stops and both
finite means for each selected table; only the fast upper is one-sided.
The constants $C_T,\varepsilon$ may depend on the budget family.
Necessity is the credited source result; sufficiency follows from the new
uniform upper. In particular every fixed positive polynomial budget
exponent suffices for this order, whereas no subpolynomial budget does.

Proof. Condition 1 implies 2 immediately. If 2 holds, (2.5), on the
intersection of the relevant neighborhoods, forces

$$
1+\log\min\{L_{M(s)},1/s\}
 \ge\frac{A_-}{C_T}\log(e/s).
\tag{7.1}
$$

Equation (2.8) bounds its left side above by
$1+\log C_L+r^{-1}\log(1+M(s))$. Absorb the fixed additive constant
for sufficiently small $s$. This proves condition 3, for example with
$\varepsilon=rA_-/(2C_T)$. This is exactly the necessity mechanism in
[SOURCE, Open problem 11.3][SOURCE]; no new necessary exponent is derived
from the chosen architecture.

Conversely, condition 3 implies
$M(s)\ge\tfrac12s^{-\varepsilon}$ eventually. In particular
$M(s)\ge\max\{M_0,4\}$ eventually. The lower comparison
$L_{M(s)}\ge(cM(s)/b)^{1/r}$ gives

$$
1+\log\min\{L_{M(s)},1/s\}
 \ge c_\varepsilon\log(e/s)
\tag{7.2}
$$

eventually for some $c_\varepsilon>0$: write $t=\log(1/s)$,
use $\log M(s)\ge\varepsilon t-\log2$, and take the minimum with $t$.
All fixed additive constants are absorbed as $t\to\infty$.
Theorem 6.1 applies to every such finite budget and supplies one common
table with both means at most
$(C_+/c_\varepsilon)s^{-(2r+1)}/\log(e/s)$. This is condition 1.
The implication is eventual at every sufficiently small $s$, including
oscillating budget families and discontinuous retuning. $\square$

**Corollary 7.2 (A declared full-scale budget and its limitation).**
For all sufficiently small $s$, taking
$J_s=\lfloor\log_2(\eta/s)\rfloor$ in Definition 5.1 gives exactly
$M_{J_s}$ listed configurations, at most $K(\eta/s)^r$, and both means
$O(s^{-(2r+1)}/\log(e/s))$. Also, for every fixed $\gamma>0$, an
available budget $M(s)=\lceil s^{-\gamma}\rceil$ eventually permits the
same paid order, with an upper constant allowed to depend on $\gamma$.
The sufficient exponent $r$ of the full-scale construction is not a
necessary exponent.

Proof. For small $s$, $J_s\ge1$, $s2^{J_s}\le\eta$ and
$J_s\asymp\log(e/s)$. Theorem 5.1 gives the first assertion and its
exact count. The polynomial budget satisfies condition 3 of Theorem 7.1
with any fixed $\varepsilon<\gamma$, giving the second assertion by its
budget-selected table (6.2). Since arbitrarily small fixed $\gamma>0$
are allowed, no positive exponent such as $r$ is forced when the paid
upper constant is free to depend on the family. Fixed sufficient budgets
have no full logarithmic gain, in agreement with the inherited fixed-
budget critical order. $\square$

## 8. A finite exact instance of the same mechanism

**Proposition 8.1 (An 84-configuration common table).** Take
$r=c=1$, $q=1/2$, $J=2$, $\delta=1/2$, and use the rows of Definition 5.1
with $H=14$ rather than its conservative asymptotic threshold. The exact
complete listed count is $3+27\cdot3=84$. Under both sources this table
stops almost surely, has finite paid mean, and has separate error less
than $1/10$. This is a finite-parameter assertion, with no claim that
$s=\log2$ is in the endpoint neighborhood of Theorem 5.1.

Proof. Here the zero matrix and reward vector are

$$
R=\begin{pmatrix}
1/2&1/2&0\\
0&3/4&1/4\\
0&0&1
\end{pmatrix},\qquad
v=(1/2,1/4,0)^{\mathsf T}.
\tag{8.1}
$$

After $k$ zeros the first two phase probabilities are
$(1/2)^k$ and $2[(3/4)^k-(1/2)^k]$. With
$Z_0(q)=q/(1-q)^2$ and $Z_1(q)=q(2-q)/(1-q)^2$, averaging these expressions
gives the two terminal phase laws

$$
\pi_0=(2/9,116/225,59/225),\qquad
\pi_1=(7/27,352/675,148/675).
\tag{8.2}
$$

Hence $m_0=6/25$, $m_1=13/50$, $\theta=1/4$, and $\Delta=1/50$.
The integer evidence increment is zero or $+1$ equiprobably in phase
one, identically zero in phase two, and $-1$ or zero equiprobably in
the dead phase. The upward and downward probabilities per gap are

$$
(u_0,v_0)=(1/9,59/450),\qquad
(u_1,v_1)=(7/54,74/675).
\tag{8.3}
$$

Both are positive; their signed drifts are $-1/50,+1/50$ in integer
evidence units. The finite drift argument (5.10) with this threshold
proves finite expected gap stopping under each source. The stopped
nearest-neighbor walk has no boundary overshoot. For its ratio
$\rho=v_i/u_i$, the process $\rho^{e_n}$ is a martingale, because
$u_i\rho+v_i/\rho+1-u_i-v_i=1$.
Bounded convergence at the already finite stop gives the ordinary
gambler's-ruin formulas

$$
e_0=\frac1{1+(59/50)^{14}},\qquad
e_1=\frac1{1+(175/148)^{14}}.
\tag{8.4}
$$

The exact integer inequalities $59^{14}>9\,50^{14}$ and
$175^{14}>9\,148^{14}$ prove $e_i<1/10$.
The signed boundary value has mean $14(1-2e_i)$, so
$\mathbb E_iG=700(1-2e_i)$. Source moment summation gives

$$
(\mu_0,\beta_0)=(4,2),\qquad
(\mu_1,\beta_1)=(11/3,20/11).
\tag{8.5}
$$

The exact paid means, using the same stationary first-wait convention,
are therefore

$$
\mathbb E_0T=3+2800(1-2e_0),\qquad
\mathbb E_1T=31/11+(7700/3)(1-2e_1).
\tag{8.6}
$$

All zeros after death and the terminal closing interval are included.
The 84 configurations include every one of the 27 evidence coordinates
paired with every phase, plus initialization and labels. The formula
rows supply both inputs even at unreachable edges. $\square$

## 9. Mathematical suppliers and unresolved boundaries

**Definition 9.1 (Literature and source correspondence).** The
source-specific occupation/reward/rounding composition and Theorems
4.1–7.1 are `repo-derived` ordinary deductions. The methods identified
below are `literature-attested` at their stated scopes. This attribution
does not assert worldwide priority for the composition.

| Supplier | Exact correspondence and transfer boundary |
| --- | --- |
| [Exact source classes and the renewal state/read frontier][SOURCE], Definitions 2.1 and 3.1, Lemma 2.3, Theorem 11.2, Open problem 11.3 | The identical normalized positive pair, stationary first wait, unrestricted retuned complete-configuration class, scalar moments, universal critical lower and its necessary growth condition. Equations (9.9)–(9.10) give predictable completed-gap payment. The present table supplies its own continuation, risk and state proof; the source is ordinary fallible theory, not independent validation of this upper. |
| [Critical multiscale renewal attainment][MULTISCALE], Theorems 9.1–9.2 and Section 10 | The exact same $F_0,F_1$, stationary first wait, source-blind $q$-retuned finite table, complete persistent-configuration accounting, and paid consecutive-bit resource contract. The supplier proves logarithmic existence with $M\le C(L+2)/(s^r\sqrt{H_L})$ and both paid means $O(s^{-(2r+1)}/H_L)$ whenever $sL\le\eta$, plus its fixed-$\theta$ specialization. Its Section 10 leaves minimum state and the full all-budget frontier open; its lower context is conditional attribution. This ordinary public source is fallible and is not independent verification of the present manuscript. The present source retains the distinct $O(2^{rJ})$ phase-table count, uniform all-sufficient-budget upper, and eventual positive-polynomial budget criterion. |
| Philippe Flajolet, *Approximate Counting: A Detailed Analysis*, BIT 25, 113–134, Section 1, printed pp. 114–116 | Starts at counter one and increments $j$ with probability $2^{-j}$. This is exactly the uncapped phase reader. Its approximate-count distribution theorems are not assumed to imply the discounted occupation estimates, the critical reward or paid testing bounds; those are proved here. |
| Lu Xia, Martijn Anthonissen, Michiel Hochstenbach and Barry Koren, *Improved stochastic rounding*, arXiv:2006.00489v1, Section 3, Corollary 3.2, Algorithm 3.1 | Distance-proportional adjacent-grid rounding and unbiasedness supply the classical update form. The source-dependent $\delta\mathbb E|V-\theta|$ control and its use at $\delta=J2^{-rJ}$ are proved in Theorem 4.1. No finite-precision implementation result is imported. |
| Marco Zamparo, *Renewal model for dependent binary sequences*, arXiv:2108.11293v2, Theorem 2.1 and Proposition 3.1 | Finite mean interval $S_2=K+1$ and first interval $S_1=\tau+1$ give (1.4), including $\tau=0$, and regeneration at visible ones. These results provide neither a free complete-gap port nor an observer memory bound. |
| Richard A. Flower and Martin E. Hellman, *Hypothesis Testing With Finite Memory in Finite Time*, IEEE TIT 18, 429–431, Introduction and Problem Statement, DOI 10.1109/TIT.1972.1054820 | Time-invariant possibly randomized updates of a finite-valued statistic and two input-conditioned stochastic matrices are the finite-table reference frame. Their iid binary-input fixed-horizon task and numerical small-machine conclusions do not supply this sequential renewal paid-time theorem or restrict its competitors to adjacent moves. |
| Steven R. Howard, Aaditya Ramdas, Jon McAuliffe and Jasjeet Sekhon, *Exponential line-crossing inequalities*, arXiv:1808.03204v5, Section 2.3, Lemma 1, equation (18) | A nonnegative adapted supermartingale starting at one has crossing probability at most the reciprocal boundary. Here the exact one-step exponential inequalities are proved for actual gap/coin increments, and a bounded-stopped proof is included. The general inequality supplies neither the observer states nor bit payment. |
| Emilie Kaufmann, Olivier Cappé and Aurélien Garivier, *On the Complexity of Best-Arm Identification in Multi-Armed Bandit Models*, arXiv:1407.4443v2, Lemma 1 and Remark 2 | Mutually absolutely continuous arm laws and an almost-surely finite stopping time yield an expected-count/KL bound on terminal-event binary entropy. This is sequential-information background. Acquisition of free iid arm observations cannot be substituted for actual paid renewal bits; the universal lower used here is the supplied one. |
| Howard et al., *Time-uniform, nonparametric, nonasymptotic confidence sequences*, arXiv:1810.08240v4, Section 3.1, Theorem 1 | Geometric stitching uses a sub-gamma process and its variance process, with a summable epoch error allocation. It is multiscale inference background, not an internal finite-state mechanism collecting gap-scale evidence. No variance-time index is made free here. |
| Tomer Berg, Or Ordentlich and Ofer Shayevitz, *Binary Hypothesis Testing with Deterministic Finite-Memory Decision Rules*, arXiv:2005.07445v1, Section I, Theorem 1 and Section IV | Its iid Bernoulli inputs, deterministic updates and asymptotic occupation error differ from the present stochastic retuned absorbing test. Its converse uses a lower bound on positive deterministic transition probabilities. That restriction is absent here and is not transferred. |

The repository's stopped multiplicative-likelihood and finite control
results concern other statement shapes. In particular bounded-horizon
likelihood-moment estimates do not supply the source-specific phase
occupation law or a complete counted realization of this logarithmic
upper. The older renewal continuation's pair-conditioned rounded product,
varying precision and deadline concern a different polynomial source
and resource contract. Neither is silently reused as this controller.
The cited classical primary results support their exact listed ports;
none of the inspected ports directly states the present complete theorem.
This bounded correspondence is not a claim that the entire literature
contains no such result.

**Definition 9.2 (Precision and physical realization boundary).** The
actual abstract model authorizes immutable real probabilities, including
the $q$-dependent midpoint $\theta$, adjacent-grid probabilities and
arbitrarily small positive edges. Their calibration, description length,
effective design computation, exact-coin realization and physical storage
or arithmetic costs are separate resources. No finite-precision or
physical implementation theorem follows from counting configurations.
Conversely those unpriced resources cannot be imposed as extra
restrictions on the present competitor class. Known-$q$ retuning is used
explicitly; unknown-$q$ adaptation and one $q$-independent table are
different questions.

The evidence grid is finite, not a real-valued persistent score. A table
with $M_J$ configurations can be indexed by
$\lceil\log_2M_J\rceil$ mutable bits, but that encoding does not measure
physical spacetime or price immutable probability precision. Proof
indices, holding times and final overshoots never become observer inputs.

**Open problem 9.3 (Sharp constants and capacities).** The matching
frontier identifies order up to source/risk constants, with a sufficient
threshold $M_0$. The minimum nonempty budget, exact finite-budget optimum,
sharp leading paid-time constants and the least memory growth for a
preassigned leading upper constant remain uncharacterized. The
$O(2^{rJ})$ count is sufficient, not a lower bound on every table's
configurations. The eventual logarithmic criterion permits any fixed
positive polynomial exponent when its time constant may vary; it does
not select a sharp necessary exponent $r$.

For a precise comparison under the common source and resource contract,
at a full permitted cutoff $L\asymp s^{-1}$ the public supplier's
Theorem 9.1 gives the sufficient count
$O(s^{-(r+1)}/\sqrt{\log(1/s)})$, while Corollary 7.2 here gives the
same logarithmic paid order with the sufficient count $O(s^{-r})$. This
compares two sufficient constructions only; it is not a universal state
lower bound, a claim of independent mechanisms, or a resolution of the
minimum-state question.

**Open problem 9.4 (Other sources and the broader recovery programme).**
No transfer is asserted to the rational-center polynomial $H_c$, sparse,
signed or oscillating perturbations, an upper tail envelope, varying
$r,c,\alpha$, or extra observation and workspace models. Such transfers
require their own normalized contrast, occupation and resource bridges.
In particular an upper envelope alone does not give the positive signed
quantity in (4.6), as the public source's sparse example demonstrates.
The native-tree exact rate and a minimal relational structure recovering
space, time, boundaries and memory from one another remain separate
unresolved mathematical objectives. The public supplier's Section 10
likewise leaves minimum state and the full all-budget frontier open, and
its lower context is conditional attribution rather than a new converse.
This source's retained result is the stronger ordinary critical
exact-renewal phase-table bound and uniform order gap under Definitions
1.1–1.3 and the credited converse; no substantive claim is inferred
solely from the supplier's publication.

[SOURCE]: https://github.com/the-omega-institute/trureturing/blob/665ad0afc598345e8372180eb5055e2e12f61137/docs/develop/theory/FIB_SOURCE_CLASS_RENEWAL_RESOURCE_FRONTIER.md
[MULTISCALE]: https://github.com/the-omega-institute/trureturing/blob/de2373d88086fe97e948407b3f25bfb81a9e899c/docs/develop/theory/FIB_CRITICAL_MULTISCALE_RENEWAL_ATTAINMENT.md
[FLAJOLET]: https://algo.inria.fr/flajolet/Publications/Flajolet85c.pdf
[ROUNDING]: https://arxiv.org/pdf/2006.00489v1
[ZAMPARO]: https://arxiv.org/pdf/2108.11293v2
[VILLE]: https://arxiv.org/pdf/1808.03204v5

## 追加锚（本行以下为增补区）
