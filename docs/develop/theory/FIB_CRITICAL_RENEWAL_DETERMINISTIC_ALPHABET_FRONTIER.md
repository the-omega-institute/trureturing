# Critical renewal testing: deterministic alphabet and paid-read order

## 1. Exact experiment and the deterministic question

**Definition 1.1 (Fixed parameters and source correspondence).** Fix an
integer $r\ge1$, a real $c>0$ and $0<\alpha<1/2$, before choosing any
neighborhood, budget or observer. Write $p=2r+1$. The common known
parameter is $q=e^{-s}$, where $s>0$. The two positive shapes are exactly

$$
F_0(k)=k^{2r-1},\qquad
F_1(k)=k^{2r-1}+c k^{r-1}\qquad(k=1,2,\ldots).
\tag{1.1}
$$

All constants below may depend on the fixed triple $(r,c,\alpha)$;
no uniformity over changing triples is asserted. Logarithms without a
subscript are natural, and $\mathrm e=\exp(1)$.

Use the following mathematical source names:

- [C], *Critical renewal observation: a counted logarithmic frontier*;
- [S], *Exact source classes and the renewal state/read frontier*;
- [P], *Critical renewal testing: dyadic precision and midpoint calibration*.

The exact experiment and unrestricted observer contract are [C,
Definitions 1.1–1.3]. The source-class correspondence is [S] with
$d=2r-1$ and $a=d+1=2r$. The unrestricted critical order and its eventual
budget criterion are already given in [C, Theorems 6.1–7.1], with the
lower credited to [S, Theorem 11.2]. Theorems 3.1–6.1 below give a
deterministic attainment of that order with a different complete table
and a larger sufficient configuration count. Theorem 7.1 gives its
deterministic eventual-growth consequence. These deductions concern
ordinary mathematical proofs; the cited frontier is not a new lower
bound of this volume.

**Definition 1.2 (Full normalized law and the stationary first wait).**
For $i\in\{0,1\}$ put

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,&
f_i(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),& f_i(0)&=0,\\
S_i(u)&=\sum_{k\ge u}f_i(k)\quad(u\ge0),&
\mu_i&=\sum_{k\ge1}(k+1)f_i(k),\\
\beta_i&=\frac{\sum_{k\ge1}k(k+1)f_i(k)}{2\mu_i}.
\end{aligned}
\tag{1.2}
$$

Draw $\tau$ with

$$
\mathsf P_i(\tau=u)=\frac{S_i(u)}{\mu_i}
\qquad(u=0,1,2,\ldots).
\tag{1.3}
$$

Independently draw $K_1,K_2,\ldots$ iid with law $f_i$. The one bits
of the single history $X_0,X_1,\ldots$ occur exactly at

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{h=1}^n(K_h+1)\quad(n\ge1).
\tag{1.4}
$$

All other bits are zero. Thus $K_n$ counts zeros in a later gap, and
$K_n+1$ includes its closing tick. The first wait is not a draw from
$f_i$. In particular $S_i(0)=S_i(1)=1$ and $\tau=0$ is allowed.
Polynomial-geometric summability makes every fixed polynomial moment
finite at each $0<q<1$. The stationary convention gives

$$
\sum_{u\ge0}S_i(u)=\mu_i,\qquad \mathbb E_i\tau=\beta_i.
\tag{1.5}
$$

These identities and stationarity are [C, Definition 1.2] and [S,
Lemma 2.2]. Their countdown is an analytical variable, never an observer
input. The equilibrium interval correspondence cited in [C] is
$S_2=K+1$, $S_1=\tau+1$ in Zamparo's notation.

**Definition 1.3 (One common table and complete compliance).** At a
selected known $(s,M)$, one source-blind table is used under both labels
with the same initialization. It may depend on $(s,M,r,c,\alpha)$ and
may retune discontinuously between different selections. During a run
its state set and two bit-conditioned rows are fixed. Every nonterminal
configuration undertakes exactly the next actual read. Entry into $d_i$
internally emits $D=i$ and stops. Label rows on unused future bits fix
the label.

The budget $M$ counts all possible complete persistent configurations,
including initialization, both labels, registers, control and working
phases, buffers, retained seeds and retained random consequences. It
counts unreachable and arbitrarily improbable configurations too.
The observation is only the uninterrupted consecutive history (1.4).
There is no external age, elapsed time, read count, gap length, program
counter, archive, tape, true-label port, parameter response, separate
history, source reset, skipped suffix, free gap or stopping-time decoder.
Any retained distinction belongs to the counted state set. A formula
for a row specifies immutable successors; it supplies no additional
arithmetic workspace or internal action during observation.

If the read prefix is $X_0,\ldots,X_{T-1}$, its paid cost is $T$.
Every initial zero and tick, rejected suffix, holding interval and
terminal read is paid. General competitors may stop in a partial gap,
whose read prefix remains paid. Write $\mathfrak A_M(e^{-s},\alpha)$
for the unrestricted stochastic class of [C, Definition 1.3] satisfying
all six requirements

$$
\begin{gathered}
\mathsf P_0(D=1)\le\alpha,\qquad
\mathsf P_1(D=0)\le\alpha,\\
\mathsf P_0(T<\infty)=1,\qquad
\mathsf P_1(T<\infty)=1,\\
\mathbb E_0T<\infty,\qquad \mathbb E_1T<\infty.
\end{gathered}
\tag{1.6}
$$

In that class fresh transition randomness is independent of the source
and previous fresh randomness, and immutable row precision is
unrestricted. Let $\mathfrak A_M^{\rm det}(e^{-s},\alpha)$ be the
subclass with deterministic initialization and rows. For an integer
$B\ge1$, let $\mathfrak A_M^{(B)}(e^{-s},\alpha)$ be the direct-table
subclass whose probabilities, including initialization, are in
$2^{-B}\mathbb Z$. Thus

$$
\mathfrak A_M^{\rm det}\subseteq\mathfrak A_M^{(B)}
\subseteq\mathfrak A_M.
\tag{1.7}
$$

Both means in every constructive assertion below refer to the very same
selected table, independent of the true label.

## 2. Inherited estimates and the credited comparison order

**Assumption 2.1 (Exact scalar source estimates).** Reuse [C, equation
(2.3)], with its source-class basis [S, Lemma 2.3]. Choose positive
$s_*<1,z_-,z_+,C_\mu,C_\beta$, before every cap and budget, such that
for both labels and $0<s<s_*$,

$$
z_-s^{-2r}\le Z_i(e^{-s})\le z_+s^{-2r},\qquad
\mu_i\le C_\mu/s,\qquad 1+\beta_i\le C_\beta/s.
\tag{2.1}
$$

The exact-source asymptotics supporting this choice are

$$
Z_i(e^{-s})=(2r-1)!s^{-2r}(1+O(s)),\qquad
\mu_i=2r/s+O(1),\qquad
\beta_i=(2r+1)/(2s)+O(1).
\tag{2.2}
$$

They concern the full normalizers in (1.2), not a tail envelope or a
replacement observation law. No phase-reader estimate from [C] or
finite-precision estimate from [P] is a premise of the deterministic
construction.

**Definition 2.2 (Credited frontier and converse scope).** Put

$$
\begin{aligned}
b&=1-2\alpha,\\
L_M&=\max\left\{1,
\left\lceil\left(\frac{2c(M-2)}b\right)^{1/r}\right\rceil\right\},\\
\Psi(s,M)&=\frac{s^{-p}}{1+\log\min\{L_M,1/s\}}
\qquad(0<s<1,\ M\ge2).
\end{aligned}
\tag{2.3}
$$

The inherited lower theorem, [S, Theorem 11.2] at $d=2r-1$, equivalently
[C, Definition 2.2 and the lower of Theorem 6.1], supplies $s_->0$ and
$C_->0$, depending only on the fixed triple, such that

$$
\forall\,0<s<s_-\quad\forall\,M\ge2\quad
\forall\,\mathcal A\in\mathfrak A_M(e^{-s},\alpha)\quad
\forall\,i\in\{0,1\}:\qquad
\mathbb E_i^{\mathcal A}T\ge C_-\Psi(s,M).
\tag{2.4}
$$

Budgets here and below are finite integers. This is an attributed
ordinary result. Its neighborhood precedes every budget and design.
It includes arbitrary stochastic retuning, initial randomization,
arbitrarily small positive edges and partial-gap stopping, retaining
both risks, both almost-sure stops and both finite means. Its normalized
clipped-law entropy, finite-configuration hitting comparison and actual
tick-price interfaces are developed in [S, Sections 3–7]. Subclass
inclusion in (1.7) retains all these lower quantifiers.

The ceiling in (2.3) also gives the useful inherited comparison

$$
L_M\le C_LM^{1/r},\qquad
C_L=1+(2c/b)^{1/r}\ge1.
\tag{2.5}
$$

The unrestricted all-sufficient-budget upper and the eventual criterion
are already [C, Theorems 6.1–7.1]. The task of the following construction
is their attainment with the fixed probability alphabet $\{0,1\}$.

## 3. Conditional contrast and deterministic integer rewards

**Theorem 3.1 (Uniform short-gap contrast; T1).** Define

$$
L_0=\left\lceil\exp(16r^2\mathrm e^3)\right\rceil,\qquad
W=2r\mathrm e(1+c),\qquad
D=\frac{c}{4\mathrm e(1+c)}.
\tag{3.1}
$$

For every integer $L\ge L_0$ and every $s>0$ with $sL\le1$, put
$J=1+\log L$, $I=J/L^{2r}$ and $h(k)=k^{-r}$. Define the actual
truncated normalizers and conditional laws by

$$
Z_i^L=\sum_{k=1}^LF_i(k)e^{-sk},\qquad
g_i(k)=\frac{F_i(k)e^{-sk}}{Z_i^L}\quad(1\le k\le L).
\tag{3.2}
$$

Thus $g_i$ is $f_i$ conditioned on $K\le L$, using that source's own
normalizer. Write

$$
m_i=\mathbb E_{g_i}h,\qquad
\theta=(m_0+m_1)/2,\qquad \Delta=m_1-m_0.
\tag{3.3}
$$

Then, throughout this entire cap range,

$$
0<I\le1,\qquad 0\le\theta\le1,\qquad
\mathbb E_{g_i}h^2\le WI,\qquad
\theta^2\le WI,\qquad \Delta\ge DI>0.
\tag{3.4}
$$

Proof. Let $\mathcal H_L=\sum_{k=1}^L1/k$, and set

$$
\begin{aligned}
B_L&=\sum_{k=1}^Lk^{2r-1}e^{-sk},\\
A_L&=\sum_{k=1}^Lk^{r-1}e^{-sk},\\
C_L^{\rm harm}&=\sum_{k=1}^Lk^{-1}e^{-sk}.
\end{aligned}
\tag{3.5}
$$

The condition $sL\le1$ puts all truncated exponential weights in
$[\mathrm e^{-1},1]$. Integral comparison for the nondecreasing
function $x^{2r-1}$ and termwise upper bounds give

$$
\frac{L^{2r}}{2r\mathrm e}\le B_L\le L^{2r},\qquad
A_L\le L^r,\qquad
\mathcal H_L/\mathrm e\le C_L^{\rm harm}\le\mathcal H_L.
\tag{3.6}
$$

In particular

$$
m_0=\frac{A_L}{B_L}\le2r\mathrm e L^{-r},\qquad
\frac{\mathcal H_L}{\mathrm e L^{2r}}
\le\mathbb E_{g_0}h^2=\frac{C_L^{\rm harm}}{B_L}
\le\frac{2r\mathrm e\mathcal H_L}{L^{2r}}.
\tag{3.7}
$$

The harmonic estimates $\mathcal H_L\ge1$,
$\mathcal H_L\ge\log L$ and $\mathcal H_L\le1+\log L$ imply
$J/2\le\mathcal H_L\le J$. Since $L\ge L_0$ makes
$J\ge16r^2\mathrm e^3$, (3.7) yields

$$
\mathbb E_{g_0}h^2\ge I/(2\mathrm e),\qquad
m_0^2\le4r^2\mathrm e^2L^{-2r}\le I/(4\mathrm e),\qquad
\operatorname{Var}_{g_0}(h)\ge I/(4\mathrm e).
\tag{3.8}
$$

For the exact positive pair, $Z_0^L=B_L$ and
$Z_1^L=B_L+cA_L=B_L(1+cm_0)$. Therefore the conditional likelihood
ratio and conditional mean contrast are exactly

$$
\frac{g_1(k)}{g_0(k)}=\frac{1+ch(k)}{1+cm_0},\qquad
m_1=\frac{m_0+c\mathbb E_{g_0}h^2}{1+cm_0},\qquad
\Delta=\frac{c\operatorname{Var}_{g_0}(h)}{1+cm_0}.
\tag{3.9}
$$

This is the classical linear-tilt variance identity applied to the
specified conditional laws. Since $0<h\le1$, $0\le m_0\le1$, and
(3.8) proves $\Delta\ge DI$. The likelihood ratio in (3.9) is at
most $1+c$. Hence (3.7) and $\mathcal H_L\le J$ give
$\mathbb E_{g_i}h^2\le WI$ for both labels. Jensen's inequality gives

$$
\theta^2\le(m_0^2+m_1^2)/2\le WI.
\tag{3.10}
$$

Both conditional means are in $[0,1]$, so the same is true of
$\theta$. Finally $J=1+\log L\le L\le L^{2r}$ gives $0<I\le1$.
Every estimate includes the endpoints of the integer truncation.
$\square$

**Theorem 3.2 (Integer reward and common integer center; T2).** Under
Theorem 3.1, choose

$$
N=\left\lceil\frac8{DI}\right\rceil,
\qquad \delta=1/N,
\qquad b_k=\left\lfloor\frac N{k^r}\right\rfloor
\quad(1\le k\le L).
\tag{3.11}
$$

Choose any integer $a\in\{0,\ldots,N\}$ satisfying
$|a/N-\theta|\le\delta$; $a=\lfloor N\theta\rfloor$ is one such
choice. For an actual full gap set

$$
U(K)=
\begin{cases}
(b_K-a)/N,&1\le K\le L,\\
0,&K>L.
\end{cases}
\qquad V=8W+8.
\tag{3.12}
$$

The same choice of $a$ gives

$$
|U|\le1,\qquad
-\mathbb E_{g_0}U\ge\Delta/4,\qquad
\mathbb E_{g_1}U\ge\Delta/4,\qquad
\mathbb E_{g_i}U^2\le VI.
\tag{3.13}
$$

Proof. From (3.11),

$$
\delta\le DI/8\le\Delta/8,\qquad
\delta\le I\le1,
\tag{3.14}
$$

where $0<D<1$. Each $b_k$ and $a$ is in $\{0,\ldots,N\}$,
so $|(b_k-a)/N|\le1$ exactly. For every accepted integer $k$,

$$
0\le h(k)-b_k/N<\delta,\qquad
\left|\frac{b_k-a}{N}-(h(k)-\theta)\right|\le2\delta.
\tag{3.15}
$$

The unquantized conditional means are $-\Delta/2$ and $\Delta/2$.
Thus either oriented mean after quantization is at least
$\Delta/2-2\delta\ge\Delta/4$. No unbiased rounding is used, and
the center is common to both labels.

Put $x=h-\theta$. Theorem 3.1 gives
$\mathbb E_{g_i}x^2\le2\mathbb E_{g_i}h^2+2\theta^2\le4WI$.
Using (3.15), $(x+y)^2\le2x^2+2y^2$ and $\delta^2\le I$ proves

$$
\mathbb E_{g_i}U^2\le8WI+8\delta^2\le(8W+8)I=VI.
\tag{3.16}
$$

The support bound also holds on rejected gaps, where $U=0$.
Exact grid equalities and endpoint centers require no exclusions.
The integers specify immutable destination choices. Neither $a/N$
nor an arithmetic calculation of $b_k-a$ is a mutable field of the
table constructed below. $\square$

**Theorem 3.3 (Full normalized signal and noise; T3).** Use the source
constants of Assumption 2.1 and set

$$
\xi_-=\frac1{2r\mathrm e z_+},\qquad
\xi_+=\frac{1+c}{z_-},\qquad
g=\xi_-D/4,\qquad v=\xi_+V.
\tag{3.17}
$$

For every $0<s<s_*$ and every cap allowed in Theorem 3.1, under the
full gap laws $f_i$ the increment (3.12) satisfies

$$
-\mathbb E_0U\ge g s^{2r}J,\qquad
\mathbb E_1U\ge g s^{2r}J,\qquad
\mathbb E_iU^2\le v s^{2r}J,\qquad |U|\le1.
\tag{3.18}
$$

Proof. Let $\pi_i=\mathsf P_i(K\le L)=Z_i^L/Z_i$. By positivity
and the exact shapes,
$B_L\le Z_i^L\le(1+c)B_L$. Equations (2.1) and (3.6) therefore give

$$
\xi_-s^{2r}L^{2r}\le\pi_i
\le\xi_+s^{2r}L^{2r}.
\tag{3.19}
$$

Each $\pi_i$ uses its own full and truncated normalizers. They have
not been equated. Because the actual increment is zero on every
$K>L$, the exact return from conditioning to the full laws is

$$
\mathbb E_iU=\pi_i\mathbb E_{g_i}U,\qquad
\mathbb E_iU^2=\pi_i\mathbb E_{g_i}U^2.
\tag{3.20}
$$

Insert (3.13), $\Delta\ge DI$ and (3.19). Each oriented mean is at
least $\xi_-s^{2r}L^{2r}DI/4=gs^{2r}J$, and each second moment is
at most $\xi_+s^{2r}L^{2r}VI=vs^{2r}J$. The support bound follows
from Theorem 3.2.

In particular the reward and center quantization errors of (3.15) occur
only on $K\le L$. Their full-law effect is multiplied by that event's
actual probability. There is no center update on a rejected gap.
An error of this conditional size applied on every long gap would not
obey (3.20). Conditioning here describes a law mathematically; it
provides no free accepted sample. $\square$

## 4. The complete deterministic bit table

**Definition 4.1 (Threshold, states and every input row).** Fix once

$$
\lambda=\min\{1,g/(\mathrm e v)\},\qquad
A=\frac{\log(1/\alpha)}\lambda.
\tag{4.1}
$$

At a selected allowed $s,L$, use $N,\delta,a,b_k$ from Theorem 3.2
and put $H=\lceil AN\rceil$. The full state set is

$$
\{w,d_0,d_1\}\cup
\{(j,z):j\in\mathbb Z,\ -H<j<H,\quad
z\in\{0,1,\ldots,L,\mathsf{overflow}\}\}.
\tag{4.2}
$$

Initialize deterministically in $w$ under both source laws. Every
nonlabel configuration undertakes the next actual read. Entry into
$d_i$ emits $D=i$ and stops. For every integer $u$ define the immutable
successor map

$$
\Gamma(u)=
\begin{cases}
d_1,&u\ge H,\\
d_0,&u\le-H,\\
(u,0),&-H<u<H.
\end{cases}
\qquad
n_z=
\begin{cases}
b_z-a,&1\le z\le L,\\
0,&z=0\text{ or }z=\mathsf{overflow}.
\end{cases}
\tag{4.3}
$$

The complete rows are as follows. Each listed successor has probability
one; every other entry has probability zero.

| Configuration and just-read bit | Successor |
| --- | --- |
| $w$, zero | $w$ |
| $w$, one | $(0,0)$ |
| $(j,z)$, zero, $0\le z<L$ | $(j,z+1)$ |
| $(j,L)$, zero | $(j,\mathsf{overflow})$ |
| $(j,\mathsf{overflow})$, zero | $(j,\mathsf{overflow})$ |
| $(j,z)$, one, every $z\in\{0,\ldots,L,\mathsf{overflow}\}$ | $\Gamma(j+n_z)$ |
| $d_0$, either unused future bit | $d_0$ |
| $d_1$, either unused future bit | $d_1$ |

The formulas for $\Gamma$ and $n_z$ select installed destinations.
A read applies its row directly and has no pending arithmetic step.

**Theorem 4.2 (Realization and exact complete count; T4).** Definition
4.1 is one common deterministic table realizing (3.12) at completed
post-first-tick gaps. Its exact listed number of configurations is

$$
M_L=3+(2H-1)(L+2)
=3+\bigl(2\lceil AN\rceil-1\bigr)(L+2).
\tag{4.4}
$$

All installed probabilities and initialization belong to the fixed
alphabet $\{0,1\}$, independently of $s,L$ and every budget. In
particular $B_*=1$ suffices for direct dyadic rows. A literal immutable
description needs at most

$$
2M_L\lceil\log_2M_L\rceil
\tag{4.5}
$$

destination bits, plus a header for the format, dimensions and
distinguished states.

Proof. Each row gives a unique successor in the declared state set.
The waiting state consumes all initial zeros and the first tick,
including the case $\tau=0$. Induction on the zeros after any read
tick shows that $z$ is their exact count up to $L$ and is overflow
thereafter. At the actual closing one its integer increment is
$b_K-a$ if $K\le L$ and zero if $K>L$. In units $\delta=1/N$
this is exactly (3.12). At a nonterminal closing tick the next phase
is zero. This resets the finite phase without resetting the source.

On a rejected gap the overflow state reads every remaining zero and
its actual closing one. Consecutive-one input rows at phase zero are
also defined, even though $f_i(0)=0$ makes those post-first-tick
histories impossible. Label rows specify both unused inputs; they
do not undertake further reads after entry.

There are $2H-1$ evidence indices and $L+2$ zero-count phases.
Every pair is counted, including unreachable pairs. Adding the waiting
state and both labels proves (4.4). The only active retained
distinctions are the two coordinates in (4.2). The bounded zero
counter is part of this counted product. There is no retained gap
index, read count, unbounded gap length, source age, clock, seed,
archive, real score, residual, pending update or arithmetic workspace.
An evidence overshoot is sent immediately to its label and is not
stored as another configuration. The integer center changes immutable
successors identically under both labels.

All rows and initialization are deterministic, so their probabilities
are in $\{0,1\}\subset2^{-B}\mathbb Z$ for every integer $B\ge1$.
No fresh transition randomness or internal coin step is required.
Numbering the states, each of their two rows has one successor index
of $\lceil\log_2M_L\rceil$ bits, which gives (4.5). This is a
description upper for the immutable table, separate from the number
of persistent configurations. $\square$

## 5. Simultaneous risks, finite stopping and fully paid means

**Theorem 5.1 (All six obligations on the same table; T5).** For
$0<s<s_*$ and every integer $L\ge L_0$ with $sL\le1$, the table of
Definition 4.1 meets (1.6). If $G$ is the number of its completed
post-first-tick gaps through absorption, then under both labels

$$
\mathbb E_iG\le\frac{A+2}{g s^{2r}J}<\infty.
\tag{5.1}
$$

Pathwise through its actual terminal read and in expectation,

$$
\begin{aligned}
T&=1+\tau+\sum_{n=1}^{G}(K_n+1),\\
\mathbb E_iT&=1+\beta_i+\mu_i\mathbb E_iG
\le C_T\frac{s^{-p}}J,\\
C_T&=C_\beta+\frac{C_\mu(A+2)}g.
\end{aligned}
\tag{5.2}
$$

All constants precede every $s,L$ and budget.

Proof. On the probability space of the original source history, use
the potential iid gaps already specified in Definition 1.2 and set
$U_n=U(K_n)$. The pairs $(K_n,U_n)$ are iid and independent of $\tau$;
their coordinates are generally dependent. Extending the sequence
after a stop is only an analytical continuation of the same history.
The phase starts at zero after every nonterminal tick and its next
increment does not depend on $j$. Thus the potential process agrees
with the installed table until exit.

For proof variables only, put

$$
\mathcal S_0=0,\qquad
\mathcal S_n=\sum_{h=1}^nU_h,\qquad
G=\inf\{n\ge1:|\mathcal S_n|\ge H\delta\}.
\tag{5.3}
$$

Before exit the table's evidence coordinate is $j=\mathcal S_n/\delta$.
At exit $\Gamma$ emits precisely the crossed label. Neither the proof
score nor its terminal overshoot is a runtime field or a stopping-time
decoder. For every finite $m$,

$$
|\mathcal S_{G\wedge m}|\le H\delta+1
\le A+\delta+1\le A+2.
\tag{5.4}
$$

The first inequality uses $|U|\le1$, and the second uses
$H=\lceil AN\rceil$, $\delta=1/N$.

Let $\mathcal F_n$ be generated by $\tau,K_1,\ldots,K_n$.
Use $\sigma_0=-1,\sigma_1=1$ solely to orient the proof, and let
$d_i^{\rm drift}=\sigma_i\mathbb E_iU\ge gs^{2r}J$.
The event $\{G\ge n\}$ is in $\mathcal F_{n-1}$, independent of
the next potential pair. Finite conditional expectation gives

$$
\begin{aligned}
\mathbb E_i[\sigma_i\mathcal S_{G\wedge m}]
&=\sum_{n=1}^m\mathbb E_i[
\mathbf1_{\{G\ge n\}}\sigma_iU_n]\\
&=d_i^{\rm drift}\sum_{n=1}^m\mathsf P_i(G\ge n)
=d_i^{\rm drift}\mathbb E_i(G\wedge m)
\le A+2.
\end{aligned}
\tag{5.5}
$$

Monotone convergence on the middle quantity proves (5.1). Consequently
$G<\infty$ almost surely under both laws. The first wait and every
individual gap are almost surely finite, so the actual read stop is
almost surely finite too. This establishes finite stopping before any
infinite stopping limit is used.

For $|u|\le1$ and $0<\lambda\le1$, Taylor's integral remainder gives

$$
e^{\lambda u}\le1+\lambda u+
\frac{\mathrm e}{2}\lambda^2u^2.
\tag{5.6}
$$

By Theorem 3.3 and $\lambda\le g/(\mathrm e v)$,

$$
\begin{aligned}
\mathbb E_0e^{\lambda U}
&\le1-\lambda gs^{2r}J
+\frac{\mathrm e}{2}\lambda^2vs^{2r}J\\
&\le1-\frac\lambda2gs^{2r}J\le1.
\end{aligned}
\tag{5.7}
$$

Under label one the identical calculation applied to $-U$ gives
$\mathbb E_1e^{-\lambda U}\le1$. Both inequalities use the actual
full increment laws of the same table. Conditional on $\mathcal F_{m-1}$,
the next gap is independent on the event the process is live, and the
stopped value is constant otherwise. Hence
$\exp(\lambda\mathcal S_{G\wedge m})$ under label zero and
$\exp(-\lambda\mathcal S_{G\wedge m})$ under label one are
nonnegative supermartingales starting at one.

By (5.4), these stopped exponentials are bounded by
$\exp(\lambda(A+2))$. The already proved almost-sure finiteness of
$G$ permits bounded convergence. At the wrong exit the corresponding
terminal exponential is at least $\exp(\lambda H\delta)$.
Therefore

$$
\mathsf P_0(D=1)\le e^{-\lambda H\delta}\le\alpha,
\qquad
\mathsf P_1(D=0)\le e^{-\lambda H\delta}\le\alpha,
\tag{5.8}
$$

because $H\delta\ge A$ and $e^{-\lambda A}=\alpha$.
This is the classical exponential-supermartingale crossing argument,
with the finite-drift and bounded-limit discipline also used in [C,
Theorem 5.1]. The signs $\sigma_i$ never enter the installed rows.

This table stops on a completed closing tick after the first tick.
Its actual cost is exactly the first line of (5.2). It includes every
initial zero, the first tick, all accepted and rejected gaps, every
overflow suffix and the final closing tick. For each $n$ the event
$\{G\ge n\}$ is determined before gap $n$, and is independent of
the next $K_n$. Tonelli's theorem therefore gives

$$
\begin{aligned}
\mathbb E_i\sum_{n=1}^G(K_n+1)
&=\sum_{n\ge1}\mathbb E_i[
\mathbf1_{\{G\ge n\}}(K_n+1)]\\
&=\mu_i\sum_{n\ge1}\mathsf P_i(G\ge n)
=\mu_i\mathbb E_iG.
\end{aligned}
\tag{5.9}
$$

This is predictable completed-gap payment, as in [S, equations
(9.9)–(9.10)] and [C, equations (5.14)–(5.15)]. It assumes neither
independence of $K_n$ from its own $U_n$ nor independence of a duration
from the event that it causes absorption. The full-gap identity is
for this construction; arbitrary competitors may have terminal partial
gaps and remain governed by Definition 1.3.

Combining (5.1), (5.9), (1.5) and (2.1) yields both finite means and

$$
\mathbb E_iT\le C_\beta/s+
\frac{C_\mu(A+2)}g\frac{s^{-p}}J.
\tag{5.10}
$$

Finally $J\le L^{2r}$ and $sL\le1$ imply
$s^{2r}J\le(sL)^{2r}\le1$. Consequently
$C_\beta/s\le C_\beta s^{-p}/J$, giving the stated $C_T$.
Both risks, both actual almost-sure stops and both finite paid means
have now been proved on one common table. $\square$

## 6. Uniform selection for every sufficient finite budget

**Theorem 6.1 (Deterministic all-sufficient-budget attainment; T6).**
Define the fixed constants

$$
C_N=8/D+1,\qquad K=4AC_N+4,\qquad
M_{\rm det}=\left\lceil K(2L_0)^p\right\rceil.
\tag{6.1}
$$

The exact count (4.4) obeys, for every allowed cap,

$$
M_L\le K\frac{L^p}{1+\log L}\le KL^p.
\tag{6.2}
$$

Choose once

$$
0<s_0<\min\{s_*,s_-,1/(2L_0),1/2\}.
\tag{6.3}
$$

For every $0<s<s_0$ and finite integer $M\ge M_{\rm det}$, set

$$
y=\min\{(M/K)^{1/p},1/s\},\qquad L=\lfloor y\rfloor.
\tag{6.4}
$$

The table of Definition 4.1 then has at most $M$ complete configurations,
belongs to $\mathfrak A_M^{\rm det}(e^{-s},\alpha)$, and satisfies

$$
\max_i\mathbb E_iT\le C_+\Psi(s,M)
\tag{6.5}
$$

with one constant $C_+>0$ independent of $s,M$. The credited lower
(2.4) holds on this same neighborhood separately for each label of
every compliant deterministic or direct fixed-dyadic competitor at
every finite $M\ge2$.

Proof. Since $I\le1$, the ceiling in (3.11) gives

$$
N\le\frac{8/D+1}{I}
=C_N\frac{L^{2r}}J,\qquad
H\le AC_N\frac{L^{2r}}J+1.
\tag{6.6}
$$

For $L\ge L_0\ge2$, $L+2\le2L$. Thus the exact count satisfies

$$
M_L\le3+4AC_N\frac{L^p}J+2L.
\tag{6.7}
$$

Because $J\le L$ and $p\ge3$,
$4L^p/J\ge4L^{p-1}\ge4L^2\ge3+2L$ for $L\ge2$.
This proves (6.2) without deleting any listed configuration.

The choices of $M_{\rm det}$ and $s_0$ imply $y\ge2L_0$.
Consequently

$$
L\ge y/2\ge L_0,\qquad sL\le1,\qquad
M_L\le KL^p\le Ky^p\le M.
\tag{6.8}
$$

All hypotheses of Theorems 3.1–5.1 hold. In particular a single selected
table supplies both risks, both almost-sure stops and both finite means
throughout one neighborhood fixed before every budget.

To compare the upper with the exact credited denominator (2.3), use
$C_L$ from (2.5) and put

$$
C_*=\max\{1,C_LK^{1/r}\},\qquad
C_3=1+\log C_*+\frac pr(1+\log2).
\tag{6.9}
$$

If $y=(M/K)^{1/p}$ is the budget branch of (6.4), then

$$
\min\{L_M,1/s\}\le C_LM^{1/r}
=C_LK^{1/r}y^{p/r}.
\tag{6.10}
$$

If $y=1/s$ is the source branch, the minimum is at most
$y\le y^{p/r}$, since $y\ge1$ and $p/r>1$. At a tie either
argument applies. Together with $y\le2L$ these give

$$
\min\{L_M,1/s\}\le C_*(2L)^{p/r},\qquad
1+\log\min\{L_M,1/s\}\le C_3(1+\log L)=C_3J.
\tag{6.11}
$$

Indeed the logarithm of the first bound is at most
$\log C_*+(p/r)(\log2+\log L)$, and the chosen $C_3$ bounds
its constant and $\log L$ coefficients. Theorem 5.1 therefore yields

$$
\max_i\mathbb E_iT
\le C_T\frac{s^{-p}}J
\le C_TC_3\frac{s^{-p}}{1+\log\min\{L_M,1/s\}}.
\tag{6.12}
$$

Take $C_+=C_TC_3$. All constants and the sufficient threshold precede
every budget. No assumption of small $sM^{1/r}$ or budget-dependent
shrinking of $s_0$ occurs.

For the lower comparison, (1.7) places every compliant deterministic
or fixed-dyadic table in the unrestricted class of (2.4). Applying
that inherited theorem proves the last assertion. This step adds no
new converse; in particular it does not infer any lower bound from
the count of the constructed table. $\square$

## 7. Eventual logarithmic gain with deterministic rows

**Theorem 7.1 (Exact eventual budget criterion; C1).** Let $M(s)\ge2$
be any finite integer-valued function on $(0,\bar s)$, without
monotonicity or regularity assumptions. The following are equivalent:

1. There are $0<C<\infty$ and $s_1>0$ such that for every $0<s<s_1$
   one can select a common table
   $\mathcal A_s\in\mathfrak A_{M(s)}^{\rm det}(e^{-s},\alpha)$ with
   $\max_i\mathbb E_i^{\mathcal A_s}T
   \le Cs^{-p}/\log(\mathrm e/s)$.
2. The same holds with one fixed target $i_\star\in\{0,1\}$ in the
   paid upper. Each selected table still satisfies both risks, both
   almost-sure stops and both finite means.
3. There are $\varepsilon>0$ and $s_2>0$ such that
   $\log(1+M(s))\ge\varepsilon\log(1/s)$ for every $0<s<s_2$.

All neighborhoods are restricted to $s<\min\{\bar s,1\}$. Constants
in these eventual conditions may depend on the budget family. The
necessity is inherited from [S, Theorem 11.2 and Open problem 11.3]
and [C, Theorem 7.1]; the deterministic sufficiency follows from
Theorem 6.1. In particular every fixed positive polynomial budget
exponent suffices when the paid upper constant may depend on that
exponent.

Proof. Condition 1 implies 2. If condition 2 holds, use the credited
lower (2.4) for its fixed target on the intersection of the applicable
neighborhoods. It forces

$$
1+\log\min\{L_{M(s)},1/s\}
\ge(C_-/C)\log(\mathrm e/s).
\tag{7.1}
$$

The left side is at most
$1+\log C_L+r^{-1}\log(1+M(s))$ by (2.5). Absorbing the fixed
additive constant as $s\downarrow0$ gives condition 3, for example
with $\varepsilon=rC_-/(2C)$ after further restricting the
neighborhood. Opposing compliance requirements have not been removed.

Conversely, condition 3 gives

$$
M(s)\ge s^{-\varepsilon}-1
\ge\tfrac12s^{-\varepsilon}
\tag{7.2}
$$

eventually, so $M(s)\ge M_{\rm det}$ eventually. For the cap selected
in (6.4), $L\ge y/2$ yields

$$
\log L\ge
\min\left\{\frac{\log M(s)-\log K}{p},\log(1/s)\right\}-\log2.
\tag{7.3}
$$

By (7.2) the right side is at least a positive constant times
$\log(\mathrm e/s)$ for all sufficiently small $s$. More explicitly,
put $\eta_\varepsilon=\min\{\varepsilon/p,1\}>0$ and
$t=\log(1/s)$. The minimum in (7.3) is at least
$\eta_\varepsilon t-(\log2+\log K)/p$, and its fixed losses can
be absorbed into, for example, a lower bound
$(\eta_\varepsilon/4)(1+t)$ once $t$ is sufficiently large.
Theorem 5.1 now supplies both means of the one selected deterministic
table at most a fixed multiple of $s^{-p}/\log(\mathrm e/s)$.
This is condition 1.

Every step is pointwise at each sufficiently small $s$, so the proof
covers oscillating finite budgets and discontinuous retuning. For
$M(s)=\lceil s^{-\gamma}\rceil$ with any fixed $\gamma>0$, condition
3 holds with any $0<\varepsilon<\gamma$. No particular positive
exponent, such as the cap-count exponent $p$, is necessary when the
paid constant is allowed to vary with the family. $\square$

## 8. Mathematical attribution and remaining resource questions

**Definition 8.1 (Source map and scope of the deductions).** The
deterministic conditional-center and integer-jump composition in
Theorems 3.1–6.1 and the deterministic sufficiency in Theorem 7.1 are
repository-derived ordinary deductions relative to the following
source interfaces. This classification makes no worldwide priority
claim. Known results used inside the deductions retain their
attribution.

| Mathematical source | Exact role and transfer boundary |
| --- | --- |
| [C], Definitions 1.1–1.3, equation (2.3), Definition 2.2, Theorems 5.1–7.1 | Identical exact pair, known common parameter, stationary first wait, complete common-table contract, scalar constants and credited converse. Its stochastic phase reader has sufficient cap count $O(L^r)$ and yields the unrestricted all-budget order and eventual criterion. The present exact zero-chain and conditional center establish deterministic attainment with the different count (4.4); they do not round that phase reader into a deterministic reader. |
| [S], Definition 2.1, Lemmas 2.2–2.3, Definition 3.1, Sections 3–7 and Theorem 11.2, with $d=2r-1$ | Full source normalizers and moments, actual read/stop normal form, positive-forest hitting comparison, normalized clipped-law entropy, harmonic finite-path comparison and actual tick payment. The critical lower is reused with all its opposing compliance conditions and arbitrary-retuning quantifiers. Equations (9.9)–(9.10) give predictable completed-gap payment for a tick-stopping construction. Its fixed-capacity nonlogarithmic upper is existing mathematics, not a new result here. |
| [P], Definitions 1.1–1.4, Theorems 4.1, 5.1, 7.2 and 8.2 | A sufficient precision/calibration bridge for the stochastic phase table, with $O(\log(1/s))$ sufficient installed precision, and failure of its specified fixed-$B$ nearest-rounding prescription at cap one. These are comparisons, not premises of Theorems 3.1–6.1 and not universal necessary precision bounds. The deterministic table changes the centering and reader mechanism and installs no small probability entries. |
| Classical linear tilting, harmonic sums and deterministic quantization | Equation (3.9) is the usual variance identity for a positive linear likelihood tilt. Its uniform variance bound, conditional integer-center allowance and return through both actual normalizers are proved in Section 3 for the exact pair. The algebraic identity itself is not a new general theorem. |
| Classical finite conditional drift, exponential concentration and predictable summation | The finite-sum stopping argument, bounded exponential-supermartingale limit and Tonelli payment appear explicitly in Theorem 5.1. The exponential method is the one attributed in [C] to Howard, Ramdas, McAuliffe and Sekhon, *Exponential line-crossing inequalities*, Section 2.3, Lemma 1. That secondary method credit supplies no observation, state or payment resource. |

Only the stated scalar and converse interfaces are inherited mathematical
premises. References contained in the sources do not add an unstated
implementation or a result for another source pair.

**Definition 8.2 (Different resource coordinates).** The installed
probability alphabet is the single fixed set $\{0,1\}$. The graph,
cap and integer destinations may nevertheless be selected anew using
the known $(s,M)$ and public fixed parameters. A fixed alphabet does
not mean a universal $q$-independent graph or a universal installed
table. The midpoint uses the two promised laws together, and never
the true label.

The exact listed count is
$3+(2\lceil AN\rceil-1)(L+2)$, and its sufficient cap order is
$O(L^{2r+1}/(1+\log L))$. It does not preserve the stochastic
construction's $O(L^r)$ sufficient count or its exact count.
The two-branch denominator comparison (6.10)–(6.12) is what permits
the larger polynomial count to attain the same order $\Psi(s,M)$.
It makes no comparison of sharp leading constants or exact finite-
budget optimizers.

An offline integer $a$ satisfying Theorem 3.2 selects a finite table.
The choice $\lfloor N\theta\rfloor$ specifies existence for arbitrary
known reals; it asserts no uniform effective decision of equality at
a grid boundary. Any certified offline choice in the stated range
and error allowance suffices. Uniform effective parameter encodings
for arbitrary noncomputable reals and design bit-operation bounds
are separate problems. Neither $a/N$ nor its accuracy is an installed
probability denominator or a mutable precision register.

The literal description upper (4.5), complete runtime configuration
count and actual paid-read cost are distinct quantities. A state index
can be represented by $\lceil\log_2M_L\rceil$ mutable bits, but neither
that representation nor the literal table description is a physical
storage or execution bound. No serial fair-coin, hardware, neural
training, generalization or empirical learning conclusion is part of
these mathematical resources.

**Definition 8.3 (Unresolved optimization and transfer problems).** The
sufficient $M_{\rm det}$ in (6.1) is conservative. The minimum
nonempty deterministic or fixed-dyadic capacity, smaller intermediate
budgets, exact finite-budget optimum and sharp paid-time constants
are not determined by the construction. The count (6.2) is not a
lower bound on competing tables. Maintaining the stochastic cap
count $O(L^r)$ with deterministic rows, or maintaining a prescribed
leading paid constant, remains a different optimization question.
Theorem 7.1 permits all positive polynomial exponents with
family-dependent constants; it gives no joint optimum for states,
installed precision, offline center accuracy and immutable description.

The known-$q$ quantifiers leave unknown-$q$ adaptation and one
$q$-independent logarithmic-order table unresolved. They also leave
effective design complexity and physical realization outside the
stated result. No broader recovery objective is inferred from the
deterministic order theorem.

The exact positive linear tilt in (1.1) is essential to (3.9).
No transfer is asserted to the older degree-nine rational-center pair,
mere upper envelopes, sparse, signed or oscillating perturbations,
varying $r,c,\alpha$, extra histories or additional workspace and
observation contracts. Such a transfer would require its own normalized
contrast, source moments, common-table construction and paid-cost
proof. In particular an upper envelope alone supplies no positive
variance contrast for a different pair. The source-class sparse
example in [S, Section 12] already distinguishes those hypotheses.

[C]: RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_RENEWAL_LOGARITHMIC_FRONTIER.md
[S]: FIB_SOURCE_CLASS_RENEWAL_RESOURCE_FRONTIER.md
[P]: FIB_CRITICAL_RENEWAL_DYADIC_PRECISION_AND_CALIBRATION.md

## 追加锚（本行以下为增补区）
