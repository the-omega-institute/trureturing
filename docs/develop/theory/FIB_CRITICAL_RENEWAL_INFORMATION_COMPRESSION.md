# Critical renewal information compression

## 1. Result and scope

Fix an integer $r\ge 1$, a real number $c>0$, and a risk level $0<\alpha<1/2$. Put
$d=2r-1$. The two source shapes are

$$
F_0(k)=k^{2r-1},\qquad F_1(k)=k^{2r-1}+c k^{r-1},\qquad k=1,2,\ldots .
$$

The common, known design parameter is $q=e^{-s}$ with $s>0$. The parameters
$r,c,\alpha$ are fixed before any neighborhood, cap, or table is selected. This volume
proves a fully paid finite implementation for the exact pair above. It uses
a source-blind dyadic stochastic category for each completed gap. The category keeps
$J+1$ observer levels, including its reset value, while retaining an affinity deficit of
order $s^{2r}(J-1)$. It is then composed with a rounded evidence lattice whose complete
configuration product is charged.

There are source-only constants $\eta\in(0,1)$, $s_0>0$ and $h_-,h_+>0$, and positive
resource constants $C_M,C_T$ depending only on the fixed $(r,c,\alpha)$, all chosen
before $s$ and $J$, such that for every
$0<s<s_0$ and every integer $J\ge 2$ satisfying $s2^J\le\eta$, the one table defined
below has

$$
 h_-s^{2r}(J-1)\le u(s,J)\le h_+s^{2r}(J-1),
$$

where $u$ is the Hellinger-affinity deficit of its completed-gap category. With
$\delta=\sqrt u$, $R=2\log(1/\alpha)$, and
$H=\lceil R/\delta\rceil$, its exact listed configuration count is

$$
 M(s,J)=3+(2H-1)(J+1),
$$

and the same table satisfies both risks, both almost-sure stopping conditions, and both
finite paid-mean conditions. Uniformly over the stated caps,

$$
 M(s,J)\le C_M\frac{J+1}{s^r\sqrt{J-1}},
 \qquad
 \max_{i\in\{0,1\}}\mathbb E_iT
 \le C_T\frac{s^{-(2r+1)}}{J-1}.
$$

On one further fixed neighborhood, choose

$$
J(s)=\left\lfloor\log_2(\eta/s)\right\rfloor.
$$

Then $J(s)=\Theta(\log(1/s))$ and the same construction gives

$$
M(s,J(s))=O\!\left(s^{-r}\sqrt{\log(1/s)}\right),\qquad
\max_i\mathbb E_iT
 =O\!\left(\frac{s^{-(2r+1)}}{\log(1/s)}\right).
$$

These are sufficient bounds for the displayed family, with resource and $O$-constants
allowed to depend on the fixed $(r,c,\alpha)$; no uniformity as the risk varies is
asserted. They do not prove a minimum complete-configuration cost or a total-memory
lower bound. Under the same fixed source/risk and paid contract, the supplied ordinary
theory [Critical renewal observation: a counted logarithmic frontier](RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_RENEWAL_LOGARITHMIC_FRONTIER.md)
gives a stronger counted controller (Theorem 5.1), the uniform all-sufficient-budget
order frontier (Theorem 6.1 and Corollary 6.2), and the eventual positive-polynomial
budget criterion (Theorem 7.1). Section 11 compares its sufficient count with this
family. The arbitrary-common-kernel active-alphabet theorem in Sections 10--11 remains
a separate statement.

The exact pair, known common $q$, unpriced immutable real transition probabilities, and
all consecutive-bit payment are part of the theorem. Unknown $q$, changing parameters,
finite precision, other source shapes, physical storage, neural or empirical-ML transfer,
and universal controller optimality are outside it.

## 2. Exact stationary source and observer contract

**Definition 2.1 (Source law).** For $i\in\{0,1\}$ define, for $s>0$,

$$
\begin{aligned}
Z_i(s)&=\sum_{k\ge1}F_i(k)e^{-sk},
&f_i(k)&=\frac{F_i(k)e^{-sk}}{Z_i(s)}\quad(k\ge1),
&f_i(0)&=0,\\
S_i(b)&=\sum_{k\ge b}f_i(k)\quad(b\ge0),
&\mu_i&=\sum_{k\ge1}(k+1)f_i(k),
&\beta_i&=\frac{\sum_{k\ge1}k(k+1)f_i(k)}{2\mu_i}.
\end{aligned}
$$

Draw an initial residual wait $\tau$ with
$\mathsf P_i(\tau=b)=S_i(b)/\mu_i$ for $b\ge0$. Independently draw iid positive
integer gaps $K_1,K_2,\ldots$ with law $f_i$, and set

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{m=1}^n(K_m+1),\qquad
X_t=\mathbf 1_{\{t=\tau_n\text{ for some }n\ge0\}}.
$$

Thus $K_m$ zeros are followed by one closing bit, and every other actual bit is zero.
The first wait is stationary residual waiting time, not an iid draw from $f_i$.

**Definition 2.2 (Paid source-blind observer).** At selected known common $q$, one
finite transition table and one deterministic initialization must serve either source. Every
persistent configuration, every simultaneously retained coordinate, the category and
the evidence coordinate, and both internally emitted labels are counted. Fresh
transition coins are independent of the source and of earlier fresh coins. Immutable
exact real transition probabilities and their design computation are allowed but
unpriced.

At runtime the table sees only the next bit of one uninterrupted consecutive history. It
has no external clock, age, read counter, gap counter, cost input, retained seed or random
tape, archive, auxiliary program state, skipped bit, free gap, source reset, extra source,
hidden source label, parameter query, probability response, or stopping-time decoder.
The table reads every bit of every gap it begins, including a saturated zero suffix, and
stops on the actual closing bit that makes its decision. If the read prefix is
$X_0,\ldots,X_{T-1}$, the paid cost is $T$.

The six obligations at the selected $s$ are

$$
\begin{gathered}
\mathsf P_0(D=1)\le\alpha,\qquad \mathsf P_1(D=0)\le\alpha,\\
\mathsf P_0(T<\infty)=\mathsf P_1(T<\infty)=1,\qquad
\mathbb E_0T<\infty,\quad \mathbb E_1T<\infty.
\end{gathered}
$$

**Lemma 2.3 (Normalization and stationarity).** All sums in Definition 2.1 are finite.
Moreover,

$$
S_i(0)=S_i(1)=1,\qquad
\sum_{b\ge0}S_i(b)=\mu_i,\qquad
\mathbb E_i\tau=\beta_i,
$$

and the bit process is stationary.

**Proof.** Polynomial growth times $e^{-sk}$ is summable. Each $f_i$ is therefore a
positive probability law on the positive integers. A mass $f_i(k)$ contributes to
$S_i(b)$ for exactly $b=0,\ldots,k$, so Tonelli's theorem gives

$$
\sum_{b\ge0}S_i(b)=\sum_{k\ge1}(k+1)f_i(k)=\mu_i,
\qquad
\sum_{b\ge0}bS_i(b)=\frac12\sum_{k\ge1}k(k+1)f_i(k).
$$

This proves normalization and the stated residual-wait mean. For stationarity, use a
countdown only on the proof probability space: a positive countdown decreases by one,
and a zero countdown draws a fresh $K$ with law $f_i$. With
$\pi_i(b)=S_i(b)/\mu_i$, incoming mass at $b$ is

$$
\pi_i(b+1)+\pi_i(0)f_i(b)
 =\frac{S_i(b+1)+f_i(b)}{\mu_i}=\pi_i(b).
$$

At $b=0$ use $f_i(0)=0$ and $S_i(0)=S_i(1)$. Starting the countdown in $\pi_i$ and
emitting one exactly at countdown zero gives the displayed stationary bit process. The
countdown and the residual age are not observer state. $\square$

## 3. Source constants fixed before the cap

For nonnegative integers $m$ write

$$
R_m(s)=\sum_{k\ge1}k^m e^{-sk}.
$$

**Lemma 3.1 (Power sums, normalization, and moments).** There is a source-only
neighborhood $(0,s_1)$ and positive constants $z_-,z_+,G,C_\mu,C_\beta$ such that,
for $0<s<s_1$,

$$
 z_-s^{-2r}\le Z_0(s)\le z_+s^{-2r},
 \qquad 0<g(s):=\frac{R_{r-1}(s)}{R_{2r-1}(s)}\le Gs^r,
$$

and $\mu_i\le C_\mu/s$, $1+\beta_i\le C_\beta/s$ for both sources. The exact
normalized likelihood ratio is

$$
\frac{f_1(k)}{f_0(k)}=\frac{1+ck^{-r}}{1+cg(s)},
\qquad
g(s)=\sum_{k\ge1}f_0(k)k^{-r}.
$$

**Proof.** The geometric identity $R_0(s)=(e^s-1)^{-1}$ can be written
$e^s-1=sE(s)$ with $E$ analytic and $E(0)=1$. Thus $R_0(s)-1/s$ extends analytically
through zero. Termwise differentiation on compact positive intervals gives

$$
R_m(s)=(-\mathrm d/\mathrm ds)^mR_0(s)=m!s^{-(m+1)}+O(1).
$$

Only finitely many orders are needed. Hence
$Z_0=R_{2r-1}$ and $Z_1=R_{2r-1}+cR_{r-1}$ have the displayed bounds, while
$g(s)=((r-1)!/(2r-1)!)s^r(1+O(s))$. Since
$Z_1=Z_0(1+cg)$, division of the two exact source masses gives the likelihood ratio.

The numerator of $\mu_i$ is

$$
R_{2r}+R_{2r-1}+ic(R_r+R_{r-1}),
$$

and the numerator of $2\beta_i$ times that same numerator is

$$
R_{2r+1}+R_{2r}+ic(R_{r+1}+R_r).
$$

Their leading terms give
$\mu_i=2r/s+O(1)$ and $\beta_i=(2r+1)/(2s)+O(1)$. The perturbation terms are at
least one degree lower even when $r=1$. Shrinking one common neighborhood and enlarging
constants proves the bounds. $\square$

The cap constant $\eta$ will be chosen only after the occupation constants in Section 5
have been displayed. It is chosen once from the fixed source parameters, before any
$s$ or $J$ is selected. The source-only interval from Lemma 3.1 is then shrunk once to
a fixed interval $0<s<s_0$.

## 4. The dyadic completed-gap category

Fix an integer $J\ge2$. Set $p_j=2^{-j}$ for $0\le j<J$, so $p_0=1$.
The observer category starts at level $0$. On a zero, level $j<J$ goes to $j+1$ with
probability $p_j$ and stays at $j$ with probability $1-p_j$; level $J$ stays at $J$.
On a closing one the current level is the completed-gap output, and the next gap
restarts the observer level at $0$. This stochastic rule is source blind.

For a proof of the exact kernel, let $G_\ell$ be independent geometric variables on
$\{1,2,\ldots\}$ with success probability $p_\ell$, and put

$$
T_0=0,\qquad T_j=\sum_{\ell=0}^{j-1}G_\ell.
$$

The variables $G_\ell,T_j$ are proof variables only; no count, coin tape, or residence
time is retained by the observer.

**Lemma 4.1 (Exact residence kernel).** For $k\ge0$ define

$$
 w_j(k)=\mathsf P(T_j\le k<T_{j+1})\quad(0\le j<J),
 \qquad w_J(k)=\mathsf P(T_J\le k).
$$

These are exactly the probabilities of the finite level table after $k$ actual zeros.
They partition every $k\ge0$. For $0\le z<1$,

$$
\sum_{k\ge0}w_j(k)z^k
=\frac{z^j\prod_{\ell<j}p_\ell}
 {\prod_{\ell\le j}(1-(1-p_\ell)z)}\quad(j<J),
$$

and

$$
\sum_{k\ge0}w_J(k)z^k
=\frac{z^J\prod_{\ell<J}p_\ell}
 {(1-z)\prod_{\ell<J}(1-(1-p_\ell)z)}.
$$
In particular, $w_0(k)=0$ for every $k\ge1$.

**Proof.** At level $\ell$, the number of zero transitions before the successful
increment is $G_\ell$. Therefore after $k$ updates the uncapped level is $j$ exactly
when $T_j\le k<T_{j+1}$; after capping, the same event holds for $j<J$ and the event
$T_J\le k$ is the level-$J$ event. The events partition the nonnegative integers.

The geometric transform is

$$
\mathbb E z^{G_\ell}=\frac{p_\ell z}{1-(1-p_\ell)z}.
$$

Conditional on arrival at $T_j$, the level-$j$ residence contributes
$\sum_{h\ge0}\mathsf P(G_j>h)z^h=[1-(1-p_j)z]^{-1}$. Multiplying transforms gives
the first formula; summing the infinite cap residence gives the second. Since $p_0=1$,
$T_1=1$ and the noncap level zero is occupied only at $k=0$. $\square$

Define the completed-gap laws

$$
 a_i(j)=\sum_{k\ge1}f_i(k)w_j(k),\qquad 1\le j\le J.
$$

**Lemma 4.2 (Support and independent blocks).** Each $a_i(j)$ is positive and
$\sum_{j=1}^J a_i(j)=1$. Across successive source gaps the category blocks are iid and
independent of the stationary first wait.

**Proof.** Lemma 4.1 partitions all $k$, and $w_0(k)=0$ for $k\ge1$, so summing against
$f_i$ gives normalization over $j=1,\ldots,J$. For any $j\ge1$, the event $K=j$ and
success of the first $j$ level increments has probability
$f_i(j)\prod_{\ell<j}p_\ell>0$ and yields level $j$, including $j=J$. The source gaps
are iid, and fresh observer coins are independent across gaps and of $\tau$; hence the
complete category blocks are iid. A proof-space continuation may sample potential
future blocks after a stop, but the machine reads only the stopped prefix. $\square$

## 5. Weighted occupation with arbitrary long-gap leakage

For an integer cap $J\ge2$, a noncap integer $1\le j<J$, a nonnegative integer
$m$, and $s>0$, define

$$
U_m(s,j)=\sum_{k\ge1} k^m e^{-sk}w_j(k).
$$

Here $w_j$ is the actual capped kernel of Lemma 4.1 at a noncap level, where it equals
$\mathsf P(T_j\le k<T_{j+1})$. The saturated kernel $w_J$ is excluded from this
definition and from the occupation bounds below.

**Lemma 5.1 (Uniform occupation bounds).** There are numerical constants

$$
\lambda=\frac34e^{-10},\qquad B_m=e(m+1)!2^{m+1},
$$

such that for every integer $J\ge2$, every noncap integer $1\le j<J$, every
nonnegative integer $m$, and every $s>0$ with $s2^j\le1$,

$$
\lambda 2^{(m+1)j}\le U_m(s,j)\le B_m2^{(m+1)j},
$$

while the upper bound holds for every $s>0$ without that last restriction. The
constants do not depend on $J$.

**Proof.** Fix $J,j,m$ in this scope. Since $j<J$, both $G_j$ and the residence
endpoint $T_{j+1}$ belong to the proof representation of the actual noncap kernel.
If $G$ is geometric with success probability $p\in(0,1]$, then
$(1-p)^{\lfloor x\rfloor}\le e^{-p\lfloor x\rfloor}
\le e^p e^{-px}\le e e^{-px}$ for $x\ge0$. Tail integration yields, for integer
$h\ge1$,

$$
\mathbb E G^h=h\int_0^\infty x^{h-1}\mathsf P(G>x)\,dx
\le e\,h!\,p^{-h}.
$$

Let $a_\ell=2^\ell$ and $W=\sum_{\ell=0}^j a_\ell<2^{j+1}$. Weighted convexity gives

$$
\left(\sum_{\ell=0}^jG_\ell\right)^h
\le W^h\sum_{\ell=0}^j\frac{a_\ell}{W}
 \left(\frac{G_\ell}{a_\ell}\right)^h.
$$

Taking expectations and using $p_\ell^{-1}=a_\ell$ gives
$\mathbb ET_{j+1}^h\le e h!2^{h(j+1)}$. On each residence interval
$T_j\le k<T_{j+1}$, at most $T_{j+1}$ terms occur and each is at most
$T_{j+1}^m$, so

$$
\sum_{k=T_j}^{T_{j+1}-1}k^me^{-sk}\le T_{j+1}^{m+1}.
$$

Tonelli with $h=m+1$ proves the upper bound, including all arbitrarily long gaps that
leak into level $j$.

For the lower bound put $n=2^j\ge2$. Since $\mathbb ET_j=n-1$, Markov gives
$\mathsf P(T_j\le4n)\ge3/4$. Independently,

$$
\mathsf P(G_j\ge2n)=(1-1/n)^{2n-1}\ge e^{-4}.
$$

The last inequality follows from
$\log(1-x)\ge-2x$ on $0\le x\le1/2$, obtained by integrating
$1/(1-x)\le2$. On the intersection, the $n$ integers
$T_j+n,\ldots,T_j+2n-1$ lie in the level-$j$ residence, are at least $n$, and are below
$6n$. If $sn\le1$, each contributes at least $n^me^{-6}$. Averaging proves the lower
constant $\lambda$. This includes $m=0$ and $j=1$, where the first residence is the
deterministic $G_0=1$. No typical-length replacement or finite-support truncation occurs.
$\square$

For every cap $J$, this correspondence holds for each $1\le j<J$ on every gap
length, including arbitrarily long gaps. The saturated level has the different event
$T_J\le k$; its whole mass is treated by normalization in Section 6.

For $1\le j<J$, put

$$
 b_j(s)=\frac{U_{r-1}(s,j)}{U_{2r-1}(s,j)}.
$$

Lemma 5.1 gives fixed constants

$$
 b_-:=\frac{\lambda}{B_{2r-1}},
\qquad b_+:=\frac{B_{r-1}}{\lambda},
$$

with $b_-2^{-rj}\le b_j(s)\le b_+2^{-rj}$ whenever $s2^J\le1$. Both moment
orders $r-1$ and $2r-1$ are nonnegative integers, including $r-1=0$ when $r=1$.
Define also
$C_\pi=B_{2r-1}/(z_-(2^{2r}-1))$. Now choose once and for all
$\eta\in(0,1)$ so that

$$
G\eta^r\le b_-/2,
\qquad C_\pi\eta^{2r}\le1/2.
$$

Finally shrink the source-only interval from Lemma 3.1 to $0<s<s_0$ if necessary.
This fixes every constant before the permitted caps are selected.

## 6. Exact normalized category contrast

For $1\le j<J$, the category masses satisfy

$$
 a_0(j)=\frac{U_{2r-1}(s,j)}{Z_0(s)},
 \qquad
 a_1(j)=\frac{U_{2r-1}(s,j)+cU_{r-1}(s,j)}{Z_1(s)}.
$$

Therefore

$$
\frac{a_1(j)}{a_0(j)}=\frac{1+cb_j(s)}{1+cg(s)},
\qquad
v_j:=\frac{a_1(j)}{a_0(j)}-1
 =\frac{c(b_j-g)}{1+cg}.
$$

**Lemma 6.1 (Noncap contrast and cap normalization).** On one source-only neighborhood,
for all $J\ge2$ and $s2^J\le\eta$,

$$
\ell_v2^{-rj}\le v_j\le L_v2^{-rj}\quad(1\le j<J),
$$

for fixed $\ell_v,L_v>0$, and

$$
\sum_{j=1}^{J-1}a_0(j)\le C_\pi(s2^J)^{2r}\le\frac12.
$$
Moreover every category likelihood ratio lies in
$[1/(1+c),1+c]$.

**Proof.** Since $j<J$ and $s2^J\le\eta$, one has
$s^r\le\eta^r2^{-rj}$. Hence
$g(s)\le G\eta^r2^{-rj}\le b_-2^{-rj}/2$. Also $1+cg\le1+c$.
Set

$$
\ell_v=\frac{cb_-}{2(1+c)},\qquad L_v=cb_+.
$$

The displayed bounds on $b_j$ imply the contrast inequality. Lemma 5.1 and the
normalizer bound imply

$$
\frac{\lambda}{z_+}s^{2r}2^{2rj}
 \le a_0(j)\le
\frac{B_{2r-1}}{z_-}s^{2r}2^{2rj}.
$$

Summing the geometric upper bound through $J-1$ gives the stated $C_\pi$ inequality.
For every $k$, the exact full likelihood ratio
$(1+ck^{-r})/(1+cg)$ lies in $[1/(1+c),1+c]$. Each category ratio is its conditional
$f_0$-average through the common kernel $w_j$, including the saturated level $J$.
Thus the same interval holds for every category, and all category log ratios are bounded
by $C_0=\log(1+c)$. The saturated mass is the actual randomized-counter mass; it has not
been replaced by an exact-length tail event. $\square$

**Theorem 6.2 (Uniform dyadic affinity).** There are fixed $h_-,h_+>0$ such that

$$
 h_-s^{2r}(J-1)\le u(s,J):=1-\sum_{j=1}^J\sqrt{a_0(j)a_1(j)}
 \le h_+s^{2r}(J-1),
$$

for every $0<s<s_0$, $J\ge2$, and $s2^J\le\eta$. In particular $0<u(s,J)<1$.

**Proof.** For normalized laws,

$$
2u=\sum_{j=1}^J\bigl(\sqrt{a_1(j)}-\sqrt{a_0(j)}\bigr)^2.
$$

For $j<J$ the summand is
$a_0(j)v_j^2/(\sqrt{1+v_j}+1)^2$. Lemma 6.1 gives
$v_j\le c$ and a positive lower bound of order $2^{-rj}$, while $a_0(j)$ has a lower
bound of order $s^{2r}2^{2rj}$. The powers cancel, so each of the $J-1$ noncap levels
contributes at least a fixed multiple of $s^{2r}$. For example one may take

$$
 h_-=
 \frac{\lambda c^2b_-^2}
 {8z_+(1+c)^2(\sqrt{1+c}+1)^2}.
$$

For the upper bound let

$$
Q=\sum_{j<J}a_0(j)v_j^2,\qquad
m=\sum_{j<J}a_0(j)v_j.
$$

Normalization gives $a_1(J)-a_0(J)=-m$. The full chi-square divergence against $a_0$ is

$$
Q+\frac{m^2}{1-\sum_{j<J}a_0(j)}.
$$

Weighted Cauchy--Schwarz gives $m^2\le(\sum_{j<J}a_0(j))Q$, and the preceding mass
bound makes this at most $2Q$. Since
$(\sqrt p-\sqrt q)^2\le(p-q)^2/q$,
$u\le Q$. The upper bounds in Lemma 6.1 then give

$$
Q\le \frac{c^2B_{2r-1}b_+^2}{z_-}\,s^{2r}(J-1),
$$

so this coefficient is a valid $h_+$. Strict positivity follows from the positive
noncap contribution; $A=1-u$ is positive because both category laws have positive
support and affinity is at most one. The cap normalization term is included in the
chi-square calculation, so long gaps and normalizer drift are charged. $\square$

## 7. Complete actual-bit controller

For a permitted $(s,J)$, use $u=u(s,J)$ and set

$$
\delta=\sqrt u,\qquad R=2\log(1/\alpha),\qquad H=\left\lceil\frac R\delta\right\rceil.
$$

Introduce a formal category $0$ only for the impossible consecutive-one row, with
$\ell_0=0$. For $1\le j\le J$, set

$$
\ell_j=\log\frac{a_1(j)}{a_0(j)},\qquad
m_j=\left\lfloor\frac{\ell_j}{\delta}\right\rfloor,\qquad
 t_j=\frac{\ell_j}{\delta}-m_j\in[0,1).
$$

At a closing one the table chooses $m_j$ with probability $1-t_j$ and $m_j+1$ with
probability $t_j$. All these values, destinations, and probabilities are immutable design
entries at the known common $q$. The table never computes a likelihood or a floor at
runtime.

The complete persistent set is

$$
\mathcal Q=\{w,d_0,d_1\}\cup
\{(e,j):-H<e<H,\ 0\le j\le J\}.
$$

The waiting state $w$ is initialized under both sources. It loops on zero and enters
$(0,0)$ on one. From $(e,j)$ with $j<J$, a zero goes to $(e,j+1)$ with probability
$2^{-j}$ and stays at $(e,j)$ otherwise. From $(e,J)$ every zero stays at $(e,J)$.
On a one, choose the rounded increment as above and use

$$
\Phi(e,n)=
\begin{cases}
 d_1,&e+n\ge H,\\
 d_0,&e+n\le-H,\\
 (e+n,0),&-H<e+n<H.
\end{cases}
$$

The label states stop on entry; their identity rows are included only to make every row
of the finite table explicit. The impossible one at category $0$ has $m_0=t_0=0$ and
therefore leaves the evidence coordinate unchanged while resetting the level.

Equivalently, every transition row is the following immutable table (the two successors
in a rounded row have their probabilities added if they coincide):

| current state | next bit | successor(s) and probabilities |
| --- | --- | --- |
| $w$ | $0$ | $w$ with probability $1$ |
| $w$ | $1$ | $(0,0)$ with probability $1$ |
| $(e,j)$, $j<J$ | $0$ | $(e,j+1)$ with probability $2^{-j}$; $(e,j)$ with probability $1-2^{-j}$ |
| $(e,J)$ | $0$ | $(e,J)$ with probability $1$ |
| $(e,j)$, $0\le j\le J$ | $1$ | $\Phi(e,m_j)$ with probability $1-t_j$; $\Phi(e,m_j+1)$ with probability $t_j$ |
| $d_i$ | $0$ or $1$ | $d_i$ with probability $1$ (the row is never read after emission) |

The $j=0$ one-row is the formal impossible consecutive-one case. Every zero after
level $J$ is still read and paid, so the table also specifies indefinitely long
saturated gaps.

**Proposition 7.1 (Exact count and access audit).** The table has exactly

$$
M(s,J)=3+(2H-1)(J+1)
$$

listed configurations and obeys Definition 2.2.

**Proof.** There are $2H-1$ evidence coordinates and $J+1$ simultaneously retained level
values, plus $w,d_0,d_1$. Unreachable pairs are still counted. The zero, one, waiting,
label, holding, saturation, and impossible-input rows are all defined and stochastic.
The fresh coin changes only the listed successor. Evidence addition and threshold
comparison are compiled into destinations; no mutable arithmetic workspace, gap count,
residence register, random tape, phase, overshoot, likelihood register, clock, or hidden
suffix exists. A saturated gap continues to consume each actual zero. Resetting level zero
resets only the observer category, never the source. The initial wait and the terminal
closing bit are actual reads. $\square$

## 8. Rounded increments, stopping, and paid reads

For a potential completed gap let $Y_n$ be its category and let $V_n$ be the rounded
increment chosen at its closing one. Across potential gaps $(Y_n,V_n)$ are iid under each
source and independent of $\tau$. Conditional on $Y_n=j$,

$$
V_n\in\{\delta m_j,\delta(m_j+1)\},\qquad
\mathbb E(V_n\mid Y_n=j)=\ell_j,
$$

and, with $\varepsilon_n=V_n-\ell_{Y_n}$,

$$
\mathbb E(\varepsilon_n\mid Y_n)=0,\qquad
|\varepsilon_n|\le\delta,\qquad
|V_n|\le C_0+\delta.
$$

Let $D_i=D(a_i\|a_{1-i})$. Then

$$
\mathbb E_0V_n=-D_0,\qquad \mathbb E_1V_n=D_1,\qquad D_i\ge2u.
$$

Indeed the first two identities follow by averaging the exact category log ratio, and
for $p=a_i,b=a_{1-i}$, $\log x\le x-1$ at
$x=\sqrt{b(j)/p(j)}$ gives

$$
D(p\|b)=-2\sum_jp(j)\log\sqrt{b(j)/p(j)}
 \ge2\sum_j\bigl(p(j)-\sqrt{p(j)b(j)}\bigr)=2u.
$$

Define $S_0=0$, $S_n=\sum_{m=1}^nV_m$, and

$$
N=\inf\{n\ge1:S_n\ge H\delta\text{ or }S_n\le-H\delta\}.
$$

Before exit, $S_n=e\delta$ is exactly the live evidence coordinate. Since
$H\delta<R+\delta$ and $\delta<1$,

$$
|S_{N\wedge m}|\le H\delta+C_0+\delta<R+C_0+2=:B
$$

for every deterministic $m$.

**Lemma 8.1 (Finite gap stop).** Under either source,

$$
\mathbb E_iN\le\frac{B}{2u}<\infty,
\qquad \mathsf P_i(N<\infty)=1.
$$

**Proof.** Let the proof filtration contain the initial wait and the first complete
potential gaps with their observer coins. On $\{N>n\}$ the next increment is independent
of the past. Sign the score positively under source one and negatively under source zero.
For every finite $m$, direct conditional summation gives

$$
\mathbb E_i[\operatorname{sgn}_i S_{N\wedge m}]
 =D_i\sum_{n=0}^{m-1}\mathsf P_i(N>n)
 =D_i\mathbb E_i(N\wedge m),
$$

where $\operatorname{sgn}_0=-1$ and $\operatorname{sgn}_1=1$. The left side is at most
$B$, so $\mathbb E_i(N\wedge m)\le B/D_i\le B/(2u)$. Monotone convergence proves the
bound and hence almost-sure finiteness. This finite-horizon identity does not use
unbounded optional stopping or assume absorption in advance. $\square$

**Lemma 8.2 (Exact actual payment).** The controller stops almost surely and

$$
T=1+\tau+\sum_{n=1}^N(K_n+1),
\qquad
\mathbb E_iT=1+\beta_i+\mu_i\mathbb E_iN.
$$

**Proof.** The initial phase reads $\tau$ zeros and its first one. Every later begun gap
is read through its closing one, including the terminating gap. Thus the pathwise identity
charges every holding zero, every post-cap zero, and the terminal bit. Each source gap and
$\tau$ is finite almost surely, and Lemma 8.1 makes $N$ finite.

The event $\{N\ge n\}$ is known before gap $n$ is drawn and is therefore independent of
$K_n$. Hence

$$
\mathbb E_i[(K_n+1)\mathbf1_{\{N\ge n\}}]
 =\mu_i\mathsf P_i(N\ge n).
$$

Tonelli's theorem gives the claimed expectation identity. This is predictable inclusion
for the present complete-gap table; it does not claim duration-score independence within
a gap and does not apply to an observer that stops partway through zeros. $\square$

## 9. Risks and uniform resource bounds

**Lemma 9.1 (Rounded risk).** The same table satisfies
$\mathsf P_0(D=1)\le\alpha$ and $\mathsf P_1(D=0)\le\alpha$.

**Proof.** For $|x|\le1/2$, Taylor's integral remainder gives
$e^x\le1+x+x^2$. Since $|\varepsilon_n|\le\delta<1$ and its conditional mean is zero,

$$
\mathbb E(e^{\pm\varepsilon_n/2}\mid Y_n=j)
 \le1+\frac14\mathbb E(\varepsilon_n^2\mid Y_n=j)
 \le1+\frac u4.
$$

The exact unrounded half-likelihood identities are

$$
\mathbb E_0e^{\ell_{Y_n}/2}=\sum_j\sqrt{a_0(j)a_1(j)}=1-u,
\qquad
\mathbb E_1e^{-\ell_{Y_n}/2}=1-u.
$$

Conditioning first on the category gives
$\mathbb E_0e^{V_n/2}\le(1-u)(1+u/4)<1$, and likewise under source one with the
negative sign. Therefore the stopped exponentials
$e^{S_{n\wedge N}/2}$ under source zero and
$e^{-S_{n\wedge N}/2}$ under source one are nonnegative supermartingales at every finite
horizon. Lemma 8.1 has already proved finite $N$ and the bound by $B$ gives uniform
boundedness. Bounded convergence yields

$$
\mathbb E_0e^{S_N/2}\le1,\qquad \mathbb E_1e^{-S_N/2}\le1.
$$

A wrong label requires respectively $S_N\ge H\delta$ or $S_N\le-H\delta$. Since
$H\delta\ge R=2\log(1/\alpha)$, both error probabilities are at most
$e^{-R/2}=\alpha$. The proof exponentials and overshoot are not runtime state. $\square$

**Theorem 9.2 (Uniform fully paid dyadic upper).** There are positive constants
$C_M,C_T$ depending only on the fixed $(r,c,\alpha)$, chosen before $s$ and $J$, such
that every permitted $(s,J)$ has the six obligations and

$$
M(s,J)\le C_M\frac{J+1}{s^r\sqrt{J-1}},
\qquad
\max_i\mathbb E_iT\le C_T\frac{s^{-(2r+1)}}{J-1}.
$$

**Proof.** The ceiling gives $H\le R/\delta+1$ and hence

$$
M\le(2R+4)\frac{J+1}{\delta}.
$$

The lower affinity bound gives
$\delta\ge\sqrt{h_-}s^r\sqrt{J-1}$, which proves the first estimate. By Lemma 8.2,
Lemma 3.1, and Lemma 8.1,

$$
\mathbb E_iT
 \le \frac{C_\beta}{s}+\frac{C_\mu B}{2su}
 \le \frac{C_\beta+C_\mu B/2}{su}
 \le \frac{C_\beta+C_\mu B/2}{h_-}
       \frac{s^{-(2r+1)}}{J-1}.
$$

The table and all six conclusions are common to the two source labels. $\square$

**Corollary 9.3 (Growing-cap endpoint).** After shrinking to one further source-only
neighborhood, the direct choice $J=\lfloor\log_2(\eta/s)\rfloor$ gives

$$
M=O\!\left(s^{-r}\sqrt{\log(1/s)}\right),
\qquad
\max_i\mathbb E_iT
=O\!\left(\frac{s^{-(2r+1)}}{\log(1/s)}\right).
$$

**Proof.** Let $t=\log(1/s)$. For $s$ small enough,
$t\ge\max\{\log2,2(|\log\eta|+2\log2)\}$. Then
$J=\lfloor(t+\log\eta)/\log2\rfloor$ obeys

$$
J-1\ge\frac{t}{2\log2}>0,
\qquad J+1\le\frac{2t}{\log2},
\qquad s2^J\le\eta.
$$

Thus $J\ge2$, including the smallest legal cap once the fixed neighborhood is chosen,
and equality $s2^J=\eta$ is allowed. Substitution into Theorem 9.2 proves both bounds.
The choice is direct and uses no parameter depending on $s$ other than the displayed cap.
$\square$

The explicit listed family also has
$M\ge H(J+1)\ge R(J+1)/\delta$, so the upper and lower estimates for this particular
list have the same $s^{-r}\sqrt{\log(1/s)}$ order at the endpoint. This is only a lower
bound on the configurations deliberately listed by this construction. It is not a lower
bound for arbitrary observers or for a minimal reachable realization.

## 10. Arbitrary stochastic kernels and alphabet necessity

The preceding dyadic category is one finite common kernel of a completed gap. The next
result applies to every finite fractional kernel, including kernels with empty cells and
with mass from arbitrarily long gaps in every cell.

**Theorem 10.1 (Uniform finite-alphabet bound).** Fix the same $r,c$ as above. There
are a source-only $s_2>0$ and $C<\infty$, fixed before the alphabet and the kernel, such
that for every $0<s<s_2$, every finite alphabet $\{1,\ldots,B\}$ with $B\ge1$, and
every common stochastic kernel $w_z(k)$ satisfying

$$
0\le w_z(k)\le1,\qquad \sum_{z=1}^B w_z(k)=1\quad(k\ge1),
$$

the output laws

$$
 a_i(z)=\sum_{k\ge1}f_i(k)w_z(k),
 \qquad
 u_Z=1-\sum_{z=1}^B\sqrt{a_0(z)a_1(z)}
$$

satisfy

$$
0\le u_Z\le C B_+s^{2r}\le C Bs^{2r},
\qquad B_+=\#\{z:a_0(z)>0\}.
$$
The positive supports of $a_0$ and $a_1$ agree.

**Proof.** Keep the exact likelihood ratio from Lemma 3.1 and write
$h(k)=k^{-r}$ and $g=\mathbb E_0h$. For $0<t<1$, the event $h(K)>t$ is
$K<t^{-1/r}$. Since $Z_0\ge z_-s^{-2r}$ and
$\sum_{k\le x}k^{2r-1}\le x^{2r}$,

$$
\mathsf P_0(h>t)\le z_-^{-1}s^{2r}t^{-2}.
$$

For $t\ge1$ the event is empty, so with $C_{\rm tail}=z_-^{-1}$,

$$
\mathsf P_0(h>t)\le\min\{1,C_{\rm tail}s^{2r}t^{-2}\}\quad(t>0).
$$

Let $0\le w\le1$, $m=\mathbb E_0w$, and $a=s^r$. If $m=0$, positivity of every
$f_0(k)$ forces $w(k)=0$ for all $k$. Suppose $m>0$ and set $\lambda=a/\sqrt m$.
For $Y=(h-g)_+$, if $\lambda\ge1$ then
$\mathbb E_0[Yw]\le m\le a\sqrt m$. If $\lambda<1$, the layer-cake identity and
$w\le1$ give

$$
\begin{aligned}
\mathbb E_0[Yw]
&=\int_0^1\mathbb E_0[w\mathbf1_{\{Y>t\}}]dt\\
&\le\lambda m+\int_\lambda^1\mathsf P_0(h>t)dt\\
&\le\lambda m+C_{\rm tail}a^2\int_\lambda^1t^{-2}dt
\le(1+C_{\rm tail})a\sqrt m.
\end{aligned}
$$

The negative part obeys $(g-h)_+\le g$, hence
$\mathbb E_0[(g-h)_+w]\le gm\le Ga\sqrt m$. With
$K=1+C_{\rm tail}+G$,

$$
\left|\mathbb E_0[(h-g)w]\right|\le K s^r\sqrt{\mathbb E_0w}.
$$

For a cell put $m_z=a_0(z)$ and
$\Delta_z=a_1(z)-a_0(z)$. The exact ratio gives

$$
\Delta_z=\frac{c}{1+cg}\mathbb E_0[(h-g)w_z],
$$

so $|\Delta_z|\le cKs^r\sqrt{m_z}$. If $m_z=0$ then $w_z$ is identically zero
on the positive support and $a_1(z)=0$ as well. Finally,

$$
 u_Z=\frac12\sum_z(\sqrt{a_1(z)}-\sqrt{a_0(z)})^2.
$$

For an active cell, rationalization and
$(\sqrt{a_1}+\sqrt{a_0})^2\ge a_0$ give a contribution at most
$\Delta_z^2/(2m_z)\le c^2K^2s^{2r}/2$. Summing over the $B_+$ active cells proves the
claim, including arbitrary fractional leakage, empty cells, growing $B$, and the exact
normalizer drift. $\square$

**Corollary 10.2 (Logarithmic active alphabet is necessary).** If a family of common
finite kernels satisfies, on a neighborhood or a specified subsequence,

$$
 u_Z\ge c_0s^{2r}\log(1/s)
$$

for one fixed $c_0>0$, then on that same eventual neighborhood or subsequence,

$$
 B_+\ge\frac{c_0}{C}\log(1/s).
$$

**Proof.** Divide the lower bound by the upper bound in Theorem 10.1. The constants were
fixed before the kernel and alphabet, so they remain valid when $B$ grows arbitrarily with
$1/s$. A coefficient tending to zero would be a different assertion and does not imply
this fixed positive multiple. $\square$

## 11. Exact alphabet-order match

For the dyadic category, every completed gap has one of the positive outputs
$1,\ldots,J$. Thus its active output alphabet has

$$
B_{\rm active}=J.
$$

The observer register has the additional reset value $0$, so its level-register size is
$J+1$; the zero value has no completed positive-gap mass. Padding the output alphabet by
that empty value changes neither its order nor Theorem 10.1.

With the endpoint cap of Corollary 9.3,
$J=\Theta(\log(1/s))$ and Theorem 6.2 gives

$$
 u(s,J)=\Theta\!\left(s^{2r}\log(1/s)\right).
$$

Corollary 10.2 therefore forces $B_{\rm active}=\Omega(\log(1/s))$ for any common finite
completed-gap kernel that retains a fixed positive multiple of this critical logarithmic
gain. The dyadic category attains the same active-alphabet order. This is an order match
for one completed-gap output alphabet only. It does not lower-bound the full sequential
controller, its evidence register, its product count, its paid reads, or any arbitrary
observer whose information has not been reduced to a completed-gap kernel.

For comparison, [Critical multiscale renewal attainment](FIB_CRITICAL_MULTISCALE_RENEWAL_ATTAINMENT.md),
Theorem 9.2, uses an exact-length category with $L+2$ level values and
$M=3+(2H-1)(L+2)$. For each fixed $0<\theta\le1$, it gives a sufficient budget
$M_{\rm exact}\le C_\theta F_\theta(s)$, where

$$
F_\theta(s)=\frac{s^{-(r+\theta)}}{\sqrt{\log(1/s)}},\qquad
F_{\rm dyadic}(s)=s^{-r}\sqrt{\log(1/s)}.
$$

Corollary 9.3 gives the sufficient budget $M_{\rm dyadic}\le C F_{\rm dyadic}(s)$.
On the intersection of their fixed neighborhoods, both constructions have a paid-mean
upper bound of order $s^{-(2r+1)}/\log(1/s)$, with constants allowed to depend on the
fixed $(r,c,\alpha,\theta)$. The quotient of these displayed sufficient-budget scale
functions is

$$
\frac{F_{\rm dyadic}(s)}{F_\theta(s)}=s^\theta\log(1/s)\longrightarrow0
\qquad(s\downarrow0)
$$

for every fixed $\theta>0$. This comparison concerns explicit sufficient-budget scales
under the same paid model. It takes no ratio of $O$-classes and gives no ratio of actual
configuration costs, total-memory lower bound, or strict comparison of minimum costs.
The predecessor's exact rounded-lattice, drift, risk, and predictable-payment ideas are
reused only after the dyadic kernel and its normalized affinity have been derived here.

The supplied [Critical renewal observation: a counted logarithmic frontier](RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_RENEWAL_LOGARITHMIC_FRONTIER.md)
has a stronger sufficient controller under the same fixed pair, known common $q$, and
complete paid contract. Its Theorem 5.1 gives $O(2^{rJ})$ complete configurations and
both paid means $O(s^{-(2r+1)}/J)$ for all its permitted caps, with its own fixed cap
constant and neighborhood. At the full-scale cap, its Corollary 7.2 gives sufficient
$O(s^{-r})$ configurations with the same logarithmic paid order. Thus the present
$O(s^{-r}\sqrt{\log(1/s)})$ sufficient controller is weaker. This compares sufficient
constructions; the active-alphabet bound here retains its separate scope.

The supplied volume's Theorem 6.1 and Corollary 6.2 give matching order

$$
\frac{s^{-(2r+1)}}{1+\log\min\{M,1/s\}}
$$

up to fixed $(r,c,\alpha)$ constants, for the two separate compliant paid-mean infima
and the infimum of the common-table maximum, uniformly over every finite $M\ge M_0$
on one neighborhood chosen before the budgets. Its lower uses its credited converse. Its Theorem 7.1 characterizes attainment
of the full logarithmic paid order under the complete contract by the eventual condition
$\log(1+M(s))\ge\varepsilon\log(1/s)$ for some fixed $\varepsilon>0$, for finite
integer-valued budget families $M(s)\ge2$ without regularity assumptions. The paid upper
constant may depend on the budget family. In particular every fixed positive polynomial budget exponent
suffices, and a subpolynomial budget does not; the exponent $r$ is not necessary
(Corollary 7.2). The all-sufficient-budget order frontier is therefore supplied there.
These are credited ordinary mathematical results, not kernel validation. They do not
supply the arbitrary stochastic-kernel active-alphabet theorem proved here.

## 12. Optional ceilings and sharpness at the cell scale

The uniform alphabet theorem has a useful exact-pair ceiling. Let

$$
 u_K=1-\sum_{k\ge1}\sqrt{f_0(k)f_1(k)}
$$

be the full-gap affinity deficit. For every common kernel, Cauchy--Schwarz gives

$$
\sum_k\sqrt{f_0(k)f_1(k)}w_z(k)
 \le\sqrt{a_0(z)a_1(z)}.
$$

Summing in $z$ yields $u_Z\le u_K$. Since
$L(k)=f_1(k)/f_0(k)=(1+ch(k))/(1+cg)$,
$L(k)\ge1/(1+c)$, and
$L(k)-1=c(h(k)-g)/(1+cg)$, the centered square obeys
$\mathbb E_0(h-g)^2\le\mathbb E_0h^2$. Consequently,

$$
 u_K\le\frac{c^2}{2}\mathbb E_0h^2
 =\frac{c^2}{2Z_0}\sum_{k\ge1}\frac{e^{-sk}}k
 =\frac{c^2}{2Z_0}\bigl[-\log(1-e^{-s})\bigr].
$$

For $0<s\le1$, $1-e^{-s}\ge s/e$, so
$u_Z\le C_{\rm gap}s^{2r}\log(e/s)$ with a source-only constant. This is an upper
ceiling, not a claim that every alphabet reaches it.

The per-cell scale is also attained in a two-cell example. Take
$w_1(k)=\mathbf1_{\{k=1\}}$ and $w_2=1-w_1$. Then
$f_0(1)=e^{-s}/Z_0\asymp s^{2r}$ and
$a_1(1)/a_0(1)=(1+c)/(1+cg)\to1+c$. The first cell contributes a fixed positive multiple
of $s^{2r}$ to $u_Z$ on a smaller source-only neighborhood. Thus the $s^{2r}$ per-active-cell
scale in Theorem 10.1 cannot generally be replaced by $o(s^{2r})$. Neither this example
nor the ceiling supplies a sequential-memory lower bound.

## 13. Credits and nontransfer boundaries

Power-sum asymptotics, equilibrium-renewal normalization, geometric residence transforms,
tail integration, convexity, Markov's inequality, weak-$L^2$ layer cake, Cauchy--Schwarz,
Hellinger affinity, chi-square domination, data processing, KL drift, unbiased stochastic
rounding, finite-horizon drift, exponential supermartingales, bounded convergence, and
Tonelli's theorem are classical methods. Geometrically slowing counters are also a
classical approximate-counting idea. Their use here is credited rather than presented as
an invention.

The predecessor [Critical multiscale renewal attainment](FIB_CRITICAL_MULTISCALE_RENEWAL_ATTAINMENT.md)
supplies the fixed source pair, stationary first-wait convention, complete-configuration
contract, and reusable rounded likelihood-lattice pattern. Sections 4--9 derive the
dyadic stochastic completed-gap kernel, its uniform weighted occupation and normalized
affinity estimates, and their sufficient composition with that lattice. The
arbitrary-common-kernel alphabet bound, conditional logarithmic alphabet necessity,
and alphabet-order match are established in Sections 10--11; Section 12 gives the
exact-pair ceiling and two-cell example.

The supplied ordinary theory [Critical renewal observation: a counted logarithmic frontier](RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_RENEWAL_LOGARITHMIC_FRONTIER.md),
Theorems 5.1, 6.1 and 7.1 and Corollaries 6.2 and 7.2, supplies the stronger counted
controller, uniform all-sufficient-budget order theorem and eventual budget criterion
compared in Section 11. The present arbitrary stochastic-kernel active-alphabet bound
is a distinct statement about one completed-gap output. The stronger controller and
order frontier are credited to that source. All these sources are fallible ordinary
theory; citation provides no independent certification. These deductions for the stated
pair retain the classical status of their methods. No formal-kernel certificate,
global originality or priority claim is made.

The conclusions are local in $s\downarrow0$ for fixed $r,c,\alpha$ and known common
$q=e^{-s}$. They do not cover unknown $q$, one table independent of $q$, all interior
$q$, changing parameters, signed or oscillating perturbations, other polynomial shapes,
finite-precision transition probabilities, or physical implementation. The arbitrary
real precision is explicitly unpriced. The alphabet statement is about a finite
completed-gap output and does not imply a lower bound on total persistent memory, a
minimum product of category and evidence states, a paid-read lower bound, or a
total-controller budget frontier. The all-sufficient-budget order frontier and eventual
budget criterion are supplied by the credited volume, Theorems 6.1 and 7.1. Its
Corollary 7.2 gives a sufficient full-scale count without this construction's
square-root logarithmic factor; the exponent $r$ is not a necessary budget exponent.
Its Open problem 9.3 leaves minimum nonempty budgets, exact finite-budget optima, sharp
leading paid-time constants, and least memory growth for a preassigned leading upper
constant unresolved. Finite-precision transition probabilities, physical realization,
and neural or empirical-ML transfer remain separate unresolved questions.

## 追加锚（本行以下为增补区）
