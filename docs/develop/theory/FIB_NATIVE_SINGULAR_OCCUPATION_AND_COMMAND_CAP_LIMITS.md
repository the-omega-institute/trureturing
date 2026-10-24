# Native point-source occupation and finite-command cap limits

## 1. The fixed full model and the observations

**Definition 1.1 (inherited source, operator and commands).** Write G for
[Native variable-coefficient Green stability](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md),
N for [Probability, phase transport and holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md),
and K for [Guarded lift limits](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md).
Fix an arbitrary both-wall model of G, §§1–3 and 29.1. In particular,
$r=1-Z$, $H=r/2$, $X=Y=H$, $I=(l,u)\Subset(0,H)$,
$\Omega=I\times\mathbb T^2$, and both actual phase circles have period
$2\pi$. Preparations and their phase rotations are fixed and arbitrary.
The two original horizontal fields, density, form and domain are

$$
\begin{gathered}
X_1=P=\partial_k,\qquad
X_2=Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta,
\qquad d\mu=\rho\,dk\,d\alpha\,d\beta,\\
T_A[f]=\int_\Omega\sum_{i,j=1}^2a^{ij}(X_jf)\overline{X_if}\,d\mu,
\qquad
\mathcal F_A=\overline{C_c^\infty(\Omega)}^{\,\|\cdot\|_2^2+T_A}.
\end{gathered}
\tag{1.1}
$$

Here $\rho$ is any fixed smooth positive raw density and $A$ any fixed
smooth real symmetric positive definite matrix on a neighbourhood of
$\overline\Omega$. Let $L_A$ be the operator of (1.1), with both height
faces killed and the actual phases periodic. Fix the original interior
source $o=(k_o,\alpha_o,\beta_o)$. The clock is $e^{-tL_A}$, with control
covariance $2A\,dt$, and

$$
\Gamma(q)=\Gamma_{A,o}(q)=\int_0^\infty p_t^\Omega(o,q)\,dt,
\qquad \Gamma(o)=+\infty.
\tag{1.2}
$$

Thus $\int\Gamma L_A\varphi\,d\mu=\varphi(o)$; neither the source nor
the angular measure is probability-normalized. Let $Q_t$ be the free
diffusion of G, (29.6)–(29.7), started at this same $o$, and $\tau$ its
first height exit. No attractive drift or ground conditioning is used.

The finite random commands throughout §§2–5 are exactly G, Definition
29.2, under its Definition 29.1's finite-sign, coefficient-evaluation and
execution capabilities. To fix the relevant clock and interpolation,

$$
\delta_n=n^{-2},\quad m_n=n^3,\quad S_n=n,\quad T_n=n+\delta_n,
\quad \Sigma=A^{1/2},\quad
d^j=\rho^{-1}\sum_iX_i(\rho a^{ij}).
\tag{1.3}
$$

At an alive node $q_i$ the increment is
$v_i=d(q_i)\delta_n+\sqrt{2\delta_n}\Sigma(q_i)\xi_i$, where the
$\xi_i$ are independent uniform signs in $\{-1,1\}^2$. On a cell the
controls have constant velocity $v_i/\delta_n$. In relative coordinates
their actual chronological integral has the prefix

$$
(a,b,j)=\left(a_i+\theta v_i^1,\ b_i+\theta v_i^2,\
j_i+\theta a_i v_i^2+\tfrac12\theta^2v_i^1v_i^2\right),
\quad \theta=(t-i\delta_n)/\delta_n.
\tag{1.4}
$$

The actual state is G, (29.2), at every prefix. A chord is cut at its
first hit of $l$ or $u$ and held thereafter. If all $m_n$ cells survive,
the original terminal height leg, with $b$ constant, reaches $u$ in the
last interval of length $\delta_n$. Denote this held state by $\bar q_n$
and its actual first hit by $\zeta_n$. There is no rejection or survival
reweighting of signs. In particular $j=\int a\,db$ throughout; all-prefix
native guards, both killing faces and the terminal leg are retained.

**Definition 1.2 (the source gauge).** Use exactly G, (2.3) and
(10.1)–(10.3). Thus, locally about $o$,

$$
\begin{gathered}
x=k-k_o,\quad y=2(\alpha-\alpha_o),\quad
z=-r\{\beta-\beta_o-(\tfrac12-k_o/r)y\},\quad B=\Sigma(o)^{-1},\\
(\xi,\eta)^{\mathsf T}=B(x,y)^{\mathsf T},\quad
\upsilon=\det(B)(z-xy/2),\quad
R=\{(\xi^2+\eta^2)^2+16\upsilon^2\}^{1/4},\\
d\mu=m(q)\,d\xi\,d\eta\,d\upsilon,\quad
m_0=\frac{\rho(o)\det A(o)}{2r},\quad c_G=(2\pi m_0)^{-1}.
\end{gathered}
\tag{1.5}
$$

This is an injective local chart, not a change of the actual phase torus.
The coordinate $\upsilon$ is distinguished from the lifetime $\tau$.
The established full-field asymptotic G, Theorem 11.1, and its polar
Jacobian give, uniformly in source directions,

$$
\Gamma=c_GR^{-2}(1+O(R)),\quad m=m_0+O(R),\quad
d\xi\,d\eta\,d\upsilon=\tfrac14 R^3\,dR\,da\,d\theta,
\quad -\tfrac\pi2<a<\tfrac\pi2,\quad 0\le\theta<2\pi.
\tag{1.6}
$$

The full field is positive and smooth off $o$ and bounded on the entire
complement of every source neighbourhood, including towards the killed
faces, by [Two-control Green stability, Proposition 2.2](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md).
All constants below may depend on this fixed model and source.

**Definition 1.3 (complete occupations and caps).** For nonnegative Borel
$W$, with its displayed representative at $o$, put

$$
\nu_n(W)=\mathbb E\int_0^{\zeta_n}W(\bar q_n(t))\,dt,
\qquad \nu(W)=\int_\Omega\Gamma W\,d\mu,
\qquad W_M=\min(W,M),\quad M>0.
\tag{1.7}
$$

These are extended integrals over the complete lifetime. A value at an
isolated time contributes zero; a positive-time hold at a point with
$W=+\infty$ contributes infinity. G, Theorem 29.6, supplies
$\nu_n(f)\to\nu(f)$ for every $f\in C(\overline\Omega)$ and identifies
$\nu(f)$ with diffusion occupation. Its path, lifetime and tail assertions
are reused with their original hypotheses.

## 2. Three different exact integrability thresholds

**Theorem 2.1 (spatial, diffusion and actual finite-command ranges).** For
every fixed model of Definition 1.1 and every real $p>0$,

$$
\begin{aligned}
\int_\Omega\Gamma^p\,d\mu<\infty
&\quad\Longleftrightarrow\quad p<2,\\
\mathbb E_o\int_0^\tau\Gamma(Q_t)^p\,dt
=\int_\Omega\Gamma^{p+1}\,d\mu<\infty
&\quad\Longleftrightarrow\quad p<1.
\end{aligned}
\tag{2.1}
$$

There is $n_0$ such that, for every $n\ge n_0$, every realization of the
original finite command has

$$
\int_0^{\zeta_n}\Gamma(\bar q_n(t))^p\,dt<\infty
\quad\Longleftrightarrow\quad p<\tfrac12.
\tag{2.2}
$$

The same equivalence holds for its expectation $\nu_n(\Gamma^p)$.
For every $n\ge1$, without a fine-mesh restriction, that integral is
infinite on every realization when $p\ge1/2$. More precisely, at any
fixed $n$, a realization with no positive-time hold at $o$ has exactly
the range $p<1/2$; one with such a hold has no positive integrability
range. The fine-mesh restriction excludes all zero-velocity random
chords uniformly for the fixed coefficients.

The spatial endpoint $p=2$ and the diffusion-mean endpoint $p=1$ are
logarithmic. In fact, for every sufficiently small fixed chart radius $b$,

$$
\int_{\epsilon<R<b}\Gamma^2\,d\mu
=\frac{1}{8m_0}\log(b/\epsilon)+O(1)
\quad(\epsilon\downarrow0).
\tag{2.3}
$$

The finite-command endpoint $p=1/2$ is logarithmic in elapsed distance
from its initial departure from $o$, unless it holds there, in which
case divergence already occurs on the hold. Finite diffusion expectation
in (2.1) implies almost sure finiteness for $p<1$. No almost sure
divergence assertion for the diffusion is made for $p\ge1$.

Proof. Equation (1.6) bounds the spatial integral near $o$ above and
below by positive constants times $\int_0^bR^{3-2p}dR$. Away from $o$
the full field is bounded and $\mu(\Omega)<\infty$. This proves the
first equivalence, including failure at equality. More precisely, its
polar integrand after angular integration is

$$
\frac{\pi^2}{2}m_0c_G^pR^{3-2p}(1+O(R))\,dR.
\tag{2.4}
$$

At $p=2$ the error is integrable and
$(\pi^2/2)m_0c_G^2=1/(8m_0)$, proving (2.3). For $p>2$ the leading
divergence is
$(\pi^2/2)m_0c_G^p\epsilon^{4-2p}/(2p-4)$; for $0<p<2$ the integral
over $R<\epsilon$ is asymptotic to
$(\pi^2/2)m_0c_G^p\epsilon^{4-2p}/(4-2p)$.

The classical degree $2-Q$ heat-integral kernel and homogeneous-gauge
calculus underlying (1.6) are described in Ciatti–Cowling–Ricci,
[*Hardy and uncertainty inequalities on stratified Lie groups*, §2,
(2.1)–(2.6)](https://arxiv.org/html/1308.2373v1), with $Q=4$ and Riesz
order $2$. They are intermediate tools here; the full variable-coefficient
killed source normalization and its remainder are those of G, §§10–11,
and have not been replaced by a homogeneous global model.

For any nonnegative Borel $W$, Tonelli applied twice to the original
killed heat density gives, with infinity allowed,

$$
\mathbb E_o\int_0^\tau W(Q_t)\,dt
=\int_0^\infty\int_\Omega p_t^\Omega(o,q)W(q)\,d\mu(q)dt
=\nu(W).
\tag{2.5}
$$

This is the usual expected-occupation identity; the same Tonelli proof
is given for killed Brownian heat densities in Mörters–Peres,
[*Brownian Motion*, public draft, Definition 3.30 and Theorem 3.31,
p.83](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf).
Here the density is the native $p_t^\Omega$ relative to raw $\mu$;
no Euclidean Brownian kernel or its normalization is substituted.
Taking $W=\Gamma^p$ proves the second equivalence by the first one at
exponent $p+1$. The nonnegative integral is almost surely finite when its
mean is finite. Infinite mean alone gives no converse pathwise assertion.

It remains to examine the actual commands. On any nonzero constant-control
chord passing through $o$ at time $t_*$, choose the continuous phase
representatives about that contact. If its control velocity is $w$, the
native flow equations give exactly

$$
(x,y,z)=(s w^1,s w^2,\tfrac12s^2w^1w^2),\qquad
\upsilon=0,\qquad R=|Bw|\,|s|,\quad s=t-t_*.
\tag{2.6}
$$

This also holds on either available side of an endpoint contact. Thus
(1.6) makes the time integrand comparable to $|t-t_*|^{-2p}$.
Each nonzero chord has only finitely many contacts with the actual
source: if $w^1\ne0$, its height can equal $k_o$ at most once; if
$w^1=0$ and $w^2\ne0$, its lifted $\alpha$ is nonconstant affine and
hits the source residue class only finitely often on a finite interval.
The finite torus windings do not change this argument. On the remaining
closed portions the field is bounded; the same off-source bound applies
towards a killed face. A stationary chord away from $o$ is harmless.
There are finitely many chords, and the terminal height leg is nonzero
until killing. This proves the claimed classification for an individual
realization with or without a source hold. In particular its first chord
either holds at $o$ for positive time or has a positive initial interval
of the form (2.6). It forces divergence for every $p\ge1/2$, at every $n$.

Finally let $s_*>0$ be the minimum singular value of $\Sigma$ on the
closed cylinder, and let $D=\sup|d|$. Every random increment satisfies

$$
|v_i|\ge2s_*\sqrt{\delta_n}-D\delta_n>0
\tag{2.7}
$$

for all sufficiently large $n$, uniformly in its node and signs.
There is consequently no source hold before death at these meshes.
For a fixed $n$ the law has finite support, at most $4^{m_n}$ commands.
When $p<1/2$, finiteness on each command therefore implies finiteness
of the expectation. The logarithmic assertion follows from
$\int_\epsilon^c s^{-1}ds$. $\square$

## 3. Failure inside the original horizontal form domain

**Theorem 3.1 (a normalized original-domain squared-amplitude witness).**
Fix any $a$ with $1/2\le a<1$. Choose a nonnegative radial cutoff
$\chi=\chi_0(R)$ in the source chart, equal to one for $R<b/2$ and
zero for $R\ge b$, where the closed gauge ball is inside that chart.
Extend by zero and set

$$
N_a^2=\int_\Omega\chi^2R^{-2a}\,d\mu,\qquad
u_a=N_a^{-1}\chi R^{-a},\qquad W^{(a)}=|u_a|^2,
\quad W^{(a)}(o)=+\infty.
\tag{3.1}
$$

The amplitude denotes an $L^2(\mu)$ class; its source value has no bearing
on membership in the form domain. Then

$$
\begin{gathered}
0<N_a<\infty,\quad u_a\in\mathcal F_A,\quad \|u_a\|_2=1,\quad
0<\int_\Omega\Gamma|u_a|^2d\mu<\infty,\\
\mathbb E_o\int_0^\tau W^{(a)}(Q_t)dt=\nu(W^{(a)})<\infty,
\qquad
\int_0^{\zeta_n}W^{(a)}(\bar q_n(t))dt=+\infty
\quad\hbox{for every realization and every }n\ge1.
\end{gathered}
\tag{3.2}
$$

In particular the continuous-test bridge of G, (29.15), cannot be
extended to all normalized squared amplitudes in its original kinetic
domain, even after requiring a finite full Green potential integral.

Proof. Near the source the squared norm is controlled by
$\int_0^bR^{3-2a}dR$, and the potential integral by
$\int_0^bR^{1-2a}dR$. Both are finite for $a<1$, and positivity is
immediate. In the source chart the energy is exactly
$\int m\langle C\nabla_Hu,\nabla_Hu\rangle dq$ of G, (10.2), with
$C$ smooth uniformly positive definite. The identity
$|\nabla_HR|^2=\cos a_{\rm ang}\le1$ from G, (10.9), gives

$$
T_A[u_a;R<b/2]\le C_a\int_0^{b/2}R^{1-2a}dR<\infty.
\tag{3.3}
$$

The angular symbol $a_{\rm ang}$ in this identity is unrelated to the
chosen exponent. The cutoff collar has finite energy because it is
smooth and separated from $o$.

To verify the original closure domain, take a smooth $\eta$ with
$\eta=0$ on $[0,1]$, $\eta=1$ on $[2,\infty)$ and bounded derivative.
The functions $u_{a,\epsilon}=u_a\eta(R/\epsilon)$ belong to
$C_c^\infty(\Omega\setminus\{o\})$. The same polar estimates and the
product rule give

$$
\|u_a-u_{a,\epsilon}\|_2^2=O(\epsilon^{4-2a}),\qquad
T_A[u_a-u_{a,\epsilon}]=O(\epsilon^{2-2a})\longrightarrow0.
\tag{3.4}
$$

Indeed the derivative of $\eta(R/\epsilon)$ is bounded by
$C/\epsilon$ on $\epsilon<R<2\epsilon$, whose contribution is
$O(\epsilon^{-2}\epsilon^{4-2a})$. Thus membership is in exactly
$\mathcal F_A$, without a critical completion or a substituted Sobolev
domain. Equation (2.5) supplies the diffusion assertion and its almost
sure finiteness. On a nonzero initial chord, (2.6) and $\chi=1$ near
zero give a positive multiple of $t^{-2a}$; a zero initial chord is a
source hold. Since $2a\ge1$, both cases give the last assertion of
(3.2). This is the same-source full-coefficient application of the
elementary cutoff and polar estimates, not an additional general Hardy
theorem. $\square$

## 4. Fixed caps and the order of limits

**Theorem 4.1 (bounded-cap transfer and incompatible uncapping orders).**
Let either $W=\Gamma^p$ for $p>0$ or $W=W^{(a)}$ from Theorem 3.1.
For every fixed $M>0$ and every $h\in C(\overline\Omega)$,

$$
\lim_{n\to\infty}\nu_n(hW_M)
=\mathbb E_o\int_0^\tau h(Q_t)W_M(Q_t)dt
=\nu(hW_M).
\tag{4.1}
$$

Complex $h$ is permitted. These bounded observations use the entire
original lifetime. For $W=\Gamma^p$ with $1/2\le p<1$, and for every
$W=W^{(a)}$, put $J=\nu(W)<\infty$. The two iterated limits are

$$
\lim_{M\to\infty}\lim_{n\to\infty}\nu_n(W_M)=J,
\qquad
\lim_{n\to\infty}\lim_{M\to\infty}\nu_n(W_M)=+\infty.
\tag{4.2}
$$

For $W=\Gamma^p$ with $p\ge1$, both iterated limits are infinity.

Proof. The cap extends continuously across the source by setting
$W_M(o)=M$, since $W\to\infty$ uniformly there. It is bounded and
continuous in the interior. Boundary continuity of $\Gamma$ need not
be assumed: take $0\le\vartheta_\epsilon(k)\le1$ continuous, zero in
a height collar of both faces and one outside a slightly larger collar,
with $\vartheta_\epsilon\to1$ at every interior point. Then
$\vartheta_\epsilon hW_M$ extends continuously by zero to the closed
cylinder. G, Theorem 29.6, applies to this test and to
$1-\vartheta_\epsilon$. The difference between its occupation and that
of $hW_M$ is at most

$$
M\|h\|_\infty\nu_n(1-\vartheta_\epsilon).
\tag{4.3}
$$

After $n\to\infty$ this bound is
$M\|h\|_\infty\int\Gamma(1-\vartheta_\epsilon)d\mu\to0$, by the
full Green $L^1$ property. The target error has the same bound.
This proves (4.1), using precisely the inherited complete-lifetime
bridge and its tail estimate rather than a new infinite-time limiting
argument. The diffusion identity is (2.5), applied to the absolute bound
and then to real and imaginary parts.

For fixed $M$ use (4.1), then monotone convergence in $M$. This gives
the first limit in (4.2), including infinity when $p\ge1$. In the
opposite order monotone convergence at each fixed $n$ gives
$\nu_n(W)$, which is infinity on every command by Theorems 2.1 and
3.1 in all the stated cases. This proves the other limits. Monotone
convergence is used only for increasing nonnegative observations; no
uniform-integrability conclusion is extracted from weak convergence.
$\square$

## 5. Necessary simultaneous cap rates from the actual first cell

**Theorem 5.1 (first-cell law, full-occupation obstruction and sufficiency boundary).**
Let $0<p<1$ and choose one of the following observations, with its
indicated source coefficient:

$$
W=\Gamma^p,\quad \kappa=c_G^p;
\qquad\hbox{or}\qquad
p=a\in[1/2,1),\quad W=W^{(a)},\quad \kappa=N_a^{-2}.
\tag{5.1}
$$

In both cases $W=\kappa R^{-2p}(1+O(R))$ near $o$ and
$J=\nu(W)<\infty$. Let $M_n\to\infty$ be deterministic caps on the
observation $W$, and write

$$
A_n=\nu_n(W_{M_n}),\qquad
I_n=\mathbb E\int_0^{\delta_n}W_{M_n}(\bar q_n(t))dt,
\qquad b_p=\kappa\,4^{-p}.
\tag{5.2}
$$

For all sufficiently large $n$ the entire first cell is alive. Uniformly
over every choice of $M_n>0$, its expectation obeys

$$
I_n=(1+O(\sqrt{\delta_n}))\,
b_p\delta_n^{1-p}F_p(M_n\delta_n^p/b_p),\qquad
F_p(h)=\int_0^1\min(h,s^{-2p})ds.
\tag{5.3}
$$

The exact scalar function is

$$
F_p(h)=
\begin{cases}
h,&0<h\le1,\\
\displaystyle\frac{2p\,h^{(2p-1)/(2p)}-1}{2p-1},
   &h\ge1,\ p\ne1/2,\\
1+\log h,&h\ge1,\ p=1/2.
\end{cases}
\tag{5.4}
$$

Full capped convergence $A_n\to J$ necessarily implies $I_n\to0$.
The exact criteria for this *first-cell* vanishing are

$$
\begin{array}{c|c|c}
\text{exponent}&I_n\to0&\delta_n=n^{-2}\\ \hline
0<p<1/2&\text{automatic for all }M_n\to\infty&\text{no first-cell restriction}\\
p=1/2&\sqrt{\delta_n}\log M_n\to0&\log M_n=o(n)\\
1/2<p<1&\sqrt{\delta_n}M_n^{1-1/(2p)}\to0
  &M_n=o(n^{2p/(2p-1)}) .
\end{array}
\tag{5.5}
$$

Each nonautomatic condition is therefore necessary for convergence of
the full original commands. It is sufficient for removing the first-cell
contribution, with no assertion that it controls later cells.

There is also a quantitative excess. Along every subsequence,

$$
\liminf_n(A_n-I_n)\ge J,
\qquad \liminf_n A_n\ge J+\liminf_n I_n.
\tag{5.6}
$$

In particular, at $p=1/2$, if
$\log M_n\sim c/\sqrt{\delta_n}$ with $c>0$, then
$I_n\to\kappa c/2$. At $1/2<p<1$, if
$M_n\sim C\delta_n^{-p/(2p-1)}$ with $C>0$, then

$$
I_n\longrightarrow
\frac{p}{2p-1}\kappa^{1/(2p)}C^{1-1/(2p)}>0.
\tag{5.7}
$$

These boundary rates already preclude $A_n\to J$; rates for which the
corresponding expression in (5.5) tends to infinity give $A_n\to\infty$.
For example, $a=3/4$ in (3.1) requires $M_n=o(n^3)$, and caps
$M_n\sim Cn^3$ have a positive excess at least
$\tfrac32N_a^{-4/3}C^{1/3}$.

For $W=\Gamma^p$, a cap $K_n$ on $\Gamma$ means
$W_{M_n}=(\Gamma\wedge K_n)^p$ with $M_n=K_n^p$. Thus the necessary
conditions are $\log K_n=o(n)$ at $p=1/2$ and
$K_n=o(n^{2/(2p-1)})$ for $1/2<p<1$. They refer to the cap on the
specified observable, not to a changed source or kinetic form.

For precision about the remaining sufficiency question, full convergence
$A_n\to J$ is equivalent to the additional complete-occupation tail
condition

$$
\lim_{K\to\infty}\limsup_{n\to\infty}
\nu_n(W_{M_n}-W_K)=0,
\tag{5.8}
$$

where for each fixed $K$ the difference is considered only for the
eventual indices with $M_n\ge K$. There exist sufficiently slowly
growing deterministic caps giving $A_n\to J$. No explicit rate in
(5.5) is asserted sufficient for (5.8), and no uncapped convergence
is asserted for $0<p<1/2$. For $p\ge1$ and $W=\Gamma^p$, in contrast,
every sequence $M_n\to\infty$ satisfies
$\nu_n(W_{M_n})\to\infty$ as an extended expected-occupation limit.

Proof. At the first node put $v=v_0$ and let its signs be $\xi$.
The height margin of $o$ is positive and $|v|\le C\sqrt{\delta_n}$,
so for large $n$ its whole first cell is inside $I$ and the source chart.
Equations (1.4)–(1.5) give, exactly for $0<t\le\delta_n$,

$$
\upsilon(t)=0,\qquad
R(t)=\ell_{n,\xi}\,t/\delta_n,\qquad
\ell_{n,\xi}=|Bv|
=|\delta_n Bd(o)+\sqrt{2\delta_n}\xi|
=2\sqrt{\delta_n}(1+O(\sqrt{\delta_n})).
\tag{5.9}
$$

The last estimate is uniform over the four sign choices. In particular
it keeps the covariance normalization $2A\,dt$, including its cross
term. With $s=t/\delta_n$, (1.6) or (3.1) now gives

$$
W(\bar q_n(t))
=b_p\delta_n^{-p}s^{-2p}(1+O(\sqrt{\delta_n})),\quad 0<s\le1,
\tag{5.10}
$$

uniformly even as $s\downarrow0$. For any positive $x,M$ and
$0<e<1$, a multiplicative bound $(1-e)x\le y\le(1+e)x$ implies
$(1-e)\min(x,M)\le\min(y,M)\le(1+e)\min(x,M)$.
Applying this to (5.10), integrating, then averaging the four signs,
proves (5.3) uniformly in the cap. Splitting the integral defining $F_p$
at $s=h^{-1/(2p)}$ for $h\ge1$ proves (5.4) by direct integration.

If $p<1/2$, $F_p(h)\le(1-2p)^{-1}$ for every $h$, proving automatic
vanishing. At $p=1/2$, the range $h\le1$ has
$I_n\le C\delta_n^{1/2}$; the range $h\ge1$ has
$I_n\sim b_p\delta_n^{1/2}(1+\log h)$.
Since $\sqrt{\delta_n}|\log\delta_n|\to0$ and $M_n\to\infty$,
these are exactly the middle criterion of (5.5). At $p>1/2$,
$F_p(h)$ is comparable to $h^{1-1/(2p)}$ on $h\ge1$, giving
$I_n\asymp\sqrt{\delta_n}M_n^{1-1/(2p)}$ there.
On $h\le1$ both $I_n$ and this latter expression are at most a
constant times $\delta_n^{1-p}\to0$. This proves the last equivalence,
and its stated $n$ form. The same formulas give the boundary constants:
$b_{1/2}=\kappa/2$, and
$\frac{2p}{2p-1}b_p^{1/(2p)}
=\frac{p}{2p-1}\kappa^{1/(2p)}$. In the power boundary regime
$M_n\delta_n^p\to\infty$ because $p<1$, justifying use of that branch.

To pass from the first cell to a necessary condition for the *whole*
occupation, fix $K>0$. For all large $n$, $M_n\ge K$ and the first
cell is alive. Positivity yields

$$
A_n-I_n
\ge\nu_n(W_K)-\mathbb E\int_0^{\delta_n}W_K(\bar q_n(t))dt
\ge\nu_n(W_K)-K\delta_n.
\tag{5.11}
$$

By Theorem 4.1 its right side tends to $\nu(W_K)$. Letting $K\to\infty$
proves (5.6), also along every subsequence. If $A_n\to J$ but $I_n$
does not tend to zero, a subsequence with $I_n\ge c>0$ contradicts
(5.6). Thus no cancellation by later nonnegative occupations can
remove the initial excess. This proves necessity without presuming
convergence of the unbounded test on the rest of the trajectory.

Condition (5.8) is the classical truncation/uniform-integrability
mechanism applied to these actual occupation measures. Here is the
complete argument in this setting. If $A_n\to J$, then at fixed $K$
the difference in (5.8) tends to $J-\nu(W_K)$, which tends to zero.
Conversely (5.8), fixed-$K$ convergence, and
$A_n=\nu_n(W_K)+\nu_n(W_{M_n}-W_K)$ give $\limsup A_n\le J$.
Positivity and fixed caps give $\liminf A_n\ge\nu(W_K)$ for every
$K$, hence $\liminf A_n\ge J$. This proves the equivalence.
It does not assert (5.8) from the lifetime estimate: that estimate
controls elapsed time, not singular source weights on later chords.

There is a qualitative sufficient cap choice. For each integer $j\ge1$,
fixed-cap convergence supplies $N_j$, increasing strictly to infinity,
such that $|\nu_n(W_j)-\nu(W_j)|<1/j$ for every $n\ge N_j$.
Put $M_n=j$ on $N_j\le n<N_{j+1}$, and choose any positive caps on
the finite initial segment. Then $M_n\to\infty$ and
$|A_n-J|\le1/j+|\nu(W_j)-J|\to0$. This proves existence but gives
no quantitative bound on $N_j$ and no explicit sufficient cap rate.
It is not an uncapped bridge. Finally, if $p\ge1$, positivity gives
$\liminf\nu_n(W_{M_n})\ge\nu(W_K)$ for every fixed $K$ by Theorem
4.1; these lower bounds tend to infinity by Theorem 2.1. $\square$

## 6. The interpolation boundary within the original lawful history class

**Proposition 6.1 (a different lawful departure, without a diffusion-limit claim).**
For each observation of (5.1) with $1/2\le p<1$, there is a deterministic
absolutely continuous original two-control history, with the same source,
preparations, guards, clock and two killed faces, whose complete
occupation of $W$ is finite. Thus the universal divergence in Theorems
2.1 and 3.1 is a property of the prescribed §29.2 commands; it is not
a property of every absolutely continuous native history.

Proof. Choose $1/2<\gamma<1/(2p)$ and a sufficiently small
$0<e<4\pi$. On $0\le t\le1$ set $a(t)=0$, $b(t)=et^\gamma$.
On $1\le t\le2$ set $a(t)=(u-k_o)(t-1)$ and $b(t)=e$.
Hold after time $2$. Both controls are absolutely continuous with
finite variation, start at zero, and their actual integral $j=\int a\,db$
is zero. Their height stays at $k_o$ initially, then increases to $u$;
every prefix therefore obeys the native guard inside $(0,H)$, and
the first killed face is reached exactly at time $2$.

On the initial segment the exact source chart gives
$R=|B(0,e)^{\mathsf T}|t^\gamma$ and $\upsilon=0$. Choose $e$ small
enough for that segment to stay in the chart. The singular occupation
there is bounded by a constant times
$\int_0^1t^{-2p\gamma}dt<\infty$. During the terminal height leg,
the actual $\alpha$ phase differs from $\alpha_o$ by $e/2$, a nonzero
residue modulo $2\pi$. That compact leg stays separated from $o$,
so the full Green field and the chosen $W$ are bounded there, including
towards $u$. This proves finiteness for the complete killed history.
The original absolutely continuous history class is N, Definition 3.1,
with prefix realization and guards in N, Theorems 9.2–9.3 (also K,
Definition 2.2 and Proposition 2.3). This deterministic command changes
the control profile, not the analytic clock. It is not the law of G,
Definition 29.2, and no diffusion approximation for it or for an altered
sampler is inferred. $\square$

Theorems 2.1–5.1 concern the original full variable-coefficient free
Green field and its specified command family. They do not alter G's
continuous-test convergence, source data or critical stability and
domain classification. In particular the dimension quantities remain
current-ray dimension three, direct rank two and homogeneous volume
exponent four. Neither a physical Euclidean dimension nor preparation
or physical-energy capabilities follow from these occupation results.

## 追加锚（本行以下为增补区）

## 7. Uniform source-ball occupation of the original complete commands

**Theorem 7.1 (height-band control and actual-chord source-ball bound).**
Fix any model and source of Definition 1.1, with precisely G,
Definitions 29.1–29.2's capabilities and commands. Write
$e_n=\sqrt{\delta_n}=1/n$. There are $n_0$, $\epsilon_0>0$ and finite
constants $C_1,C_2$, depending on this fixed model and source, such that
the following assertions hold simultaneously for every $n\ge n_0$.

Use G, Lemma 29.5's comparison node chain, starting at the same $o$,
only up to its first node exit

$$
K_i=k(q_i),\qquad K_0=k_o,\qquad
N_n=\inf\{i\ge1:K_i\notin(l,u)\}.
\tag{7.1}
$$

Couple this auxiliary chain with the actual command on its first $m_n$
sign vectors, as in G, Lemma 29.5; subsequent comparison signs are not
executed. At a final exiting cell it retains the uncut endpoint for
estimation; the actual command still stops at the first wall hit.
For every $s\ge0$ its expected number of alive nodes in the height band
satisfies

$$
\delta_n\,\mathbb E\sum_{i=0}^{N_n-1}
  {\bf1}_{\{|K_i-k_o|\le s\}}\le C_1(s+e_n).
\tag{7.2}
$$

For $0<\epsilon\le\epsilon_0$ let $\mathcal B_\epsilon$ be the
source-chart ball $\{R<\epsilon\}$, including $o$. Then

$$
\nu_n({\bf1}_{\mathcal B_\epsilon})\le C_2\epsilon.
\tag{7.3}
$$

This includes every executed random chord, its possible wall cut, and
the original terminal height leg at $S_n$ on survival. Constants and the
mesh threshold are independent of $s$ and $\epsilon$ in their stated
ranges. No phase-independent coefficient or autonomous law of a
horizontal projection is assumed.

Proof. All conditional expectations below condition on the entire past
$\mathcal F_i$, including both actual phases and chronological area.
Put $\delta=\delta_n$ and $e=e_n$. Compactness, smoothness, positivity
of $\rho$ and positive definiteness of $A$ give constants
$a_*,s_*,C_v>0$ and $D\ge0$ such that, at every alive node,

$$
\begin{gathered}
a^{11}\ge a_*,\qquad |d^1|\le D,\qquad
\sigma_{\min}(\Sigma)\ge s_*,\qquad |v_i|\le C_ve,\\
\mathbb E_i v_i^1=d^1(q_i)\delta,\qquad
\mathbb E_i (v_i^1)^2
 =2a^{11}(q_i)\delta+(d^1(q_i))^2\delta^2\ge2a_*\delta.
\end{gathered}
\tag{7.4}
$$

The moment identities are exactly G, (29.8), without a change to the
density drift. Moreover, $|\xi_i|=\sqrt2$ gives
$|v_i|\ge2s_*e-\|d\|_\infty e^2$. Increase $n_0$ so that

$$
c_ve\le |v_i|\le C_ve
\tag{7.5}
$$

for some $c_v>0$, uniformly in all nodes and sign choices. In particular
no executed random chord is stationary. G, (29.13), already proves

$$
\delta\mathbb E N_n\le M
\tag{7.6}
$$

for a fixed $M<\infty$. Its hypotheses are just (7.4)'s positive height
variance, bounded drift and increments, with conditioning on the full
state. We use this mean node-exit estimate, rather than inferring a
singular-weight estimate from the lifetime tail.

To prove (7.2), put $L=s+C_ve$ and use the convex $C^1$ function

$$
F_L(x)=
\begin{cases}
x^2/2,&|x|\le L,\\
L|x|-L^2/2,&|x|>L.
\end{cases}
\tag{7.7}
$$

It satisfies $0\le F_L(x)\le L|x|$ and $|F_L'(x)|\le L$.
For $x=K_i-k_o$ and $h=v_i^1$, convexity makes
$F_L(x+h)-F_L(x)-F_L'(x)h$ nonnegative. If $|x|\le s$, the whole
segment from $x$ to $x+h$ lies in $[-L,L]$, so this remainder is
exactly $h^2/2$. Thus at every $i<N_n$,

$$
\mathbb E_i\{F_L(K_{i+1}-k_o)-F_L(K_i-k_o)\}
\ge a_*\delta\,{\bf1}_{\{|K_i-k_o|\le s\}}-DL\delta.
\tag{7.8}
$$

The negative term bounds the signed drift contribution
$F_L'(K_i-k_o)d^1(q_i)\delta$; no symmetry of the variable drift
is required. For a deterministic integer $j$, sum (7.8) with the
$\mathcal F_i$-measurable indicators $\{i<N_n\wedge j\}$.
Since $F_L(K_0-k_o)=0$, this gives

$$
a_*\delta\,\mathbb E\sum_{i<N_n\wedge j}
 {\bf1}_{\{|K_i-k_o|\le s\}}
\le \mathbb E F_L(K_{N_n\wedge j}-k_o)
       +DL\delta\mathbb E(N_n\wedge j).
\tag{7.9}
$$

Before exit the height is in $I$; its last uncut overshoot has size at
most $C_ve$. Hence
$|K_{N_n\wedge j}-k_o|\le C_K$ with, for example,
$C_K=(u-l)+C_v$ for $e\le1$. By (7.6), the right side of (7.9)
is at most $L(C_K+DM)$. Monotone convergence as $j\to\infty$
proves (7.2). In particular the terminal overshoot has been included
in the telescope, without optional stopping at an unbounded time.

We next estimate actual elapsed time in $\mathcal B_\epsilon$.
Choose $\epsilon_0$ so that its closed ball lies in the injective
source chart of Definition 1.2. From (1.5), for a fixed $C_B>0$,

$$
R<\epsilon\ \Longrightarrow\
 |(x,y)|\le C_B\epsilon,\qquad
x=k-k_o,\quad y=2(\alpha-\alpha_o)
\tag{7.10}
$$

in the local representatives. Indeed $|B(x,y)^{\mathsf T}|\le R$,
so $C_B=\|B^{-1}\|$ suffices. This implication discards the central
coordinate only for an upper bound on a set of times. It imposes no
quotient dynamics and makes no change to $j=\int a\,db$.

On the $i$th random cell the lifted horizontal pair is exactly

$$
(k-k_o,\,2(\alpha-\alpha_o))
 =(K_i-k_o,\,y_i)+\theta(v_i^1,v_i^2),\qquad 0\le\theta\le1.
\tag{7.11}
$$

Here the lift $y_i$ can be chosen on this one cell; its actual period
is $4\pi$. Source representatives in this plane have centers
$(0,4\pi z)$, $z\in\mathbb Z$. Decrease $\epsilon_0$ and increase
$n_0$ so that $2C_B\epsilon_0+C_v/n_0<4\pi$.
An entire cell has horizontal length at most $C_ve$, so it can meet
at most one of the disks of radius $C_B\epsilon$ about these centers:
points of two different disks are separated by at least
$4\pi-2C_B\epsilon>C_ve$. On the lift centered at that disk,
the intersection of the affine segment (7.11) with the disk is an
interval of $\theta$-length at most
$\min(1,2C_B\epsilon/|v_i|)$. Possible further restrictions from the
actual $\beta$ phase or the central gauge can only shorten its total
time. Therefore (7.5) proves that the executed portion of this cell
spends at most

$$
C\delta\min(1,\epsilon/e)
\tag{7.12}
$$

in the source ball. The same upper bound applies to a wall-cut cell,
as its actual time interval is a prefix of this segment.

If that executed portion meets the ball, (7.10) and the height part
of (7.11) give $|K_i-k_o|\le C_B\epsilon+C_ve$.
Let $J_n=N_n\wedge m_n$; its indices $0\le i<J_n$ are exactly the
random cells with an alive starting node, including the last cut cell
when there is one. Combining (7.12) and (7.2) at
$s=C_B\epsilon+C_ve$ yields

$$
\begin{aligned}
\mathbb E\int_0^{\zeta_n\wedge S_n}
 {\bf1}_{\mathcal B_\epsilon}(\bar q_n(t))dt
&\le C\delta\min(1,\epsilon/e)\,
 \mathbb E\sum_{i<J_n}
 {\bf1}_{\{|K_i-k_o|\le C_B\epsilon+C_ve\}}\\
&\le C\min(1,\epsilon/e)(\epsilon+e)
 \le 2C\epsilon.
\end{aligned}
\tag{7.13}
$$

The last inequality follows separately from $\epsilon\ge e$ and
$\epsilon<e$. Thus the estimate holds even for balls smaller than
the mesh displacement. It counts all returns to the source chart;
no density of a node distribution or exclusion of return contacts
has been used.

It remains to include the unchanged terminal leg. It occurs only
on $N_n>m_n$, where $K_{m_n}<u$, and has exactly

$$
k(t)=K_{m_n}+\frac{t-S_n}{\delta}(u-K_{m_n}),
\qquad S_n\le t\le S_n+\delta,
\tag{7.14}
$$

with $b,j$ constant. Decrease $\epsilon_0$ so that
$C_B\epsilon_0\le(u-k_o)/2$.
If this increasing leg meets $\mathcal B_\epsilon$, then
$K_{m_n}\le k_o+C_B\epsilon$, so
$u-K_{m_n}\ge(u-k_o)/2$. Its elapsed time in the necessary height
band $|k-k_o|\le C_B\epsilon$ is consequently at most

$$
\delta\frac{2C_B\epsilon}{u-K_{m_n}}
\le \frac{4C_B}{u-k_o}\,\delta\epsilon.
\tag{7.15}
$$

This is a deterministic bound on every surviving command, with zero
contribution when the leg misses the ball. Combining it with (7.13)
and $\delta\le1$ proves (7.3) for the complete original lifetime.
Holds after a wall hit are outside $[0,\zeta_n)$ and do not enter any
of these integrals. $\square$

The convex remainder and stopped telescoping in (7.7)–(7.9) are the
classical convex occupation/Lyapunov method, of the same type as the
discrete absolute-value decomposition and Itô–Tanaka argument in
Kartashov–Kulik, [*Invariance principle for additive functionals of
Markov chains*, §5, Proposition 3, (5.2)–(5.3)](https://arxiv.org/html/0704.0508v1).
That proposition treats a scalar diffusion approximation with scalar
coefficients. Here $K_i$ need not be an autonomous scalar Markov chain:
its coefficients depend on the complete native state. Equations
(7.4)–(7.9) prove the estimate directly under that dependence. The
classical convex identity is an intermediate tool; the conclusion
(7.3) concerns the specified native chords and their complete killing
rule.

## 8. Uncapped subcritical expected occupation

**Theorem 8.1 (uniform source-weight tails and the full subcritical bridge).**
For every fixed admitted model of Definition 1.1, there are $n_0$ and
$\epsilon_0>0$ as in Theorem 7.1 such that, for each $0<p<1/2$, a
finite $C_p$ satisfies

$$
\begin{gathered}
\nu_n({\bf1}_{\{o\}})=0\quad(n\ge n_0),\\
\sup_{n\ge n_0}
 \nu_n(R^{-2p}{\bf1}_{\mathcal B_\epsilon})
 \le C_p\epsilon^{1-2p},\qquad 0<\epsilon\le\epsilon_0,\\
\sup_{n\ge n_0}
 \nu_n(\Gamma^p{\bf1}_{\mathcal B_\epsilon})
 \le C_p\epsilon^{1-2p}.
\end{gathered}
\tag{8.1}
$$

The local weight is extended by zero outside the source chart and
has value infinity at $o$. In particular the spatial source-weight
tails vanish uniformly for these expected occupation measures:

$$
\lim_{M\to\infty}\sup_{n\ge n_0}
 \nu_n\bigl(\Gamma^p-(\Gamma^p\wedge M)\bigr)=0.
\tag{8.2}
$$

For exactly the original uncapped complete commands the limit is

$$
\boxed{\displaystyle
\lim_{n\to\infty}\mathbb E\int_0^{\zeta_n}
 \Gamma(\bar q_n(t))^pdt
=\mathbb E_o\int_0^\tau\Gamma(Q_t)^pdt
=\int_\Omega\Gamma^{p+1}\,d\mu<\infty,
\qquad 0<p<\tfrac12.}
\tag{8.3}
$$

Every command at $n\ge n_0$ still has the finite integral of Theorem
2.1. The new assertion is uniform control of its expected spatial
tails and convergence of its expectation, not a deduction of either
from that individual finiteness.

Proof. Each $\nu_n$ is a finite Borel measure: it is the expectation
of the time-occupation measure of the actual finite command; we write
$\nu_n(E)=\nu_n({\bf1}_E)$ for Borel sets $E$. For the
indices in question, (7.6) and the terminal-leg duration even give
$\nu_n(1)\le M+\delta_n\le M+1$.
The balls $\mathcal B_\epsilon$ decrease to $\{o\}$, so continuity
from above and (7.3) give zero source mass for every such $\nu_n$.

Put $a=2p\in(0,1)$. For $0<r<\epsilon$ the elementary identity

$$
r^{-a}=\epsilon^{-a}
       +a\int_r^\epsilon t^{-a-1}dt
\tag{8.4}
$$

and Tonelli, with infinity allowed before the estimate, give

$$
\begin{aligned}
\nu_n(R^{-a}{\bf1}_{\mathcal B_\epsilon})
&=\epsilon^{-a}\nu_n(\mathcal B_\epsilon)
 +a\int_0^\epsilon t^{-a-1}\nu_n(\mathcal B_t)dt\\
&\le C_2\epsilon^{1-a}
 +aC_2\int_0^\epsilon t^{-a}dt
 =\frac{C_2}{1-a}\epsilon^{1-a}.
\end{aligned}
\tag{8.5}
$$

There is no contribution from $R=0$, since its measure is zero.
The local comparison (1.6), after decreasing $\epsilon_0$, gives
$\Gamma\le C_\Gamma R^{-2}$ throughout the punctured ball, proving
both weighted bounds in (8.1). This layer-cake argument controls all
source returns together with the initial departure and terminal leg.

For every fixed $\epsilon>0$ in this range, the full off-source bound
of Definition 1.2 gives
$B_\epsilon=\sup_{\Omega\setminus\mathcal B_\epsilon}\Gamma^p<\infty$,
including the neighbourhoods of both killed faces. If $M\ge B_\epsilon$,
then pointwise outside a $\nu_n$-null source,

$$
0\le\Gamma^p-(\Gamma^p\wedge M)
\le\Gamma^p{\bf1}_{\mathcal B_\epsilon}.
\tag{8.6}
$$

Taking the supremum over $n\ge n_0$, then $M\to\infty$ and finally
$\epsilon\downarrow0$, proves (8.2). Equivalently one also obtains
the usual spatial-weight tail bound with
$\Gamma^p{\bf1}_{\{\Gamma^p>2M\}}$, since that function is at most
$2(\Gamma^p-(\Gamma^p\wedge M))$.

Set $W=\Gamma^p$ and $J=\nu(W)$. Theorem 2.1 gives $J<\infty$
and (2.5) identifies it with the diffusion expectation in (8.3).
For a fixed $M$, Theorem 4.1 gives $\nu_n(W\wedge M)\to\nu(W\wedge M)$
over the entire original lifetime. All quantities below are finite
for $n\ge n_0$, and positivity gives the precise truncation bound

$$
\begin{aligned}
|\nu_n(W)-J|
\le {}&|\nu_n(W\wedge M)-\nu(W\wedge M)|\\
 &+\nu_n(W-W\wedge M)+\nu(W-W\wedge M).
\end{aligned}
\tag{8.7}
$$

The first term tends to zero at each fixed $M$. The second tends to
zero uniformly in $n\ge n_0$ by (8.2); the third tends to zero by
integrability of $W$ under $\nu$. First take $n\to\infty$, then
$M\to\infty$. This proves (8.3) without a cap in the command or in
the asserted limiting observation. $\square$

The source-specific derivation (7.10)–(8.7) supplies the tail that
§5 left unclaimed for $0<p<1/2$. The truncation step is the classical
bounded-test plus uniform-integrability argument already used in the
equivalence (5.8); the additional mathematical input is the proved
uniform source-ball estimate for the same producer. It requires
neither a node transition density nor an independent horizontal
quotient law. In particular no assumption that $\rho$ or $A$ is close
to constant has entered the proof.

For comparison with published additive-functional approximation
theorems, Kulik's [*Difference approximation for local times of
multidimensional diffusions*, §2, Theorem 2.1, A1 and A3](https://arxiv.org/html/math/0702175v2)
requires uniform ellipticity in the full Euclidean state and a $C^4$
innovation density with derivative and moment bounds. The native
three-coordinate state has rank-two instantaneous covariance, and its
four-sign innovation has no Lebesgue density. Even the elliptic
horizontal projection does not remove its dependence on the remaining
state. Those hypotheses therefore do not justify applying that theorem
to these commands. Kartashov–Kulik's [§3, Theorem 1, condition 2](https://arxiv.org/html/0704.0508v1)
assumes uniform convergence of the additive-functional characteristics,
in addition to Markov approximation, vanishing maximal summands and
uniform continuity of the limiting characteristic. It cannot provide
the missing singular expectation convergence by assuming that
characteristic convergence. Kulik's [*Malliavin calculus for difference
approximations of multidimensional diffusions: truncated local limit
theorem*, §1.1, Theorem 1.1, B1 and B3](https://arxiv.org/html/0801.2319v1)
also imposes full-state ellipticity and, in B3, a positive absolutely
continuous component of the innovation law bounded below on an open
set. Four signs fail B3. Its truncation is a decomposition of transition
probabilities, not an uncapping theorem for the present source weight.
These are hypothesis comparisons, not imports of their conclusions.
The convex/Tanaka method and truncation principle are classical;
the result here is their repo-derived application with the original
full-coefficient native geometry, interpolation and termination rule.
No assertion of world priority is made.

The uniformity in (8.1)–(8.2) concerns spatial weights under the
deterministic expected measures $\nu_n$. No uniform integrability of
the random total occupations, almost sure convergence, or convergence
rate is asserted. Theorem 2.1's infinite finite-command occupations
for $p\ge1/2$, Theorem 3.1's original-form-domain witnesses and §5's
larger-exponent cap restrictions retain their stated force. Neither
(7.3) nor its layer-cake proof supplies the missing tails at those
exponents: the upper integral in (8.5) is finite only for $2p<1$.

## 追加锚（本行以下为增补区）

## 9. Full-state discrete potentials and the simultaneous cap boundary

**Lemma 9.1 (a smooth auxiliary potential with a positive decaying source).**
In the first-kind whitened coordinates $(\xi,\eta,\upsilon)$ of (1.5),
put

$$
\begin{gathered}
U=\partial_\xi-\tfrac\eta2\partial_\upsilon,\qquad
V=\partial_\eta+\tfrac\xi2\partial_\upsilon,\qquad
\Delta_H=U^2+V^2,\\
q\cdot q'=(\xi+\xi',\eta+\eta',
 \upsilon+\upsilon'+(\xi\eta'-\eta\xi')/2),\qquad
G_H(q)=(2\pi)^{-1}R(q)^{-2},\\
f_s(q)=\bigl(1+R(q)^4/s^4\bigr)^{-3/4},\qquad
\mathcal U_s(q)=\int_{\mathbb R^3}G_H(z^{-1}\cdot q)f_s(z)\,dz,
\quad s>0.
\end{gathered}
\tag{9.1}
$$

Lebesgue measure $dz$ is Haar measure for this auxiliary group. The
integral is finite, nonnegative and smooth, and

$$
-\Delta_H\mathcal U_s=f_s,\qquad
f_s(q)\asymp\frac{s^3}{(s+R(q))^3},\qquad
|Z_{i_1}\cdots Z_{i_k}\mathcal U_s(q)|
 \le C_k\frac{s^3}{(s+R(q))^{1+k}},\quad 0\le k\le4,
\quad (Z_1,Z_2)=(U,V).
\tag{9.2}
$$

For $k=0$ the derivative denotes the function itself. Constants are
independent of $s,q$ and the word of length $k$. In particular
$0\le\mathcal U_s\le Cs^2$. These are deterministic auxiliary tests;
no new random command, source normalization or physical domain is
introduced.

Proof. G, Theorem 10.2, including its flux calculation after (10.9),
gives $-\Delta_HG_H=\delta_0$ relative to Lebesgue measure. The kernel
is smooth away from zero, homogeneous of degree $-2$, and its horizontal
derivatives of order $k$ have degree $-2-k$. The function $f_1$ is
smooth even at zero, since $R^4=(\xi^2+\eta^2)^2+16\upsilon^2$ is a
polynomial. At infinity $f_1=O(R^{-3})$. The potential integral converges:
near its diagonal the kernel $R^{-2}$ is locally integrable in homogeneous
volume dimension four; at infinity its radial majorant is $CR^{-2}dR$.

Here are uniform derivative bounds, including the derivatives needed for
the discrete transfer. Write $\mathfrak d_a(\xi,\eta,\upsilon)
=(a\xi,a\eta,a^2\upsilon)$ and $u=\mathcal U_1$. For $a\ge1$,
change variables $z=\mathfrak d_a w$ to obtain

$$
a\,u(\mathfrak d_a q)
 =\int G_H(w^{-1}\cdot q)g_a(w)\,dw,\qquad
g_a(w)=\bigl(a^{-4}+R(w)^4\bigr)^{-3/4}
 \le R(w)^{-3}.
\tag{9.3}
$$

Consider $q$ in the fixed compact annulus $1\le R(q)\le2$.
Split the integral by smooth cutoffs into a sufficiently small ball
about $w=0$, a fixed intervening annulus, and the complement of a
sufficiently large ball. The small ball is separated from every such
$q$ in group distance. All derivatives in $q$ of its kernel are uniformly
bounded, and $R^{-3}$ is integrable there. On the outer region those
derivatives are bounded by $C_kR(w)^{-2-k}$, by homogeneity and compactness
of the unit gauge sphere. Multiplication by $g_a\le R^{-3}$ gives the
integrable radial bound $C_kR^{-2-k}dR$.

On the intervening annulus, let $h_a$ be $g_a$ times its smooth compact
cutoff. All ordinary derivatives of $h_a$ are bounded uniformly in
$a\ge1$, because this support avoids zero. Its contribution is

$$
\int G_H(w^{-1}\cdot q)h_a(w)dw
 =\int G_H(v)h_a(q\cdot v^{-1})dv.
\tag{9.4}
$$

For $q$ in a neighbourhood of the fixed annulus, the integrand and all
its $q$ derivatives vanish outside a common compact set of $v$.
Differentiate the smooth factor $h_a(q\cdot v^{-1})$. Its derivatives
are uniformly bounded on that set, and $G_H(v)$ is integrable there.
Thus the middle contribution has uniformly bounded derivatives too.
This proves that all horizontal derivatives through order four of the
right side of (9.3) are uniformly bounded on the fixed annulus.
Homogeneity of each horizontal field gives
$|Z_{i_1}\cdots Z_{i_k}u(q)|\le C_kR(q)^{-1-k}$ for $R(q)\ge1$.
On a fixed ball the same cutoff argument, with the smooth $f_1$ in the
middle part, bounds all derivatives and proves smoothness.

The fundamental-solution identity gives $-\Delta_Hu=f_1$ in
distributions. For example, first cut $f_1$ off at a large radius; its
potentials have that identity, and their omitted tails, together with
all local horizontal derivatives through order two, tend to zero by
the outer-region bounds above. Smoothness makes the identity pointwise.
Finally
$\mathcal U_s(q)=s^2u(\mathfrak d_{1/s}q)$ and
$f_s(q)\asymp s^3(s+R(q))^{-3}$. Scaling proves (9.2). $\square$

The fundamental solution and convolution calculus used here are classical
intermediate tools; see Ciatti–Cowling–Ricci,
[*Hardy and uncertainty inequalities on stratified Lie groups*, §2,
(2.1), (2.5)–(2.7)](https://arxiv.org/html/1308.2373v1).
The derivative bounds for the particular noncompact smooth source $f_s$
are proved above, rather than inferred from a heat-kernel upper bound.

**Lemma 9.2 (mesh-uniform node occupation with all returns).**
Keep every fixed model of Definition 1.1 and the comparison-node exit
$N_n$ of (7.1). There are $n_0,s_0>0$ and $C<\infty$, depending on
this model and source, such that

$$
\delta_n\,\mathbb E\sum_{i<N_n}
 {\bf1}_{\mathcal B_s}(q_i)
 \le C(s^2+e_n^2),\qquad
0<s\le s_0,\quad n\ge n_0,
\qquad e_n=\sqrt{\delta_n}.
\tag{9.5}
$$

The comparison after $m_n$ cells is used only for an upper bound, as in
Theorem 7.1; the executed random cells are the indices
$i<N_n\wedge m_n$. Conditioning uses the complete state and past.

Proof. The exact source-chart fields must be distinguished from their
second-kind expressions. Before whitening, $t=z-xy/2$ gives
$P=\partial_x-(y/2)\partial_t$ and
$Q=\partial_y+(x/2)\partial_t$. The graded map in G, (10.1), pushes
these fields to the columns of $B$ in the frame $(U,V)$ of (9.1).
If $w_i=Bv_i$, the actual chord in a local lift is exactly

$$
\begin{aligned}
(\xi,\eta)(\theta)&=(\xi_i,\eta_i)+\theta(w_i^1,w_i^2),\\
\upsilon(\theta)&=\upsilon_i+
 \tfrac\theta2(\xi_iw_i^2-\eta_iw_i^1),\qquad 0\le\theta\le1.
\end{aligned}
\tag{9.6}
$$

Equivalently it is $q_i\cdot(\theta w_i^1,\theta w_i^2,0)$, the flow
of $w_i^1U+w_i^2V$. Formula (9.6) is (1.4) after its quadratic
second-kind term is combined with $-xy/2$; it retains the actual
chronological area across every join.

Write $\delta=e^2=\delta_n$, $b(q)=Bd(q)$ and
$C(q)=BA(q)B^{\mathsf T}$. On a fixed source chart the generator is
exactly

$$
\mathcal G=\sum_a b^aZ_a+\sum_{a,b}C^{ab}Z_aZ_b,
\qquad C(0)=I_2,\qquad |C(q)-I_2|\le C_*R(q),\quad |b(q)|\le C_*.
\tag{9.7}
$$

This is the push-forward of G, (29.7), including its raw-density drift.
All coefficient bounds are uniform on a fixed compact chart. Applied
to (9.2), they give, for small $s$ and chart radius,

$$
|\mathcal G\mathcal U_s+f_s|
 \le C(s+R)f_s.
\tag{9.8}
$$

Indeed the second-derivative error is at most
$CRs^3(s+R)^{-3}$ and the drift error at most
$Cs^3(s+R)^{-2}$. Choose a fixed $b_0>0$ so small that
$\overline{\mathcal B_{4b_0}}$ is an injective interior chart and
(9.8) is at most $f_s/4$ whenever $s\le b_0/4$ and $R\le b_0$.
Choose $0\le\chi\le1$ smooth, equal to one on $R\le b_0$ and zero
on $R\ge2b_0$. On the native cylinder set
$F_s=\chi\mathcal U_s$ in this chart and zero elsewhere, also extending
it by zero beyond the two height faces. It is smooth and nonnegative,
$\|F_s\|_\infty\le Cs^2$, and all its horizontal derivatives through
order four outside $\mathcal B_{b_0/4}$ are bounded by $Cs^3$.
The cutoff is fixed independently of $s,n$.

We now prove the one-step error uniformly for these changing tests.
At an alive node,
$w=\delta b+\sqrt{2\delta}\,B\Sigma(q_i)\xi_i$, with the original
four signs, so

$$
\mathbb E_iw^a=\delta b^a,\qquad
\mathbb E_iw^aw^b=2\delta C^{ab}+\delta^2b^ab^b,
\qquad |\mathbb E_iw^aw^bw^c|\le C\delta^2,
\qquad |w|\le Ce.
\tag{9.9}
$$

The third bound follows by expanding the product: the pure-noise cubic
has mean zero under $\xi_i\mapsto-\xi_i$, and every other nonzero term
has at least one factor $\delta b$. It is a one-step statement;
no symmetry of a variable-coefficient multistep block is assumed.
Taylor expansion along the exact flow (9.6), through degree three with
a fourth-order integral remainder, consequently gives

$$
\left|\mathbb E_i(F_s(q_{i+1})-F_s(q_i))
      -\delta\mathcal GF_s(q_i)\right|
 \le C\delta^2\left(
 |\nabla_H^2F_s(q_i)|+|\nabla_H^3F_s(q_i)|
 +\sup_{0\le\theta\le1}|\nabla_H^4F_s(q_i(\theta))|\right).
\tag{9.10}
$$

Here $|\nabla_H^k|$ means the sum over every word of length $k$;
the coefficients of the flow are frozen at its initial node. Off the
chart the identical formula uses the original fields $P,Q$, with the
fixed factors of $B$ absorbed in $C$.

For $R(q_i)\le b_0/2$ and fine meshes the whole chord is in $R<b_0$.
The identity $|\nabla_HR|\le1$ in G, (10.9), implies
$|R(q_i(\theta))-R(q_i)|\le Ce$. Hence if $s\ge Ke$, with a fixed
sufficiently large $K$, then $s+R$ along this chord is comparable to
its initial value. Equations (9.2), (9.9)–(9.10) bound the error by

$$
C\delta^2\frac{s^3}{(s+R(q_i))^5}
 \le C\delta(e/s)^2f_s(q_i).
\tag{9.11}
$$

The second and third derivatives in (9.10) satisfy the same bound
after increasing $C$, since $s+R$ is in a fixed bounded interval.
Choose $K$ so that (9.11) is at most $\delta f_s/4$.
Together with (9.8), this gives decrement at least $\delta f_s/2$
on this smaller chart. For nodes outside $\mathcal B_{b_0/2}$, a
fine-mesh chord stays outside $\mathcal B_{b_0/4}$ whenever it meets
the support of $F_s$. All derivatives there are $O(s^3)$, so its
conditional increment is at most $C\delta s^3$. It follows globally,
for every alive node and $Ke\le s\le s_0:=b_0/4$, that

$$
\mathbb E_i(F_s(q_{i+1})-F_s(q_i))
 \le-c\delta\,{\bf1}_{\mathcal B_s}(q_i)+C\delta s^3,
\tag{9.12}
$$

where $c>0$ uses $f_s\ge2^{-3/4}$ on $\mathcal B_s$.
The positive cutoff error is controlled over the complete lifetime;
it is not discarded by an annular summation.

For each deterministic integer $j$, multiply (9.12) by the predictable
indicator $i<N_n\wedge j$ and sum. Nonnegativity of $F_s$ and
$F_s(o)\le Cs^2$ give

$$
c\delta\,\mathbb E\sum_{i<N_n\wedge j}
 {\bf1}_{\mathcal B_s}(q_i)
 \le F_s(o)-\mathbb EF_s(q_{N_n\wedge j})
       +Cs^3\delta\mathbb E(N_n\wedge j)
 \le Cs^2+CMs^3.
\tag{9.13}
$$

Here $\delta\mathbb EN_n\le M$ is exactly (7.6). The last uncut
overshoot is included in $q_{N_n\wedge j}$; $F_s$ is defined and
nonnegative there, and is zero outside the height interval.
Monotone convergence as $j\to\infty$ proves the $Cs^2$ bound for
$Ke\le s\le s_0$. Increase $n_0$ so that $Ke_n\le s_0$.
For $s<Ke_n$, set inclusion in $\mathcal B_{Ke_n}$ and that already
proved bound give $CK^2e_n^2$. This proves (9.5), including the
submesh branch, without multiplying a mere lifetime bound by $e_n^2$.
Every alive-node index is counted, including all returns. $\square$

**Theorem 9.3 (complete mesh-aware source-ball occupation).**
For every fixed model of Definition 1.1 there are $n_0,\epsilon_1>0$
and $C<\infty$ such that the unchanged complete commands satisfy

$$
\boxed{\displaystyle
\nu_n(\mathcal B_\epsilon)
 \le C(\epsilon^2+e_n\epsilon),\qquad
0<\epsilon\le\epsilon_1,\quad n\ge n_0.}
\tag{9.14}
$$

Both walls, the last cut chord, all later returns and the terminal height
leg are included.

Proof. The deterministic chord-time bound (7.12) is
$C\delta_n\min(1,\epsilon/e_n)$. It uses the nonzero two-control speed,
the true affine horizontal chord and at most one lifted source disk.
The central-coordinate condition only shortens that set of times.
If a chord meets $\mathcal B_\epsilon$, its starting node has a lift
in the same enlarged injective chart for all sufficiently small
$\epsilon,e_n$. Following this chord backwards in (9.6) and using
$|\nabla_HR|\le1$ gives
$R(q_i)\le\epsilon+Ce_n$. Choose a fixed $L\ge\max(C,K)$ and
$s=\epsilon+Le_n$. Decrease $\epsilon_1$ and increase $n_0$ so that
$s\le s_0$. Lemma 9.2, or its proved $s\ge Ke_n$ branch, yields

$$
\begin{aligned}
\mathbb E\int_0^{\zeta_n\wedge S_n}
 {\bf1}_{\mathcal B_\epsilon}(\bar q_n(t))dt
&\le C\delta_n\min(1,\epsilon/e_n)
 \mathbb E\sum_{i<N_n\wedge m_n}{\bf1}_{\mathcal B_s}(q_i)\\
&\le C\min(1,\epsilon/e_n)(\epsilon+Le_n)^2
 \le C(\epsilon^2+e_n\epsilon).
\end{aligned}
\tag{9.15}
$$

The last inequality follows separately for $\epsilon\ge e_n$ and
$\epsilon<e_n$. A wall cut restricts a chord to a prefix and therefore
preserves its time bound. The comparison's uncut exit endpoint was used
only in (9.13), not executed after a wall hit.

The unchanged terminal leg has the deterministic source-band time bound
(7.15), $C\delta_n\epsilon$, on every surviving command. It is zero
when that leg misses the ball, and otherwise its speed towards $u$ is
bounded below by the fixed source-to-upper-wall margin divided by
$\delta_n$. Since $\delta_n\le e_n$, adding this contribution proves
(9.14). No death hold is integrated. $\square$

**Theorem 9.4 (exact simultaneous cap rates for every fixed smooth model).**
Fix any model of Definition 1.1 and $1/2\le p<1$. Let $M_n\to\infty$
be arbitrary deterministic positive caps on $W=\Gamma^p$ and
$J_p=\int_\Omega\Gamma^{p+1}d\mu<\infty$. Then

$$
\boxed{\displaystyle
\nu_n(\Gamma^p\wedge M_n)\longrightarrow J_p
\quad\Longleftrightarrow\quad
\begin{cases}
e_n\log M_n\longrightarrow0,&p=1/2,\\
e_nM_n^{1-1/(2p)}\longrightarrow0,&1/2<p<1.
\end{cases}}
\tag{9.16}
$$

Under these equivalent conditions, for every
$h\in C(\overline\Omega;\mathbb C)$,

$$
\mathbb E\int_0^{\zeta_n}h(\bar q_n(t))
 (\Gamma(\bar q_n(t))^p\wedge M_n)dt
 \longrightarrow
\mathbb E_o\int_0^\tau h(Q_t)\Gamma(Q_t)^pdt
 =\int_\Omega h\Gamma^{p+1}d\mu.
\tag{9.17}
$$

Thus the necessary rates of Theorem 5.1 are sufficient for the complete
original producer, with no restriction on the size of the fixed smooth
coefficient variation. For $\delta_n=n^{-2}$ they are
$\log M_n=o(n)$ at $p=1/2$, and
$M_n=o(n^{2p/(2p-1)})$ at $1/2<p<1$.

Proof. Necessity is Theorem 5.1, which also gives its positive-excess
boundary constants. To prove sufficiency put $a=2p\in[1,2)$.
The source comparison (1.6) gives $\Gamma^p\le D_pR^{-a}$ on a
fixed ball $\mathcal B_{\epsilon_1}$. For all $M\ge1$ and
$0<\epsilon\le\epsilon_1$, (9.14) implies

$$
\nu_n\bigl((\Gamma^p\wedge M){\bf1}_{\mathcal B_\epsilon}\bigr)
 \le C_p\epsilon^{2-2p}+C_pe_n H_p(M),\qquad
H_p(M)=
\begin{cases}
1+\log M,&p=1/2,\\
M^{1-1/(2p)},&1/2<p<1.
\end{cases}
\tag{9.18}
$$

For completeness, set $t_0=(D_p/M)^{1/a}$. If $t_0<\epsilon$,
the capped layer-cake identity and Tonelli give the upper bound

$$
D_p\epsilon^{-a}\nu_n(\mathcal B_\epsilon)
 +aD_p\int_{t_0}^{\epsilon}
 t^{-a-1}\nu_n(\mathcal B_t)dt
 \le C_p\left[
 \epsilon^{2-a}+e_n\epsilon^{1-a}
 +\int_{t_0}^{\epsilon}(t^{1-a}+e_nt^{-a})dt\right].
\tag{9.19}
$$

The first integral is bounded by $C_p\epsilon^{2-a}$ because $a<2$.
For $a>1$, the other terms are bounded by $C_pe_nt_0^{1-a}$;
for $a=1$ they are bounded by
$C_pe_n(1+\log(\epsilon/t_0))\le C_pe_n(1+\log M)$, after adjusting
constants on the fixed radius range. If $t_0\ge\epsilon$, use instead
$M\nu_n(\mathcal B_\epsilon)$: here
$M\epsilon^2\le D_p\epsilon^{2-a}$ and
$M\epsilon\le D_p^{1/a}M^{1-1/a}$, with the last exponent zero
when $a=1$. These estimates prove (9.18) in both cap regimes.
Its derivation uses the actual occupation measure, not a node density.

Let $K$ be at least the finite off-source bound
$\sup_{\Omega\setminus\mathcal B_\epsilon}\Gamma^p$, which includes
neighbourhoods of both killed faces. For all eventual $n$ with $M_n\ge K$,

$$
0\le\nu_n\bigl((W\wedge M_n)-(W\wedge K)\bigr)
 \le C_p\epsilon^{2-2p}+C_pe_nH_p(M_n).
\tag{9.20}
$$

The rate in (9.16) makes the second term tend to zero. First take
$n\to\infty$, then $\epsilon\downarrow0$ (and allow $K\to\infty$).
This proves the complete-tail condition (5.8). The fixed-cap bridge of
Theorem 4.1 and that condition give convergence to $J_p$.
For (9.17), multiply each fixed-cap error by the bounded continuous
$h$ and bound its tail by $\|h\|_\infty$ times (9.20).
The target tail vanishes by $\int\Gamma^{p+1}d\mu<\infty$.
Tonelli and absolute integrability identify the diffusion expectation.
$\square$

The new input in this section is the same-producer discrete occupation
estimate (9.5), obtained from the smooth positive-source potential and
the uniform one-step bounds (9.8)–(9.13). The auxiliary potential on
$\mathbb R^3$ is cut off inside an injective chart to form a native
periodic test. Its cutoff error is $O(s^3)$ over a uniformly bounded
expected lifetime, while its initial size is $O(s^2)$. It changes neither
the raw unit-source Green field being observed nor any executed command.
This is a repo-derived application of classical homogeneous convolution,
Taylor expansion and stopped telescoping; no worldwide novelty claim
is made. In particular no limiting diffusion density is substituted
for a finite-sign-chain density.

Conclusions (9.16)–(9.17) concern deterministic expected occupation
measures. They assert neither pathwise convergence of these singular
integrals nor uniform integrability of their random total values.
They concern the single fixed observation $\Gamma^p$ with its displayed
caps, rather than all mesh-dependent smooth probes or continuity of a
command trace in the spatial form norm. The nonclosability and
changing-probe obstructions in
[Original-control instrument stability, §§7–11](https://github.com/the-omega-institute/trureturing/blob/6b0a6edd60b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md)
therefore have different quantifiers. The original integrability
thresholds and original kinetic domain in §§1–8 are retained. The
three state coordinates, two direct controls and homogeneous volume
exponent four are contact-geometric quantities, without an inference
of physical Euclidean three-space, empirical sampling capability or
Lean certification.

## 追加锚（本行以下为增补区）
