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
