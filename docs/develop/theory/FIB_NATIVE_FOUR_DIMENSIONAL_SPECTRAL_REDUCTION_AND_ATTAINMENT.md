# Native FIB: unrestricted four-dimensional spectral reduction and attainment

This volume gives ordinary handwritten mathematics for the original
full-open native affine model. Its proofs are not Lean kernel
verification. The spectral family below is derived from unrestricted
competitors; it is not an additional encoder hypothesis.

At most four real coordinates have an exact minimax reduction to complex
exponential polynomials of order at most two. The scalar infimum is a
minimum. The literal and prescribed-path classes attain their common
value, and the two guarded classes have the same infimum. Below the
transition, their attainment is equivalent to the existence of at least
one global scalar minimizer with the specified height-separating spectrum.
The scalar minimum is not evaluated in that range, and existence of such
a guarded minimizer remains unresolved.

The mathematical suppliers, with labels used throughout, are:

- **[M]** [*Native FIB: exact two-dimensional affine minimax and an
  attaining annulus*](FIB_NATIVE_TWO_DIMENSIONAL_AFFINE_MINIMAX.md),
  including its §§12–20 on the unrestricted three-dimensional plateau.
- **[Q]** [*Native FIB: an actual four-coordinate strict affine
  improvement*](FIB_NATIVE_FOUR_DIMENSIONAL_STRICT_AFFINE_IMPROVEMENT.md).
- **[O]** [*Native FIB on the full open domain: affine approximation and
  finite attainment*](FIB_NATIVE_OPEN_DOMAIN_AFFINE_APPROXIMATION_AND_FINITE_ATTAINMENT.md),
  including its §11 on fixed-dimension uniform gaps.

The precise inherited statements and parameter substitutions are in §2.
The three main theorems are stated in §3 and proved by the eight arguments
in §§4–11. Section 12 gives the resulting parameter picture and the
remaining optimization obligations. No result from an unquoted parent
manuscript is an extra premise.

## 1. Native objects, arbitrary preparation, metric and contracts

**Definition 1.1 (Fixed source and preparation).** Fix $0<Z<1$, and set

$$
r=1-Z,\qquad H=r/2,\qquad
p(k)=(k,H-k,Z,H-k,k),\qquad 0<k<H.
$$

The mode order is $(0,1,2,3,13)$, and the probability tangent is
$d=(1,-1,0,-1,1)^{\mathsf T}$. Fix any $k_0\in(0,H)$ and any
preparation phases $\theta_j^{\rm in}$. The native negative phase
convention and control equations are

$$
\psi_j=\sqrt{p_j}\,e^{-i\theta_j},\qquad
\dot p=d\dot k,\qquad
\dot\theta_j=\frac{d_j}{p_j(k)I(k)}\dot\chi,\qquad
I(k)=\frac2k+\frac2{H-k}=\frac r{k(H-k)}.
$$

A producing history is a piecewise $C^1$ or absolutely continuous
native path on a finite compact time interval, with interior height
throughout and finite phase variation. Its initial real relation phase
is consistent with $d^{\mathsf T}\theta^{\rm in}$. A queried state is
the current ray at a finite prefix, without the producing history or a
retained real lift. There is no common bound on the number of commands,
their real magnitudes, or the duration of these individually finite
histories. Put $\mathbb T=\mathbb R/(2\pi\mathbb Z)$.

**Proposition 1.2 (Exact ray coordinates and signed commands).** The
actual reachable current-ray space is

$$
\mathcal M=(0,H)\times\mathbb T^2.
$$

Writing phase increments as $(u,v,0,v,u)$, its circle coordinates are
$\alpha=u-v$ and $\beta=u$. For every real displacement $a$ and real
phase command $t$,

$$
\begin{aligned}
P_a(k,\alpha,\beta)&=(k+a,\alpha,\beta),\\
\operatorname{dom}P_a
 &=\{(k,\alpha,\beta)\in\mathcal M:0<k+a<H\},\\
Q_t(k,\alpha,\beta)
 &=\left(k,\alpha+t/2,\beta+(1/2-k/r)t\right),\\
\operatorname{dom}Q_t&=\mathcal M.
\end{aligned}
$$

The phase input $t$ remains a signed real number. Only the resulting
state coordinates are reduced on their circles.

Proof. The positive phase rates are $(H-k)/r=1/2-k/r$, the negative
rates are $-k/r$, and the middle rate is zero. Hence

$$
du=(1/2-k/r)d\chi,\qquad dv=-(k/r)d\chi,\qquad
d\alpha=d\chi/2,\qquad d\beta=(1/2-k/r)d\chi.
$$

Equal increments within each group follow from equal rates and zero
initial increments, with no equality assumption on the preparation
phases. The inverse change is $u=\beta$, $v=\beta-\alpha$; both
changes have integer coefficients and are inverse on the two circles.
With $\zeta_j=\theta_j^{\rm in}-\theta_2^{\rm in}$, use the ray
representative

$$
\left(\sqrt{k}e^{-i(\zeta_0+u)},
\sqrt{H-k}e^{-i(\zeta_1+v)},\sqrt Z,
\sqrt{H-k}e^{-i(\zeta_3+v)},
\sqrt{k}e^{-i(\zeta_{13}+u)}\right).
$$

Its positive middle entry fixes the common ray scalar. Equality of
representatives determines $k$ from the moduli and $u,v$ modulo $2\pi$
from the positive group amplitudes. Conversely those coordinates
determine the representative. Thus there is no further ray quotient.

Integration on the two straight legs gives $P_a,Q_t$. The whole
probability segment is interior exactly when its two endpoints are
interior. For reachability choose $k_1\ne k_0$ in $(0,H)$ and write
$b=k_1-k_0$. The chronological rectangle
$P_b,Q_t,P_{-b},Q_{-t}$ fixes $\alpha$ and adds $-bt/r$ to $\beta$.
Given target real representatives $\alpha_*,\beta_*$, choose

$$
L=2\alpha_*,\qquad
q=\beta_*-(1/2-k_0/r)L,\qquad t=-rq/b.
$$

That rectangle, then $Q_L$ at $k_0$, then $P_{k-k_0}$ reaches the
target. Each leg is finite and lawful. This reconstructs the native
interface of [M, §§1–2], [Q, Proposition 1.2] and [O, §1] using only
the original two controls. $\square$

**Definition 1.3 (Original outputs and preparation-dependent decoder).**
Use the ordered edges

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)),\qquad
\delta_{ij}=\theta_i^{\rm in}-\theta_j^{\rm in}.
$$

For each edge the observables are

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|.
$$

Their expectation pairs, concatenated in the declared edge order, give
$y:\mathcal M\to\mathbb R^{10}$. Define

$$
U(v)=\binom{\cos v}{\sin v},\quad
\mathsf R_v=\begin{pmatrix}\cos v&-\sin v\\\sin v&\cos v\end{pmatrix},\quad
J=\operatorname{diag}(1,-1),
$$

$$
A(k)=2\sqrt{k(H-k)},\qquad B(k)=2\sqrt{Zk},\qquad
D_0(a,b)=(a,b,a,Ja,Ja),
$$

$$
O_{\rm prep}=\bigoplus_{e\in\mathcal E}\mathsf R_{\delta_e},\qquad
D=O_{\rm prep}D_0.
$$

Here $a,b$ are planar vectors. We also identify $\mathbb C$ with this
real plane, so $D(z,0)$ is meaningful for a complex number $z$.

**Lemma 1.4 (Unchanged metric).** On the actual source,

$$
y=D(A(k)e^{i\alpha},B(k)e^{i\beta}),\qquad
D^{\mathsf T}D=4I_2\oplus I_2,\qquad
\|D(a,b)\|_2^2=4|a|^2+|b|^2.
$$

Proof. The negative phase convention gives
$\overline\psi_i\psi_j=\sqrt{p_ip_j}e^{i(\theta_i-\theta_j)}$.
The expectation pair is twice its real and imaginary parts. The five
increment differences are $\alpha,\beta,\alpha,-\alpha,-\alpha$,
and $U(-\alpha)=JU(\alpha)$. This proves the displayed factorization.
Four distinct output blocks contain the first vector and one contains
the second. Orthogonality of $J$ and the fixed preparation rotations
gives the Gram matrix. In particular $y$ is bounded, since $A\le H$
and $B<2\sqrt{ZH}$. These are the original ten-output Euclidean
weights, as in [M, Lemma 1.5], [Q, Lemma 1.4] and [O, Lemma 1.3].
$\square$

**Definition 1.5 (Four affine contracts).** For $n\ge0$, an at-most-$n$
literal model chooses $0\le m\le n$, an arbitrary encoder
$E:\mathcal M\to\mathbb R^m$, one fixed affine decoder
$\mathcal D(z)=q_0+Lz$, and one fixed affine ambient map
$\mathcal U_a$ for each $P_a$ and $\mathcal V_t$ for each $Q_t$.
They satisfy

$$
E(P_a\zeta)=\mathcal U_a(E(\zeta))
\quad(\zeta\in\operatorname{dom}P_a),\qquad
E(Q_t\zeta)=\mathcal V_t(E(\zeta))
\quad(\zeta\in\mathcal M).
$$

All affine offsets are allowed. Parameters may depend on the fixed
source, preparation, model and prescribed command, but not on the
current ray or history. No regularity, measurability, boundedness,
injectivity or computability of $E$ is assumed, and no parameter
regularity, ambient inverse or ambient composition law is assumed.
Empty domains still have assigned ambient maps and impose no identity.
Decoded vectors need not belong to the native physical output image.

Denote this contract by $\mathsf L$. Contract $\mathsf G$ additionally
requires each straight-command domain to be saturated under encoder
fibers: it is the inverse image of a subset of the actual encoded
image. Contract $\mathsf P$ additionally requires a fixed affine update
for every prescribed simultaneous native path on its full all-times
domain. The velocities and duration of each prescribed path are fixed
independently of its starting ray. Contract $\mathsf{GP}$ requires
both properties, including saturation of each full path domain.
Guard-recovery functions are not required to be affine.

Write $\mathfrak F_{\le n,\mathsf C}$ for the corresponding class and

$$
\operatorname{err}(E,\mathcal D)
=\sup_{\zeta\in\mathcal M}\|\mathcal D(E(\zeta))-y(\zeta)\|_2,\qquad
e_{n,\mathsf C}^{\rm aff}(Z)
=\inf_{\mathfrak F_{\le n,\mathsf C}}\operatorname{err}(E,\mathcal D).
$$

The infimum of an empty class is $+\infty$; infinite-error models are
permitted. A finite tolerance is achievable if some model's error is
at most that tolerance. Write $e_n$ when the four values have been
proved equal. Stored dimension, actual affine-hull dimension and
decoder rank are separate notions. The class inclusions are

$$
\mathfrak F_{\le n,\mathsf{GP}}\subseteq
\mathfrak F_{\le n,\mathsf G}\subseteq\mathfrak F_{\le n,\mathsf L},\qquad
\mathfrak F_{\le n,\mathsf{GP}}\subseteq
\mathfrak F_{\le n,\mathsf P}\subseteq\mathfrak F_{\le n,\mathsf L}.
$$

**Definition 1.6 (Scalar parameters).** For the entire source range put

$$
x=k/H,\qquad \tau=\frac Z{4H}>0,\qquad s(x)=\sqrt{x(1-x)}.
$$

The inverse correspondence is

$$
Z=\frac{2\tau}{1+2\tau},\qquad
H=\frac1{2(1+2\tau)}.
$$

Thus $0<\tau<1$ is exactly $0<Z<2/3$, and $\tau=1$ is $Z=2/3$.
The scalar variable $x$ and scalar function $s$ do not rename a control
input. Closed scalar endpoints in this volume concern limits of
explicit functions; the source always has $0<x<1$.

## 2. Exact supplier telescope and inherited bounds

**Theorem 2.1 (Inherited bounded-observable and projection interface).**
For every finite literal model, any fixed affine scalar observable of
$E$ that is bounded on each fixed-height phase torus is independent
of $\beta$. For a finite-error decoder $q=\mathcal D\circ E$, write

$$
\binom ab=(D^{\mathsf T}D)^{-1}D^{\mathsf T}q,\qquad
w=q-D(a,b),\qquad w\perp\operatorname{im}D.
$$

These are bounded affine observables of $E$, independent of $\beta$.
At every interior $k$ and every $\alpha$,

$$
\max_{\beta}\|q-y\|_2^2
=\|w\|_2^2+4|a-A(k)e^{i\alpha}|^2+(|b|+B(k))^2.
$$

Consequently replacement of the decoder by $D(a,0)$ does not increase
error, and every finite-dimensional literal model has error at least

$$
e_*=2\sqrt{ZH}=\sqrt{2Z(1-Z)}.
$$

Supplier justification. These are [M, Theorem 3.4 and Proposition 3.5]
and [O, Theorem 3.3 and Proposition 4.1], with $q$ equal to the present
composed decoder. Their hypotheses are exactly Definition 1.5: arbitrary
current-ray encoders, both offsets, every signed command, and no latent
bound. The proof bounds a finite-dimensional space of observable
functions, not the hidden encoder. The worst-phase identity uses
Lemma 1.4 and actual independent reachability of the two phase circles.
The floor takes the supremum of $4Zk$ through interior heights. It
does not require a state at $H$. These supplier theorems are used as
handwritten premises here. $\square$

**Definition 2.2 (The inherited two-coordinate value on all parameters).**
For $0<\tau<1$ and $t>\tau$ define

$$
\begin{aligned}
v_t(x)&=\sqrt{t-\tau x},\\
\lambda_t&=\frac12\log\frac{t-\tau}{t},\\
f_t(x)&=\sqrt t\,e^{\lambda_t x}
       =t^{(1-x)/2}(t-\tau)^{x/2},\\
\Phi_\tau(t)&=\max_{0\le x\le1}\{s(x)-v_t(x)-f_t(x)\}.
\end{aligned}
$$

Let $T_2(\tau)$ be the unique zero of $\Phi_\tau$ for $0<\tau<1$,
and set $T_2(\tau)=\tau$ for $\tau\ge1$. Thus $T_2$ is defined
throughout the parameter range of the main theorems.

**Theorem 2.3 (Inherited complete two- and three-coordinate comparison).**
For every fixed preparation, every $0<Z<1$ and every contract,

$$
e_{2,\mathsf C}^{\rm aff}(Z)=e_{3,\mathsf C}^{\rm aff}(Z)
=4H\sqrt{T_2(\tau)}.
$$

Each of these values is attained in $\mathsf{GP}$, and the finite
tolerance set in each of the four classes is
$[4H\sqrt{T_2(\tau)},\infty)$. More strongly, every literal model
with at most three coordinates is dominated by an actual radial model
with at most two coordinates. The common squared value is

$$
\inf_{C\ge0,\ \gamma\in\mathbb R}
\sup_{0<k<H}\{4(Ce^{\gamma k}-A(k))^2+4Zk\}.
$$

For $0<\tau<1$, put $T=T_2(\tau)$ and $T_0=(1+\tau)^2/4$.
Then $\tau<T<T_0$. The optimal positive radial profile is uniquely
$f_T$ within that radial family. The function $s-v_T-f_T$ is strictly
concave on $(0,1)$, with unique zero and maximum at a point $x_*$
satisfying

$$
\frac{1+\tau}{2}<x_*<1,\qquad
s(x_*)-v_T(x_*)=f_T(x_*),
$$

$$
\frac{1-2x_*}{2s(x_*)}
+\frac{\tau}{2v_T(x_*)}-\lambda_T f_T(x_*)=0.
$$

The attaining annulus is

$$
E_*(k,\alpha,\beta)=2Hf_T(k/H)e^{i\alpha},\qquad
\mathcal D_*(z)=D(z,0),\qquad
2H\sqrt{T-\tau}<|z|<2H\sqrt T.
$$

Its fibers are the $\beta$ circles at fixed $(k,\alpha)$, and its
actual affine hull is the real plane. Its exact initialization is
$E_*(k_0,0,0)$; its command maps are $e^{\lambda_T a/H}z$ and
$e^{it/2}z$. It recovers height by

$$
\kappa_*(z)=\frac H{\lambda_T}\log\frac{|z|}{2H\sqrt T}.
$$

For $\tau\ge1$, the height encoder $E_{\rm h}(k,\alpha,\beta)=k$
with zero decoder gives the common value $e_*$. It uses $K\mapsto K+a$
and $K\mapsto K$ for the two commands. The full path extensions of
both witnesses use the exact formulas in §8 below.

Supplier justification. The all-competitor two-coordinate reduction is
[M, Theorem 6.4], its root and contact are [M, Theorems 7.4–7.6], and
the annulus, paths and transition are [M, Theorem 8.1, Proposition 8.2,
Theorem 9.2 and Theorem 10.2]. The unrestricted three-coordinate
domination is [M, Theorem 17.2]; its exact values and all four attained
endpoints are [M, Corollaries 18.1–18.2 and Theorem 19.1]. In the
supplier notation $x=k/H$, $c=C/(2H)$, $\lambda=\gamma H$, and
the normalized squared objective is multiplied by $16H^2$. Its literal
$e_n^{\rm aff}$ is the present $e_{n,\mathsf L}^{\rm aff}$. No
restriction on hidden coordinates is added in passing to this notation.
The uniqueness assertion is radial uniqueness, not uniqueness of all
optimal encoders. $\square$

**Definition 2.4 (The exact inherited strict-improvement certificate).**
For $0<\tau<1$, keep $T,x_*,\lambda=\lambda_T,f=f_T,v=v_T$ from
Theorem 2.3. To specify the certificate of [Q, Definitions 4.1 and 4.3],
use distinct names for its perturbation constants:

$$
b_Q=e^{-1}-1,\quad
\psi_Q(x)=1+b_Qx-e^{-x},\quad
\eta_Q=\psi_Q(x_*)/2,\quad a_Q=1-\eta_Q,
$$

$$
R_u^Q(x)=f(x)\bigl[(1+ua_Q)e^{ub_Qx}-u e^{-x}\bigr],\qquad
F_0^Q(x)=(f(x)-s(x))^2+\tau x,
$$

$$
h_Q=f(\psi_Q-\eta_Q),\quad W_Q=2(f-s)h_Q,\quad
m_Q=\eta_Q\min\{T,T-\tau,f(x_*)v(x_*)\},
$$

$$
K_Q=\{x\in[0,1]:W_Q(x)\ge-m_Q\},\qquad
d_Q=T-\max_{K_Q}F_0^Q,
$$

$$
C_Q=2T+\sqrt T,\qquad M_Q=28T+2\sqrt T,\qquad
\varepsilon_Q=\min\left\{\frac12,\frac{m_Q}{2M_Q},
\frac{d_Q}{2(C_Q+M_Q)}\right\},
$$

$$
\mu(\tau)=\min\{m_Q\varepsilon_Q/2,d_Q/2\}.
$$

**Theorem 2.5 (Inherited four-coordinate strict upper bound).** The set
$K_Q$ is nonempty and compact, $d_Q,m_Q,\varepsilon_Q$ are positive,
and

$$
0<\mu(\tau)<\frac{T_2(\tau)-\tau}{8},\qquad
\max_{[0,1]}\bigl((R_{\varepsilon_Q}^Q-s)^2+\tau x\bigr)
\le T_2(\tau)-\mu(\tau).
$$

This very profile has an actual four-real-coordinate $\mathsf{GP}$
realization with full affine hull. For all four contracts,

$$
e_{4,\mathsf C}^{\rm aff}(Z)
\le4H\sqrt{T_2(\tau)-\mu(\tau)}
<4H\sqrt{T_2(\tau)}=e_2(Z)=e_3(Z)
\quad(0<Z<2/3).
$$

Supplier justification. These are [Q, Lemmas 4.4–4.5, Theorem 4.6
and Theorem 7.2], with its $T,\mu$ equal to the present
$T_2(\tau),\mu(\tau)$. Its stored blocks are
$e^{(\lambda+\varepsilon_Q b_Q)x}e^{i\alpha}$ and
$e^{(\lambda-1)x}e^{i\alpha}$; [Q, §§5–6] supply their exact
decoder, guards, initialization and all prescribed paths in the same
native source and metric. The certificate is parameterwise, exact and
positive, without claiming it is the optimal improvement. $\square$

**Definition 2.6 (The inherited fixed-dimension lower certificate).**
For $n\ge0$, let $N=n+1$. For $m\ge0$ and
$u\in\mathbb R^{2m+1}$ set

$$
\mathcal H_m(u)=(u_{p+q+1})_{0\le p,q\le m},\qquad
d_{N,m}=\min_{\operatorname{rank}\mathcal H_m(u)\le N}
\max_{1\le j\le2m+1}\frac{|u_j-\sqrt j|}{\sqrt j}.
$$

For $0<Z<2/3$ put

$$
\rho_0=\sqrt{Z/(4H)}=\sqrt\tau,\qquad
\eta_O=(1-\rho_0)/4,\qquad \rho_O=(1+\rho_0)/2,
$$

$$
M_O=\min\{m\ge0:d_{N,m}\ge\rho_O\},
$$

$$
\Gamma(n,Z)=\frac{16H^2}{2M_O+1}(2\eta_O-\eta_O^2)
\bigl((\rho_0+\eta_O)^2-\rho_0^2\bigr).
$$

**Theorem 2.7 (Inherited uniform lower gap).** The finite minima
$d_{N,m}$ exist, are nondecreasing in $m$, and tend to one. Therefore
$M_O$ is finite and $\Gamma(n,Z)>0$ for $0<Z<2/3$. For every
allowed preparation and every literal model of stored dimension at
most $n$,

$$
\operatorname{err}(E,\mathcal D)^2\ge4ZH+\Gamma(n,Z).
$$

The bound holds on each stronger class by inclusion. The quantities
are precisely [O, Lemma 11.2 and §§11.3–11.4], and the uniform
model quantifiers are [O, Theorem 11.1]. Its $n$ is a real stored
coordinate budget, $N=n+1$ includes the affine constant, and its
$\Gamma$ is in original squared-error units. A feasible finite Hankel
prefix need not have a native realization. No evaluation of its least
index or of these finite minima is supplied here. $\square$

## 3. Spectral family and the three main theorems

**Definition 3.1 (Order-at-most-two scalar family).** Let $\mathcal E_2$
be the complex-valued functions of a real variable of either form

$$
R(x)=c_1e^{\lambda_1x}+c_2e^{\lambda_2x},\qquad
R(x)=(c_0+c_1x)e^{\lambda x},
$$

with arbitrary complex coefficients and exponents. Zero, single-mode,
coincident-root and vanishing-coefficient cases are included. The
minimal order is the least degree of a nonzero constant-coefficient
polynomial $p$ with $p(\partial_x)R=0$: it is zero for $R=0$, one
for a nonzero single exponential, and two for either a distinct pair
with both coefficients nonzero or a confluent profile with $c_1\ne0$.
For $\tau>0$ define

$$
J_\tau(R)=\max_{0\le x\le1}
\left(|R(x)-s(x)|^2+\tau x\right),\qquad
T_4(\tau)=\inf_{R\in\mathcal E_2}J_\tau(R).
$$

The functions in this definition are explicit continuous functions on
the closed scalar interval. The definition does not assert that an
arbitrary competing native encoder is continuous.

**Theorem 3.2 (T1: full-class reduction and strict-improver rigidity).**
Every at-most-four literal model is dominated in original uniform
error by an actual model associated with some $R\in\mathcal E_2$.
Conversely every $R\in\mathcal E_2$ has a lawful realization with at
most four real coordinates. Thus

$$
\bigl(e_{4,\mathsf L}^{\rm aff}(Z)\bigr)^2=16H^2T_4(\tau).
$$

For $0<Z<2/3$, any individual model with error strictly below $e_2(Z)$
has actual affine-hull dimension four and is $\beta$-independent.
After an affine real isomorphism of its actual hull, its encoder is
one of

$$
e^{i\alpha}(e^{\lambda_1x},e^{\lambda_2x})\quad
(\lambda_1\ne\lambda_2),\qquad
e^{i\alpha}(e^{\lambda x},xe^{\lambda x}).
$$

In those coordinates its decoder can be replaced, without increasing
error or changing encoder fibers, by a fixed linear decoder whose value is
$D(2HR(x)e^{i\alpha},0)$. This scalar profile has minimal order two:
both distinct-mode coefficients are nonzero, or the confluent linear
coefficient is nonzero. In particular the original strict improver's
encoder is bounded and continuous; these are conclusions. No such
normal-form assertion is made for non-improvers or for the original
ambient update assignments on empty domains.

**Theorem 3.3 (T2: scalar minimum and actual unguarded attainment).**
For every $\tau>0$, some $R\in\mathcal E_2$ satisfies
$J_\tau(R)=T_4(\tau)$. For all $0<Z<1$,

$$
e_{4,\mathsf L}^{\rm aff}(Z)=e_{4,\mathsf P}^{\rm aff}(Z)
=4H\sqrt{T_4(\tau)},
$$

and both infima are attained by actual models. For $0<\tau<1$ every
scalar minimizer has minimal order two. For any fixed real
$a<T_2(\tau)$, the characteristic roots of all minimal-order-two
profiles with $J_\tau\le a$ are bounded by a finite constant depending
on $a,\tau$. This is vacuous for an empty sublevel; in particular
such sublevels are empty for $\tau\ge1$. Root collisions are allowed,
and no uniform bound on separate exponential coefficients near a
collision is asserted.

**Theorem 3.4 (T3: equal infima and the exact guarded endpoint criterion).**
For every fixed preparation and $0<Z<1$,

$$
e_{4,\mathsf L}^{\rm aff}
=e_{4,\mathsf G}^{\rm aff}
=e_{4,\mathsf P}^{\rm aff}
=e_{4,\mathsf{GP}}^{\rm aff}
=4H\sqrt{T_4(\tau)}.
$$

When $0<Z<2/3$, attainment in $\mathsf G$ is equivalent to attainment
in $\mathsf{GP}$, and occurs if and only if at least one global
minimizer in $\mathcal E_2$ has one of these minimal order-two forms:

1. A confluent profile $(c_0+c_1x)e^{\lambda x}$ with $c_1\ne0$.
2. A distinct pair with at least one $\operatorname{Re}\lambda_j\ne0$.
3. A purely imaginary distinct pair $\lambda_j=i\omega_j$ with
   $|\omega_1-\omega_2|\le2\pi$.

The excluded spectrum for an individual minimal realization is a
purely imaginary distinct pair of separation greater than $2\pi$.
Finding one excluded global minimizer does not exclude another global
minimizer satisfying the criterion.

For $2/3\le Z<1$, all four infima equal $\sqrt{2Z(1-Z)}$ and are
attained by the height/zero-decoder model. Below the transition the
literal and prescribed-path tolerance sets are
$[4H\sqrt{T_4(\tau)},\infty)$. Both guarded tolerance sets contain
every strictly larger tolerance and include the endpoint exactly under
the existential criterion above. The criterion itself does not decide
guarded attainment at any unspecified subtransition parameter.

## 4. Proof 1: local spanning, lawful extension and beta quotient

**Lemma 4.1 (Every open interval spans).** Let $I$ be an open interval
and let $v(k,\sigma)$ take values in a finite-dimensional real or
complex vector space, for $k\in I$ and arbitrary labels $\sigma$.
Suppose that for each displacement $a$ there is one linear map taking
$v(k,\sigma)$ to $v(k+a,\sigma)$ whenever both heights belong to
$I$. Then the values with heights in any nonempty open subinterval
span the same space as all values on $I$. No regularity of $v$ is
required.

Proof. For an open subinterval $J$ let $X(J)$ be its value span.
If two subintervals have the same finite length, translation maps
one span onto the other, while reverse translation is an inverse on
their generating vectors. Their dimensions agree. Let $d_0$ be the
least dimension among finite-length open subintervals and choose one
of length $\ell_0$ with that dimension. Any interval of positive
length less than $\ell_0$ can be translated inside this interval;
inclusion and minimality show that its dimension is $d_0$ too.

Two such short intervals with open overlap have identical spans:
their overlap already has dimension $d_0$ and is contained in both.
A finite chain of overlapping short intervals inside $I$ connects
any two of them, so their spans all coincide. These intervals cover
$I$, and every nonempty open subinterval contains one. Their common
span is therefore exactly the span over $I$. This proof also covers
$d_0=0$ and unbounded $I$. $\square$

**Lemma 4.2 (Actual hull and global extension of lawful height maps).**
Restrict a literal model to affine coordinates on
$\mathscr H=\operatorname{aff}E(\mathcal M)$, of dimension $d$.
Let $F=(1,E)^{\mathsf T}$ and
$X=\operatorname{span}_{\mathbb R}F(\mathcal M)$, so $\dim X=d+1$.
Every nonempty height-command domain spans $X$ in homogeneous
coordinates. Its homogeneous map $T_a$ is invertible on $X$ and
satisfies the local additive representation law. There is a
representation $A_t$ of $(\mathbb R,+)$ on $X$ agreeing with $T_t$
for $|t|<H$ and satisfying

$$
A_tF(k,\alpha,\beta)=F(k+t,\alpha,\beta)
\quad(0<k,k+t<H).
$$

Proof. For the hull restriction choose an affine retraction from the
ambient space to $\mathscr H$, and compose it after each ambient
update restricted to $\mathscr H$. On a lawful encoded state the
update already lands in the image, so the retraction changes no
identity. Restrict the decoder as well. This is [M, Lemma 13.1]; it
retains all offsets even if a partial ambient update did not preserve
the hull on unused vectors.

Homogenization makes each of these affine maps linear. Lemma 4.1,
with $\sigma=(\alpha,\beta)$, implies that every nonempty open
height interval spans $X$. For $|a|<H$, the lawful start interval is

$$
I_a=(\max\{0,-a\},\min\{H,H-a\}).
$$

The identity $T_{-a}T_aF=F$ holds at all its heights, and hence on
$X$; the reverse order holds using $I_{-a}$. Thus $T_a^{-1}=T_{-a}$.
In particular $T_0=I$ on $X$.

If $|a|,|b|,|a+b|<H$, the spread of $\{0,a,a+b\}$ is
$\max\{|a|,|b|,|a+b|\}<H$. The lawful triple
$k,k+a,k+a+b$ therefore has a nonempty open interval of starting
heights. On all those states,
$T_bT_aF=T_{a+b}F$, so Lemma 4.1 gives the operator identity
$T_bT_a=T_{a+b}$ on $X$. Interchanging $a,b$ gives commutation in
the same range.

For real $t$, choose a positive integer $n$ with $|t|/n<H$ and set
$A_t=T_{t/n}^{\,n}$. To verify independence, let $m$ be another
admissible subdivision. Repeated local addition inside
$[-|t|/n,|t|/n]$ gives

$$
T_{t/n}=T_{t/(nm)}^{\,m},\qquad
T_{t/m}=T_{t/(nm)}^{\,n}.
$$

Taking powers shows that both definitions of $A_t$ agree. If
$|t|<H$, the same repeated local addition proves $A_t=T_t$.
For arbitrary $t,u$, use a common sufficiently fine subdivision so
that $t/n,u/n,(t+u)/n$ are in the local range. Their local maps
commute and obey the sum law, whence

$$
A_{t+u}=T_{(t+u)/n}^{\,n}
       =T_{t/n}^{\,n}T_{u/n}^{\,n}=A_tA_u.
$$

This is an extension of the forced lawful maps. For $|t|\ge H$
the original probability domain is empty; its original assigned
ambient map is neither constrained nor identified with $A_t$.
$\square$

**Lemma 4.3 (A lawful beta quotient on the full actual hull).** In the
preceding homogeneous space put

$$
N=\operatorname{span}_{\mathbb R}
\{F(k,\alpha,\beta_1)-F(k,\alpha,\beta_2)\}.
$$

For a finite-error model, quotienting the actual affine hull by $N$
gives a literal model of affine dimension $d-\dim N$, independent of
$\beta$, with the same decoded output. No guard property of that
quotient is asserted.

Proof. The first-coordinate covector $\lambda_0$ annihilates $N$,
so $N$ lies in the direction space of the homogeneous affine slice.
The difference family in this definition satisfies Lemma 4.1, since
the two endpoints of each difference have the same height and each
lawful probability leg acts linearly on their difference. Thus the
differences whose heights lie in any open subinterval already span
$N$.

For a nonempty probability command choose those differences inside
$I_a$. Their images under $T_a$ are again differences at the same
height and $\alpha$. Therefore $T_aN\subseteq N$; the reverse
command gives equality. Every phase command sends a same-$(k,\alpha)$
beta pair to another such pair at $\alpha+t/2$, so its homogeneous
map also preserves $N$, with equality by the negative command.
All decoder rows annihilate $N$ by Theorem 2.1. Hence each nonempty
command descends to a fixed affine map on the quotient and the
decoder factors through it. Empty-domain commands can be assigned
arbitrary quotient maps. Every required literal identity and decoded
value is retained. The quotient image spans the quotient affine hull,
whose dimension is $d-\dim N$. Identifying additional heights could
destroy guard recovery; this quotient is used only in $\mathsf L$.
$\square$

**Proposition 4.4 (Every strict improver has a full beta-independent hull).**
If a model with at most four coordinates has error $\epsilon<e_2(Z)$,
then $d=4$ and $N=0$. Such a model can occur only for $0<Z<2/3$.
All remaining competitors are already dominated by an inherited
attaining $e_2$ model.

Proof. If $d\le3$, Lemma 4.2 gives a literal budget-three model
with the same output, contrary to Theorem 2.3. Thus $d=4$.
If $N\ne0$, Lemma 4.3 gives another contradiction with dimension
at most three. Therefore $N=0$, which says precisely that $E$ itself
is independent of $\beta$. For $Z\ge2/3$, $e_2=e_*$ and Theorem
2.1 excludes a strict improver. A model of error at least $e_2$,
including infinite error, is dominated by the annular or zero
profile of Theorem 2.3. Each is in $\mathcal E_2$ after the
normalization of Definition 1.6. $\square$

## 5. Proof 2: the bounded phase module and its native coefficient

For §§5–7 fix a strict improver with error $\epsilon<e_2(Z)$.
By §4 its encoder is beta-independent, and its actual homogeneous
space has real dimension five. Write $F(k,\alpha)$ for its value.

**Lemma 5.1 (Commuting phase and height actions on the actual space).**
The maps induced by $Q_{2\delta}$ give a representation $V_\delta$
of the abstract circle on $X$, with

$$
V_\delta F(k,\alpha)=F(k,\alpha+\delta),\quad
V_\delta V_\eta=V_{\delta+\eta},\quad
V_0=I,\quad V_\delta^{-1}=V_{-\delta}.
$$

The covector $\lambda_0$ is invariant, and every $A_t$ from Lemma
4.2 commutes with every $V_\delta$.

Proof. Beta independence makes the first formula true. Changing a
real representative of $\delta$ by $2\pi$ gives identical values
on all actual $F$. Products, inverses and the zero-parameter map likewise
agree on these spanning states, so they are operator identities
on $X$. The same argument proves $\lambda_0V_\delta=\lambda_0$.
This is a fixed covector and does not yet assert an affine center.

For a lawful pair of heights,

$$
T_aV_\delta F(k,\alpha)=F(k+a,\alpha+\delta)
                         =V_\delta T_aF(k,\alpha).
$$

The two source orders can have different beta coordinates, which
this encoder forgets. For $|a|<H$ the interval $I_a$ spans $X$ by
Lemma 4.1, proving full operator commutation there. Subdivision in
Lemma 4.2 then proves commutation for all $A_t$. $\square$

**Lemma 5.2 (Finite positive character averages).** If
$\psi_1,\ldots,\psi_b$ are finitely many nontrivial unitary
characters of an abstract abelian group, finite probability
averages can make all their averages tend to zero, while leaving
every trivial character equal to one.

Proof. This is [M, Lemma 6.1], whose finite construction is useful
here. Choose $g_j$ with $\psi_j(g_j)\ne1$. Average with equal
positive weights over the multiset
$\sum_{j=1}^b n_jg_j$, $0\le n_j<N$. The average of any character
$\psi$ is

$$
\prod_{j=1}^b\left(\frac1N\sum_{n=0}^{N-1}\psi(g_j)^n\right).
$$

Every factor has modulus at most one. For $\psi=\psi_j$, its
$j$th factor is
$(1-\psi_j(g_j)^N)/(N(1-\psi_j(g_j)))$, which tends to zero.
If the list is empty, the point mass at the identity suffices.
All operations are finite sums; no measurable group structure is
needed. $\square$

**Proposition 5.3 (Native coefficient and the exact error corridor).**
There is a complex homogeneous row $\ell$ on $X_{\mathbb C}$ with

$$
\ell V_\delta=e^{i\delta}\ell,\qquad
f(k)=\ell F(k,0),\qquad
|f(k)-A(k)|\le\sqrt{\epsilon^2/4-Zk}\quad(0<k<H).
\tag{5.1}
$$

The row is allowed to be zero at this stage. The right-hand side
is real and nonnegative.

Proof. Let $a$ be the useful planar observable from Theorem 2.1
and $z=a_1+ia_2$. Form the complex row space $W$ spanned by the
two real rows of $a$, all their phase translates, and $\lambda_0$.
Each generator is bounded on actual states, since phase translation
permutes all $\alpha$ at each height. On $W$ the quantity

$$
\|h\|_{\rm obs}=\sup_{0<k<H,\ \alpha\in\mathbb T}
|hF(k,\alpha)|
$$

is a genuine finite norm: a row vanishing on actual states vanishes
on their span. Right multiplication by $V_\delta$ gives commuting
invertible isometries of $W$.

For completeness, an eigenvalue of an isometry on a finite complex
normed space has modulus one. A nontrivial Jordan pair would give
$Tu=\lambda u$, $Tv=\lambda v+u$ and
$T^nv=\lambda^nv+n\lambda^{n-1}u$, contradicting bounded iterates.
Thus each isometry is diagonalizable. A common eigenbasis for the
commuting family follows by induction: split into eigenspaces of
a nonscalar member, preserve them by commutation, and continue in
smaller dimension; if every member is scalar there is no split to
make. This is the bounded-module argument of [M, Lemmas 3.2 and
14.2], without the budget-three multiplicity restriction.

Each common eigenrow satisfies $hV_\delta=\chi(\delta)h$ for an
abstract unitary character $\chi$, and hence
$hF(k,\alpha)=\chi(\alpha)hF(k,0)$. Decompose the row of $z$
into its finitely many character components, grouping any equal
characters. Let $\xi(\alpha)=e^{i\alpha}$, and let $\ell$ be the
$\xi$ component, or zero if absent. This defines an actual row
on the whole $X_{\mathbb C}$, with the stated eigenrow identity;
its coefficient is $f(k)$.

At each fixed height Theorem 2.1 gives, for every $\alpha$,

$$
|z(k,\alpha)-A(k)e^{i\alpha}|
\le r_\epsilon(k),\qquad
r_\epsilon(k)=\sqrt{\epsilon^2/4-Zk}.
$$

The radicand is nonnegative because $\epsilon\ge e_*$. Multiply
the error by $e^{-i\alpha}$ and apply Lemma 5.2 to the finite list
of nontrivial characters $\chi\xi^{-1}$. Convexity of the closed
disk of radius $r_\epsilon(k)$ puts each finite average in that
disk. The averages converge to $f(k)-A(k)$, proving (5.1).
The averaging is over actual phase points, so an irregular encoder
has not been integrated. In particular $f$ is uniformly bounded on
$(0,H)$ by $H+\epsilon/2$. $\square$

## 6. Proof 3: full primary blocks, cyclicity and saturation

**Lemma 6.1 (Full phase primary projectors).** The representation
$V$ on the five-dimensional complexification has a finite primary
decomposition

$$
X_{\mathbb C}=\bigoplus_{\chi\in\Lambda}X_\chi.
$$

For a character absent from $\Lambda$, set $X_\chi=\{0\}$.
For $\chi\in\Lambda$, each $V_\delta$ on $X_\chi$ has sole
eigenvalue $\chi(\delta)$,
where $\chi:\mathbb T\to\mathbb C^\times$ is an abstract character.
The full generalized-block projector $\Pi_\chi$ is a finite complex
linear combination of phase maps. Moreover $X_1\ne0$, and

$$
\dim_{\mathbb C}X_\xi=\dim_{\mathbb C}X_{\xi^{-1}}\le2,
\qquad \xi(\delta)=e^{i\delta}.
$$

Proof. The dimension-independent argument of [M, Lemma 15.1] applies
as follows. A commuting complex family has a common eigenvector:
inside a common invariant subspace, take a proper eigenspace of a
nonscalar member when one exists and descend in dimension. Induction
on the quotient by a common eigenline produces a simultaneous
triangular flag. The diagonal functions of the group parameter are
nonzero characters by the representation law. Let $\Lambda$ be
the finite list of distinct characters so obtained.

Choose finitely many $\delta_j$ separating each pair in $\Lambda$.
For each $V_{\delta_j}$, Bezout identities between the relatively
prime powers in its characteristic polynomial, together with
Cayley–Hamilton, give polynomial projectors onto its generalized
eigenspaces. These projectors commute. Their products for the
eigenvalue tuple of a given $\chi$ are pairwise disjoint idempotents
$\Pi_\chi$.

In the triangular flag, a product has a one on exactly the diagonal
positions with that tuple and zero on the other positions. An
idempotent has rank equal to the number of these ones. Thus no
additional nonzero joint piece exists, the projectors sum to the
identity, and the image for $\chi$ has exactly the diagonal
characters $\chi$ for every phase map. This proves the primary
assertion, including possible hidden Jordan parts. The span of all
$V_\delta$ is an algebra, since it contains $I$ and
$V_\delta V_\eta=V_{\delta+\eta}$. Hence each polynomial projector
and its finite products are finite linear combinations of phase
maps.

For a nontrivial $\chi$, choose $\delta$ with $\chi(\delta)\ne1$.
Then $V_\delta-I$ is invertible on $X_\chi$, while
$\lambda_0(V_\delta-I)=0$. Thus $\lambda_0$ annihilates every
nontrivial block. Since $\lambda_0F=1$, a nonzero trivial block
must remain. Reality pairs $X_\xi$ and $X_{\xi^{-1}}$ with equal
dimension; these characters are distinct. Their common dimension
$q_0$ satisfies $1+2q_0\le5$, proving $q_0\le2$. This count
does not assume that the full hidden representation is semisimple.
$\square$

**Proposition 6.2 (The native observable height module fills the hull).**
Let

$$
\mathscr M=\operatorname{span}_{\mathbb C}\{\ell A_t:t\in\mathbb R\},
\qquad q=\dim_{\mathbb C}\mathscr M.
$$

Then $q=2$. For any basis $\ell_1,\ell_2$ of $\mathscr M$, define
$w_j(k)=\ell_jF(k,0)$. The affine map from the original actual
hull to the two complex coordinates

$$
E(k,\alpha)\longmapsto e^{i\alpha}(w_1(k),w_2(k))
$$

is a real affine isomorphism. Its height action is an invertible
complex representation $B_t$ with $w(k+t)=B_tw(k)$ on lawful
heights. A fixed complex row reads $f(k)$ from $w(k)$.

Proof. The row $\ell$ of Proposition 5.3 annihilates every primary
block other than $X_\xi$: on another block choose $\delta$ where
$\chi(\delta)\ne\xi(\delta)$ and invert
$V_\delta-\xi(\delta)I$ there. Since $A_t$ commutes with every
phase map and therefore with its polynomial projectors, $\ell A_t$
has the same support and eigenrow character. Consequently
$q\le\dim X_\xi\le2$.

If $q>0$, choose a basis of this row module. Its invariance under
right multiplication by $A_t$ defines an invertible matrix $B_t$
by

$$
\ell_jA_t=\sum_h(B_t)_{jh}\ell_h.
$$

The additive representation law implies the same law for $B_t$;
the matrices commute. Evaluation on $F$ gives
$w(k+t)=B_tw(k)$ whenever lawful. All basis rows have character
$\xi$, so their values at phase $\alpha$ are $e^{i\alpha}w(k)$.
Writing $\ell$ in this basis gives the fixed scalar row reading
$f$. Thus $e^{i\alpha}w(k)$, as $2q$ real coordinates, has exact
lawful height maps $B_a$, phase maps $e^{it/2}I$, and decoder
$D(f(k)e^{i\alpha},0)$ on its source image. Formula (5.1) and
Lemma 1.4 show that this decoder's error is at most $\epsilon$.
If $q=0$ use the zero profile, with the same error comparison.

The vectors $w(k)$ span $\mathbb C^q$. Indeed a linear combination
of the basis rows vanishing on all $w(k)$ vanishes also at every
phase, hence on all actual $F$, hence as a row. If $q\le1$, the
preceding construction would be a literal model with at most two
real coordinates and error at most $\epsilon<e_2$, contradicting
Theorem 2.3. Therefore $q=2$.

The two rows in $\mathscr M$, their two conjugate rows of character
$\xi^{-1}$, and $\lambda_0$ are independent: eigenspaces for
distinct characters form a direct sum. They exhaust the
five-dimensional complexified dual. Taking real and imaginary
parts, the four native rows are independent on the real direction
space $\ker\lambda_0$. They therefore give a real affine
isomorphism on the slice $\lambda_0=1$. Its restriction to the
original actual hull is precisely the displayed coordinate change.
Thus there is no extra hidden direction beyond the native coordinates.
This is saturation of the original hull, not merely a lower-error
quotient. $\square$

**Lemma 6.3 (Latent boundedness is derived after saturation).** The
function $w$ is bounded on $(0,H)$, and the matrices $B_t$ and
$B_t^{-1}$ are bounded for $t$ near zero.

Proof. Apply Lemma 4.1 on $I=\mathbb R$ to the row-valued orbit
$v(t)=\ell A_t$, with translation implemented by right
multiplication by $A_a$. A basis of $\mathscr M$ can therefore
be chosen from $\ell A_{t_j}$ with $|t_j|<H/8$. In these basis
coordinates,

$$
w_j(k)=f(k+t_j)\qquad(H/8<k<7H/8).
$$

All such coordinates are uniformly bounded by (5.1). For
$0<k\le H/8$, translate by $H/4$ into the central interval and
write $w(k)=B_{-H/4}w(k+H/4)$. For $7H/8\le k<H$, translate
by $-H/4$ and use $B_{H/4}$. Each is a fixed finite matrix, so
$w$ is bounded on the whole open interval. A change to any other
fixed basis preserves boundedness.

Choose two interior heights $k_1,k_2$ with independent vectors
$w(k_1),w(k_2)$, which exist by Proposition 6.2. For sufficiently
small $t$, both translated heights are lawful, and

$$
B_t=[w(k_1+t)\ \ w(k_2+t)]
       [w(k_1)\ \ w(k_2)]^{-1}.
$$

The first matrix is uniformly bounded and the second fixed. This
bounds $B_t$ near zero; applying the same argument to $-t$ bounds
$B_t^{-1}=B_{-t}$. No bound on the original hidden coordinates
was used before proving the affine isomorphism. $\square$

## 7. Proof 4: height classification and removal of discontinuous phases

**Lemma 7.1 (Locally bounded two-complex-dimensional representations).**
For the representation $B_t$ of §6, a fixed complex basis puts it
in one of these forms:

$$
B_t=\operatorname{diag}(\sigma_1(t),\sigma_2(t)),\qquad
\sigma_j(t)=e^{\gamma_jt}\chi_j(t),
\tag{7.1}
$$

or

$$
B_t=e^{\gamma t}\chi(t)(I+tN),\qquad
N\ne0,\quad N^2=0.
\tag{7.2}
$$

Here the $\gamma_j,\gamma$ are real, and the $\chi_j,\chi$ are
abstract unitary characters of $(\mathbb R,+)$. In (7.1) the two
multiplicative characters $\sigma_j$ are distinct. No continuity
of the unitary characters is asserted in this lemma.

Proof. If some $B_t$ has distinct eigenvalues, its two eigenlines
are invariant under every commuting $B_u$. In that fixed basis all
matrices are diagonal. Invertibility and the group law make each
diagonal entry a character $\sigma_j:\mathbb R\to\mathbb C^\times$.
Local bounds for the matrices and their inverses bound
$\log|\sigma_j(t)|$ near zero. This logarithm is additive.

An additive real or complex function $b$ bounded by $K$ on
$(-h,h)$ is continuous at zero: for every positive integer $n$,
$|t|<h/n$ gives $|b(t)|=|b(nt)|/n\le K/n$. Additivity then
gives continuity everywhere, and rational approximation to any real
argument proves $b(t)=tb(1)$. Applying this to the logarithm gives
$|\sigma_j(t)|=e^{\gamma_jt}$. Dividing by this modulus leaves
the abstract unitary character $\chi_j$.

Suppose instead that every $B_t$ has a repeated eigenvalue. Not
all $B_t$ can be scalar, since then the orbit of one state vector
would span only one complex line, contrary to Proposition 6.2.
Choose a nonscalar member. Its nonzero nilpotent Jordan part $N_0$
has $N_0^2=0$. In a Jordan basis the equation of commutation with
$N_0$ says that every commuting matrix has the form $aI+bN_0$.
Thus

$$
B_t=\sigma(t)(I+b(t)N_0),
$$

where $\sigma(t)\ne0$. Uniqueness of these two coefficients and
the group law imply that $\sigma$ is multiplicative and $b$ is
additive. Local matrix and inverse bounds bound $|\sigma|$ above
and away from zero. They also bound the nilpotent entry divided
by $\sigma$, hence $b$. The preceding bounded-additivity argument
gives $\log|\sigma(t)|=\gamma t$ and $b(t)=ct$, with $c\ne0$
because a nonscalar member exists. Set $N=cN_0$ and
$\chi(t)=e^{-\gamma t}\sigma(t)$. This proves (7.2), without
replacing an abstract unit phase by a continuous one. $\square$

**Lemma 7.2 (State and row cyclicity give minimal scalar coefficients).**
Before any continuity conclusion, the native coefficient has either
the form

$$
f(k)=a_1e^{\gamma_1k}\chi_1(k)
     +a_2e^{\gamma_2k}\chi_2(k),\qquad a_1a_2\ne0,
\tag{7.3}
$$

or

$$
f(k)=(a_0+a_1k)e^{\gamma k}\chi(k),\qquad a_1\ne0.
\tag{7.4}
$$

The state encoder itself is affinely isomorphic to the corresponding
two-character state orbit, not just its scalar readout.

Proof. Fix an interior reference height $k_*$. The lawful height
identity gives $w(k)=B_{k-k_*}w(k_*)$ for every interior $k$.
Absorb the invertible $B_{-k_*}$ into a reference vector $v$;
then $w(k)=B_kv$ on that interval.

In the diagonal case write $v=(v_1,v_2)$. State spanning forces
$v_1,v_2\ne0$. Otherwise all actual $w(k)$ would lie in one
coordinate line. Write the scalar readout as a row $(d_1,d_2)$.
Its translates under $B_t$ span the whole two-dimensional dual,
because their pullbacks are exactly the cyclic row module
$\mathscr M$. Therefore $d_1,d_2\ne0$ as well. The products
$a_j=d_jv_j$ are nonzero, proving (7.3). Rescaling coordinates
by $v_j$ normalizes the state orbit to $(\sigma_1(k),\sigma_2(k))$.
The two characters are distinct because one representation member
has distinct eigenvalues. Their restrictions to an open interval
cannot be proportional: a constant ratio there makes the ratio
character one on a neighborhood of zero, and subdivision makes
it one on all of $\mathbb R$.

In the nilpotent case $v,Nv$ must be independent. If $Nv=0$ the
state orbit is a line; if they are dependent, nilpotence again
forces $Nv=0$. In the basis $(v,Nv)$ the state orbit is
$e^{\gamma k}\chi(k)(1,k)$. If $d$ is its scalar row, row
cyclicity forces $dN\ne0$. Since $v,Nv$ are a basis, this is
equivalent to $dNv\ne0$. The scalar coefficient of $k$ is
therefore nonzero, proving (7.4). All changes used here are fixed
complex linear maps after the affine real isomorphism of §6.
They preserve the original fibers. $\square$

**Lemma 7.3 (Cluster subgroup and pointwise removal).** Suppose a
profile of form (7.3) or (7.4) satisfies the corridor (5.1).
Removing every summand with a discontinuous height character
preserves that corridor. In the confluent case discontinuity
removes the entire profile.

Proof. For the diagonal case form the joint cluster set at zero

$$
K=\bigcap_{\delta>0}
\overline{\{(\chi_1(h),\chi_2(h)):|h|<\delta\}}
\subseteq(S^1)^2.
$$

The closures are nested nonempty compact sets, and $K$ is compact
and nonempty. Each point of $K$ can be obtained along a sequence
$h_n\to0$: choose an image point within $1/n$ of it with
$|h_n|<1/n$. If two such sequences have limits $a,b$, their sums
give limit $ab$, and their negatives give inverses. Thus $K$ is
a compact subgroup. Its $j$th coordinate projection is trivial
exactly when $\chi_j$ is continuous at zero. Continuity proves
one implication. If continuity fails, a sequence tending to zero
has that coordinate bounded away from one; compactness of the
joint torus supplies a subsequential limit in $K$ with nontrivial
$j$th coordinate. A character continuous at zero is continuous
everywhere.

For $b=(b_1,b_2)\in K$ choose a realizing sequence $h_n\to0$.
Fix one interior height $k$. Eventually $k+h_n$ is interior, and
the corridor there passes to the limit, since its center $A(k)$
and radius $r_\epsilon(k)$ are continuous. Multiplicativity of
the characters gives

$$
\left|\sum_{j=1}^2a_je^{\gamma_jk}\chi_j(k)b_j-A(k)\right|
\le r_\epsilon(k).
\tag{7.5}
$$

Each coordinate $b\mapsto b_j$ is a unitary character of the
abstract abelian group $K$. Apply Lemma 5.2 to its nontrivial
coordinate characters. Positive finite averages of (7.5) remain
in the same closed disk. Their limit kills exactly the coordinates
whose projection on $K$ is nontrivial, and leaves every trivial
coordinate unchanged. This proves the claimed corridor after
removing exactly the discontinuous summands.

This reasoning is pointwise in $k$. The group and finite averages
can be fixed before choosing $k$, but neither uniform convergence
of $\chi_j(k+h_n)$ in height nor any integration of those
characters is used. The conclusion holds for each interior
height because $k$ was arbitrary.

For (7.4), use the one-coordinate cluster group of $\chi$.
The polynomial factor at $k+h_n$ tends to $a_0+a_1k$. The same
argument therefore averages the whole summand to zero if $\chi$
is discontinuous. $\square$

**Proposition 7.4 (Ordinary continuous spectral normal forms).** Every
character in Lemma 7.2 for a strict improver is continuous. The
encoder and minimal profile consequently have exactly the forms
in Theorem 3.2.

Proof. A continuous unitary character of $\mathbb R$ is
$e^{i\omega t}$ for some real $\omega$. To see the needed fact
directly, choose a continuous argument $\theta$ near zero with
$\theta(0)=0$. Shrink the interval until arguments are small.
The character law makes
$\theta(s+t)-\theta(s)-\theta(t)$ an integer multiple of $2\pi$;
smallness forces it to be zero for sufficiently small $s,t,s+t$.
Local additivity and continuity give $\theta(t)=\omega t$ there
by rational subdivision and density. Subdividing any real $t$
extends the character formula globally.

If either character in (7.3) were discontinuous, Lemma 7.3 would
leave at most one ordinary complex exponential, or zero, with
the same error corridor. One complex coordinate
$e^{(\gamma+i\omega)k}e^{i\alpha}$, with height multiplier
$e^{(\gamma+i\omega)a}$ and phase multiplier $e^{it/2}$,
realizes any such single-mode profile with a fixed linear decoder.
The zero profile has the constant zero realization. Lemma 1.4
and (5.1) would then give a literal budget-two model of error at
most $\epsilon<e_2$, a contradiction. In (7.4) a discontinuous
character would leave zero and gives the same contradiction.
Thus all the used height characters are continuous.

Set $x=k/H$. A diagonal character becomes
$e^{\lambda_jx}$ with $\lambda_j=H(\gamma_j+i\omega_j)$;
distinctness of the characters gives $\lambda_1\ne\lambda_2$.
After the coordinate rescaling in Lemma 7.2 the state is exactly
$e^{i\alpha}(e^{\lambda_1x},e^{\lambda_2x})$. In the confluent
case rescale the second coordinate from $k$ to $x$ to obtain
$e^{i\alpha}(e^{\lambda x},xe^{\lambda x})$. Dividing the scalar
coefficient $f(k)$ by $2H$ gives $R(x)$ with the nonzero
coefficients asserted in Theorem 3.2.

These coefficients imply minimal order two. For a distinct pair,
the equation $R'=\mu R$ would give
$c_1(\lambda_1-\mu)e^{\lambda_1x}
+c_2(\lambda_2-\mu)e^{\lambda_2x}=0$; independence of the two
exponentials and nonzero coefficients would force both distinct
exponents to equal $\mu$. For a confluent profile with nonzero
linear coefficient, $R'=\mu R$ would require the polynomial
$(\lambda-\mu)(c_0+c_1x)+c_1$ to vanish; its linear and constant
coefficients make this impossible. The stated quadratic
annihilators do work, so the order is exactly two.

The affine isomorphism of Proposition 6.2 and these fixed coordinate
changes prove continuity and boundedness of the original encoder
on its full source. For the scalar decoder (5.1) gives no greater
error. This establishes the strict-improver part of T1. Together
with Proposition 4.4 it proves the all-competitor domination
direction, without assuming any spectral ansatz at the outset.
$\square$

**Proposition 7.5 (Continuous spectral family and confluence).** The
diagonal and confluent formulas vary continuously in their finite
complex parameters, in the uniform norm on $[0,1]$. The confluent
family is also a limit of distinct-root profiles, with no required
bound on their separate scalar coefficients.

Proof. Exponentiation and multiplication are jointly continuous on
compact parameter sets and the compact scalar interval, giving
the first assertion. For a direct collision formula, let $h\ne0$
be complex and write

$$
R_h(x)=c e^{\lambda x}
       +d\frac{e^{(\lambda+h)x}-e^{\lambda x}}h
       =\left(c-\frac dh\right)e^{\lambda x}
         +\frac dh e^{(\lambda+h)x}.
$$

The quotient equals $e^{\lambda x}\int_0^x e^{ht}\,dt$, which
converges uniformly on $[0,1]$ to $xe^{\lambda x}$. Thus
$R_h\to(c+dx)e^{\lambda x}$ uniformly. The integral is of an
ordinary continuous exponential. If $d\ne0$, the two displayed
coefficients are unbounded as $h\to0$, even though the profiles
converge. Vanishing coefficients and equal roots can also lower
minimal order. These degenerations explain why neither bounded
individual coefficients nor exclusion of collisions is an
appropriate compactness hypothesis for T2. $\square$

## 8. Proof 5: actual realizations, original errors and all native paths

**Proposition 8.1 (Diagonal and confluent real-coordinate realizations).**
For each $R\in\mathcal E_2$ there is a literal and prescribed-path
model using at most four real coordinates, with exact initialization,
whose squared error is $16H^2J_\tau(R)$.

Proof. For a distinct pair, or any two-term representation, store
the real and imaginary parts of

$$
z_1=e^{\lambda_1x}e^{i\alpha},\qquad
z_2=e^{\lambda_2x}e^{i\alpha},\qquad x=k/H,
\tag{8.1}
$$

and use the one fixed real-linear decoder

$$
\mathcal D_R(z_1,z_2)=D(2H(c_1z_1+c_2z_2),0).
\tag{8.2}
$$

Complex coefficients here act by their real two-by-two multiplication
matrices. Thus neither the encoder dimension nor the affine readout
permission has been enlarged. For every real $a,t$ assign

$$
\mathcal U_a(z_1,z_2)
 =(e^{\lambda_1a/H}z_1,e^{\lambda_2a/H}z_2),\qquad
\mathcal V_t(z_1,z_2)=e^{it/2}(z_1,z_2).
\tag{8.3}
$$

They are fixed real-linear ambient maps. Substitution of $P_a$
and $Q_t$ from Proposition 1.2 proves exact intertwining on every
lawful domain. Negative and zero parameters are included. For
$|a|\ge H$ the source domain is empty, but (8.3) still assigns a
map. A single nonzero mode uses only one complex coordinate;
a zero profile may use zero coordinates in $\mathsf L$ or
$\mathsf P$.

For $R(x)=(c_0+c_1x)e^{\lambda x}$ use instead

$$
z_0=e^{\lambda x}e^{i\alpha},\qquad
z_1=xe^{\lambda x}e^{i\alpha},\qquad
\mathcal D_R(z_0,z_1)=D(2H(c_0z_0+c_1z_1),0),
\tag{8.4}
$$

with maps

$$
\mathcal U_a(z_0,z_1)
=e^{\lambda a/H}(z_0,z_1+(a/H)z_0),\qquad
\mathcal V_t(z_0,z_1)=e^{it/2}(z_0,z_1).
\tag{8.5}
$$

Again these are exactly four real coordinates and real-linear
maps. The identity
$(x+a/H)e^{\lambda(x+a/H)}
=e^{\lambda a/H}(xe^{\lambda x}+(a/H)e^{\lambda x})$
proves the probability update. The phase update follows directly.
All affine offsets in these witnesses are zero, as permitted;
offsets in arbitrary competing models were retained in the lower
argument.

At the arbitrary original preparation $x_0=k_0/H$, the diagonal
initial value is $(e^{\lambda_1x_0},e^{\lambda_2x_0})$, and the
confluent initial value is $(e^{\lambda x_0},x_0e^{\lambda x_0})$.
Their real and imaginary parts are the stored real coordinates.
The preparation increments have $\alpha=\beta=0$, while every
original preparation phase remains in $D$. Any actual current ray
can likewise be initialized by the displayed encoder formula.

For either realization the decoded value on the source is
$D(2HR(x)e^{i\alpha},0)$. The original Gram identity gives

$$
\begin{aligned}
\|\mathcal D_R(E_R(k,\alpha,\beta))-y(k,\alpha,\beta)\|_2^2
 &=4|2HR(x)-A(k)|^2+4Zk\\
 &=16H^2\bigl(|R(x)-s(x)|^2+\tau x\bigr).
\end{aligned}
\tag{8.6}
$$

This identity includes complex-valued $R$ and all ten original
outputs. The function on the right is continuous on $[0,1]$.
Its supremum over the actual interval $(0,1)$ equals its maximum
on $[0,1]$, by taking interior sequences to either endpoint.
No endpoint source ray or encoder extension is needed. This proves
the claimed error identity. The prescribed-path obligation is
verified in Proposition 8.3. $\square$

**Lemma 8.2 (Actual image and full affine hull of the minimal forms).**
For the minimal distinct pair and minimal confluent forms, the
actual images are exactly, respectively,

$$
\mathscr S_{\lambda_1,\lambda_2}
=\{e^{i\alpha}(e^{\lambda_1x},e^{\lambda_2x}):
0<x<1,\ \alpha\in\mathbb T\},
$$

$$
\mathscr S_{\lambda}^{\rm conf}
=\{e^{i\alpha}(e^{\lambda x},xe^{\lambda x}):
0<x<1,\ \alpha\in\mathbb T\}.
$$

Each has real affine hull $\mathbb R^4$. Equality of encoded points
always ignores the whole beta circle; any further identification
is determined exactly by equality of the displayed complex pairs.

Proof. Full reachability of $\mathcal M$ proves the image
descriptions and the statement about beta. The height vectors
$(e^{\lambda_1x},e^{\lambda_2x})$ span $\mathbb C^2$ when the
exponents are distinct: a constant complex dependence would make
$e^{(\lambda_1-\lambda_2)x}$ constant, whose derivative is nonzero.
The vectors $(e^{\lambda x},xe^{\lambda x})$ also span, since
division by the nowhere-zero exponential reduces a putative
dependence to a linear polynomial vanishing on an interval.

The phase replacement $\alpha\mapsto\alpha+\pi$ negates a whole
encoded pair, so its affine hull contains zero. If a real linear
functional vanished on the image, express it as the real part
of a complex linear row on $\mathbb C^2$. Variation of
$e^{i\alpha}$ would force that complex row to vanish on every
height vector. Their complex spanning property makes the row zero.
Thus the real affine hull is full. The exact same images and
fibers describe strict improvers after their affine isomorphism
from §§6–7. $\square$

**Proposition 8.3 (Every prescribed path on its full all-times domain).**
Prescribe integrable velocities $a_c=\dot k,b_c=\dot\chi$ in the
native regularity class on a finite compact interval $[0,T_{\rm p}]$,
independently of the starting ray. Define

$$
\eta(u)=\int_0^u a_c(v)\,dv,\qquad
\Delta=\eta(T_{\rm p}),\qquad
L=\int_0^{T_{\rm p}}b_c(u)\,du,\qquad
C=\int_0^{T_{\rm p}}\eta(u)b_c(u)\,du.
\tag{8.7}
$$

Its exact original guard is

$$
0<k+\eta(u)<H\quad\hbox{for every }u\in[0,T_{\rm p}],
\tag{8.8}
$$

equivalently $k+\min\eta>0$ and $k+\max\eta<H$ on that compact
time interval. On the guard the endpoint is

$$
k'=k+\Delta,\qquad \alpha'=\alpha+L/2,\qquad
\beta'=\beta+(1/2-k/r)L-C/r.
\tag{8.9}
$$

For either realization of Proposition 8.1 a fixed exact affine
path map is

$$
\mathcal W_{\rm p}=e^{iL/2}\mathcal U_\Delta.
\tag{8.10}
$$

Every truncation has this same assertion with its own truncated
integrals and its own full all-times guard. Finite concatenations
retain exact encoding and the same current-state error at every
prefix and intermediate time.

Proof. The displacement $\eta$ is absolutely continuous and
bounded on the compact interval, so its product with integrable
$b_c$ is integrable. The height trajectory is $k+\eta(u)$.
Continuity and attained extrema prove exactly (8.8) and its two
strict extremal inequalities. Endpoint lawfulness alone cannot
replace this domain. Integrate the phase equations from
Proposition 1.2. In particular,

$$
\int_0^{T_{\rm p}}\left(\frac12-\frac{k+\eta(u)}r\right)b_c(u)\,du
=(1/2-k/r)L-C/r,
$$

which gives the true beta endpoint, including its mixed term and
negative sign. This is the source integration of [M, Proposition
9.1], [Q, Proposition 6.2] and [O, §9 and §11.7]. It uses no
splitting limit or extra source control.

Substitution of $k',\alpha'$ into (8.1) or (8.4) gives (8.10)
directly. The beta term in (8.9) is still part of the source;
only this beta-independent encoder forgets it. All coefficients
of (8.10) depend just on the fixed model and prescribed path.
A path with empty domain still has its assigned map. On its
full lawful domain the identity shows preservation of the actual
image. Replacing the upper limits in (8.7) by any earlier time
proves the corresponding identity for every truncation, including
a lawful truncation of a path whose full extension is unlawful.

Two successive relative paths have combined triple

$$
(\Delta_1+\Delta_2,\ L_1+L_2,
 C_1+C_2+\Delta_1L_2).
\tag{8.11}
$$

Indeed the displacement during the second piece relative to the
original start is $\Delta_1+\eta_2$, which contributes
$C_2+\Delta_1L_2$ to the mixed integral. Substituting this triple
into (8.9) agrees with successive source application. The combined
guard is the first full guard and the second full guard from
height $k+\Delta_1$. For both diagonal and shear maps,
$\mathcal U_a\mathcal U_b=\mathcal U_{a+b}$ and these maps
commute with common complex multiplication. Thus (8.10) composes
by the first two parameters, consistently with the retained
source mixed term.

Induction from exact initialization proves each finite prefix.
The truncation identity proves every intermediate point; straight
legs and all their fractional commands are included. At each
point apply (8.6) to the exact current encoded ray. No approximate
decoded output feeds back into an update, so the uniform error
does not accumulate along the history. $\square$

**Corollary 8.4 (Completion of the full-class reduction).** The
identity in Theorem 3.2 holds, and every scalar feasible profile
supplies its claimed literal and prescribed-path upper bound.

Proof. Sections 4–7 dominate each literal competitor by a profile
in $\mathcal E_2$, with no greater original error. Proposition
8.1 realizes every such profile and gives its exact error, and
Proposition 8.3 gives every prescribed path. Taking infima gives
both inequalities in
$e_{4,\mathsf L}^2=16H^2\inf_{\mathcal E_2}J_\tau$; all errors
are nonnegative, so squaring the infimum is legitimate. This
finishes T1. $\square$

## 9. Proof 6: primitive compactness, distribution equations and attainment

**Lemma 9.1 (Limits of bounded scalar primitives and annihilators).**
Let $R_n\in\mathcal E_2$ be uniformly bounded on $[0,1]$. For each
$n$ choose a monic quadratic annihilator $p_n$ of $R_n$, padding
lower orders if necessary. A subsequence has uniformly convergent
primitives

$$
F_n(x)=\int_0^xR_n(t)\,dt\longrightarrow F(x),
$$

and normalized coefficient vectors converging to those of a nonzero
polynomial $p$ of degree at most two. The distribution $u=F'$ on
$(0,1)$ satisfies $p(\partial_x)u=0$.

Proof. For a distinct pair use
$p_n(z)=(z-\lambda_{1,n})(z-\lambda_{2,n})$; for a confluent
profile use $(z-\lambda_n)^2$. A nonzero single exponential may
use $z(z-\lambda_n)$, and zero may use $z^2$. Thus a monic
quadratic always exists without bounding its roots.

Write $p_n(z)=p_{0,n}+p_{1,n}z+z^2$ and divide its coefficient
vector by its Euclidean norm $b_n$. The resulting vectors lie on
the unit sphere in $\mathbb C^3$, viewed as $\mathbb R^6$. A
subsequence converges to a unit vector $(p_0,p_1,p_2)$, defining
$p(z)=p_0+p_1z+p_2z^2\ne0$. Its leading coefficient can be zero.
No bound on the unnormalized coefficients or roots has been used.

Let $|R_n|\le M$ on the scalar interval. Then $F_n(0)=0$,
$|F_n|\le M$ and $|F_n(x)-F_n(y)|\le M|x-y|$. On a countable
dense subset of $[0,1]$, successively extract convergent scalar
subsequences and take a diagonal subsequence. The common Lipschitz
bound makes it uniformly Cauchy: for a prescribed error choose a
finite sufficiently fine net from the dense subset, use convergence
at those finitely many points, and bound the two intervening
differences by the common Lipschitz constant. Hence $F_n$ converges
uniformly to a Lipschitz, in particular continuous, $F$. This
further subsequence retains the coefficient limit.

We use complex distributions as continuous linear functionals on smooth
compactly supported test functions on $(0,1)$, with
$\langle v',\phi\rangle=-\langle v,\phi'\rangle$. Every $R_n$
is an ordinary smooth function. Integration by parts gives

$$
\int_0^1R_n\phi=-\int_0^1F_n\phi'
\longrightarrow-\int_0^1F\phi'
=\langle F',\phi\rangle.
$$

Applying this identity to each fixed derivative of $\phi$ gives
distributional convergence of $R_n$ and all derivatives needed
for a quadratic equation. The normalized polynomial annihilates
$R_n$ too. In its pairing with $\phi$, each of the three scalar
coefficients converges and each corresponding derivative pairing
converges to a finite value. Passing to the limit therefore gives
$p(\partial_x)F'=0$. All integration here involves the explicit
smooth scalar profiles or their continuous primitives, never an
arbitrary original encoder. $\square$

**Lemma 9.2 (Elementary distribution solutions through order two).**
On $(0,1)$, a distribution annihilated by a nonzero constant-
coefficient polynomial of degree at most two is an ordinary
analytic function in $\mathcal E_2$. If the polynomial has
degree at most one, the function has minimal order at most one.

Proof. First, if $v'=0$, choose one smooth compactly supported
$\theta$ with integral one. For any test function $\phi$, the
function $\phi-(\int\phi)\theta$ has integral zero. Its ordinary
primitive, taken from a point to the left of its support, is
smooth and compactly supported inside $(0,1)$: it vanishes both
before and after that support because the total integral is zero.
Consequently $v$ annihilates it as a derivative. It follows that

$$
\langle v,\phi\rangle=\langle v,\theta\rangle\int\phi,
$$

which is the constant distribution. Multiplication of a
distribution by a smooth function obeys the product rule, directly
from its definition on test functions. Thus
$(\partial_x-\lambda)v=0$ implies
$(e^{-\lambda x}v)'=0$ and $v=ce^{\lambda x}$.

A degree-zero nonzero polynomial forces $v=0$. A degree-one
polynomial reduces to the preceding first-order equation. In
degree two factor over $\mathbb C$ and divide out the nonzero
leading coefficient. Suppose
$(\partial_x-\lambda_1)(\partial_x-\lambda_2)v=0$.
Set $w=(\partial_x-\lambda_2)v$. The first-order result gives
$w=ae^{\lambda_1x}$. Therefore

$$
(e^{-\lambda_2x}v)'=ae^{(\lambda_1-\lambda_2)x}.
$$

For distinct roots subtract the ordinary primitive
$a e^{(\lambda_1-\lambda_2)x}/(\lambda_1-\lambda_2)$.
The remaining derivative is zero, so
$v=c_1e^{\lambda_1x}+c_2e^{\lambda_2x}$. For equal roots
subtract $ax$ instead, obtaining
$v=(c_0+c_1x)e^{\lambda x}$. This proves all cases, including
zero coefficients. The formulas extend analytically to both
scalar endpoints and beyond; this is a property of the solution,
not an endpoint assumption. $\square$

**Lemma 9.3 (The limiting error corridor survives degree collapse).**
Suppose $R_n\in\mathcal E_2$ and
$T_n=J_\tau(R_n)\to T<\infty$ for a fixed $\tau>0$.
There is a profile $R\in\mathcal E_2$ with $J_\tau(R)\le T$.
It can be chosen to satisfy the limiting annihilator equation in
Lemma 9.1, including when that equation has lower degree.

Proof. The value at $x=1$ gives $T_n\ge\tau$, so $T\ge\tau$.
The defining inequality for $J_\tau$ gives at every scalar point

$$
|R_n(x)-s(x)|\le\sqrt{T_n-\tau x},\qquad
|R_n(x)|\le\frac12+\sqrt{T_n}.
\tag{9.1}
$$

Thus the profiles have a common bound. Apply Lemma 9.1, then
Lemma 9.2, to obtain $F$ with $F'=R$ as distributions for an
ordinary analytic $R\in\mathcal E_2$. Subtract the ordinary
primitive of $R$ from $F$. Its distributional derivative is zero,
so the preceding lemma makes it constant as a distribution.
Both functions are continuous, hence they differ by that constant
pointwise: a continuous function inducing the zero distribution
is zero, since a nonzero value has a neighborhood detected by a
smooth test function after taking a real component. In particular,

$$
F(b)-F(a)=\int_a^bR(x)\,dx\qquad(0<a<b<1).
$$

For each such interval, (9.1) and the triangle inequality give

$$
\left|\int_a^b(R_n(x)-s(x))\,dx\right|
\le\int_a^b\sqrt{T_n-\tau x}\,dx.
\tag{9.2}
$$

The integral on the left converges through uniform convergence
of the primitives. On the right use

$$
\left|\sqrt{T_n-\tau x}-\sqrt{T-\tau x}\right|
\le\sqrt{|T_n-T|},
$$

valid for the nonnegative radicands. This gives uniform
convergence even when $T=\tau$ and the endpoint radius is zero.
Passing to the limit in (9.2), dividing by $b-a$, and shrinking
intervals about any interior point gives by continuity

$$
|R(x)-s(x)|\le\sqrt{T-\tau x}\qquad(0<x<1).
$$

Continuity of the analytic profile and the scalar center and
radius passes this inequality to $x=0,1$ as well. Thus
$J_\tau(R)\le T$. The equation and its possible degree collapse
were retained throughout this argument. No convergence of
$R_n$ pointwise, of latent encoders, or of update matrices has
been assumed. $\square$

**Theorem 9.4 (Global scalar attainment).** For each $\tau>0$ there
exists $R\in\mathcal E_2$ with $J_\tau(R)=T_4(\tau)$.

Proof. The zero profile makes the infimum finite, and
$J_\tau(R)\ge\tau$ for every profile by the scalar endpoint
$x=1$. Choose a minimizing sequence with
$J_\tau(R_n)\to T_4(\tau)$. Lemma 9.3 supplies $R$ with
$J_\tau(R)\le T_4(\tau)$. The reverse inequality is the
definition of the infimum, proving equality. The subsequence
argument admits escaping roots and collisions; it uses bounded
primitives and normalized polynomial coefficients, not a presumed
compact spectral parameter set. $\square$

**Proposition 9.5 (Strict-sublevel root bound and minimal optimizers).**
For fixed $\tau>0$ and $a<T_2(\tau)$, all minimal quadratic
characteristic roots of profiles with $J_\tau\le a$ are bounded.
For $0<\tau<1$, every minimizer of $J_\tau$ has minimal order two.

Proof. A profile of order zero or one has a literal realization
with at most two real coordinates by Proposition 8.1. Theorem
2.3 and its original normalization imply

$$
J_\tau(R)\ge T_2(\tau)
\quad\hbox{for every profile of order at most one}.
\tag{9.3}
$$

Suppose the claimed root bound fails. Choose minimal-order-two
profiles $R_n$ with $J_\tau(R_n)\le a$ and with maximum root
modulus tending to infinity. Their monic minimal polynomials are
$p_n(z)=z^2+b_{1,n}z+b_{0,n}$. Bounded coefficients would bound
each root: its equation gives

$$
|\lambda|^2\le|b_{1,n}|\,|\lambda|+|b_{0,n}|.
$$

If both coefficients had modulus at most $M$, then for $|\lambda|\ge1$
this would force $|\lambda|\le2M$, with smaller roots already
bounded. Thus, on a subsequence, the coefficient norms tend to
infinity. Normalize as in Lemma 9.1. A further subsequence has
a unit coefficient limit whose quadratic coefficient is zero.
The limiting polynomial is nonzero of degree at most one.

Also extract a convergent subsequence of objective values:
$T_n=J_\tau(R_n)\in[\tau,a]$ converges to some $T\le a$.
If this interval is empty the original sequence cannot exist.
The extraction leaves the polynomial conclusions intact. Apply
the primitive, distribution and corridor argument of Lemmas
9.1–9.3 along that same subsequence. It gives a profile satisfying
the lower-degree annihilator, of order at most one, and
$J_\tau(R)\le T\le a<T_2(\tau)$, contrary to (9.3).
This proves the root bound. It asserts no bound on separate
exponential coefficients near colliding roots, as Proposition
7.5 illustrates.

For $0<\tau<1$, Theorem 2.5 gives a profile with
$J_\tau\le T_2(\tau)-\mu(\tau)<T_2(\tau)$. Hence
$T_4<T_2$, and (9.3) rules out order at most one for every
minimizer. For $\tau\ge1$, $T_2(\tau)=\tau$ and all
$J_\tau\ge\tau$, so every sublevel with $a<T_2$ is empty.
This verifies both the full range and the vacuous cases in T2.
$\square$

**Corollary 9.6 (Actual literal and path minima).** Theorem 3.3 holds.

Proof. Realize a scalar minimizer from Theorem 9.4 by Proposition
8.1 and extend it to all prescribed paths by Proposition 8.3.
Its error is exactly $4H\sqrt{T_4(\tau)}$. The literal lower
bound is Corollary 8.4, and $\mathsf P$ is a literal subclass.
Thus both classes attain this same value. Proposition 9.5
supplies the additional order and root assertions. $\square$

## 10. Proof 7: recoverable approximants and equality of four infima

**Lemma 10.1 (Height recovery from the actual spectral coordinates).**
The confluent realization recovers $x$ as $z_1/z_0$. A diagonal
realization with some $\operatorname{Re}\lambda_j\ne0$ recovers it as

$$
x=\frac{\log|z_j|}{\operatorname{Re}\lambda_j}.
$$

In each case the same model belongs to $\mathsf{GP}$.

Proof. In the confluent realization $z_0=e^{\lambda x}e^{i\alpha}$
never vanishes, and $z_1/z_0=x$ is real on the actual image. In
the diagonal realization $|z_j|=e^{\operatorname{Re}\lambda_j x}$,
giving the displayed formula. Multiply by $H$ to obtain height
$\kappa(z)$. On the actual image, the straight guard is exactly
$0<\kappa(z)+a<H$, and every phase command has full guard. For
each prescribed path the full guard is exactly

$$
0<\kappa(z)+\eta(u)<H\quad(0\le u\le T_{\rm p}),
$$

with its original displacement from (8.7). These subsets have
precisely the original source domains as inverse images, including
empty domains. The affine maps and every truncation and
concatenation identity are already in Proposition 8.3. The guard
function can be nonlinear; only updates and the output decoder
are required to be affine. No height coordinate or external
height input has been added. $\square$

**Proposition 10.2 (Every scalar value is approximated in the combined class).**
For every $R\in\mathcal E_2$ and every positive tolerance above
$4H\sqrt{J_\tau(R)}$, an actual at-most-four $\mathsf{GP}$ model
has error below that tolerance.

Proof. A confluent realization already has height recovery by
Lemma 10.1. In a nonzero diagonal or single-mode representation,
replace the profile by

$$
R_\delta(x)=e^{\delta x}R(x),\qquad \delta\in\mathbb R.
$$

Choose a sequence $\delta\to0$ avoiding the finitely many values
$-\operatorname{Re}\lambda_j$ of the stored nonzero modes.
Each exponent is shifted to $\lambda_j+\delta$, so the same
number of complex coordinates suffices and a stored radius
recovers height. Proposition 8.3 and Lemma 10.1 make every such
model a $\mathsf{GP}$ model with all original full guards.

On $[0,1]$ the profiles $R_\delta$ converge uniformly to $R$.
If $U,V$ are two continuous scalar profiles, the elementary
estimate

$$
\bigl||U-s|^2-|V-s|^2\bigr|
\le |U-V|\,(|U-s|+|V-s|)
$$

shows that this uniform convergence gives
$J_\tau(R_\delta)\to J_\tau(R)$. Their exact original errors
therefore converge as well, proving the asserted strict-tolerance
approximation. For $R=0$, use the one-coordinate height encoder
with zero decoder; its exact error is the same zero-profile
objective and it has all full guards and paths. No perturbation
claim asserts attainment by the unshifted diagonal profile.
$\square$

**Theorem 10.3 (All four infima agree).** For every $0<Z<1$,

$$
e_{4,\mathsf L}^{\rm aff}
=e_{4,\mathsf G}^{\rm aff}
=e_{4,\mathsf P}^{\rm aff}
=e_{4,\mathsf{GP}}^{\rm aff}
=4H\sqrt{T_4(\tau)}.
$$

Proof. Apply Proposition 10.2 to the scalar minimizer from
Theorem 9.4. Every tolerance strictly above the literal optimum
is achieved in $\mathsf{GP}$, so
$e_{4,\mathsf{GP}}^{\rm aff}\le e_{4,\mathsf L}^{\rm aff}$.
The reverse inequality and both intermediate equalities follow
from the two class-inclusion chains in Definition 1.5. This
proves equality of infima while keeping guard attainment
separate. $\square$

## 11. Proof 8: original fibers and the exact guarded-attainment criterion

**Lemma 11.1 (Exact height collisions of the minimal spectral image).**
For a minimal order-two realization, height is constant on each
encoder fiber precisely in the three cases listed in Theorem 3.4.
In the remaining case of a purely imaginary distinct pair,
$\lambda_j=i\omega_j$, different interior heights collide if
and only if

$$
|\omega_1-\omega_2|>2\pi.
$$

Proof. The confluent ratio and the nonzero-real-part radius of
Lemma 10.1 prove height constancy in those cases. It remains to
consider a distinct pair with both real parts zero. At normalized
heights $x,y$, the two pairs in (8.1) agree for suitable phases
$\alpha,\alpha'$ exactly when

$$
e^{i\omega_1(y-x)}=e^{i\omega_2(y-x)}.
\tag{11.1}
$$

Necessity follows by dividing their two coordinate equalities.
For sufficiency, choose
$\alpha'-\alpha=-\omega_1(y-x)$ modulo $2\pi$; (11.1) makes
both coordinates agree. Hence the height difference must satisfy

$$
(\omega_1-\omega_2)(y-x)\in2\pi\mathbb Z.
$$

The smallest positive difference is
$p=2\pi/|\omega_1-\omega_2|$. Two different heights in $(0,1)$
can differ by $p$ exactly when $p<1$. If $p<1$, choose any
$x\in(0,1-p)$ and $y=x+p$. If $p\ge1$, no nonzero integer
multiple of $p$ lies in $(-1,1)$. In particular equality
$|\omega_1-\omega_2|=2\pi$ is allowed: its first possible
collision is across the two absent endpoints, not between
source heights. This proves the exact threshold. At the same
height any equality of encoded points forces equality of
$e^{i\alpha}$, since both stored exponentials are nonzero.
Thus in the good cases the fibers are exactly the full beta
circles at fixed $(k,\alpha)$; in the excluded case the
additional height collisions are exactly those just described.
$\square$

**Lemma 11.2 (Height-fiber criterion for the original guards).** For
any encoder on the present source, recovering every straight
probability guard requires height to be constant on encoder
fibers. Conversely, if height is constant on fibers, every
straight and every prescribed-path full guard is recoverable.

Proof. If rays at $k_1<k_2$ have equal encodings, use the
original signed displacement

$$
a=H-(k_1+k_2)/2.
$$

Then $k_1+a=H-(k_2-k_1)/2$ is strictly between zero and $H$,
whereas $k_2+a=H+(k_2-k_1)/2>H$. Equal encodings would need
different answers to this one straight guard. Thus its domain
is not saturated.

Conversely, constancy defines a well-defined height function
$\kappa$ on the actual image. The inverse images of
$0<\kappa+a<H$ are exactly the original straight probability
domains, and phase domains are full. For a prescribed path use
$0<\kappa+\eta(u)<H$ at every time. Proposition 8.3 identifies
its inverse image with precisely the all-times source domain.
Only these guard subsets are being asserted here; an arbitrary
encoder's affine path updates do not follow from height recovery
alone. For the spectral realizations those updates have already
been constructed. $\square$

**Theorem 11.3 (Existential criterion for an attained guarded optimum).**
For $0<Z<2/3$, the common value in Theorem 10.3 is attained in
$\mathsf G$ if and only if it is attained in $\mathsf{GP}$,
if and only if at least one global scalar minimizer has a
confluent form, a distinct pair with a nonzero real exponent
part, or a purely imaginary distinct pair of separation at
most $2\pi$.

Proof. The inherited strict witness gives the common value
$e_4<e_2$ by Theorem 2.5. Therefore any optimal model in any
of the four contracts is a strict improver. Theorem 3.2 applies
to its actual original encoder. It has full four-dimensional
affine hull, and its coordinate change to the minimal spectral
encoding is an affine isomorphism. In particular it preserves
all encoder fibers, and saturation leaves no unused hidden
direction that could distinguish colliding heights.

Suppose a $\mathsf G$ optimum exists. Its fibers have constant
height by Lemma 11.2. Replace its decoder by the native scalar
decoder furnished by §§5–7, using the same encoder in spectral
coordinates. The replacement cannot increase error. It also
cannot reduce the error below the common optimum, since it
remains an admissible literal model. Thus its scalar profile
satisfies $J_\tau(R)=T_4(\tau)$. It has minimal order two by
Proposition 9.5, and its unchanged fibers have constant height.
Lemma 11.1 forces one of the three stated spectral cases.

Conversely, a scalar global minimizer in any of those cases
has the actual realization of Proposition 8.1. Lemmas 11.1–11.2
give every recovered straight and full path guard, and
Proposition 8.3 gives all required affine path maps. Its error
is exactly the common value. It is a $\mathsf{GP}$ optimum,
and hence a $\mathsf G$ optimum by inclusion. This proves
every direction without using a possibly guard-losing quotient
as the necessity argument. $\square$

**Corollary 11.4 (Tolerance endpoints and the logical scope of the obstruction).**
Below the transition, both guarded classes achieve every finite
tolerance strictly larger than $4H\sqrt{T_4(\tau)}$. Their
finite tolerance sets are either the closed ray starting at
this value, or the open ray, according to Theorem 11.3. A
minimizer with an excluded imaginary spectrum proves failure
of guard recovery for that minimal realization only.

Proof. Proposition 10.2 supplies every strictly larger tolerance,
and Theorem 10.3 excludes smaller tolerances. Theorem 11.3
decides precisely whether the endpoint belongs. Its condition
is existence of at least one good global minimizer. Consequently
nonattainment would require exclusion of every good minimizer;
the presence of one bad minimizer is insufficient. $\square$

## 12. Parameter picture, source-relative result map and unresolved tasks

**Proposition 12.1 (Transition, upper range and model attainment).**
For $\tau\ge1$,

$$
T_4(\tau)=\tau,\qquad
e_{4,\mathsf C}^{\rm aff}(Z)=2\sqrt{ZH}=\sqrt{2Z(1-Z)}
\quad\hbox{for all four contracts}.
$$

The height encoder with zero decoder attains this value throughout
$2/3\le Z<1$. No lawful state maximizes that witness's error,
including at the transition.

Proof. Every scalar profile has $J_\tau\ge\tau$ from $x=1$.
For zero,

$$
s(x)^2+\tau x-\tau=(1-x)(x-\tau)\le0
\qquad(0\le x\le1,\ \tau\ge1).
$$

Its maximum is $\tau$, proving $T_4=\tau$. Multiplying by
$16H^2$ gives squared value $4ZH$. The height encoder is
$E_{\rm h}(k,\alpha,\beta)=K=k$, initialized at $K=k_0$,
with zero decoder. It has exact probability map $K\mapsto K+a$,
phase map $K\mapsto K$, and path map $K\mapsto K+\Delta$.
Its straight and full path guards are exactly $0<K+a<H$ and
$0<K+\eta(u)<H$ at all prescribed times. These formulas also
give every truncation and finite concatenation. It is the
inherited witness of [M, Theorems 10.1–10.2] and [O, Proposition
8.1 and §9], and fits the at-most-four budget in every class.

Its original squared pointwise error is

$$
16k(H-k)+4Zk=4ZH+4(H-k)(4k-Z)<4ZH
\qquad(0<k<H,\ Z\ge4H).
$$

Its supremum is $4ZH$ by interior approach to $H$. At
$Z=4H$, the difference is exactly $-16(H-k)^2$. Thus the
model attains its error infimum without a maximizing source
state, as claimed. This also supplies the upper-range part
of T3 independently of any divergent spectral limit. $\square$

**Corollary 12.2 (Subtransition parameter bounds in original units).**
For every $0<Z<2/3$, write $\tau=Z/(4H)$. Then

$$
\sqrt{4ZH+\Gamma(4,Z)}
\le4H\sqrt{T_4(\tau)}
\le4H\sqrt{T_2(\tau)-\mu(\tau)}
<e_2(Z)=e_3(Z)<1-Z/2.
\tag{12.1}
$$

Equivalently the normalized values obey

$$
\tau+\frac{\Gamma(4,Z)}{16H^2}
\le T_4(\tau)\le T_2(\tau)-\mu(\tau)<T_2(\tau)
<\frac{(1+\tau)^2}{4}.
$$

Here $\Gamma$ and $\mu$ are exactly Definitions 2.6 and 2.4,
with their original supplier quantifiers and no new evaluated
constants. The strict improvements are parameterwise.

Proof. Theorem 2.7 with $n=4$ bounds every literal competitor
below by the first expression. Theorem 2.5 supplies the matching
strict upper certificate in the strongest class. Theorem 10.3
identifies the common infimum, and Theorem 2.3 supplies the
remaining comparisons. The same normalization gives the second
display. All square roots have positive radicands by the cited
results. $\square$

**Proposition 12.3 (Retained lower-budget and limiting facts).** The
source comparisons used here leave the following inherited results
intact. At budgets zero and one the literal and path capacities
are the zero-readout baseline

$$
R_0=\begin{cases}
1-Z/2,&0<Z<2/3,\\
2\sqrt{ZH},&2/3\le Z<1.
\end{cases}
$$

The guarded zero-dimensional class is empty; at budget one the
height/zero-decoder model attains $R_0$ in both guarded classes.
At budgets two and three Theorem 2.3 gives the complete common
value and attained tolerance endpoint. In the subtransition
range the inherited scalar limits are

| Parameter limit | $T_2(\tau)$ | $\lambda_{T_2(\tau)}$ | $x_*$ | $e_2=e_3$ |
|---|---|---|---|---|
| $\tau\downarrow0$ | $1/16$ | $0$ | $1/2$ | $1/2$ |
| $\tau\uparrow1$ | $1$ | $-\infty$ | $1$ | $2/3$ |

No strictly positive additive improvement of $e_4$ over $e_2$
is uniform over the whole interval $0<Z<2/3$.

Supplier justification and consequence. The lower-budget
statements are [M, Theorem 10.1 and Corollary 10.3], and the
limits are [M, Proposition 10.4], transferred to dimension three
by [M, §18]. The inherited four-coordinate comparison has the
same parameterwise limitation [Q, Proposition 8.2]. Directly,
the universal floor and (12.1) give

$$
0<e_2-e_4\le4H\bigl(\sqrt{T_2(\tau)}-\sqrt\tau\bigr)
\longrightarrow0\qquad(\tau\uparrow1).
$$

This uses the displayed inherited scalar limits and does not
evaluate $T_4$ at any subtransition parameter. The limits
$Z\to0,1$ do not add their support-degenerate ray spaces; at
$Z=0$ the positive middle reference is lost, and at $Z=1$
there is no open height interval. $\square$

**Definition 12.4 (Result and source map).** The following table locates
the mathematical obligations and separates inherited interfaces from
the deductions in this volume.

| Result | Present declarations | Source dependence and role |
|---|---|---|
| Native rays, arbitrary preparation, all signed domains and Gram weights | 1.1–1.6 | [M, §§1–2], [Q, §§1–2], [O, §§1–2]; the native bridge is reconstructed explicitly |
| Bounded-observable erasure and exact worst-beta residual | 2.1 | [M, Theorem 3.4 and Proposition 3.5], [O, Theorem 3.3 and Proposition 4.1]; permits arbitrary hidden coordinates |
| Exact budgets two and three, all four attained endpoints | 2.2–2.3 | [M, Theorems 6.4, 7.4–7.6, 8.1, 9.2, 10.2, 17.2 and 19.1, Corollaries 18.1–18.2]; reused with the same parameter map |
| Parameterwise strict four-coordinate upper certificate | 2.4–2.5 | [Q, §4 and Theorem 7.2], with its actual image and path realization in §§5–6 |
| Model-uniform fixed-dimension lower certificate | 2.6–2.7 | [O, Theorem 11.1 and §§11.2–11.4]; the finite relaxation is not a native-realizability converse |
| Proof 1: every local interval spans, lawful subdivision and beta quotient | 4.1–4.4 | Hull restriction from [M, Lemma 13.1]; the local-span and extension argument gives strict four-dimensional beta independence using the inherited plateau |
| Proof 2: native observable coefficient | 5.1–5.3 | Bounded-module argument of [M, Lemmas 3.2 and 14.2] and positive averages of [M, Lemma 6.1], applied without their budget-three multiplicity count |
| Proof 3: complete primary blocks, row module and actual saturation | 6.1–6.3 | Dimension-independent projectors of [M, Lemma 15.1], expanded on a homogeneous space of dimension five; new saturation and derived latent bounds |
| Proof 4: locally bounded height representation and character removal | 7.1–7.5 | Full two-complex-coordinate classification, state and row cyclicity, pointwise cluster averaging, ordinary normal forms and confluence |
| Proof 5: actual spectral models and every prescribed path | 8.1–8.4 | New complex diagonal/confluent witnesses; native path interface [M, Proposition 9.1], [Q, §6], [O, §9 and §11.7] is kept intact |
| Proof 6: scalar attainment and strict-sublevel root bound | 9.1–9.6 | Bounded primitives, normalized annihilators, distribution equations, degree collapse and endpoint corridors; no parameter compactness premise |
| Proof 7: equality of the four infima | 10.1–10.3 | Height recovery and small real spectral shifts supply actual combined-contract approximants |
| Proof 8: necessary and sufficient guarded endpoint | 11.1–11.4 | Saturation preserves original fibers; exact imaginary separation threshold and existential quantifier over global minimizers |
| Parameter bounds and transition | 12.1–12.3 | Combines the three suppliers with the new reduction and attainment, without evaluating the subtransition minimum |

The contribution relative to [M], [Q] and [O] is the unrestricted
order-two spectral reduction and rigidity of every strict improver,
including elimination of discontinuous height phases, global scalar
minimum existence, equality of the four budget-four infima and the
exact remaining guarded-attainment condition. The two-coordinate
root, three-coordinate plateau, existing strict improvement and
fixed-dimension gap retain their credited sources. Their statements
are handwritten premises, not consequences of publication status.

The general tools are finite-dimensional affine homogenization,
commuting representations and invariant flags, Bezout primary
projectors and Cayley–Hamilton, compactness in finite-dimensional
Euclidean spaces, elementary bounded additivity, positive finite
character averages, and ordinary real/complex calculus. The forms
of local spanning, cluster removal, primitive compactness and
distributional ODE solution needed here are proved explicitly.
No external translation-space regularity theorem is a premise.
The source-relative classification is repo-derived handwritten
mathematics; no worldwide originality or exhaustive literature
claim is made.

**Openproblem 12.5 (Exact subtransition minimax evaluation).** For every
$0<\tau<1$, determine the value of $T_4(\tau)$ by a globally
justified exact formula, or a root/contact/global-feasibility
description that actually determines it. The expression
$\min_{\mathcal E_2}J_\tau$ is an exact full-class variational
characterization and existence theorem, not this evaluation.
Determine the global minimizing spectra and every asserted
parameter-regime boundary, including distinct, confluent, real,
complex and purely imaginary possibilities. A stationary point
or an optimum within a selected real-exponential subfamily does
not settle this problem.

**Openproblem 12.6 (Existence of a guarded scalar minimizer).** For each
$0<\tau<1$, decide whether the set of all global minimizers
contains at least one of the three good spectral types in
Theorem 11.3. Neither guarded attainment nor guarded
nonattainment throughout that interval follows from the present
criterion. To prove nonattainment one must exclude every good
global minimizer, not merely exhibit one bad optimum. Scalar
attainment alone and the guarded approximation sequence do not
answer this existential question.

**Remark 12.7 (Unchanged model and research boundaries).** These results
concern current rays on the full open positive support, with the
original two signed real controls and all finite lawful histories.
Retained lifts, history encoders, external height inputs, endpoint
rays, a smaller command menu or a finite-horizon replacement are
different models. There is no assumed regularity of competing
encoders; the continuous normal forms are conclusions only for
strict improvers. Empty-domain ambient maps remain unconstrained
in the original model. The fixed covector, derived primary
decomposition and actual-hull saturation do not classify all
finite affine factors.

Guard recovery concerns subsets of the actual encoded image;
it imposes no off-image guard behavior or affine inverse.
The full all-times path guard remains distinct from an endpoint
test. The explicit witnesses use noninjective encoders and
decoded vectors outside the native output image. Requiring
injection or physical decoded outputs would require its own
upper-bound analysis. All preparation rotations, original norm
weights and affine-offset permissions remain present.

The fixed-dimension positive lower certificate is inherited,
and does not become a sharp dimension rate or an effective
algorithm here. No general dimension-parity law, general
higher-dimensional attainment classification, or result about
the separate original finite-hidden-$N$ alternative is supplied.
That alternative still lacks a proved identification of its
objective and admissible realizations with this affine problem.
Exact-real initialization and continuation provide no finite-bit,
noise, conditioning, acquisition, runtime, physical-implementation,
training or empirical machine-learning conclusion. The scoped
theorems do not complete the broader research objective.

## 追加锚（本行以下为增补区）
