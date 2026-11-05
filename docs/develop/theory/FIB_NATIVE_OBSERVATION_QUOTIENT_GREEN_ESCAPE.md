# Native observation quotient, hidden Green harmonics and attractive response

> This reference volume uses the `generic-v1` theorem/proof shape. Its
> published text is preserved; extensions and corrections belong after the
> final append anchor. The proofs are ordinary mathematical arguments, not
> Lean-kernel-certified declarations.

## 1. The same source and the task-dependent quotient

**Definition 1.1 (native source and supplier notation).** Let [N] be
[Auric FIB atom probability, phase transport and holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md),
[B] its [observation and purity continuation](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY_CONTINUATION.md),
and [G] [Native two-control Green stability](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md).
Fix the double wall of these sources:

$$
0<Z<1,
\qquad r=1-Z,
\qquad h=r/2,
\qquad X=Y=h,
\qquad 0<k<h.
\tag{1.1}
$$

In mode order $(0,1,2,3,13)$ the probability vector is
$(k,h-k,Z,h-k,k)$. Fix an arbitrary preparation height in $(0,h)$
and arbitrary preparation phases. The phase convention remains
$\psi_s=\sqrt{p_s}\,e^{-i\theta_s}$. If $u_0,v_0$ are the grouped
phase increments, use exactly [G, Definition 4.1]'s torus coordinates

$$
\alpha=u_0-v_0\pmod{2\pi},\qquad
\beta=u_0\pmod{2\pi},\qquad
(u_0,v_0)=(\beta,\beta-\alpha).
\tag{1.2}
$$

This is an integer unimodular coordinate change. Each displayed phase has
period $2\pi$; neither is replaced by a doubled relation angle. The original
current-ray manifold, including all reachable heights, is

$$
\mathcal M=(0,h)\times\mathbb T_\alpha\times\mathbb T_\beta,
\qquad \mathbb T=\mathbb R/(2\pi\mathbb Z).
$$

[N, Theorem 8.2] supplies exact finite native histories reaching its points
from the fixed preparation. This statement concerns individual rays, not
preparation of functions on $\mathcal M$.

After calibrating only the fixed preparation rotations, the bottom
coherence is $z=\sqrt{k(h-k)}e^{i\alpha}$, and the middle-reference
coherence is $w=\sqrt{Zk}e^{i\beta}$, as in [B, Proposition 10.4]. The
four bottom edges give $z,z,\overline z,\overline z$, with their original
fixed rotations and factor two in the raw real outputs. Calibration does
not equate distinct preparation phases.

**Definition 1.2 (complete partial commands and the supplied quotient).**
A relative command is an absolutely continuous or piecewise $C^1$ path
$(a(t),b(t))$, starting at zero, with the finite variation required in
[N, Definitions 3.1 and 9.1]. Write

$$
A=a(T),\quad B=b(T),\quad K=\int_0^T a\,db,
\quad m=\min_t a(t),\quad M=\max_t a(t).
$$

It is legal at the current height $k$ exactly when

$$
k+m>0,\qquad k+M<h.
\tag{1.3}
$$

The endpoint, in the coordinates (1.2), is

$$
(k,\alpha,\beta)\longmapsto
\left(k+A,\alpha+B/2,
\beta+(1/2-k/r)B-K/r\right).
\tag{1.4}
$$

The base behavioral quotient supplied by [B, Theorems 10.5--10.6] is

$$
\pi:\mathcal M\longrightarrow\mathcal B=(0,h)\times\mathbb T,
\qquad \pi(k,\alpha,\beta)=(k,\alpha).
\tag{1.5}
$$

It is the smooth quotient by the free common-increment circle. For the
bottom-output task, two states have identical outputs after every common
command, including refusal, if and only if their images in (1.5) agree.
The quotient update is $(k,\alpha)\mapsto(k+A,\alpha+B/2)$ on exactly
(1.3). Height is a current coordinate; the current bottom coherence alone
still has the reflection ambiguity $k\leftrightarrow h-k$.

For commands $\gamma$ then $\delta$, the full signatures compose as

$$
\begin{aligned}
A''&=A+A',&B''&=B+B',&K''&=K+K'+AB',\\
m''&=\min(m,A+m'),&&&M''&=\max(M,A+M').
\end{aligned}
\tag{1.6}
$$

Thus forgetting $K$ on the base does not permit forgetting the extrema.
An out-and-back height excursion can have the identity endpoint and a
proper lawful domain. Adding the reference output $w$ changes the task:
$|w|^2/Z=k$, its argument gives $\beta$, and $z$ gives $\alpha$.
The original two fields are

$$
P=\partial_k,\qquad
Q=\tfrac12\partial_\alpha+c(k)\partial_\beta,
\qquad c(k)=\tfrac12-k/r.
\tag{1.7}
$$

No independent hidden-phase actuator, height reset or mean selector is
included. An everywhere lawful height translation is not one of these
commands.

**Definition 1.3 (one fixed added operator contract).** Choose
$I=(l,u)\Subset(0,h)$, put $d=u-l$, and fix $\varepsilon>0$. Throughout,

$$
\Omega=I\times\mathbb T^2,\qquad
D=I\times\mathbb T,\qquad
\mu=dk\,d\alpha\,d\beta,\qquad \nu=dk\,d\alpha,
\tag{1.8}
$$

with unnormalized angular measures. Use the constant density one and
covariance $A_\varepsilon=\operatorname{diag}(\varepsilon^2,1)$ of
[G, Definition 4.1]. Let

$$
T[f]=\int_\Omega\bigl(\varepsilon^2|Pf|^2+|Qf|^2\bigr)d\mu,
\qquad
\mathcal F=\overline{C_c^\infty(\Omega)}^{(\|\cdot\|_2^2+T)^{1/2}}.
\tag{1.9}
$$

Phases are periodic; compact support here concerns the open height interval.
The nonnegative selfadjoint operator is the form operator

$$
\begin{aligned}
D(L)&=\{f\in\mathcal F:\ \exists F\in L^2(\mu),\
 T(f,v)=\langle F,v\rangle\text{ for every }v\in\mathcal F\},\\
Lf&=F,\qquad L=-(\varepsilon^2P^2+Q^2)_{F,\Omega}.
\end{aligned}
\tag{1.10}
$$

Inner products are linear in the first slot. This is the horizontal
Dirichlet domain, not an asserted isotropic $H^1_0(\Omega)$ domain.
The clock is $H_t=e^{-tL}$, with instantaneous control covariance
$2A_\varepsilon\,dt$. Killing occurs on first height exit from $I$.
For deterministic commands constrained to this cylinder, (1.3) is
strengthened to $k+m>l$, $k+M<u$; this does not redefine the original
guard on $\mathcal M$.

Fix one original source point $o=(k_o,\alpha_o,\beta_o)\in\Omega$ and set

$$
\Gamma_o(q)=\int_0^\infty p_t^\Omega(o,q)\,dt,\qquad
V_o[f]=\int_\Omega\Gamma_o|f|^2d\mu,\qquad q_g[f]=T[f]-gV_o[f].
\tag{1.11}
$$

[G, Propositions 2.1--2.2] supply a positive smooth heat kernel, a positive
spectral gap, compact free resolvent, and a positive Green field smooth and
finite off $o$, integrable on $\Omega$, with
$\int\Gamma_o L\varphi\,d\mu=\varphi(o)$ on the compact smooth core.
Its value at $o$ is infinite. All field comparisons below use this field,
this pole, this density, these boundaries and this clock unless a different
source is explicitly declared. Diffusion, killing, attraction and the
Hilbert space of amplitudes are added mathematical structure.

## 2. Free descent includes the closed domains

**Theorem 2.1 (the native base reduces the fixed free family).** Define

$$
\begin{aligned}
(Jv)(k,\alpha,\beta)&=(2\pi)^{-1/2}v(k,\alpha),\\
(J^*f)(k,\alpha)&=(2\pi)^{-1/2}\int_{\mathbb T}f(k,\alpha,\beta)d\beta,\\
\Pi f=JJ^*f&=\frac1{2\pi}\int_{\mathbb T}f(k,\alpha,\beta')d\beta'.
\end{aligned}
\tag{2.1}
$$

Here $J:L^2(D,\nu)\to L^2(\Omega,\mu)$ is an isometry, and $\Pi$ is
its orthogonal range projection. Let

$$
\overline T[v]=\int_D
 \left(\varepsilon^2|\partial_kv|^2+\tfrac14|\partial_\alpha v|^2\right)d\nu,
\qquad
\overline{\mathcal F}=
\overline{C_c^\infty(D)}^{(\|\cdot\|_2^2+\overline T)^{1/2}},
\tag{2.2}
$$

and let $\overline L$ be its form operator. Then

$$
\begin{gathered}
\Pi\mathcal F\subset\mathcal F,\qquad
\mathcal F\cap\operatorname{Ran}J=J\overline{\mathcal F},\qquad
T[Jv]=\overline T[v],\\
D(L)\cap\operatorname{Ran}J=J D(\overline L),\qquad
LJv=J\overline Lv,\qquad
H_tJ=J e^{-t\overline L}.
\end{gathered}
\tag{2.3}
$$

The base form domain is the ordinary first Sobolev space with zero height
trace and periodic angle. In the normalized basis

$$
e_{jm}(k,\alpha)=\sqrt{2/d}\sin\frac{j\pi(k-l)}d\,
\frac{e^{im\alpha}}{\sqrt{2\pi}},
\qquad
\lambda_{jm}=\varepsilon^2(j\pi/d)^2+m^2/4,
\tag{2.4}
$$

where $j\ge1$ and $m\in\mathbb Z$, its form domain is exactly
$\sum\lambda_{jm}|v_{jm}|^2<\infty$ and its operator domain is exactly
$\sum\lambda_{jm}^2|v_{jm}|^2<\infty$.

For bounded Borel base observables $b$, without the Hilbert normalization,

$$
H_t(b\circ\pi)=\left(e^{-t\overline L}b\right)\circ\pi.
\tag{2.5}
$$

This includes the same height survival event. It determines all finite-time
joint laws of base observations of the killed free diffusion, with an
absorbing cemetery state. Original guarded deterministic commands also act
on this same base by (1.3)--(1.6). For starting states in $\Omega$,
adjoining these free base laws to the original bottom-output/refusal task
therefore leaves its behavioral equivalence exactly equality under $\pi$.

Proof. Hidden translations preserve $\mu$, the smooth core, $P$ and $Q$.
Averaging them gives $\Pi$ on the core. Differentiation commutes with this
average, and Jensen gives $T[\Pi f]\le T[f]$. It consequently extends
continuously to $\mathcal F$. On core functions, integration in $\beta$
gives
$T(\Pi f,(1-\Pi)g)=0$. Passing to the closure preserves this orthogonal
form splitting.

The isometry and the energy identity for $J$ follow by integration over a
circle of length $2\pi$. If $f=\Pi f\in\mathcal F$, average a core
sequence converging to $f$. The averaged sequence equals $Jv_n$ for
$v_n\in C_c^\infty(D)$, and its form convergence is exactly that of
$v_n$ in (2.2). This proves the equality of form domains in (2.3), including
the reverse inclusion. Since $\varepsilon$ is fixed and positive, (2.2)
is equivalent to the usual first Sobolev norm; approximation by periodic
smooth functions with zero height trace gives the stated Sobolev domain.
Sine and circle Fourier expansion then gives (2.4), first on a dense smooth
class and then by closure and Parseval. Diagonal form representation gives
the displayed operator domain, so no differential-expression-only domain
identification is being used.

If $v\in D(\overline L)$, test the full form against any
$w\in\mathcal F$. Form orthogonality eliminates $(1-\Pi)w$, and
$T(Jv,w)=\langle J\overline Lv,w\rangle$. Thus $Jv\in D(L)$ with the
claimed operator value. Conversely, if $Jv\in D(L)$, testing against the
orthogonal form component shows $LJv\in\operatorname{Ran}J$, and testing
against $J\overline{\mathcal F}$ gives $v\in D(\overline L)$.
The variational resolvent equation splits in the same way. Uniqueness and
spectral calculus therefore give the semigroup identity and the fact that
$\Pi$ reduces $L$. These are applications of closed-form representation
and reducing-subspace theory, as in Teschl [T, Theorem 2.13 and Lemma 2.24].

For a bounded Borel $b$, finite volume puts $b$ and $b\circ\pi$ in
their respective $L^2$ spaces. The Hilbert semigroup identity therefore
already gives (2.5) almost everywhere. For $t>0$ both sides have smooth
interior representatives, by the supplied full heat smoothing and the base
series (2.4), so equality holds everywhere. Their positive kernels determine
the same base transition probabilities. In particular $b=1$ gives the same
survival probability; the base kernel kills precisely at the height faces.
Iteration with intermediate bounded base tests proves the finite-time
joint-law assertion, including the cemetery state. This argument obtains
the Borel law from the closed-domain identity. Equal base coordinates
therefore remain sufficient for the enlarged free task; necessity already
follows from the retained native task in [B, Theorem 10.6].

The corresponding explicit smooth diffusion is

$$
dK_t=\sqrt2\varepsilon\,dB_t^1,\qquad
d\alpha_t=2^{-1/2}\,dB_t^2,\qquad
d\beta_t=\sqrt2c(K_t)\,dB_t^2,
\tag{2.6}
$$

with independent real Brownian motions, phases wrapped with period $2\pi$,
and killing at $\tau_I=\inf\{t:K_t\notin I\}$. Its generator before
killing is $\varepsilon^2P^2+Q^2$; $Qk=0$ gives zero Itô correction.
The projection has generator
$\varepsilon^2\partial_k^2+\tfrac14\partial_\alpha^2$, and its killing
time is exactly the same $\tau_I$. The smooth coefficients extend past
$\overline I$, so the stopped stochastic equation is well posed; the
Dirichlet realization of its symmetric generator is (1.10). This is the
same killed-process correspondence used in [G, Proposition 6.1], now
retaining $\alpha$. It gives the explicit killed-process realization of
the already established identity (2.5). The covariance clock in (2.6) is
unchanged. Brownian sample paths are not declared admissible
finite-variation native histories. $\square$

**Definition 2.2 (explicit base heat and Green).** In this theorem's
normalization the base heat density is

$$
\begin{aligned}
\overline p_t((k_o,\alpha_o),(k,\alpha))
&=h_t^I(k_o,k)\,s_t(\alpha-\alpha_o),\\
h_t^I(k_o,k)&=\frac2d\sum_{j=1}^\infty
 e^{-\varepsilon^2(j\pi/d)^2t}
 \sin\frac{j\pi(k_o-l)}d\sin\frac{j\pi(k-l)}d,\\
s_t(a)&=\frac1{2\pi}\sum_{m\in\mathbb Z}e^{-m^2t/4}e^{ima},\\
\overline\Gamma_{\pi o}(x)&=\int_0^\infty\overline p_t(\pi o,x)dt.
\end{aligned}
\tag{2.7}
$$

The heat series and their derivatives converge locally uniformly for
$t>0$, by their exponential coefficients. The Green integral, rather than
an unjustified pointwise rearrangement of a double resolvent series, fixes
its positive representative. It is the unit-source Green kernel for
$\overline L$ relative to $\nu$. The height gap
$\varepsilon^2\pi^2/d^2>0$ makes its total mass finite.

## 3. Green marginal, source smearing and restricted energy

**Theorem 3.1 (exact hidden-circle marginal).** For the same original pole,

$$
\int_{\mathbb T}p_t^\Omega(o,(k,\alpha,\beta))d\beta
 =\overline p_t(\pi o,(k,\alpha)),
\tag{3.1}
$$

and, with nonnegative integral representatives,

$$
\int_{\mathbb T}\Gamma_o(k,\alpha,\beta)d\beta
 =\overline\Gamma_{\pi o}(k,\alpha).
\tag{3.2}
$$

The identity holds as an extended pointwise integral and in $L^1(D)$.
In particular the conditional average and the integral are different:

$$
W_o(k,\alpha):=\frac1{2\pi}\int_{\mathbb T}\Gamma_o(k,\alpha,\beta)d\beta
 =\frac{\overline\Gamma_{\pi o}(k,\alpha)}{2\pi}.
\tag{3.3}
$$

For every $v\in\overline{\mathcal F}$ the same-field restriction is

$$
V_o[Jv]=\int_D W_o|v|^2d\nu,
\qquad
q_g[Jv]=\overline T[v]-g\int_D W_o|v|^2d\nu.
\tag{3.4}
$$

Uniformly smearing the original source along its hidden circle produces
another full-space field, namely

$$
\frac1{2\pi}\int_0^{2\pi}
 \Gamma_{(k_o,\alpha_o,\beta_o+s)}(k,\alpha,\beta)ds
 =W_o(k,\alpha).
\tag{3.5}
$$

Its source is $\delta_{(k_o,\alpha_o)}\otimes d\beta/(2\pi)$, not the
original point mass $\delta_o$.

Proof. Integrate the left kernel against a bounded base test and use (2.5).
This gives (3.1) almost everywhere; both densities are smooth in the
interior for $t>0$, and the hidden circle is compact, so equality holds at
every base point. Tonelli gives (3.2) as an extended identity. Integrating
again in $\alpha$ gives the already supplied [G, Proposition 6.1] value

$$
\int_{\mathbb T^2}\Gamma_o(k,\alpha,\beta)d\alpha d\beta
 =\varepsilon^{-2}G_I(k_o,k),\qquad
G_I(a,k)=\frac{(\min(a,k)-l)(u-\max(a,k))}{d}.
\tag{3.6}
$$

One can obtain this pointwise version directly from the smooth heat
marginal and Tonelli; its right side is finite at every interior height.
Its height integral is $(k_o-l)(u-k_o)/(2\varepsilon^2)$, proving the
claimed $L^1$ statement. At the base pole $\overline\Gamma$ is infinite:
the one-dimensional interior height diagonal and the circle diagonal each
have order $t^{-1/2}$ in (2.7). This does not make $\Gamma_o$ infinite at
other points of that hidden fiber; [G, Proposition 2.2] says it is finite
there. All finite witnesses below stay away even from the source height.

Formula (3.4) follows from $|Jv|^2=|v|^2/(2\pi)$ and Tonelli. Its
finiteness on the full form domain follows from [G, Proposition 4.3], whose
hypotheses and constants are retained in Definition 3.2 below; weighted
polarization gives the corresponding sesquilinear identity. Hidden
translation symmetry of the free form and its heat kernel gives
$\Gamma_{(k_o,\alpha_o,\beta_o+s)}(k,\alpha,\beta)
=\Gamma_o(k,\alpha,\beta-s)$. Averaging proves (3.5), including its
normalization. Testing against $L\varphi$ gives the declared smeared source.
Thus source smearing has been identified by a correspondence, not silently
substituted for the point source. $\square$

**Definition 3.2 (strict attractive realizations and their domains).**
Retain the sufficient constant $C_H>0$ and, for each fixed $\varepsilon$,
the finite $B_\varepsilon\ge0$ of [G, Proposition 4.3]:

$$
V_o[f]\le\frac{2rC_H}{\varepsilon^2}T[f]
             +B_\varepsilon\|f\|_2^2
\qquad(f\in\mathcal F).
\tag{3.7}
$$

For statements involving a full attractive operator or its evolution,
assume

$$
g=\gamma\varepsilon^2,\qquad
0<\gamma<(2rC_H)^{-1}.
\tag{3.8}
$$

[G, Theorem 5.1] supplies a closed semibounded $q_g$ on exactly
$\mathcal F$, with compact resolvent and the bound

$$
q_g[f]\ge(1-2rC_H\gamma)T[f]
             -\gamma\varepsilon^2B_\varepsilon\|f\|_2^2.
\tag{3.9}
$$

Write $H_g$ for its selfadjoint form operator, with domain

$$
D(H_g)=\{f\in\mathcal F:\ \exists F\in L^2(\mu),\
 q_g(f,v)=\langle F,v\rangle\ \forall v\in\mathcal F\}.
\tag{3.10}
$$

Write $\overline H_g$ for the operator of the restricted form in (3.4)
on exactly $\overline{\mathcal F}$, with the analogous variational domain.
This form is closed and semibounded by (3.7), (2.3) and KLMN [T, Theorem
6.24]; the same strict relative bound is less than one. Its form norm is
equivalent to the free base norm, and the latter embeds compactly into
$L^2(D)$ by (2.4). Hence it also has compact resolvent. Neither domain
(3.10) is being replaced by the intersection of a free operator domain
and a multiplier domain.

On compact smooth tests whose height support avoids $k_o$, the full and
restricted operators do have the concrete expressions

$$
H_gf=Lf-g\Gamma_of,\qquad
\overline H_gv=\overline Lv-gW_ov.
\tag{3.11}
$$

Indeed the multipliers are smooth and bounded with all derivatives on such
supports, so integration by parts against the form core extends by form
continuity to the entire domain. The right sides are again compact smooth
tests supported away from $k_o$. These tests therefore belong to the
domains of every positive integer power of the respective operators.
This local statement, rather than unrestricted multiplier membership of
all form states, will justify the response derivatives below.

## 4. A positive hidden harmonic of the actual point field

**Theorem 4.1 (native first harmonic and explicit lower control).** Put

$$
C_1(k)=\int_{\mathbb T^2}\Gamma_o(k,\alpha,\beta)
                  \cos(\beta-\beta_o)d\alpha d\beta.
\tag{4.1}
$$

The integral is absolutely convergent for each $k\in I$, and it is
precisely the Dirichlet Green kernel $R_1(k_o,k)$ of

$$
A_1=-\varepsilon^2\frac{d^2}{dk^2}+c(k)^2,
\qquad D(A_1)=H^2(I)\cap H^1_0(I),
\tag{4.2}
$$

relative to ordinary $dk$. This is the zero $\alpha$ mode and first
$\beta$ Fourier moment, without normalized angular averaging. In
particular it is strictly positive.
For $a>0$ let

$$
R^{(a)}(k_o,k)=
\frac{
 \sinh(a(\min(k_o,k)-l)/\varepsilon)
 \sinh(a(u-\max(k_o,k))/\varepsilon)}
 {\varepsilon a\sinh(ad/\varepsilon)}.
\tag{4.3}
$$

With $c_-=1/2-u/r$ and $c_+=1/2-l/r$, both strictly positive,

$$
0<R^{(c_+)}(k_o,k)\le C_1(k)
 \le R^{(c_-)}(k_o,k)\le\varepsilon^{-2}G_I(k_o,k)
\qquad(k\in I).
\tag{4.4}
$$

All constants, domains and scales here use the fixed $\varepsilon$.

Proof. Apply the ordinary circle Fourier decomposition to the closed form
(1.9). For integers $m,n$, the isometry

$$
(E_{mn}\varphi)(k,\alpha,\beta)
 =\frac{\varphi(k)}{2\pi}
 e^{i[m(\alpha-\alpha_o)+n(\beta-\beta_o)]}
$$

takes the height form to

$$
\int_I\left(\varepsilon^2|\varphi'|^2
       +(m/2+nc(k))^2|\varphi|^2\right)dk,
\qquad \varphi\in H^1_0(I).
\tag{4.5}
$$

To justify the closed-domain statement, the Fourier projection is an
average of phase translations with a character. It preserves the smooth
core, is bounded in the form norm, and its complementary sectors are form
orthogonal. The proof of (2.3) therefore applies sector by sector. In each
fixed sector the displayed potential is smooth and bounded on $\overline I$.
The one-dimensional weak equation puts its operator domain in
$H^2(I)\cap H^1_0(I)$, with the reverse inclusion by integration by parts.
Thus the sector correspondence is an operator correspondence with the same
height killing, not only the formal identity $Qe^{i(m\alpha+n\beta)}
=i(m/2+nc)e^{i(m\alpha+n\beta)}$.

For $m=0,n=1$ or $-1$ it gives (4.2). In particular, for a smooth height
test $a$,

$$
H_t\bigl(a(k)\cos(\beta-\beta_o)\bigr)(o)
 =(e^{-tA_1}a)(k_o).
\tag{4.6}
$$

The left side is the integral of $a(k)$ against the phase integral of
$p_t^\Omega(o,\cdot)\cos(\beta-\beta_o)$. The one-dimensional heat
kernel $h_t^{A_1}$ therefore equals that phase integral, first by testing
and then pointwise by smoothness. There is no $2\pi$ factor in (4.6):
the test character has value one at the original pole. By (3.6) and
$|\cos|\le1$, absolute integration in time is legitimate at every height.
Integrating (4.6) gives $C_1=\int_0^\infty h_t^{A_1}dt=R_1$.

For completeness, the elementary positive-resolvent comparison needed here
can be checked directly in this height problem. For a continuous
nonnegative potential $V$, solve
$-\varepsilon^2y''+Vy=0$ with $y(l)=0,y'(l)=1$, and solve the right
solution with $z(u)=0,z'(u)=-1$. They stay strictly positive in the
interior: while positive their respective outward derivatives cannot turn
towards a first zero, by $y''=Vy/\varepsilon^2$ and the reversed version
for $z$. Their Wronskian gives the Green kernel
$y(k_<)z(k_>)/(\varepsilon^2(y'z-yz'))$, with positive denominator.
The Wronskian is constant and at $l$ equals $z(l)>0$. The kernel
has endpoint zero values and derivative jump $-1/\varepsilon^2$,
so it is the inverse of the positive Dirichlet operator.
If $V_1\le V_2$, the resolvent identity reads

$$
R_{V_1}(a,k)-R_{V_2}(a,k)
 =\int_I R_{V_1}(a,s)(V_2(s)-V_1(s))R_{V_2}(s,k)ds\ge0.
\tag{4.7}
$$

All kernels in this bounded-interval identity are continuous and bounded;
positivity and the identity can equivalently be obtained from the weak
Dirichlet equations. For $V=a^2$, solving those equations gives (4.3).
For $V=0$ it gives $\varepsilon^{-2}G_I$. Apply (4.7) with
$0\le c_-^2\le c(k)^2\le c_+^2$ to prove (4.4).
These are standard Sturm--Liouville and resolvent tools; their use here
identifies a positive, quantitatively controlled harmonic of the original
native full Green field. $\square$

**Corollary 4.2 (explicit finite witnesses on original source fibers).**
For every $k\in I\setminus\{k_o\}$ take the two original source points

$$
q_+=(k,\alpha_o,\beta_o),\qquad
q_-=(k,\alpha_o,\beta_o+\pi).
$$

They have the same base coordinate, are distinct on the original $2\pi$
hidden circle, and have finite fields with

$$
\Gamma_o(q_+)-\Gamma_o(q_-)
 \ge \frac{C_1(k)}{\pi^2}
 \ge \frac{R^{(c_+)}(k_o,k)}{\pi^2}>0.
\tag{4.8}
$$

In particular the full point field does not factor through (1.5), even
on an off-pole height slice. One definite choice is $k=(l+k_o)/2$.

Proof. Let $R_{mn}(k_o,k)$ be the Dirichlet Green kernel of the height
operator in (4.5). Its potential $(m/2+nc)^2$ is nonnegative, so the
Wronskian proof in Theorem 4.1 gives $R_{mn}>0$. Testing the heat
semigroup against the corresponding character, exactly as in (4.6), gives

$$
\int_{\mathbb T^2}\Gamma_o(k,\alpha,\beta)
 e^{-i[m(\alpha-\alpha_o)+n(\beta-\beta_o)]}d\alpha d\beta
 =R_{mn}(k_o,k).
$$

Here reversing both indices leaves the height operator unchanged, so the
minus sign in the Fourier convention changes no coefficient. Absolute
interchange follows again from (3.6). When $k\ne k_o$, the field on the
entire phase torus is smooth. Its Fourier series is therefore absolutely
convergent, for example by integrating $(1-\partial_\alpha^2-
\partial_\beta^2)^2\Gamma_o$ against each character. Consequently

$$
\begin{aligned}
\Gamma_o(q_+)-\Gamma_o(q_-)
 &=\frac1{4\pi^2}\sum_{m,n\in\mathbb Z}
       (1-(-1)^n)R_{mn}(k_o,k)\\
 &\ge\frac{2R_{0,1}(k_o,k)+2R_{0,-1}(k_o,k)}{4\pi^2}
 =\frac{C_1(k)}{\pi^2}.
\end{aligned}
$$

Every summand is nonnegative, and $R_{0,1}=R_{0,-1}=C_1$.
Both points are off the pole and are reachable native rays by [N,
Theorem 8.2]. The point source used to evaluate their fields has not moved.
$\square$

## 5. Equal free summaries and unequal fixed-pole energy

**Definition 5.1 (a domain-safe pair of amplitudes).** Choose any compact
height subinterval $[j_0,j_1]\subset I\setminus\{k_o\}$ with
$j_0<j_1$, and any real $\phi\in C_c^\infty((j_0,j_1))$ of
$L^2(I)$ norm one. Such functions exist on either nonempty side of $k_o$;
a normalized interior smooth bump suffices. For $0<a<1$ put

$$
N_a=1+a^2/2,\qquad
f_\pm(k,\alpha,\beta)=
\frac{\phi(k)}{2\pi\sqrt{N_a}}
 \bigl(1\pm a\cos(\beta-\beta_o)\bigr).
\tag{5.1}
$$

These are smooth Hilbert-space amplitudes on the current-ray cylinder.
They are not five-mode pure rays, and no native operation preparing them
is assumed. Define their base amplitude summary as $J^*f$, its normalized
version as $b_f=J^*f/\|J^*f\|_2$ when nonzero, and their base probability
summary as the actual pushforward density

$$
m_f(k,\alpha)=\int_{\mathbb T}|f(k,\alpha,\beta)|^2d\beta.
\tag{5.2}
$$

The linear amplitude projection and the quadratic probability summary are
different maps.

**Theorem 5.2 (exact native energy separation).** Both amplitudes in (5.1)
have norm one, belong to $C_c^\infty(\Omega\setminus\{o\})$, and satisfy

$$
\begin{aligned}
J^*f_+=J^*f_-&=\frac{\phi(k)}{\sqrt{2\pi N_a}},
& b_{f_+}=b_{f_-}&=\frac{\phi(k)}{\sqrt{2\pi}},\\
m_{f_+}=m_{f_-}&=\frac{|\phi(k)|^2}{2\pi},\\
T[f_+]=T[f_-]&=
\varepsilon^2\|\phi'\|_2^2+
\frac{a^2}{2N_a}\int_I c(k)^2|\phi(k)|^2dk.
\end{aligned}
\tag{5.3}
$$

Against the single fixed field $\Gamma_o$ their difference is

$$
\begin{aligned}
\Delta V&:=V_o[f_+]-V_o[f_-]
 =\frac{a}{\pi^2N_a}\int_I|\phi(k)|^2C_1(k)dk\\
&\ge\frac{a}{\pi^2N_a}
 \int_I|\phi(k)|^2R^{(c_+)}(k_o,k)dk>0,\\
q_g[f_+]-q_g[f_-]&=-g\Delta V<0\qquad(g>0).
\end{aligned}
\tag{5.4}
$$

The energy identity is valid on these tests for every $g>0$; statements
about the full attractive operator use (3.8). Under that assumption the
pair lies in $D(H_g^n)$ for every positive integer $n$. Its spectral
measures for the same $H_g$ are different, as are its sufficiently short
positive-time attractive return responses:

$$
\langle e^{-tH_g}f_+,f_+\rangle
 -\langle e^{-tH_g}f_-,f_-\rangle
 =t g\Delta V+o(t)\quad(t\downarrow0).
\tag{5.5}
$$

Proof. Integrating $1$, $\cos$, $\cos^2$ and $\sin^2$ over a full
$2\pi$ circle gives $2\pi,0,\pi,\pi$. Hence the norm of each function
is one and the first three summaries are (5.3). The $P$ derivative acts
only on $\phi$. The $Q$ derivative is
$\mp ac(k)\phi(k)\sin(\beta-\beta_o)/(2\pi\sqrt{N_a})$.
Their squared integrals give the kinetic formula, with no dropped
cross term. The pointwise probability difference is

$$
|f_+|^2-|f_-|^2
 =\frac{a|\phi(k)|^2}{\pi^2N_a}\cos(\beta-\beta_o).
\tag{5.6}
$$

The entire support avoids the source height, so $\Gamma_o$ is smooth and
bounded there. Integrating (5.6), using (4.1) and (4.4), proves (5.4).
The positive lower integral is finite and strictly positive since
$\phi$ has norm one and $R^{(c_+)}>0$ at every interior height.
Definition 3.2 gives the iterated operator-domain statements. For a
normalized operator-domain vector the first spectral moment is
$\langle H_gf,f\rangle=q_g[f]$. Thus (5.4) separates the spectral
measures. Differentiating the bounded semibounded heat semigroup at zero
on this domain gives (5.5). This compares states at one pole, not spectra
of operators with different pole positions. $\square$

**Proposition 5.3 (which free futures agree for this same pair).** Put
$(S_sf)(k,\alpha,\beta)=f(k,\alpha,\beta-s)$. Then $f_-=S_\pi f_+$.
For every $t\ge0$ the pair has identical projected free amplitudes
$J^*H_tf_\pm$ and identical densities
$m_{H_tf_\pm}$. Their full free norms also agree, so these equalities
remain true after normalizing the two nonzero free amplitudes to norm
one. Separately, if $\rho_\pm=|f_\pm|^2$ are used as initial probability
densities for the killed Markov process, their projected subprobability
laws at all times and all finite collections of base observation times
are identical. They also have identical free Schrödinger projected
amplitudes and base probability summaries under $e^{-itL}$.

Proof. These translations are comparison maps on the analytic cylinder,
not additional native actuators or amplitude-preparation operations. The
phase translation preserves the free form, its domain and the measure, so
it commutes with every spectral function of $L$. Also
$J^*S_s=J^*$ and $m_{S_sf}=m_f$. This proves the amplitude assertions,
their norm equality and the Schrödinger assertions. The operators $H_t$
are injective by spectral calculus, so normalization is defined at each
finite $t$ for these nonzero vectors.

For probability transport, (2.5), symmetry and Fubini imply

$$
\int_{\mathbb T}(H_t\rho)(k,\alpha,\beta)d\beta
 = e^{-t\overline L}\left(\int_{\mathbb T}\rho\,d\beta\right)(k,\alpha)
\tag{5.7}
$$

for integrable densities. Apply it to the equal initial marginals (5.3).
The projected process is the killed base Markov process of Theorem 2.1;
hence its initial marginal also determines all its finite-time joint laws,
including survival. The same holds for finite interleavings with prescribed
deterministic commands confined to $I$, using the cylinder guard in
Definition 1.3 and recording refusals. Their domains and base updates factor
through the same base. A command leaving this cylinder is not inserted into
its killed semigroup without a separately specified continuation.

The density $H_t|f|^2$ in (5.7) is not in general $|H_tf|^2$.
The proposition establishes the two separate equalities for this translated
pair; it does not identify the two evolution rules. No interacting-future
equality is asserted. $\square$

## 6. A quantified defect in compressed attractive evolution

**Theorem 6.1 (nonzero second response with justified domains).** Assume
(3.8), keep the same pole, and let

$$
v(k,\alpha)=\frac{\phi(k)}{\sqrt{2\pi}},\qquad
h_0=Jv=\frac{\phi(k)}{2\pi},\qquad
\sigma_o^2(k,\alpha)=\frac1{2\pi}\int_{\mathbb T}
 |\Gamma_o(k,\alpha,\beta)-W_o(k,\alpha)|^2d\beta.
\tag{6.1}
$$

The variance is used only on the compact height support of $\phi$, where
it is smooth and finite. Let
$C_g(t)=J^*e^{-tH_g}J$ on the base Hilbert space. On this particular
unit vector $v$, the exact second derivative defect is

$$
\begin{aligned}
J^*H_g^2Jv-\overline H_g^{\,2}v&=g^2\sigma_o^2v,\\
C_g(t)v-e^{-t\overline H_g}v
 &=\tfrac12t^2g^2\sigma_o^2v+o_{L^2}(t^2)
 \quad(t\downarrow0).
\end{aligned}
\tag{6.2}
$$

In particular, with $\mathcal D_g(v)$ denoting its scalar second
coefficient before the factor $1/2$,

$$
\begin{aligned}
\mathcal D_g(v)
&=\|H_gh_0\|_2^2-\|\overline H_gv\|_2^2\\
&=g^2\|(1-\Pi)\Gamma_oh_0\|_2^2
 =g^2\int_D\sigma_o^2|v|^2d\nu\\
&\ge\frac{g^2}{8\pi^4}
       \int_I|\phi(k)|^2 C_1(k)^2dk>0.
\end{aligned}
\tag{6.3}
$$

Thus $\operatorname{Ran}J$ reduces the free operator but does not remain
invariant under the full attractive evolution. The compressed family
$C_g(t)$ is not the semigroup of the restricted same-field form.
In fact it fails the semigroup identity itself for sufficiently small
equal positive time steps.

Proof. Definition 3.2 puts $h_0$ and $v$ in the domains of all powers of
their operators. Multiplying by $\Gamma_o$, averaging in $\beta$, and
applying either differential expression preserves smoothness and the same
compact height support. Consequently every product in the following
calculation is an actual $L^2$ operator product on these tests. Free
reduction and (3.11) give

$$
J^*H_gJv=\overline H_gv,\qquad
(1-\Pi)H_gh_0=-g(1-\Pi)\Gamma_oh_0.
\tag{6.4}
$$

Insert $1=\Pi+(1-\Pi)$ between the two $H_g$ factors. The projected
factor gives $\overline H_g^2v$. In the other factor the free part
vanishes after $J^*$, since $L$ reduces $\Pi$. The remaining product is

$$
g^2J^*M_{\Gamma_o}(1-\Pi)M_{\Gamma_o}Jv
 =g^2\sigma_o^2v.
\tag{6.5}
$$

Here $M_{\Gamma_o}$ means multiplication by the actual full field.
The last identity uses the conditional average in (3.3), so
$\operatorname{avg}_\beta(\Gamma_o(\Gamma_o-W_o))
=\operatorname{avg}_\beta(\Gamma_o-W_o)^2$.
Semibounded spectral calculus has a strong second-order Taylor expansion
on $D(H_g^2)$ and $D(\overline H_g^2)$ for $t\downarrow0$.
Their zero and first terms agree by (6.4), proving (6.2).

Orthogonality of $\Pi$ and the first identity of (6.4) give the first
three expressions of (6.3). For its strict lower bound, at each height in
the support,

$$
\begin{aligned}
C_1(k)&=\int_{\mathbb T^2}(\Gamma_o-W_o)
                         \cos(\beta-\beta_o)d\alpha d\beta,\\
\int_{\mathbb T^2}|\Gamma_o-W_o|^2d\alpha d\beta
&\ge\frac{C_1(k)^2}{2\pi^2},
\end{aligned}
\tag{6.6}
$$

because the cosine has squared norm $2\pi^2$ on the actual phase torus.
Since $|h_0|^2=|\phi|^2/(4\pi^2)$, this is exactly (6.3).
The lower bound in (4.4) could further replace $C_1$ by $R^{(c_+)}$.

There is also an exact semigroup-law test, with no unbounded block
exponentials. For $t>0$,

$$
\begin{aligned}
\langle(C_g(2t)-C_g(t)^2)v,v\rangle
 &=\|(1-\Pi)e^{-tH_g}Jv\|_2^2\\
 &=t^2\mathcal D_g(v)+o(t^2)>0
 \quad\text{for sufficiently small }t>0.
\end{aligned}
\tag{6.7}
$$

The exact identity follows by inserting $1-\Pi$ between two bounded
selfadjoint heat operators. The first-order strong expansion on $h_0$
and (6.4) give its last line. This proves the failure of the semigroup
law and the actual leakage, without a formal global decomposition of an
unbounded singular generator. $\square$

**Definition 6.2 (what memory is required by this obstruction).** The
restricted form describes the evolution generated by $\overline H_g$.
The operator $C_g(t)$ describes full attractive evolution followed by
one base amplitude projection. Composing $C_g(t)$ twice instead inserts
an additional projection at the intermediate time; lifting it by $J$
erases the hidden component. Equation (6.7) measures the resulting exact
loss of return response on the given test.

The general distinction between present projection, hidden initial state
and later feedback is supplied by [F, §§18,33], [S, §§2.1,5.1--5.2] and
Gouasmi--Parish--Duraisamy [M, §2.1, equations (2.1)--(2.3)]. None of those
generic identities alone proves a nonzero term for this singular operator.
Equations (4.1)--(4.4) and (6.3) provide that missing native quantity,
on an explicitly checked operator domain. They require retaining hidden
response information, or changing the predictive task or state class;
they do not specify a minimal finite memory model, a global memory-kernel
formula or a computational cost reduction. A hidden reset is an additional
operation, not a consequence of the lawful commands.

## 7. Spectral symmetry and independent stability conditions

**Proposition 7.1 (the source-pole spectral exception).** For
$o_s=(k_o,\alpha_o,\beta_o+s)$, the original source points $o_s$ have the
same base coordinate. In the constant-density family and the strict regime
(3.8), their full attractive operators obey

$$
H_{g,o_s}=S_s H_{g,o}S_s^{-1},\qquad
D(H_{g,o_s})=S_sD(H_{g,o}),
\tag{7.1}
$$

and their form domains are transported by the same unitary. Consequently
the entire spectrum with multiplicities, and in particular the ground
energy, is independent of $\beta_o$ at fixed $(k_o,\alpha_o)$.
Unitary-invariant scalar spectral data of the pole therefore factor through
this quotient. This statement does not apply to the fixed-pole,
state-dependent responses in Theorems 5.2 and 6.1.

Proof. The free translation symmetry gives
$\Gamma_{o_s}(k,\alpha,\beta)=\Gamma_o(k,\alpha,\beta-s)$. Changing
variables in the potential integral gives
$q_{g,o_s}[S_sf]=q_{g,o}[f]$. The free form domain is invariant under
$S_s$, so the variational definition of the operator transports its full
domain and gives (7.1). Spectral calculus gives the spectral statement.
For example (5.1) translates the amplitude by $\pi$ while keeping the
pole fixed; (7.1) instead translates the pole and the amplitude together.
Those comparisons are distinct. $\square$

**Corollary 7.2 (the obstruction occurs inside the supplied stable binding
family).** Fix $r,I,o$ as above and choose $\gamma$ satisfying (3.8).
Let the independent periodic binding data of [G, Theorem 6.2] be

$$
\phi_1(k)=\sqrt{2/d}\sin\frac{\pi(k-l)}d,
\qquad
M_o=\int_I G_I(k_o,k)|\phi_1(k)|^2dk>0.
\tag{7.2}
$$

For every positive $\varepsilon$ satisfying

$$
\varepsilon^2<\frac{\gamma M_od^2}{4\pi^4},
\qquad g=\gamma\varepsilon^2,
\tag{7.3}
$$

the full and the restricted same-field forms have finite attained negative
ground energies. All the positive harmonic, unequal-energy and compressed
response results above hold for each such fixed parameter. There is no
conflict between those obstructions and strict stability.

Proof. The full statement is [G, Theorems 5.1 and 6.2], whose distinct
hypotheses (3.8) and (7.3) are both imposed. For the restricted form use the
same normalized full test $\phi_1/(2\pi)=J(\phi_1/\sqrt{2\pi})$.
Equations (3.4) and (3.6) give its unchanged Rayleigh value

$$
\varepsilon^2\pi^2/d^2-\gamma M_o/(4\pi^2)<0.
\tag{7.4}
$$

The restricted closed form has compact resolvent by Definition 3.2, so its
infimum is also finite and attained. Variational inclusion gives only
$\inf q_g\le\inf\overline q_g$ on the respective unit spheres; no strict
ground-energy gap is inferred from leakage or from the two trial energies.
The interval of positive $\varepsilon$ in (7.3) is nonempty. For each
such fixed choice one can choose the compact test interval of Definition
5.1, so the obstructions coexist with the two attained-negative results.
No exchange with a limit $\varepsilon\downarrow0$ is used. $\square$

## 8. Exact sufficient tasks and the remaining conditional statistic

**Proposition 8.1 (conditional energy is not the Haar marginal).** For a
normalized $f\in\mathcal F$, put $m_f$ as in (5.2) and, on its positive
fibers, define

$$
\rho_f(\beta\mid k,\alpha)=\frac{|f(k,\alpha,\beta)|^2}{m_f(k,\alpha)},
\qquad
\mathcal E_{o,f}(k,\alpha)=\int_{\mathbb T}
 \Gamma_o(k,\alpha,\beta)\rho_f(\beta\mid k,\alpha)d\beta.
\tag{8.1}
$$

Set the integrand $m_f\mathcal E_{o,f}$ to zero on zero-marginal fibers.
The same-field potential is

$$
V_o[f]=\int_D m_f\mathcal E_{o,f}\,d\nu.
\tag{8.2}
$$

For $f=Jv$, the conditional density is $1/(2\pi)$ on positive fibers,
so $\mathcal E_{o,f}=W_o$. On the unrestricted form domain, the full base
amplitude and probability summaries, their free futures described in
Proposition 5.3 and the single kinetic scalar do not determine (8.2).
In particular the obstruction is not removed by storing both the linear
and quadratic base summaries.

Proof. The disintegration identity (8.2) is the same elementary conditional
expectation identity already used in [C, Corollary 82.6]. Tonelli and (3.7)
justify it here on the actual finite-circle form domain. On $Jv$ the
conditional density is exactly uniform by (2.1), giving (3.4). For the
unrestricted assertion, use the two normalized members (5.1) of that very
domain. Their summaries and free futures agree by (5.3) and Proposition
5.3, while (5.4) gives unequal values of (8.2). Thus the extra missing
quantity is a relation between the conditional state density and the fixed
point field. Merely integrating the field against unweighted angular
measure, as in (3.2), does not supply it. $\square$

**Definition 8.2 (scope of sufficiency).** In this source the exact
sufficiency statements are indexed by their tasks:

| Task on the declared source | Sufficient information and mathematical boundary |
| --- | --- |
| Native bottom outputs and command refusal | $(k,\alpha)$ with the complete guards (1.3), by [B] |
| Added free killed base laws | Initial base law and the operator of Theorem 2.1, in the original clock |
| Hidden-integrated point Green field | $\pi o$ and the base Green kernel, with the integral normalization (3.2) |
| Same-field form on $\operatorname{Ran}J$ | Base amplitude and multiplier $W_o=\overline\Gamma/(2\pi)$, by (3.4) |
| Full fixed-pole point field | Does not factor through $\pi$, by the finite witnesses (4.8) |
| Full fixed-pole energy on all allowed amplitudes | Not determined by the combined base summaries and kinetic scalar, by (5.4) |
| Full attractive evolution followed by projection | Differs from restricted evolution and fails a semigroup law, by (6.2)--(6.7) |
| Unitary-invariant spectrum as the pole moves along one hidden fiber | Constant along that fiber, by (7.1) |

These tasks distinguish an output function, a pushforward law, an amplitude
projection, a Green marginal, multiplication by a field and an evolution.
The table does not assert that one common smaller state solves all of them.
The family of probability densities in Proposition 5.3 is a family of
functions on a two-dimensional base, not a two-real-number predictor.

## 9. Mathematical sources and boundaries of the correspondence

**Definition 9.1 (primary analytic suppliers).** The classical tools used
inside the source-specific proofs have the following precise scope.

| Primary source | Correspondence used here |
| --- | --- |
| [T] G. Teschl, *Mathematical Methods in Quantum Mechanics*, [primary text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorem 2.13, Lemma 2.24, Theorem 6.24, §§7.1 and 9.1 | Closed-form representation, reducing subspaces, KLMN, Fourier and regular Sturm--Liouville tools. In (4.2) the Sturm--Liouville coefficients are $p_{\rm SL}=\varepsilon^2$, $r_{\rm SL}=1$, $q_{\rm SL}=c^2$ on a bounded interval with Dirichlet endpoints. The text's conjugate-linear first-slot inner product is conjugated to our linear-first-slot convention; energies and operator domains are unchanged. KLMN is used only with the strict relative bound in (3.8). |
| [H] Y. Colin de Verdière, L. Hillairet and E. Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, [doi:10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), §3.1.2, Theorem B and Theorem 3.2 | Free smooth heat and interior localization underlying [G]. For the present family the fields are $\varepsilon P,Q$, the density is smooth positive, the drift is zero, the bracket step is two, and the Dirichlet realizations are contraction semigroups. Theorems about smooth free operators are not applied to the singular attractive multiplier. |
| [R] P. Ciatti, M. G. Cowling and F. Ricci, *Hardy and uncertainty inequalities on stratified Lie groups*, [arXiv:1308.2373v1](https://arxiv.org/pdf/1308.2373v1), §2 and Corollary 3.2 | The unweighted group estimate consumed by [G, Proposition 4.3]. Its substitution is $p=2$, $\alpha=1$, homogeneous dimension four, so $0<1<4/2$. Its group Green normalization is transferred by [G, Proposition 4.2], with the actual measure factor $\varepsilon^2/(2r)$ and unit-source factor $2r/\varepsilon^2$. |
| [M] A. Gouasmi, E. J. Parish and K. Duraisamy, *A priori estimation of memory effects in coarse-grained nonlinear systems using the Mori--Zwanzig formalism*, [arXiv:1611.06277v2](https://arxiv.org/pdf/1611.06277v2), §2.1 | The distinction between a projected instantaneous term, hidden initial state and feedback memory. Exact elimination alone gives no complexity reduction. It does not supply the unbounded-domain calculation (6.5); that calculation is justified on the compact tests here. |

These ingredients are `literature-attested`. The native first harmonic,
its finite source-fiber witnesses, the simultaneous normalized amplitude
and kinetic matching, and the quantified attractive response defect are
`repo-derived` applications in this fixed contract. No worldwide priority
or exhaustive literature-search claim is made.

**Definition 9.2 (repository precedents and nontransferred hypotheses).**
Besides [N], [B] and [G], the closest suppliers are:

| Repository source | Precise use and boundary |
| --- | --- |
| [C] [Recursive holographic boundary geometry, continuation III](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md), §§81.5,82.3--82.6,85.5 | Prior matched heat-factor/Green-marginal, translated-energy and compressed-multiplier arguments. Its carrier is $H^1\times\mathbb R$ with three direct fields, infinite hidden Haar fiber and volume exponent five. Its pullback is generally not an $L^2$ map and its all-scale collapse conclusion is not transferred to the present compact hidden circle with two direct fields and exponent four. |
| [F] [Recursive holographic boundary geometry](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md), §§18,33 | Existing static/dynamic elimination and hidden-initial-state distinctions. They do not by themselves identify a nonzero coupling for (1.10)--(1.11). |
| [S] [Symplectic predictive completion](SYMPLECTIC_PREDICTIVE_COMPLETION.md), §§2.1,5.1--5.2 | Existing invariant-quotient and projected-response viewpoint. Its finite linear/Gaussian or Hamiltonian hypotheses are not imposed on native nonlinear pure-source commands by analogy. |
| [A] [Native open-domain affine approximation and finite attainment](FIB_NATIVE_OPEN_DOMAIN_AFFINE_APPROXIMATION_AND_FINITE_ATTAINMENT.md), complete §11 | Fixed-dimension affine approximation, varying-model quantifiers and all-times guard recovery are separate contracts. The smooth behavioral base and its exact killed free factor here do not evade those affine-capacity hypotheses or make an endpoint guard sufficient. |
| [D] [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md), §12 | Exact coefficient selection is distinguished there from finite-precision realization of its own instrument. That result supplies no instrument, conditioning estimate or amplitude preparation for this cylinder. |

The structural overlap with [C] is explicit. The positive circular harmonic
(4.1), the finite compact-torus estimate (4.8), the exact pair (5.1) and
coefficient (6.3) are the native-source additions; a generic projection
identity is not being counted again as new mathematics.

**Definition 9.3 (unresolved interpretation and parameter boundaries).**
The full native source has ray dimension three, direct control rank two,
bracket growth $(2,3)$ and local volume exponent four. The base behavioral
quotient has dimension two. These are distinct from affine predictive
capacity, the amount of data in a probability density, acquisition or
precision resources, and the number of physical spatial axes. None of the
proved correspondences supplies a source-to-physical-space map.

The free covariance, density, analytic clock, Dirichlet killing, attractive
coupling and $L^2$ state space remain explicit additions. No CPTP map is
inferred from the original nonlinear pure-source command law. No proof of
preparation, measurement or finite-resource acquisition of the amplitudes,
conditional densities or response coefficients is supplied. Including the
reference coherence would enlarge the original observation task; ignoring
it does not remove the corresponding rays from the source.

The strict stability condition (3.8) and the separate periodic binding
condition (7.3) retain their supplier scopes. The value of $C_H$ is
sufficient, not sharp. Critical equality, a complete coupling classification,
a strict full-versus-restricted ground-energy gap, an operator at
$\varepsilon=0$, and estimates uniform as $\varepsilon\downarrow0$ are
not established. In particular all quantitative lower estimates in this
volume are statements for each fixed positive $\varepsilon$. The
point-source field is never replaced by a weighted Hardy surrogate, a
Euclidean potential or a finite-time field. A globally valid closed
attractive base model would need an additional sufficient state restriction
or a proved retention mechanism; free Markov sufficiency alone fails by
(6.7).

## 追加锚（本行以下为增补区）

## 10. Uniform same-point energy on the retained three-coordinate family

**Definition 10.1 (fixed native family and retained contract).** Retain
[N]'s negative amplitude convention, arbitrary fixed preparation phases,
and two original controls. Fix $0<Z<1$, $H=(1-Z)/2$,
$I=(l,u)\Subset(0,H)$, $k_0\in I$, and $\varepsilon>0$.
For an immutable parameter $\kappa$ put $X=Y=H+\kappa$. In mode order
$(0,1,2,3,13)$ the probabilities and phase weights are exactly

$$
p_\kappa=(k-2\kappa,H+\kappa-k,Z,H+\kappa-k,k),\qquad
w_s=\frac{d_s}{p_{\kappa,s}\mathcal I_\kappa},\quad
d=(1,-1,0,-1,1),\quad
\mathcal I_\kappa=\sum_{s\in\{0,1,3,13\}}p_{\kappa,s}^{-1}.
\tag{10.1}
$$

Increments satisfy $h_2=0$, $h_1=h_3=v$. Use
$\theta=[h_{13}]$, $D=[h_0-h_{13}]$, and the declared observation
$q=(k,\theta,[v])$. All three angular periods are $2\pi$.
This is the unimodular phase change of [G, Definition 12.1], and its
nearby full leaf has dimension four. The preparation phases are translated,
not equated. The original full read menu is not replaced by $q$.

Write $s_\kappa=H+\kappa$, $a_\kappa=\kappa s_\kappa/H$, and

$$
\begin{aligned}
A_\kappa&=\frac{(k-2\kappa)(s_\kappa-k)}{2H(k-a_\kappa)},&
B_\kappa&=-\frac{k(k-2\kappa)}{2H(k-a_\kappa)},\\
C_\kappa&=\frac{\kappa(s_\kappa-k)}{H(k-a_\kappa)},&
b_\kappa&=A_\kappa-B_\kappa
 =\frac{s_\kappa(k-2\kappa)}{2H(k-a_\kappa)}.
\end{aligned}
\tag{10.2}
$$

These are the original coefficients of [G, Calculation 12.2]. Thus

$$
P=\partial_k,\qquad
Q_\kappa=A_\kappa\partial_\theta+B_\kappa\partial_v
                  +C_\kappa\partial_D,\qquad
R_\kappa=A_\kappa\partial_\theta+B_\kappa\partial_v.
\tag{10.3}
$$

Choose one closed two-sided parameter interval $K=[-\kappa_1,\kappa_1]$
small enough that all probabilities are positive on a common larger height
interval $I'\Supset\overline I$, with $\overline{I'}\subset(0,H)$,
and $s_\kappa>\sup I'$, $b_\kappa>0$ there. Such a choice follows,
for example, by first enlarging $I$ and then decreasing
$\min(l/4,(H-u)/2,H/4)$. All constants below are chosen on this one
compact parameter set; $Z,I,k_0,\varepsilon$ remain fixed.

For $\kappa\ne0$ the full analytic cylinder, measure and free form are

$$
\Omega=I\times\mathbb T_\theta\times\mathbb T_v\times\mathbb T_D,
\quad d\mu=dk\,d\theta\,dv\,dD,\qquad
T_\kappa[f]=\int_\Omega
 (\varepsilon^2|Pf|^2+|Q_\kappa f|^2)d\mu.
\tag{10.4}
$$

Its domain is the compact smooth height-core completion; its operator
$L_\kappa$ is the horizontal Friedrichs form operator. The full field
$\Gamma_{\kappa,o}$ is its killed free unit point-source Green field
at $o=(k_0,0,0,0)$. Density one, covariance
$\operatorname{diag}(\varepsilon^2,1)$, clock $e^{-tL_\kappa}$,
periodic phases and Dirichlet height killing are unchanged.

On $B=I\times\mathbb T^2$, with $d\nu=dk\,d\theta\,dv$, set

$$
\begin{aligned}
\mathcal E_\kappa[z]&=\int_B
 (\varepsilon^2|\partial_kz|^2+|R_\kappa z|^2)d\nu,\qquad
\mathcal F_\kappa^B=
 \overline{C_c^\infty(B)}^{(\|\cdot\|_2^2+\mathcal E_\kappa)^{1/2}},\\
(Jz)(q,D)&=(2\pi)^{-1/2}z(q).
\end{aligned}
\tag{10.5}
$$

Here $J$ is the actual isometry into $L^2(\Omega,\mu)$.
The notation $\mathcal E_\kappa$ avoids confusing a function with the
phase coordinate $v$. At $\kappa=0$, (10.5) is defined directly on the
native three-coordinate double-wall leaf. No four-dimensional smooth
point-Green density at $\kappa=0$ is postulated.

**Theorem 10.2 (uniform native Green control and collective compactness).**
For the family (10.1)--(10.5), the actual restricted killed free operator is
the form operator $\mathscr L_\kappa$ of $\mathcal E_\kappa$.
Let $p_\kappa^B$ and
$G_\kappa(q)=\int_0^\infty p_\kappa^B(t,q_0,q)dt$ be its heat and
unit-source Green densities, where $q_0=(k_0,0,0)$.
There are finite constants $A>0$, $B_0\ge0$, independent of
$\kappa\in K$, such that

$$
\int_B G_\kappa|z|^2d\nu
 \le A\mathcal E_\kappa[z]+B_0\|z\|_2^2
 \qquad(z\in\mathcal F_\kappa^B).
\tag{10.6}
$$

The union of the sets
$\{z\in\mathcal F_\kappa^B:\|z\|_2^2+\mathcal E_\kappa[z]\le M\}$,
$\kappa\in K$, is relatively compact in $L^2(B)$ for every finite $M$.
As $\kappa\to0$ through either sign, the free forms Mosco-converge to
$\mathcal E_0$, and $G_\kappa\to G_0$ locally uniformly off $q_0$
and in $L^1(B)$. The constants are not asserted uniform as
$\varepsilon\downarrow0$ or as the fixed height data move.

Proof. Hidden $D$ translations commute with the two original fields,
preserve measure, and preserve the compact smooth height core. Their Haar
average $\Pi$ decreases $T_\kappa$ by Jensen's inequality and gives
orthogonal free form components. The averaged-core and variational
resolvent proof of Theorem 2.1 therefore applies with $D$ as the hidden
circle. It gives exactly

$$
\begin{gathered}
\mathcal F_\kappa^{\rm full}\cap\operatorname{Ran}J
   =J\mathcal F_\kappa^B,\qquad T_\kappa[Jz]=\mathcal E_\kappa[z],\\
D(L_\kappa)\cap\operatorname{Ran}J=J D(\mathscr L_\kappa),\qquad
L_\kappa J=J\mathscr L_\kappa,\qquad
e^{-tL_\kappa}J=J e^{-t\mathscr L_\kappa}.
\end{gathered}
\tag{10.7}
$$

These reused projection facts require no full attractive stability.
They also give the $q$-only free transition laws and the same height
survival event, by iteration against bounded base observables. Equivalently
its killed diffusion is

$$
dK_t=\sqrt2\varepsilon\,dB_t^1,\qquad
d\theta_t=\sqrt2A_\kappa(K_t)\,dB_t^2,\qquad
dv_t=\sqrt2B_\kappa(K_t)\,dB_t^2,
$$

with two independent real Brownian motions, phases reduced modulo
$2\pi$, and killing at $\inf\{t:K_t\notin I\}$.
The coefficients have no vertical derivatives and $R_\kappa k=0$, so
there is no Itô correction. This is the original analytic clock; these
sample paths are not asserted to be finite-variation native commands.

For a concrete completed-domain description, expand in the normalized
angular basis $(2\pi)^{-1}e^{i(m\theta+nv)}$ and write $z_{mn}(k)$
for its coefficients. Then

$$
\begin{aligned}
V_{\kappa,mn}(k)&=(mA_\kappa+nB_\kappa)^2
 =b_\kappa(k)^2\left(m-\frac{(m+n)k}{s_\kappa}\right)^2,\\
\mathcal F_\kappa^B
 &=\left\{z:\ z_{mn}\in H^1_0(I),\
 \sum_{m,n}\int_I(\varepsilon^2|z_{mn}'|^2+
                 V_{\kappa,mn}|z_{mn}|^2)dk<\infty\right\},\\
D(\mathscr L_\kappa)
 &=\left\{z:\ z_{mn}\in H^2(I)\cap H^1_0(I),\
 \sum_{m,n}\|(-\varepsilon^2\partial_k^2+
                       V_{\kappa,mn})z_{mn}\|_2^2<\infty\right\}.
\end{aligned}
\tag{10.8}
$$

Membership in $L^2(B)$ is implicit. Parseval, finite-mode truncation and
one-dimensional core approximation prove these identities. On the smooth
core the expression is
$\mathscr L_\kappa=-\varepsilon^2\partial_k^2-R_\kappa^2$;
(10.8), or equivalently form representation, specifies its actual domain.
No equality of the domains for different parameters is used.

Here is a uniform compactness bound. Put $M=|m|+|n|$, $N=m+n$, and
$b_- =\inf_{K\times I'}b_\kappa>0$.
For $|N|\ge M/4$, zero extension from $I$ and the elementary oscillator
inequality on the real line give

$$
\int_I(\varepsilon^2|f'|^2+
 b_-^2(m-Nk/s_\kappa)^2|f|^2)dk
 \ge\frac{\varepsilon b_-|N|}{s_\kappa}\|f\|_2^2.
\tag{10.9}
$$

Indeed expand the nonnegative square
$\|\varepsilon f'+a(k-t)f\|_2^2$ with
$a=b_-|N|/s_\kappa$, $t=ms_\kappa/N$; integration by parts gives
(10.9), also when $t$ lies outside $I$.
If $|N|<M/4$, then $|m|>3M/8$ and $0<k/s_\kappa<1$, so
$|m-Nk/s_\kappa|>M/8$. Thus in both cases the fiber energy is at least
$cM\|f\|_2^2-C\|f\|_2^2$, with common constants.
High angular modes have a uniformly small $L^2$ tail on every bounded
energy set. Each finite collection of modes is bounded in $H^1_0(I)$,
which is compact in $L^2(I)$. This proves collective compactness.
The height Poincaré bound also gives the common gap
$\lambda_0=\varepsilon^2\pi^2/(u-l)^2$.

For free Mosco lower semicontinuity, take a weakly convergent sequence of
bounded free energy. Each finite collection of Fourier modes has weak
$H^1_0$ compactness, its coefficients converge smoothly, and its energy is
lower semicontinuous. Taking the supremum over finite mode sets gives
membership in $\mathcal F_0^B$ and the full lower bound. Recovery follows
by first approximating in the $\mathcal E_0$ norm with a fixed smooth
finite-mode core function and then taking a diagonal sequence. This proves
the free limit without imposing a common completed domain.

It remains to establish the uniform singular estimate; compactness of the
parameter interval alone would not give (10.6). Use the unimodular base
angles $\alpha=\theta-v$, $\beta=\theta$. Then

$$
R_\kappa=b_\kappa(k)
 \left(\partial_\alpha+(1-k/s_\kappa)\partial_\beta\right),\qquad
\det\begin{pmatrix}A_\kappa&B_\kappa\\A_\kappa'&B_\kappa'\end{pmatrix}
 =-b_\kappa^2/s_\kappa.
\tag{10.10}
$$

The determinant is uniformly separated from zero. In a real local chart
at $q_0$, set $b_o=b_\kappa(k_0)$, $c_o=1-k_0/s_\kappa$ and

$$
\begin{gathered}
x=k-k_0,\quad y=\alpha,\quad
z=-s_\kappa(\beta-c_oy),\qquad
\xi=x/\varepsilon,\quad\eta=y/b_o,\quad\zeta=z/(\varepsilon b_o),\\
\varepsilon P=U:=\partial_\xi,\qquad
R_\kappa=\frac{b_\kappa(k)}{b_o}
 V,\quad V:=\partial_\eta+\xi\partial_\zeta,\qquad
 d\nu=m_\kappa\,d\xi\,d\eta\,d\zeta,\quad
 m_\kappa=\frac{\varepsilon^2b_o^2}{s_\kappa}.
\end{gathered}
\tag{10.11}
$$

These are exact identities, not only tangent limits. On one common
coordinate neighborhood the chart Jacobians, their inverses and all
coefficient derivatives have uniform bounds; $m_\kappa$ and
$b_\kappa/b_o$ have positive upper and lower bounds. The Heisenberg gauge

$$
N(\xi,\eta,\zeta)
 =\left((\xi^2+\eta^2)^2+(2\zeta-\xi\eta)^2\right)^{1/4}
\tag{10.12}
$$

is comparable to the horizontal distance there, with common constants.
Write $N_\kappa(q)$ for its pullback. The same construction centered at
any point of a compact larger cylinder gives uniform local ball volumes
comparable to $r^4$ for sufficiently small $r$.

For completeness, the precise heat estimate used to integrate the
singularity is

$$
p_\kappa^B(t,q_0,q)
 \le C t^{-2}\exp(-cN_\kappa(q)^2/t),\quad 0<t<t_0,
\tag{10.13}
$$

on a smaller common source chart, together with a uniform integrable
small-time bound away from that chart. These are the local upper Gaussian
estimates of Jerison--Sánchez-Calle [J, Theorem 2, p.849], with the
parameter bounds checked as follows. Extend the vertical pair
$(A_\kappa,B_\kappa)$ from $I'$ to a common height circle, keeping its
length positive and its argument derivative of one sign. To construct the
extension, lift its argument on $I'$; its derivative is
$-b_\kappa^2/(s_\kappa(A_\kappa^2+B_\kappa^2))<0$.
Continue that derivative negatively on the complementary arc, with integral
making one full turn, and continue the positive length smoothly. The arc
can be chosen long enough and the construction depends smoothly on
$\kappa$. On the compact three-torus the two fields
$\varepsilon\partial_k$ and
$A_\kappa\partial_\theta+B_\kappa\partial_v$ are divergence free and
uniformly bracket-generating of step two.

Apply [J]'s upper-bound proof on a finite common chart cover. On the
native cylinder its lifting coordinates can be chosen by (10.11); on the
complementary arc the uniformly nonzero argument derivative supplies
smooth contact coordinates with the same bounds. Their Taylor remainders
of weighted order zero, cutoff derivatives and inverse frame determinants
are uniformly bounded. The homogeneous model is the same pair $U,V$.
Consequently the convolution-parametrix bounds in [J, §4, pp.848--850]
have common constants and a common finite iteration order. More
explicitly, on the native charts the principal model heat-kernel error is
$((b_\kappa/b_o)^2-1)V^2p_t^H$ times the chart density factor.
Since $b_\kappa(k)/b_o-1=O(|\xi|)$ uniformly, the homogeneous Gaussian
bounds for $V^2p_t^H$ give an error bounded by
$Ct^{-5/2}e^{-cN^2/t}$, whose spatial $L^1$ norm is at most
$Ct^{-1/2}$. Each time convolution therefore gains a factor of order
$t^{1/2}$; the beta-integral constants in any fixed number of iterations
are common. Cutoff errors lie off the local diagonal and have uniform
flat small-time bounds. This verifies directly the uniform error class
used in [J]'s finite parametrix construction. The
uniform off-diagonal Gevrey bound in its Proposition 3 follows from the
same integration-by-parts argument with these bounded coefficients and
the uniform local subelliptic estimate [H, Theorem B.1]. The maximum
principle and finite-cover step in [J, Theorem 2] therefore give common
$C,c,t_0$. This tracks the constants in that proof, rather than taking a
supremum of unexamined fixed-operator constants. The volume denominator
there is comparable to $t^2$ by (10.11)--(10.12). Restriction to $B$ kills
earlier, so domain domination transfers the bound from the compact
extension. Short paths near $q_0$ remain in the chosen chart, giving
(10.13); outside it the distance from $q_0$ has a uniform positive lower
bound. This extension is used only for estimates and changes neither
height killing nor the native operator.

At time one the same extension bounds all killed heat diagonals uniformly.
The gap $\lambda_0$ and the semigroup identity then give
$p_\kappa^B(t,q_0,q)\le C e^{-\lambda_0(t-1)}$ for $t\ge1$,
uniformly on $B$. Integration of (10.13), using
$\int_0^1t^{-2}e^{-cr^2/t}dt\le C'r^{-2}$, proves

$$
G_\kappa(q)\le C N_\kappa(q)^{-2}+C'
\tag{10.14}
$$

on the source chart and a uniform bound on its exterior, including near
the killed height faces. The Green field is positive and finite off
$q_0$; at $q_0$ the contact diagonal asymptotic $ct^{-2}$ from [H,
Theorem B] makes its time integral infinite.

The unweighted Heisenberg Hardy inequality [R, Corollary 3.2], with
$p=2$, $\alpha=1$, homogeneous dimension four, gives
$\int N^{-2}|f|^2\le C_H\int(|Uf|^2+|Vf|^2)$.
Its required strict condition is $1<4/2$.
Use (10.11), a fixed smooth source cutoff, and horizontal localization.
The constant density factor $m_\kappa$ appears on both sides and cancels;
the positive lower bound on $b_\kappa/b_o$ controls the group energy by
$\mathcal E_\kappa$. The bounded remainder and cutoff derivatives
contribute only $B_0\|z\|_2^2$. This proves (10.6) on the smooth core.
Applying it to differences of core approximants proves weighted $L^2$
convergence, identifies the same almost-everywhere function, and extends
(10.6) to exactly $\mathcal F_\kappa^B$.

Finally, free Mosco convergence gives strong free resolvent and heat
convergence. Uniform interior hypoelliptic smoothing upgrades the kernels
to local smooth convergence for positive times, as in [H, Theorem 3.5];
the common semigroup bound is one, the density is fixed, the drift and
potential are zero, and (10.10) verifies its uniform strong Hörmander
hypothesis. The Gaussian off-diagonal and exponential large-time bounds
justify integrating on compact sets away from $q_0$. The source-chart
mass in $\{N_\kappa<r\}$ is at most $Cr^2$, by (10.14) and volume
$r^4$. The charts and inverses are uniformly bounded, so the mass of a
common Euclidean neighborhood of $q_0$ tends uniformly to zero with its
radius. Away from it the Green fields are uniformly bounded, including
the boundary collars. Dominated convergence proves the $L^1$ assertion.
The corresponding height marginal, obtained by testing the free evolution
on functions of height alone, is exactly

$$
\int_{\mathbb T^2}G_\kappa(k,\theta,v)d\theta\,dv
 =\varepsilon^{-2}G_I(k_0,k),\qquad
G_I(a,k)=\frac{(\min(a,k)-l)(u-\max(a,k))}{u-l}.
\tag{10.15}
$$

It supplies the same finite total Green mass for every parameter.
$\square$

## 11. A fixed strict coupling window and the singular two-sign limit

**Theorem 11.1 (closed restricted forms, attained minima and actual limit).**
With the fixed neighborhood and constants of Theorem 10.2, put

$$
g_* =\pi/A,\qquad 0<g<g_*,\qquad
W_\kappa=G_\kappa/(2\pi),\qquad
\mathfrak h_{\kappa,g}[z]
 =\mathcal E_\kappa[z]-g\int_BW_\kappa|z|^2d\nu,
\quad D(\mathfrak h_{\kappa,g})=\mathcal F_\kappa^B.
\tag{11.1}
$$

These are closed semibounded forms on their natural completed horizontal
domains, with the uniform coercivity

$$
\mathfrak h_{\kappa,g}[z]
 \ge\tfrac12\mathcal E_\kappa[z]
             -\frac{g_*B_0}{2\pi}\|z\|_2^2.
\tag{11.2}
$$

Their form operators have compact resolvent. Every normalized infimum
$e_\kappa(g)=\min_{\|z\|_2=1}\mathfrak h_{\kappa,g}[z]$ is finite
and attained. For every fixed $g$ in this one positive interval,

$$
\mathfrak h_{\kappa,g}\longrightarrow\mathfrak h_{0,g}
 \quad\hbox{in shifted Mosco sense},\qquad
e_\kappa(g)\longrightarrow e_0(g)
\tag{11.3}
$$

through either sign. The limit is the native three-coordinate double-wall
point-Green form with coupling $g/(2\pi)$ relative to its unit source.
It is not that form with coupling $g$.

There is a unique nonnegative normalized ground state $z_\kappa$;
it is positive almost everywhere. For this choice,

$$
\begin{gathered}
z_\kappa\to z_0\quad\hbox{strongly in }L^2(B),\\
(\varepsilon\partial_kz_\kappa,R_\kappa z_\kappa)
 \to(\varepsilon\partial_kz_0,R_0z_0)
 \quad\hbox{strongly in }L^2(B)\oplus L^2(B),\\
\int_BG_\kappa|z_\kappa|^2d\nu
 \longrightarrow\int_BG_0|z_0|^2d\nu.
\end{gathered}
\tag{11.4}
$$

Arbitrary normalized complex ground states require fixing their constant
phases, for example by making their inner product with $z_0$ positive
real for all sufficiently small parameters. Without phase fixing the
conclusion is convergence of the ground-state lines.

Proof. Equation (10.6) gives relative form bound
$gA/(2\pi)<1/2$. KLMN [T, Theorem 6.24] proves closedness on exactly
$\mathcal F_\kappa^B$, norm equivalence and (11.2).
The attractive operator is defined by the variational domain

$$
D(\mathscr H_{\kappa,g})=
 \{z\in\mathcal F_\kappa^B:\ \exists F\in L^2(B), \mathfrak h_{\kappa,g}(z,w)=\langle F,w\rangle \text{ for all }w\in\mathcal F_\kappa^B\},
 \qquad\mathscr H_{\kappa,g}z=F.
$$

This domain is not replaced by an intersection of a free operator domain
and a multiplier domain. Collective compactness of the free energy balls
then gives compactness of the shifted attractive form balls. In particular each individual form
has compact resolvent. Alternatively, a normalized minimizing sequence
is bounded in the free form norm, has a strongly $L^2$ convergent
subsequence, and a weakly convergent subsequence in the closed attractive
form norm; weak lower semicontinuity proves attainment and finiteness.

We give the singular lower-limit argument explicitly. Fix $g$ and
$\kappa_j\to0$, and suppose $u_j\rightharpoonup u$ in $L^2$ with
bounded shifted attractive energy. By (11.2) and collective compactness,
a subsequence converges strongly to $u$, has bounded free energy, and
free lower semicontinuity puts $u\in\mathcal F_0^B$.
In the source charts choose smooth real cutoffs
$\chi_{\kappa,r}^2+\vartheta_{\kappa,r}^2=1$ with
$\chi=1$ for $N_\kappa\le r$, $\chi=0$ for $N_\kappa\ge2r$.
They can be obtained as cosine and sine of a fixed smooth function of
$N_\kappa/r$ constant near both endpoints. They satisfy

$$
\varepsilon^2|\partial_k\chi_{\kappa,r}|^2+
 |R_\kappa\chi_{\kappa,r}|^2+
\varepsilon^2|\partial_k\vartheta_{\kappa,r}|^2+
 |R_\kappa\vartheta_{\kappa,r}|^2
 \le Cr^{-2}\mathbf1_{\{r<N_\kappa<2r\}}.
\tag{11.5}
$$

For each fixed $r$ these cutoffs and their derivatives converge smoothly
as $\kappa\to0$. Horizontal IMS is an identity for both completed forms;
the potential term splits without a remainder. Denote its nonnegative
kinetic error by $\mathcal R_{\kappa,r}[u]$, the integral of the left
side of (11.5) against $|u|^2$.
The inner form is at least $-gB_0\|\chi u_j\|_2^2/(2\pi)$ by
(10.6). For the outer form, the Green multipliers are uniformly bounded
and converge pointwise off the pole; strong $L^2$ convergence therefore
makes their integrals converge. Free lower semicontinuity applies to the
outer cutoff functions. Consequently

$$
\liminf_j\mathfrak h_{\kappa_j,g}[u_j]
 \ge \mathfrak h_{0,g}[\vartheta_{0,r}u]
       -\frac{gB_0}{2\pi}\|\chi_{0,r}u\|_2^2
       -\mathcal R_{0,r}[u].
\tag{11.6}
$$

The local Hardy inequality also gives
$N_0^{-1}u\in L^2$ near the pole. Thus
$r^{-2}\int_{r<N_0<2r}|u|^2\to0$ by absolute continuity of that
weighted integral. Equation (11.5) implies
$\mathcal R_{0,r}[u]\to0$, and the product rule gives
$\chi_{0,r}u\to0$ in the free form norm. The potential follows by
(10.6). Hence $\vartheta_{0,r}u\to u$ in the attractive form norm;
letting $r\downarrow0$ in (11.6) proves the required lower bound.
This is the step that retains the inverse-square singularity.

Recovery follows first for a fixed compact smooth test: its free energy
converges by smooth coefficient convergence, and its potential converges
by $L^1$ Green convergence. Approximate a general $u\in\mathcal F_0^B$
in its form norm by such tests and use a diagonal sequence. A fixed shift
larger than $g_*B_0/(2\pi)$ makes all forms nonnegative, so these lower
and recovery statements are precisely shifted Mosco convergence.
They do not assume compactness of the critical potential multiplier.

Normalized recovery gives $\limsup e_{\kappa_j}(g)\le e_0(g)$.
For actual normalized minimizers, (11.2), a fixed finite trial bound and
collective compactness give a strongly convergent subsequence with
norm-one limit. The lower bound just proved gives the reverse inequality
and identifies every such limit as a limit-form minimizer. This proves
the minimum convergence in (11.3).

The modulus contraction for the two real fields decreases kinetic energy
and leaves the potential unchanged, so a nonnegative ground state exists.
To check simplicity and positivity with the singular potential, truncate
$W_\kappa$ from above. For a bounded nonnegative truncation, the
Trotter product formula gives
$e^{-t(\mathscr L_\kappa-g\min(W_\kappa,M))}f
 \ge e^{-t\mathscr L_\kappa}f$ for $f\ge0$.
The decreasing truncated forms have the same lower bound and converge
on the natural domain to the closed form (11.1); the monotone closed-form
convergence theorem gives strong resolvent, hence heat convergence.
The inequality passes to the limit. The free heat kernel is strictly
positive: (10.10) gives bracket accessibility on the connected cylinder,
and the killed free heat positivity principle applies with the same
height boundary. Thus the restricted attractive heat operator is
positivity improving. The elementary positive-eigenvector argument of
[T, Theorem 10.11] applies on this $L^2(B)$ as well: its proof uses only
selfadjointness, reality and positivity improvement. The lowest
eigenvalue is simple and its nonnegative eigenvector is positive almost
everywhere. These are restricted semigroups only.

We finally verify the stronger assertions in (11.4), rather than infer
them from compactness alone. Along a convergent minimizing subsequence
write $u_j=z_{\kappa_j}$, $u=z_0$ and
$c_g=1-gA/(2\pi)>0$. The IMS identity and (10.6) give

$$
\begin{aligned}
c_g\limsup_j\mathcal E_{\kappa_j}
 [\chi_{\kappa_j,r}u_j]
 &\le e_0(g)-\mathfrak h_{0,g}[\vartheta_{0,r}u]
       +\mathcal R_{0,r}[u]
       +\frac{gB_0}{2\pi}\|\chi_{0,r}u\|_2^2\\
 &=\mathfrak h_{0,g}[\chi_{0,r}u]
       +\frac{gB_0}{2\pi}\|\chi_{0,r}u\|_2^2
 \longrightarrow0\quad(r\downarrow0).
\end{aligned}
\tag{11.7}
$$

The potential of these inner cutoffs tends uniformly to zero by (10.6).
Outside them bounded multipliers and strong $L^2$ convergence give
potential convergence. This proves the last line of (11.4).
The energy identity then gives
$\mathcal E_{\kappa_j}[u_j]\to\mathcal E_0[u]$.
Distributional testing, smooth coefficient convergence and the uniform
energy bound identify the weak limits of the two horizontal derivatives
as $(\varepsilon\partial_ku,R_0u)$. Convergence of their combined squared
norm makes that convergence strong. Positivity and simplicity identify
all subsequential limits, so the whole positive family converges.
The same argument applies after the stated constant-phase choice.

At zero parameter, $b_0=1/2$ and $s_0=H$. In the actual unimodular
angles $(\alpha,\beta)=(\theta-v,\theta)$,
$R_0=\tfrac12\partial_\alpha+
(\tfrac12-k/(2H))\partial_\beta$. This is exactly the native double-wall
operator of [G, Definition 4.1], with $r=2H$, the same density and clock.
Its unit point source is $G_0$. Equation (11.1) therefore has native
coupling $g/(2\pi)$, as claimed. $\square$

## 12. Same-source normalization, lowering and local omitted-phase leakage

**Theorem 12.1 (same-source lowering and checked omitted-phase leakage).**
For every nonzero $\kappa\in K$, the same full point-source field obeys

$$
\begin{aligned}
\int_{\mathbb T_D}p_\kappa^\Omega(t,o,(q,D))dD
 &=p_\kappa^B(t,q_0,q),\\
\int_{\mathbb T_D}\Gamma_{\kappa,o}(q,D)dD&=G_\kappa(q),\\
\frac1{2\pi}\int_{\mathbb T_D}\Gamma_{\kappa,o}(q,D)dD
 &=W_\kappa(q),\\
T_\kappa[Jz]-g\int_\Omega\Gamma_{\kappa,o}|Jz|^2d\mu
 &=\mathfrak h_{\kappa,g}[z].
\end{aligned}
\tag{12.1}
$$

The Green identity is an extended pointwise integral, also in $L^1(B)$;
the last identity is finite on every natural restricted form domain.
Uniform smearing of the original pole around its hidden circle gives the
different full-space field

$$
\frac1{2\pi}\int_{\mathbb T}
 \Gamma_{\kappa,(q_0,s)}(q,D)ds=W_\kappa(q).
\tag{12.2}
$$

Its source is $\delta_{q_0}\otimes dD/(2\pi)$ and has total mass one.
Viewed as a field on $B$, $W_\kappa$ has source charge $1/(2\pi)$,
whereas $G_\kappa$ has charge one. Theorem 11.1 concerns the original
point field evaluated on the declared state class. It makes no
full-space smeared-source stability assertion. In addition, the normalized
test (12.3) strictly lowers the free minimum as in (12.4), and the original
attractive differential expression fails to preserve the retained class
on the checked local cores below.

Proof. The marginal and smearing identities are reused intermediate
steps in this same-source comparison. Apply the free semigroup identity
(10.7) to bounded base tests.
Smooth interior kernels and compactness of the hidden circle make the
heat marginal pointwise. Tonelli gives the Green marginal and its
$L^1$ version, using (10.15). The conditional Haar average divides that
integral by the circle length. Since $|Jz|^2=|z|^2/(2\pi)$, Tonelli and
(10.6) give the form identity, including finiteness and weighted
polarization. Hidden translation symmetry of the free kernel gives
(12.2); testing its free equation identifies the displayed smeared source.
These are the marginal and source-smearing mechanisms of Theorem 3.1,
now applied to the full-four/retained-three family after its actual free
domains have been checked.

For the lowering assertion put $d=u-l$ and

$$
\phi(k)=\sqrt{2/d}\sin\frac{\pi(k-l)}d,\qquad
z_*(k,\theta,v)=\phi(k)/(2\pi),\qquad
\mathcal V_*=
 \frac1{(2\pi)^3\varepsilon^2}
 \int_I G_I(k_0,k)|\phi(k)|^2dk>0.
\tag{12.3}
$$

Then $z_*\in\mathcal F_\kappa^B$, $\|z_*\|_2=1$ and

$$
\min_{\|z\|_2=1}\mathcal E_\kappa[z]=\lambda_0,\qquad
e_\kappa(g)\le\lambda_0-g\mathcal V_*<\lambda_0
\quad(\kappa\in K,\ 0<g<g_*).
\tag{12.4}
$$

The zero angular mode in (10.8) includes $\phi\in H^1_0(I)$,
so the test is in the completed domain with kinetic value $\lambda_0$.
The height Poincaré bound proves it is the free minimum. Equation (10.15)
and the exact $1/(2\pi)$ in (12.1) give its attractive expectation
$\mathcal V_*$, with all three factors of circle length retained.
The height Green is positive in $I$, proving strict positivity and
(12.4). This compares with the actual free minimum; it does not assert
that the ground energy is negative relative to zero.

For the local noninvariance assertion, for each $\kappa\ne0$ and $g>0$,
the differential expression $L_\kappa-g\Gamma_{\kappa,o}$ fails to preserve the
$D$-independent class, already on compact smooth tests supported away
from the source height. This statement uses no semibounded full
attractive operator or full attractive heat evolution.

Define the actual hidden harmonic, with all angular measures
unnormalized, by

$$
F_\kappa(k)=\int_{\mathbb T^3}
 \Gamma_{\kappa,o}(k,\theta,v,D)e^{-iD}\,d\theta\,dv\,dD.
\tag{12.5}
$$

Fourier decomposition of the free height operator, or its heat integral,
gives

$$
F_\kappa(k)=
 \left(-\varepsilon^2\partial_k^2+C_\kappa(k)^2\right)^{-1}_D(k_0,k)>0.
\tag{12.6}
$$

The subscript denotes Dirichlet height endpoints. To check its charge,
the full angular Fourier expansion has factor $(2\pi)^{-3}$; integration
in (12.5) cancels that factor. Thus its height source is exactly
$\delta_{k_0}$. Positivity follows from the one-dimensional positive
Dirichlet heat kernel with bounded nonnegative potential $C_\kappa^2$.
In particular it is positive at every $k\ne k_0$ in $I$.

Choose any nonnegative nonzero $\eta\in C_c^\infty(I\setminus\{k_0\})$
and use the $D$-independent full test
$f=\eta(k)/(2\pi)^{3/2}$. It is in the full free operator domain by
integration by parts against the completed form domain, with
$L_\kappa f=-\varepsilon^2\eta''/(2\pi)^{3/2}$.
The full Green field is smooth with bounded derivatives on this entire
phase-torus height support, so $\Gamma_{\kappa,o}f$ is another compact
smooth test there. Consequently $f$ lies in the domain of the symmetric
minimal attractive differential operator on
$C_c^\infty(\Omega\setminus\{o\})$, and every expression used here is
an actual $L^2$ function on that checked local core.
The angular $e^{iD}$ coefficient of its attractive image, integrated over
the two retained circles, is
$-g\eta(k)F_\kappa(k)/(2\pi)^{3/2}$, which is nonzero.
A $D$-independent function would have zero such coefficient. This proves
local leakage of the same original point multiplier.

The full unrestricted point-source form is nevertheless unbounded below
for every $g>0$, by [G, Theorem 3.1]: $X=Y$ and $X+Y\ne2H$ put each
nonzero parameter exactly on its single-wall row. Restricting tests has
not altered that theorem or repaired its form. In particular the stable
restricted operators in Theorem 11.1 cannot be identified with a
compression of a semibounded full attractive heat semigroup. The
semiboundedness hypothesis used in §6's double-wall compressed-evolution
argument fails for this nearby full point-source problem. $\square$

## 13. Supplier correspondence and mathematical meaning of the limit

**Definition 13.1 (exact reuse and the parameter-uniform increment).**
The following supplier map fixes the mathematical scope of the appendix.

| Supplier | Exact use and nontransferred condition |
| --- | --- |
| [N, Theorems 8.2, 8.4 and §§8.5,10.2--10.3]; [G, Definition 12.1 and Calculation 12.2] | Original probabilities, arbitrary preparation translation, negative phases, actual circle periods, full prefix rays, the declared $q,D$ change and the rational coefficients (10.2). Reachability does not prepare analytic amplitudes. The full nearby dimension is four; its retained base is three. |
| This volume, Theorems 2.1 and 3.1; [Native free diffusion quotient rigidity](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md), Theorem 3.1 | Averaged-core form reduction, variational operator reduction, killed free observation laws, point-Green marginal and normalized source smearing. The abstract identities are reused inside (10.7) and (12.1), not counted as new quotient results. The older bottom-output base is two-dimensional and elliptic; it is not the present $B$. |
| [G, Propositions 4.2--4.3 and Theorem 5.1] | Fixed double-wall Heisenberg normalization and strict Green stability supply the limit interpretation. They do not supply a common nearby parameter window or singular-form convergence. In (10.11), $m_0=\varepsilon^2/(4H)=\varepsilon^2/(2r)$ exactly recovers their Haar factor. |
| [G, Theorem 3.1] | Full point-source collapse at every nonzero single-wall parameter. The point source, state class and coupling are those of (10.4); the collapse remains in force. |
| [J] D. S. Jerison and A. Sánchez-Calle, *Estimates for the Heat Kernel for a Sum of Squares of Vector Fields*, Indiana Univ. Math. J. 35 (1986), 835--854, [primary text](https://www.iumj.indiana.edu/IUMJ/FTDLOAD/1986/35/35043/pdf), Proposition 3 and Theorem 2, §§3--4 | The upper bound is $C\mu(B(x,\sqrt t))^{-1}e^{-cd(x,y)^2/t}$ for smooth Hörmander fields on a compact manifold. The contact extension, common charts, bounded parametrix coefficients, common subelliptic constants and volume exponent four are checked in the proof of Theorem 10.2; Dirichlet domain domination returns to the actual cylinder. No full four-coordinate uniform heat bound is imported. |
| [H], Theorems 3.2, 3.5 and B.1 | Uniform strong Hörmander generation, smooth parameter dependence, positive smooth density and uniform semigroup bounds are required. They hold for the retained free family by (10.10), not for the degenerate four-coordinate limit. Free kernel localization and positive-time convergence do not by themselves prove convergence of the singular attractive forms. |
| [R], Corollary 3.2 | The unweighted inequality uses $p=2$, $\alpha=1$, $Q=4$ and the Lebesgue Heisenberg fields $U,V$ with gauge (10.12). The local density factor and the varying horizontal coefficient are explicitly retained in (10.11). It is an intermediate estimate, not a replacement potential. |
| [T], Theorem 2.13, Lemma 2.24, Theorem 6.24 and the positive-eigenvector argument of Theorem 10.11 | Closed-form representation, reduction, strict relative-form perturbation and simplicity. The perturbation bound here is $gA/(2\pi)<1/2$; compactness and the critical lower limit are proved separately. The positivity argument is on $L^2(B)$ and uses restricted heat operators only. |
| Arendt--Dier--Ouhabaz, [arXiv:1303.1167v1](https://arxiv.org/pdf/1303.1167v1), Theorem 2.2 | Its closed-form convex-set criterion assumes projection preserves the form domain and the cross-form inequality. Free Haar averaging meets those conditions by (10.7). It supplies no invariant class for the original singular multiplier; (12.5)--(12.6) give a direct checked-core obstruction. |
| Gouasmi--Parish--Duraisamy [M], §2.1; the present volume, §6 | Projection, initial hidden data and subsequent feedback are distinct. Formal elimination is not a semibounded full-source evolution, and the older compressed-semigroup calculation is not applied across its failed stability hypothesis. |
| Pinned Mathlib $\mathtt{db584cd6d46c92f209a44c0f1c829460d327499d}$, `Analysis/FunctionalSpaces/SobolevInequality` and `Analysis/Distribution/Sobolev`; native `Quantum/Fibers/FiniteRectangleTransport`, including private leg and polygon proofs | The Mathlib results concern Euclidean derivative Sobolev estimates and Bessel-potential spaces, not this horizontal point-Green singular family. The native private proofs supply lawful finite legs and probability/phase compatibility, not (10.6) or (11.3). No compiled application or new Lean result is asserted. |

The Gaussian, Hardy, representation and projection tools are
`literature-attested`. The added `repo-derived` result is their native
fixed-window combination: the exact varying contact chart and Fourier
tightness, uniform same-point Green control, the critical cutoff
lower-limit argument, and the resulting actual minimum and ground-state
limit with its source factor. No general projection identity or rewritten
fixed-wall theorem is counted as new content. This correspondence makes
no exhaustive-search or global originality claim.

**Proposition 13.2 (scope of the three-coordinate conclusion).** Within
Definition 10.1, a stable same-field restricted energy and its two-sign
native limit exist on the declared $D$-independent analytic state class.
They do not imply stability of the original nearby full point-source
model or invariance of that state class under its attractive expression.
They imply neither physical spatial dimension three nor an operation
that realizes the restriction.

Proof. Theorem 11.1 gives the restricted statement, and Theorem 12.1
fixes its exact same-field and unit-source meaning and proves both the
surviving full instability and the local noninvariance.
A $q$-only free evolution, an energy evaluated on $Jz$, the energy of a
different smeared source, and the full original point-source energy are
therefore distinct mathematical tasks even when some restricted numerical
values agree. The native full coherence menu still distinguishes the
omitted phase. No projection/reset controller, amplitude preparation,
acquired observation, finite precision law, spatial-axis map or mean
selection appears among the premises. None can consequently be inferred
as a realization of these analytic conclusions. All diffusion, attraction,
covariance, density, clock, killing and amplitude-space assumptions remain
explicit added mathematics. The sufficient window is not sharp; critical
coupling equality, moving-data uniformity and $\varepsilon\to0$ uniformity
are outside the assertions. $\square$

## 追加锚（本行以下为增补区）

## 14. Finite hidden Fourier sectors of the unchanged native point field

**Definition 14.1 (source, sector and natural domain).** Fix Definition
10.1, including its immutable $\kappa\ne0$, preparation, probabilities,
$\varepsilon>0$, pole $o=(q_0,0)$, raw measures, and three $2\pi$ circles.
Write $\Gamma_\kappa=\Gamma_{\kappa,o}$. The fields are still exactly
$P,Q_\kappa$ of (10.3), and the Green field is still
$\int_0^\infty p_\kappa^\Omega(t,o,\cdot)dt$ for $e^{-tL_\kappa}$,
with Dirichlet height killing. In particular no source averaging, spatial
cap, time cutoff or change of clock is made.
The native guard remains $k+a(t)\in J_\kappa$
with $J_\kappa=(\max(0,2\kappa),H+\kappa)$; restriction to $I$ is the
additional whole-path guard of [G, Definition 12.1]. Refusal and Stop,
actual common histories, preparation rotations and the original full read
menu are retained. The analytic state spaces below add no native command.

Let $\varnothing\ne S\subset\mathbb Z$ be finite, $M=|S|$, and put

$$
\begin{aligned}
\mathcal H_S&=\left\{f(q,D)=(2\pi)^{-1/2}
                \sum_{n\in S}z_n(q)e^{inD}:z_n\in L^2(B,d\nu)\right\},\\
t_{\kappa,n}[z]&=\int_B\left(\varepsilon^2|\partial_kz|^2+
                  |(R_\kappa+inC_\kappa)z|^2\right)d\nu,\\
\mathcal F_{\kappa,S}&=\overline{
 (2\pi)^{-1/2}\sum_{n\in S}C_c^\infty(B)e^{inD}
 }^{(\|\cdot\|_2^2+T_\kappa)^{1/2}},\\
T_{\kappa,S}[f]&=\sum_{n\in S}t_{\kappa,n}[z_n],\qquad
V_{\kappa,S}[f]=\int_\Omega\Gamma_\kappa|f|^2d\mu,\\
h_{\kappa,S,g}[f]&=T_{\kappa,S}[f]-gV_{\kappa,S}[f].
\end{aligned}
\tag{14.1}
$$

Thus $\|f\|_2^2=\sum_n\|z_n\|_2^2$. This is an explicitly changed
analytic amplitude class; the multiplier is the original unsmoothed full
point field. No bound on the two retained angular frequencies is imposed.

**Proposition 14.2 (completed sector and its actual potential).** The
sector is a reducing subspace for the free operator. Its completed form
domain is exactly

$$
\mathcal F_{\kappa,S}=
 \left\{(2\pi)^{-1/2}\sum_{n\in S}z_ne^{inD}:
                      z_n\in\mathcal F_\kappa^B\right\}.
\tag{14.2}
$$

The free sector form is densely defined and closed on $\mathcal H_S$,
and its form domain embeds compactly in that Hilbert space. Its potential
in (14.1) is finite on this whole domain and is the actual point-field
integral, with the exact formula

$$
\begin{gathered}
\gamma_{\kappa,j}(q)=\frac1{2\pi}\int_{\mathbb T}
                     \Gamma_\kappa(q,D)e^{-ijD}dD,\qquad
\gamma_{\kappa,0}=\frac{G_\kappa}{2\pi},\\
V_{\kappa,S}[f]=\int_B\sum_{n,m\in S}
       \gamma_{\kappa,m-n}(q)z_n(q)\overline{z_m(q)}d\nu.
\end{gathered}
\tag{14.3}
$$

The coefficients are defined pointwise for $q\ne q_0$ and as $L^1$
functions across the source. No finite value at $q_0$ is required.

Proof. Fourier projection in $D$ preserves the smooth height core and
commutes with both free fields. Parseval gives the kinetic identity in
(14.1), and projection is contractive for the free form norm. This proves
free reduction by the same closed-domain argument as (10.7).
Since $C_\kappa$ is bounded, for every $0<\delta<1$,

$$
(1-\delta)\mathcal E_\kappa[z]-C_{\delta,n}\|z\|_2^2
 \le t_{\kappa,n}[z]
 \le(1+\delta)\mathcal E_\kappa[z]+C_{\delta,n}\|z\|_2^2.
\tag{14.4}
$$

Core completion gives (14.2) with equivalent norms. Compactness now follows
from Theorem 10.2 and the finite direct sum. These are form domains, not
assertions about intersection domains of differential operators.

Pointwise Cauchy--Schwarz and the same-source marginal (12.1) give

$$
|f(q,D)|^2\le\frac{M}{2\pi}\sum_{n\in S}|z_n(q)|^2,
\qquad
0\le V_{\kappa,S}[f]\le\frac{M}{2\pi}
               \sum_n\int_BG_\kappa|z_n|^2d\nu.
\tag{14.5}
$$

Theorem 10.2 makes this finite and continuous in the completed kinetic
norm. The marginal also gives
$|\gamma_{\kappa,j}|\le G_\kappa/(2\pi)$ and
$\gamma_{\kappa,-j}=\overline{\gamma_{\kappa,j}}$.
Fubini first on the smooth core and then weighted $L^2$ completion proves
(14.3). This argument identifies the integral itself, rather than defining
an unrelated matrix potential by completion. $\square$

## 15. The common Green coefficient of all finitely many mode differences

**Definition 15.1 (exact source chart and sharp supplied constant).** Use
$(\xi,\eta,\zeta)$, $b_o=b_\kappa(k_0)$ and $m_\kappa$ of (10.11).
Set

$$
\begin{gathered}
\tau=\zeta-\xi\eta/2,\qquad X=(\xi,\eta,\tau),\qquad
R(X)=\big((\xi^2+\eta^2)^2+16\tau^2\big)^{1/4},\\
U=\partial_\xi-\tfrac\eta2\partial_\tau,\qquad
V=\partial_\eta+\tfrac\xi2\partial_\tau,\qquad
\delta_rX=(r\xi,r\eta,r^2\tau),\\
\varepsilon P=U,\quad R_\kappa=a_\kappa^{\rm loc}(X)V,
\quad a_\kappa^{\rm loc}(X)=b_\kappa(k_0+\varepsilon\xi)/b_o,\quad
 d\nu=m_\kappa dX,\quad
 m_\kappa=\frac{\varepsilon^2b_o^2}{H+\kappa}.
\end{gathered}
\tag{15.1}
$$

Denote this local chart by $\Psi_\kappa$. The symbol
$a_\kappa^{\rm loc}$ is distinct from $a_\kappa$ in (10.2).
The radius $R$ is used for exact coefficients. The gauge $N$ in (10.12)
is comparable to $R$, but is not substituted for it in a fundamental
solution or a sharp constant.

Let $\lambda_H$ be exactly $\lambda_0$ of
[V, Definition 10.1 and Theorem 10.2], where
[V] denotes [Variable-coefficient Green stability](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md).
Explicitly it is the lowest eigenvalue of

$$
-4(\cos a\,\phi')'+\cos a\,\phi=\lambda_H\phi,
\qquad -\pi/2<a<\pi/2,
\tag{15.2}
$$

on $\{b\in L^2: b\in AC_{\rm loc},\sqrt{\cos a}\,b'\in L^2\}$,
with natural endpoint conditions, not Dirichlet endpoint conditions.
Thus $0<\lambda_H<2/\pi$ and the supplied sharp inequality is

$$
\int_{\mathbb R^3}(|Uu|^2+|Vu|^2)dX
 \ge\lambda_H\int_{\mathbb R^3}R^{-2}|u|^2dX.
\tag{15.3}
$$

Its class contains all complex compact punctured smooth tests, including
all angular and logarithmic radial frequencies. The supplied annular
sharpness tests are also used below. No weighted radial Hardy constant
or symmetry-restricted constant is substituted.

**Lemma 15.2 (same-source finite-mode Green coefficients).** For every
finite $F\subset\mathbb Z$ there are a source neighborhood and finite
constants $C_F,B_F$ such that, for $j\in F$ and $0<R(X)<r_0$,

$$
\left|\gamma_{\kappa,j}(\Psi_\kappa^{-1}X)
       -\frac{1}{4\pi^2m_\kappa}R(X)^{-2}\right|
 \le C_FR(X)^{-1}.
\tag{15.4}
$$

On the exterior of that neighborhood $|\gamma_{\kappa,j}|\le B_F$.
The coefficients are those of the full killed-time Green field in
(14.3). Both estimates can be chosen uniformly for the base/modal
extension over any closed parameter interval $[-a,a]\subset K$.
For this last statement the full-source interpretation is asserted only
for $\kappa\ne0$; at zero it means the modal kernels defined in the proof.

Proof. Let $L_{\kappa,j}$ be the operator of $t_{\kappa,j}$ on
$L^2(B,d\nu)$ and $K_{\kappa,j}(t;q,p)$ its kernel, in the convention
$e^{-tL_{\kappa,j}}z(q)=\int K_{\kappa,j}(t;q,p)z(p)d\nu(p)$.
Hidden Fourier extraction from the free full kernel gives

$$
\gamma_{\kappa,j}(q)=\frac1{2\pi}G_{\kappa,j}(q,q_0),\qquad
G_{\kappa,j}(q,p)=\int_0^\infty K_{\kappa,j}(t;q,p)dt.
\tag{15.5}
$$

The factor follows from the orthonormal hidden basis
$e^{ijD}/\sqrt{2\pi}$ evaluated at the pole $D=0$.
It is not a change of the point source's unit charge.

There is a useful direct domination, without any attractive evolution.
Along the retained free killed diffusion in Theorem 10.2, lift
$dD_t=\sqrt2C_\kappa(K_t)dB_t^2$, with the same $B^2$ that drives both
retained phases. For a test $z(q)e^{ijD}$, its free conditional expectation
contains the unit-modulus factor
$\exp(ij\sqrt2\int C_\kappa(K_s)dB_s^2)$.
The Itô correction is exactly the $-j^2C_\kappa^2$ term, and the cross
variation gives $2ijC_\kappa R_\kappa$; $R_\kappa C_\kappa=0$.
Consequently its generator is
$\varepsilon^2\partial_k^2+(R_\kappa+ijC_\kappa)^2$ with the same
height killing. Taking absolute values proves semigroup domination and,
by smooth kernels,

$$
|K_{\kappa,j}(t;q,p)|\le p_\kappa^B(t,q,p),\qquad
|G_{\kappa,j}(q,p)|\le G_\kappa^B(q,p),
\tag{15.6}
$$

where $G_\kappa^B(q,p)=\int_0^\infty p_\kappa^B(t,q,p)dt$.
Here $G_\kappa(q)=G_\kappa^B(q,q_0)$.
These formulas also define the modal extension at $\kappa=0$, where
$C_0=0$. No full four-coordinate point kernel is invoked at zero.

The contact Gaussian and localization argument of Theorem 10.2, with
its center allowed to range over the compact support of a source-chart
cutoff, gives uniformly

$$
G_\kappa^B(q,p)\le C d_\kappa(q,p)^{-2}+C,
\qquad
\int_{t_0}^\infty |K_{\kappa,j}(t;q,p)|dt\le C_{t_0}.
\tag{15.7}
$$

In the first bound $q,p$ lie in a fixed larger source chart and
$d_\kappa$ is its horizontal distance; outside a smaller source
neighborhood the kernel with source $q_0$ is bounded. To check the
uniform use, (10.10) keeps the contact determinant separated from zero,
(15.1) gives ball volume comparable to $r^4$, and all coefficient and
inverse-chart derivatives are bounded on the compact parameter set.
The compact contact extension and domain domination used for (10.13)
apply at every such center. The common height gap
$\varepsilon^2\pi^2/(u-l)^2$, positive-time diagonal bounds and the
semigroup identity give the second estimate and the bounded term of
the first. Thus (15.7) includes the entire large-time tail; it is not an
integration of a tangent limit with an uncontrolled tail.
The classical intermediate upper Gaussian estimate is [J, Theorem 2,
p.849]; its lifting/finite-iteration construction on pp.848--850 has
bounded coefficients for this compact contact family, exactly as tracked
in Theorem 10.2. Interior Dirichlet localization is also [H, Theorem 3.2]
under its uniform strong Hörmander and uniform semigroup hypotheses.

In (15.1), put $c_\kappa(X)=C_\kappa(k_0+\varepsilon\xi)$ and
$a=a_\kappa^{\rm loc}$. Both depend on $\xi$ alone, so $Va=Vc_\kappa=0$.
The exact modal expression is

$$
L_{\kappa,j}=-U^2-a^2V^2-2ijac_\kappa V+j^2c_\kappa^2.
\tag{15.8}
$$

Let $G_H=(2\pi m_\kappa)^{-1}R^{-2}$.
The source normalization is the one in [V, (10.7)]: the outward flux
of $-\nabla_HR^{-2}$ is $2\pi$, and $d\nu=m_\kappa dX$.
Choose a smooth cutoff $\chi$ equal to one near zero inside the chart.
Since $a(0)=1$, $a-1=O(R)$ and
$\nabla_H^d R^{-2}=O(R^{-2-d})$ for $d=1,2$, (15.8) yields, in
distributions relative to $d\nu$,

$$
L_{\kappa,j}(\chi G_H)=\delta_{q_0}+F_{\kappa,j},\qquad
|F_{\kappa,j}(X)|\le C_F R(X)^{-3}\quad(0<R<r_0).
\tag{15.9}
$$

The residual is compactly supported and smooth off zero. Its order
$R^{-3}$ is locally integrable in volume dimension four. The terms
$-2ijac_\kappa VG_H$ and $j^2c_\kappa^2G_H$ have orders at most
$R^{-3}$ and $R^{-2}$. No modal term changes the delta coefficient:
the coefficient error in the principal flux tends to zero as $R\to0$,
and the first-order flux is $O(R)$.
All these bounds are uniform for finitely many $j$ on $[-a,a]$.

The exact residual resolvent identity, with the full Dirichlet resolvent,
is

$$
G_{\kappa,j}(q,q_0)=\chi(q)G_H(q)
 -\int_B G_{\kappa,j}(q,p)F_{\kappa,j}(p)d\nu(p).
\tag{15.10}
$$

For justification, test (15.9) against $L_{\kappa,j}^{-1}\psi$ with
$\psi\in C_c^\infty(B)$. Local hypoellipticity makes this inverse smooth
near the cutoff support. It is bounded, since (15.6), short-time
$L^\infty$ contraction of the base semigroup and the common gap control
its resolvent on bounded data. Integrability of $F_{\kappa,j}$ permits
absolute Fubini; self-adjointness of the modal resolvent, with complex
conjugation when moving it between slots, gives (15.10) in distributions.
It holds pointwise off $q_0$ by the smooth resolvent representative.
This argument does not assume $G_H$ belongs to the kinetic domain.

For $s=R(q)$, the integral in (15.10) is $O(s^{-1})$.
Indeed split its source-chart part into $R(p)<c s$, $R(p)\asymp s$,
and $R(p)>C s$. In the first part $d_\kappa(p,q)\asymp s$ and
$\int_{R<cs}R^{-3}dX=O(s)$, giving $O(s^{-1})$ by (15.7).
In the middle part the residual is $O(s^{-3})$ and
$\int_{d_\kappa(p,q)<C's}d_\kappa(p,q)^{-2}d\nu(p)=O(s^2)$.
In the last part distance is comparable to $R(p)$ and the radial
integral is $O(\int_{Cs}^{r_0}r^{-2}dr)=O(s^{-1})$.
The bounded kernel term and the smooth cutoff annulus contribute $O(1)$.
The triangle comparisons and volumes are uniform by (15.1).
Finally divide by $2\pi$ in (15.5), proving (15.4), including its
normalization and complete killed-time contribution. $\square$

## 16. The exact strict stability boundary in each finite native sector

**Theorem 16.1 (sharp strict finite-sector threshold).** With the source
of Definition 14.1 and the full-complex $\lambda_H$ of (15.2), put

$$
g_S(\kappa)=\frac{4\pi^2m_\kappa\lambda_H}{M}.
\tag{16.1}
$$

For every $0<g<g_S(\kappa)$, $h_{\kappa,S,g}$ is a densely defined
closed semibounded Hermitian form on exactly $\mathcal F_{\kappa,S}$.
For some $c>0$ and finite $B$,

$$
h_{\kappa,S,g}[f]\ge cT_{\kappa,S}[f]-B\|f\|_2^2.
\tag{16.2}
$$

Its sufficiently shifted form norm is equivalent to the natural kinetic
norm. Its representation operator on $\mathcal H_S$ has compact
resolvent, and $\inf_{\|f\|_2=1}h_{\kappa,S,g}[f]$ is finite and
attained in $\mathcal F_{\kappa,S}$.
For every $g>g_S(\kappa)$ there are normalized smooth sector functions,
supported away from the full pole, whose energies tend to $-\infty$.
No assertion here concerns $g=g_S(\kappa)$, including closure,
completion or attainment at equality.

Proof. Apply Lemma 15.2 to $F=S-S$. With
$c_{G,\kappa}=(4\pi^2m_\kappa)^{-1}$, its local matrix has the form

$$
\big(\gamma_{\kappa,m-n}(q)\big)_{m,n\in S}
 = c_{G,\kappa}R(q)^{-2}\mathbf1\mathbf1^*+\mathcal R_\kappa(q),
\qquad \|\mathcal R_\kappa(q)\|\le C_S R(q)^{-1}.
\tag{16.3}
$$

Here $\mathbf1$ has $M$ entries equal to one. Its rank-one matrix has
largest eigenvalue $M$. This coefficient identity, not just a marginal
inequality, determines both directions of the threshold.

For detail on localization, the elementary diamagnetic chain rule gives

$$
\mathcal E_\kappa[|z|]\le t_{\kappa,n}[z].
\tag{16.4}
$$

For the retained direction this follows from
$R_\kappa|z|=\operatorname{Re}(\overline z(R_\kappa+inC_\kappa)z)/|z|$
on $z\ne0$; regularize the modulus and pass to the limit to include its
zero set and the completed domain. The height direction is the ordinary
modulus inequality. On a source neighborhood of radius $b$,
$a_\kappa^{\rm loc}=1+O(b)$, so (15.3), applied to a source cutoff
of $|z|$, gives a localized bound with leading constant arbitrarily close
to $1/\lambda_H$ relative to $t_{\kappa,n}$.
A two-cutoff partition $\chi_0^2+\chi_1^2=1$ avoids a fixed factor loss:

$$
\sum_{i=0}^1t_{\kappa,n}[\chi_i z]
 =t_{\kappa,n}[z]+\int_B
   \sum_i(\varepsilon^2|P\chi_i|^2+|R_\kappa\chi_i|^2)|z|^2d\nu.
\tag{16.5}
$$

The cutoff errors are bounded multipliers for fixed $b$.
Also $R^{-1}\le\delta R^{-2}+(4\delta)^{-1}$ for every $\delta>0$.
Combining this with (16.3), $|\sum_nz_n|^2\le M\sum_n|z_n|^2$,
(16.4)--(16.5), and the bounded exterior coefficient gives, for every
$\eta>0$, a finite $B_\eta$ such that

$$
0\le V_{\kappa,S}[f]
 \le\left(g_S(\kappa)^{-1}+\eta\right)T_{\kappa,S}[f]
                  +B_\eta\|f\|_2^2.
\tag{16.6}
$$

The Hardy inequality extends across the source by free-form density:
a cutoff on a ball of radius $r$ has energy $O(r^2)$ in volume dimension
four when multiplied by a fixed smooth function. Thus punctured tests
approximate the smooth core. Formula (14.5) then identifies the weighted
completion with the actual integral on (14.2).

Choose $\eta$ so that $g(g_S^{-1}+\eta)<1$.
KLMN [T, Theorem 6.24] applies with this strict relative bound and
proves closedness on exactly (14.2) and (16.2). The other inequality
$h_{\kappa,S,g}\le T_{\kappa,S}$ proves shifted norm equivalence.
The operator is specified by form representation:

$$
\begin{aligned}
D(H_{\kappa,S,g})=\{f\in\mathcal F_{\kappa,S}:\ &\exists F\in\mathcal H_S,
\ h_{\kappa,S,g}(f,w)=\langle F,w\rangle\ \forall w\in\mathcal F_{\kappa,S}\},\\
&H_{\kappa,S,g}f=F,
\end{aligned}
\tag{16.7}
$$

using the linear-first-slot convention. Compactness of (14.2) and norm
equivalence imply compact resolvent. A normalized minimizing sequence is
bounded in this Hilbert form norm, has a weak form limit and a strong
$L^2$ limit, and weak lower semicontinuity proves attainment. No
positivity or uniqueness assertion about a multi-mode ground state is
needed, and the minimum need not be negative relative to zero.

For sharpness, suppose $g>g_S(\kappa)$. The annular sharpness part of
[V, Theorem 10.2, (10.12)--(10.13)] supplies one fixed smooth annular
$u$ on the full Heisenberg group, normalized in $L^2(dX)$, with

$$
E_H[u]-gc_{G,\kappa}M D_H[u]<0,\qquad
E_H[u]=\int(|Uu|^2+|Vu|^2)dX,\quad
D_H[u]=\int R^{-2}|u|^2dX.
\tag{16.8}
$$

There is no angular symmetry restriction on the inequality being tested;
these particular allowed annular tests suffice to attain its infimum.
For sufficiently small $r$ put

$$
\begin{gathered}
u_r(\Psi_\kappa^{-1}X)=m_\kappa^{-1/2}r^{-2}
                                  u(\delta_{1/r}X),\\
p_S(D)=\frac1{\sqrt{2\pi M}}\sum_{n\in S}e^{inD},
\qquad f_r(q,D)=u_r(q)p_S(D).
\end{gathered}
\tag{16.9}
$$

Zero extension outside the chart is smooth because $u$ is compactly
supported in an annulus. Both factors have norm one, $|p_S(0)|^2=M/(2\pi)$, and $f_r$ is in the
original smooth core and in the declared sector. Exact measure in
(15.1), $a_\kappa^{\rm loc}-1=O(r)$ on its support, bounded fixed
$nC_\kappa$, and (16.3) give

$$
\begin{aligned}
T_{\kappa,S}[f_r]&=r^{-2}E_H[u]+O(r^{-1}),\\
V_{\kappa,S}[f_r]&=r^{-2}c_{G,\kappa}M D_H[u]+O(r^{-1}).
\end{aligned}
\tag{16.10}
$$

For the first line the magnetic cross term has order at most $r^{-1}$
and its square term is $O(1)$. For the second line the remainder
$R^{-1}$ integrates to $O(r^{-1})$ against the normalized state.
The constants may depend on the actual frequency locations, $\kappa,S,u$.
The strictly negative coefficient in (16.8) proves collapse in this
same finite sector. This proves the exact strict boundary (16.1),
without resolving its equality case. $\square$

**Corollary 16.2 (the retained zero mode and its source factor).** For
$S=\{0\}$ the form in Theorem 16.1 is exactly

$$
h_{\kappa,\{0\},g}[Jz]=\mathcal E_\kappa[z]
              -\frac{g}{2\pi}\int_BG_\kappa|z|^2d\nu,
\qquad g_{\{0\}}=4\pi^2m_\kappa\lambda_H.
\tag{16.11}
$$

Proof. Equations (14.1)--(14.3) and $Jz=(2\pi)^{-1/2}z$ give the
identity. A unit base source has leading coefficient
$(2\pi m_\kappa)^{-1}R^{-2}$ and strict boundary
$2\pi m_\kappa\lambda_H$ for its own coupling. Writing the base
coupling as $g/(2\pi)$ gives precisely (16.11).
This extends the sufficient window of (11.1), without identifying its
nonsharp symbol $g_*$ with the new sharp boundary. $\square$

## 17. A common two-sided window and the obstruction to soft hidden costs

**Theorem 17.1 (fixed-sector uniform source collars).** Fix
$0<b<a\le\kappa_1$ with $[-a,a]\subset K$ as in Definition 10.1, and
consider the compact two-sided collar

$$
\mathcal K_{a,b}=[-a,-b]\cup[b,a].
\tag{17.1}
$$

The source has $\kappa\ne0$ everywhere on this collar. Preparation,
$Z,I,k_0$, the common additional guard $I$ and $\varepsilon>0$ are fixed. For fixed finite $S$ let

$$
\begin{aligned}
\underline g_S(a)&=\frac{4\pi^2\lambda_H}{M}
                         \min_{|\kappa|\le a}m_\kappa>0,\\
m_\kappa&=
\frac{\varepsilon^2(H+\kappa)(k_0-2\kappa)^2}
 {4H^2(k_0-\kappa(H+\kappa)/H)^2}.
\end{aligned}
\tag{17.2}
$$

Every $0<g<\underline g_S(a)$ gives the closed, compact-resolvent,
attained-minimum conclusions of Theorem 16.1 at every point of the
collar. For $0<g\le\underline g_S(a)/2$ there is a single finite $B$,
independent of $\kappa$ and $g$ in these ranges, for which

$$
h_{\kappa,S,g}[f]\ge\tfrac14T_{\kappa,S}[f]-B\|f\|_2^2.
\tag{17.3}
$$

For the ranges in (17.3), the shifted normalized form balls are
collectively relatively compact in $L^2(\Omega)$. Constants can in fact be chosen independently of
$b>0$ with $a,S$ fixed; this is a statement for $0<|\kappa|\le a$,
not a full-source construction at zero.

Proof. The explicit positive expression in (17.2) follows from (10.2)
and (15.1). Positivity and smoothness on $[-a,a]$ make its minimum
positive. Lemma 15.2 is uniform for the finite set $S-S$ there. The
source cutoffs in (16.5), contact coefficient errors and lower-order
bounds in (16.4)--(16.6) can therefore be chosen uniformly. In
particular (16.6) holds with common $B_\eta$ and coefficient
$\underline g_S(a)^{-1}+\eta$. Taking
$\eta=(2\underline g_S(a))^{-1}$ makes the relative bound at most
$3/4$ for $g\le\underline g_S(a)/2$, proving (17.3).
For any fixed $g<\underline g_S(a)$ take a smaller common $\eta$.
The uniform version of (14.4) and collective compactness in Theorem
10.2 prove the last claim. This uses only modal extension at zero to
choose constants on a compact set. It postulates neither a
four-coordinate Green density at zero nor an identification of artificial
nonzero hidden modes there with the native double-wall leaf.
No uniformity as $M\to\infty$, as frequency locations diverge,
as $\varepsilon\to0$, or as the pole or height faces move is asserted.
$\square$

**Definition 17.2 (a genuinely hidden-only soft quadratic cost).** Let
$\mathfrak a$ be any nonnegative Hermitian quadratic form on a linear
subspace of $L^2(\mathbb T_D,dD)$ containing every trigonometric
polynomial, with finite value on each such polynomial. A hidden-only
cost on product states, and on every larger domain where it is defined,
is

$$
\mathcal A[f]=\int_B\mathfrak a[f(q,\cdot)]d\nu(q),\qquad
\mathcal A[u(q)p(D)]=\|u\|_2^2\mathfrak a[p].
\tag{17.4}
$$

No translation invariance, diagonal Fourier representation, boundedness
or closability of $\mathfrak a$ is required. A chosen finite prefactor
can be included in $\mathfrak a$. The cost does not depend on $q$ or on
retained derivatives. Finiteness on every polynomial distinguishes it
from a hard domain restriction that excludes modes altogether.

**Theorem 17.3 (no soft hidden-only quadratic cost stabilizes the full
original point field).** For fixed nonzero $\kappa$ of Definition 10.1,
any $g>0$ and every cost (17.4),

$$
\inf_{\substack{\|f\|_2=1\\f\text{ a smooth sector product as in }(16.9)}}
 \left(T_\kappa[f]+\mathcal A[f]
                   -g\int_\Omega\Gamma_\kappa|f|^2d\mu\right)=-\infty,
\tag{17.5}
$$

where the union over all finite hidden sectors is allowed in the infimum.
Consequently no larger unrestricted-domain realization agreeing with
these energy values can be semibounded.

Proof. Choose an integer $M>4\pi^2m_\kappa\lambda_H/g$ and any fixed
set $S$ of that cardinality. Then $g>g_S(\kappa)$.
Take the annular sequence $f_r=u_rp_S$ from (16.8)--(16.10).
Its hidden penalty is the single finite number
$\mathfrak a[p_S]$, independent of $r$, since $\|u_r\|_2=1$.
The kinetic minus attractive energy has a strictly negative
$r^{-2}$ coefficient and an $O(r^{-1})$ remainder.
Adding the finite penalty cannot prevent divergence to $-\infty$.
The choice of $M$ and $p_S$ is made once, before $r\downarrow0$;
no estimate uniform in growing $M$ is needed. $\square$

## 18. Supplier correspondence and the native consumer's exact boundary

**Definition 18.1 (attributed supplies and the source-specific synthesis).**
The source and operator correspondences used in §§14--17 are as follows.

| Supplier | Consumed statement and preserved conditions |
| --- | --- |
| [N], Definitions 2.1, 3.1, 8.1 and Theorem 8.2; [G], Definition 12.1 and Calculation 12.2 | The actual five probabilities, negative phase convention, immutable source means, preparation translations, original two controls, all-prefix height guards and unimodular $q,D$ coordinates. Current-ray reachability supplies neither analytic amplitude preparation nor a Fourier-sector selector. |
| This volume, Theorems 10.2, 11.1 and 12.1 | Natural retained kinetic domain, compactness, uniform contact estimates, exact raw hidden marginal and the normalized $1/(2\pi)$ zero-mode energy. Lemma 15.2 adds the nonzero complex mode differences; these were not supplied by the scalar marginal. |
| [V], §§10--13, especially Theorems 10.2 and 11.1 | Exact Heisenberg flux $2\pi$, full-complex angular constant $\lambda_H=\lambda_0$, annular sharpness and the residual-convolution method. The local correspondence here is (15.1): density $m_\kappa$, coefficient matrix $\operatorname{diag}(1,(a_\kappa^{\rm loc})^2)$, plus the explicitly retained magnetic first-order and bounded terms (15.8). The proof of Lemma 15.2 supplies those extra terms directly; a global different native source is not substituted. The supplier's critical completion is not transferred to this matrix problem. |
| [J] Jerison--Sánchez-Calle, *Estimates for the Heat Kernel for a Sum of Squares of Vector Fields*, Indiana Univ. Math. J. 35 (1986), 835--854, [primary text](https://www.iumj.indiana.edu/IUMJ/FTDLOAD/1986/35/35043/pdf), Theorem 2, p.849, and pp.848--850 | The compact smooth Hörmander-field upper bound is $C\mu(B(q,\sqrt t))^{-1}\exp(-\beta d(q,p)^2/t)$ for $0<t<1$. The contact extension and its uniform coefficient/volume checks are those of Theorem 10.2 and (15.7); killing returns to the original cylinder by domination. This is a free-kernel supply, not a sharp Hardy constant. |
| [H] Colin de Verdière--Hillairet--Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, [doi:10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), Theorem B, §3.1.2 and Theorem 3.2 | The local free fields have step-two strong Hörmander generation, positive smooth density and self-adjoint contraction realizations. The compact-family hypotheses of Theorem 3.2 hold for the base extension used in (15.7). Theorem B's smooth nilpotent heat limit alone supplies neither the complete Green tail nor the $O(R^{-1})$ resolvent error; these are proved in (15.7)--(15.10). No theorem about a real free operator is silently applied to an attractive singular matrix operator. |
| [R] Ciatti--Cowling--Ricci, *Hardy and uncertainty inequalities on stratified Lie groups*, [arXiv:1308.2373v1](https://arxiv.org/pdf/1308.2373v1), §2, (2.1), (2.6)--(2.7), Corollary 3.2 | Heat/Riesz normalization and unweighted control with $p=2$, $\alpha=1$, $Q=4$ are mature supplies. The strict requirement $0<1<4/2$ holds. That corollary provides a finite control constant, not the sharp full-complex $\lambda_H$ of (15.2). |
| [T] Teschl, *Mathematical Methods in Quantum Mechanics*, [primary text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorem 6.24 and Theorem 2.13 | KLMN uses only the strict relative bound $g(g_S^{-1}+\eta)<1$ on the already closed natural sector form. Representation gives (16.7). Compactness and attainment use Proposition 14.2 separately. This invocation gives no equality assertion. |
| [C], [Recursive holographic boundary geometry, continuation III](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md), §§84--85 | Its carrier is $H^1\times\mathbb R$, with three direct fields, noncompact hidden fibre, volume exponent five and a Coulomb marginal on a Euclidean three-dimensional base. Its finite central band has infinitesimal relative form bound for every fixed bandwidth. Here there are two original fields, a compact hidden circle and a contact inverse-square base singularity with a finite strict coupling boundary. Neither its all-coupling finite-band stability nor its noncompact attainment hypotheses are transferred. |

The Fourier evaluation inequality, classical free heat estimates, form
representation and KLMN are `literature-attested` intermediate ingredients.
The `repo-derived` synthesis is the original nearby native point field's
finite-mode coefficient matrix with exact raw-source normalization,
its cardinality-dependent strict boundary, and the resulting hard-sector
versus soft-cost separation. It is not a new general Hardy theorem or a
republication of [C]'s finite-band theorem. This attribution makes no
world-priority or exhaustive literature-search claim.

**Proposition 18.2 (what this supplies to the full4/retained3 comparison).**
At every fixed nearby native source with $\kappa\ne0$, the original full
point field admits a stable, compact, attained restricted variational
problem on the declared finite sector for every coupling strictly below
(16.1), and collapses within that very sector above it. Its threshold
scales as $1/M$ and depends on frequency locations only through
lower-order estimates. Hence no positive attraction is stable on all
finite sectors at once, even after any cost of Definition 17.2.
These conclusions provide an analytic stability control, and do not
identify physical spatial dimension or acquire that control natively.

Proof. Theorems 16.1 and 17.3 give the assertions, with equality excluded
throughout. The zero-mode instance is exactly the original retained3
consumer by Corollary 16.2, and Theorem 17.1 supplies a common two-sided
source window. The full4 parent still has the all-positive-coupling
instability supplied by [G, Theorem 3.1]; no bounded attractive parent
heat semigroup is available to justify repeated projection or a Trotter
construction. Free sector reduction in Proposition 14.2 is therefore
not such a protocol. Analytic sector selection and a soft penalty are
also different from a sensor, an attractive sampler, a finite-bit
implementation or an operation preparing amplitudes from the original
immutable INITIAL. None is among Definition 14.1's allowed operations.

The paid producer of [Paid-point observation tracking](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md),
§§51--53, has a positive initial grid hold at its starting pole; its
Theorem 53.2 concerns bounded original-clock occupations and the stated
cap/limit order. That producer has its own source and operation contract,
not an automatic realization of Definition 14.1. A hold of duration
$h>0$ at a pole where $\Gamma=+\infty$ gives infinite uncapped
occupation, however small $h$ is. The positive-hold obstruction of
[Central-noise Green stability](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md),
§7, therefore survives paid tracking. The different coefficient-access
polygon family [V, §§29--30] and its
[Point-source occupation and finite-command cap limits](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md)
have their own singular integrability results. None supplies an uncapped
paid-producer transfer for the present full point field, and none is
used as one here.
The actual source, law, history, observation, density, metric, clock,
resources and acquisition permissions still require their own proved
correspondence for any operational consumer.
Finally, the current-ray count four, retained-coordinate count three,
direct-control rank two and contact volume exponent four describe
different objects. The only new state-space premise here is finite
hidden Fourier support; it neither removes original readable rays nor
constructs a source-to-physical-space map. Critical equality and any
finite-resource realization of this premise remain outside these
statements. $\square$

## 追加锚（本行以下为增补区）
