# Native FIB: an actual four-coordinate strict affine improvement

**Status.** This volume contains ordinary handwritten mathematics. Its
proofs have not been verified by Lean.

For every fixed $0<Z<2/3$, four stored real coordinates suffice to improve
strictly on the exact two-coordinate affine minimax error, uniformly over
all actual native current rays. The same four-coordinate model has exact
initialization, every signed real straight command, recoverable original
guards, and every prescribed simultaneous native path on its full
all-times domain. The decoder is one fixed affine map into the original
ten outputs, measured in their original Euclidean norm.

The quantitative conclusion, with the exact constants defined below, is

$$
e_{4,\mathsf C}^{\rm aff}(Z)
\le 4H\sqrt{T-\mu}
<4H\sqrt T=e_{2,\mathsf C}^{\rm aff}(Z),\qquad \mu>0,
$$

for each of the literal, guard-recoverable, prescribed-path, and combined
contracts $\mathsf C$. This is an upper witness and a strict comparison;
it is not a solution of the four-dimensional minimax problem.

The mathematical suppliers used here are:

- **[M]** *Native FIB: exact two-dimensional affine minimax and an
  attaining annulus*.
- **[A]** *Native FIB on the full open domain: affine approximation and
  finite attainment*, including its fixed-dimension continuation.

In particular, [M, Theorem 6.4] supplies the lower bound over arbitrary
two-coordinate affine models. That theorem is reused, not presented as a
new classification of competitors. The native interfaces and path
integration are supplied by [A, §§1–4 and 9] and [M, §§1–3 and 9]. The
scalar root and unique lower contact already occur in [M, §7]. The proofs
below develop the complete active set needed for a strict perturbation,
give its explicit uniform margin, and realize that very perturbation with
four actual affine coordinates. Section 9 separates these roles.

## 1. Current rays, preparation and the original ten-output metric

**Definition 1.1 (Native data and histories).** Let $0<Z<1$ and set

$$
r=1-Z,\qquad H=r/2,\qquad
p(k)=(k,H-k,Z,H-k,k),\qquad 0<k<H.
$$

The mode order is $(0,1,2,3,13)$ and the probability tangent is
$d=(1,-1,0,-1,1)^{\mathsf T}$. Fix any preparation height
$k_0\in(0,H)$ and any preparation phases $\theta_j^{\rm in}$.
With the negative phase convention, the native equations are

$$
\psi_j=\sqrt{p_j}\,e^{-i\theta_j},\qquad
\dot p=d\dot k,\qquad
\dot\theta_j=\frac{d_j}{p_j(k)I(k)}\dot\chi,\qquad
I(k)=\frac2k+\frac2{H-k}.
$$

Histories are piecewise $C^1$ or absolutely continuous native paths on
finite compact time intervals, with interior height throughout and finite
phase variation. The initial real relation phase is consistent with
$d^{\mathsf T}\theta^{\rm in}$. Real lifts may be used to integrate a
history. The state queried at a finite prefix is its current ray, without
its producing history or a retained lift. There is no loop, winding,
command-size or common finite-horizon restriction. Write
$\mathbb T=\mathbb R/(2\pi\mathbb Z)$.

**Proposition 1.2 (Exact source and straight commands).** The actual
current-ray space from this arbitrary fixed preparation is exactly

$$
\mathcal M=(0,H)\times\mathbb T^2.
$$

Its coordinates $(k,\alpha,\beta)$ have phase increments
$h=\theta-\theta^{\rm in}=(u,v,0,v,u)$ with
$\alpha=u-v$, $\beta=u$. For every $s,t\in\mathbb R$ the original
straight commands act by

$$
P_s(k,\alpha,\beta)=(k+s,\alpha,\beta),\qquad
\operatorname{dom}P_s=\{(k,\alpha,\beta)\in\mathcal M:0<k+s<H\},
$$

$$
Q_t(k,\alpha,\beta)
=\left(k,\alpha+\frac t2,\beta+\left(\frac12-\frac kr\right)t\right),
\qquad \operatorname{dom}Q_t=\mathcal M.
$$

Proof. The reciprocal sum and phase rates are

$$
I(k)=\frac r{k(H-k)},\qquad
w_+(k)=\frac{H-k}{r}=\frac12-\frac kr,\qquad
w_-(k)=-\frac kr.
$$

The equal rates within the two groups give equal increments, regardless
of the preparation phases. Thus

$$
du=\left(\frac12-\frac kr\right)d\chi,\qquad
dv=-\frac kr\,d\chi,\qquad
d\alpha=\frac12d\chi,\qquad
d\beta=\left(\frac12-\frac kr\right)d\chi.
$$

Both changes between $(u,v)$ and $(\alpha,\beta)$ have integer
coefficients, with inverse $u=\beta$, $v=\beta-\alpha$, and so are
inverse changes of circle coordinates. To check equality of rays, set
$\zeta_j=\theta_j^{\rm in}-\theta_2^{\rm in}$ and use the representative

$$
\left(
\sqrt{k}e^{-i(\zeta_0+u)},
\sqrt{H-k}e^{-i(\zeta_1+v)},
\sqrt Z,
\sqrt{H-k}e^{-i(\zeta_3+v)},
\sqrt{k}e^{-i(\zeta_{13}+u)}
\right).
$$

The fixed positive middle component forces any scalar relating two such
representatives of one ray to be one. Their moduli determine $k$, and
the remaining positive amplitudes determine $u,v$ modulo $2\pi$.
Conversely these data determine the representative. There is no further
quotient.

Integration along a fixed-phase probability leg and a fixed-height phase
leg gives $P_s,Q_t$. The straight probability segment is interior if and
only if its endpoint is, by convexity of $(0,H)$. The command $t$ is a
signed real input, not a circle input reduced modulo a period.

It remains to verify that all displayed phase pairs are actual. Choose
$k_1\ne k_0$ in $(0,H)$, and put $d_k=k_1-k_0$. The chronological
rectangle $P_{d_k},Q_t,P_{-d_k},Q_{-t}$ fixes $k,\alpha$ and adds
$-d_kt/r$ to $\beta$. For any target real representatives
$\alpha_*,\beta_*$, let

$$
L=2\alpha_*,\qquad
q=\beta_*-\left(\frac12-\frac{k_0}{r}\right)L,\qquad
t=-\frac{rq}{d_k}.
$$

Perform that rectangle, then $Q_L$ at $k_0$, then $P_{k-k_0}$.
The endpoint is the target $(k,\alpha_*,\beta_*)$ on the phase circles.
Every leg is finite and lawful. This proves reachability using the
original two controls, without adding independent phase controls.
$\square$

**Definition 1.3 (Original decoder coordinates).** Use the edge order

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)),\qquad
\delta_{ij}=\theta_i^{\rm in}-\theta_j^{\rm in}.
$$

For each edge, the two observables are

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|.
$$

Let $y:\mathcal M\to\mathbb R^{10}$ concatenate their expectation
pairs in this order. Put

$$
U(a)=\binom{\cos a}{\sin a},\quad
R_a=\begin{pmatrix}\cos a&-\sin a\\\sin a&\cos a\end{pmatrix},\quad
J=\operatorname{diag}(1,-1),
$$

$$
A(k)=2\sqrt{k(H-k)},\qquad B(k)=2\sqrt{Zk},
$$

$$
D_0(a,b)=(a,b,a,Ja,Ja),\qquad
O=\bigoplus_{e\in\mathcal E}R_{\delta_e},\qquad D=OD_0.
$$

The letters $a,b$ in $D_0$ denote arbitrary planar vectors. The error
norm is the original Euclidean norm on all ten entries.

**Lemma 1.4 (Preparation rotations and metric multiplicities).** On all
actual rays,

$$
y(k,\alpha,\beta)=D(A(k)U(\alpha),B(k)U(\beta)),\qquad
D^{\mathsf T}D=4I_2\oplus I_2.
$$

Consequently $\|D(a,b)\|_2^2=4\|a\|_2^2+\|b\|_2^2$.

Proof. The negative phase convention gives
$\overline\psi_i\psi_j=\sqrt{p_ip_j}e^{i(\theta_i-\theta_j)}$.
The expectation pair is twice its real and imaginary parts, namely
$2\sqrt{p_ip_j}U(\delta_{ij}+h_i-h_j)$.
The five increment differences are
$\alpha,\beta,\alpha,-\alpha,-\alpha$. Since $U(-\alpha)=JU(\alpha)$,
this is exactly $OD_0$ applied to the two stated planar vectors.
The first vector occurs in four orthogonal output blocks and the second
in one; there are no cross terms. The preparation rotations and $J$ are
orthogonal. The Gram formula follows without changing the output metric.
Also $A(k)\le H$ and $B(k)<2\sqrt{ZH}$, so $y$ is uniformly bounded.
$\square$

## 2. At-most-dimension capacities and the inherited lower bound

**Definition 2.1 (Literal affine contract).** For an integer $n\ge0$, a
model of dimension at most $n$ chooses $m\in\{0,\ldots,n\}$, an arbitrary
function $E:\mathcal M\to\mathbb R^m$, a fixed affine decoder
$\mathcal D(z)=q_0+Lz\in\mathbb R^{10}$, and affine ambient maps

$$
\mathcal U_s(z)=L_sz+b_s,\qquad
\mathcal V_t(z)=C_tz+d_t\qquad(s,t\in\mathbb R)
$$

satisfying

$$
E(P_s\xi)=\mathcal U_s(E(\xi))\quad(\xi\in\operatorname{dom}P_s),
\qquad
E(Q_t\xi)=\mathcal V_t(E(\xi))\quad(\xi\in\mathcal M).
$$

The coefficients may depend on the fixed source, preparation, chosen
model and prescribed command, but not on the current ray or its history.
Both decoder and update offsets are permitted. No regularity,
measurability, boundedness, injectivity or computability of $E$ is
assumed; no parameter regularity, ambient invertibility or ambient group
law is assumed either. All commands are assigned ambient maps, including
commands with empty source domains. Decoded outputs need not be native
physical outputs. Initialization and the update identities use exact real
values. Height, history and real phase lifts are not extra source inputs.

For a model write

$$
\operatorname{err}(E,\mathcal D)
=\sup_{\xi\in\mathcal M}\|\mathcal D(E(\xi))-y(\xi)\|_2.
$$

The literal class is denoted $\mathfrak F_{\le n,\mathsf L}$, and

$$
e_{n,\mathsf L}^{\rm aff}(Z)
=\inf_{(E,\mathcal D,\ldots)\in\mathfrak F_{\le n,\mathsf L}}
\operatorname{err}(E,\mathcal D).
$$

**Definition 2.2 (Guard and prescribed-path contracts).** The class
$\mathsf G$ additionally requires each straight-command domain to be
the inverse image under $E$ of a subset of the actual encoded image.
Equivalently, all rays in an encoder fiber must agree on lawfulness.
The class $\mathsf P$ additionally requires a state-independent affine
update for every prescribed simultaneous native path on a finite compact
interval, with integrable prescribed velocities independent of the
starting ray, on that path's full all-times source domain. The class
$\mathsf{GP}$ imposes both requirements, including recovery of full path
guards. Section 6 specifies these paths and domains directly.

For $\mathsf C\in\{\mathsf L,\mathsf G,\mathsf P,\mathsf{GP}\}$ define
$\mathfrak F_{\le n,\mathsf C}$ and $e_{n,\mathsf C}^{\rm aff}$ by the
same at-most-dimension convention and the same original error. An empty
class has infimum $+\infty$. The inclusions used below are

$$
\mathfrak F_{\le n,\mathsf{GP}}\subseteq
\mathfrak F_{\le n,\mathsf G}\subseteq\mathfrak F_{\le n,\mathsf L},
\qquad
\mathfrak F_{\le n,\mathsf{GP}}\subseteq
\mathfrak F_{\le n,\mathsf P}\subseteq\mathfrak F_{\le n,\mathsf L}.
$$

Stored dimension, manifold dimension of the actual image, dimension of
its affine hull, and rank of an affine readout are separate quantities.
The dimension budget here counts stored real coordinates.

**Theorem 2.3 (Published comparison interface).** For precisely the
literal contract of Definition 2.1 and every $0<Z<1$,

$$
\bigl(e_{2,\mathsf L}^{\rm aff}(Z)\bigr)^2
=\inf_{C\ge0,\ \gamma\in\mathbb R}
\sup_{0<k<H}\left\{4(Ce^{\gamma k}-A(k))^2+4Zk\right\}.
$$

For every finite dimension $n$, the inherited lower floor is

$$
e_{n,\mathsf L}^{\rm aff}(Z)\ge 2\sqrt{ZH}.
$$

Supplier correspondence. The first statement is [M, Theorem 6.4], with
its $e_2^{\rm aff}$ equal to the present $e_{2,\mathsf L}^{\rm aff}$.
The source has the same $k,\alpha,\beta,r,H,Z$, the same arbitrary fixed
preparation, the same maps $P_s,Q_t$ with their full partial domains,
and the same $D$ and Euclidean metric. Its composed decoder $q$ is the
present $\mathcal D\circ E$. Its dimension is at most two, not exactly
two and not the dimension of an assumed smooth image. The theorem
includes affine offsets, deficient affine hulls, irregular encoders and
unbounded hidden coordinates. Thus no symmetry or regularity of a
competitor is an additional premise in this application.

The second statement is [A, Theorem 3.3 and Proposition 4.1], also
reconstructed in [M, Theorem 3.4 and Proposition 3.5]. Their bounded
affine-observable theorem makes every finite-error decoder independent
of $\beta$. Its orthogonal decomposition $q=D(a,b)+w$, with
$w\perp\operatorname{im}D$, has exact worst-$\beta$ squared error

$$
\|w\|^2+4\|a-A(k)U(\alpha)\|^2+(\|b\|+B(k))^2\ge4Zk.
$$

Taking the supremum through interior heights gives $4ZH$. Infinite-error
models satisfy the bound as well. Only bounded affine observables are
being declared $\beta$-independent, not arbitrary hidden coordinates.
This volume uses these published lower theorems; it does not repeat
their all-competitor proofs as new results. $\square$

## 3. The exact two-dimensional profile and its complete active set

Throughout §§3–7 assume $0<Z<2/3$. Define

$$
\tau=\frac Z{4H}\in(0,1),\qquad x=\frac kH,\qquad
s(x)=\sqrt{x(1-x)},\qquad T_0=\frac{(1+\tau)^2}{4}.
$$

The function $s(x)$ is unrelated to the real displacement parameter in
$P_s$. All closed-interval functions in this section are scalar formulas
for limits of interior errors; the source remains $0<k<H$.

**Definition 3.1 (Endpoint exponential and normalized objective).** Set

$$
\mathcal J(c,\ell)
=\max_{0\le x\le1}\{(ce^{\ell x}-s(x))^2+\tau x\}
\qquad(c\ge0,\ \ell\in\mathbb R).
$$

For a trial level $t>\tau$ let

$$
v_t(x)=\sqrt{t-\tau x},\qquad
\lambda_t=\frac12\log\frac{t-\tau}{t},\qquad
f_t(x)=\sqrt t\,e^{\lambda_t x}
=t^{(1-x)/2}(t-\tau)^{x/2},
$$

$$
g_t(x)=s(x)-v_t(x)-f_t(x),\qquad
\Phi_\tau(t)=\max_{[0,1]}g_t.
$$

The substitution $c=C/(2H)$, $\ell=\gamma H$ in Theorem 2.3 gives

$$
4(Ce^{\gamma k}-A(k))^2+4Zk
=16H^2\bigl((ce^{\ell x}-s(x))^2+\tau x\bigr).
$$

Continuity of this explicit formula on $[0,1]$ makes its maximum equal
to its supremum on $(0,1)$. In particular, the zero amplitude has value
$T_0$, because

$$
s(x)^2+\tau x=T_0-\left(x-\frac{1+\tau}{2}\right)^2.
$$

Every positive finite exponential has $\mathcal J(c,\ell)>\tau$,
as its scalar limit at $x=1$ is $c^2e^{2\ell}+\tau>\tau$.

**Lemma 3.2 (Corridor criterion with strict interior upper inequality).**
For $t>\tau$, a positive exponential $R(x)=ce^{\ell x}$ with
$\mathcal J(c,\ell)\le t$ exists if and only if $\Phi_\tau(t)\le0$.
Every feasible $R$ satisfies $R\le f_t$. For every $t>\tau$,

$$
f_t(x)<s(x)+v_t(x)\qquad(0<x<1).
$$

When $\Phi_\tau(t)\le0$, the exponential $f_t$ itself is feasible.

Proof. Feasibility is exactly the pair of corridor inequalities

$$
s-v_t\le R\le s+v_t.
$$

The endpoint limits give $R(0)\le\sqrt t$ and
$R(1)\le\sqrt{t-\tau}$. Since $\log R$ is affine, interpolation of
these two inequalities gives $\log R\le\log f_t$. Hence feasibility
requires $s-v_t\le f_t$.

For the reverse implication, put $u_t=s+v_t$. The function $s$ is
strictly concave on $[0,1]$; on its interior,
$s''=-1/(4s^3)<0$, and continuity excludes any affine endpoint segment.
The function $v_t$ is concave and positive. Thus $u_t$ is strictly
concave and positive on the closed interval. For distinct points and a
strict convex combination, apply strict concavity of $u_t$, then the
increasing logarithm, then concavity of the logarithm. This proves that
$\log u_t$ is strictly concave. Its endpoint chord is $\log f_t$.
It follows that $f_t<u_t$ in the interior, with equality at the two
endpoints. If $s-v_t\le f_t$, both corridor inequalities therefore hold
for $f_t$. The lower corridor can be negative; no logarithm of it has
been taken. $\square$

**Proposition 3.3 (Exact root and literal two-coordinate value).** There
is a unique $T>\tau$ such that $\Phi_\tau(T)=0$, and

$$
\tau<T<T_0,\qquad
e_{2,\mathsf L}^{\rm aff}(Z)=4H\sqrt T.
$$

The minimum normalized radial error is $T$, achieved by $f_T$.

Proof. On any compact $t$ interval inside $(\tau,\infty)$ the defining
functions are jointly continuous with $x\in[0,1]$. Uniform continuity
and the inequality bounding the difference of two maxima by the supremum
of the difference prove continuity of $\Phi_\tau$. For $t_2>t_1>\tau$,

$$
v_{t_2}(x)-v_{t_1}(x)
=\frac{t_2-t_1}{v_{t_2}(x)+v_{t_1}(x)}
\ge\frac{t_2-t_1}{\sqrt{t_2}+\sqrt{t_1}}>0,
$$

while

$$
\partial_t\log f_t(x)
=\frac{1-x}{2t}+\frac{x}{2(t-\tau)}>0.
$$

Thus $g_{t_2}$ lies uniformly below $g_{t_1}$, and $\Phi_\tau$ is
strictly decreasing. At $T_0$, the square-completion identity in
Definition 3.1 gives $s\le v_{T_0}$. Also
$T_0-\tau=(1-\tau)^2/4>0$, so $f_{T_0}$ has a positive minimum.
Consequently $\Phi_\tau(T_0)<0$.

Set $x_0=(1+\tau)/2$, which lies strictly between $\tau$ and $1$.
As $t\downarrow\tau$, at this fixed interior point,

$$
f_t(x_0)\longrightarrow0,\qquad
s(x_0)-v_t(x_0)\longrightarrow
\sqrt{1-x_0}\bigl(\sqrt{x_0}-\sqrt\tau\bigr)>0.
$$

This yields $\Phi_\tau(t)>0$ near $\tau$ from above. Continuity and
strict decrease give the asserted unique root and its range. This sign
argument is pointwise at $x_0$, without a false claim of uniform
convergence of $f_t$ as $t\downarrow\tau$ at $x=0$.

Every positive exponential's objective exceeds $\tau$. If its objective
were below $T$, Lemma 3.2 would force $\Phi_\tau$ to be nonpositive
below its root, a contradiction. The zero amplitude has objective
$T_0>T$. At the root Lemma 3.2 makes $f_T$ feasible, so the radial
minimum is $T$. Theorem 2.3 and the normalization in Definition 3.1
give the stated value for all literal competitors. This scalar argument
is the root construction of [M, §7], included to fix the exact parameters
used in the new perturbation. $\square$

For the rest of the construction write

$$
\lambda=\lambda_T<0,\qquad f=f_T,\qquad v=v_T,\qquad
g=g_T,\qquad F_0(x)=(f(x)-s(x))^2+\tau x.
$$

**Lemma 3.4 (Unique lower contact and its location).** For every trial
level $t>\tau$, $g_t$ has exactly one interior maximizer. At the root
$T$ it has exactly one zero, denoted $x_*$, and

$$
\frac{1+\tau}{2}<x_*<1,\qquad
f(x_*)=s(x_*)-v(x_*)>0.
$$

The root and contact are equivalently specified by their ranges and

$$
\begin{aligned}
s(x_*)-\sqrt{T-\tau x_*}&=\sqrt T\,e^{\lambda_Tx_*},\\
\frac{1-2x_*}{2s(x_*)}
+\frac{\tau}{2\sqrt{T-\tau x_*}}
-\lambda_T\sqrt T\,e^{\lambda_Tx_*}&=0.
\end{aligned}
$$

Proof. For $0<x<1$, differentiation gives

$$
g_t'(x)=\frac{1-2x}{2s(x)}+\frac{\tau}{2v_t(x)}-\lambda_t f_t(x),
$$

$$
g_t''(x)=-\frac1{4s(x)^3}
+\frac{\tau^2}{4v_t(x)^3}-\lambda_t^2 f_t(x).
$$

Since $v_t(x)^2>\tau(1-x)$ and $0<\tau<1$,

$$
\frac{\tau^2}{v_t(x)^3}
<\frac{\sqrt\tau}{(1-x)^{3/2}}
<\frac1{[x(1-x)]^{3/2}}=\frac1{s(x)^3}.
$$

Hence $g_t''<0$. The terms of $g_t'$ other than $s'$ have finite
limits at both endpoints. Thus $g_t'\to+\infty$ as $x\downarrow0$
and $g_t'\to-\infty$ as $x\uparrow1$. The continuous function
$g_t'$ is strictly decreasing and has exactly one zero, which is
the unique maximizer of $g_t$. The endpoint
values are $g_t(0)=-2\sqrt t$ and
$g_t(1)=-2\sqrt{t-\tau}$, both negative.

At $t=T$ the maximum is zero, so only the unique maximizer is a zero.
At $x_0=(1+\tau)/2$, the inequality $T<T_0$ implies
$v(x_0)<s(x_0)$. Therefore

$$
g'(x_0)=\frac{\tau}{2}
\left(\frac1{v(x_0)}-\frac1{s(x_0)}\right)-\lambda f(x_0)>0.
$$

Its zero lies to the right of $x_0$. At this zero, the maximum equation
and the derivative equation give the displayed system. Conversely, any
pair in the specified ranges satisfying the system gives a zero maximum
of $g_t$; Proposition 3.3 and strict concavity force $t=T$ and $x=x_*$.
$\square$

**Theorem 3.5 (The complete three-point active set).** The exact
two-dimensional profile has

$$
F_0(x)\le T\quad(0\le x\le1),\qquad
\{x\in[0,1]:F_0(x)=T\}=\{0,x_*,1\}.
$$

At $x_*$ the signed radial error is $f-s=-v<0$, whereas its limits
at $0$ and $1$ are $\sqrt T>0$ and $\sqrt{T-\tau}>0$.

Proof. Lemma 3.2 gives both corridor inequalities at the root, and so
gives $F_0\le T$. Direct evaluation of the scalar limits gives
$F_0(0)=T$ and $F_0(1)=(T-\tau)+\tau=T$.
At an interior point, equality $F_0=T$ is equivalent to
$f=s+v$ or $f=s-v$. Lemma 3.2 excludes the first equality strictly
at every interior point. Lemma 3.4 leaves exactly $x_*$ for the
second. These exhaust all equality possibilities. In particular, there
is no unexamined fourth active point. At $x_*$, $v>0$ and $f>0$,
and the claimed signs follow. The two boundary points describe scalar
error limits, not additional rays or encodings. $\square$

## 4. A specified two-exponential perturbation with a uniform margin

The negative radial error at the unique interior contact must be increased,
while the positive errors at both ends must be decreased. The following
single perturbation accomplishes these three signed changes and remains
a sum of two exponential modes.

**Definition 4.1 (Perturbation and first variation).** With the exact
$T,x_*,\lambda,f,v$ of §3, put

$$
b=e^{-1}-1,\qquad
\psi(x)=1+bx-e^{-x},\qquad
\eta=\frac{\psi(x_*)}{2},\qquad a=1-\eta.
$$

For $0\le u\le1$ define

$$
R_u(x)=f(x)\left[(1+ua)e^{ubx}-u e^{-x}\right],\qquad
F_u(x)=(R_u(x)-s(x))^2+\tau x.
$$

In particular $R_0=f$ and the present $F_0$ is the same as in §3.
For a fixed $u$, the two exponential terms have exponents
$\lambda+ub$ and $\lambda-1$. Write

$$
h(x)=\left.\partial_uR_u(x)\right|_{u=0},\qquad
W(x)=\left.\partial_uF_u(x)\right|_{u=0}.
$$

**Lemma 4.2 (Strict descent at every active point).** These choices obey

$$
-1<b<0,\qquad 0<\eta<\frac12,\qquad \frac12<a<1,
$$

and

$$
h=f(\psi-\eta),\qquad W=2(f-s)h.
$$

At the complete active set their values are

$$
W(0)=-2\eta T,\qquad
W(1)=-2\eta(T-\tau),\qquad
W(x_*)=-2\eta f(x_*)v(x_*).
$$

Proof. The endpoints of $\psi$ are both zero, and
$\psi''(x)=-e^{-x}<0$. Strict concavity therefore gives
$\psi(x)>0$ in the interior. Also $bx\le0$ and $e^{-x}>0$, so
$\psi(x)<1$ throughout $[0,1]$. Since $x_*$ is interior, the bounds
on $\eta$ and $a$ follow. Differentiating the defining formula in
$u$ at zero gives

$$
h=f(a+bx-e^{-x})=f(\psi-\eta),
$$

and differentiation of its squared error gives $W=2(f-s)h$.
At the endpoints, $h=-\eta f$ and $s=0$. At the interior contact,
$\psi(x_*)=2\eta$, so $h(x_*)=\eta f(x_*)$, while
$f(x_*)-s(x_*)=-v(x_*)$. Substitution proves all three strict
negative values. $\square$

**Definition 4.3 (Compact gap and exact constants).** Set

$$
m=\eta\min\{T,\ T-\tau,\ f(x_*)v(x_*)\},\qquad
K=\{x\in[0,1]:W(x)\ge-m\}.
$$

Once the compact maximum below is justified, define

$$
d=T-\max_{x\in K}F_0(x),\qquad
C_0=2T+\sqrt T,\qquad M=28T+2\sqrt T,
$$

$$
\varepsilon=
\min\left\{\frac12,\frac{m}{2M},\frac{d}{2(C_0+M)}\right\},\qquad
\mu=\min\left\{\frac{m\varepsilon}{2},\frac d2\right\}.
$$

Here $M$ is a remainder constant, not the source $\mathcal M$ or the
supplier label [M]. All the choices are exact scalar definitions. They
involve one unique root, one unique contact, and one specified compact
maximum, with no unspecified sufficiently small coefficient.

**Lemma 4.4 (Nonempty compact complement and positive gap).** The set
$K$ is nonempty and compact, $m>0$, and its defining maximum exists
with $d>0$.

Proof. Each factor in the definition of $m$ is positive: $\eta>0$,
$T>\tau>0$, $f(x_*)>0$, and $v(x_*)>0$. Thus $m>0$.
The continuous function $f-s$ is positive at zero and negative at
$x_*$. It has a zero at some point strictly between them. There
$W=2(f-s)h=0\ge-m$, proving $K\ne\varnothing$.

The function $W$ is continuous on $[0,1]$, including both scalar
endpoints, so $K$ is closed in a compact interval. Lemma 4.2 shows that
each of $0,x_*,1$ has $W\le-2m<-m$. Hence $K$ avoids the entire
active set of Theorem 3.5. Continuity makes $F_0$ attain its maximum
on $K$. If that maximum were $T$, a point of $K$ would be active,
contradicting the preceding sentence. Since $F_0\le T$, the maximum
is strictly smaller than $T$, proving $d>0$. This proves the global
gap needed away from strict descent; contact signs alone would not do
so. $\square$

**Lemma 4.5 (Uniform first-variation and Taylor bounds).** On $[0,1]$,

$$
|W(x)|\le C_0.
$$

On the full rectangle $0\le u,x\le1$,

$$
|R_u|\le3\sqrt T,\qquad
|\partial_uR_u|\le4\sqrt T,\qquad
|\partial_u^2R_u|\le4\sqrt T,\qquad
|\partial_u^2F_u|\le2M.
$$

Consequently for $0\le u\le1$, uniformly in $x\in[0,1]$,

$$
F_u(x)\le F_0(x)+uW(x)+Mu^2.
$$

Proof. We have $0<f\le\sqrt T$, $0\le s\le1/2$, and
$|\psi-\eta|\le1$ by Lemma 4.2. Thus $|h|\le\sqrt T$ and

$$
|W|\le2(f+s)|h|
\le2(\sqrt T+1/2)\sqrt T=2T+\sqrt T=C_0.
$$

The derivatives in the perturbation parameter are exactly

$$
\partial_uR_u
=f\left[(a+bx(1+ua))e^{ubx}-e^{-x}\right],
$$

$$
\partial_u^2R_u
=f\left[2abx+(1+ua)(bx)^2\right]e^{ubx}.
$$

On the stated rectangle, $0<a<1$, $|b|<1$, $bx\le0$,
$e^{ubx}\le1$, $e^{-x}\le1$, and $1+ua\le2$. Therefore the
absolute values of the three brackets in $R_u,\partial_uR_u,
\partial_u^2R_u$ are bounded respectively by $2+1=3$,
$1+2+1=4$, and $2+2=4$. Multiplication by $f\le\sqrt T$
proves the first three bounds. Differentiating the squared error gives

$$
\partial_u^2F_u
=2(\partial_uR_u)^2+2(R_u-s)\partial_u^2R_u.
$$

Hence

$$
\begin{aligned}
|\partial_u^2F_u|
&\le 2(4\sqrt T)^2
+2(3\sqrt T+1/2)4\sqrt T\\
&=56T+4\sqrt T=2M.
\end{aligned}
$$

For every fixed $x$, Taylor's formula with integral remainder now gives

$$
F_u(x)=F_0(x)+uW(x)
+\int_0^u(u-v_0)\partial_{v_0}^2F_{v_0}(x)\,dv_0
\le F_0(x)+uW(x)+Mu^2.
$$

All derivatives here are in $u$. No derivative of $s$ in $x$ at a
scalar endpoint is required, so the estimate includes both endpoints.
$\square$

**Theorem 4.6 (Explicit positive margin on the whole scalar interval).**
Every constant in Definition 4.3 is well-defined and positive, and

$$
0<\varepsilon\le\frac12,\qquad
0<\mu<\frac{T-\tau}{8},\qquad T-\mu>\tau>0.
$$

For this one prescribed perturbation,

$$
\boxed{F_\varepsilon(x)\le T-\mu\quad(0\le x\le1).}
$$

Proof. Lemma 4.4 gives $m,d>0$, and $T>0$ gives $C_0,M>0$.
All entries of the minima defining $\varepsilon$ and $\mu$ are
therefore positive. If $x\notin K$, then $W(x)<-m$ and
$F_0(x)\le T$. Lemma 4.5 and $\varepsilon\le m/(2M)$ yield

$$
F_\varepsilon(x)
\le T-m\varepsilon+M\varepsilon^2
\le T-\frac{m\varepsilon}{2}.
$$

If $x\in K$, then $F_0(x)\le T-d$ and $|W(x)|\le C_0$.
Using $\varepsilon\le1$ and
$\varepsilon\le d/[2(C_0+M)]$ gives

$$
F_\varepsilon(x)
\le T-d+C_0\varepsilon+M\varepsilon^2
\le T-d+\varepsilon(C_0+M)
\le T-\frac d2.
$$

These two sets cover $[0,1]$, and the definition of $\mu$ gives the
uniform conclusion. Finally,

$$
\mu\le\frac{m\varepsilon}{2}
\le\frac{\eta(T-\tau)}4
<\frac{T-\tau}{8},
$$

using $m\le\eta(T-\tau)$, $\varepsilon\le1/2$ and $\eta<1/2$.
This proves the claimed lower bound on $T-\mu$ as well. The bound is
uniform in the scalar source variable for each fixed $Z$. It does not
claim an optimal margin or an evaluated numerical value. $\square$

## 5. The actual four-coordinate model

**Definition 5.1 (Two height modes in four stored coordinates).** Fix
the constants of §4, and put

$$
\nu_1=\lambda+\varepsilon b,\qquad \nu_2=\lambda-1.
$$

Store exactly the four real entries of

$$
E_\varepsilon(k,\alpha,\beta)=(z_1,z_2)
=\left(e^{\nu_1 k/H}U(\alpha),\ e^{\nu_2 k/H}U(\alpha)\right)
\in\mathbb R^2\oplus\mathbb R^2.
$$

The numbers $k/H$, $\alpha$ and $\beta$ in this formula specify the
encoder as a function on current rays. They are not additional stored
coordinates.

**Proposition 5.2 (Actual image, fibers and full affine hull).** Both
$\nu_1,\nu_2$ are finite and negative, and
$\nu_1-\nu_2=1+\varepsilon b>1/2$. The actual image is exactly

$$
\mathscr S_\varepsilon=
\left\{(z_1,z_2):
e^{\nu_2}<\|z_2\|<1,\quad
z_1=\|z_2\|^{\nu_1/\nu_2-1}z_2\right\}.
$$

Its fibers are exactly the full $\beta$ circles at fixed $(k,\alpha)$.
It is a two-dimensional smooth manifold, and its actual affine hull is
the whole $\mathbb R^4$.

Proof. The bounds on $\lambda,b,\varepsilon$ show negativity and
finiteness. Since $-1<b<0$ and $0<\varepsilon\le1/2$, one has
$\varepsilon b\ge b/2>-1/2$. Thus the exponents are distinct.

For an encoded point, set $r_2=\|z_2\|=e^{\nu_2 x}$, where
$x=k/H\in(0,1)$. Since $\nu_2<0$, this radius ranges bijectively
over $(e^{\nu_2},1)$. Also

$$
z_1=e^{\nu_1 x}U(\alpha)
=r_2^{\nu_1/\nu_2-1}z_2.
$$

Conversely, any point in the displayed set determines
$x=(\log r_2)/\nu_2\in(0,1)$ and the unique circle direction
$U(\alpha)=z_2/r_2$. It is the encoding of every actual ray with
that $(k,\alpha)$ and arbitrary $\beta$. This proves both the image
and the exact fibers. The parameterization by $(x,U(\alpha))$ has
the smooth inverse just displayed, using a direction on the circle
rather than a chosen angle branch. Thus its image is a smooth open
cylinder of manifold dimension two.

To determine the affine hull, replacing $\alpha$ by $\alpha+\pi$
negates both blocks, so zero lies in the affine hull. If the hull were
proper, some nonzero linear functional
$(z_1,z_2)\mapsto p\cdot z_1+q\cdot z_2$ would vanish on it.
For every interior $x$, varying $\alpha$ would then imply

$$
e^{\nu_1x}p+e^{\nu_2x}q=0.
$$

After division by $e^{\nu_2x}$, two distinct interior values of $x$
give two distinct coefficients $e^{(\nu_1-\nu_2)x}$. Subtracting
forces $p=0$, then $q=0$, a contradiction. The affine hull is
$\mathbb R^4$. Its dimension is not reduced by the manifold
parameterization. $\square$

**Definition 5.3 (One fixed original-output decoder).** On all of
$\mathbb R^4$ define

$$
\widehat A(z_1,z_2)
=2H\sqrt T\bigl[(1+\varepsilon a)z_1-\varepsilon z_2\bigr],
\qquad
\mathcal D_\varepsilon(z_1,z_2)=D(\widehat A(z_1,z_2),0).
$$

In the five original output blocks, this is

$$
\left(
R_{\delta_{01}}\widehat A,\quad
0_2,\quad
R_{\delta_{03}}\widehat A,\quad
R_{\delta_{1,13}}J\widehat A,\quad
R_{\delta_{3,13}}J\widehat A
\right).
$$

This is one fixed linear decoder with zero affine offset. Its negative
coefficient on the second block is allowed by the affine contract.
Preparation phases occur only in its fixed rotations. In particular
the zero $02$ pair is permitted even though no native ray in the open
source has a zero $02$ radius.

**Proposition 5.4 (Every signed command and exact initialization).** For
every real $s,t$, assign the ambient maps

$$
\mathcal U_s^\varepsilon(z)
=\begin{pmatrix}
e^{\nu_1s/H}I_2&0\\0&e^{\nu_2s/H}I_2
\end{pmatrix}z+0_4,
\qquad
\mathcal V_t^\varepsilon(z)
=\begin{pmatrix}R_{t/2}&0\\0&R_{t/2}\end{pmatrix}z+0_4.
$$

They intertwine $P_s,Q_t$ on their entire original domains. The exact
initial encoded state at the original preparation is

$$
z^{\rm in}=
\left(e^{\nu_1 k_0/H},0,e^{\nu_2 k_0/H},0\right).
$$

Proof. In either block, the two substitutions are

$$
e^{\nu_j(k+s)/H}U(\alpha)
=e^{\nu_js/H}e^{\nu_jk/H}U(\alpha),
$$

$$
e^{\nu_jk/H}U(\alpha+t/2)
=R_{t/2}e^{\nu_jk/H}U(\alpha)\qquad(j=1,2).
$$

These are the exact encodings of the source formulas in Proposition 1.2.
The true $\beta$ change under $Q_t$ remains in the source and is
forgotten only by this encoder. All signs and zero commands are
included. For $|s|\ge H$, the probability domain is empty but the
displayed ambient map is still assigned. No real command parameter has
been bounded or identified modulo a period. The preparation increments
are zero, hence $\alpha=\beta=0$ there, yielding $z^{\rm in}$ for
arbitrary preparation phases. $\square$

**Theorem 5.5 (Uniform error in the original ten-output norm).** For
every actual current ray,

$$
\begin{aligned}
\|\mathcal D_\varepsilon(E_\varepsilon(k,\alpha,\beta))
-y(k,\alpha,\beta)\|_2^2
&=16H^2F_\varepsilon(k/H)\\
&\le16H^2(T-\mu).
\end{aligned}
$$

In particular the bound is independent of both phases, and is uniform
arbitrarily close to either boundary of the original open height interval.

Proof. For $x=k/H$, Definitions 4.1 and 5.1 give

$$
\begin{aligned}
\widehat A(E_\varepsilon(k,\alpha,\beta))
&=2H\sqrt T\bigl[(1+\varepsilon a)e^{(\lambda+\varepsilon b)x}
-\varepsilon e^{(\lambda-1)x}\bigr]U(\alpha)\\
&=2H R_\varepsilon(x)U(\alpha).
\end{aligned}
$$

Using $A(k)=2Hs(x)$ and the original Gram matrix of Lemma 1.4,
the squared error is therefore exactly

$$
4\bigl(2H R_\varepsilon(x)-A(k)\bigr)^2+B(k)^2
=16H^2\bigl((R_\varepsilon(x)-s(x))^2+\tau x\bigr).
$$

Theorem 4.6 supplies the uniform bound. This is a pointwise identity
in the original ten outputs, not a change of norm or an average over
phases. $\square$

## 6. Exact height, full guards and every prescribed simultaneous path

**Proposition 6.1 (Recovering the original straight guards).** On the
actual image $\mathscr S_\varepsilon$ define

$$
\kappa(z_1,z_2)=\frac H{\nu_2}\log\|z_2\|.
$$

Then $\kappa(E_\varepsilon(k,\alpha,\beta))=k$. The exact probability
guard for command $s$ is

$$
\mathscr G_s=\{z\in\mathscr S_\varepsilon:0<\kappa(z)+s<H\},
$$

and the exact phase guard is all of $\mathscr S_\varepsilon$. The
updates in Proposition 5.4 preserve the actual image on these guards.

Proof. The second radius is $e^{\nu_2 k/H}>0$, and $\nu_2\ne0$,
so substitution proves the height identity. The inverse image of
$\mathscr G_s$ is precisely $\operatorname{dom}P_s$ of Proposition
1.2, including the strict inequalities and the empty-domain cases.
Every ray in a fiber has that same height, so every fiber agrees on
lawfulness. Phase commands are lawful at every source point. On a lawful
command, exact intertwining identifies the image point after the update
with the encoding of its lawful endpoint; hence it lies in
$\mathscr S_\varepsilon$.

Height recovery is a mathematical function of an already stored radius
on the actual image. Neither a fifth coordinate nor an external height
selector has been added. No guard behavior is required of off-image
vectors. $\square$

**Proposition 6.2 (The full source formula for a prescribed path).**
Prescribe integrable velocities $a_c=\dot k$ and $b_c=\dot\chi$ in the
native class on $[0,T_{\rm p}]$, independently of the initial ray. Put

$$
\rho(t)=\int_0^t a_c(v_0)\,dv_0,\qquad
\Delta=\rho(T_{\rm p}),\qquad
L=\int_0^{T_{\rm p}}b_c(t)\,dt,\qquad
C_{\rm p}=\int_0^{T_{\rm p}}\rho(t)b_c(t)\,dt.
$$

The original source guard is exactly

$$
\mathcal G_{\rm p}
=\{(k,\alpha,\beta)\in\mathcal M:
0<k+\rho(t)<H\ \text{for every }t\in[0,T_{\rm p}]\},
$$

equivalently $k+\min\rho>0$ and $k+\max\rho<H$, with extrema on
this same compact time interval. On this guard the endpoint is

$$
k'=k+\Delta,\qquad
\alpha'=\alpha+L/2,\qquad
\beta'=\beta+\left(\frac12-\frac kr\right)L-\frac{C_{\rm p}}r.
$$

Proof. The displacement $\rho$ is absolutely continuous, hence
continuous and bounded on the compact interval. Thus $C_{\rm p}$
exists, since $b_c$ is integrable. The exact height trajectory is
$k+\rho(t)$. This proves the all-times guard; attained extrema of
$\rho$ make its two extremal inequalities equivalent to it, including
their strictness. Checking only $k$ and $k+\Delta$ would not suffice
for a general path. Each individual lawful compact path has its own
positive height margin by these attained extrema; no margin common to
different rays or paths is imposed.

Integration of the equations in Proposition 1.2 gives the height and
$\alpha$ formulas. For the other circle coordinate it gives

$$
\int_0^{T_{\rm p}}
\left(\frac12-\frac{k+\rho(t)}r\right)b_c(t)\,dt
=\left(\frac12-\frac kr\right)L-\frac{C_{\rm p}}r.
$$

This proves the exact negative mixed term. The formulas are identities
on the phase circles, with no stored real lift. This is direct
integration of the source, rather than an approximation by finitely
split straight commands. It is the native path interface supplied by
[A, §9] and [M, Proposition 9.1]. $\square$

**Theorem 6.3 (One four-coordinate model for all paths and truncations).**
For every path of Proposition 6.2, assign the fixed ambient linear map

$$
\mathcal W_{\rm p}^\varepsilon(z)
=\begin{pmatrix}
e^{\nu_1\Delta/H}R_{L/2}&0\\
0&e^{\nu_2\Delta/H}R_{L/2}
\end{pmatrix}z+0_4.
$$

On the actual image its exact guard is

$$
\mathscr G_{\rm p}=
\{z\in\mathscr S_\varepsilon:
0<\kappa(z)+\rho(t)<H\ \text{for every }t\in[0,T_{\rm p}]\}.
$$

The map intertwines the full native endpoint on all of
$\mathcal G_{\rm p}$. Every truncated path has the same assertion with
its own truncated integrals and full truncated guard. The original
uniform error bound of Theorem 5.5 holds at every such current point.

Proof. Substitute the source endpoint into the $j$th block of the
encoder, for $j=1,2$:

$$
e^{\nu_j(k+\Delta)/H}U(\alpha+L/2)
=e^{\nu_j\Delta/H}R_{L/2}
e^{\nu_jk/H}U(\alpha).
$$

This proves exact intertwining. The coefficients depend only on the
fixed model and the prescribed path, never on the starting ray.
The mixed source term $C_{\rm p}$ is present in Proposition 6.2;
it is absent here solely because $E_\varepsilon$ is independent of
$\beta$. The source dynamics have not been replaced by different
dynamics.

Proposition 6.1 identifies the inverse image of $\mathscr G_{\rm p}$
with precisely $\mathcal G_{\rm p}$, so this is the full original
guard, constant on encoder fibers. Empty guards impose no identity,
but their ambient map remains assigned. On a lawful path the
intertwining identity proves preservation of the actual image.

For any $t_0\in[0,T_{\rm p}]$, replace all upper limits by $t_0$,
and restrict the guard to $[0,t_0]$. The same integration and
substitution prove the exact intermediate encoding. This argument
also handles a lawful truncation of a path whose full extension is
unlawful: its own full truncated guard is the relevant one. At every
encoded current ray, Theorem 5.5 applies without a time-dependent
change of model or constants. $\square$

**Proposition 6.4 (Finite concatenation, every prefix and no feedback of
readout error).** For two successive relative prescribed paths, their
parameters combine as

$$
(\Delta_1,L_1,C_1)\star(\Delta_2,L_2,C_2)
=(\Delta_1+\Delta_2,\ L_1+L_2,\ C_1+C_2+\Delta_1L_2).
$$

The combined guard is the first full path guard together with the second
full path guard from height $k+\Delta_1$. From exact initialization,
the same four-coordinate model stays exactly encoded at every prefix
and every intermediate time of every finite lawful concatenation.
Its original-output error is always bounded by $4H\sqrt{T-\mu}$.

Proof. In the second piece, displacement from the original starting
height is $\Delta_1+\rho_2(t)$. The mixed integral of that piece
is consequently $C_2+\Delta_1L_2$. Adding the first piece proves
the displayed triple. Substituting this triple in Proposition 6.2
agrees with successive application: the phase increment from the
second piece contains $-\Delta_1L_2/r$ through its initial height.
The stated conjunction of all-times guards describes exactly the
combined height trajectory.

For each encoded block, the two affine maps compose as

$$
\bigl(e^{\nu_j\Delta_2/H}R_{L_2/2}\bigr)
\bigl(e^{\nu_j\Delta_1/H}R_{L_1/2}\bigr)
=e^{\nu_j(\Delta_1+\Delta_2)/H}R_{(L_1+L_2)/2}.
$$

Thus the combined encoded map agrees with Theorem 6.3, while the
source retains its additional mixed term. The commutation visible
in the encoded blocks is not a claim that the native controls
commute; the rectangle of Proposition 1.2 changes the true $\beta$.

Starting with $z^{\rm in}=E_\varepsilon(k_0,0,0)$, apply the exact
intertwining identity successively. Induction over any finite number
of paths proves exact encoding at each endpoint. The truncation
statement of Theorem 6.3 proves every intermediate point as well.
Straight legs are included, using their corresponding prescribed
velocities; fractional legs give their intermediate encodings. The
uniform readout estimate is evaluated on each exact current encoding.
No approximate decoded output is fed back into an update, so no
readout error accumulates with the length of the history. There is
no uniform bound on that finite length or on its finite real command
parameters. $\square$

## 7. Matching comparisons in all four contracts

**Proposition 7.1 (The exact two-coordinate comparator in the combined
class).** Set

$$
E_*(k,\alpha,\beta)=2H\sqrt T\,e^{\lambda k/H}U(\alpha),\qquad
\mathcal D_*(z)=D(z,0).
$$

This model belongs to $\mathfrak F_{\le2,\mathsf{GP}}$ and has error
exactly $4H\sqrt T$. Consequently

$$
e_{2,\mathsf C}^{\rm aff}(Z)=4H\sqrt T
\quad\text{for every }
\mathsf C\in\{\mathsf L,\mathsf G,\mathsf P,\mathsf{GP}\}.
$$

Proof. This is the attaining annulus of [M, §§8–9]. Its exact image is

$$
\mathscr A_*=
\{z\in\mathbb R^2:2H\sqrt{T-\tau}<\|z\|<2H\sqrt T\},
$$

since $\lambda<0$ and $e^\lambda=\sqrt{(T-\tau)/T}$.
On this actual image,

$$
\kappa_*(z)=\frac H\lambda
\log\frac{\|z\|}{2H\sqrt T}
$$

recovers exactly $k$. Its fibers are the $\beta$ circles at fixed
$(k,\alpha)$, its affine hull is the whole plane, and its exact
initial value is $2H\sqrt T e^{\lambda k_0/H}U(0)$.
For all signed real commands and every prescribed path, the maps are

$$
\mathcal U_s^*(z)=e^{\lambda s/H}z+0_2,\qquad
\mathcal V_t^*(z)=R_{t/2}z+0_2,\qquad
\mathcal W_{\rm p}^*(z)=e^{\lambda\Delta/H}R_{L/2}z+0_2.
$$

Substituting the native endpoints proves these identities exactly as
for each block in §6. The straight guard is
$0<\kappa_*(z)+s<H$, and the full path guard is
$0<\kappa_*(z)+\rho(t)<H$ at every prescribed time. The same
substitution, truncation and concatenation arguments therefore put
this single model in the combined class, without changing its two
coordinates or the full guards.

Its pointwise squared error, by Lemma 1.4, is

$$
4\bigl(2H f(k/H)-A(k)\bigr)^2+4Zk=16H^2F_0(k/H).
$$

Theorem 3.5 bounds this by $16H^2T$, and equality occurs at the
actual interior height $k=Hx_*$ for every phase pair. Its error
is exactly $4H\sqrt T$; no endpoint ray is needed for attainment.

For any of the four contracts, subclass inclusion and Proposition 3.3
give

$$
4H\sqrt T=e_{2,\mathsf L}^{\rm aff}(Z)
\le e_{2,\mathsf C}^{\rm aff}(Z)
\le\operatorname{err}(E_*,\mathcal D_*)=4H\sqrt T.
$$

Both inequalities are now supported by models and a lower bound for
the correct classes. Equality of these capacities does not identify
the classes of all admissible models. $\square$

**Theorem 7.2 (Actual four-coordinate strict affine improvement).** For
every arbitrary fixed preparation and every $0<Z<2/3$, the model
of §§5–6 uses exactly four stored real coordinates, has actual affine
hull $\mathbb R^4$, and belongs to the combined class. In each of
the four contracts,

$$
\boxed{
e_{4,\mathsf C}^{\rm aff}(Z)
\le\operatorname{err}(E_\varepsilon,\mathcal D_\varepsilon)
\le4H\sqrt{T-\mu}
<4H\sqrt T=e_{2,\mathsf C}^{\rm aff}(Z).}
$$

The explicit certified squared improvement and additive improvement are
respectively

$$
\bigl(e_{2,\mathsf C}^{\rm aff}(Z)\bigr)^2
-\bigl(e_{4,\mathsf C}^{\rm aff}(Z)\bigr)^2
\ge16H^2\mu>0,
$$

$$
e_{2,\mathsf C}^{\rm aff}(Z)-e_{4,\mathsf C}^{\rm aff}(Z)
\ge
\frac{4H\mu}{\sqrt T+\sqrt{T-\mu}}>0.
$$

Proof. Propositions 5.2 and 5.4 give the dimension, actual affine hull,
initialization and all straight affine maps, including their zero
offsets. Section 6 proves the full guard and prescribed-path obligations
for the same encoder and decoder. Thus the model belongs to
$\mathfrak F_{\le4,\mathsf{GP}}$, and hence to every weaker class.
Theorem 5.5 supplies its error bound. Proposition 7.1 supplies the
exact two-coordinate comparator in each corresponding class.
Theorem 4.6 gives $0<\mu<T-\tau<T$, so the square roots are
positive and the strict comparison follows. Squaring the bounds and
rationalizing
$4H(\sqrt T-\sqrt{T-\mu})$ gives the two displayed margins.
They also bound the improvement of the actual displayed witness over
the two-coordinate optimum. $\square$

For each fixed $Z$, all scalar constants are fixed before a current
state or producing history is selected. They are independent of that
state, the phase coordinates, the arbitrary preparation phases and
the finite history length. Preparation only fixes initialization and
the rotations of the single decoder. The certified tolerance
$4H\sqrt{T-\mu}$ is achieved as an upper bound by this actual model,
but it is not asserted to equal its exact error or the four-dimensional
infimum. Nothing here asserts attainment of that infimum.

## 8. Scalar limits and the separate transition witness

**Proposition 8.1 (Scalar boundary values do not add source states).**
For a fixed $0<\tau<1$, the scalar profiles satisfy

$$
\begin{array}{c|cc}
&x=0&x=1\\\hline
f(x)&\sqrt T&\sqrt{T-\tau}\\
v(x)&\sqrt T&\sqrt{T-\tau}\\
g(x)&-2\sqrt T&-2\sqrt{T-\tau}\\
F_0(x)&T&T
\end{array}
$$

and $g'(x)\to+\infty$ at $0$ and $g'(x)\to-\infty$ at $1$.
For the perturbed radius the endpoint limits are

$$
R_\varepsilon(0)=\sqrt T(1-\varepsilon\eta),\qquad
R_\varepsilon(1)=\sqrt{T-\tau}
\bigl[(1+\varepsilon a)e^{\varepsilon b}-\varepsilon e^{-1}\bigr].
$$

Its scalar squared-error limits at both ends obey
$F_\varepsilon\le T-\mu$.

Proof. These values follow by substituting into the explicit scalar
formulas; the derivative limits are those proved in Lemma 3.4.
Theorem 4.6 includes both endpoints and yields the final bounds.
They are limits of errors along interior heights. The actual image
in Proposition 5.2 has strict radius inequalities and excludes those
boundary circles. No encoder value, command identity or new phase
identification on $k=0,H$ is asserted. $\square$

**Proposition 8.2 (Parameter limits and fixed-$Z$ scope of the margin).**
With $T=T_\tau$, $\lambda=\lambda_{T_\tau}$ and $x_*=x_\tau$,

$$
\begin{array}{c|cccc}
&T&\lambda&x_*&4H\sqrt T\\\hline
\tau\downarrow0&1/16&0&1/2&1/2\\
\tau\uparrow1&1&-\infty&1&2/3
\end{array}
$$

The certified $\mu$ tends to zero as $\tau\uparrow1$. Neither the
certified margin nor the best capacity improvement admits a common
strictly positive additive lower bound for all $0<Z<2/3$.

Proof. These comparator limits are those of [M, Proposition 10.4].
Their needed scalar argument is as follows. Solving the relation
between the parameters gives

$$
Z=\frac{2\tau}{1+2\tau},\qquad
H=\frac1{2(1+2\tau)}.
$$

As $\tau\uparrow1$, the inequalities

$$
\tau<T<\frac{(1+\tau)^2}{4},\qquad
0<T-\tau<\frac{(1-\tau)^2}{4}
$$

give $T\to1$, $T-\tau\to0$ and $\lambda\to-\infty$.
The bound $(1+\tau)/2<x_*<1$ gives $x_*\to1$.
The formula for $H$ then gives $4H\sqrt T\to2/3$.

For $\tau\downarrow0$, fix a trial level $t>0$. For sufficiently
small $\tau$, $t>\tau$ and $v_t,f_t$ converge uniformly on
$[0,1]$ to $\sqrt t$. For $v_t$, rationalizing its difference from
$\sqrt t$ gives a uniform bound tending to zero. For $f_t$, use
$\lambda_t\to0$ and $0\le x\le1$. Therefore

$$
\Phi_\tau(t)\longrightarrow\frac12-2\sqrt t.
$$

For any fixed $0<t_-<1/16<t_+$, the limiting signs at $t_-,t_+$
are respectively positive and negative. The unique decreasing-root
criterion puts $t_-<T<t_+$ for all sufficiently small $\tau$.
Letting these brackets approach $1/16$ proves $T\to1/16$.
It follows that $\lambda\to0$ and $4H\sqrt T\to1/2$.
At these varying roots, $g_T$ converges uniformly to $s-1/2$.
Outside any neighborhood of $1/2$, that limit has a strictly
negative compact maximum. Since $g_T(x_*)=0$, uniform convergence
forces $x_*\to1/2$.

Finally, Theorem 4.6 gives
$0<\mu<(T-\tau)/8$, so $\mu\to0$ as $\tau\uparrow1$.
More generally, the literal floor of Theorem 2.3 remains valid on
every subclass, while Theorem 7.2 and Proposition 7.1 give

$$
0<e_{2,\mathsf C}^{\rm aff}-e_{4,\mathsf C}^{\rm aff}
\le 4H\bigl(\sqrt T-\sqrt\tau\bigr)\longrightarrow0.
$$

Thus even the actual capacity difference cannot have a positive
lower bound common to the entire open $Z$ range. This does not
determine the optimal margin at any fixed $Z$. The exponents
$\nu_1,\nu_2$ also tend to $-\infty$ at the transition, because
their differences from $\lambda$ are bounded. These are parameter
limits, not finite exponential parameters defining a transition
model. At $Z=0$ the positive middle amplitude is absent and the
ray identification changes; no theorem at that parameter is
obtained by this limit. $\square$

**Theorem 8.3 (Separate equality witness at $Z=2/3$).** At the
transition itself, all four contracts satisfy

$$
e_{2,\mathsf C}^{\rm aff}(2/3)
=e_{4,\mathsf C}^{\rm aff}(2/3)=\frac23.
$$

A height encoder with zero decoder achieves this value. It has exact
initialization, every original guard and every prescribed path; it is
not an endpoint extension of the divergent exponential construction.

Proof. Here $H=1/6$, $Z=4H$ and $2\sqrt{ZH}=2/3$. Use

$$
E_{\rm h}(k,\alpha,\beta)=K=k,\qquad
\mathcal D_{\rm h}(K)=0_{10},\qquad K^{\rm in}=k_0.
$$

Its actual image is $(0,H)$. For every real straight command the
affine maps are $K\mapsto K+s$ and $K\mapsto K$, with exact
probability guard $0<K+s<H$. For a prescribed path use
$K\mapsto K+\Delta$ with the full guard
$0<K+\rho(t)<H$ for every time. The exact height integration in
Proposition 6.2, and its truncations and concatenations, proves all
required identities. This one-coordinate model fits both at-most
budgets two and four in every contract.

Its original squared error is

$$
16k(H-k)+4Zk=4ZH-16(H-k)^2<4ZH\qquad(0<k<H),
$$

with supremum $4ZH$ as interior $k\uparrow H$. Thus the model's
error is $2/3$, even though no lawful state maximizes that error.
Theorem 2.3 supplies the lower floor for both literal budgets, and
subclass inclusion supplies it for the stronger variants. The
displayed model supplies the matching upper bounds. Its affine
probability offset is the prescribed real number $s$; its path
offset is $\Delta$. No divergent exponential limit is used as a
model. $\square$

## 9. Result map, source credit and unresolved optimization

The assertions in this volume have the following dependencies and roles.

| Result | Declarations | Role in the strict comparison |
|---|---|---|
| Native current-ray and output interface | 1.1–1.4 | Arbitrary preparation, actual reachability, every signed command and the original Gram factors |
| Literal and stronger model classes | 2.1–2.2 | At-most coordinate budgets, offsets, unrestricted competitors and exact subclass inclusions |
| Published all-competitor lower interface | 2.3 | [M, Theorem 6.4] and the bounded-observable floor from [A, §§3–4] |
| Scalar root and exhaustive contacts | 3.1–3.5 | Exact comparator parameters, strict upper corridor and active set exactly $\{0,x_*,1\}$ |
| Fixed perturbation and compact-gap estimate | 4.1–4.6 | Descent at all contacts, nonempty $K$, positive $d$, uniform Taylor remainder and prescribed $\varepsilon,\mu$ |
| Actual four-coordinate affine witness | 5.1–5.5 | Image, fibers, full affine hull, original decoder, signed updates, initialization and original-metric error identity |
| Full guards and prescribed paths | 6.1–6.4 | Exact recovered height, mixed source term, all-times domains, every truncation and finite concatenation |
| Contract-matched strict inequalities | 7.1–7.2 | One attaining two-coordinate comparator and one improving four-coordinate model in the combined class |
| Limits and transition | 8.1–8.3 | Scalar endpoints only, fixed-$Z$ positive margin, parameter limits and a separate height-only equality witness |

The native transport, actual-ray identification, original ten-output
factorization and simultaneous-path mixed term are inherited from the
suppliers named at the beginning. Their arguments are reconstructed here
where needed to verify that the witness addresses the original source.
The bounded-observable floor and exhaustive two-dimensional minimax
reduction are reused with the exact correspondence in Theorem 2.3.
The root, lower contact and two-coordinate annulus are from [M, §§7–9];
their necessary properties are exposed here so that the perturbation
and the comparison in each stronger class can be checked directly.

Relative to those two mathematical suppliers, the substantive addition
is the exhaustive three-point active-set argument used for the specified
signed two-exponential descent, its positive compact-complement gap and
uniform explicit remainder certificate, and the actual four-coordinate
realization of that same perturbed radius. The realization includes its
exact image, full four-dimensional affine hull, radius-based height
recovery, original decoder and complete path contract. A two-dimensional
manifold image is compatible with a four-dimensional affine hull; it
does not turn this model into a two-coordinate affine competitor.

The arguments use elementary real calculus, strict concavity, the
intermediate value theorem, compact extrema, Taylor's formula, finite
linear algebra and exact integration. Source credit specifies the
inherited theorems; publication status or an endorsement is not a
substitute for a mathematical premise or one of the new proofs. No
worldwide-originality or exhaustive-literature claim is made.

The remaining boundaries are part of the result:

- For $0<Z<2/3$, the exact value of $e_{4,\mathsf C}^{\rm aff}$,
  attainment of its own infimum, and the optimal strict margin remain
  unresolved in each contract. The displayed positive certificate is
  sufficient, not optimal. Equality between the four four-dimensional
  capacities is not asserted.
- The least dimension permitting strict improvement over the
  two-coordinate optimum remains unresolved. No three-dimensional
  plateau is a premise or a conclusion, and no dimension-parity law or
  general larger-dimension classification follows here.
- Every source state is an actual current ray with $0<k<H$ and
  $0<Z<1$, with the strict improvement restricted to $0<Z<2/3$.
  Scalar support limits do not add endpoint states, retained lifts,
  history inputs or external height. The positive margin is uniform
  over the full original open source for fixed $Z$, and over all
  finite lawful histories, not uniformly positive over the entire
  parameter interval up to the transition.
- Only the displayed encoders have the specified $\beta$-circle
  fibers. The inherited erasure theorem concerns bounded affine
  observables; it does not classify unbounded hidden coordinates or
  every finite affine factor. No regularity hypothesis is imposed on
  the competitors in the lower comparison.
- Noninjectivity and nonphysical decoded vectors are allowed by the
  contract. Requiring a native physical output, injectivity, a different
  norm or a restricted command menu would change the problem and would
  require its own comparison. All preparation rotations and all ten
  original outputs remain present in the result proved here.
- The exact constants, initialization, command coefficients and path
  integrals are real mathematical quantities. No finite-bit storage,
  conditioning, noise robustness, acquisition, efficient computation,
  physical implementation, training or empirical machine-learning
  consequence is supplied. The original finite-hidden-$N$ alternative
  has no proved identification with this objective and remains
  unresolved. These are handwritten results, not kernel-verified
  declarations.

## 追加锚（本行以下为增补区）
