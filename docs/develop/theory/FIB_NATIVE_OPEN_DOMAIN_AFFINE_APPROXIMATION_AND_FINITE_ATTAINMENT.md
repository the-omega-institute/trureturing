# Native FIB on the full open domain: affine approximation and finite attainment

Fix $0<Z<1$, and set

$$
r=1-Z,\qquad H=\frac r2,\qquad e_0=2\sqrt{ZH}.
$$

For the actual native current rays on $(0,H)\times\mathbb T^2$, with
$\mathbb T=\mathbb R/(2\pi\mathbb Z)$, consider arbitrary finite real
encoders, exact state-independent affine updates for all lawful real
probability and phase commands, and one fixed affine decoder into the
original ten outputs with their original Euclidean norm. The infimum of
uniform output errors is $e_0$. The achievable tolerances are exactly

$$
\begin{cases}
(e_0,\infty),&0<Z<2/3,\\
[e_0,\infty),&2/3\le Z<1.
\end{cases}
$$

The same classification holds when every prescribed simultaneous native
path, with its full all-times guard, is also required. The lower result
allows irregular, unbounded and noninjective encoders and both affine
offsets. The upper results give explicit exact-real finite models on the
entire open domain. In the attaining range a stored height and the zero
decoder suffice. In the other range finite dimension prevents attainment,
even though one finite model exists for every tolerance strictly above
$e_0$.

The source conventions come from *Native FIB continuation: exact affine
obstruction and compact-band approximation*. Its source and output
identifications are reconstructed below, rather than used as unstated
bridges. The present question concerns full-open affine approximation;
it is different from the original finite-hidden-$N$ attainment alternative.
Source credit and the precise limits of the classification appear in §10.

## 1. The native source and the original metric

### 1.1 Probabilities, arbitrary preparation and transport

Use the mode order $(0,1,2,3,13)$. On the native double wall $X=Y=H$,
fix the probability curve and its tangent by

$$
p(k)=(k,H-k,Z,H-k,k),\qquad 0<k<H,
\qquad d=(1,-1,0,-1,1)^{\mathsf T}.
$$

All five probabilities are positive and sum to $2H+Z=1$.
Choose any fixed preparation height $k_0\in(0,H)$ and any fixed
preparation phases $\theta^{\rm in}_s$. They need not be equal within
any group. With the native negative phase convention, the amplitudes and
transport equations are

$$
\psi_s=\sqrt{p_s}\,e^{-i\theta_s},\qquad
\dot p=d\dot k,\qquad
\dot\theta_s=w_s(k)\dot\chi,\qquad
w_s(k)=\frac{d_s}{p_s(k)I(k)},
$$

$$
I(k)=\frac1{p_0(k)}+\frac1{p_1(k)}+
     \frac1{p_3(k)}+\frac1{p_{13}(k)}.
$$

Here $k$ and $\chi$ are the original controls. A producing history is a
piecewise $C^1$ or absolutely continuous path on a finite compact time
interval, with $k$ strictly between $0$ and $H$ throughout and with finite
phase variation. The initial real relation phase is chosen consistently
with $d^{\mathsf T}\theta^{\rm in}$. Queries are allowed at any finite
prefix; no return loop or integer winding is required. Real lifts may be
used to integrate a history, but the current state is its ray, not a lift.

**Lemma 1.1 (Phase equations).** Write $h=\theta-\theta^{\rm in}$.
Every history has increments

$$
h=(u,v,0,v,u),
$$

and, with $\alpha=u-v$ and $\beta=u$,

$$
\begin{aligned}
I(k)&=\frac2k+\frac2{H-k}=\frac r{k(H-k)},\\
w_+(k)&=\frac12-\frac kr,\qquad
w_-(k)=-\frac kr,\qquad w_2(k)=0,\\
du&=\left(\frac12-\frac kr\right)d\chi,
&dv&=-\frac kr\,d\chi,\\
d\alpha&=\frac12d\chi,
&d\beta&=\left(\frac12-\frac kr\right)d\chi.
\end{aligned}
$$

**Proof.** The reciprocal sum gives the displayed $I$. Dividing the
positive and negative entries of $d$ by their corresponding $p_sI$
gives $w_+=(H-k)/r=1/2-k/r$ and $w_-=-k/r$. Equal transport
coefficients give equal increments in modes $0,13$ and in modes $1,3$,
starting from zero increments. The middle increment stays zero. This
asserts equality of increments only, with no restriction on preparation
phases. Subtraction gives $d(u-v)=d\chi/2$.
The inverse coordinate change $u=\beta$, $v=\beta-\alpha$ has integer
coefficients, as does the forward change, so both descend to inverse
maps of $\mathbb T^2$. Along real lifts,
$d^{\mathsf T}h=2(u-v)=\chi-\chi(0)$. $\square$

Put $\eta_s=\theta_s^{\rm in}-\theta_2^{\rm in}$. A constant common
gauge gives the representative

$$
\psi(k,u,v)=\left(
\sqrt{k}e^{-i(\eta_0+u)},\
\sqrt{H-k}e^{-i(\eta_1+v)},\
\sqrt Z,\
\sqrt{H-k}e^{-i(\eta_3+v)},\
\sqrt{k}e^{-i(\eta_{13}+u)}
\right).
$$

Its middle coordinate is fixed and positive. Equality of two such rays
therefore forces equality of the representatives. Their moduli determine
$k$, and the positive group amplitudes then determine $u$ and $v$
separately modulo $2\pi$. Conversely these data determine the ray.
There is no extra parity identification or quotient by a common bottom
phase: the positive middle amplitude remains present.

### 1.2 Exact reachability and actual relative commands

**Proposition 1.2 (Full current-ray domain).** From the one fixed
preparation the exact reachable current-ray space is

$$
\mathcal M=(0,H)\times\mathbb T^2,
$$

in coordinates $(k,\alpha,\beta)$. Every point has a finite lawful
producing history using just the original controls.

**Proof.** Fix $k_1\in(0,H)$ different from $k_0$ and write
$d_k=k_1-k_0$. For a target choose real representatives $u,v$ merely
to specify a producing path. Set

$$
L=2(u-v),\quad
u_L=\left(\frac12-\frac{k_0}{r}\right)L,\quad
v_L=-\frac{k_0}{r}L,\quad
q=u-u_L=v-v_L.
$$

The equality defining $q$ follows from $u_L-v_L=L/2=u-v$.
Take the real rectangle parameter $A_{\rm rect}=-rq/d_k$.
First move from $k_0$ to $k_1$ at fixed $\chi$, then increase
$\chi$ by $A_{\rm rect}$ at $k_1$, return to $k_0$ at fixed
$\chi$, and decrease $\chi$ by $A_{\rm rect}$ there. The net
increment in each of $u,v$ is

$$
A_{\rm rect}\bigl(w_\pm(k_1)-w_\pm(k_0)\bigr)
=-A_{\rm rect}d_k/r=q.
$$

Next apply one phase leg of increment $L$ at $k_0$, and then a
probability leg from $k_0$ to the target $k$. The resulting increments
are $(q+u_L,q+v_L)=(u,v)$. All heights along the probability legs lie
between interior endpoints, and all phase parameters are finite. This is
a finite piecewise linear history. Lemma 1.1 gives the converse inclusion
of all reachable rays in the displayed domain. The representative above
proves that the parameterization identifies precisely equal rays.
Independent reachable phase coordinates have thus been obtained without
introducing independent phase controls. $\square$

For every real command parameter $s$ or $t$, the original straight legs
induce

$$
P_s(k,\alpha,\beta)=(k+s,\alpha,\beta),
\qquad \operatorname{dom}P_s=\{(k,\alpha,\beta)\in\mathcal M:0<k+s<H\},
$$

$$
Q_t(k,\alpha,\beta)=
\left(k,\alpha+\frac t2,\beta+\left(\frac12-\frac kr\right)t\right),
\qquad \operatorname{dom}Q_t=\mathcal M.
$$

Indeed $P_s$ prescribes $k(\tau)=k+\tau s$ with $\chi$ fixed, and
$Q_t$ prescribes constant $k$ and phase increment $t$ on a unit interval.
Lemma 1.1 integrates to these formulas. Convexity of $(0,H)$ makes
$0<k+s<H$ necessary and sufficient for the whole straight probability
leg to be lawful. The real phase parameter $t$ is not reduced modulo
$2\pi$ or any other period. Circle reduction applies to the resulting
state coordinates.

### 1.3 The ten outputs, preparation rotations and their Gram matrix

The ordered edge menu is

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)).
$$

For each edge use the original Hermitian observables

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,
\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|.
$$

Write $\delta_{ij}=\theta_i^{\rm in}-\theta_j^{\rm in}$. Their
ordered expectation pair is

$$
y_{ij}=2\sqrt{p_ip_j}
\begin{pmatrix}
\cos(\delta_{ij}+h_i-h_j)\\
\sin(\delta_{ij}+h_i-h_j)
\end{pmatrix}.
$$

Concatenating these five pairs defines $y:\mathcal M\to\mathbb R^{10}$.
All errors in this volume are measured by the ordinary Euclidean norm on
these ten entries, including their original factors of two.

For later use define

$$
U(a)=\binom{\cos a}{\sin a},\qquad
R_a=\begin{pmatrix}\cos a&-\sin a\\\sin a&\cos a\end{pmatrix},
\qquad J=\operatorname{diag}(1,-1),
$$

$$
A(k)=2\sqrt{k(H-k)},\qquad B(k)=2\sqrt{Zk},
$$

$$
D_0(a,b)=(a,b,a,Ja,Ja),\qquad
O=\bigoplus_{(i,j)\in\mathcal E}R_{\delta_{ij}},\qquad D=OD_0.
$$

Here $a,b\in\mathbb R^2$, so $D$ maps $\mathbb R^4$ into
$\mathbb R^{10}$.

**Lemma 1.3 (Original output factorization).** For arbitrary fixed
preparation,

$$
y(k,\alpha,\beta)=D(A(k)U(\alpha),B(k)U(\beta)),
\qquad D^{\mathsf T}D=4I_2\oplus I_2.
$$

In particular,

$$
\|D(a,b)\|_2^2=4\|a\|_2^2+\|b\|_2^2.
$$

**Proof.** The negative exponential convention gives
$\overline\psi_i\psi_j=\sqrt{p_ip_j}e^{i(\theta_i-\theta_j)}$.
The two expectations are twice its real and imaginary parts. The five
increment differences are, in their declared order,
$\alpha,\beta,\alpha,-\alpha,-\alpha$. Since $U(-a)=JU(a)$,
this gives $D_0$ followed by the fixed preparation rotations $O$.
The four copies of the first pair each contribute $I_2$ to its Gram
matrix; the second pair contributes one $I_2$. There are no cross terms
between these pairs, and $O,J$ are orthogonal. This proves the identities.
In particular $D$ is injective. Also $k(H-k)\le H^2/4$, so
$A(k)\le H$ and $B(k)<e_0$. Thus $y$ is uniformly bounded on
$\mathcal M$. $\square$

These formulas express the original metric, not a change of that metric.
They also show that the outputs distinguish current rays: the rotated
$02$ pair has squared norm $4Zk$, determining $k$, and normalization
of the rotated $01$ and $02$ pairs then determines the two circle
coordinates. This uses mathematical ideal outputs and chooses no real
angle branch or measurement procedure.

## 2. The finite affine contract and the classification statement

**Definition 2.1 (Achievable tolerance).** A real number $\epsilon\ge0$
is achievable if there are a finite integer $n\ge0$, an arbitrary
function $E:\mathcal M\to\mathbb R^n$, one fixed affine decoder

$$
q(x)=c+LE(x)\in\mathbb R^{10},
$$

and, for every real $s,t$, fixed ambient affine maps

$$
\mathcal U_s(z)=A_sz+b_s,\qquad
\mathcal V_t(z)=C_tz+d_t,
$$

such that

$$
E(P_sx)=\mathcal U_s(E(x))\quad(x\in\operatorname{dom}P_s),
\qquad
E(Q_tx)=\mathcal V_t(E(x))\quad(x\in\mathcal M),
$$

$$
\operatorname{err}(E,q):=
\sup_{x\in\mathcal M}\|q(x)-y(x)\|_2\le\epsilon.
$$

The coefficients may depend on the fixed source, preparation, model and
command, but never on the current state or producing history. No
continuity, measurability, boundedness or injectivity is imposed on $E$.
No continuity in the command parameter, invertibility of the ambient
matrices, or ambient group law is assumed. Both decoder and update
offsets are permitted. Conditions on probability commands apply exactly
on their lawful partial domains; an empty domain imposes no identity.
All signs, zero commands and all finite lawful histories are included.

The state remains an actual current ray. An external current-height
selector, a chosen real lift, a history coordinate or an endpoint state
is not an extra input. The explicit models below store the height
internally and implement the exact source guards on their actual images.
Decoded vectors need not be native physical outputs. Initialization and
updates mean exact real values; no floating-point assumption is part of
the contract.

**Theorem 2.2 (Complete full-open classification).** For every fixed
preparation and $0<Z<1$, Definition 2.1 has achievable tolerance set

$$
\mathcal A_Z=
\begin{cases}
(e_0,\infty),&Z<2/3,\\
[e_0,\infty),&Z\ge2/3,
\end{cases}
\qquad e_0=2\sqrt{ZH}=\sqrt{2Z(1-Z)}.
$$

Consequently the infimum of errors over all finite models is $e_0$.
For every $\epsilon>e_0$, one explicit sufficient dimension is $2m+3$,
where

$$
\Delta_\epsilon=\epsilon^2-4ZH,\qquad
m=\max\left\{1,\left\lceil
\left(\frac{8H^2}{\Delta_\epsilon}\right)^2
\right\rceil\right\}.
$$

For $Z\ge2/3$, a one-coordinate height encoder with zero decoder
attains the infimum. These are sufficient dimensions, with no
minimum-dimension assertion. The conclusions persist under the larger
prescribed-path contract in §9.

The proof is assembled from the bounded-observable result in §3, the
metric floor in §4, the nonattainment proof in §§5–6, and the constructions
in §§7–9.

## 3. What bounded affine observables can retain

This section uses only the exact affine update identities and finite
dimension. Boundedness will be imposed on particular observables, not on
the encoder.

### 3.1 One function space for all heights

Homogenize the encoder and update maps by setting

$$
F(x)=\begin{pmatrix}1\\E(x)\end{pmatrix}\in\mathbb R^N,
\qquad N=n+1,
$$

$$
T_s=\begin{pmatrix}1&0\\b_s&A_s\end{pmatrix},\qquad
S_t=\begin{pmatrix}1&0\\d_t&C_t\end{pmatrix}.
$$

Then $F(P_sx)=T_sF(x)$ and $F(Q_tx)=S_tF(x)$ on their respective
domains. Every fixed affine scalar functional of $E$ is a fixed linear
functional of $F$. This includes all offsets without bounding them.

At an interior height $k$, let

$$
V_k=\operatorname{span}_{\mathbb C}
\{\theta\mapsto F_i(k,\theta):1\le i\le N\},
\qquad \theta=(\alpha,\beta)\in\mathbb T^2,
$$

as a space of pointwise functions, not equivalence classes modulo null
sets. For two interior heights $k,l$, the command $P_{l-k}$ is lawful
at every phase point at height $k$, so

$$
F(l,\theta)=T_{l-k}F(k,\theta).
$$

Thus $V_l\subseteq V_k$. Reversing the displacement gives the reverse
inclusion. All these spaces equal one space $V$ of dimension at most $N$.
This uses inverse source commands, not invertibility of their ambient
matrices.

For $v\in\mathbb T^2$ write $(\tau_vf)(\theta)=f(\theta+v)$.
The phase identity at height $k$ makes $V$ invariant under

$$
\tau_{v(k,t)},\qquad
v(k,t)=\left(\frac t2,c(k)t\right),\qquad
c(k)=\frac12-\frac kr.
$$

The inverse command gives inverse invariance as well. Choose two
distinct heights. The two real vectors $(1/2,c(k))$ obtained this way
are linearly independent: their determinant is half the nonzero
difference of the two $c(k)$ values. Every real two-vector is a real
linear combination of these directions. Translating by its circle class
is therefore a composition of two of the above translation operators.
It follows that $V$ is invariant under every torus translation.
This is a conclusion about operators on the common function space;
it adds no commands to the native control menu.

### 3.2 Bounded functions and possibly discontinuous characters

Let

$$
W=\{f\in V:\|f\|_\infty:=\sup_{\theta\in\mathbb T^2}|f(\theta)|<\infty\}.
$$

This is a finite-dimensional complex vector space with a genuine norm.
Translations on $W$ are commuting invertible isometries: torus translation
is a bijection of all points, so it leaves the supremum unchanged.

**Lemma 3.1 (Character basis without regularity).** The space $W$ has
a basis of common translation eigenfunctions. Every nonzero common
eigenfunction is a nonzero constant times an abstract unitary character
of $\mathbb T^2$; that character need not be continuous or measurable.

**Proof.** First consider one invertible isometry $A$ on a finite
complex normed space. An eigenvector gives $|\lambda|=1$ for its
eigenvalue. A nontrivial Jordan block would supply vectors $u\ne0,v$
with $Au=\lambda u$ and $Av=\lambda v+u$. Induction gives

$$
A^jv=\lambda^jv+j\lambda^{j-1}u,
$$

whose norm is at least $j\|u\|-\|v\|$, contradicting
$\|A^jv\|=\|v\|$. Hence every such isometry is diagonalizable.
Here the usual finite complex generalized-eigenspace decomposition is
pure linear algebra; no function regularity is involved.

A commuting family of these maps has a common eigenbasis even if the
family is infinite. If every member is scalar, any basis works. Otherwise
split into the eigenspaces of a nonscalar member. All other members and
their inverses preserve these spaces by commutation, and restrict to
isometries. Each eigenspace has smaller dimension; induction gives a
common eigenbasis in each. Their union proves the assertion. In dimension
zero there is nothing to prove.

For a nonzero common eigenfunction $f$, write
$\tau_vf=\lambda(v)f$. All eigenvalues have modulus one, and the
actual translation law implies

$$
\lambda(v+w)=\lambda(v)\lambda(w),\qquad \lambda(0)=1.
$$

Evaluating at zero gives $f(v)=\lambda(v)f(0)$. If $f(0)=0$ then
$f$ vanishes at every point, a contradiction. Thus $f$ is the claimed
constant multiple of a character. In particular,

$$
\lambda(\alpha,\beta)=\lambda_1(\alpha)\lambda_2(\beta),
$$

where the two factors are its restrictions to the two circle subgroups.
No topological classification of characters has been used. $\square$

### 3.3 A fixed command has a finite spectrum across all heights

For each $k$, define the surjection

$$
\pi_k:\mathbb C^N\longrightarrow V,\qquad
\pi_k(a)(\theta)=a^{\mathsf T}F(k,\theta).
$$

The phase update gives the intertwining identity

$$
\tau_{v(k,t)}\pi_k=\pi_k S_t^{\mathsf T}.
$$

The kernel of $\pi_k$ is consequently invariant under $S_t^{\mathsf T}$.
Choose a basis adapted to this kernel and then to the quotient. In this
basis the matrix is block triangular, and the quotient block represents
$\tau_{v(k,t)}$ on $V$. Factoring the characteristic polynomial of that
block triangular matrix proves that every eigenvalue of this translation
on $V$ belongs to the finite spectrum of $S_t$. The kernel can vary
with height, but $S_t$ and its spectrum are fixed for the command $t$.

In particular, a character from Lemma 3.1 obeys

$$
\lambda_1(t/2)\lambda_2(c(k)t)\in\operatorname{spec}(S_t)
\quad\hbox{for every }0<k<H.
$$

Here circle arguments are understood modulo $2\pi$. No relation between
ambient matrices for different commands has been assumed.

**Lemma 3.2 (Finite interval image of an abstract character).** Let
$h:(\mathbb R,+)\to\{z\in\mathbb C:|z|=1\}$ be a group
homomorphism. If its image on one nonempty open interval is finite,
then $h$ is identically one.

**Proof.** The image group is divisible: for any $h(y)$ and positive
integer $q$, the element $h(y/q)$ is a $q$th root in the image.
Suppose the image is nontrivial. Its element orders cannot all be at
most any fixed integer $M\ge1$. If they were, every element raised
to $M!$ would be one. Divisibility would then imply that every element
itself is one, because it is an $M!$th power of an image element.
Thus, for any $M$, the image contains an element of order greater than
$M$, with infinite order allowed.

Now suppose an interval $I$ has at most $M$ image values. Let $a$
be its midpoint after taking a smaller finite open subinterval if
necessary, and let $\ell>0$ be that subinterval's length. Choose $y$
so that $h(y)$ has order greater than $M$. Choose a positive integer
$q$ with $M|y|/q<\ell/2$. All $M+1$ points

$$
a+j y/q,\qquad 0\le j\le M,
$$

lie inside the subinterval. The order of $h(y/q)$ is greater than $M$,
since its $q$th power is $h(y)$. Their images
$h(a)h(y/q)^j$ are therefore distinct. This contradicts the bound $M$.
No continuity or measurability was required. $\square$

**Theorem 3.3 (Bounded affine observables lose the beta phase).** In any
finite model satisfying the exact updates of Definition 2.1, let a fixed
affine scalar functional of $E$ be bounded on every phase torus at fixed
height. That observable is independent of $\beta$. In particular, every
component of any decoded output with finite uniform error is independent
of $\beta$.

**Proof.** Set $t=1$ in the spectral inclusion. Since $0<k<H=r/2$,
the values $c(k)$ range over exactly $(0,1/2)$. Dividing the finite
set $\operatorname{spec}(S_1)$ by the nonzero number $\lambda_1(1/2)$
shows that

$$
h(x)=\lambda_2(x\bmod 2\pi)
$$

has finite image on $(0,1/2)$. Lemma 3.2 makes $h$ trivial. Every
circle class has a real representative, so $\lambda_2$ itself is
trivial. Every eigenfunction in the basis of $W$ is therefore independent
of $\beta$, and so is every function of $W$.

At each height the given affine observable belongs to $V$, by
homogenization, and its stated boundedness puts it in $W$. This proves
the first assertion. For the decoder, finite uniform error and the
uniform boundedness of $y$ give
$\|q(x)\|_2\le\epsilon+\sup_{x\in\mathcal M}\|y(x)\|_2$.
Each component is thus bounded and qualifies. The homogeneous constant
ensures that offsets have been included even when $n=0$.

Unbounded encoder coordinates need not belong to $W$. The proof says
nothing that places them there. It consequently does not classify every
encoder coordinate, every affine factor, or all encoder fibers. It is a
bounded-observable theorem, exactly sufficient for finite-error affine
readout. $\square$

## 4. The exact worst-phase error and its equality residual

A decoder is allowed to leave both the native output image and the linear
space $\operatorname{im}D$. Neither possibility can be omitted in a
lower bound.

**Proposition 4.1 (Orthogonal decomposition and the floor).** Every
finite-error decoder has a unique decomposition

$$
q(k,\alpha,\beta)=D(a(k,\alpha),b(k,\alpha))+w(k,\alpha),
\qquad w\perp\operatorname{im}D,
$$

where $a,b\in\mathbb R^2$. At each fixed $k,\alpha$, its exact
worst squared error over the full $\beta$ circle is

$$
\|w\|_2^2+4\|a-A(k)U(\alpha)\|_2^2+
\bigl(\|b\|_2+B(k)\bigr)^2.
\tag{4.1}
$$

Every achievable tolerance obeys $\epsilon\ge e_0$. At tolerance
$e_0$, the complete necessary residual inequality is

$$
\|w\|_2^2+4\|a-A(k)U(\alpha)\|_2^2+
\|b\|_2^2+2B(k)\|b\|_2\le4Z(H-k).
\tag{4.2}
$$

**Proof.** Since $D^{\mathsf T}D$ is invertible, define

$$
\binom ab=(D^{\mathsf T}D)^{-1}D^{\mathsf T}q,
\qquad w=q-D(a,b).
$$

Then $D^{\mathsf T}w=0$. This is the unique orthogonal decomposition,
and all its entries are fixed affine scalar functionals of $E$.
Theorem 3.3 makes them independent of $\beta$. Orthogonality and
Lemma 1.3 give

$$
\|q-y\|_2^2
=\|w\|_2^2+4\|a-A(k)U(\alpha)\|_2^2+
\|b-B(k)U(\beta)\|_2^2.
$$

If $b\ne0$, choosing $U(\beta)=-b/\|b\|_2$ maximizes the last
term, with value $(\|b\|_2+B(k))^2$. If $b=0$, every $\beta$
gives that value. Every such phase is an actual reachable ray by
Proposition 1.2, so this is the exact maximum for the original task.
It proves (4.1), including the output-complement term.

In particular,

$$
\epsilon^2\ge4\|a-A(k)U(\alpha)\|_2^2+4Zk
\quad(0<k<H).
$$

Taking the real supremum over the interior heights gives
$\epsilon^2\ge4ZH$. This is a supremum of values on lawful states;
it does not evaluate an encoder at $k=H$. If $\epsilon=e_0$,
expanding the last square in (4.1) and moving $B(k)^2=4Zk$ to the
right gives exactly (4.2). $\square$

Fix $\alpha=\beta=0$ and let $g(k)$ be the first component of
$a(k,0)$. Because the projection above is fixed, there is a single real
row $\ell$ with

$$
g(k)=\ell F(k,0,0).
$$

Dropping only nonnegative terms from (4.2) gives, for every $0<x<H$,

$$
\left|g(H-x)-2\sqrt{(H-x)x}\right|\le\sqrt{Zx}.
\tag{4.3}
$$

The row $\ell$ is independent of $k$. This feature of the original
fixed affine decoder will constrain finite probability histories near
the upper end of the open interval.

## 5. A finite-Hankel-rank growth lemma

The following elementary form of the finite-rank/linear-recurrence
principle supplies the needed obstruction. Its proof includes the
cancellation argument, so a spectral growth assertion is not being
assumed from a heuristic dominant term.

**Lemma 5.1 (Sublinear square-root growth is bounded at finite rank).**
Let $(b_j)_{j\ge0}$ be a complex sequence. Suppose there is a finite
integer $N\ge0$ such that every finite submatrix of its Hankel array

$$
\mathcal H=(b_{p+q})_{p,q\ge0}
$$

has rank at most $N$. If $|b_j|\le C\sqrt{j+1}$ for some finite
$C$, then the sequence is bounded.

**Proof.** For $q\ge0$ let

$$
v_q=(b_{p+q})_{p\ge0}
$$

be an actual infinite sequence, and let $X$ be the complex span of all
$v_q$. We first prove $\dim X\le N$, without presuming that infinite
matrices have an independently defined rank.

If $N+1$ columns $v_{q_1},\ldots,v_{q_{N+1}}$ were independent,
consider their coefficient space $\mathbb C^{N+1}$. The map from
coefficients to the corresponding sequence would be injective. The
coordinate evaluations on this coefficient space therefore have common
kernel zero. Finitely many already have common kernel zero: starting
with the whole coefficient space, if the current common kernel is
nonzero, choose a nonzero coefficient vector in it. Its corresponding
sequence is nonzero, so some coordinate evaluation does not vanish on
that vector. Intersecting with this evaluation's kernel strictly reduces
the dimension. After at most $N+1$ steps the common kernel is zero.
The resulting finite set of row coordinates makes the selected columns
independent in a finite Hankel submatrix, a contradiction. If
$\dim X>N$, independent columns could be chosen successively from its
generating family, so this argument proves the dimension bound.

Coordinate shift on sequences restricts to a linear map $S:X\to X$,
since it sends $v_q$ to $v_{q+1}$. Let $e:X\to\mathbb C$ be
evaluation at coordinate zero. Then

$$
b_j=e(S^jv_0).
\tag{5.1}
$$

If $X=0$, all $b_j$ vanish and the conclusion follows. Otherwise
$S$ is a finite complex matrix. The standard generalized-eigenspace
decomposition can be obtained algebraically as follows. Factor its
characteristic polynomial over $\mathbb C$ into the relatively prime
powers $(z-\lambda)^{d_\lambda}$. The Cayley–Hamilton identity
annihilates $S$. Bezout identities for these relatively prime factors
express the identity map as a sum of polynomial maps in $S$ with images
in the kernels of the corresponding $(S-\lambda I)^{d_\lambda}$.
Their pairwise intersections are zero by the same Bezout identity.
Thus $X$ is the direct sum of invariant generalized eigenspaces.
On each of them $S=\lambda I+R$ with $R$ nilpotent. This also
explains the only finite-dimensional spectral decomposition needed here.

For $\lambda\ne0$, the finite binomial identity gives on that space

$$
S^j=\sum_{h=0}^{d_\lambda-1}
\binom jh\lambda^{j-h}R^h
$$

for all sufficiently large $j$. Applying $e$ and the component of
$v_0$ gives a polynomial in $j$ times $\lambda^j$, because each
$\binom jh$ is a polynomial of degree $h$. The zero-eigenvalue
space contributes zero once $j$ exceeds its nilpotency index.
Consequently, after a finite initial segment,

$$
b_j=\sum_{\lambda\in\Lambda}p_\lambda(j)\lambda^j,
\tag{5.2}
$$

where $\Lambda$ is a finite set of distinct nonzero eigenvalues and
zero polynomials have been omitted. If no terms survive, boundedness is
immediate. It remains to control the possible cancellations in (5.2).

For distinct unit complex numbers $z_1,\ldots,z_a$ and constants
$c_1,\ldots,c_a$, the finite geometric-sum formula proves

$$
\lim_{L\to\infty}\frac1L\sum_{j=0}^{L-1}
\left|\sum_{i=1}^a c_i z_i^j\right|^2
=\sum_{i=1}^a|c_i|^2.
\tag{5.3}
$$

Indeed the diagonal terms are constant, while a cross term has the
factor

$$
\frac1L\sum_{j=0}^{L-1}(z_i\overline{z_h})^j
=\frac{1-(z_i\overline{z_h})^L}
       {L(1-z_i\overline{z_h})}\longrightarrow0
\quad(i\ne h).
$$

Thus a nonzero finite sum of distinct unit exponentials cannot tend to
zero. If it did, its squared moduli would tend to zero, and so would
their Cesaro means: split each mean into a fixed finite initial segment
and a tail bounded by any prescribed positive tolerance. That would
contradict (5.3).

Suppose a surviving eigenvalue in (5.2) has modulus greater than one.
Let $R_0$ be the greatest modulus and let $d$ be the largest polynomial
degree among terms with that modulus. Divide (5.2) by $R_0^j j^d$.
The left side tends to zero by the given square-root bound. Terms of
smaller modulus tend to zero, regardless of their polynomial degree;
terms of modulus $R_0$ and smaller degree do also. For the former
assertion, a polynomial times $\rho^j$ with $0<\rho<1$ tends to zero:
the ratio of successive absolute monomial bounds tends to $\rho<1$,
so a geometric majorant applies beyond a finite index. The remaining
leading terms form a nonzero sum

$$
\sum_{\substack{|\lambda|=R_0\\\deg p_\lambda=d}}
 c_\lambda(\lambda/R_0)^j
$$

of distinct unit exponentials, which would tend to zero. This contradicts
(5.3). No surviving eigenvalue has modulus greater than one.

If any surviving unit-modulus term has polynomial degree at least one,
let $d\ge1$ be the largest such degree and divide (5.2) by $j^d$.
The hypothesis gives $|b_j|/j^d\le C\sqrt{j+1}/j^d\to0$.
Smaller-degree unit terms vanish after division, and all strictly
smaller-modulus terms vanish as well. The leading unit terms again
contradict (5.3). Therefore all surviving unit-modulus terms have
constant polynomials. They are bounded, and every smaller-modulus term
is bounded and decays. Adding the finite initial segment proves that
$(b_j)$ is bounded. $\square$

Finite rank here is uniform over all finite row and column choices.
The lemma does not require convergence of any family of matrices,
continuity of an encoder, or a bound on a latent vector norm.

## 6. Nonattainment below the transition

**Theorem 6.1 (No finite equality model when $Z<2/3$).** If
$Z<4H$, no finite model of Definition 2.1 has error at most $e_0$.
Since $4H=2(1-Z)$, this is exactly $Z<2/3$.

**Proof.** Assume there is such a model, and use the fixed homogeneous
size $N=n+1$ and the scalar $g$ from (4.3). For each integer $l\ge1$
put

$$
h_l=\frac H{l+1},\qquad
u_j^{(l)}=\frac{g(H-jh_l)}{\sqrt{h_l}}
\quad(1\le j\le l).
$$

All the heights $H-jh_l$ are strictly interior; the last is $h_l>0$.
Substituting $x=jh_l$ in (4.3) gives

$$
\left|u_j^{(l)}-2\sqrt{j(H-jh_l)}\right|\le\sqrt{Zj},
\qquad |u_j^{(l)}|\le C\sqrt j,
\quad C=2\sqrt H+\sqrt Z.
\tag{6.1}
$$

Each starting ray $(H-h_l,0,0)$ is produced from the fixed preparation
by a single lawful phase-free probability leg. Repeating the one
command $P_{-h_l}$ at most $l-1$ times gives exactly the finite list
of heights above. Write

$$
M_l=T_{-h_l},\qquad v_l=F(H-h_l,0,0).
$$

The exact update identity along that lawful list yields

$$
u_j^{(l)}=\ell M_l^{j-1}v_l/\sqrt{h_l}\qquad(1\le j\le l).
\tag{6.2}
$$

For nonnegative integers $p,q$ with $p+q+1\le l$, the corresponding
Hankel entry factors as

$$
u_{p+q+1}^{(l)}=(\ell M_l^p)(M_l^qv_l/\sqrt{h_l}).
\tag{6.3}
$$

Hence every finite submatrix for which all these entries exist has
rank at most the same number $N$. Both update and readout offsets are
already included in (6.2) by homogenization.

For each fixed positive integer $j$, the scalars $u_j^{(l)}$ for
$l\ge j$ lie in the compact real interval $[-C\sqrt j,C\sqrt j]$.
Choose an infinite subsequence on which the first coordinate converges,
then an infinite subsequence of it on which the second converges, and
continue. Removing finitely many indices at each stage ensures the
coordinate is defined. Choose a strictly increasing diagonal sequence of
indices, with its $j$th index in the $j$th nested subsequence and at
least $j$. Along that diagonal every fixed coordinate converges. Denote
the limits by $u_j$.

Because $h_l\to0$, (6.1) passes at each fixed $j$ to

$$
(2\sqrt H-\sqrt Z)\sqrt j\le u_j
\le(2\sqrt H+\sqrt Z)\sqrt j.
\tag{6.4}
$$

No value or continuity of $g$ at $H$ is invoked: only these bounded
scalar sequences have been passed to a limit.

Now fix any finite row and column sets in the infinite array
$(u_{p+q+1})_{p,q\ge0}$. For all sufficiently large diagonal indices,
every required entry of (6.3) exists. All its $(N+1)$ by $(N+1)$
minors vanish. A determinant is a finite sum of products of entries,
so scalar convergence preserves those zero minors. Thus the limiting
finite matrix has rank at most $N$. This holds for every finite choice
of indices.

Apply Lemma 5.1 to $b_j=u_{j+1}$. Its square-root bound follows from
(6.4), and all its finite Hankel ranks are at most $N$. The lemma says
that $(u_j)$ is bounded. But $Z<4H$ makes
$2\sqrt H-\sqrt Z>0$, so the lower bound in (6.4) is unbounded.
This contradiction proves the theorem.

Each list used in (6.2) is a separately finite lawful history. The
infinite sequence $(u_j)$ is a proof object obtained from scalar
limits of different finite histories. There is no infinite executed
history, no endpoint encoding, no limiting latent vector, and no common
limit or bound assumed for the matrices $M_l$. $\square$

## 7. A single finite model for every strict tolerance

### 7.1 Interior samples and a uniform polynomial bound

Fix $\epsilon>e_0$, and choose $\Delta_\epsilon,m$ as in
Theorem 2.2. For $0\le j\le m$ let

$$
\kappa_j=\frac{H(j+1)}{m+2},\qquad
w_j(t)=\binom mj t^j(1-t)^{m-j},\qquad t=k/H,
$$

$$
P_m(k)=\sum_{j=0}^m A(\kappa_j)w_j(k/H).
\tag{7.1}
$$

Every sample $\kappa_j$ is strictly between $0$ and $H$. These are
samples of the explicit radius function, not encodings of endpoints.
The expression is a single polynomial of degree at most $m$ on the
whole real line; its approximation assertion concerns every $0<k<H$.

**Lemma 7.1 (Uniform estimate from interior Bernstein samples).** For
all $0<k<H$ and all integers $m\ge1$,

$$
|P_m(k)-A(k)|\le\sqrt2\,H m^{-1/4}.
\tag{7.2}
$$

**Proof.** For nonnegative $a,b$, assume for example $a\ge b$.
Then

$$
(\sqrt a-\sqrt b)^2
\le(\sqrt a-\sqrt b)(\sqrt a+\sqrt b)=a-b.
$$

Interchanging them gives $|\sqrt a-\sqrt b|\le\sqrt{|a-b|}$.
For $k,l\in(0,H)$,

$$
|k(H-k)-l(H-l)|=|k-l|\,|H-k-l|\le H|k-l|.
$$

It follows that

$$
|A(k)-A(l)|\le2\sqrt H\,|k-l|^{1/2}.
\tag{7.3}
$$

The weights in (7.1) are nonnegative and sum to one by the binomial
theorem. The finite coefficient identities

$$
j\binom mj=m\binom{m-1}{j-1},\qquad
j(j-1)\binom mj=m(m-1)\binom{m-2}{j-2}
$$

give

$$
\sum_j j w_j=mt,\qquad
\sum_j j(j-1)w_j=m(m-1)t^2.
$$

The first coefficient identity is used for $j\ge1$ and the second
for $j\ge2$; the omitted lower-index contributions are zero. The
second identity is needed only for $m\ge2$.
For $m=1$ the factorial moment on each side is directly zero. Thus in
all cases $m\ge1$,

$$
\sum_j(j-mt)w_j=0,\qquad
\sum_j(j-mt)^2w_j=mt(1-t).
$$

Since

$$
\kappa_j-k=\frac H{m+2}\bigl((j-mt)+(1-2t)\bigr),
$$

the cross term vanishes on summing, and

$$
\begin{aligned}
\sum_jw_j(\kappa_j-k)^2
&=\frac{H^2}{(m+2)^2}\bigl(mt(1-t)+(1-2t)^2\bigr)\\
&\le\frac{H^2(m+4)}{4(m+2)^2}
\le\frac{H^2}{4m}.
\end{aligned}
\tag{7.4}
$$

Here $t(1-t)\le1/4$, $|1-2t|\le1$, and the last comparison is
$m(m+4)\le(m+2)^2$. No limiting distribution or numerical estimate
is involved.

For the finite probability weights, two Cauchy–Schwarz applications give

$$
\begin{aligned}
\sum_jw_j|\kappa_j-k|^{1/2}
&\le\left(\sum_jw_j|\kappa_j-k|\right)^{1/2}\\
&\le\left(\sum_jw_j(\kappa_j-k)^2\right)^{1/4}.
\end{aligned}
$$

Apply (7.3) term by term in (7.1), then use (7.4). The result is

$$
|P_m(k)-A(k)|
\le2\sqrt H\left(\frac{H^2}{4m}\right)^{1/4}
=\sqrt2\,H m^{-1/4},
$$

as required. This proof includes $m=1$ and is uniform arbitrarily close
to either end of the open interval. $\square$

For an exact fixed-coefficient decoder, write

$$
P_m(k)=\sum_{l=0}^m\pi_l k^l,
$$

where finite expansion of $(1-k/H)^{m-j}$ gives explicitly

$$
\pi_l=H^{-l}\sum_{j=0}^l
A(\kappa_j)\binom mj\binom{m-j}{l-j}(-1)^{l-j}
\quad(0\le l\le m).
\tag{7.5}
$$

Indeed the term indexed by $j$ contributes to $k^l$ only when
$l-j$ factors of the expanded power supply $-k/H$. All coefficients
are exact real constants determined by the fixed source and tolerance.
No encoder value occurs in their definition.

### 7.2 Encoding, actual image and the original error

Store

$$
E_m(k,\alpha,\beta)=(K,f_0,\ldots,f_m),\qquad
K=k,\qquad f_j=k^jU(\alpha)\in\mathbb R^2.
\tag{7.6}
$$

There are $1+2(m+1)=2m+3$ real coordinates. On the entire ambient
feature space use the one fixed linear decoder

$$
L_m(K,f_0,\ldots,f_m)=D\left(\sum_{j=0}^m\pi_jf_j,0\right).
\tag{7.7}
$$

Its offset is zero, which is allowed by the affine contract. Its column
on the stored height is zero: it reads stored polynomial features
linearly, rather than evaluating a polynomial nonlinearly on $K$ at
readout time.

**Proposition 7.2 (Image and accuracy).** The actual image of (7.6) is

$$
\mathscr S_m=\left\{(K,f_0,\ldots,f_m):
0<K<H,\quad\|f_0\|_2=1,\quad
f_j=K^jf_0\ (1\le j\le m)\right\}.
\tag{7.8}
$$

Its fibers are exactly the $\beta$ circles at fixed $k,\alpha$. Its
uniform original-output error is at most $\epsilon$.

**Proof.** Every encoded ray satisfies (7.8). Conversely a unit vector
$f_0$ equals $U(\alpha)$ for one circle class. Together with $k=K$,
the remaining equations identify the point as (7.6), and Proposition
1.2 realizes it with every value of $\beta$. Equality of $K$ and
$f_0$ proves the fiber assertion.

On an encoded state the decoder gives $D(P_m(k)U(\alpha),0)$.
The original Gram identity gives the exact squared error

$$
\|L_mE_m(k,\alpha,\beta)-y(k,\alpha,\beta)\|_2^2
=4(P_m(k)-A(k))^2+4Zk.
$$

By (7.2) and the choice of $m$,

$$
4(P_m(k)-A(k))^2+4Zk
\le\frac{8H^2}{\sqrt m}+4ZH
\le\Delta_\epsilon+4ZH=\epsilon^2.
\tag{7.9}
$$

The inequalities hold on the whole open source and for both entire
phase circles. They include the case where the specified $m$ is one.
This is one finite full-domain model for the given tolerance, not a
collection of separate models on an increasing sequence of bands.
$\square$

The $02$ pair of (7.7) is zero, whereas every actual native ray has
positive $02$ radius $B(k)$. Its decoded vector is therefore outside
the native output image. This is expressly permitted by Definition 2.1.
The exact encoded state remains in (7.8). Approximation of the output
does not alter the probability law or support of that state.

### 7.3 Exact updates, saturated guards and persistence

For every real $s,t$ define ambient affine maps

$$
\mathcal U_s:\quad
K'=K+s,\qquad
f_j'=\sum_{h=0}^j\binom jh s^{j-h}f_h
\quad(0\le j\le m),
\tag{7.10}
$$

$$
\mathcal V_t:\quad
K'=K,\qquad f_j'=R_{t/2}f_j
\quad(0\le j\le m).
\tag{7.11}
$$

At $s=0$ the expressions have their polynomial values, including
$s^0=1$. The only affine offset in (7.10) is $s$ in the stored height.
The phase map is linear.

**Proposition 7.3 (Exact operations and all finite prefixes).** The
maps (7.10)–(7.11) intertwine $P_s,Q_t$ exactly on their full lawful
source domains. On $\mathscr S_m$ their guards are exactly

$$
0<K+s<H\quad\hbox{for }\mathcal U_s,
\qquad \mathscr S_m\quad\hbox{for }\mathcal V_t.
$$

From exact initialization, every finite lawful command history stays
exactly encoded at every prefix and every intermediate point of each
leg. The same error bound (7.9) holds there, independently of the
history's length.

**Proof.** Substituting (7.6) in (7.10) gives, by the finite binomial
theorem,

$$
f_j'=(k+s)^jU(\alpha),
$$

while (7.11) gives $f_j'=k^jU(\alpha+t/2)$. These are exactly
$E_m(P_sx)$ and $E_m(Q_tx)$. Translation preserves polynomial degree,
so there is no truncation error. The change in $\beta$ under $Q_t$
is still present in the actual state and is omitted only by this
particular permitted encoder.

For a point of (7.8), the stored height is its actual height. The
straight probability segment is lawful throughout precisely when its
endpoint satisfies $0<K+s<H$, and every fixed-height phase command
is lawful. Thus the guards are exact. All rays in any encoder fiber
agree on these guards, since they have the same height; this is the
meaning of saturated guards here. The substitution identities also prove
preservation of (7.8) on the guards. Both signs and every real command
are covered; $|s|\ge H$ has empty probability domain. Off-image
vectors are not asserted to encode native states.

Let $x_0$ be any actual current ray and initialize $z_0=E_m(x_0)$.
If $z_i=E_m(x_i)$ and the next command is lawful, the just-proved
identity gives $z_{i+1}=E_m(x_{i+1})$. Induction proves the claim
for every finite list. On a probability leg use $P_{\tau s}$ and on
a phase leg use $Q_{\tau t}$, with $0\le\tau\le1$, from the
exact preceding encoding. These give the exact intermediate encodings.
The pointwise bound (7.9) can then be applied at each current state.
An approximate output is never fed back as the latent state, so no
readout error is accumulated. The proof also covers a sequence of
state-selected commands once their actual successive guards hold.
$\square$

The quotient does not make the native controls commute. For example,
the chronological rectangle $P_s,Q_t,P_{-s},Q_{-t}$ changes the true
$\beta$ coordinate by $-st/r$ whenever its probability legs are
lawful, while fixing $k,\alpha$. This follows by subtracting the two
phase rates $c(k+s)t-c(k)t$. The resulting ray changes precisely when
$st/r$ is not an integer multiple of $2\pi$, by the ray identification
in §1.
The displayed encoding forgets that circle, so its rectangle action is
the identity. Equal encoded actions do not identify the original real
commands or enlarge their source domains.

## 8. Equality at and above the transition

**Proposition 8.1 (Height and zero readout).** If $Z\ge4H$, the model

$$
E_0(k,\alpha,\beta)=k\in\mathbb R,\qquad
\mathcal U_s(K)=K+s,\qquad
\mathcal V_t(K)=K,\qquad L_0(K)=0\in\mathbb R^{10}
\tag{8.1}
$$

has error supremum exactly $e_0$. Every individual lawful state has
strictly smaller error. The assertion includes $Z=4H$, equivalently
$Z=2/3$.

**Proof.** The image is precisely $(0,H)$. The probability guard is
$0<K+s<H$ and the phase guard is the entire image. These are saturated
on the encoder fibers, which here contain both phase circles at each
height. The formulas intertwine the native commands exactly and
preserve the image whenever lawful. The finite-prefix and intermediate-leg
induction of Proposition 7.3 applies directly to the height coordinate.

The squared error of the zero decoder, in the original metric, is

$$
\begin{aligned}
\|y(k,\alpha,\beta)\|_2^2
&=16k(H-k)+4Zk\\
&=4ZH+4(H-k)(4k-Z).
\end{aligned}
\tag{8.2}
$$

If $Z\ge4H$, then $4k-Z<0$ at every interior height, while $H-k>0$.
Thus (8.2) is strictly smaller than $4ZH$ at each such state. Its
supremum is nevertheless $4ZH$, since its scalar polynomial value
tends to $4ZH$ as interior $k$ approaches $H$. At the transition
$Z=4H$, the difference from $4ZH$ is exactly

$$
-16(H-k)^2,
$$

so the same strict pointwise inequality and the same supremum apply.
No encoder value at the missing endpoint has been used. Attainment
means that this one finite model has error supremum $e_0$, not that a
lawful state must realize its supremum. $\square$

When $Z<4H$, interior heights with $k>Z/4$ make the last term of
(8.2) positive, so this particular zero decoder exceeds the floor.
Theorem 6.1 supplies the stronger conclusion that every finite candidate
fails to attain it. When $Z\ge4H$, (8.1) is a sufficient
one-coordinate witness, not a minimality result. Noninjectivity and
nonphysical decoded vectors are used openly as permissions of the
contract.

Combining Proposition 4.1, Theorem 6.1, Proposition 7.2 and Proposition
8.1 proves the achievable-tolerance assertion of Theorem 2.2. The
set is upward closed because a model of error at most $\epsilon$
also satisfies any larger tolerance. The existence of a model for
every $\epsilon>e_0$, together with the universal lower bound, proves
the stated infimum in both regimes.

## 9. Simultaneous native paths, guards and exact-real resources

### 9.1 The actual mixed integral

Prescribe native velocities $a_c=\dot k$ and $b_c=\dot\chi$ on a
finite interval $[0,T]$, in the regularity class of §1. Define their
relative parameters

$$
\rho(\tau)=\int_0^\tau a_c(v)\,dv,\qquad
\Delta_k=\rho(T),\qquad
L=\int_0^T b_c(\tau)\,d\tau,\qquad
C=\int_0^T\rho(\tau)b_c(\tau)\,d\tau.
$$

The function $\rho$ is continuous and bounded on the compact interval,
and $b_c$ has finite absolute integral, so $C$ exists. The exact source
guard is

$$
0<k+\rho(\tau)<H\quad\hbox{for every }\tau\in[0,T].
\tag{9.1}
$$

Equivalently, with the extrema on this same compact interval,

$$
k+\min\rho>0,\qquad k+\max\rho<H.
\tag{9.2}
$$

The strict inequalities follow because the extrema are attained. Lawful
endpoints alone do not ensure (9.1) for a general path.

Integrating the actual equations of Lemma 1.1 on this guard gives

$$
k'=k+\Delta_k,\qquad
\alpha'=\alpha+L/2,\qquad
\beta'=\beta+\left(\frac12-\frac kr\right)L-\frac Cr.
\tag{9.3}
$$

In particular,

$$
\int_0^T\left(\frac12-\frac{k+\rho(\tau)}r\right)b_c(\tau)\,d\tau
=\left(\frac12-\frac kr\right)L-\frac Cr.
$$

This proves both the mixed term and its negative sign. The formula
respects the phase circles and uses no stored past lift. If two paths
with relative triples $(\Delta_1,L_1,C_1)$ and
$(\Delta_2,L_2,C_2)$ are concatenated, their relative displacement in
the second piece is $\Delta_1+\rho_2$. Thus the combined triple is

$$
(\Delta_1+\Delta_2,\ L_1+L_2,\ C_1+C_2+\Delta_1L_2).
\tag{9.4}
$$

Substitution in (9.3) agrees with successive application. The combined
guard consists of the first all-times guard and the second one from
the actual intervening height. This verifies the source composition
without replacing simultaneous control by an asserted finite splitting.

### 9.2 Affine realization by the same models

**Proposition 9.1 (No change of threshold for prescribed paths).**
Both constructions above admit an exact fixed affine map for each
prescribed path on (9.1). Their error estimates persist at all
intermediate times and at all prefixes of every finite lawful
concatenation of such paths. Consequently the full classification
in Theorem 2.2 is unchanged by requiring all these paths as well as
$P_s,Q_t$.

**Proof.** For the polynomial model use

$$
K'=K+\Delta_k,\qquad
f_j'=R_{L/2}\sum_{h=0}^j\binom jh\Delta_k^{j-h}f_h
\quad(0\le j\le m).
\tag{9.5}
$$

All its coefficients depend on the prescribed relative path and fixed
model, not on the initial ray. Substitution of (7.6) and the finite
binomial theorem gives
$f_j'=(k+\Delta_k)^jU(\alpha+L/2)$, exactly the encoding of (9.3).
The true mixed term $C$ is retained in (9.3); it disappears from (9.5)
only because this encoder forgets $\beta$. For the height-only model
the affine map is simply $K'=K+\Delta_k$.

For either actual image, impose

$$
0<K+\rho(\tau)<H\quad(0\le\tau\le T).
$$

It is precisely (9.1), computed from a stored coordinate, and is
constant on every encoder fiber. On that guard the endpoint identities
prove preservation of the actual image. Replacing the upper integration
limit $T$ by any intermediate time supplies its relative displacement,
phase integral and mixed integral. The same calculation proves exact
encoding at that time. Applying the uniform current-state readout bound
then proves its error assertion. Induction over any finite concatenation
proves all finite prefixes, and (9.4) confirms consistency with the
actual native composition.

The larger contract contains the $P_s,Q_t$ requirements used in the
lower and nonattainment proofs, so those conclusions still apply.
The same upper witnesses now satisfy the larger contract as well.
Both inclusions are therefore proved; the classification is identical.
$\square$

### 9.3 Quantifiers and resource bounds

The polynomial model uses exactly $2m+3$ stored real coordinates with
the explicit sufficient $m$ in Theorem 2.2. Its degree is at most $m$,
and (7.5) specifies all decoder coefficients by finite sums of interior
radius samples. On the actual image it also satisfies the finite bound

$$
\|E_m(k,\alpha,\beta)\|_2^2
=k^2+\sum_{j=0}^m k^{2j}
\le H^2+\sum_{j=0}^m H^{2j}.
$$

Boundedness here is a property of this construction and was not an
assumption about competing encoders. At equality in the attaining
range, (8.1) uses one stored real coordinate with $0<K<H$.
No coordinate count in this volume is an optimal-dimension assertion.

All model maps are prescribed for every real signed command. Every
asserted execution has finite duration and finite phase variation, and
each finite concatenation uses its own actual guards. There is no
uniform upper bound on the number of commands, their total variation,
or their finite real magnitudes. No positive margin from the support
boundary is imposed uniformly on the source. Each individual lawful
continuous path on a compact time interval does have a positive
height margin, as follows from (9.2); that pathwise fact does not
restrict the full-domain supremum.

Exact initialization and exact real operations are essential to the
stated persistence argument. It propagates an exact encoded point,
then evaluates its approximate readout. It supplies no error bound
for perturbed initialization, rounding, noise, or approximation of a
control integral. There is no finite-bit, runtime, conditioning,
measurement, training, or implementation guarantee implicit in these
coordinate and degree bounds.

## 10. Source credit, mathematical contribution and boundaries

The source credited here is *Native FIB continuation: exact affine
obstruction and compact-band approximation*, specifically its §§1–3
for the native probability law, negative-phase convention, preparation,
reachability, original output factorization and prescribed-path formulas,
and its §7.5, Proposition 7.13, for the full-open necessary floor.
That source situates its native conventions in *AURIC FIB-ATOM:
Probability, Phase Transport and Holonomy*. The latter attribution is
source context; no unquoted result of that parent is needed in the
proofs here. Section 1 and §9 reconstruct the actual source bridges
used by this volume.

Sections 3–9 supply the proofs of the full-open classification,
including the finite-dimensional, scalar-limit and exact native
interfaces; the source attributions in this section supply no additional
theorem hypothesis.

The general mathematical ingredients are classical: finite-dimensional
translation representations and abstract characters; finite Hankel
rank, shift realizations and linear recurrences; generalized
eigenspaces and exponential-polynomial sequences; finite geometric
sums and Cesaro cancellation; Bernstein polynomial weights and moment
identities; finite Cauchy–Schwarz estimates; and polynomial closure
under translation. The forms needed here are proved explicitly.
Finite-dimensional translation-space theory is related classical
context, as in Engert's work on finite-dimensional translation-invariant
spaces, cited in the native continuation source at
[doi:10.2140/pjm.1970.32.333](https://doi.org/10.2140/pjm.1970.32.333).
No external translation-space theorem, regularity hypothesis, or
classification from that reference is a premise here.

The source-specific synthesis is the classification for one full open
native domain under the original ten-output Euclidean metric and full
real control menu. It combines the bounded-observable loss of $\beta$
with the equality residual, extracts a uniformly finite-rank scalar
limit from separately finite lawful histories, and matches the resulting
nonattainment boundary with full-domain polynomial and height-only
models. It includes the arbitrary-preparation rotations, both affine
offsets, exact guards and simultaneous-path mixed integral. This is a
statement of mathematical content relative to the specified source,
with no worldwide-priority claim.

The following boundaries are part of the result's scope:

- The parameters satisfy $0<Z<1$ and the current heights satisfy
  $0<k<H$. At $k=0$ or $k=H$ a group loses support and its phase
  no longer parametrizes the same ray space. At $Z=0$ the positive
  middle reference is absent, while at $Z=1$ the open height interval
  is empty. None of these support changes is included by taking a
  limit in this theorem.
- The encoders are functions of current rays. Retained real lifts or
  arbitrary producing-history encoders are different domains. In
  particular the bounded-observable argument uses equality of
  current-ray function spaces and is not a nonattainment theorem
  for unrestricted history encoders.
- Only bounded affine observables were proved $\beta$-independent.
  Unbounded encoder coordinates and general finite affine factor
  fibers have not been classified. The explicit models' fibers do
  not establish the fibers of all models.
- Requiring injectivity, physical decoded outputs, a reduced command
  menu, a different metric, or a finite-horizon source changes the
  contract. The present witnesses and lower proof do not supply a
  classification for those modified problems. All original commands
  remain present here, and no endpoint or external height label is
  added.
- The displayed dimensions are sufficient. No minimum dimension or
  quantitative positive gap at a fixed dimension is proved. In
  particular nonattainment at $e_0$ does not by itself supply a
  fixed-dimension lower bound strictly above $e_0$.
- The separate original question of an attainer at some finite hidden
  $N$ versus a strict gap for every finite $N$ remains unresolved.
  No identification of its objective and admissible realizations
  with Definition 2.1 has been established. The transition proved
  here does not settle that alternative or the broader research goal.
- Ideal exact-real source access and persistence supply no actual
  machine-learning, acquisition, training, physical implementation,
  robustness or task-transfer benefit without additional bridges.

## 10.99 追加锚

# 11. Fixed-dimension uniform gaps and finite Hankel certificates

The preceding volume fixes the full-open native contract. This section keeps
that contract unchanged and makes the dimension quantifier explicit. In
particular, every encoder, update matrix, decoder row, affine offset, and
preparation may vary from one model to another.

## 11.1 Capacity at a dimension bound

Fix $0<Z<1$, put $r=1-Z$ and $H=r/2$, and write
$$
e_*=\sqrt{4ZH}=\sqrt{2Z(1-Z)}.
$$
For an integer $n\ge 0$, let $\mathfrak F_{\le n}(Z)$ be the class of all
models of Definition 2.1 whose encoder dimension is some
$d\in\{0,\ldots,n\}$. The preparation is arbitrary but fixed when a model
is considered: $0<k_0<H$ and all preparation phases are allowed. The
notation below suppresses this preparation because changing it only rotates
the five output pairs by a fixed orthogonal map, while the command formulas
in $(k,\alpha,\beta)$ are unchanged. The initial height changes a producing
history, not the reachable current-ray domain.

For $A\in\mathfrak F_{\le n}(Z)$ define
$$
\operatorname{err}(A)
 =\sup_{x\in\mathcal M}\|q_A(x)-y(x)\|_2\in[0,+\infty],
\qquad
e_n^{\mathrm{aff}}(Z)
 =\inf_{A\in\mathfrak F_{\le n}(Z)}\operatorname{err}(A),
$$
with the convention $\inf\varnothing=+\infty$. Define the finite-tolerance
set
$$
\mathcal A_{\le n,Z}
 =\{\varepsilon\in[0,\infty):
       \exists A\in\mathfrak F_{\le n}(Z),\
       \operatorname{err}(A)\le\varepsilon\}.
$$
The norm is the original Euclidean norm on all ten outputs. The class is
nonempty and contains a finite-error model for every $n$: use the unique
zero-dimensional encoder, its unique affine updates, and the constant zero
decoder. Thus $e_n^{\mathrm{aff}}(Z)<\infty$. Models with infinite error
cannot witness a finite tolerance.

The set $\mathcal A_{\le n,Z}$ is upward closed and has infimum
$e_n^{\mathrm{aff}}(Z)$. For every $\varepsilon>e_n^{\mathrm{aff}}(Z)$,
the definition of an infimum supplies a model of error at most
$\varepsilon$ (indeed, of error strictly below it). Its lower endpoint is
in $\mathcal A_{\le n,Z}$ exactly when some model attains the infimum. These
statements concern a fixed dimension bound and do not identify the endpoint
for positive $n$ below the transition.

**Theorem 11.1 (Uniform fixed-dimension gap).** For every $0<Z<2/3$ and
every integer $n\ge0$, there is a number
$\Gamma(n,Z)>0$ such that, for every allowed preparation and every
$A\in\mathfrak F_{\le n}(Z)$,
$$
\operatorname{err}(A)^2\ge 4ZH+\Gamma(n,Z).
\tag{11.1}
$$
Consequently
$$
e_n^{\mathrm{aff}}(Z)\ge
\sqrt{4ZH+\Gamma(n,Z)}>e_*.
\tag{11.2}
$$
The number $\Gamma(n,Z)$ is defined exactly in §11.4 below. It depends on
$n$ and $Z$ only, not on any model parameter or preparation.

**Proof.** A model with infinite error satisfies (11.1) trivially, so take a
finite-error model whenever a residual is used. The preceding
bounded-observable theorem and Proposition 4.1 apply to Definition 2.1 with
both affine offsets present. They give a single scalar affine observable
$g(k)$ and, with
$$
\Delta=\operatorname{err}(A)^2-4ZH\ge0,
$$
the residual
$$
\left|g(H-x)-2\sqrt{(H-x)x}\right|
 \le\sqrt{Zx+\Delta/4}
\qquad(0<x<H).
\tag{11.3}
$$
The coefficient $\Delta/4$ is the coefficient from the fourfold first-pair
metric in Proposition 4.1.

Suppose, for contradiction, that $e_n^{\mathrm{aff}}(Z)=e_*$. Put
$N=n+1$. For each integer $\ell\ge1$ set
$$
h_\ell=\frac{H}{\ell+1}.
$$
Since $\sqrt{4ZH+h_\ell^2}>e_*$, the infimum definition supplies a model
$A_\ell\in\mathfrak F_{\le n}(Z)$ with finite error
$\varepsilon_\ell<\sqrt{4ZH+h_\ell^2}$. For its residual $\Delta_\ell$,
$$
0\le\Delta_\ell\le h_\ell^2.
\tag{11.4}
$$
All parameters of $A_\ell$ may depend on $\ell$.

Let $g_\ell$ be the scalar from (11.3), and define, for $1\le j\le\ell$,
$$
u_j^{(\ell)}
 =\frac{g_\ell(H-jh_\ell)}{\sqrt{h_\ell}}.
$$
The fixed preparation reaches $(H-h_\ell,0,0)$ by one phase-free
probability leg. Repeating $P_{-h_\ell}$ at most $\ell-1$ times reaches all
heights $H-jh_\ell$. The minimum is $h_\ell>0$, so every leg and every
intermediate point is lawful. Applying (11.3) with $x=jh_\ell$ and using
(11.4) gives
$$
\left|u_j^{(\ell)}
      -2\sqrt{j(H-jh_\ell)}\right|
 \le \sqrt{Zj+\frac{\Delta_\ell}{4h_\ell}}
 \le \sqrt{Zj+\frac{h_\ell}{4}}.
\tag{11.5}
$$
Hence, uniformly in $\ell$ and in the varying model,
$$
|u_j^{(\ell)}|
 \le \left(2\sqrt H+\sqrt{Z+\frac H4}\right)\sqrt j.
\tag{11.6}
$$

For the one-step command in $A_\ell$, let $T_\ell$ be its homogeneous
update matrix and let $v_\ell$ be the homogeneous state at
$(H-h_\ell,0,0)$. If $\lambda_\ell$ is the fixed homogeneous decoder row
for $g_\ell$, exact intertwining gives
$$
u_j^{(\ell)}
 =\lambda_\ell T_\ell^{\,j-1}v_\ell/\sqrt{h_\ell}.
\tag{11.7}
$$
Therefore
$$
u_{p+q+1}^{(\ell)}
 =(\lambda_\ell T_\ell^{\,p})
   (T_\ell^{\,q}v_\ell/\sqrt{h_\ell})
\tag{11.8}
$$
whenever $p+q+1\le\ell$. This factors every finite Hankel submatrix through
$d_\ell+1\le N$ coordinates. It uses only the separately finite lawful
chain; no common matrix, latent bound, ambient inverse, or infinite
execution is assumed.

For each fixed $j$, (11.6) places all defined scalars in a common compact
interval. Successive scalar subsequences and a diagonal choice with
indices eventually at least $j$ produce limits $u_j$ for every $j\ge1$.
Since $h_\ell\to0$ and
$0\le\Delta_\ell/h_\ell\le h_\ell\to0$, (11.5) yields
$$
(2\sqrt H-\sqrt Z)\sqrt j
 \le u_j\le
(2\sqrt H+\sqrt Z)\sqrt j.
\tag{11.9}
$$
The lower coefficient is strictly positive because $Z<4H$.

Fix any finite row and column sets in the array
$(u_{p+q+1})_{p,q\ge0}$. For all sufficiently large diagonal indices the
corresponding entries occur in (11.8), so every $(N+1)$-minor is zero.
Determinants are finite polynomials in their scalar entries; taking the
coordinatewise limit preserves those zero minors. Thus every finite Hankel
submatrix of the limit has rank at most $N$.

Apply Lemma 5.1 of the preceding volume to $b_j=u_{j+1}$. Its finite-rank
hypothesis is exactly the conclusion of the preceding paragraph, and its
square-root upper bound is (11.9). The lemma makes $(u_j)$ bounded, while
the positive lower coefficient in (11.9) makes it unbounded. This
contradiction proves $e_n^{\mathrm{aff}}(Z)>e_*$. The finite certificate in
§11.4 turns this strict conclusion into the model-uniform number in
(11.1). $\square$

The quantifiers in Theorem 11.1 are stronger than the assertion that each
individual finite model has error strictly above $e_*$. They allow the
models, their dimensions, all affine parameters, and their decoders to
vary with $\ell$, while the final rank bound is the common number $n+1$.
They also remain compatible with
$\inf_n e_n^{\mathrm{aff}}(Z)=e_*$.

## 11.2 The finite Hankel relaxation

Fix $N=n+1\ge1$. For an integer $m\ge0$ put $L_m=2m+1$. For
$u=(u_1,\ldots,u_{L_m})\in\mathbb R^{L_m}$ define
$$
H_m(u)=(u_{p+q+1})_{0\le p,q\le m},
\qquad
\mathcal R_{N,m}
 =\{u:\operatorname{rank}H_m(u)\le N\}.
$$
When the matrix is too small for an $(N+1)$-minor, the rank restriction is
vacuous. Otherwise $\mathcal R_{N,m}$ is exactly the common zero set of
all such minors, hence a closed finite-dimensional determinantal set.
Define
$$
J_m(u)=\max_{1\le j\le L_m}
 \frac{|u_j-\sqrt j|}{\sqrt j},
\qquad
d_{N,m}=\min_{u\in\mathcal R_{N,m}}J_m(u).
\tag{11.10}
$$

**Lemma 11.2 (Existence, monotonicity, and limit).** For every fixed
$N\ge1$, the minimum in (11.10) exists, the sequence $d_{N,m}$ is
nondecreasing, and
$$
\lim_{m\to\infty}d_{N,m}=1.
\tag{11.11}
$$

**Proof.** The zero vector belongs to $\mathcal R_{N,m}$ and has
$J_m(0)=1$. The set
$$
K_m=\{u\in\mathcal R_{N,m}:J_m(u)\le1\}
$$
is nonempty and closed, and $J_m(u)\le1$ implies
$0\le u_j\le2\sqrt j$ for every coordinate. Thus $K_m$ is compact and
$J_m$ attains a minimum on it. Outside $K_m$ the objective is larger than
one, so this is also the global minimum on $\mathcal R_{N,m}$ and
$0\le d_{N,m}\le1$; the endpoint value $d_{N,m}=1$ is included.

Truncating a feasible vector for $m+1$ to its first $2m+1$ coordinates
takes the upper-left principal submatrix of $H_{m+1}$ and cannot increase
the maximum in $J_m$. Applying this to a minimizer proves
$d_{N,m}\le d_{N,m+1}$.

Let $D=\lim_m d_{N,m}\le1$. If $D<1$, choose $D<\sigma<1$. A minimizer
$u^{(m)}$ then obeys, on every defined coordinate,
$$
(1-\sigma)\sqrt j\le u_j^{(m)}
 \le(1+\sigma)\sqrt j.
\tag{11.12}
$$
A scalar diagonal subsequence gives an infinite sequence $u_j$ with the
same bounds. Any finite submatrix of $(u_{p+q+1})$ is, for sufficiently
large $m$, a submatrix of $H_m(u^{(m)})$; its $(N+1)$-minors therefore
vanish in the limit. Lemma 5.1 applied to $u_{j+1}$ makes this sequence
bounded, contradicting the positive lower bound in (11.12). Hence
$D=1$. The finite prefixes are a relaxation only: no individual feasible
finite prefix is asserted to extend to a native model or even to an infinite
finite-rank realization. The infinite finite-rank sequence used in the
contradiction is obtained by diagonal compactness. $\square$

## 11.3 An exact implicit excess certificate

Let $A\in\mathfrak F_{\le n}(Z)$ have finite error
$\varepsilon=\operatorname{err}(A)$, and put
$$
\Delta=\varepsilon^2-4ZH\ge0,\qquad
\rho_0=\sqrt{\frac{Z}{4H}}.
$$
Fix $m\ge0$, $L=2m+1$, and $0<h<H/L$, and set
$$
\eta_h=1-\sqrt{1-\frac{Lh}{H}}.
$$
Suppose
$$
d_{N,m}-\eta_h>\rho_0.
\tag{11.13}
$$
Use the scalar $g$ from (11.3), and sample the lawful chain by
$$
v_j=\frac{g(H-jh)}{2\sqrt{Hh}},\qquad 1\le j\le L.
$$
The rank factorization (11.8), with one fixed model instead of the varying
family, gives $v\in\mathcal R_{N,m}$. Dividing (11.3) by
$2\sqrt{Hhj}$ gives
$$
\frac{\left|v_j-\sqrt j\sqrt{1-jh/H}\right|}{\sqrt j}
 \le
 \sqrt{\rho_0^2+\frac{\Delta}{16Hhj}}.
\tag{11.14}
$$
Since $jh\le Lh$, $j\ge1$, and $\Delta\ge0$, the triangle inequality gives
$$
J_m(v)\le
\eta_h+\sqrt{\rho_0^2+\frac{\Delta}{16Hh}}.
\tag{11.15}
$$
By minimality, $d_{N,m}\le J_m(v)$. Under (11.13), both sides that are
squared are nonnegative, and therefore
$$
\Delta\ge
16Hh\left((d_{N,m}-\eta_h)^2-\rho_0^2\right)>0.
\tag{11.16}
$$
This is a lower bound for every native model with dimension at most $n$.
It is a necessary certificate only: no feasible finite Hankel prefix is
claimed to be extendible to an infinite prefix or realizable by a native
model.

## 11.4 Canonical constants and the uniform number

Assume $0<Z<4H$ and retain $N=n+1$. Then $\rho_0\in(0,1)$; define
$$
\eta=\frac{1-\rho_0}{4},
\qquad
\rho=\rho_0+2\eta=\frac{1+\rho_0}{2}.
\tag{11.17}
$$
Thus $0<\eta<1/4$ and $\rho_0<\rho<1$. By Lemma 11.2 there is a finite
index
$$
M=\min\{m\ge0:d_{N,m}\ge\rho\}.
\tag{11.18}
$$
Set
$$
L=2M+1,\qquad
h=\frac{H(2\eta-\eta^2)}{L}.
\tag{11.19}
$$
Because $0<2\eta-\eta^2<1$, one has $0<h<H/L$, and
$$
\eta_h
 =1-\sqrt{1-\frac{Lh}{H}}
 =1-\sqrt{(1-\eta)^2}
 =\eta.
$$
The canonical squared excess is
$$
\Gamma(n,Z)
 =\frac{16H^2}{2M+1}(2\eta-\eta^2)
   \left((\rho_0+\eta)^2-\rho_0^2\right).
\tag{11.20}
$$
It is strictly positive because $H>0$, $2M+1>0$,
$\eta(2-\eta)>0$, and
$$
(\rho_0+\eta)^2-\rho_0^2=\eta(2\rho_0+\eta)>0.
$$
Since $d_{N,M}-\eta\ge\rho-\eta=\rho_0+\eta>\rho_0$, (11.16) yields
$$
\operatorname{err}(A)^2-4ZH\ge\Gamma(n,Z)
$$
for every finite-error model in $\mathfrak F_{\le n}(Z)$. Infinite-error
models satisfy the same inequality trivially. This proves (11.1).

The corresponding additive gap in error, if desired, is
$$
\gamma(n,Z)
 =\sqrt{4ZH+\Gamma(n,Z)}-\sqrt{4ZH}
 =\frac{\Gamma(n,Z)}
 {\sqrt{4ZH+\Gamma(n,Z)}+\sqrt{4ZH}}>0.
\tag{11.21}
$$
The certificate is exact but implicit. Existence of $M$ is proved, while no
effective upper bound on $M$, evaluated value of $d_{N,M}$, practical
algorithm, native-realizability converse, matching capacity rate, or
optimal-dimension theorem is asserted.

## 11.5 Dimension zero, the transition, and guard recovery

For $n=0$ the encoder has no coordinates and every decoder is a constant
$c\in\mathbb R^{10}$. At each fixed height, the state obtained by replacing
$(\alpha,\beta)$ with $(\alpha+\pi,\beta+\pi)$ has output $-y$. Hence
$$
\frac{\|c-y\|_2^2+\|c+y\|_2^2}{2}
 =\|c\|_2^2+\|y\|_2^2.
$$
Taking the supremum proves that $c=0$ is optimal among constants and
$$
e_0^{\mathrm{aff}}(Z)^2
 =\sup_{0<k<H}\left(16k(H-k)+4Zk\right).
\tag{11.22}
$$
Writing
$$
f(k)=-16k^2+(16H+4Z)k
$$
shows that its vertex is $k_*=H/2+Z/8$. If $Z<4H$ this vertex is
interior and
$$
e_0^{\mathrm{aff}}(Z)=\frac{4H+Z}{2}=1-\frac Z2,
\qquad
\left(e_0^{\mathrm{aff}}(Z)\right)^2-e_*^2
 =\frac{(4H-Z)^2}{4}>0.
\tag{11.23}
$$
The zero-dimensional infimum is attained by the zero constant decoder.

If $Z\ge4H$ then for every interior $k$,
$$
f(k)=4ZH+4(H-k)(4k-Z)<4ZH,
$$
and its supremum is $4ZH$ as $k$ tends to $H$ through interior heights.
At $Z=4H$ the difference is exactly $-16(H-k)^2$. Therefore, under
literal Definition 2.1,
$$
e_n^{\mathrm{aff}}(Z)=e_*
\quad\text{and}\quad
\mathcal A_{\le n,Z}=[e_*,\infty)
\qquad(2/3\le Z<1,\ n\ge0),
\tag{11.24}
$$
with the zero-dimensional constant model already attaining the infimum.
The supremum need not be realized by a lawful state.

Consequently
$$
\mathcal A_{\le0,Z}
 =[e_0^{\mathrm{aff}}(Z),\infty)
\quad(0<Z<2/3),
$$
whereas for $Z\ge2/3$ the preceding display gives the endpoint for every
dimension bound. For positive fixed $n$ below the transition, (11.1)
proves a strict gap above $e_*$ but does not decide whether the infimum
$e_n^{\mathrm{aff}}(Z)$ is attained at its own value.

Guard recovery is a separate contract. Suppose the encoded state must
decide, for every command, whether its native straight segment is lawful.
A zero-dimensional encoder cannot do this: for $k_1<k_2$ choose
$s=H-(k_1+k_2)/2$. Then
$$
0<k_1+s<H,\qquad k_2+s>H,
$$
although both states have the same singleton encoding. The
guard-recoverable zero-dimensional class is therefore empty, with
infimum $+\infty$ and no finite tolerance. For $n\ge1$, the height encoder
$E(k,\alpha,\beta)=k$ has exact guards and finite error, so the subclass
is nonempty. The lower gap and the finite certificate remain valid on this
smaller class because it is a subclass of $\mathfrak F_{\le n}(Z)$.
When $Z\ge2/3$, the height model attains $e_*$ in the guard-recoverable
class for every $n\ge1$. These guard statements do not alter the literal
dimension-zero conclusions above.

## 11.6 Polynomial witnesses and the dimension limit

For an integer $b\ge1$, the interior Bernstein construction already proved
in §7 gives nodes and a polynomial
$$
\kappa_j=\frac{H(j+1)}{b+2},\qquad
P_b(k)=\sum_{j=0}^b A(\kappa_j)
 \binom bj(k/H)^j(1-k/H)^{b-j},
$$
where $A(k)=2\sqrt{k(H-k)}$. Its samples are all interior, and the
finite moment identities give
$$
\sum_jw_j(\kappa_j-k)^2
 =\frac{H^2}{(b+2)^2}\bigl(bt(1-t)+(1-2t)^2\bigr)
 \le\frac{H^2}{4b},
\qquad t=k/H.
$$
The square-root estimate for $A$ and two finite Cauchy--Schwarz
inequalities therefore give
$$
|P_b(k)-A(k)|\le\sqrt2\,H b^{-1/4}
\qquad(0<k<H).
\tag{11.25}
$$
Writing $P_b(k)=\sum_{j=0}^b\pi_jk^j$ and storing
$$
K=k,\qquad f_j=k^jU(\alpha)\quad(0\le j\le b)
$$
uses exactly $1+2(b+1)=2b+3$ real coordinates. The fixed linear decoder
$D(\sum_j\pi_jf_j,0)$ and the exact affine updates
$$
K'=K+s,\qquad
f_j'=\sum_{h=0}^j\binom jh s^{j-h}f_h,
\qquad
f_j'=R_{t/2}f_j\quad\text{for a phase command}
$$
satisfy all real signed commands on their full lawful domains, including
both affine offsets allowed by Definition 2.1. The preceding volume proves
that the actual guard is exactly $0<K+s<H$, the phase guard is the whole
image, and all finite prefixes and intermediate points remain encoded.
Using the original output metric,
$$
e_n^{\mathrm{aff}}(Z)^2
 \le4ZH+\frac{8H^2}{\sqrt b}
\quad\text{whenever }2b+3\le n.
\tag{11.26}
$$
In particular, for $n\ge5$ let
$$
b=\left\lfloor\frac{n-3}{2}\right\rfloor\ge1.
$$
Then
$$
e_n^{\mathrm{aff}}(Z)^2
 \le4ZH+
 \frac{8H^2}{\sqrt{\lfloor(n-3)/2\rfloor}}.
\tag{11.27}
$$
Below the transition the zero decoder also supplies
$e_n^{\mathrm{aff}}(Z)\le1-Z/2$ for every $n$ under the literal contract.
In the guard-recoverable class, the same bound is supplied by the height
encoder for every $n\ge1$.

The classes $\mathfrak F_{\le n}(Z)$ are nested, so
$e_{n+1}^{\mathrm{aff}}(Z)\le e_n^{\mathrm{aff}}(Z)$. The universal floor
$e_n^{\mathrm{aff}}(Z)\ge e_*$ together with (11.26), with $b$ tending to
infinity, gives
$$
\lim_{n\to\infty}e_n^{\mathrm{aff}}(Z)
 =\inf_{n\ge0}e_n^{\mathrm{aff}}(Z)
 =e_*.
\tag{11.28}
$$
For $Z<2/3$, (11.1) still leaves a positive gap at every fixed dimension.
Neither (11.26) nor the implicit certificate gives matching rates,
attainment for a general positive fixed dimension, or an optimal dimension
at a prescribed tolerance.

## 11.7 Prescribed paths, all-times guards, and contract matching

Consider the larger contract that additionally requires an affine update for
each prescribed finite native path from §9. Let
$$
\rho_{\rm path}(\tau)=\int_0^\tau a_c(v)\,dv,\qquad
\Delta_k=\rho_{\rm path}(T),\qquad
L_\chi=\int_0^T b_c(\tau)\,d\tau,
$$
and
$$
C_{\rm path}=\int_0^T
 \rho_{\rm path}(\tau)b_c(\tau)\,d\tau.
$$
For a lawful path the exact guard is
$$
0<k+\rho_{\rm path}(\tau)<H
\quad\text{for every }\tau\in[0,T],
\tag{11.29}
$$
equivalently
$$
k+\min_{[0,T]}\rho_{\rm path}>0,\qquad
k+\max_{[0,T]}\rho_{\rm path}<H.
$$
Integrating the native equations gives the endpoint
$$
k'=k+\Delta_k,\qquad
\alpha'=\alpha+\frac{L_\chi}{2},
$$
$$
\beta'=\beta+
 \left(\frac12-\frac kr\right)L_\chi-\frac{C_{\rm path}}r.
\tag{11.30}
$$
The mixed term has this sign because the varying height contributes
$-\rho_{\rm path}b_c/r$ to the phase integral.

A model required to implement all such paths is a subclass of the
straight-command class used in Theorem 11.1 and §11.3. Hence the same
lower gap and certificate apply. Conversely, the polynomial witness has
the exact affine path update
$$
K'=K+\Delta_k,\qquad
f_j'=R_{L_\chi/2}
 \sum_{h=0}^j\binom jh\Delta_k^{\,j-h}f_h,
\tag{11.31}
$$
and the height witness has $K'=K+\Delta_k$. Substitution gives the exact
encoding of the endpoint in (11.30); $C_{\rm path}$ is forgotten only in
the permitted beta-independent encoder. At every intermediate time,
replace $T$ by that time in the displayed integrals. The same identities
therefore prove all prefixes and intermediate points, with the original
uniform readout bound. Concatenating two paths gives
$$
(\Delta_1+\Delta_2,\,
 L_1+L_2,\,
 C_1+C_2+\Delta_1L_2),
\tag{11.32}
$$
which agrees with successive application and introduces no extra stored
history coordinate.

Thus the classification, the dimension upper bound, and the finite
certificate are unchanged when prescribed paths and their full all-times
guards are added. The same comparison applies within the corresponding
guard-recoverable subclasses. It does not identify the capacities of these
different contracts with one another, and it does not replace an all-times
guard by an endpoint check.

## 11.8 Scope, source credit, and remaining boundaries

This continuation extends the owning volume *Native FIB on the full open
domain: affine approximation and finite attainment*. Its §§1--4 supply the
native current-ray interface, original ten-output metric, bounded
observable reduction, and scalar residual used above; §§5--9 supply the
finite-rank growth lemma, polynomial witnesses, exact updates, and
prescribed-path interface. The new synthesis is the varying-model
fixed-dimension quantifier, the finite Hankel minima and their limit, and
the exact implicit positive certificate. The classical ingredients are
finite-dimensional linear algebra, translation characters, scalar diagonal
subsequences, closed determinant equations, finite Hankel shift
realizations, generalized eigenspaces, finite geometric sums and Cesaro
cancellation, Bernstein moment identities, and finite Cauchy--Schwarz
estimates. These ingredients are used here only within the unchanged
native contract.

The statements remain limited to $0<Z<1$ and the open support
$0<k<H$. No endpoint or support-degenerate limit is included. Encoders are
functions of current rays, and only bounded affine observables were shown
to lose $\beta$; unbounded encoder coordinates and arbitrary encoder fibers
remain unclassified. The exact capacity and its attainment for general
positive fixed $n$ below $Z=2/3$ remain open. Effective bounds on the least
certificate index $M$, evaluated finite minima, matching rates, and an
optimal dimension characterization remain open. The original unrelated
finite-hidden-$N$ alternative remains unresolved, with no identification
between its objective or admissible realizations and Definition 2.1. The
results make no claim about kernel verification, finite precision,
robustness, physical implementation, efficient algorithms, training,
machine-learning benefit, or worldwide priority. The guard-recoverable
zero-dimensional exception is separate as stated in §11.5.

## 11.99 追加锚
