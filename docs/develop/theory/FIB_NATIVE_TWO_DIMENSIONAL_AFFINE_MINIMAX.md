# Native FIB: exact two-dimensional affine minimax and an attaining annulus

**Status.** Permanent reference input. The statements and proofs in this
volume are ordinary handwritten mathematics, unverified by Lean.

For the native current rays on the full open positive fiber, the optimal
uniform error with at most two real stored coordinates and exact affine
continuation has an exact scalar characterization. Below the transition
$Z=2/3$, its value is strictly between the all-finite error floor and the
best constant-readout error. A two-coordinate annulus attains it, recovers
height and every native guard, and supports every prescribed simultaneous
path. The lower bound permits arbitrary encoders; radial symmetry is a
conclusion about minimax domination, not an assumption on competitors.

The source and earlier results are credited to these two manuscripts:

- **[F]** *Native FIB continuation: exact affine obstruction and compact-band
  approximation*, including its sections on affine phase continuation and
  finite affine factors.
- **[O]** *Native FIB on the full open domain: affine approximation and
  finite attainment*, including its section on fixed-dimension uniform gaps
  and finite Hankel certificates.

Sections 1–3 reconstruct the source bridge and the bounded-observable result
needed from those manuscripts. The useful-readout rank analysis begins in
§4. The precise dependency and result maps are in §11.

## 1. Actual native rays, arbitrary preparation and the original metric

**Definition 1.1 (Native source data).** Fix $0<Z<1$, and put

$$
r=1-Z,\qquad H=r/2.
$$

Use mode order $(0,1,2,3,13)$, probability vector and tangent

$$
p(k)=(k,H-k,Z,H-k,k),\qquad 0<k<H,\qquad
d=(1,-1,0,-1,1)^{\mathsf T}.
$$

Fix an arbitrary preparation height $k_0\in(0,H)$ and arbitrary fixed
phases $\theta^{\rm in}_j$. With the native negative phase convention,

$$
\psi_j=\sqrt{p_j}\,e^{-i\theta_j},\qquad
\dot p=d\dot k,\qquad
\dot\theta_j=\frac{d_j}{p_j(k)I(k)}\dot\chi,\qquad
I(k)=\frac2k+\frac2{H-k}.
$$

Producing histories are piecewise $C^1$ or absolutely continuous native
control paths on finite compact intervals, with interior height throughout
and finite phase variation. The initial real relation lift is consistent
with $d^{\mathsf T}\theta^{\rm in}$. Queries concern current rays at arbitrary
finite prefixes, without a loop or winding restriction. Write
$\mathbb T=\mathbb R/(2\pi\mathbb Z)$.

**Lemma 1.2 (Phase equations and equality of current rays).** Relative
phase increments have the form $h=(u,v,0,v,u)$, and

$$
I(k)=\frac r{k(H-k)},\qquad
du=\left(\frac12-\frac kr\right)d\chi,\qquad
dv=-\frac kr\,d\chi.
$$

The circle coordinates $\alpha=u-v$, $\beta=u$ consequently satisfy

$$
d\alpha=\frac12d\chi,\qquad
d\beta=\left(\frac12-\frac kr\right)d\chi.
$$

They identify precisely the actual current rays, with no additional
quotient.

**Proof of Lemma 1.2.** The reciprocal sum gives the displayed $I$.
The two positive entries of $d_j/(p_jI)$ equal $(H-k)/r=1/2-k/r$;
the two negative entries equal $-k/r$, and the middle entry is zero.
Starting from zero increments proves the asserted grouping. These are
equalities of increments, without restrictions on preparation phases.
Subtracting the two equations gives the equation for $\alpha$.
Both changes of circle coordinates have integer coefficients, with inverse
$u=\beta$, $v=\beta-\alpha$.

Put $\eta_j=\theta_j^{\rm in}-\theta_2^{\rm in}$. A constant gauge gives
the representative

$$
\psi(k,u,v)=\left(
\sqrt{k}e^{-i(\eta_0+u)},
\sqrt{H-k}e^{-i(\eta_1+v)},
\sqrt Z,
\sqrt{H-k}e^{-i(\eta_3+v)},
\sqrt{k}e^{-i(\eta_{13}+u)}
\right).
$$

The positive middle entry forces any scalar relating two such
representatives of the same ray to be one. Their moduli determine $k$;
the other positive amplitudes determine $u$ and $v$ separately modulo
$2\pi$. Conversely these data determine the representative. Along a real
history lift, $d^{\mathsf T}h=2(u-v)=\chi-\chi(0)$; this does not store
that lift in the current ray. $\square$

**Proposition 1.3 (Exact reachability and all signed straight commands).**
The current-ray domain from the fixed preparation is exactly

$$
\mathcal M=(0,H)\times\mathbb T^2.
$$

For every real $s,t$, the native straight commands are

$$
P_s(k,\alpha,\beta)=(k+s,\alpha,\beta),\qquad
\operatorname{dom}P_s=\{(k,\alpha,\beta)\in\mathcal M:0<k+s<H\},
$$

$$
Q_t(k,\alpha,\beta)=
\left(k,\alpha+t/2,\beta+(1/2-k/r)t\right),\qquad
\operatorname{dom}Q_t=\mathcal M.
$$

Every point of $\mathcal M$ has a finite lawful producing history.

**Proof of Proposition 1.3.** Integrating Lemma 1.2 along a probability
leg at fixed $\chi$ and a phase leg at fixed $k$ gives these formulas.
The entire straight probability segment is interior exactly when its
endpoint is interior, by convexity. The real command $t$ itself is not
reduced modulo a period.

Choose $k_1\ne k_0$ in $(0,H)$ and put $d_k=k_1-k_0$.
The chronological rectangle $P_{d_k},Q_t,P_{-d_k},Q_{-t}$ adds
$-d_kt/r$ to both $u,v$, hence fixes $\alpha$ and adds that number
to $\beta$. For target representatives $\alpha_*,\beta_*$ set

$$
L=2\alpha_*,\qquad
q=\beta_*-(1/2-k_0/r)L,\qquad t=-rq/d_k.
$$

Execute this rectangle, then $Q_L$ at $k_0$, then $P_{k-k_0}$.
The final coordinates are exactly $(k,\alpha_*,\beta_*)$ on the
two circles. Every probability segment joins interior endpoints; every
phase variation and every history is finite. Lemma 1.2 gives the converse
and the exact equality of states. Reachable independent phase coordinates
have not been added as independent source controls. $\square$

**Definition 1.4 (Original ten outputs).** Keep edge order

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)),\qquad
\delta_{ij}=\theta_i^{\rm in}-\theta_j^{\rm in}.
$$

For each edge use the Hermitian observables

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|.
$$

Their expectation pair is
$2\sqrt{p_ip_j}U(\delta_{ij}+h_i-h_j)$, where

$$
U(a)=\binom{\cos a}{\sin a},\qquad
R_a=\begin{pmatrix}\cos a&-\sin a\\\sin a&\cos a\end{pmatrix},\qquad
J=\operatorname{diag}(1,-1).
$$

Concatenating the pairs defines $y:\mathcal M\to\mathbb R^{10}$.
Every error below uses its original Euclidean norm, with no whitening or
rescaling of outputs. Define

$$
A(k)=2\sqrt{k(H-k)},\qquad B(k)=2\sqrt{Zk},
$$

$$
D_0(a,b)=(a,b,a,Ja,Ja),\qquad
O=\bigoplus_{e\in\mathcal E}R_{\delta_e},\qquad D=OD_0.
$$

**Lemma 1.5 (Preparation-dependent decoder and exact metric factors).**
For all actual rays,

$$
y=D(A(k)U(\alpha),B(k)U(\beta)),\qquad
D^{\mathsf T}D=4I_2\oplus I_2.
$$

Thus $\|D(a,b)\|_2^2=4\|a\|_2^2+\|b\|_2^2$, and $y$ is uniformly
bounded on $\mathcal M$.

**Proof of Lemma 1.5.** The negative phase convention gives
$\overline\psi_i\psi_j=\sqrt{p_ip_j}e^{i(\theta_i-\theta_j)}$;
the expectations are twice its real and imaginary parts. The increment
differences in edge order are $\alpha,\beta,\alpha,-\alpha,-\alpha$.
Since $U(-\alpha)=JU(\alpha)$, this is exactly the asserted
factorization. The four first-pair blocks contribute $4I_2$, the other
pair contributes $I_2$, and there are no cross terms. The maps $O,J$
are orthogonal. Finally $A(k)\le H$ and $B(k)<2\sqrt{ZH}$.
Preparation affects the fixed rotations and exact initialization, not
these norm factors. $\square$

## 2. Dimension budgets and distinct continuation contracts

**Definition 2.1 (Literal affine model).** For an integer $n\ge0$, a
model of dimension at most $n$ consists of some $m\in\{0,\ldots,n\}$,
an arbitrary function $E:\mathcal M\to\mathbb R^m$, one fixed affine
decoder $q(x)=q_0+LE(x)$ into $\mathbb R^{10}$, and, for every
real $s,t$, fixed affine maps

$$
\mathcal U_s(z)=L_sz+b_s,\qquad
\mathcal V_t(z)=C_tz+d_t
$$

such that

$$
E(P_sx)=\mathcal U_sE(x)\quad(x\in\operatorname{dom}P_s),\qquad
E(Q_tx)=\mathcal V_tE(x)\quad(x\in\mathcal M).
$$

All coefficients may depend on the fixed source, preparation, model and
command, and are independent of the current state and producing history.
Both update offsets and the decoder offset are allowed. No regularity,
measurability, computability, boundedness or injectivity of $E$, no
parameter regularity, and no ambient inverse or group law are assumed.
The source supplies neither a retained lift nor an external height input.
An empty lawful domain imposes no identity, although an ambient map is
assigned for every command. Decoded vectors need not be physical outputs.

Define

$$
\operatorname{err}(E,q)=\sup_{x\in\mathcal M}\|q(x)-y(x)\|_2,\qquad
e_n^{\rm aff}(Z)=\inf_{\text{models of dimension at most }n}
\operatorname{err}(E,q).
$$

The error may be infinite. The zero-dimensional constant model makes
this literal class nonempty with finite infimum. A finite tolerance
$\epsilon$ is achievable when a model has error at most $\epsilon$.

**Definition 2.2 (Guard and path variants).** Guard recovery additionally
requires that, for every command, its lawful domain be the inverse image
under $E$ of a subset of the actual encoded image. Equivalently, all rays
in any encoder fiber must agree on lawfulness. This is separate from an
identity required only where a command is lawful.

The prescribed-path variant additionally requires one fixed affine update
for each finite prescribed simultaneous native control path, on its full
all-times source guard. The path and its integrable velocities are fixed
independently of the starting ray. Section 9 gives the exact guard and
endpoint formula. In the variant imposing both requirements, those full
path guards must also be recoverable. Infima and finite tolerance sets are
defined as above for each class; an empty class has infimum $+\infty$ and
no finite tolerance.

The stored dimension $m$, the dimension of
$\mathscr H_E=\operatorname{aff}E(\mathcal M)$, and the rank of a
particular affine readout on its direction space are different quantities.
The lower proof will use the rank of the two-coordinate $\alpha$ readout,
not the stored dimension alone or the rank of the entire decoder.

**Definition 2.3 (Reference floor and baseline).** Write

$$
e_*=2\sqrt{ZH},\qquad
R_0^2=\sup_{0<k<H}\{4A(k)^2+B(k)^2\}.
$$

The notation $e_*$ denotes the inherited all-finite floor, and must not
be confused with the dimension-zero capacity $e_0^{\rm aff}$. The
arguments below prove the needed floor and evaluate $R_0$ in the original
metric.

## 3. The inherited bounded-observable reduction

The bounded-observable theorem and worst-$\beta$ decomposition in this
section are the results of [O, §§3–4]. Their needed proofs are included to
make the interface to arbitrary encoders explicit. They are not new
phase-erasure or floor claims.

**Lemma 3.1 (One common pointwise function space).** For any finite model,
homogenize $F=(1,E)^{\mathsf T}$ and its affine updates as

$$
T_s=\begin{pmatrix}1&0\\b_s&L_s\end{pmatrix},\qquad
S_t=\begin{pmatrix}1&0\\d_t&C_t\end{pmatrix}.
$$

The spaces

$$
V_k=\operatorname{span}_{\mathbb C}
\{F_i(k,\cdot):1\le i\le m+1\}
$$

of pointwise functions on $\mathbb T^2$ are one common space $V$,
invariant under every torus translation.

**Proof of Lemma 3.1.** For any two interior heights $k,l$,
$F(l,\theta)=T_{l-k}F(k,\theta)$ at every phase point. This gives
$V_l\subseteq V_k$, and the reverse command gives equality without
assuming either ambient matrix invertible.

For $(\tau_vf)(\theta)=f(\theta+v)$, the phase command makes this
common space invariant under translation by

$$
v(k,t)=(t/2,(1/2-k/r)t),
$$

and the negative command gives inverse invariance. Two different heights
give two linearly independent real directions $(1/2,1/2-k/r)$.
Every real two-vector is their real linear combination, so every torus
translation is a composition of two such translation operators on $V$.
This statement about a common function space introduces no new source
command. $\square$

**Lemma 3.2 (Abstract characters on the bounded subspace).** Let

$$
W=\{f\in V:\|f\|_\infty<\infty\}.
$$

Then $W$ has a basis of abstract unitary characters of $\mathbb T^2$.
Each character has the form $\chi_1(\alpha)\chi_2(\beta)$; continuity
or measurability is not asserted.

**Proof of Lemma 3.2.** This is a finite-dimensional complex normed
space under the genuine pointwise supremum norm. Translations restrict
to commuting invertible isometries. An eigenvalue of one such isometry
has modulus one. A nontrivial Jordan block would give
$Au=\lambda u$, $Av=\lambda v+u$, $u\ne0$, and hence

$$
A^jv=\lambda^jv+j\lambda^{j-1}u,\qquad
\|A^jv\|\ge j\|u\|-\|v\|,
$$

contradicting isometry. Thus each translation is diagonalizable over
$\mathbb C$. The entire commuting family has a common eigenbasis:
if all its members are scalar there is nothing to show; otherwise split
into eigenspaces of a nonscalar member, note that all other members and
their inverses preserve those spaces, and induct on dimension.

For a common nonzero eigenfunction, write $\tau_vf=\chi(v)f$.
The actual translation law gives $\chi(v+w)=\chi(v)\chi(w)$ and
$|\chi(v)|=1$. Evaluation at zero gives $f(v)=f(0)\chi(v)$;
$f(0)$ cannot vanish. Rescale the basis vectors accordingly. Restricting
the character to the two circle subgroups gives the displayed product.
No integration or topological character theorem is involved. $\square$

**Lemma 3.3 (Finite interval image forces triviality).** If an abstract
homomorphism $h:(\mathbb R,+)\to S^1$ has finite image on one nonempty
open interval, it is identically one.

**Proof of Lemma 3.3.** Suppose at most $M\ge1$ image values occur
there. Fix any real $y$ and an interior point $a$. For a sufficiently
large integer $q$, the $M+1$ points $a+jy/q$, $0\le j\le M$,
all lie in the interval. Two have the same image, so
$h(y/q)^d=1$ for some $1\le d\le M$. Raising to the $q$th power
gives $h(y)^d=1$. Thus every image element has exponent dividing
$M!$. Divisibility now gives
$h(y)=h(y/M!)^{M!}=1$ for every $y$. $\square$

**Theorem 3.4 (Bounded affine observables are $\beta$-independent).**
In any finite model of Definition 2.1, a fixed affine scalar observable
of $E$ that is bounded on each phase torus at fixed height is independent
of $\beta$. In particular every component of a finite-error decoder has
this property. No such conclusion is imposed on unbounded hidden
coordinates.

**Proof of Theorem 3.4.** The surjection

$$
\pi_k:\mathbb C^{m+1}\to V,\qquad
\pi_k(a)=a^{\mathsf T}F(k,\cdot)
$$

satisfies $\tau_{v(k,t)}\pi_k=\pi_kS_t^{\mathsf T}$.
Its kernel is invariant under $S_t^{\mathsf T}$. A basis adapted to
that kernel makes this matrix block triangular, with the translation on
$V$ as its quotient block. Every eigenvalue of that translation
therefore belongs to the finite spectrum of the one fixed matrix $S_t$.
For a character from Lemma 3.2 this implies

$$
\chi_1(t/2)\chi_2((1/2-k/r)t)\in\operatorname{spec}(S_t)
\quad(0<k<H).
$$

Set $t=1$. Since $1/2-k/r$ ranges over $(0,1/2)$, the homomorphism
$x\mapsto\chi_2(x\bmod2\pi)$ has finite image on that interval.
Lemma 3.3 makes it trivial, and every circle class has a real
representative. All basis characters of $W$ are thus $\beta$-independent.

At each height the observable belongs to $V$, and its stated boundedness
puts it in $W$. For finite-error $q$, the bound
$\|q(x)\|\le\operatorname{err}(E,q)+\sup\|y\|$ proves the requisite
boundedness. Homogenization includes every affine offset, including
dimension zero. Unbounded coordinates need not belong to $W$.
$\square$

**Proposition 3.5 (Decoder projection and exact worst-phase error).**
Every finite-error decoder has the unique orthogonal decomposition

$$
q=D(a,b)+w,\qquad w\perp\operatorname{im}D,\qquad
\binom ab=(D^{\mathsf T}D)^{-1}D^{\mathsf T}q.
$$

Here $a,b,w$ are fixed affine observables of $E$ and are
$\beta$-independent. At every $k,\alpha$,

$$
\max_{\beta\in\mathbb T}\|q-y\|_2^2
=\|w\|_2^2+4\|a-A(k)U(\alpha)\|_2^2
 +(\|b\|_2+B(k))^2.
$$

Replacing the decoder by $D(a,0)$ cannot increase uniform error, and
every finite model has error at least $e_*$.

**Proof of Proposition 3.5.** Lemma 1.5 gives an invertible Gram matrix
and the asserted orthogonal projection. Its entries are fixed affine
functionals of $E$ and bounded when $q$ is bounded, so Theorem 3.4
applies. Orthogonality gives

$$
\|q-y\|_2^2=\|w\|_2^2+4\|a-A(k)U(\alpha)\|_2^2
 +\|b-B(k)U(\beta)\|_2^2.
$$

The last term is maximized in the direction opposite to $b$ when
$b\ne0$, and is constant when $b=0$. All these phases are actual
reachable rays. This proves the formula and decoder domination.
Dropping nonnegative terms gives error squared at least $4Zk$ for
every interior $k$. Its real supremum is $4ZH$, with no evaluation
at a missing endpoint. Infinite-error models satisfy this lower bound
as well. $\square$

## 4. The useful-readout rank split

**Lemma 4.1 (Zero-decoder baseline).** The zero decoder has error $R_0$,
where

$$
R_0=
\begin{cases}
(4H+Z)/2=1-Z/2,&0<Z<2/3,\\
2\sqrt{ZH},&2/3\le Z<1.
\end{cases}
$$

It is optimal among constant decoders. Below the transition its error
is attained at the interior height $k_*=H/2+Z/8$.

**Proof of Lemma 4.1.** Its squared error is

$$
4A(k)^2+B(k)^2=16k(H-k)+4Zk
=-16\left(k-\frac H2-\frac Z8\right)^2
 +\frac{(4H+Z)^2}{4}.
$$

The vertex is interior exactly when $Z<4H$, equivalently $Z<2/3$.
For $Z\ge4H$ the supremum on $(0,H)$ is its limit $4ZH$ at $H$.
For any constant decoder $q_0$, replacing $(\alpha,\beta)$ by
$(\alpha+\pi,\beta+\pi)$ replaces $y$ by $-y$, and

$$
\frac{\|q_0-y\|_2^2+\|q_0+y\|_2^2}{2}
=\|q_0\|_2^2+\|y\|_2^2.
$$

The uniform error is therefore at least $R_0$, attained by $q_0=0$.
$\square$

**Proposition 4.2 (Exhaustive rank alternatives at budget two).**
Consider a finite-error model with $m\le2$ and its affine observable
$a$ from Proposition 3.5. Let $r_a$ be the rank of the linear part
of $a$ on the direction space of $\mathscr H_E$.

If $r_a\le1$, the model has error at least $R_0$. If $r_a=2$,
then $m=2$, $\mathscr H_E=\mathbb R^2$, and $a$ itself can be used
as a bounded $\beta$-independent two-coordinate encoder with exact
state-independent affine updates. These cases cover every competitor,
including degenerate affine hulls and unbounded hidden coordinates.

**Proof of Proposition 4.2.** For $r_a\le1$, the range of $a$ lies
in a fixed affine line or point. Choose a unit normal $\nu$ and a
constant $d_0$ with $\nu\cdot a=d_0$. At any fixed height,

$$
\sup_\alpha\|a(k,\alpha)-A(k)U(\alpha)\|
\ge\sup_\alpha|d_0-A(k)\nu\cdot U(\alpha)|
=|d_0|+A(k)\ge A(k).
$$

Proposition 3.5 then gives error squared at least
$\sup_k(4A(k)^2+4Zk)=R_0^2$. This makes no assumption about
coordinates in the kernel of this useful readout.

If $r_a=2$, the inequalities
$2\le\dim\mathscr H_E\le m\le2$ are all equalities.
The affine map from $E$ to $a$ is an affine isomorphism of
$\mathbb R^2$. Conjugating each original affine update by it gives
the exact affine updates for $a$ on the same lawful domains, including
their offsets. The fixed projection of bounded $q$ makes $a$ bounded
on the whole source. Theorem 3.4 makes it $\beta$-independent.
Boundedness was derived only in this full useful-rank case. Models
with infinite error cannot improve the finite zero witness.
$\square$

## 5. A useful character pair, its common center and its modulus

In this section let $a$ be the bounded two-coordinate encoder obtained in
the rank-two case of Proposition 4.2. The common space of Lemma 3.1 now
has the form

$$
V=\operatorname{span}_{\mathbb C}\{1,a_1(k,\cdot),a_2(k,\cdot)\},
\qquad \dim_{\mathbb C}V\le3,
$$

and all its functions are bounded and $\beta$-independent.

**Lemma 5.1 (The phase-space alternatives).** Either $V$ consists only
of constants, in which case the error is at least $R_0$, or there is
one nontrivial abstract unitary character $\chi:\mathbb T\to S^1$
such that

$$
V=\operatorname{span}_{\mathbb C}\{1,\chi,\overline\chi\},\qquad
a(k,\alpha)=c(k)+M(k)
\binom{\operatorname{Re}\chi(\alpha)}{\operatorname{Im}\chi(\alpha)},
$$

where $M(k)$ is a real invertible matrix for every interior height.

**Proof of Lemma 5.1.** Lemma 3.2 supplies the character basis.
The space is closed under complex conjugation because its original
generators are real, so each character occurs with its conjugate.
A real unitary character takes values in $\{1,-1\}$ and is trivial:
for each circle element $h$ choose a half $h/2$ and use
$\chi(h)=\chi(h/2)^2=1$. A nontrivial character and its conjugate
are therefore distinct. A character eigenspace has dimension one,
since evaluation at zero determines every eigenfunction as a scalar
multiple of that character. With the constant already present, dimension
at most three leaves exactly the stated alternatives.

In the constant case $a(k,\alpha)$ is independent of $\alpha$;
its distance from the radius-$A(k)$ circle has supremum at least $A(k)$,
so Proposition 3.5 gives $R_0$. Otherwise the real coefficients of the
character pair give $c(k),M(k)$. If $M(k)$ were singular at one
height, the span of $1,a_1(k,\cdot),a_2(k,\cdot)$ would have dimension
at most two, contradicting the common three-dimensional space $V$.
No heightwise collapse or unproved continuity assertion is used.
$\square$

For a unit complex number $z$, let $\mathsf R(z)$ denote its real
multiplication matrix on $\mathbb C\cong\mathbb R^2$.

**Lemma 5.2 (Common center and complex commutant).** In the nontrivial
case there are a fixed $c\in\mathbb R^2$, a real invertible matrix
$M_*$, and a function $f:(0,H)\to\mathbb C\setminus\{0\}$ with
$f(H/2)=1$ such that

$$
a(k,\alpha)=c+M_*\bigl(f(k)\chi(\alpha)\bigr).
$$

For each $|s|<H$ there is one nonzero complex number $m_s$ with
$f(k+s)=m_sf(k)$ at every lawful starting height. Every phase update
and every probability update with nonempty domain fix the same center $c$.

**Proof of Lemma 5.2.** Write the update of $a$ for $Q_{2h}$ as
$z\mapsto C_hz+d_h$, where $h\in\mathbb R$ and $\chi(h)$ means
evaluation on its circle class. Comparing
the independent constant and character coefficients in Lemma 5.1 gives

$$
c(k)=C_hc(k)+d_h,\qquad
M(k)\mathsf R(\chi(h))=C_hM(k).
$$

Choose $h$ with $\chi(h)\ne1$. Since $C_h$ is similar to
$\mathsf R(\chi(h))$, the matrix $I-C_h$ is invertible. Thus every
$c(k)$ equals the one solution of $(I-C_h)c=d_h$. Call it $c$;
the displayed identity also shows that every other phase update fixes $c$.

Let $k_*=H/2$ and $M_*=M(k_*)$. Comparing phase actions at $k$
and $k_*$ shows that $M_*^{-1}M(k)$ commutes with every
$\mathsf R(\chi(h))$. The image of this nontrivial character is not
contained in $\{1,-1\}$, by the half-element argument of Lemma 5.1.
Choose a value with nonzero imaginary part and put

$$
J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

Commuting with that rotation is equivalent to commuting with $J_0$,
after subtracting its scalar real part and dividing by its nonzero
imaginary part. Solving $NJ_0=J_0N$ gives
$N=\begin{pmatrix}a&-b\\b&a\end{pmatrix}$, exactly complex
multiplication by $a+ib$. Invertibility excludes zero. This proves
the representation by $f(k)$ and its normalization.

Write the useful probability update as $z\mapsto L_sz+b_s$.
For any lawful pair $k,k+s$, coefficient comparison gives

$$
L_sM(k)=M(k+s),\qquad L_sc+b_s=c.
$$

Thus $L_s$ is invertible for $|s|<H$. In the $M_*$ coordinates it
is multiplication by $f(k+s)/f(k)$, which is independent of the
lawful starting height because $L_s$ is one fixed matrix. Denote it
by $m_s$. No statement has been made about unused ambient directions
in other models or about maps with empty lawful domain. $\square$

**Lemma 5.3 (A local law and an ordinary exponential modulus).** There
is a finite real $\gamma$ such that

$$
|m_s|=e^{\gamma s}\quad(|s|<H),\qquad
|f(k)|=e^{\gamma(k-H/2)}\quad(0<k<H).
$$

This conclusion imposes no continuity on $\chi$ or on $f/|f|$.

**Proof of Lemma 5.3.** If $|s|,|t|,|s+t|<H$, the spread of
$\{0,s,s+t\}$ equals $\max\{|s|,|t|,|s+t|\}<H$. Some $k$
therefore makes $k,k+s,k+s+t$ all interior. Comparing the two
lawful consecutive legs with the single summed leg gives

$$
m_{s+t}=m_tm_s,\qquad m_0=1,\qquad m_{-s}=m_s^{-1}.
$$

This local law is derived on actual lawful triples. It is not an
assumed ambient representation.

Boundedness of $a$ and invertibility of $M_*$ bound $|f(k)|$ by
some finite $K\ge1$: evaluate the representation at $\alpha=0$ and
apply $M_*^{-1}$ to $a(k,0)-c$. For $|s|<H/2$, using the
reference height gives $|m_s|=|f(H/2+s)|\le K$. Using $-s$
and the inverse law gives $|m_s|\ge K^{-1}$.
Consequently $b(s)=\log|m_s|$ is locally additive on $(-H,H)$
and $|b(s)|\le\log K$ for $|s|<H/2$.

For any positive integer $N$ and $|s|<H/(2N)$, successive use
of the local law along $s,2s,\ldots,Ns$ gives
$|b(s)|=|b(Ns)|/N\le\log K/N$. This proves continuity at zero.
For each fixed $s\in(-H,H)$, the identity
$b(s+h)-b(s)=b(h)$ for sufficiently small $h$ proves continuity
at $s$. Put $a_*=H/4$. Subdivision and finite sums inside
$(-H,H)$ give $b(qa_*)=q b(a_*)$ for every rational $q$ with
$|qa_*|<H$, including negative $q$ by oddness. Density and
continuity yield $b(s)=\gamma s$ throughout that interval, with
$\gamma=b(a_*)/a_*$. Apply this to $s=k-H/2$ and $f(H/2)=1$.
$\square$

**Example 5.4 (Bounded encoders can retain a discontinuous unit phase).**
For any additive $\ell:\mathbb R\to\mathbb R$ and finite real
$\gamma$, the bounded encoder

$$
E(k,\alpha,\beta)=e^{\gamma k}U(\alpha+\ell(k))
$$

has exact updates $e^{\gamma s}R_{\ell(s)}$ and $R_{t/2}$ for
the full straight-command menu. Its unit phase need not be continuous.

**Proof of Example 5.4.** Additivity and the native command formulas
give the two identities by substitution. Boundedness follows from
$0<k<H$ and finite $\gamma$. To see explicitly that the phase can
be discontinuous, choose an irrational $a$ and a rational vector-space
basis of $\mathbb R$ containing $1,a$. Prescribe $\ell(1)=0$,
$\ell(a)=1$, zero on the remaining basis elements, and extend
rationally linearly. For rationals $q_j\to a$, the increments
$a-q_j$ tend to zero while $e^{i\ell(a-q_j)}=e^i\ne1$.
The same increments at any interior height disprove phase continuity
there. This choice example is only a boundary example; the minimax
argument uses no basis choice and no phase regularity. $\square$

## 6. Finite character averages and exhaustive radial domination

**Lemma 6.1 (Simultaneous finite averages of nontrivial characters).**
For any finite list $\psi_1,\ldots,\psi_d$ of nontrivial unitary
characters of an abelian group, there are finite probability averages
of group points under which every listed character has average tending
to zero.

**Proof of Lemma 6.1.** Choose $h_j$ with $\psi_j(h_j)\ne1$.
Average over the multiset of points
$\sum_{j=1}^d n_jh_j$, $0\le n_j<N$, with equal weights.
For any character $\psi$ its average is

$$
\prod_{j=1}^d\left(\frac1N\sum_{n=0}^{N-1}\psi(h_j)^n\right).
$$

Each factor has modulus at most one. For $\psi=\psi_j$, its
$j$th factor is
$(1-\psi_j(h_j)^N)/(N(1-\psi_j(h_j)))$, tending to zero.
This is a finite geometric-sum identity followed by a scalar limit,
requiring neither integration nor measurability. $\square$

**Lemma 6.2 (Unmatched characters cannot improve the baseline).** Let
$\xi(\alpha)=e^{i\alpha}$. If the character in Lemma 5.2 is neither
$\xi$ nor $\xi^{-1}$, the model has error at least $R_0$.

**Proof of Lemma 6.2.** Identify the useful output plane with
$\mathbb C$ and write the real-linear map
$M_*(z)=p_+z+p_-\overline z$. At a fixed height,

$$
a(k,\alpha)=c+p_+f(k)\chi(\alpha)
 +p_-\overline{f(k)}\chi(\alpha)^{-1}.
$$

The characters $\xi^{-1}$, $\chi\xi^{-1}$ and
$\chi^{-1}\xi^{-1}$ are all nontrivial under the stated
assumption. Lemma 6.1 makes the average of
$a(k,\alpha)\xi(\alpha)^{-1}$ tend to zero. Since

$$
|a-A(k)\xi|^2=|a|^2+A(k)^2
 -2A(k)\operatorname{Re}(a\xi^{-1}),
$$

its supremum is at least $A(k)^2$: each finite average is at
least $A(k)^2$ minus a term tending to zero. Proposition 3.5
then gives the uniform lower bound $R_0$. All averages use actual
phase points, including for discontinuous abstract characters.
$\square$

**Lemma 6.3 (Matched-character radial domination).** In the remaining
case some $C\ge0$ and finite real $\gamma$ satisfy

$$
\operatorname{err}(E,q)^2\ge
\sup_{0<k<H}\left\{4(Ce^{\gamma k}-A(k))^2+4Zk\right\}.
$$

**Proof of Lemma 6.3.** Conjugate the chosen character basis if
necessary so that $\chi=\xi$. At a fixed height the useful error
vector is

$$
c+(p_+f(k)-A(k))e^{i\alpha}
 +p_-\overline{f(k)}e^{-i\alpha}.
$$

Write its nonconstant part as $h(\alpha)$. Since
$h(\alpha+\pi)=-h(\alpha)$, the mean of the squared errors
at these opposite phases is $|c|^2+|h(\alpha)|^2$.
Their worst error is therefore at least $|h(\alpha)|$.
For any complex $z,w$,

$$
\sup_\alpha|ze^{i\alpha}+we^{-i\alpha}|=|z|+|w|:
$$

the triangle inequality gives the upper bound, and choosing $2\alpha$
to align the two nonzero terms gives equality; zero terms are immediate.
It follows that the worst useful error at this height is at least

$$
|p_+f(k)-A(k)|+|p_-|\,|f(k)|
\ge\bigl||p_+|\,|f(k)|-A(k)\bigr|.
$$

By Lemma 5.3 the last expression is $|Ce^{\gamma k}-A(k)|$
with $C=|p_+|e^{-\gamma H/2}\ge0$. The case $p_+=0$ gives
$C=0$. Add the unavoidable $4Zk$ term using Proposition 3.5
and take the supremum. $\square$

**Theorem 6.4 (Exact arbitrary-encoder radial minimax reduction).**
For every $0<Z<1$,

$$
\boxed{
(e_2^{\rm aff}(Z))^2
=\inf_{C\ge0,\ \gamma\in\mathbb R}
\sup_{0<k<H}\{4(Ce^{\gamma k}-A(k))^2+4Zk\}.}
$$

This is equality of minimax values and domination of every competitor
in uniform error. It does not classify all affine factors as radial.

**Proof of Theorem 6.4.** Models of infinite error are harmless.
For a finite-error model Proposition 4.2 is exhaustive. The deficient
rank case, the constant phase-space case of Lemma 5.1, and the
unmatched-character case of Lemma 6.2 have error at least the zero
baseline, which is the radial choice $C=0$. Lemma 6.3 treats every
remaining case. Thus each competing model is bounded below by the
error of an allowed radial choice.

Conversely, for any $C>0$ and finite real $\gamma$, use

$$
E_{C,\gamma}(k,\alpha,\beta)=Ce^{\gamma k}U(\alpha),\qquad
q=D(E_{C,\gamma},0),
$$

with updates $z\mapsto e^{\gamma s}z$ and
$z\mapsto R_{t/2}z$. Substitution proves the exact identities on
every full lawful domain, for all signed real commands. Lemma 1.5
gives exactly the objective displayed in the theorem. For $C=0$ use
the zero model. Both infimum inequalities follow, and nonnegativity
allows squaring the error infimum. Every sign of $\gamma$ is included.
No compactness of encoder images, coefficient bound, convergence of
matrices, or endpoint encoding is used. $\square$

## 7. The exact scalar endpoint and the unique radial profile

**Definition 7.1 (Normalized error and endpoint exponential).** Throughout
this section assume $0<Z<2/3$, and put

$$
\tau=\frac{Z}{4H}\in(0,1),\qquad
x=\frac{k}{H},\qquad
s(x)=\sqrt{x(1-x)},\qquad
T_0=\frac{(1+\tau)^2}{4}.
$$

For $c\ge0$, $\lambda\in\mathbb R$, define

$$
\mathcal J(c,\lambda)=
\max_{0\le x\le1}\{(ce^{\lambda x}-s(x))^2+\tau x\}.
$$

For $T>\tau$ define

$$
v_T(x)=\sqrt{T-\tau x},\qquad
\lambda_T=\frac12\log\frac{T-\tau}{T},\qquad
f_T(x)=\sqrt T\,e^{\lambda_Tx}
       =T^{(1-x)/2}(T-\tau)^{x/2},
$$

$$
g_T(x)=s(x)-v_T(x)-f_T(x),\qquad
\Phi_\tau(T)=\max_{0\le x\le1}g_T(x).
$$

**Lemma 7.2 (Normalization and scalar endpoint meaning).** Under
$c=C/(2H)$ and $\lambda=\gamma H$, the radial squared error of
Theorem 6.4 equals $16H^2\mathcal J(c,\lambda)$. For $c=0$ it equals
$16H^2T_0=R_0^2$. For every $c>0$ and finite $\lambda$,
$\mathcal J(c,\lambda)>\tau$.

**Proof of Lemma 7.2.** Substitute $k=Hx$ and $A(k)=2Hs(x)$.
The radial amplitude is $2Hce^{\lambda x}$, and the remaining term
becomes $4ZHx=16H^2\tau x$. The resulting scalar function is
continuous on $[0,1]$, so its supremum on $(0,1)$ equals its
closed-interval maximum. This concerns the explicit scalar formula;
it makes no extension of an arbitrary encoder to endpoint source states.

For $c=0$,

$$
s(x)^2+\tau x
=T_0-\left(x-\frac{1+\tau}{2}\right)^2,
$$

and the vertex is interior. For $c>0$, the scalar endpoint value at
$x=1$ is $c^2e^{2\lambda}+\tau>\tau$. It is a limit of interior
errors, hence bounds their supremum below. $\square$

**Lemma 7.3 (Endpoint-log corridor equivalence).** At any $T>\tau$,
there exists a positive exponential $R(x)=ce^{\lambda x}$ with
$\mathcal J(c,\lambda)\le T$ if and only if

$$
s(x)-v_T(x)\le f_T(x)\quad(0\le x\le1),
$$

equivalently $\Phi_\tau(T)\le0$. Whenever this holds, $f_T$ is itself
feasible. Every feasible positive exponential satisfies $R\le f_T$.

**Proof of Lemma 7.3.** The error inequality is exactly the corridor

$$
\ell_T(x):=s(x)-v_T(x)\le R(x)\le
u_T(x):=s(x)+v_T(x).
$$

In particular $R(0)\le\sqrt T$ and $R(1)\le\sqrt{T-\tau}$.
Because $\log R$ is affine,

$$
\log R(x)=(1-x)\log R(0)+x\log R(1)
\le\frac{1-x}{2}\log T+\frac x2\log(T-\tau)=\log f_T(x).
$$

Thus feasibility implies $\ell_T\le R\le f_T$.

For the converse, $s$ and $v_T$ are concave and $u_T>0$ on the
closed interval. The logarithm of $u_T$ is concave: for positive
values, first use concavity of $u_T$, then monotonicity and concavity
of $\log$. A concave function lies above its endpoint chord.
That chord for $\log u_T$ is precisely $\log f_T$, since
$u_T(0)=\sqrt T$ and $u_T(1)=\sqrt{T-\tau}$. Hence
$f_T\le u_T$ everywhere. If $\ell_T\le f_T$, both corridor
inequalities hold for $f_T$. This proves equivalence, with no
logarithm taken of the possibly nonpositive lower corridor.
$\square$

**Theorem 7.4 (Unique scalar root strictly between floor and baseline).**
There is exactly one $T_\tau>\tau$ satisfying
$\Phi_\tau(T_\tau)=0$, and

$$
\tau<T_\tau<T_0.
$$

Every radial model has normalized squared error at least $T_\tau$,
and $\mathcal J(\sqrt{T_\tau},\lambda_{T_\tau})=T_\tau$.

**Proof of Theorem 7.4.** The defining functions are jointly continuous
on a compact $x$ interval and any compact $T$ interval inside
$(\tau,\infty)$. Uniform continuity there proves continuity of
$\Phi_\tau$: the difference of two maxima is bounded in absolute
value by the supremum of the difference of their functions.

For every $x\in[0,1]$,

$$
\partial_T\log f_T(x)=
\frac{1-x}{2T}+\frac{x}{2(T-\tau)}>0.
$$

If $T_2>T_1>\tau$, also

$$
v_{T_2}(x)-v_{T_1}(x)
=\frac{T_2-T_1}{v_{T_2}(x)+v_{T_1}(x)}
\ge\frac{T_2-T_1}{\sqrt{T_2}+\sqrt{T_1}}>0.
$$

Thus $g_{T_2}$ lies below $g_{T_1}$ by a uniform positive amount;
$\Phi_\tau$ is strictly decreasing.

The square-completion identity in Lemma 7.2 gives
$s(x)\le v_{T_0}(x)$ everywhere. Since
$T_0-\tau=(1-\tau)^2/4>0$ and $f_{T_0}$ has a positive minimum,
$\Phi_\tau(T_0)<0$.

For the other sign, fix $x_0=(1+\tau)/2$, so $\tau<x_0<1$.
As $T\downarrow\tau$,

$$
f_T(x_0)\longrightarrow0,\qquad
s(x_0)-v_T(x_0)\longrightarrow
\sqrt{1-x_0}\,(\sqrt{x_0}-\sqrt\tau)>0.
$$

Thus $\Phi_\tau(T)>0$ for $T$ sufficiently close to $\tau$ from
above. This uses a fixed interior point and does not assert uniform
convergence of $f_T$ at $x=0$ as $T\downarrow\tau$.
The intermediate value theorem and strict decrease give exactly one
root, in the asserted interval.

For a positive exponential, Lemma 7.2 puts its error level above
$\tau$. If it were below $T_\tau$, Lemma 7.3 would contradict
strict decrease of $\Phi_\tau$. Conversely Lemma 7.3 makes
$f_{T_\tau}$ feasible. It cannot have error below $T_\tau$ by the
same argument. The zero amplitude has larger value $T_0$.
This proves the minimum over all radial parameters, without any
compactness or existence assumption about a minimizing sequence.
$\square$

**Theorem 7.5 (Strict concavity, unique contact and tangency system).**
For each $T>\tau$, $g_T$ is strictly concave on $(0,1)$ and has one
interior maximizer. At $T=T_\tau$, denote it by $x_\tau$. Then

$$
\frac{1+\tau}{2}<x_\tau<1.
$$

The pair $(T_\tau,x_\tau)$ is the unique solution in
$\tau<T<T_0$, $(1+\tau)/2<x<1$ of

$$
\sqrt{x(1-x)}-\sqrt{T-\tau x}
=\sqrt T\,e^{\lambda_Tx},
$$

$$
\frac{1-2x}{2\sqrt{x(1-x)}}
+\frac{\tau}{2\sqrt{T-\tau x}}
-\lambda_T\sqrt T\,e^{\lambda_Tx}=0.
$$

**Proof of Theorem 7.5.** On the open interval write $s=s(x)$ and
$v=v_T(x)$. Direct differentiation of these explicit smooth functions
gives

$$
s'=\frac{1-2x}{2s},\qquad s''=-\frac1{4s^3},\qquad
v'=-\frac{\tau}{2v},\qquad v''=-\frac{\tau^2}{4v^3},
$$

$$
g_T'=\frac{1-2x}{2s}+\frac{\tau}{2v}-\lambda_Tf_T,\qquad
g_T''=-\frac1{4s^3}+\frac{\tau^2}{4v^3}-\lambda_T^2f_T.
$$

Because $T>\tau$ and $0<\tau<1$,

$$
v^2>\tau(1-x),\qquad
\frac{\tau^2}{v^3}
<\frac{\sqrt\tau}{(1-x)^{3/2}}
<\frac1{[x(1-x)]^{3/2}}=\frac1{s^3}.
$$

Consequently $g_T''<0$. For fixed $T>\tau$, the terms other than
$s'$ in $g_T'$ have finite endpoint limits, while $s'$ tends to
$+\infty$ at zero and $-\infty$ at one. The derivative is strictly
decreasing and has exactly one zero; this is the unique maximizer.
The endpoint values are

$$
g_T(0)=-2\sqrt T,\qquad g_T(1)=-2\sqrt{T-\tau},
$$

both negative.

If $\tau<T<T_0$, at $x_0=(1+\tau)/2$ the square-completion identity
gives $v_T(x_0)<s(x_0)$, and $\lambda_T<0$. Therefore

$$
g_T'(x_0)=
\frac{\tau}{2}\left(\frac1{v_T(x_0)}-\frac1{s(x_0)}\right)
-\lambda_Tf_T(x_0)>0.
$$

The maximizer at the root is strictly to the right of $x_0$.
At that maximizer $g_{T_\tau}=0$ and $g_{T_\tau}'=0$,
which are the two displayed equations. Conversely, any pair in the
specified ranges satisfying them is the unique maximizer of $g_T$
and has maximum zero. The unique root of Theorem 7.4 and strict
concavity then force that pair to be $(T_\tau,x_\tau)$.
$\square$

**Theorem 7.6 (Exact capacity and uniqueness within the radial family).**
For $0<Z<2/3$,

$$
\boxed{e_2^{\rm aff}(Z)=4H\sqrt{T_\tau}},\qquad
2\sqrt{ZH}<e_2^{\rm aff}(Z)<1-Z/2.
$$

The unique optimal positive radial amplitude is

$$
\rho(k)=2H\sqrt{T_\tau}\,
\exp\!\left(\lambda_{T_\tau}\frac{k}{H}\right).
$$

No uniqueness of arbitrary affine realizations is asserted.

**Proof of Theorem 7.6.** Theorem 6.4, Lemma 7.2 and Theorem 7.4
give the exact squared minimum $16H^2T_\tau$.
The inequalities $\tau<T_\tau<T_0$ give precisely the two strict
bounds in the original norm.

Let $R(x)=ce^{\lambda x}>0$ be any optimal normalized radial
amplitude. Lemma 7.3 puts $R\le f_{T_\tau}$. At the interior
contact $x_\tau$, the lower corridor equals $f_{T_\tau}$, so
$R(x_\tau)=f_{T_\tau}(x_\tau)$. The affine function
$\log f_{T_\tau}-\log R$ is nonnegative at both endpoints and
zero at an interior point. Its value there is a strictly positive
convex combination of its endpoint values, so both endpoint values
are zero. It vanishes identically. Thus
$c=\sqrt{T_\tau}$ and $\lambda=\lambda_{T_\tau}$, giving the
stated unique amplitude. The zero amplitude is excluded because its
value is $T_0>T_\tau$.

The lower bound holds for every finite parameter choice. Consequently
sequences with $C$ or $\gamma$ escaping to infinity, or $C$ tending
to zero while $\gamma$ varies, cannot lower the infimum. The same
uniform lower bound applies to arbitrary varying encoders by Theorem
6.4; no limiting latent object is needed. $\square$

## 8. The actual annulus, exact updates and interior error attainment

**Theorem 8.1 (Attaining native annulus).** Assume $0<Z<2/3$ and set

$$
T=T_\tau,\qquad \lambda=\lambda_T<0,\qquad \gamma=\lambda/H.
$$

Use the two-coordinate encoder and one fixed linear original decoder

$$
E_*(k,\alpha,\beta)=\rho(k)U(\alpha),\qquad
\rho(k)=2H\sqrt T\,e^{\gamma k},\qquad
\mathcal D_*(z)=D(z,0).
$$

Its image is exactly the open annulus

$$
\mathscr A_*=
\{z\in\mathbb R^2:2H\sqrt{T-\tau}<\|z\|<2H\sqrt T\}.
$$

Its affine hull is $\mathbb R^2$, and its fibers are precisely the
$\beta$ circles at fixed $(k,\alpha)$. It attains uniform error
$4H\sqrt T$; every phase pair at the actual interior height
$k=Hx_\tau$ realizes that error.

**Proof of Theorem 8.1.** The exponent is finite and negative because
$T>\tau>0$. The positive radius is strictly decreasing, with limits
$2H\sqrt T$ at $k=0$ and
$2H\sqrt T\,e^\lambda=2H\sqrt{T-\tau}$ at $k=H$.
It maps $(0,H)$ bijectively onto the open radius interval. Full
phase reachability proves the image assertion. A positive-radius
circle spans the whole affine plane, so the actual affine hull is
two-dimensional. The radius recovers $k$ and the unit vector recovers
the circle class $\alpha$; $\beta$ is ignored, proving the fibers.

With $x=k/H$, Lemma 1.5 gives squared error

$$
\|\mathcal D_*E_*(k,\alpha,\beta)-y(k,\alpha,\beta)\|_2^2
=4(\rho(k)-A(k))^2+4Zk
=16H^2\bigl((f_T(x)-s(x))^2+\tau x\bigr).
$$

The corridor bounds it by $16H^2T$. At $x=x_\tau$ the contact
identity gives $f_T=s-v_T$, so the bracket equals
$v_T(x_\tau)^2+\tau x_\tau=T$. This is an actual interior source
height, and the expression is independent of both phases. The
model therefore attains the infimum, and its error supremum is
also attained by lawful states. $\square$

**Proposition 8.2 (Height recovery, all real commands and initialization).**
On the actual annulus define

$$
\kappa(z)=\frac1\gamma
\log\frac{\|z\|}{2H\sqrt T}.
$$

The exact probability guard is $0<\kappa(z)+s<H$, and the phase
guard is all of $\mathscr A_*$. The fixed ambient linear maps

$$
\mathcal U_s^*(z)=e^{\gamma s}z,\qquad
\mathcal V_t^*(z)=R_{t/2}z
$$

intertwine every real signed command on its entire native domain.
At the original preparation the exact initial value is
$z_0=\rho(k_0)U(0)$. More generally every actual current ray can be
initialized at its displayed $E_*$.

**Proof of Proposition 8.2.** Direct substitution gives
$\kappa(E_*(k,\alpha,\beta))=k$. Thus the displayed guard is
exactly the source guard and is constant on every encoder fiber.
Also

$$
E_*(P_sx)=e^{\gamma s}E_*(x),\qquad
E_*(Q_tx)=R_{t/2}E_*(x)
$$

on the respective domains. The actual source change of $\beta$ is
still present in $Q_t$, and disappears only after applying $E_*$.
All signed real commands, including zero and those with empty
probability domains, have the displayed ambient maps. The image is
preserved whenever the command is lawful; no off-image vector is
declared a native state.

The preparation increments are zero, even for arbitrary preparation
phases, so its $\alpha$ is zero. The decoder still contains the
original fixed rotations $O$. Starting from any exact encoding,
induction with the two identities gives exact encoding after every
finite lawful word. Fractional commands give the same statement at
every intermediate point of a straight leg. The uniform readout
bound is evaluated at each current encoded ray and does not
accumulate; no approximate output is fed back as latent state.
$\square$

## 9. Every prescribed simultaneous path and its full guard

**Proposition 9.1 (Native simultaneous path formula).** Prescribe
integrable velocities $a_c=\dot k$ and $b_c=\dot\chi$ on a finite
compact interval $[0,T_{\rm p}]$, in the native regularity class.
Put

$$
\eta(t)=\int_0^t a_c(v)\,dv,\qquad
\Delta=\eta(T_{\rm p}),\qquad
L=\int_0^{T_{\rm p}}b_c(t)\,dt,\qquad
C_{\rm p}=\int_0^{T_{\rm p}}\eta(t)b_c(t)\,dt.
$$

The exact guard from initial height $k$ is

$$
0<k+\eta(t)<H\quad\text{for every }t\in[0,T_{\rm p}],
$$

equivalently

$$
k+\min_{[0,T_{\rm p}]}\eta>0,\qquad
k+\max_{[0,T_{\rm p}]}\eta<H.
$$

On that guard the native endpoint is

$$
k'=k+\Delta,\qquad
\alpha'=\alpha+L/2,\qquad
\beta'=\beta+(1/2-k/r)L-C_{\rm p}/r.
$$

Two successive relative paths have combined parameters

$$
(\Delta_1+\Delta_2,\quad L_1+L_2,\quad
C_1+C_2+\Delta_1L_2).
$$

**Proof of Proposition 9.1.** The displacement $\eta$ is absolutely
continuous, hence continuous and bounded on the compact interval.
The mixed integral exists since $b_c$ is integrable. The entire
height trajectory is $k+\eta(t)$, proving the all-times guard.
Its extrema are attained, justifying the strict extremal
inequalities. Lawful endpoints alone cannot replace this guard.

Integrating Lemma 1.2 gives the height and $\alpha$ formulas, and

$$
\int_0^{T_{\rm p}}\left(\frac12-\frac{k+\eta(t)}r\right)b_c(t)\,dt
=\left(\frac12-\frac kr\right)L-\frac{C_{\rm p}}r
$$

gives the $\beta$ formula, including the negative mixed term.
These are circle identities and require no stored real phase lift.
During the second path of a concatenation, displacement relative
to the original start is $\Delta_1+\eta_2(t)$. Its contribution to
the mixed integral is $C_2+\Delta_1L_2$, proving the combined
triple. Substitution in the endpoint formula agrees with successive
source application. The combined guard is the first full guard
together with the second full guard from height $k+\Delta_1$.
This argument integrates the source directly, without any
finite-splitting or trajectory-limit assertion. $\square$

**Theorem 9.2 (The same annulus realizes all paths and all truncations).**
The annulus of Theorem 8.1 has, for every prescribed path of
Proposition 9.1, the fixed linear update

$$
\mathcal W_{\rm p}(z)=e^{\gamma\Delta}R_{L/2}z
$$

on the exact recoverable guard

$$
0<\kappa(z)+\eta(t)<H\quad(0\le t\le T_{\rm p}).
$$

Exact encoding and the same optimal uniform error hold at every
intermediate time and every prefix of every finite lawful concatenation.
Below $Z=2/3$, the literal, guard-recoverable, prescribed-path, and
combined dimension-at-most-two capacities all equal $4H\sqrt{T_\tau}$,
and all include that tolerance endpoint.

**Proof of Theorem 9.2.** Substitute the endpoint in Proposition 9.1
into $E_*$:

$$
E_*(k',\alpha',\beta')
=2H\sqrt T\,e^{\gamma(k+\Delta)}U(\alpha+L/2)
=e^{\gamma\Delta}R_{L/2}E_*(k,\alpha,\beta).
$$

The mixed source term has not been deleted from the native formula.
It is invisible to this encoder because its fibers are the $\beta$
circles. The update coefficients depend only on the prescribed path
and fixed model. The recovered height gives precisely the full source
guard, including empty guards, and proves image preservation there.

Replace the upper integration limit by any intermediate time. The
same identity proves the exact intermediate encoding, including
every truncated path and its own all-times guard. For two successive
paths, the encoded maps compose by adding $\Delta$ and $L$ because
scalar multiplication commutes with planar rotation. Proposition
9.1 retains the additional $\Delta_1L_2$ in the true source's
mixed parameter. Thus encoded commutation is a consequence of the
permitted phase loss, not commutation of the original controls.
Induction proves every finite lawful concatenation, with the
current-state error from Theorem 8.1 at every point.

Each stronger class is a subclass of the literal class, so
Theorem 7.6 supplies its lower bound. The one annular model belongs
to all four classes and supplies the matching upper bound.
Its error equals the endpoint, so every finite tolerance at or
above it is achievable and none below it is. No equality of
arbitrary model classes is inferred from equality of their
capacities. $\square$

## 10. Lower dimensions, transition and scalar parameter limits

**Theorem 10.1 (Exact dimension-zero and dimension-one baselines).**
For every $0<Z<1$,

$$
e_0^{\rm aff}(Z)=e_1^{\rm aff}(Z)=R_0.
$$

The same values hold if all prescribed paths are required. In the
guard-recoverable class, with or without prescribed paths, the
dimension-zero class is empty and the dimension-at-most-one capacity
is $R_0$. Every finite endpoint asserted here is achieved.

**Proof of Theorem 10.1.** Every model of stored dimension at most
one has useful-readout rank at most one. Proposition 4.2 therefore
gives the lower bound $R_0$, while the literal zero-dimensional
model with decoder zero gives the upper bound. In $\mathbb R^0$
there is a single encoded value and a unique ambient update. Its
intertwining identities hold for every lawful source command and
every lawful prescribed path, without a guard-recovery assertion.
Lemma 4.1 also directly proves optimality over all constant decoder
offsets.

To disprove guard recovery in dimension zero, choose $k_1<k_2$ in
$(0,H)$ and set $s=H-(k_1+k_2)/2$. Then

$$
0<k_1+s=H-(k_2-k_1)/2<H,\qquad
k_2+s=H+(k_2-k_1)/2>H.
$$

The two equal encodings would have to give different guard answers.
Thus this class is empty.

For dimension at most one with guard recovery, use

$$
E_{\rm h}(k,\alpha,\beta)=K=k,\qquad
\mathcal U_s(K)=K+s,\qquad
\mathcal V_t(K)=K,\qquad q(K)=0.
$$

Its actual image is $(0,H)$ and its straight guard is exactly
$0<K+s<H$. For the path of Proposition 9.1 its affine update is
$K\mapsto K+\Delta$, with full guard
$0<K+\eta(t)<H$ at every time. These formulas give exact endpoint,
truncation and concatenation identities directly. The zero readout
has error $R_0$. Subclass inclusion supplies the same lower bound
for both guarded variants, completing the proof. $\square$

**Theorem 10.2 (Transition and model attainment without a maximizing state).**
For $2/3\le Z<1$, all four dimension-at-most-two capacities equal

$$
e_*=2\sqrt{ZH}.
$$

For the literal and prescribed-path classes the same holds for
every dimension bound $n\ge0$, already attained in dimension zero.
For the guard-recoverable variants it holds for every $n\ge1$,
attained by the height encoder. For these witnesses every individual
lawful state has error strictly smaller than $e_*$.

**Proof of Theorem 10.2.** The universal lower bound is Proposition
3.5. If $Z\ge4H$, the zero decoder has squared error

$$
16k(H-k)+4Zk
=4ZH+4(H-k)(4k-Z)<4ZH\quad(0<k<H).
$$

Its supremum is nevertheless $4ZH$ by taking the scalar limit
through interior heights $k\uparrow H$. At $Z=4H$, equivalently
$Z=2/3$, the difference from $4ZH$ is exactly
$-16(H-k)^2$, so the strict pointwise inequality includes the
transition. The zero-dimensional model supplies both unguarded
contracts; the height model of Theorem 10.1 supplies both guarded
contracts. They fit all larger dimension-at-most budgets. These
are single models attaining their error infima even though no
lawful source state maximizes their errors. No value of an encoder
at $k=H$ has been used. $\square$

**Corollary 10.3 (Exact tolerance sets for all solved small budgets).**
In the following table each finite entry $v$ means capacity $v$
and finite achievable tolerance set exactly $[v,\infty)$. The
notation “empty” means no models, capacity $+\infty$, and no finite
tolerance. A path requirement always means every prescribed native
path on its full all-times guard.

| Dimension budget | Contract | $0<Z<2/3$ | $2/3\le Z<1$ |
|---|---|---|---|
| At most $0$ | Literal, or with paths | $1-Z/2$ | $2\sqrt{ZH}$ |
| At most $0$ | Guard recovery, with or without paths | Empty | Empty |
| At most $1$ | Any of the four variants | $1-Z/2$ | $2\sqrt{ZH}$ |
| At most $2$ | Any of the four variants | $4H\sqrt{T_\tau}$ | $2\sqrt{ZH}$ |

**Proof of Corollary 10.3.** Theorems 7.6 and 9.2 give the strict
subtransition two-dimensional endpoint and its attainment in every
variant. Theorems 10.1–10.2 give the other entries and the empty
case. Each nonempty class has the displayed attaining model, and
the same model satisfies every larger tolerance. The lower bounds
exclude every smaller tolerance. $\square$

**Proposition 10.4 (Limits of the implicit scalar parameters).** With
$0<\tau<1$ and the root/contact parameters defined in §7,

$$
\begin{array}{c|cccc}
&T_\tau&\lambda_{T_\tau}&x_\tau&e_2^{\rm aff}(Z)\\ \hline
\tau\downarrow0&1/16&0&1/2&1/2\\
\tau\uparrow1&1&-\infty&1&2/3
\end{array}
$$

These are parameter limits, not assertions adding support-degenerate
source states.

**Proof of Proposition 10.4.** As $\tau\uparrow1$, the bounds

$$
\tau<T_\tau<\frac{(1+\tau)^2}{4},\qquad
0<T_\tau-\tau<\frac{(1-\tau)^2}{4}
$$

give $T_\tau\to1$ and $T_\tau-\tau\to0$. Thus
$\lambda_{T_\tau}=\frac12\log((T_\tau-\tau)/T_\tau)\to-\infty$.
The interval $(1+\tau)/2<x_\tau<1$ gives $x_\tau\to1$.
Solving the parameter relation gives

$$
Z=\frac{2\tau}{1+2\tau},\qquad
H=\frac1{2(1+2\tau)}.
$$

The capacity formula therefore tends to $2/3$, the value already
attained at the transition by the separate zero-readout witnesses.
A finite limiting exponential parameter is not required there.

As $\tau\downarrow0$, fix any $T>0$. For sufficiently small $\tau$,
$T>\tau$, and $v_T,f_T$ converge uniformly on $[0,1]$ to
$\sqrt T$. For $v_T$ this follows by rationalizing its difference
from $\sqrt T$; for $f_T$ it follows from $\lambda_T\to0$ and
$0\le x\le1$. Consequently

$$
\Phi_\tau(T)\longrightarrow
\max_{[0,1]}s-2\sqrt T=\frac12-2\sqrt T.
$$

Choose any fixed $0<T_-<1/16<T_+$. The limiting signs are positive
at $T_-$ and negative at $T_+$, so the strictly decreasing root
characterization puts $T_-<T_\tau<T_+$ for sufficiently small
$\tau$. Letting the two brackets approach $1/16$ gives
$T_\tau\to1/16$. The logarithm defining $\lambda_{T_\tau}$
then tends to zero, and $4H\sqrt{T_\tau}\to1/2$.

At these root parameters, $g_{T_\tau}$ converges uniformly to
$s-1/2$. This limit has its unique maximum zero at $1/2$.
On the compact complement of any neighborhood of $1/2$ its
maximum is strictly negative. Uniform convergence and
$\max g_{T_\tau}=0$ force $x_\tau$ into that neighborhood
eventually, proving $x_\tau\to1/2$.

All compactness here concerns explicit scalar functions on a
fixed interval. It imposes no compactness on competing latent
images. The limits $k\to0,H$ used in the scalar problem do not
add those points to $\mathcal M$. Similarly $Z=0$ loses the
positive middle reference, and $Z=1$ leaves no open height
interval; neither is included by this parameter calculation.
$\square$

## 11. Result map, published dependencies and remaining boundaries

The source-specific results can be located as follows. Every entry is
under the arbitrary fixed preparation and original ten-output Euclidean
contract of §§1–2.

| Result | Declarations | Mathematical role |
|---|---|---|
| Actual source, signed commands and fixed preparation rotations | 1.1–1.5 | Full $(0,H)\times\mathbb T^2$ domain, finite reachability and Gram $4I_2\oplus I_2$ |
| Bounded affine observables and worst-$\beta$ projection | 3.1–3.5 | Inherited erasure with offsets; hidden unbounded coordinates remain allowed |
| Actual-hull useful-readout split | 4.2 | Rank at most one gives $R_0$; rank two gives bounded affine coordinates |
| Character pair, center, commutant and modulus | 5.1–5.3 | Abstract characters first; ordinary exponential modulus derived from boundedness and lawful triples |
| Discontinuous phase boundary | 5.4 | Exact updates do not force continuity of the unit phase |
| Every-competitor radial domination | 6.1–6.4 | Finite character averages and original-metric comparison; all radial witnesses are legal |
| Endpoint-log corridor and unique scalar root | 7.1–7.4 | Normalization $16H^2$, maximal endpoint-allowed exponential and global feasibility |
| Unique interior contact and radial amplitude | 7.5–7.6 | Tangency system, exact $e_2^{\rm aff}$, strict floor/baseline inequalities and escaping-parameter coverage |
| Attaining actual annulus | 8.1–8.2 | Exact image, fibers, height recovery, initialization, all real commands and interior error attainment |
| Simultaneous paths | 9.1–9.2 | Mixed native term, all-times guards, every truncation and finite concatenation; matching class inclusions |
| Small budgets and transition | 10.1–10.3 | Exact $e_0^{\rm aff},e_1^{\rm aff},e_2^{\rm aff}$, included tolerance endpoints and the empty guarded zero-dimensional class |
| Scalar limits | 10.4 | Limits within the positive-support family, without endpoint source extension |

The published suppliers and the extent of reuse are distinct from that
result map:

| Source | Supplied mathematics | Use in this volume |
|---|---|---|
| [F, §§1–3] | Native probability and phase law, arbitrary preparation, actual-ray reachability, original outputs and simultaneous-path formula | Reconstructed in §§1 and 9; these are the unchanged source interfaces |
| [F, Proposition 7.13] | Necessary full-open error floor | Prior floor credit; §3 derives the needed bound through the sharper bounded-observable interface |
| [F, §10] | Finite affine factors and the distinction between arbitrary factors and bounded common-phase behavior | Scope boundary: arbitrary factor coordinates cannot all be declared $\beta$-independent; its field-automorphism constructions are not premises here |
| [O, §§3–4] | Bounded affine observable erasure and exact worst-$\beta$ decomposition | Reused with full proofs in §3, for precisely bounded affine observables |
| [O, §§6, 8 and 11] | All-finite nonattainment below the transition, equality above it, dimension-zero baseline, a positive gap at every fixed dimension and the dimension limit | Prior results and context, not discoveries claimed here; the exact two-dimensional endpoint is established directly by §§4–8 |
| [O, §9 and §11.7] | Direct simultaneous-path integration and full all-times guard interface | Reconstructed in §9 and applied to the annulus and height witnesses |

Relative to those manuscripts, the substantive addition is the exhaustive
useful-readout reduction at budget two, its exact radial-exponential
minimax, the unique scalar root and radial profile, and the matching
annulus with the same optimum in all four contracts. The rank argument
also determines the one-coordinate baseline below the transition. The
floor, bounded-observable erasure, dimension-zero baseline, transition and
existence of a fixed-dimension positive gap already have the credited
suppliers above. The exact formula does not depend on treating their
nonattainment or gap results as a substitute for the new minimax proof.

The general ingredients used here are finite-dimensional affine
homogenization and linear algebra, characters of abstract abelian groups,
divisibility, finite geometric sums, the bounded additive-function
argument, orthogonal projection, elementary convexity and concavity, and
one-variable calculus. The needed forms are proved directly. No
topological classification of discontinuous characters or external
translation-space theorem is a premise. No worldwide-priority or
exhaustive-literature claim is made.

The following boundaries are part of the conclusions:

- The source is the actual current-ray domain with $0<Z<1$ and
  $0<k<H$. Retained lifts, arbitrary history encoders, vanished
  support, a reduced command menu or a finite-horizon replacement
  specify different problems. Every executed history in the
  assertions is individually finite.
- Stored dimension, actual affine-hull dimension and useful-readout
  rank have separate roles. The radial reduction concerns optimal
  error; it neither classifies every finite affine factor nor proves
  that all unbounded hidden coordinates lose $\beta$. The radial
  uniqueness theorem does not classify all optimizing realizations.
- All updates and initialization are exact over real coordinates.
  No common matrix across varying models, coefficient bound,
  precision bound, regularity of arbitrary encoders, or compactness
  of their latent images is assumed. The exact height guard of the
  annulus is a mathematical function on its actual image.
- The witness is noninjective and its decoded $02$ pair is zero,
  although every actual native ray has positive $02$ radius. Thus
  decoded vectors need not be native physical outputs. Requiring
  physical outputs or injection would remove this witness and
  would require a separate upper-bound analysis.
- General positive fixed dimensions beyond the solved budgets
  $0,1,2$ below the transition retain unresolved exact capacities
  and attainment questions. The prior all-finite and dimension-limit
  results do not settle them, and the two-dimensional formula gives
  no general sharp dimension rate or efficient algorithm.
- The original finite-hidden-$N$ attainment alternative remains
  unresolved. No bridge identifying its objective or admissible
  realizations with this affine-readout problem is supplied.
- Exact-real persistence does not give finite-bit storage, noisy
  robustness, conditioning, measurement acquisition, physical
  implementation, training, or empirical machine-learning claims.
  These handwritten proofs are not kernel-verified declarations.

## 11.99 追加锚

## 12. The unrestricted three-coordinate question and its inherited interface

Sections 12–20 establish the dimension-three plateau
$e_3^{\rm aff}(Z)=e_2^{\rm aff}(Z)$ on the same full native domain.
The additional coordinate may be unbounded and may carry a nontrivial
hidden phase action. The conclusion is domination in uniform readout
error by a two-coordinate radial model, not a classification of all
three-coordinate encoders. The proofs are ordinary handwritten
mathematics, unverified by Lean.

The source, preparation, and metric are exactly those of §§1–2. In
particular, $0<Z<1$, $r=1-Z$, $H=r/2$, the fixed preparation is
arbitrary, and every point of
$\mathcal M=(0,H)\times\mathbb T^2$ is an actual current ray.
The commands remain

$$
P_s(k,\alpha,\beta)=(k+s,\alpha,\beta),\qquad
0<k,k+s<H,
$$

$$
Q_t(k,\alpha,\beta)=
\left(k,\alpha+t/2,\beta+(1/2-k/r)t\right),\qquad
(k,\alpha,\beta)\in\mathcal M,
$$

for every signed real $s,t$. The first formula specifies the full
partial domain of $P_s$; $Q_t$ has full domain. No phase control,
height selector, endpoint ray, or history variable is added.

**Definition 12.1 (Budget three and the radial comparison family).**
Let $\mathfrak F_{\le3}^{\rm aff}(Z)$ consist of the models of
Definition 2.1 with stored dimension $m\in\{0,1,2,3\}$. Thus

$$
e_3^{\rm aff}(Z)=
\inf_{(E,q)\in\mathfrak F_{\le3}^{\rm aff}(Z)}
\sup_{x\in\mathcal M}\|q(x)-y(x)\|_2.
$$

There is one fixed affine ten-output decoder and one state-independent
affine map for each original command, including both update offsets.
Encoders may be irregular, nonmeasurable, unbounded, and noninjective.
No ambient inverse, ambient composition law, common affine center,
or regularity in a command parameter is required. Infinite errors are
included. Guard recovery and prescribed paths retain Definition 2.2.

For $C\ge0$ and $\gamma\in\mathbb R$ write

$$
\mathcal R_Z(C,\gamma)=
\sup_{0<k<H}\left\{4(Ce^{\gamma k}-A(k))^2+4Zk\right\},
\qquad A(k)=2\sqrt{k(H-k)}.
$$

Here $C=0$ means the zero model, so
$\mathcal R_Z(0,\gamma)=R_0^2$ independently of $\gamma$.
Every positive $C$ and finite $\gamma$ gives the actual model of
Theorem 6.4, with encoder $Ce^{\gamma k}U(\alpha)$ and decoder
$D(E,0)$. Thus these comparisons refer to lawful models in the
original metric, not just scalar lower bounds.

**Proposition 12.2 (The inherited useful-observable interface).**
For every finite-error competitor of Definition 12.1 there is a bounded,
$\beta$-independent affine two-output observable $a$ of its encoder
such that

$$
\operatorname{err}(E,q)^2\ge
\sup_{0<k<H,\ \alpha\in\mathbb T}
\left\{4\|a(k,\alpha)-A(k)U(\alpha)\|_2^2+4Zk\right\}.
\tag{12.1}
$$

Replacing the decoder by $D(a,0)$ cannot increase its error.
Furthermore,

$$
(e_2^{\rm aff}(Z))^2=\inf_{C\ge0,\ \gamma\in\mathbb R}
\mathcal R_Z(C,\gamma).
\tag{12.2}
$$

**Proof of Proposition 12.2.** Theorem 3.4 applies to the bounded
components of the decoder, since finite error and bounded $y$ imply
bounded $q$. Proposition 3.5 then gives the orthogonal decomposition
$q=D(a,b)+w$ and the exact worst-$\beta$ expression

$$
\|w\|^2+4\|a-A(k)U(\alpha)\|^2+(\|b\|+B(k))^2,
\qquad B(k)^2=4Zk.
$$

Dropping the indicated nonnegative terms gives (12.1) and the decoder
domination. This uses $D^{\mathsf T}D=4I_2\oplus I_2$ from Lemma
1.5, including the fixed preparation rotations. Equation (12.2), and
the stronger assertion that each budget-two competitor is dominated
by an individual radial choice, are Theorem 6.4. These are reused
results. Neither their application nor boundedness of $a$ bounds an
unread coordinate of $E$. $\square$

The bounded-observable erasure and worst-$\beta$ reduction are the
credited results of [O, §§3–4], presented in §3 of this volume.
The exact two-coordinate reduction, scalar endpoint, and matching
witnesses are §§4–10 of this volume. The new lower-bound obligation is
therefore to control the extra hidden direction at budget three.

## 13. Actual affine hulls and propagation into every partial domain

**Lemma 13.1 (Restriction to the actual affine hull).** Let
$\mathscr H=\operatorname{aff}E(\mathcal M)$ and
$d=\dim\mathscr H\le m$. One may replace the ambient stored space
by affine coordinates on $\mathscr H$, retaining the same source,
decoder values, and all lawful affine identities. This does not require
a probability command to preserve $\mathscr H$ away from its lawful
encoded states.

**Proof of Lemma 13.1.** Choose an affine retraction
$\mathcal P:\mathbb R^m\to\mathscr H$ that is the identity on
$\mathscr H$. Such a retraction is obtained by choosing an origin in
$\mathscr H$, extending a basis of its direction space to the ambient
space, and projecting along the added directions. Replace an ambient
update $\mathcal U$ by
$\mathcal P\circ\mathcal U|_{\mathscr H}$. On a lawful encoded
state the original update equals another actual encoding, so the
retraction changes nothing there. Restrict the affine decoder to
$\mathscr H$ and choose affine coordinates on this hull. These maps
include all their affine offsets. Empty domains still impose no
identity. In the resulting $\mathbb R^d$, the encoded image has full
affine hull. $\square$

Use these actual-hull coordinates from now on, and write the useful
observable as

$$
a(x)=a_0+L E(x),\qquad L:\mathbb R^d\to\mathbb R^2.
$$

The rank here is the rank of this useful readout on the direction
space of the actual hull. It is neither the stored dimension nor the
rank of the entire ten-output decoder.

**Proposition 13.2 (The deficient-rank and two-dimensional branches).**
If $\operatorname{rank}L\le1$, then
$\operatorname{err}(E,q)\ge R_0$. If
$\operatorname{rank}L=2$ and $d=2$, the competitor is dominated by
a budget-two model with bounded encoder $a$. These branches cover all
$d\le2$.

**Proof of Proposition 13.2.** In the first case the image of $a$
lies in an affine line or point. Choose a unit normal $\nu$ and a
constant $c_0$ such that $\nu\cdot a=c_0$. For every interior $k$,

$$
\sup_\alpha\|a(k,\alpha)-A(k)U(\alpha)\|
\ge\sup_\alpha|c_0-A(k)\nu\cdot U(\alpha)|
=|c_0|+A(k)\ge A(k).
$$

Equation (12.1) gives the lower bound
$\sup_k\{4A(k)^2+4Zk\}=R_0^2$ in squared error.
The radial choice $C=0$ realizes this comparison.

In the second case the affine map $z\mapsto a_0+Lz$ is an
isomorphism on $\mathbb R^2$. Conjugating each hull update by it
makes $a$ an exact affine encoder on every original lawful domain.
Theorem 3.4 gives its $\beta$-independence, finite error gives its
boundedness, and Proposition 12.2 supplies the decoder $D(a,0)$ of
no greater error. Theorem 6.4 applies. Rank cannot exceed $d$, so
there is no other case with $d\le2$. $\square$

**Lemma 13.3 (Nonzero beta fibers propagate and give a lawful quotient).**
Suppose $d=3$ and $\operatorname{rank}L=2$, and put
$N=\ker L$, a real line. If the encoder is not $\beta$-independent,
then every nonempty-domain update preserves $N$ in its linear part.
The affine quotient $\mathbb R^3/N$, identified with $\mathbb R^2$
by $a$, is consequently a lawful budget-two encoder with no greater
readout error. This is a literal-class quotient; guard recovery is
not a conclusion.

**Proof of Lemma 13.3.** The $\beta$-independence of $a$ implies
that every difference between encodings at the same $(k,\alpha)$
belongs to $N$. Failure of $\beta$-independence of $E$ gives an
actual nonzero difference

$$
v=E(k_*,\alpha_*,\beta_1)-E(k_*,\alpha_*,\beta_2)\in N.
$$

Write the hull probability update as $z\mapsto A_sz+b_s$.
For every $l\in(0,H)$, both original states admit the leg
$P_{l-k_*}$. Their transported difference is

$$
v_l=A_{l-k_*}v
=E(l,\alpha_*,\beta_1)-E(l,\alpha_*,\beta_2)\in N.
$$

The reverse leg is lawful at both transported states, and gives

$$
A_{k_*-l}v_l=v.
$$

Thus $v_l\ne0$ and spans $N$ at every interior height. This is an
identity on actual pairs of states, not an ambient inverse assertion.
Offsets cancel in differences but are retained in the affine maps.

For a fixed $s$ with $|s|<H$, the interval

$$
I_s=(\max\{0,-s\},\ \min\{H,H-s\})
$$

is nonempty. Choose $l\in I_s$ and use the nonzero pair just
constructed there. Its images under $P_s$ have the same height and
$\alpha$, so their useful readouts agree. Hence
$LA_s v_l=0$, and, since $v_l$ spans $N$, one has
$A_sN\subseteq N$. For a phase update
$z\mapsto C_tz+d_t$, the same pair at any interior $l$ has images
with the same height and $\alpha+t/2$. Thus $LC_tv_l=0$ and
$C_tN\subseteq N$ for every real $t$. The nonzero fiber has been
placed inside each command's own domain before it is used.

An affine map whose linear part preserves $N$ induces a fixed affine
map on the quotient: changing a representative by an element of $N$
changes its image by an element of $N$. Since $L$ is surjective,
$[z]\mapsto a_0+Lz$ is an affine isomorphism of that quotient with
$\mathbb R^2$. The encoder $a(k,\alpha)$ therefore has exact affine
updates for all nonempty original command domains. For $|s|\ge H$
the probability domain is empty and any affine quotient update may be
assigned. This supplies maps for every real command, with offsets.
The decoder $D(a,0)$ has no greater error by Proposition 12.2, so
Theorem 6.4 gives a radial comparison.

A quotient encoder may identify rays of different heights. None of
this reasoning says its fibers determine a probability guard. Its
only role is to supply the literal-class lower bound. $\square$

**Corollary 13.4 (Exhaustive remaining case).** Every budget-three
competitor either is already dominated by a radial budget-two model,
or has finite error, actual hull dimension three, useful rank two,
and a $\beta$-independent encoder.

**Proof of Corollary 13.4.** Infinite-error competitors are dominated
by the finite zero witness. Proposition 13.2 handles every deficient
useful rank and every actual hull of dimension at most two. In the
remaining dimension-three, rank-two case, either a nonzero beta-fiber
difference exists and Lemma 13.3 applies, or all such differences
vanish, which is exactly $\beta$-independence of $E$. $\square$

## 14. The full phase action and the bounded useful module

The next arguments apply to a $\beta$-independent encoder on its
actual affine hull of any dimension $d\le3$. They will be used for
the remaining case of Corollary 13.4. Write

$$
F(k,\alpha)=(1,E(k,\alpha))^{\mathsf T},\qquad
X=\operatorname{span}_{\mathbb R}\{F(k,\alpha):0<k<H,
\ \alpha\in\mathbb T\}.
$$

The full actual affine hull implies $\dim_{\mathbb R}X=d+1\le4$.
Let $\lambda_0$ be its first-coordinate covector, so
$\lambda_0F(k,\alpha)=1$. Homogenize the hull updates, including
offsets, as $T_s$ for probability commands and $S_t$ for phase
commands.

**Lemma 14.1 (An actual phase representation and a fixed covector).**
There is a representation $\delta\mapsto V_\delta$ of the abstract
circle $\mathbb T$ on $X$ satisfying

$$
V_\delta F(k,\alpha)=F(k,\alpha+\delta),\qquad
V_\delta V_\epsilon=V_{\delta+\epsilon},\qquad
V_0=I,\qquad V_\delta^{-1}=V_{-\delta}.
\tag{14.1}
$$

It obeys $\lambda_0V_\delta=\lambda_0$. The assertion is about a
covector; it does not assert a fixed vector with first coordinate one
or a common affine fixed point.

**Proof of Lemma 14.1.** For a real representative of $\delta$,
restrict $S_{2\delta}$ to $X$. The full-domain $Q_{2\delta}$ identity
and $\beta$-independence give the first equality in (14.1).
Changing that representative by $2\pi$ gives the same values on
every actual $F$, and therefore the same linear operator on their
span $X$. Products, zero, and inverses in (14.1) likewise agree on
all actual $F$, hence on $X$. The full-domain phase operators
preserve $X$ because they map these generators to generators. The
first coordinate of every generator is one, which also proves the
covector identity. None of these arguments applies an asserted
ambient law to unused directions. $\square$

**Lemma 14.2 (Only the useful observable module is bounded).** Let
$\ell_1,\ell_2\in X_{\mathbb C}^{\vee}$ be the homogeneous rows
of $a$, where $X_{\mathbb C}$ is the complexification of $X$. Let
$W$ be the complex span of $\lambda_0$ and all rows
$\ell_iV_\delta$. Then $W$ has a basis of common eigencovectors
for right multiplication by all $V_\delta$. Their eigenvalues are
abstract unitary characters of $\mathbb T$. There is at most one
nontrivial conjugate pair, and each member of that pair has
multiplicity one. Trivial-character rows may have different height
profiles.

**Proof of Lemma 14.2.** Each generating row is a bounded function
on actual states, since
$\ell_iV_\delta F(k,\alpha)=a_i(k,\alpha+\delta)$ and $a$ is
uniformly bounded. Every finite linear combination is also bounded.
On $W$ set

$$
\|\ell\|_{\rm obs}=
\sup_{0<k<H,\ \alpha\in\mathbb T}|\ell F(k,\alpha)|.
$$

It is a genuine norm: a row vanishing on all actual states vanishes
on their span $X_{\mathbb C}$. Right multiplication by $V_\delta$
is an invertible isometry, since it permutes the phase circle at
every height. These maps commute. The finite-dimensional argument
of Lemma 3.2 now applies to this normed space: eigenvalues have
modulus one, nontrivial Jordan chains would have unbounded iterates,
and induction over invariant eigenspaces simultaneously diagonalizes
the entire commuting family. This argument uses no norm on $E$.

For a common eigenrow $\ell\ne0$, write
$\ell V_\delta=\chi(\delta)\ell$. Equation (14.1) proves that
$\chi$ is a group homomorphism into the unit circle, and

$$
\ell F(k,\alpha)=\chi(\alpha)\,\ell F(k,0).
\tag{14.2}
$$

The coefficient at a particular height is allowed to vanish. Two
independent eigenrows with the same character would represent two
independent height profiles; they are not identified by evaluation
at one height.

The space $W$ is closed under conjugation, because its original rows
and phase operators are real. The covector $\lambda_0$ gives a
nonzero trivial-character row. Any real unitary character is trivial:
for every circle element $\delta$ choose a half-element $\eta$;
then $\chi(\delta)=\chi(\eta)^2=1$ if its values lie in
$\{1,-1\}$. Thus each nontrivial character is distinct from its
conjugate and consumes at least two dimensions together with it.
Since $\dim_{\mathbb C}W\le d+1\le4$, there is at most one
such pair. A multiplicity of two for one member would force two for
its conjugate and, together with $\lambda_0$, at least five
dimensions. Each member therefore has multiplicity one. The
trivial eigenspace need not have dimension one. $\square$

Identify the useful output plane with $\mathbb C$ and put
$z(k,\alpha)=a_1(k,\alpha)+i a_2(k,\alpha)$ and
$\xi(\alpha)=e^{i\alpha}$. If $W$ has a nontrivial pair
$\chi,\overline\chi$, Lemma 14.2 gives

$$
z(k,\alpha)=c(k)+u(k)\chi(\alpha)
                  +v(k)\overline{\chi(\alpha)}.
\tag{14.3}
$$

The term $c(k)$ may depend on height. No common affine center is
implicit in this formula.

**Proposition 14.3 (Unmatched abstract characters give the baseline).**
If $a$ is phase-independent, or if the nontrivial pair in (14.3)
is neither $\xi,\xi^{-1}$, then
$\operatorname{err}(E,q)\ge R_0$.

**Proof of Proposition 14.3.** At fixed $k$, a phase-independent
value has worst distance from the radius-$A(k)$ circle at least
$A(k)$. In the other case the characters

$$
\xi^{-1},\qquad \chi\xi^{-1},\qquad
\overline\chi\xi^{-1}
$$

are all nontrivial. Lemma 6.1 applies to this finite list on the
abstract circle. Explicitly, choose one circle element for each
listed character on which it differs from one, and average over
all finite sums of integer multiples of those elements with
coefficients $0,\ldots,N-1$. The average of each character is a
product of finite geometric averages; one factor tends to zero
and the others have modulus at most one. Consequently, at this
fixed height, the finite average of $z(k,\alpha)\xi(\alpha)^{-1}$
tends to zero. Since

$$
|z-A(k)\xi|^2=|z|^2+A(k)^2
       -2A(k)\operatorname{Re}(z\xi^{-1}),
$$

and $|z|^2\ge0$, the supremum of the squared useful error is at
least $A(k)^2$. Equation (12.1) gives $R_0^2$ after taking the
height supremum. These are finite averages of actual phase states;
no Haar integral, measurability, continuity, or density of a chosen
phase sequence is required. This exhausts every nonnative pair in
the bounded useful module. $\square$

## 15. Complete primary blocks, the invariant covector, and hidden phases

The useful module is not the whole hidden state. To isolate a native
coefficient under a partial probability command, a projector on the
full homogeneous hull is needed, including any nonsemisimple or
nonunitary hidden action.

**Lemma 15.1 (Primary projectors are finite combinations of phase maps).**
For the representation (14.1), there are finitely many distinct
abstract characters $\lambda:\mathbb T\to\mathbb C^\times$
and a direct sum

$$
X_{\mathbb C}=\bigoplus_{\lambda\in\Lambda}X_\lambda
$$

of invariant primary subspaces. On $X_\lambda$ every $V_\delta$
has sole eigenvalue $\lambda(\delta)$. The projector
$\Pi_\lambda$ onto $X_\lambda$ along the other primary subspaces
has a finite expression

$$
\Pi_\lambda=\sum_{j=1}^{J_\lambda}
 c_{\lambda,j}V_{\delta_{\lambda,j}},
\qquad c_{\lambda,j}\in\mathbb C,\quad
\delta_{\lambda,j}\in\mathbb T.
\tag{15.1}
$$

Neither unitarity nor diagonalizability of the representation on
$X_{\mathbb C}$ is assumed.

**Proof of Lemma 15.1.** First simultaneously triangularize the
commuting complex family. A common eigenvector exists by a finite
dimension descent: in a nonzero common invariant subspace, if every
operator is scalar choose any nonzero vector; otherwise take a
nonzero proper eigenspace of a nonscalar operator. All other
operators preserve it by commutation. Repeat until a common
eigenline is obtained. Induction on the quotient by that line
produces a common invariant flag and a simultaneous triangular
basis. The diagonal functions $\lambda_j(\delta)$ are nonzero,
and the representation law makes each a character. There are
only finitely many distinct such functions; call their set
$\Lambda$.

Choose finitely many circle elements $\delta_1,\ldots,\delta_b$
so that their evaluations distinguish each pair of distinct
characters in $\Lambda$. For each selected $V_{\delta_h}$,
factor its characteristic polynomial into powers of distinct
linear factors. Bezout identities for those relatively prime
powers, together with Cayley–Hamilton, give polynomial projectors
onto its generalized eigenspaces: for eigenvalue $\omega$, choose
a polynomial congruent to one modulo the factor for $\omega$
and to zero modulo each other factor. Evaluating it at
$V_{\delta_h}$ gives the required projector. All these projectors
commute, since the phase operators commute.

For $\lambda\in\Lambda$, multiply the selected projectors for
the eigenvalues $\lambda(\delta_h)$. The resulting idempotent
$\Pi_\lambda$ selects their joint generalized eigenspace. To see
that these are exactly all nonzero joint pieces, use the common
triangular flag. The diagonal of a joint projector is one at a
flag position precisely when its tuple of selected eigenvalues
matches that position's character, and zero otherwise. An
idempotent has rank equal to the number of ones on this diagonal.
Every nonzero joint piece therefore matches some character in
$\Lambda$, and the selected tuples distinguish those characters.
The projectors are pairwise disjoint and sum to the identity.
Their images inherit the common flag, with precisely the diagonal
positions belonging to $\lambda$, so each $V_\delta$ has sole
eigenvalue $\lambda(\delta)$ on $X_\lambda$.

Finally the complex linear span of all $V_\delta$ is an algebra:
it contains $I=V_0$, and a product $V_\delta V_\epsilon$ equals
$V_{\delta+\epsilon}$. Each polynomial projector and each finite
product of such projectors belongs to that algebra. Expansion is
therefore a finite linear combination as in (15.1). If there is
only one character, the projector is simply $I$. This proof
selects complete generalized blocks, including any Jordan parts,
and does not use an average over infinitely many phases. $\square$

**Lemma 15.2 (Native blocks have multiplicity one in the full hull).**
The set $\Lambda$ contains the trivial character, with
$\dim X_1\ge1$. If a native pair $\xi,\xi^{-1}$ is used by the
bounded useful readout, then

$$
\dim_{\mathbb C}X_\xi=
\dim_{\mathbb C}X_{\xi^{-1}}=1.
\tag{15.2}
$$

On these lines $V_\delta$ acts as multiplication by
$\xi(\delta)$ and $\xi(\delta)^{-1}$ respectively, without a
Jordan part. Their vectors have homogeneous coordinate zero.

**Proof of Lemma 15.2.** For a nontrivial $\lambda$, choose
$\delta$ with $\lambda(\delta)\ne1$. On $X_\lambda$, the
operator $V_\delta-I$ is invertible because its only eigenvalue
is $\lambda(\delta)-1$. The invariant covector satisfies
$\lambda_0(V_\delta-I)=0$, so it annihilates $X_\lambda$.
If there were no trivial block, it would annihilate all of
$X_{\mathbb C}$, contrary to $\lambda_0F=1$. This proves the
trivial-block assertion using a covector, without producing a
fixed vector.

A nonzero native eigencovector $\ell$ in $W$ obeys
$\ell V_\delta=\xi(\delta)\ell$. For $\lambda\ne\xi$,
choose $\delta$ with $\lambda(\delta)\ne\xi(\delta)$.
The operator $V_\delta-\xi(\delta)I$ is invertible on
$X_\lambda$, so $\ell$ annihilates that block. It cannot
annihilate every block. Hence $X_\xi\ne0$. Reality of the
representation gives
$\overline{X_\xi}=X_{\xi^{-1}}$ with equal dimension. If that
dimension were at least two, the two distinct conjugate blocks
would consume at least four dimensions, and the trivial block
would consume a fifth. This contradicts $\dim X_{\mathbb C}\le4$.
They are therefore lines, proving (15.2). The first part of the
proof also shows that $\lambda_0$ annihilates both lines.
$\square$

In this native case the real residual module has dimension at most
two and contains a trivial composition factor. If it has two
dimensions, it can contain a separate nontrivial real character,
or two trivial factors with a nontrivial unipotent extension. A
real character takes positive values, since
$\lambda(\delta)=\lambda(\delta/2)^2>0$. A second nonreal pair,
or an extra generalized dimension in either native block, would
exceed the dimension budget. The residual action need not be
trivial.

For clarity, this count does not hide a boundedness assertion.
Every eigenrow in $W$ is unitary and annihilates full primary
blocks with a different character by the invertibility argument
above. Moreover $W$ is stable under each $\Pi_\lambda$, since
(15.1) is a finite combination of phase maps. In the native case,
put

$$
\Pi_{\rm res}=I-\Pi_\xi-\Pi_{\xi^{-1}}.
$$

For the complex readout row $\ell_1+i\ell_2$, its product with
$\Pi_{\rm res}$ is a row in $W$ whose native components vanish.
Lemma 14.2 makes it a trivial-character row. Its evaluation is
therefore independent of $\alpha$, but may depend on $k$.
Nonunitary hidden primary blocks and hidden Jordan directions
have not been declared bounded or absent.

**Example 15.3 (A lawful positive hidden phase character).** There
are full-hull three-coordinate, finite-error encoders whose third
coordinate has a nontrivial positive phase character.

**Proof of Example 15.3.** Choose a nonzero rational-linear map
$\ell:\mathbb R\to\mathbb R$ with $\ell(2\pi)=0$. For example,
extend $2\pi$ and a rationally independent real number to a
rational vector-space basis, assign zero to $2\pi$, one to that
other number, and zero to the other basis elements. It descends
to an additive map $h:\mathbb T\to\mathbb R$. Choose a circle
element $\alpha_0$ with $h(\alpha_0)>0$, changing sign if
necessary. Then $h(n\alpha_0)=nh(\alpha_0)$ and
$e^{h(n\alpha_0)}\to\infty$.

For fixed $C>0$, set

$$
E_+(k,\alpha,\beta)=
(C\cos\alpha,\ C\sin\alpha,\ e^{h(\alpha)}).
$$

Use the identity update for every $P_s$, and for every real $t$
use

$$
(z_1,z_2,z_3)\longmapsto
\bigl(R_{t/2}(z_1,z_2),\ e^{h(t/2)}z_3\bigr)
$$

for $Q_t$, with circle arguments in $h$. Direct substitution gives
the exact source identities on all original domains. The fixed
decoder is $D((z_1,z_2),0)$. Its error is finite, since its first
pair has fixed norm $C$ and $y$ is bounded. The affine hull is
three-dimensional: any affine dependence with a nonzero
coefficient of $e^{h(\alpha)}$ would bound that unbounded function
by a combination of $1,\cos\alpha,\sin\alpha$; with that
coefficient zero, those three functions are linearly independent.
The homogeneous phase representation has the trivial factor, the
native conjugate pair, and the positive character $e^h$.
$\square$

**Example 15.4 (A lawful additive shear without an affine center).**
Using the same $h$ and $C$, the encoder

$$
E_{\rm sh}(k,\alpha,\beta)=
(C\cos\alpha,\ C\sin\alpha,\ h(\alpha))
$$

has full affine hull and finite error with the same decoder, but
its phase action has no common affine fixed point.

**Proof of Example 15.4.** The probability maps are again the
identity, and the exact phase maps are

$$
(z_1,z_2,z_3)\longmapsto
\bigl(R_{t/2}(z_1,z_2),\ z_3+h(t/2)\bigr).
$$

Additivity proves all lawful identities. Unboundedness of $h$
and linear independence of $1,\cos,\sin$ prove the full hull as
in Example 15.3. The decoder remains bounded. Choose a phase
increment $\delta$ with $h(\delta)\ne0$. Its map translates the
third coordinate by a nonzero constant, and therefore fixes no
ambient point. On the homogeneous coordinates $(1,z_3)$ its block
is

$$
\begin{pmatrix}1&0\\h(\delta)&1\end{pmatrix}.
$$

It has the invariant first-coordinate covector but no vector with
first coordinate one fixed by this increment. Thus the full phase
family has no normalized fixed vector or common affine center.
$\square$

These examples disprove phase-triviality of every extra hidden
coordinate and the inference from a fixed homogeneous covector to
an affine center. They do not disprove the capacity plateau: their
useful readout is already the constant-radius radial model. They
ignore height, so no guard-recovery assertion is made for them.
Both examples satisfy the unrestricted literal contract. The basis
choice only exhibits permitted irregular encoders and is not a
premise of the lower-bound proof.

## 16. A native projector on each lawful orbit and its height modulus

Assume now that the bounded useful readout uses the native pair.
The lines and projectors in Lemmas 15.1–15.2 are defined on the
whole actual homogeneous hull, while a probability identity is
still required only on its original partial domain.

**Lemma 16.1 (Projector intertwining on an individual actual orbit).**
Set

$$
u_\xi(k)=\Pi_\xi F(k,0).
$$

For each lawful pair $0<k,k+s<H$,

$$
T_s\Pi_\xi F(k,0)=\Pi_\xi T_sF(k,0),\qquad
u_\xi(k+s)=T_su_\xi(k).
\tag{16.1}
$$

Also

$$
\Pi_\xi F(k,\alpha)=\xi(\alpha)u_\xi(k).
\tag{16.2}
$$

The vector $u_\xi(k)$ is a finite complex linear combination of
actual homogeneous states at that single height. No spanning
assumption about a probability-command domain is needed.

**Proof of Lemma 16.1.** For each circle element $\delta$ and
this particular lawful starting height,

$$
T_sV_\delta F(k,0)=T_sF(k,\delta)=F(k+s,\delta)
=V_\delta F(k+s,0)=V_\delta T_sF(k,0).
\tag{16.3}
$$

Here the native commands can change $\beta$ differently in the
two orders. Their encoded values agree because this encoder is
$\beta$-independent. Equation (16.3) is asserted on the selected
actual state, not as an operator commutation law on all of $X$.

Insert the finite expression (15.1) for $\Pi_\xi$ into (16.3)
and use linearity. This proves (16.1). The same expression gives

$$
u_\xi(k)=\sum_j c_{\xi,j}F(k,\delta_{\xi,j}),
$$

so the projected vector lies in the span of that actual phase
orbit. Projectors commute with all phase operators, and the
native block is a line on which $V_\alpha$ acts by
$\xi(\alpha)$. Applying this to $F(k,\alpha)=V_\alpha F(k,0)$
proves (16.2). $\square$

**Lemma 16.2 (Nonvanishing and the partial multiplier law).**
The vector $u_\xi(k)$ is nonzero at every interior height. For
every $|s|<H$ there is a single $m_s\in\mathbb C^\times$ such
that

$$
T_s|_{X_\xi}=m_sI,\qquad
u_\xi(k+s)=m_su_\xi(k)\quad(k\in I_s).
\tag{16.4}
$$

These scalars satisfy

$$
m_0=1,\qquad m_{-s}=m_s^{-1},\qquad
m_{s+t}=m_tm_s
\quad\text{if }|s|,|t|,|s+t|<H.
\tag{16.5}
$$

These are derived local laws. There is no asserted relation for
probability maps with empty source domain.

**Proof of Lemma 16.2.** If $u_\xi(k)$ vanished at every height,
(16.2) would make $\Pi_\xi$ vanish on every actual state, and
therefore on their span. This contradicts $X_\xi\ne0$. Choose
a height $k_*$ where it is nonzero. For any other interior $l$,
the leg $P_{k_*-l}$ is lawful at height $l$. If $u_\xi(l)=0$,
(16.1) would imply
$u_\xi(k_*)=T_{k_*-l}u_\xi(l)=0$, a contradiction. This proves
nonvanishing everywhere, without a regularity assertion at any
height.

Fix $|s|<H$ and choose one $k\in I_s$. The nonzero vector
$u_\xi(k)$ spans $X_\xi$, and (16.1) takes it to the nonzero
vector $u_\xi(k+s)$ in the same line. Thus the one fixed linear
map $T_s$ preserves this line and acts on it by a nonzero scalar
$m_s$. The scalar is independent of the lawful starting height,
and (16.1) gives (16.4) at every such height. Zero and reverse
lawful legs give $m_0=1$ and $m_{-s}m_s=1$.

If $|s|,|t|,|s+t|<H$, the spread of the three real numbers
$0,s,s+t$ is
$\max\{|s|,|t|,|s+t|\}<H$. Choose a translation of these three
numbers placing all of them in $(0,H)$. From the resulting
starting height $k$, the two successive legs and the single
summed leg are lawful and yield

$$
m_{s+t}u_\xi(k)=u_\xi(k+s+t)=m_tm_su_\xi(k).
$$

Nonvanishing gives the local product law. No partial domain was
assumed to span $X$ or any residual hidden block. $\square$

The homogeneous coordinate vanishes on $X_\xi$ by Lemma 15.2,
so the vector being multiplied in (16.4) is a genuine direction
vector. Nevertheless both probability and phase offsets are
present in $T_s$ and $V_\delta$. The finite projector identity,
not an assumption that those offsets vanish, prevents an
additional inhomogeneous term in the native coefficient on
lawful states. It also prevents hidden blocks from supplying such
a term there. It imposes no general off-image block decomposition
on $T_s$. The fixed decoder offset belongs to the trivial
observable part.

**Proposition 16.3 (A bounded native coefficient has exponential modulus).**
There are fixed $p_+,p_-\in\mathbb C$, a function
$c:(0,H)\to\mathbb C$, and a nowhere-zero function
$f:(0,H)\to\mathbb C$ such that

$$
z(k,\alpha)=c(k)+p_+f(k)e^{i\alpha}
                    +p_-\overline{f(k)}e^{-i\alpha}.
\tag{16.6}
$$

In a used native-pair case at least one of $p_+,p_-$ is nonzero.
Normalize $f(H/2)=1$. Then for some finite real $\gamma$,

$$
f(k+s)=m_sf(k)\quad(k\in I_s),\qquad
|m_s|=e^{\gamma s}\quad(|s|<H),\qquad
|f(k)|=e^{\gamma(k-H/2)}.
\tag{16.7}
$$

Only the modulus is asserted to be an ordinary exponential.

**Proof of Proposition 16.3.** Choose the native basis vector
$v_*=u_\xi(H/2)\ne0$ and write $u_\xi(k)=f(k)v_*$. This gives
the normalization, nonvanishing, and the first identity in (16.7).
Reality and uniqueness of the primary decomposition imply
$\overline{\Pi_\xi}=\Pi_{\xi^{-1}}$. Since $F$ is real, its
conjugate primary component is therefore
$\overline{f(k)}\,\overline{v_*}$ at phase zero. Apply the fixed
complex row $\ell=\ell_1+i\ell_2$ to these two components and
set $p_+=\ell v_*$, $p_-=\ell\overline{v_*}$. The residual
row $\ell\Pi_{\rm res}$ is phase-invariant by the argument
after Lemma 15.2. This gives (16.6), with
$c(k)=\ell\Pi_{\rm res}F(k,0)$. If both fixed coefficients
vanish, $z$ and both of its real components are phase-independent;
that is the baseline case of Proposition 14.3, not a used native
pair.

It remains to justify a bound on $f$, rather than on the hidden
state. Put $M=\sup_{k,\alpha}|z(k,\alpha)|<\infty$, as supplied
by finite readout error. Let $\omega=e^{2\pi i/3}$. Evaluating
(16.6) at the three actual phases $2\pi j/3$ gives the finite
coefficient identities

$$
p_+f(k)=\frac13\sum_{j=0}^2
 z(k,2\pi j/3)\omega^{-j},\qquad
p_-\overline{f(k)}=\frac13\sum_{j=0}^2
 z(k,2\pi j/3)\omega^j.
\tag{16.8}
$$

They follow from $1+\omega+\omega^2=0$. Both right sides have
modulus at most $M$. Since at least one fixed coefficient is
nonzero, there is a finite $K\ge1$ with $|f(k)|\le K$ for all
interior $k$. No latent norm or hidden residual coordinate has
been bounded.

For $|s|<H/2$, use (16.4) at the reference height $H/2$ to get
$|m_s|\le K$. Use $-s$ and (16.5) to get the reciprocal bound.
Thus

$$
K^{-1}\le|m_s|\le K\quad(|s|<H/2).
$$

The function $b(s)=\log|m_s|$ is locally additive on $(-H,H)$
by (16.5), and $|b(s)|\le\log K$ near zero. This is the
bounded-additivity mechanism already used in Lemma 5.3. Explicitly,
for a positive integer $N$ and $|s|<H/(2N)$, all partial sums
up to $Ns$ remain lawful for the local scalar law, so

$$
|b(s)|=|b(Ns)|/N\le\log K/N.
$$

This proves continuity at zero. Local additivity gives continuity
at every point of $(-H,H)$. With $a_*=H/4$, subdivision, finite
addition, and sign reversal give
$b(qa_*)=q b(a_*)$ for every rational $q$ with $|qa_*|<H$.
Density and continuity then give $b(s)=\gamma s$, where
$\gamma=b(a_*)/a_*$ is finite. Applying the multiplier identity
between $H/2$ and $k$ proves the last equality in (16.7).
$\square$

Neither the complex multiplier nor the unit phase $f/|f|$ has
been proved continuous. Example 5.4 already supplies bounded
encoders $e^{\gamma k}U(\alpha+\ell(k))$ with additive,
possibly discontinuous height twists and exact updates
$e^{\gamma s}R_{\ell(s)}$, $R_{t/2}$. They remain within the
contract. The modulus argument does not exclude them.

## 17. Original-metric domination and the dimension-three plateau

**Lemma 17.1 (Radial domination with a height-dependent residual).**
In the native case of Proposition 16.3 there are $C\ge0$ and
finite $\gamma\in\mathbb R$ such that

$$
\operatorname{err}(E,q)^2\ge\mathcal R_Z(C,\gamma).
\tag{17.1}
$$

The residual $c(k)$ need not be constant across heights.

**Proof of Lemma 17.1.** At a fixed interior height the complex
useful error is

$$
z(k,\alpha)-A(k)e^{i\alpha}
=c(k)+(p_+f(k)-A(k))e^{i\alpha}
             +p_-\overline{f(k)}e^{-i\alpha}.
$$

Call the nonconstant part $h_k(\alpha)$. It changes sign under
$\alpha\mapsto\alpha+\pi$. The mean of the squared errors
at these two actual phases is

$$
\frac{|c(k)+h_k(\alpha)|^2+|c(k)-h_k(\alpha)|^2}{2}
=|c(k)|^2+|h_k(\alpha)|^2.
$$

Thus the worst useful error at this height is at least
$\sup_\alpha|h_k(\alpha)|$. For complex numbers $u,v$,

$$
\sup_\alpha|ue^{i\alpha}+ve^{-i\alpha}|=|u|+|v|:
$$

the triangle inequality gives one direction, and choosing
$2\alpha$ to align the two nonzero terms gives the other; if
one term is zero the equality is immediate. Consequently

$$
\begin{aligned}
\sup_\alpha|z(k,\alpha)-A(k)e^{i\alpha}|
&\ge |p_+f(k)-A(k)|+|p_-|\,|f(k)|\\
&\ge \bigl||p_+|\,|f(k)|-A(k)\bigr|\\
&=|Ce^{\gamma k}-A(k)|,
\end{aligned}
$$

where $C=|p_+|e^{-\gamma H/2}\ge0$ by (16.7). In particular
$p_+=0$ yields the valid comparison $C=0$. Equation (12.1)
restores the fourfold useful-plane weight and the exact residual
$4Zk$, giving (17.1). The opposite-phase comparison is made at
each height separately. It neither constructs a common affine
center nor asserts that removing $c(k)$ is an admissible change
of encoder. $\square$

**Theorem 17.2 (Unrestricted three-dimensional plateau).** For
every $0<Z<1$ and every fixed preparation, every affine competitor
of stored dimension at most three is dominated in uniform
original-output error by some radial competitor of dimension at
most two. In particular,

$$
\boxed{
(e_3^{\rm aff}(Z))^2=(e_2^{\rm aff}(Z))^2
=\inf_{C\ge0,\ \gamma\in\mathbb R}
\sup_{0<k<H}\{4(Ce^{\gamma k}-A(k))^2+4Zk\}.}
\tag{17.2}
$$

Hence $e_3^{\rm aff}(Z)=e_2^{\rm aff}(Z)$.

**Proof of Theorem 17.2.** A competitor of infinite error is
dominated by the finite zero witness. For finite error, the
actual-hull reduction and rank split of §13 are exhaustive.
Deficient useful rank gives the zero radial comparison. A
full-rank hull of dimension two, or the lawful quotient of a
nonzero beta fiber at dimension three, is dominated by a radial
choice using the already-proved Theorem 6.4. Every other
competitor has a $\beta$-independent encoder on a hull of
dimension three.

For this last case, §14 bounds only the useful observable module.
A phase-independent readout or any unmatched abstract character
gives the zero radial comparison by Proposition 14.3. If the
native pair is used, the full primary-block argument of §15,
the lawful projector identities and nonzero multipliers of §16,
and Lemma 17.1 give a radial comparison. These cases include
rank loss, a missing pair, both possible zero useful coefficients,
unbounded hidden coordinates, and both affine offsets. No
partial-domain spanning or regularity assumption enters them.

Every radial comparison is an actual budget-two model, as stated
in Definition 12.1 and proved in Theorem 6.4. Thus the radial
infimum is a lower bound for every budget-three squared error. Conversely
all those radial models lie in the budget-three class, and the
budget-two class is a subclass of the budget-three class.
Equation (12.2) now gives both inequalities in (17.2).
Nonnegativity permits taking square roots. This argument compares
each individual competitor before taking any infimum; no compact
latent image, convergent sequence of encoders, or bound on model
parameters is needed. $\square$

The source's $\beta$ motion and its noncommuting rectangles are
unchanged. The only commuting action used globally is the phase
action on the actual homogeneous hull after the relevant encoder
has been shown to be $\beta$-independent. The probability/phase
identity used for the projector is only (16.3) on lawful states.
Thus (17.2) is an error plateau, not a claim that every hidden
coordinate is phase-trivial or that every affine realization is
radial.

## 18. Exact endpoint and attainment by reuse of the scalar solution

**Corollary 18.1 (The exact shared value and its parameter map).**
Define $v(Z)=e_2^{\rm aff}(Z)=e_3^{\rm aff}(Z)$. Then

$$
v(Z)=
\begin{cases}
4H\sqrt{T_\tau},&0<Z<2/3,\\
2\sqrt{ZH},&2/3\le Z<1,
\end{cases}
\qquad \tau=\frac{Z}{4H}\quad\text{in the first case}.
\tag{18.1}
$$

Here $T_\tau$ is the unique root supplied by Theorem 7.4, with

$$
\tau<T_\tau<T_0=\frac{(1+\tau)^2}{4},
$$

$$
\max_{0\le x\le1}
\left\{\sqrt{x(1-x)}-\sqrt{T_\tau-\tau x}
-T_\tau^{(1-x)/2}(T_\tau-\tau)^{x/2}\right\}=0.
\tag{18.2}
$$

Below the transition,

$$
2\sqrt{ZH}<v(Z)<1-Z/2.
$$

The normalization and the optimal radial parameters are exactly

$$
x=\frac{k}{H},\qquad c=\frac{C}{2H},\qquad
\lambda=\gamma H,\qquad
\mathcal R_Z(C,\gamma)=16H^2\mathcal J(c,\lambda),
$$

$$
C_*=2H\sqrt{T_\tau},\qquad
\gamma_*=\frac{1}{2H}\log\frac{T_\tau-\tau}{T_\tau}<0.
\tag{18.3}
$$

**Proof of Corollary 18.1.** Equation (17.2) has exactly the same
radial objective, with exactly the same $A(k)$ and metric
coefficient four, as Theorem 6.4. Lemma 7.2 identifies its
normalization by the displayed substitution. Lemma 7.3 and Theorems 7.4–7.6
then give (18.2), its unique root, the strict interval for that
root, the exact value, and the parameters (18.3). At and above
$Z=2/3$, Theorem 10.2 gives $e_2^{\rm aff}=2\sqrt{ZH}$;
Theorem 17.2 transfers it to budget three. This reuses the
published endpoint-log corridor, root, contact, and transition
proofs without introducing a different scalar optimization.
$\square$

**Corollary 18.2 (Attained tolerance endpoints and retained distinctions).**
In the literal class, the finite achievable tolerance set at
either budget two or budget three is $[v(Z),\infty)$.
For $0<Z<2/3$ the optimal positive radial amplitude is the same
unique amplitude

$$
\rho(k)=2H\sqrt{T_\tau}\,e^{\gamma_*k}
$$

as in Theorem 7.6. Its annular model attains error $v(Z)$ at
every phase pair of the actual interior height $k=Hx_\tau$,
where $x_\tau$ is the unique contact in Theorem 7.5. For
$Z\ge2/3$ the zero decoder attains the error infimum, although
none of its lawful states attains its error supremum. The
transition value is $v(2/3)=2/3$.

**Proof of Corollary 18.2.** The annulus of Theorem 8.1 is an
actual budget-two model, hence also a budget-three model, with
the stated attained error and interior maximizing height. Its
radial uniqueness and the contact statements are precisely
Theorems 7.5–7.6 and 8.1, with the parameter map (18.3).
Theorem 10.2 supplies the zero decoder and its strict pointwise
error inequality in the other range, including the transition.
Theorem 17.2 excludes every tolerance below $v(Z)$; the stated
single witnesses include the endpoint and every larger finite
tolerance. $\square$

The uniqueness here is only that of the optimal positive radial
amplitude, not of arbitrary optimizing affine realizations. The
scalar limits of Proposition 10.4 also apply to the shared value
$v(Z)$, including the limit $1/2$ as $Z\downarrow0$ and $2/3$
as $Z\uparrow2/3$ from below. In the latter limit the radial
exponent tends to $-\infty$; the separate transition witness
supplies attainment there. Scalar maxima at $x=0,1$ or scalar
parameter limits do not extend an arbitrary encoder or the source
to $k=0,H$ or to $Z=0,1$. Escaping radial parameters and varying
arbitrary encoders cannot improve the value, because (17.2)
already bounds every competitor before taking an infimum.

## 19. Equal capacities with guards and all prescribed paths

For $n=2,3$, write $\mathfrak F_{\le n}^{\rm lit}$,
$\mathfrak F_{\le n}^{\rm g}$,
$\mathfrak F_{\le n}^{\rm p}$, and
$\mathfrak F_{\le n}^{\rm gp}$ for the four classes of
Definition 2.2: literal, recoverable straight guards, all prescribed
paths, and both guard and path requirements. In the combined class,
the full path guards are recoverable as well. Every path is a
prescribed finite simultaneous native path with its velocities
fixed independently of the starting ray. Its domain is its full
all-times guard.

**Theorem 19.1 (The same endpoint in all four contracts).** For
each $0<Z<1$, every fixed preparation, and $n\in\{2,3\}$,
the capacities of all four classes equal $v(Z)$ from (18.1),
and their finite tolerance sets are all $[v(Z),\infty)$.
The attaining witnesses have exact encoding at every truncated
path, every intermediate time, and every prefix of every finite
lawful concatenation, with the same current-state uniform error.

**Proof of Theorem 19.1.** The inclusions at each fixed dimension
budget are

$$
\mathfrak F_{\le n}^{\rm gp}\subseteq
\mathfrak F_{\le n}^{\rm g}\subseteq
\mathfrak F_{\le n}^{\rm lit},\qquad
\mathfrak F_{\le n}^{\rm gp}\subseteq
\mathfrak F_{\le n}^{\rm p}\subseteq
\mathfrak F_{\le n}^{\rm lit}.
\tag{19.1}
$$

Therefore the literal lower bounds of Theorem 7.6, Theorem 10.2,
and Theorem 17.2 are lower bounds for each corresponding stronger
class. The direction of inclusion is essential: the quotient of
Lemma 13.3 was only required to be literal and is not being
asserted to recover guards.

Below the transition use the actual annulus of Theorem 8.1, with
$\gamma_*<0$ and $C_*$ from (18.3). Its image and recovered
height, as proved in Proposition 8.2, are

$$
2H\sqrt{T_\tau-\tau}<\|z\|<2H\sqrt{T_\tau},\qquad
\kappa(z)=\frac1{\gamma_*}
\log\frac{\|z\|}{2H\sqrt{T_\tau}}.
$$

The exact straight guards are $0<\kappa(z)+s<H$ for every real
$s$ and the whole actual image for every real $t$. The fixed
maps are $e^{\gamma_*s}I$ and $R_{t/2}$. This includes zero,
negative, and empty-domain commands. The original preparation
initializes $z=\rho(k_0)U(0)$, with all preparation phases still
in the fixed original decoder $D$. Recovering height from the
actual stored norm adds no external input and changes no affine
readout requirement.

To match the full path contract explicitly, use the parameters
of Proposition 9.1. For prescribed integrable velocities on
$[0,T_{\rm p}]$ put

$$
\eta(u)=\int_0^u a_c(v)\,dv,\qquad
\Delta=\eta(T_{\rm p}),\qquad
L=\int_0^{T_{\rm p}}b_c(u)\,du,\qquad
C_{\rm p}=\int_0^{T_{\rm p}}\eta(u)b_c(u)\,du.
$$

The native all-times guard and endpoint remain

$$
0<k+\eta(u)<H\quad\text{for every }u\in[0,T_{\rm p}],
\tag{19.2}
$$

$$
k'=k+\Delta,\qquad \alpha'=\alpha+L/2,\qquad
\beta'=\beta+(1/2-k/r)L-C_{\rm p}/r.
\tag{19.3}
$$

The proof of these formulas, the existence of the mixed integral,
and the equivalence of (19.2) to
$k+\min\eta>0$, $k+\max\eta<H$ are Proposition 9.1.
In particular, the extrema are attained on the compact time
interval; lawful endpoints alone are not a substitute for
(19.2). The negative mixed term remains in the true source.

Theorem 9.2 supplies the fixed annular path map

$$
z\longmapsto e^{\gamma_*\Delta}R_{L/2}z
$$

on the exact recoverable guard
$0<\kappa(z)+\eta(u)<H$ for every $u$. It is defined even for
a prescribed path with empty guard. Substitution into (19.3)
is its exact encoding identity; the mixed term is invisible
only because this particular encoder forgets $\beta$.
For every truncation, replace the upper integration limit by
the truncated time and retain that truncation's own all-times
guard. The same identity holds. For two concatenated paths,
Proposition 9.1 gives the full source triple

$$
(\Delta_1+\Delta_2,\ L_1+L_2,
 C_1+C_2+\Delta_1L_2),
$$

and its guard is the first full guard together with the second
full guard from the actual intervening height. The encoded maps
compose by adding $\Delta$ and $L$, consistently with this
source formula and the permitted loss of $\beta$. Induction
gives every finite lawful concatenation. Exact latent encoding
at each current state lets Theorem 8.1 apply at each time without
accumulating readout error.

At and above the transition, use the actual one-coordinate
height witness of Theorems 10.1–10.2:

$$
E_{\rm h}(k,\alpha,\beta)=K=k,\qquad q(K)=0,
$$

with probability update $K\mapsto K+s$, phase update $K\mapsto K$,
and prescribed-path update $K\mapsto K+\Delta$. Its full path
guard is exactly $0<K+\eta(u)<H$ for all $u$; its straight
guards are the corresponding special cases. The same truncation
and concatenation identities are exact. Its error is $v(Z)$.
The zero-dimensional literal witness also attains that value,
but is not used to supply recoverable guards.

The annulus uses two real coordinates and the height witness one,
so each belongs to the combined class at both budgets two and
three. These matching upper witnesses, together with (19.1),
prove every capacity equality. The endpoints are included because
these are actual attaining models, and larger finite tolerances
are satisfied by the same models. Equality of capacities does
not assert equality of the four model classes. $\square$

## 20. Three-dimensional result map, sources, and surviving boundaries

All results in the following map retain the arbitrary fixed
preparation, full actual current-ray domain, original signed command
menu, affine offsets, and ten-output Euclidean metric.

| Result | Declarations | Role in the three-dimensional conclusion |
|---|---|---|
| At-most-three budget and inherited interface | 12.1–12.2 | Keeps the original contract; reuses bounded-observable erasure and the exact two-dimensional radial minimax |
| Actual-hull restriction and useful-rank split | 13.1–13.2 | Includes degenerate hulls and derives bounded useful coordinates only when justified |
| Nonzero beta-fiber propagation and quotient | 13.3–13.4 | Places a nonzero kernel direction in every nonempty partial domain before descending the update; quotient is only literal |
| Full phase representation and useful module | 14.1–14.2 | Derives the circle action on the actual homogeneous hull and distinguishes its fixed covector from a fixed vector |
| Unmatched character exclusion | 14.3 | Finite geometric averages cover discontinuous abstract characters without integration |
| Complete primary blocks and finite phase projectors | 15.1–15.2 | Counts the whole native blocks, including possible Jordan multiplicity, and leaves lawful hidden residual blocks |
| Hidden positive character and additive shear | 15.3–15.4 | Actual full-hull examples showing that hidden phase-triviality and a common affine center are not required |
| Orbitwise projector and nonvanishing multiplier | 16.1–16.2 | Uses only lawful actual phase orbits, not a partial-domain spanning assumption or an ambient group law |
| Useful native amplitude and its modulus | 16.3 | Bounds only observable coefficients and derives exponential modulus from reciprocal local multipliers |
| Original-metric radial domination and plateau | 17.1–17.2 | Every budget-three competitor is dominated by an actual budget-two radial model |
| Exact scalar value, parameter map, and attainment | 18.1–18.2 | Applies the existing root/contact/transition results with their original normalization and tolerance endpoints |
| Recoverable guards and all prescribed paths | 19.1 | Uses proper subclass lower bounds and actual matching annular/height witnesses, with every truncation and finite concatenation |

The published suppliers retain their precise roles. [F], *Native FIB
continuation: exact affine obstruction and compact-band approximation*,
supplies the native source conventions and original-output/path
interfaces reconstructed in §§1 and 9. [O], *Native FIB on the full
open domain: affine approximation and finite attainment*, supplies
bounded affine observable erasure and the worst-$\beta$ reduction,
as reused in §3 and Proposition 12.2. Its all-finite floor,
nonattainment, fixed-dimension gap, and dimension-limit results
remain prior results, not substitutes for the dimension-three
argument. Sections 4–10 of this volume supply the exact budget-two
minimax, endpoint-log corridor, unique root and radial amplitude,
attaining annulus, transition, and exact path witnesses used in
§§18–19. Their proofs are reused rather than claimed as new
three-dimensional scalar results.

The additional mathematical synthesis is the actual-hull rank
alternative with nonzero-fiber transport into each partial domain,
the invariant-covector count of complete conjugate primary blocks,
and the finite phase projector acting on each individual lawful
orbit. Together these give a nonvanishing native coefficient,
its local multiplier law, and an ordinary exponential modulus
without bounding arbitrary hidden coordinates. Opposite-phase
comparison then handles a height-dependent residual and yields
the exact plateau in the original metric. The hidden examples
specify why stronger statements about centers and phase-trivial
hidden state are unavailable under this contract.

The general ingredients are finite-dimensional affine
homogenization, invariant flags and primary decompositions,
polynomial spectral projectors from Bezout identities,
characters of abstract abelian groups, divisibility, finite
geometric averages, and the bounded additive-function argument.
The needed forms are proved here or reused from the preceding
sections. No topological character classification or external
regularity theorem is a premise. This is a statement of content
relative to the specified sources, with no worldwide-priority
claim.

The remaining boundaries are part of the result:

- The source has $0<Z<1$ and $0<k<H$. All phase points are actual
  current rays from the arbitrary fixed preparation. No endpoint
  ray, vanished support, stored real lift, producing-history
  encoder, reduced command menu, or finite-horizon replacement
  is included. Each executed history is individually finite.
- Stored dimension, actual affine-hull dimension, and useful-readout
  rank are distinct. Homogeneous dimension at most four is used
  only after actual-hull restriction. An invariant covector is
  not a normalized fixed vector. Hidden positive characters and
  unipotent blocks remain lawful, as the examples demonstrate.
- The boundedness arguments concern the decoder, its useful
  phase translates, and the native coefficients they expose.
  They impose no measurability, continuity, injectivity, or
  latent bound on arbitrary encoders. The native modulus is
  regular only because the useful coefficient supplies local
  upper and reciprocal bounds; its unit phase remains unrestricted.
- Every probability inference is made on a nonempty lawful
  partial domain, or on a lawful reversible leg or triple.
  Empty-domain maps are unconstrained. Global phase identities
  hold on the actual homogeneous hull because the phase maps
  have full domain. No ambient probability group law or
  off-image inverse is assumed.
- The radial comparison is an error domination, not a guard
  theorem for intermediate quotients or a classification of all
  affine factors or optimizers. The matching annular and height
  witnesses separately establish the full guard and path claims.
  General radial choices need not recover height; only the
  specified attaining witnesses are used for the stronger classes.
- The exact small budgets established here are $0,1,2,3$.
  Below $Z=2/3$, this result supplies no exact capacity or
  attainment classification for general budgets $n\ge4$, no
  general parity law, and no dimension-four theorem. The earlier
  all-finite and fixed-dimension results do not remove those
  remaining questions or give a general sharp dimension rate.
- The original finite-hidden-$N$ attainment alternative remains
  unresolved. No identification of its objective and admissible
  realizations with this affine-readout problem is supplied, and
  no broader research-completion conclusion follows.
- Initialization and continuation are exact over real coordinates.
  The permitted witnesses are noninjective and have decoded
  vectors outside the native physical output image. Imposing
  injection or physical readouts would require a different
  upper-bound analysis. No finite-bit, conditioning, noise,
  acquisition, physical-implementation, training, or empirical
  machine-learning claim is made.
- These proofs are handwritten source mathematics. They are not
  Lean declarations, kernel verification, or a certification of
  unrelated statements in the cited manuscripts.

## 20.99 追加锚
