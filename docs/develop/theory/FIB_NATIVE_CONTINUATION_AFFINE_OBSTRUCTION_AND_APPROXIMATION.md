# Native FIB continuation: exact affine obstruction and compact-band approximation

The native double-wall source has three-dimensional current rays and an exact
four-coordinate affine readout. Nevertheless, no finite-dimensional encoder,
however irregular, can combine an exact fixed affine readout with
state-independent affine updates for every lawful probability displacement.
On every closed positive interior band, a different finite encoding has exact
affine probability updates and a fixed linear readout with any prescribed
positive uniform error. These are separate statements about the same source,
the same ten outputs and the same output norm.

## 1. Source, preparation and the current-ray task

### 1.1 Native correspondence

The parent volume is *AURIC FIB-ATOM: Probability, Phase Transport and
Holonomy*. Its Definition 2.1 fixes the mode order, probabilities and relation
direction; Definitions 2.3 and 3.1 fix the negative phase convention and
transport law. Its Definition 8.1 permits queries at arbitrary finite
prefixes of those controls. Theorems 8.2, 8.4 and 8.6 already supply the
current-ray domain, its observability and its static affine capacity. The
specialization below retains precisely that task.

**Definition 1.1 (Fixed double-wall source and original controls).** Fix
$0<Z<1$, put $r=1-Z$ and $H=r/2$, and impose the two native walls
$X=Y=H$. In mode order $(0,1,2,3,13)$ the probability law and its tangent are

$$
p(k)=(k,H-k,Z,H-k,k),\qquad 0<k<H,
\qquad d=(1,-1,0,-1,1)^{\mathsf T}.
$$

Fix an arbitrary initial height $k_0\in(0,H)$ and arbitrary fixed preparation
phases $\theta^{\rm in}$. All producing histories start from this same
preparation. Write $h=\theta-\theta^{\rm in}$ for the real phase
increment. The pure amplitudes and declared transport are

$$
\psi_s=\sqrt{p_s}\,e^{-i\theta_s},\qquad
\dot p=d\dot k,\qquad
\dot\theta_s=w_s(k)\dot\chi,
\qquad
w_s(k)=\frac{d_s}{p_s(k)I(k)},
$$

$$
I(k)=\frac1{p_0(k)}+\frac1{p_1(k)}
     +\frac1{p_3(k)}+\frac1{p_{13}(k)}.
$$

An admissible history is a piecewise $C^1$ or absolutely continuous control
path $(k,\chi)$ on a finite compact time interval, with $k(t)\in(0,H)$
throughout and finite phase variation. The real initial relation lift is
chosen consistently with $d^{\mathsf T}\theta^{\rm in}$. We query its
current ray without requiring a closing loop or integer winding at query
time. Write $\mathbb T=\mathbb R/(2\pi\mathbb Z)$.

The correspondence to the parent fiber is $\kappa=k$,
$r-X-Y=0$, $\kappa_-=0$, $\kappa_+=H$, and
$p_0=p_{13}=k$, $p_1=p_3=H-k$. In particular $2H+Z=1$, so normalization
and the five probabilities are unchanged. Probability displacement here is
vertical motion at fixed means, not Fisher-horizontal transport across means.

**Lemma 1.2 (Native phase equations and ray representatives).** After a
common constant gauge change, put
$\eta_s=\theta_s^{\rm in}-\theta_2^{\rm in}$. Every admissible phase
increment has the form

$$
h_0=h_{13}=u,\qquad h_1=h_3=v,\qquad h_2=0.
$$

The current representative is

$$
\psi(k,u,v)=\bigl(
\sqrt{k}e^{-i(\eta_0+u)},
\sqrt{H-k}e^{-i(\eta_1+v)},
\sqrt Z,
\sqrt{H-k}e^{-i(\eta_3+v)},
\sqrt{k}e^{-i(\eta_{13}+u)}
\bigr).
$$

For real lifts along a history, and hence also as equations for circle
increments, set $\alpha=u-v$ and $\beta=u$. Then

$$
\begin{aligned}
I(k)&=\frac2k+\frac2{H-k}=\frac r{k(H-k)},\\
w_+(k)&=\frac12-\frac{k}{r},\qquad
w_-(k)=-\frac{k}{r},\qquad w_2(k)=0,\\
du&=\left(\frac12-\frac{k}{r}\right)d\chi,
\qquad dv=-\frac{k}{r}d\chi,\\
d\alpha&=\frac12d\chi,
\qquad d\beta=\left(\frac12-\frac{k}{r}\right)d\chi.
\end{aligned}
$$

**Proof.** Substitution of the five probabilities into $I$ and $w$ gives
the displayed formulas. The equal components of $w$ give equal increments
within the two groups, starting at zero increments. They do not impose any
equalities between the arbitrary preparation phases. The middle component
remains zero. Subtraction of the two group equations gives the equations for
$\alpha,\beta$. The inverse change of circle coordinates is
$u=\beta$, $v=\beta-\alpha$; both directions use integer coefficients and
are well defined on $\mathbb T^2$. The real relation increment is
$d^{\mathsf T}h=2(u-v)=2\alpha=\chi-\chi(0)$ for the actual lifts.
$\square$

### 1.2 Actual reachability, without added phase controls

**Proposition 1.3 (Exact reachable current-ray domain).** From the one fixed
preparation, the exact current-ray domain is

$$
\mathcal M=(0,H)\times\mathbb T^2,
$$

with coordinates $(k,\alpha,\beta)$, equivalently $(k,u,v)$. Every point
has a finite realization consisting of a rectangle, exactly one fixed-height
phase leg, and a probability leg, in that order. The intrinsic dimension is
three.

**Proof.** Fix once and for all $k_1\in(0,H)$ different from $k_0$.
Given a target $k\in(0,H)$ and any real representatives $u,v$, calculate

$$
L=2(u-v),\qquad
u_L=\left(\frac12-\frac{k_0}{r}\right)L,
\qquad v_L=-\frac{k_0}{r}L.
$$

These are the contributions of a phase leg; no leg has yet been executed.
Since $u_L-v_L=u-v$, the number $t=u-u_L=v-v_L$ is well defined.
Set $A=-rt/(k_1-k_0)$. Execute first the rectangle

$$
(k_0,\chi_0)\longrightarrow(k_1,\chi_0)
\longrightarrow(k_1,\chi_0+A)
\longrightarrow(k_0,\chi_0+A)
\longrightarrow(k_0,\chi_0).
$$

Only its two phase legs contribute phase increment. Lemma 1.2 gives the
increment in each group as

$$
A\bigl(w_\pm(k_1)-w_\pm(k_0)\bigr)
   =-\frac{A(k_1-k_0)}r=t.
$$

Next execute exactly one phase leg of increment $L$ at $k_0$. Finally move
from $k_0$ to $k$ with $\chi$ fixed. The resulting increments are
$(t+u_L,t+v_L)=(u,v)$. Every probability segment stays in $(0,H)$ by
convexity, and all phase increments are finite. This is a finite piecewise
linear admissible history with the original two controls. Conversely the
ODE enforces the group equalities of Lemma 1.2, so there are no other current
states.

Equality of rays in the displayed representatives forces equality of the
representatives themselves: the middle amplitude is the fixed positive
number $\sqrt Z$. Equality of their moduli gives equal $k$, and their
nonzero group components then give equal $u,v$ modulo $2\pi$. These
conditions also suffice for equality. There is no additional finite quotient.
The inverse from the projective chart with nonzero middle coordinate
recovers $k$ and the two unit phase pairs smoothly. Thus the parametrization
is a smooth embedding and has dimension $1+2=3$.

This is the double-wall instance of the parent's Theorem 8.2, with its
finite rectangle mechanism made explicit. Reachable independent phase
coordinates are not new independently available phase controls. $\square$

## 2. The original outputs and the reused static result

**Definition 2.1 (Unchanged coherence output).** Keep the ordered edge menu

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)).
$$

For $e=(i,j)$ let $\delta_e=\theta_i^{\rm in}-\theta_j^{\rm in}$.
The edge observables are

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,
\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|.
$$

Their original doubled expectation pair is

$$
y_e=2\sqrt{p_ip_j}
  \bigl(\cos(\delta_e+h_i-h_j),\sin(\delta_e+h_i-h_j)\bigr).
$$

Concatenate these five pairs to obtain $y:\mathcal M\to\mathbb R^{10}$.
All errors below use the original Euclidean norm $\|\cdot\|_2$ on these
ten coordinates. No output is whitened, divided by its radius, or rescaled
in the task definition.

**Lemma 2.2 (Fixed native decoder and its exact norm).** Write

$$
U(t)=\binom{\cos t}{\sin t},\qquad
R_t=\begin{pmatrix}\cos t&-\sin t\\\sin t&\cos t\end{pmatrix},
\qquad J=\operatorname{diag}(1,-1),
$$

$$
A(k)=2\sqrt{k(H-k)},\qquad B(k)=2\sqrt{kZ},\qquad
z_\alpha=A(k)U(\alpha),\qquad z_\beta=B(k)U(\beta).
$$

Define the fixed linear maps

$$
D_0(z_\alpha,z_\beta)
 =(z_\alpha,z_\beta,z_\alpha,Jz_\alpha,Jz_\alpha),
\qquad O=\bigoplus_{e\in\mathcal E}R_{\delta_e},\qquad D=OD_0.
$$

Then the original output, with zero offset, is

$$
y=D(z_\alpha,z_\beta),\qquad
D^{\mathsf T}D=4I_2\oplus I_2.
$$

In particular, for arbitrary pairs $a,a',b,b'\in\mathbb R^2$,

$$
\|D(a,b)-D(a',b')\|_2^2
 =4\|a-a'\|_2^2+\|b-b'\|_2^2.
$$

**Proof.** The negative amplitude exponential gives
$\overline\psi_i\psi_j=\sqrt{p_ip_j}e^{i(\theta_i-\theta_j)}$.
The two Hermitian expectations are respectively twice its real and imaginary
parts. In edge order the increment differences are
$\alpha,\beta,\alpha,-\alpha,-\alpha$. The last two signs are essential
for open prefixes. Since $U(-t)=JU(t)$, the five blocks are exactly those
of $D$. Each of the four bottom-edge blocks contributes one copy of $I_2$
to its pullback Gram; the middle-reference block contributes the remaining
copy. Both $O$ and $J$ are orthogonal. This proves the Gram and norm
identities in the original output coordinates. $\square$

**Proposition 2.3 (Current observability, image and static capacity).** The
original output smoothly separates all current rays. The four response
coordinates have exactly the source image

$$
\mathscr Z=\left\{(z_\alpha,z_\beta):
 0<t<4HZ,\quad
 \|z_\alpha\|^2=\frac{Ht}{Z}-\frac{t^2}{4Z^2},
 \quad t=\|z_\beta\|^2\right\}.
$$

Both pair angles are arbitrary. The least dimension of an arbitrary encoder
with a fixed affine decoder for the current output alone is four.

**Proof.** The $02$ block recovers

$$
k=\frac{\|y_{02}\|^2}{4Z}.
$$

Removing the known preparation rotations from the $02$ and $01$ blocks
and dividing by the now known positive radii $B(k),A(k)$ recovers
$U(\beta),U(\alpha)$. This is a smooth circle-valued inverse on the
image; it does not choose a global real angle branch. Thus the output is a
smooth embedding of the current rays. This reconstruction is a mathematical
function of ideal expectations, not a finite-measurement acquisition claim.

For the response image, $t=4kZ$ gives $0<t<4HZ$, and substitution into
$\|z_\alpha\|^2=4k(H-k)$ gives the stated equation. Conversely that
inequality puts $k=t/(4Z)$ in $(0,H)$, the equation gives the correct
positive radius for $z_\alpha$, and Proposition 1.3 realizes both angles.
Hence every point in the displayed set is an actual encoded ray.

Lemma 2.2 gives an affine decoder of dimension four. For the lower bound,
fix any interior $k$. Proposition 1.3 realizes the full product of the two
circles of positive radii $A(k),B(k)$. If

$$
c+\ell_\alpha\cdot z_\alpha+\ell_\beta\cdot z_\beta=0
$$

on this product, compare opposite values of $\alpha$ with $\beta$ held
fixed. This gives $\ell_\alpha\cdot U(\alpha)=0$ for all $\alpha$,
so $\ell_\alpha=0$. Opposite values of $\beta$ give
$\ell_\beta=0$, and then $c=0$. The affine hull is therefore
$\mathbb R^4$. The map $D$ is injective, as is already seen from its first
two blocks after undoing their fixed rotations. Thus the output affine hull
has dimension four. Any affine decoder from $\mathbb R^n$ has image affine
hull of dimension at most $n$, regardless of its encoder or offset.
Consequently $n\ge4$.

These are precisely the parent's double-wall Theorems 8.4 and 8.6 and
equations (8.18)–(8.21), with $(z_a,z_b)=(z_\alpha,z_\beta)$ and
$r/2=H$. They are reused static facts, not a continuation closure theorem.
The curved image has dimension three while its affine hull has dimension
four. $\square$

## 3. Finite exact nonlinear continuation

**Proposition 3.1 (Every lawful probability displacement).** The original
straight probability leg of displacement $s$ is

$$
k(t)=k+ts,\qquad \chi(t)=\chi(0),\qquad 0\le t\le1.
$$

On $\mathcal M$ it is the partial action
$T_s(k,\alpha,\beta)=(k+s,\alpha,\beta)$, with exact guard
$0<k+s<H$. On $\mathscr Z$, recover $k=\|z_\beta\|^2/(4Z)$.
Its exact four-coordinate update is

$$
F_s(z_\alpha,z_\beta)=\left(
 \sqrt{\frac{(k+s)(H-k-s)}{k(H-k)}}\,z_\alpha,
 \sqrt{\frac{k+s}{k}}\,z_\beta\right).
$$

**Proof.** The ODE leaves both phases fixed on this leg. Its entire
probability segment is interior if and only if its endpoint is interior,
because the current height is already interior and the interval is convex.
Every denominator and square-root argument above is positive on the guard.
The two factors are exactly $A(k+s)/A(k)$ and $B(k+s)/B(k)$, so the
formula gives the actual encoded endpoint. It preserves $\mathscr Z$ and
$D(F_s(z))$ is the original endpoint output. The factors depend on the
recovered current height, giving a finite realization with generally
nonlinear updates. $\square$

**Theorem 3.2 (Every prescribed native continuation and its all-times
guard).** Prescribe a finite continuation by its original integrable control
velocities $a_c=\dot k$, $b_c=\dot\chi$ on $[0,T]$, in the regularity
class of Definition 1.1. Put

$$
\rho(t)=\int_0^t a_c(\tau)\,d\tau,\qquad
\Delta=\rho(T),\qquad L=\int_0^T b_c(t)\,dt,\qquad
C=\int_0^T\rho(t)b_c(t)\,dt.
$$

Its exact source guard is

$$
k+\rho(t)\in(0,H)\quad\hbox{for every }t\in[0,T].
$$

On that guard the endpoint coordinates satisfy

$$
k'=k+\Delta,\qquad
\alpha'=\alpha+\frac L2,\qquad
\beta'=\beta+\left(\frac12-\frac{k}{r}\right)L-\frac Cr.
$$

Its exact four-coordinate map is

$$
\begin{aligned}
z_\alpha'&=
 \sqrt{\frac{(k+\Delta)(H-k-\Delta)}{k(H-k)}}\,
 R_{L/2}z_\alpha,\\
z_\beta'&=
 \sqrt{\frac{k+\Delta}{k}}\,
 R_{(1/2-k/r)L-C/r}z_\beta.
\end{aligned}
$$

It is well defined on the actual source image, preserves that image, and
decodes exactly by the same $D$. All finite lawful concatenations are covered.

**Proof.** The continuous function $\rho$ is bounded on $[0,T]$ and
$b_c$ is integrable with finite phase variation, so $C$ exists. The
declared path from a current height is $k(t)=k+\rho(t)$, which proves
the guard. For a general path, lawful endpoints alone do not imply this
all-times condition.

Integrating Lemma 1.2 gives the phase formulas directly. In particular,

$$
\int_0^T\left(\frac12-\frac{k+\rho(t)}r\right)b_c(t)\,dt
 =\left(\frac12-\frac kr\right)L-\frac Cr,
$$

so the sign of the mixed integral is negative. Positive endpoint radius
ratios give the two displayed amplitude factors. Since $R_tU(q)=U(q+t)$,
substitution proves the response map and its source-image preservation.
All expressions depend only on the current ray and prescribed control, and
the rotations respect the phase circles. They do not require recovering a
past real lift.

For completeness, if a continuation with parameters
$(\Delta_1,L_1,C_1)$ is followed by one with relative parameters
$(\Delta_2,L_2,C_2)$, its combined relative displacement during the
second piece is $\Delta_1+\rho_2$. Thus the combined parameters are

$$
(\Delta_1+\Delta_2,\ L_1+L_2,\ C_1+C_2+\Delta_1L_2).
$$

Applying the endpoint formulas successively gives the same phase and height
as this combined triple. The guard is the guard of the first piece together
with the guard of the second from the actual height $k+\Delta_1$.
Induction gives every finite lawful concatenation. Setting $b_c=0$ recovers
Proposition 3.1; a fixed-height phase leg has $\rho=0$ and $C=0$.
This is an exact finite realization with generally nonlinear updates, with
no affine assertion for the full control class. $\square$

## 4. Part A: obstruction to every finite exact affine lift

**Definition 4.1 (The full affine probability-continuation contract).** Fix
the source and preparation above. For a finite integer $n\ge0$, allow an
arbitrary function $E:\mathcal M\to\mathbb R^n$, a fixed linear map
$D_*:\mathbb R^n\to\mathbb R^{10}$ and a fixed $c\in\mathbb R^{10}$.
For every $s\in(-H,H)$ allow a fixed matrix $M_s\in\mathbb R^{n\times n}$
and vector $b_s\in\mathbb R^n$. Require

$$
y(x)=c+D_*E(x)\qquad(x\in\mathcal M),
$$

$$
E(T_sx)=M_sE(x)+b_s
\quad\hbox{whenever }x=(k,\alpha,\beta)\in\mathcal M,
\quad 0<k+s<H.
$$

The coefficients may depend on the fixed source, preparation and displacement
$s$, but not on the current state or producing history. There is no encoder
regularity or injectivity assumption, no regularity in $s$, no global matrix
group law, and no obligation outside the lawful partial domains. The actual
action is exactly the straight leg of Proposition 3.1. These quantifiers
allow both the readout offset and the update offset.

**Lemma 4.2 (Local independence of square-root translates).** Let $I$ be
a nonempty open real interval, and let $s_1,\ldots,s_m$ be distinct, with
$k+s_j>0$ for every $k\in I$ and every $j$. For every integer $m\ge1$,
the functions $k\mapsto\sqrt{k+s_j}$ are linearly independent on $I$.

**Proof.** Suppose $\sum_{j=1}^m c_j\sqrt{k+s_j}=0$ on $I$, and fix
$k_*\in I$. Differentiate this finite sum $q$ times for
$q=0,\ldots,m-1$. The power rule gives

$$
0=\gamma_q\sum_{j=1}^m c_j(k_*+s_j)^{1/2-q},\qquad
\gamma_0=1,\qquad
\gamma_q=\prod_{\ell=0}^{q-1}\left(\frac12-\ell\right)
\quad(q\ge1).
$$

Every $\gamma_q$ is nonzero. Set
$a_j=c_j\sqrt{k_*+s_j}$ and $t_j=(k_*+s_j)^{-1}$. After division,

$$
\sum_{j=1}^m a_j t_j^q=0,\qquad q=0,\ldots,m-1.
$$

The $t_j$ are distinct. For each $i$ the polynomial
$P_i(t)=\prod_{j\ne i}(t-t_j)$ has degree at most $m-1$, hence is a
linear combination of those monomials. Therefore

$$
0=\sum_{j=1}^m a_jP_i(t_j)
 =a_i\prod_{j\ne i}(t_i-t_j).
$$

The product is nonzero, including the empty product $1$ when $m=1$.
Thus $a_i=0$, and positivity of $k_*+s_i$ gives $c_i=0$. This proves
independence by the elementary Vandermonde interpolation argument. Only
explicit smooth square-root functions were differentiated. $\square$

**Theorem 4.3 (Native all-finite affine-lift obstruction).** For every
allowed $Z$, every fixed arbitrary preparation and initial interior height,
and every finite $n\ge0$, Definition 4.1 has no solution.

**Proof.** Use the common starting interval and displacement family

$$
I=(H/4,H/2),\qquad S=(0,H/4).
$$

For each $k\in I$, the canonical straight probability prefix from $k_0$
to $k$ with $\chi$ fixed is lawful and has zero phase increments. Denote
its actual current ray by $x_k=(k,0,0)$. For every $s\in S$ the appended
leg stays in $(H/4,3H/4)$. Thus the same reachable open interval lies in
every selected action domain, with a positive margin from both fiber ends.
No limiting zero-support state or infinite history is used.

Put $\delta=\delta_{02}$ and define the fixed linear functional on the
original ten outputs by

$$
\ell(y)=\cos\delta\,y_{02,1}+\sin\delta\,y_{02,2}.
$$

Both $x_k$ and its probability continuation have $\beta=0$. Definition
2.1 therefore gives, for every $k\in I$ and $s\in S$,

$$
\ell(y(T_sx_k))=2\sqrt Z\sqrt{k+s}.
$$

This is a consequence of the required full output, not a replacement task.
It preserves the original factor of two and works for every fixed
preparation.

If the contract held, set $e_j(k)=E_j(x_k)$ and let

$$
W=\operatorname{span}_{\mathbb R}\{1,e_1,\ldots,e_n\}
$$

as a space of pointwise functions on $I$. Its dimension is at most $n+1$,
even if every $e_j$ is irregular. For each $s\in S$ the two affine
identities yield

$$
2\sqrt Z\sqrt{k+s}
 =\ell(c)+\ell(D_*b_s)+(\ell D_*M_s)E(x_k).
$$

All coefficients on the right are constant in $k$. The constant function
in $W$ accounts for both affine offsets. Since $Z>0$, this puts every
function $\sqrt{k+s}$, $s\in S$, in $W$.

Choose $n+2$ distinct displacements in the nonempty interval $S$.
Lemma 4.2 makes their square-root responses linearly independent, whereas
$\dim W\le n+1$. This contradiction proves the result, including $n=0$.
The proof never differentiates the encoder or the update coefficients and
needs no global translation theorem. $\square$

**Corollary 4.4 (Arbitrary encoders of full histories).** The same
nonexistence holds for an arbitrary finite-dimensional encoder of complete
producing histories if one fixed affine readout returns their current
original output and one state-independent affine map for each $s$ appends
the same lawful probability leg.

**Proof.** Let $H_k$ be the canonical probability history used in Theorem
4.3, and let $H_k*s$ append the displacement leg. Replace $e_j(k)$ by
$E_j(H_k)$. The current response of $H_k*s$ under $\ell$ is still
$2\sqrt Z\sqrt{k+s}$, while the appending contract gives the same
expression in $\operatorname{span}\{1,e_1,\ldots,e_n\}$. Lemma 4.2
gives the same contradiction. No histories with the same current ray have
been identified, so retaining history-dependent features does not evade this
affine contract. This is not a bound on acquiring or storing histories.
$\square$

**Corollary 4.5 (Exact obstruction on every positive closed band).** Fix
$0<a<b<H$ and restrict the current source to
$\mathcal M_{ab}=[a,b]\times\mathbb T^2$. Require the exact contract only
for all straight probability legs contained in that band. It still has no
finite-dimensional solution.

**Proof.** Write $w=b-a>0$ and use
$I=(a+w/4,a+w/2)$ and $S=(0,w/4)$. The canonical zero-increment rays
are reachable from the original preparation, and every appended segment
stays in the band. The scalar response, both-offset finite-span calculation
and independence proof of Theorem 4.3 apply without change. $\square$

The parent's Proposition 8.8 rules out one nonzero affine probability update
in its particular four response coordinates. Theorem 4.3 addresses the
strictly broader question of an arbitrary finite encoding and the full
lawful displacement family. Neither claim contradicts the exact nonlinear
maps in §3. The proof also does not settle an arbitrary prescribed finite
menu with its full composition domains merely by naming that menu finite.

## 5. Part B: constructive approximation with exact affine updates

### 5.1 Band parameters and a complete square-root estimate

**Definition 5.1 (Fixed band and approximation parameters).** Fix
$0<a<b<H$ and $\epsilon>0$. Only the continuation operations in this
part are restricted to straight probability legs wholly contained in
$[a,b]$. The current states remain actual native rays in
$\mathcal M_{ab}=[a,b]\times\mathbb T^2$, with arbitrary producing
native prefixes. Put

$$
g(k)=k(H-k),\qquad k_*=\min\{b,\max\{a,H/2\}\},
\qquad G=g(k_*),\qquad g_{\min}=\min\{g(a),g(b)\},
$$

$$
q_A=1-\frac{g_{\min}}G,\qquad q_B=1-\frac ab,
\qquad q=\max\{q_A,q_B\},\qquad C=\sqrt{4G+Zb}.
$$

Completing the square gives
$g(k)=H^2/4-(k-H/2)^2$. Thus the closest point in the band to $H/2$
is $k_*$ and a farthest point is an endpoint. Consequently

$$
0<g_{\min}\le g(k)\le G\le H^2/4,
\qquad 0\le q_A<1,\qquad 0<q_B\le q<1.
$$

Define the polynomials

$$
t_A(k)=1-\frac{g(k)}G\in[0,q_A],\qquad
t_B(k)=1-\frac kb\in[0,q_B]\qquad(k\in[a,b]).
$$

Their degrees are two and one, and all denominators are positive.

**Lemma 5.2 (Square-root series and uniform tail).** Define real
coefficients $c_j$ by

$$
c_0=1,\qquad (j+1)c_{j+1}=\left(j-\frac12\right)c_j
\quad(j\ge0),\qquad S_m(t)=\sum_{j=0}^m c_jt^j.
$$

For $|t|<1$,

$$
\sqrt{1-t}=\sum_{j=0}^{\infty}c_jt^j.
$$

For every integer $m\ge0$ and $0\le t\le q<1$,

$$
|S_m(t)-\sqrt{1-t}|
 \le\frac{q^{m+1}}{2(1-q)}.
$$

**Proof.** The recurrence gives $c_1=-1/2$. For $j\ge1$ its multiplier
$(j-1/2)/(j+1)$ lies strictly between zero and one, so
$|c_j|\le1/2$ for all $j\ge1$. On each $|t|\le\rho<1$ the series
therefore converges absolutely and uniformly by a geometric majorant.
For $0<\rho<1$ its derivative series also converges uniformly, because

$$
\sum_{j=1}^{\infty}j\rho^{j-1}=\frac1{(1-\rho)^2}.
$$

To justify this majorant without differentiating an infinite series, multiply
two geometric series of nonnegative terms. The coefficient at
$\rho^{j-1}$ counts the $j$ pairs of nonnegative integers with sum $j-1$.
Finite triangular sums are bounded by finite square sums and every finite
square is contained in a larger triangle. Taking their increasing limits
gives the displayed identity from
$\sum_{j\ge0}\rho^j=(1-\rho)^{-1}$, itself the limit of the finite
geometric-sum identity. The coefficient bound now supplies the derivative
majorant.

Let $F$ be the series sum. Each partial sum satisfies
$F_N(t)=1+\int_0^t F_N'(x)\,dx$. Uniform convergence of the functions
and derivative series on every such compact interval permits passage to
the limit in this identity. The fundamental theorem of calculus then
justifies differentiating $F$ there. Applying the coefficient recurrence
to the convergent series gives

$$
(1-t)F'(t)=-\frac12F(t),\qquad F(0)=1.
$$

Indeed the constant coefficient is $c_1=-c_0/2$, and the coefficient of
$t^j$ for $j\ge1$ is $(j+1)c_{j+1}-jc_j=-c_j/2$. Hence

$$
\frac{d}{dt}\left(\frac{F(t)^2}{1-t}\right)
 =\frac{2F(t)F'(t)(1-t)+F(t)^2}{(1-t)^2}=0.
$$

At zero this quotient is one, so $F(t)^2=1-t$ on $(-1,1)$.
Continuity, nonvanishing and $F(0)=1$ select the positive square root.
Finally $m+1\ge1$, so for $0\le t\le q$,

$$
|S_m(t)-F(t)|\le\frac12\sum_{j=m+1}^{\infty}q^j
 =\frac{q^{m+1}}{2(1-q)}.
$$

The last equality is the limit of
$q^{m+1}(1-q^N)/(1-q)$ as $N\to\infty$. This proves both the identity
and the uniform tail on the required domain. $\square$

### 5.2 Finite features, their actual image and the fixed decoder

**Definition 5.3 (Explicit polynomials and encoding).** For $m\ge0$ put

$$
P_m(k)=2\sqrt G\,S_m\left(1-\frac{k(H-k)}G\right),\qquad
Q_m(k)=2\sqrt{Zb}\,S_m\left(1-\frac kb\right).
$$

These are real polynomials of degrees at most $2m$ and $m$. Write their
monomial expansions, allowing zero coefficients, as

$$
P_m(k)=\sum_{j=0}^{2m}p_{m,j}k^j,\qquad
Q_m(k)=\sum_{j=0}^m q_{m,j}k^j.
$$

The recurrence and finite compositions specify all these fixed coefficients.
Define

$$
E_m(k,\alpha,\beta)
 =(K,\mathbf a_0,\ldots,\mathbf a_{2m},
          \mathbf b_0,\ldots,\mathbf b_m),
\qquad
K=k,\quad \mathbf a_j=k^jU(\alpha),\quad
\mathbf b_j=k^jU(\beta).
$$

Each bold block has two real coordinates. Thus the stored dimension is

$$
n_m=1+2(2m+1)+2(m+1)=6m+5.
$$

Use the single fixed linear decoder, with zero offset,

$$
L_m(K,(\mathbf a_j),(\mathbf b_j))
 =D\left(\sum_{j=0}^{2m}p_{m,j}\mathbf a_j,
         \sum_{j=0}^m q_{m,j}\mathbf b_j\right).
$$

It ignores $K$. In particular the decoder is a fixed linear matrix on
stored features, not a nonlinear polynomial evaluation on the height
coordinate at readout time. Its encoded output is

$$
\widehat y_m(k,\alpha,\beta)
 =D(P_m(k)U(\alpha),Q_m(k)U(\beta)).
$$

**Proposition 5.4 (Exact encoded source image).** The image of $E_m$ is
exactly

$$
\begin{aligned}
\mathscr S_m=\{(K,(\mathbf a_j),(\mathbf b_j)):\;&K\in[a,b],
\quad\|\mathbf a_0\|=\|\mathbf b_0\|=1,\\
&\mathbf a_j=K^j\mathbf a_0\quad(0\le j\le2m),\\
&\mathbf b_j=K^j\mathbf b_0\quad(0\le j\le m)\}.
\end{aligned}
$$

The encoder is injective on the actual current rays, including when $m=0$.

**Proof.** Every encoded ray satisfies the equations. Conversely each unit
pair is $U(\alpha)$ or $U(\beta)$ for a unique circle class. Together
with $k=K$, the displayed equations give exactly $E_m(k,\alpha,\beta)$.
Proposition 1.3 realizes that ray using the original controls. The coordinates
$K,\mathbf a_0,\mathbf b_0$ also prove injectivity. For $m=0$ these
three blocks are still present, so the argument is unchanged. All features
are functions of the actual current ray, and Proposition 2.3 even expresses
them as mathematical functions of its exact ideal output. No auxiliary
hidden observer or additional source state is introduced. $\square$

### 5.3 Exact affine updates and the source guard

**Proposition 5.5 (All real probability displacements).** For every real
$s$, define one affine map $U_s$ on the entire feature space by

$$
\begin{aligned}
K'&=K+s,\\
\mathbf a_j'&=\sum_{\ell=0}^j\binom j\ell s^{j-\ell}\mathbf a_\ell
                       &&(0\le j\le2m),\\
\mathbf b_j'&=\sum_{\ell=0}^j\binom j\ell s^{j-\ell}\mathbf b_\ell
                       &&(0\le j\le m).
\end{aligned}
$$

Its coefficients are independent of the current state; its only affine
offset is $s$ in the $K$ coordinate. The exact lawful source guard is

$$
\mathscr G_{m,s}=\{z\in\mathscr S_m:a\le K+s\le b\}.
$$

For every $(k,\alpha,\beta)\in\mathcal M_{ab}$ with $k+s\in[a,b]$,

$$
U_sE_m(k,\alpha,\beta)=E_m(k+s,\alpha,\beta)
$$

exactly. In particular $U_s$ preserves the actual source image on this
guard, and $U_{-s}$ returns the original encoded state.

**Proof.** Expand $(k+s)^j$ by choosing which $\ell$ of its $j$ factors
contribute $k$ and which contribute $s$. There are $\binom j\ell$ such
choices, so substitution of the encoded features gives

$$
\mathbf a_j'=(k+s)^jU(\alpha),\qquad
\mathbf b_j'=(k+s)^jU(\beta).
$$

The height update is also exact, which proves the identity. This finite
binomial expansion has no truncation error: translation preserves the
stored polynomial degree.

On $\mathscr S_m$ the current height already lies in $[a,b]$. The
original segment $K+ts$ stays in that closed interval for every
$0\le t\le1$ if and only if $K+s\in[a,b]$, by convexity and endpoint
necessity. This proves precisely the stated guard. Since $a>0$ and $b<H$,
every such segment has full native support. It includes both band boundaries,
both displacement signs and the endpoint-to-endpoint legs. For
$|s|>b-a$ the guard is empty; the affine formula still exists. There is no
finite-menu restriction. The identity and its counterpart for $-s$ prove
image preservation and return. The guard is a guard on the characterized
source image, not a claim that an arbitrary off-image feature vector is a
native state. $\square$

### 5.4 Error, sufficient dimension and boundary margin

**Theorem 5.6 (Uniform original-output error).** For every $m\ge0$,

$$
\sup_{x\in\mathcal M_{ab}}\|L_mE_m(x)-y(x)\|_2
 \le C\frac{q^{m+1}}{1-q}.
$$

**Proof.** By Definition 5.1 the exact radii are

$$
A(k)=2\sqrt G\sqrt{1-t_A(k)},\qquad
B(k)=2\sqrt{Zb}\sqrt{1-t_B(k)},
$$

with $t_A(k),t_B(k)\in[0,q]$. Lemma 5.2, with
$R_m=q^{m+1}/(1-q)$, therefore gives

$$
|P_m(k)-A(k)|\le\sqrt G\,R_m,\qquad
|Q_m(k)-B(k)|\le\sqrt{Zb}\,R_m.
$$

Both phase pairs have norm one. Applying the exact original decoder norm
from Lemma 2.2 yields

$$
\begin{aligned}
\|\widehat y_m-y\|_2^2
 &=4(P_m(k)-A(k))^2+(Q_m(k)-B(k))^2\\
 &\le(4G+Zb)R_m^2.
\end{aligned}
$$

This includes all four bottom-edge pairs and the middle-reference pair in
their original scale. Preparation rotations disappear from this norm only
because they are orthogonal. The bound is uniform over the closed band and
both entire phase circles. $\square$

**Corollary 5.7 (Explicit precision and margin bounds).** For $x>0$ set
$\log_+(x)=\max\{0,\log x\}$, and choose

$$
m=\left\lceil
 \frac{\log_+\!\bigl(C/[\epsilon(1-q)]\bigr)}{\log(1/q)}
 \right\rceil.
$$

This finite nonnegative integer gives uniform error at most $\epsilon$ and
the sufficient feature dimension

$$
n=6\left\lceil
 \frac{\log_+\!\bigl(C/[\epsilon(1-q)]\bigr)}{\log(1/q)}
 \right\rceil+5.
$$

With the native boundary margin and a source constant

$$
\eta=\min\{a,H-b\}>0,\qquad C_0=\sqrt{H^2+ZH},
$$

the same choice satisfies

$$
n\le6\left\lceil
 \frac H\eta\log_+\!\left(\frac{C_0H}{\epsilon\eta}\right)
 \right\rceil+5.
$$

**Proof.** Since $0<q<1$, the denominator $\log(1/q)$ is positive.
If $C/[\epsilon(1-q)]>1$, the ceiling gives
$m\log(1/q)\ge\log(C/[\epsilon(1-q)])$, hence
$q^m\le\epsilon(1-q)/C$. Theorem 5.6 bounds the error by
$\epsilon q\le\epsilon$. If the ratio is at most one, $m=0$ and
$Cq/(1-q)\le\epsilon q\le\epsilon$. This covers large tolerances
and the smallest permitted degree as well as the small-tolerance regime.

The inequalities $a<b$ imply $0<\eta<H/2$, and the band is contained
in $[\eta,H-\eta]$. For its every point,

$$
g(k)-\eta(H-\eta)=(k-\eta)(H-\eta-k)\ge0.
$$

Consequently $g_{\min}\ge\eta(H-\eta)$ and $G\le H^2/4$, so

$$
1-q_A=\frac{g_{\min}}G
 \ge\frac{4\eta(H-\eta)}{H^2}\ge\frac{2\eta}H,
\qquad
1-q_B=\frac ab\ge\frac\eta H.
$$

Taking the smaller gives $1-q\ge\eta/H$. Moreover $C\le C_0$ because
$4G\le H^2$ and $b\le H$, and

$$
\log(1/q)=\int_q^1\frac{dt}{t}\ge1-q\ge\frac\eta H.
$$

Monotonicity of $\log_+$ now gives

$$
\frac{\log_+\!\bigl(C/[\epsilon(1-q)]\bigr)}{\log(1/q)}
 \le\frac H\eta\log_+\!\left(\frac{C_0H}{\epsilon\eta}\right).
$$

Monotonicity of the ceiling proves the dimension bound. For fixed positive
band and fixed source this is an $O(\log(1/\epsilon))$ sufficient dimension
as $\epsilon\downarrow0$, with the displayed constants. This is an output
tolerance estimate, not a bit-precision or conditioning estimate. No lower
bound, optimal width or sharp margin rate is asserted. $\square$

### 5.5 Arbitrary finite persistence and nonaccumulation

**Theorem 5.8 (Exact affine probability continuation with approximate
outputs).** For the choice in Corollary 5.7, the encoder $E_m$, the fixed
linear decoder $L_m$ and every affine map $U_s$ satisfy the following
joint contract on the original current-ray source $\mathcal M_{ab}$:

1. The output error is at most $\epsilon$ uniformly in the original
   ten-coordinate Euclidean norm.
2. Every straight probability leg wholly contained in the closed band has
   an exact state-independent affine encoded update, on exactly the guard
   of Proposition 5.5.
3. From exact initialization, every finite valid sequence remains exactly
   encoded at every stage and throughout every leg, with the same error
   bound independent of sequence length.

**Proof.** The first two statements are Theorem 5.6, Corollary 5.7 and
Proposition 5.5. For the third, let
$x_0=(k^{(0)},\alpha,\beta)$ be any actual current ray in the band and
initialize $z^{(0)}=E_m(x_0)$ exactly. Let $s_1,\ldots,s_N$ be any
finite sequence such that

$$
k^{(i)}=k^{(i-1)}+s_i\in[a,b]\qquad(1\le i\le N).
$$

With $k^{(0)}\in[a,b]$, convexity makes these conditions equivalent to
lawfulness of all the complete straight segments within the band. Define
$z^{(i)}=U_{s_i}z^{(i-1)}$. Induction using the exact update identity gives

$$
z^{(i)}=E_m(k^{(i)},\alpha,\beta)
\qquad(0\le i\le N).
$$

The uniform current-output estimate therefore yields

$$
\|L_m z^{(i)}-y(k^{(i)},\alpha,\beta)\|_2\le\epsilon
\qquad(0\le i\le N).
$$

During the $i$th leg apply the same identity with displacement $ts_i$,
$0\le t\le1$, from $z^{(i-1)}$. It gives the exact encoded intermediate
ray and the same output bound. No bound on $N$, total variation or the
signs of the displacements is required. Because the identities hold
pointwise for every lawful $s$, they also apply to state-selected sequences
once their actual successive guards hold.

Only the output function is approximated. The latent state never acquires
approximation error in this theorem, and an approximate output is never
substituted for an encoded state. Thus the bound is applied afresh at each
exactly encoded current ray and does not accumulate with the number of
steps. This argument assumes exact initialization and exact real arithmetic.
$\square$

## 6. Mathematical scope, reuse and remaining questions

The same fixed preparation and native negative-phase ODE underlie both
parts. The full phase circles in Part B are already reachable current rays
by Proposition 1.3; they do not enlarge the control menu. Its initialization
may be at any such current ray in the band. If the original preparation
height lies outside the band, a lawful original prefix can first produce
that state. No band-confined probability path starting outside the band is
asserted. The approximation theorem begins with an exact encoding of its
specified initial current ray.

The four-coordinate image $\mathscr Z$ and the larger feature image
$\mathscr S_m$ both represent actual native states exactly. The approximate
decoded vector $L_mE_m(x)$ need not itself lie in the exact output image
$D\mathscr Z$. This is permitted by the positive output tolerance and does
not change the state, its probability law, or its source-image guard.
Corollary 4.5 rules out zero tolerance in every finite dimension even on
the same closed band. Section 3 separately gives finite exact nonlinear
realization, including every prescribed native continuation under its
all-times guard.

No affine closure or approximation theorem for phase legs or simultaneous
phase/probability controls is included in Part B. No guarantee here concerns
perturbed initialization, noisy measurement, floating-point updates,
numerical conditioning, a chosen neural activation, implementation by a
neural network, training, sample acquisition, runtime or memory cost.
The feature dimension is an explicit sufficient dimension in exact real
mathematics, not an optimal network width. The transparent formulas specify
what a latent representation and its updates accomplish under a declared
task; they do not themselves supply a learning or physical interface.

The source-specific advance in Part A is the passage from the parent's
particular four-coordinate obstruction to every finite arbitrary encoder,
including encoders of histories and both affine offsets. Its engine is the
classical finite-span argument and Vandermonde interpolation, proved locally
in §4. Engert's finite-dimensional translation-invariant-space theory
([doi:10.2140/pjm.1970.32.333](https://doi.org/10.2140/pjm.1970.32.333))
provides related classical context; no global translation-space theorem,
measurability assumption or external classification is used as a premise.

Part B combines the same native output factorization with classical
square-root power series, geometric tail estimates and polynomial closure
under translation. Their needed statements and proofs are given in §5.
The source-specific composition is the explicit $6m+5$ encoding, its exact
native guard and source image, the original ten-output constant
$\sqrt{4G+Zb}$, the displayed accuracy and margin bounds, and persistence
for arbitrary finite valid probability sequences. These are ordinary
mathematical proofs; no worldwide priority, exhaustive literature search or
formal verification is claimed.

The necessary or optimal approximation dimension, sharper margin estimates,
other action menus with their full composition domains, and an extension
of Part B to phase operations are not settled here. The separate original
alternative of an attainer at some finite $N$ versus a strict gap for every
finite $N$ remains open. No implication connecting that optimization
alternative to this affine-realization contract has been established.
Arbitrary finite sequence length in Theorem 5.8 is not finite-$N$
attainment, and the all-finite affine obstruction is not a strict-gap proof
for that other problem. The broader machine-learning white-box objective
retains its unsupplied acquisition, implementation and task-transfer bridges.

## 6.99 追加锚
