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

## 7. Sharp approximation with exact affine phase continuation

### 7.1 The band contract and its native source

**Definition 7.1 (Affine continuation with approximate original readout).**
Keep Definition 1.1, including arbitrary fixed preparation phases and
$k_0\in(0,H)$, and fix $0<a<b<H$. The current source is
$\mathcal M_{ab}=[a,b]\times\mathbb T^2$ of actual rays, in the
$(k,\alpha,\beta)$ coordinates of Lemma 1.2. Write $P_s=T_s$ for the
straight probability command of Proposition 3.1. The two relative commands
are

$$
P_s(k,\alpha,\beta)=(k+s,\alpha,\beta),
\qquad \operatorname{dom}P_s=\{(k,\alpha,\beta)\in\mathcal M_{ab}:a\le k+s\le b\},
$$

$$
Q_t(k,\alpha,\beta)=
 \left(k,\alpha+\frac t2,\beta+\left(\frac12-\frac kr\right)t\right),
\qquad \operatorname{dom}Q_t=\mathcal M_{ab}.
$$

Here $s,t$ are real numbers. They prescribe respectively
$(\dot k,\dot\chi)=(s,0)$ and $(0,t)$ on a unit interval. The angles are
circle classes; the commanded increment $t$ is not reduced modulo
$2\pi$. Every finite word whose successive guards hold is included, with
no uniform bound on word length or total phase variation.

For $\epsilon\ge0$, the contract asks for a finite integer $n\ge0$,
an arbitrary function $E:\mathcal M_{ab}\to\mathbb R^n$, a fixed affine
readout $c+D_*z$ into the original ten outputs of Definition 2.1, and,
for every real $s,t$, fixed affine maps

$$
\mathcal U_s(z)=A_sz+b_s,\qquad
\mathcal V_t(z)=C_tz+d_t
$$

such that

$$
\sup_{x\in\mathcal M_{ab}}\|c+D_*E(x)-y(x)\|_2\le\epsilon,
$$

$$
E(P_sx)=\mathcal U_sE(x)\quad(x\in\operatorname{dom}P_s),
\qquad
E(Q_tx)=\mathcal V_tE(x)\quad(x\in\mathcal M_{ab}).
$$

The matrices and offsets may depend on the fixed source, band, preparation
and prescribed command, but not on the current height, phases or producing
history. Both readout and update offsets are allowed. No regularity,
boundedness or injectivity of $E$ is assumed, nor any regularity in the
command parameter or ambient matrix group law. Approximate outputs may be
arbitrary vectors of $\mathbb R^{10}$. There is no external height
selector choosing the update matrix.

The contract starts from exact initialization at a band state. If the
preparation lies outside the band, lawful original positive-fiber prefixes
may first enter it; no band-confined history is asserted to start outside
the band. Exact initialization and updates mean exact real arithmetic.

**Proposition 7.2 (Full band reachability and actual relative commands).**
The source in Definition 7.1 is precisely the full band of native current
rays. If $k_0\in[a,b]$, all these rays have band-confined producing
histories. Otherwise they have a phase-free positive-fiber entry followed
by such a history. The displayed $P_s,Q_t$ are the actual original
relative commands on this source.

**Proof.** From Definition 1.1,

$$
I(k)=\frac2k+\frac2{H-k}=\frac r{k(H-k)},\qquad
w_+(k)=\frac12-\frac kr,\qquad w_-(k)=-\frac kr.
$$

Consequently the phase increments, not the arbitrary preparation phases,
satisfy $h=(u,v,0,v,u)$. Lemma 1.2 gives

$$
\alpha=u-v,\qquad\beta=u,\qquad
u=\beta,\quad v=\beta-\alpha,\qquad
d\alpha=\tfrac12d\chi,\quad
d\beta=(\tfrac12-k/r)d\chi.
$$

The integer coordinate changes are inverse on $\mathbb T^2$.
The positive middle amplitude $\sqrt Z$ fixes the common ray phase;
the other positive amplitudes distinguish both circles. Thus these
coordinates impose no extra parity quotient or closed-loop condition.
Integrating along the two straight legs gives exactly $P_s,Q_t$.

For the band version of Proposition 1.3, choose $k_*\in[a,b]$ and
$k_1\in[a,b]$ with $k_1\ne k_*$. Take $k_*=k_0$ when preparation is
in the band; otherwise reach $k_*$ by a probability leg at fixed $\chi$.
For arbitrary target real representatives $u,v$, put

$$
L=2(u-v),\qquad
u_L=(\tfrac12-k_*/r)L,\qquad v_L=-(k_*/r)L,
\qquad q=u-u_L=v-v_L.
$$

The chronological rectangle
$P_{k_1-k_*},Q_A,P_{k_*-k_1},Q_{-A}$ adds
$-A(k_1-k_*)/r$ to both groups. Choose
$A=-rq/(k_1-k_*)$, then execute $Q_L$ at $k_*$ and a probability leg
to the desired $k\in[a,b]$. The endpoint increments are exactly $u,v$.
Every probability segment after entry lies between band points, every
phase leg has finite variation, and the whole history is finite.
Conversely the native ODE preserves the displayed group equalities.
This proves exact reachability, rather than density or closure of a
reachable subset. Band endpoints remain strictly inside the positive
fiber. $\square$

**Lemma 7.3 (Original-output metric for the phase problem).** With the
notation of Lemma 2.2,

$$
y(k,\alpha,\beta)=D(A(k)U(\alpha),B(k)U(\beta)),
\qquad A(k)=2\sqrt{k(H-k)},\quad B(k)=2\sqrt{Zk},
$$

and

$$
\|D(v,w)\|_2^2=4\|v\|_2^2+\|w\|_2^2.
$$

The $02$ projection followed by $R_{-\delta_{02}}$, with its real
plane identified isometrically with $\mathbb C$, is a norm-one map
$\pi:\mathbb R^{10}\to\mathbb C$ satisfying
$\pi y=B(k)e^{i\beta}$.

**Proof.** The negative amplitude convention makes the doubled coherence
pair $2\sqrt{p_ip_j}U(\delta_{ij}+h_i-h_j)$. The five increment
differences in their original order are
$\alpha,\beta,\alpha,-\alpha,-\alpha$. Thus the five blocks before the
fixed preparation rotations are $(v,w,v,Jv,Jv)$, where
$v=A(k)U(\alpha)$ and $w=B(k)U(\beta)$.
Each of the four copies of $v$ contributes its squared norm;
the preparation rotations and $J$ are orthogonal. The $02$ block is
exactly the asserted complex response. All ten coordinates, their factor
of two and their Euclidean metric are retained. $\square$

### 7.2 A lower bound without encoder regularity

**Theorem 7.4 (Native phase approximation floor).** Every model in
Definition 7.1 satisfies

$$
\epsilon\ge B(b)=2\sqrt{Zb}.
$$

For this necessary bound, all probability-update requirements may be
deleted. It even suffices to require one nonzero phase command $Q_{t_0}$
on the full source, with its finite repetitions.

**Proof.** Suppose $\epsilon<B(b)$ and take the actual reachable rays
$x_k=(k,0,0)$ for $k\in[a,b]$. Put $e_j(k)=E_j(x_k)$ and

$$
W=\operatorname{span}_{\mathbb C}\{1,e_1,\ldots,e_n\}.
$$

After a fixed relative phase command $Q_t$, the decoded complex $02$
prediction is

$$
f_t(k)=\pi\bigl(c+D_*(C_tE(x_k)+d_t)\bigr)\in W.
$$

The constant function absorbs both affine offsets. The true response is

$$
F_t(k)=B(k)e^{ic_0(k)t},\qquad c_0(k)=\frac12-\frac kr,
$$

so exact encoded continuation and the uniform original-output error imply

$$
|f_t(k)-F_t(k)|\le\epsilon,\qquad
\|f_t\|_\infty\le B(b)+\epsilon.
$$

An encoder coordinate need not be bounded. Instead set

$$
W_{\rm bd}=\{f\in W:\sup_{k\in[a,b]}|f(k)|<\infty\}.
$$

This is a complex vector subspace of dimension at most $n+1$,
with its genuine supremum norm, and it contains every $f_t$.

Choose $q\in[a,b)$ with $B(q)>\epsilon$; this is possible by
continuity and $B(b)>\epsilon$. Put

$$
T=\frac{2\pi r}{b-q},\qquad t_j=jT\quad(j=0,1,2,\ldots).
$$

For $j\ne l$, the interval of values of
$(t_j-t_l)c_0(k)$ on $[q,b]$ has length $2\pi|j-l|$.
Every closed interval of length at least $2\pi$ contains an odd multiple
of $\pi$. At a corresponding height the two true responses are
antipodal, giving

$$
\|f_{t_j}-f_{t_l}\|_\infty
 \ge2(B(q)-\epsilon)>0.
$$

This is an infinite, uniformly separated family in a norm-bounded
subset of the finite-dimensional space $W_{\rm bd}$.

For completeness, total boundedness here requires no regularity of
functions of $k$. If $v_1,\ldots,v_d$ is a basis of $W_{\rm bd}$,
then

$$
N(\lambda)=\left\|\sum_{i=1}^d\lambda_i v_i\right\|_\infty
$$

is continuous on $\mathbb C^d$, because differences are at most
$\sum_i|\lambda_i-\mu_i|\|v_i\|_\infty$.
For $d>0$, it is positive on the Euclidean unit sphere by linear
independence. The sphere is compact, so its minimum $\mu$ is positive.
Homogeneity gives $N(\lambda)\ge\mu\|\lambda\|_2$. A bounded set in
$W_{\rm bd}$ therefore has bounded coefficient vectors and lies in
the continuous image of a compact coefficient ball. That image is
compact and hence has a finite cover by balls of any positive radius.
Balls of radius less than one third of the displayed separation contain
at most one member of the separated family, a contradiction.
For $d=0$ the space consists only of zero and cannot contain that
separated family either.

Each $Q_{t_j}$ is a separately finite lawful history; no infinite
execution is used. To use just one nonzero $t_0$, choose a positive
integer $M$ with

$$
M|t_0|(b-q)/r\ge2\pi
$$

and replace $Q_{t_j}$ by $jM$ repetitions of $Q_{t_0}$.
Its native increment is $jMt_0$, and the corresponding iterate of one
affine map is still affine. The predictions still lie in the same
$W_{\rm bd}$ and have the same uniform bound. For distinct $j,l$,
the frequency interval has length at least $2\pi$, giving the same
contradiction. No group law on the ambient feature space, inverse
matrix, or command-parameter continuity is needed. $\square$

**Corollary 7.5 (Arbitrary producing-history features).** The same
necessary floor holds if the finite encoder is a function of the entire
producing history, the fixed affine readout is uniformly accurate on
all allowed histories, and one state-independent affine append map
implements each required phase command.

**Proof.** If preparation is in the band, let $H_k$ be its phase-free
probability prefix to $k$. Otherwise first use one phase-free
positive-fiber entry to $k_*\in[a,b]$ and then the band probability
prefix to $k$. These histories all have zero phase increments.
Define $e_j(k)=E_j(H_k)$ and append the same $Q_t$ to every $H_k$.
The actual response is again $B(k)e^{ic_0(k)t}$, while the affine
append rule puts its prediction in
$\operatorname{span}_{\mathbb C}\{1,e_1,\ldots,e_n\}$.
The bounded-readout subspace, separated packing and norm argument
of Theorem 7.4 apply verbatim. Iterated affine appending also gives
the one-command version. No two histories with the same current
ray are identified in this argument. The outside-band case explicitly
uses initialization after lawful entry. $\square$

### 7.3 An anchored polynomial attaining the floor

**Lemma 7.6 (Explicit derivative approximation with endpoint slack).**
Put

$$
\ell=b-a,\qquad g(k)=k(H-k),\qquad
g_{\min}=\min\{g(a),g(b)\},\qquad
K=\frac{H^2}{2g_{\min}^{3/2}},
$$

$$
m=\max\left\{1,\left\lceil\frac{K^2(b-a)^3}{4Z}\right\rceil\right\},
\qquad d=m+1,\qquad \zeta=\frac{K\ell}{2\sqrt m}.
$$

There is an explicitly specified polynomial $\Pi_m$ of degree at most
$d$ such that

$$
\Pi_m(b)=A(b),\qquad
|\Pi_m(k)-A(k)|\le\zeta(b-k)\quad(a\le k\le b),
\qquad \zeta^2\ell\le Z.
$$

**Proof.** For $k=(1-t)a+tb$ with $0\le t\le1$, expansion gives

$$
g(k)=(1-t)g(a)+tg(b)+t(1-t)\ell^2\ge g_{\min}>0.
$$

Differentiating the explicit native radius, not an encoder, gives

$$
A'(k)=\frac{H-2k}{\sqrt{g(k)}},\qquad
A''(k)=-\frac{H^2}{2g(k)^{3/2}}.
$$

Thus $A'$ is Lipschitz on the band with constant $K$.
For $t=(k-a)/\ell$, define the Bernstein weights and polynomial

$$
w_j(t)=\binom mj t^j(1-t)^{m-j},\qquad
\nu_j=A'(a+\ell j/m),\qquad
\mathcal B_m(k)=\sum_{j=0}^m\nu_jw_j(t).
$$

At $t=0,1$ the weights mean polynomial evaluations. They are
nonnegative and sum to one by the binomial theorem. Using
$j\binom mj=m\binom{m-1}{j-1}$ gives
$\sum_jj w_j=mt$. For $m\ge2$, using
$j(j-1)\binom mj=m(m-1)\binom{m-2}{j-2}$ gives
$\sum_jj(j-1)w_j=m(m-1)t^2$. For $m=1$ both sides of this last
identity are zero. It follows that, in every allowed case,

$$
\sum_{j=0}^m j^2w_j=m(m-1)t^2+mt,\qquad
\sum_{j=0}^m(j/m-t)^2w_j=\frac{t(1-t)}m.
$$

Lipschitz continuity and the finite Cauchy--Schwarz inequality give

$$
\begin{aligned}
|\mathcal B_m(k)-A'(k)|
&\le K\ell\sum_{j=0}^m w_j|j/m-t|\\
&\le K\ell
 \sqrt{\left(\sum_jw_j\right)
             \left(\sum_jw_j(j/m-t)^2\right)}\\
&=K\ell\sqrt{\frac{t(1-t)}m}\le\zeta.
\end{aligned}
$$

At $t=0$ all weight is at $j=0$; at $t=1$ it is at $j=m$.
Thus $\mathcal B_m(a)=A'(a)$ and $\mathcal B_m(b)=A'(b)$,
without an ambiguous endpoint power convention. Define

$$
\Pi_m(k)=A(b)+\int_b^k\mathcal B_m(v)\,dv.
$$

It is a polynomial of degree at most $m+1$, anchored at $b$.
The fundamental theorem of calculus yields

$$
|\Pi_m(k)-A(k)|
 =\left|\int_b^k(\mathcal B_m(v)-A'(v))\,dv\right|
 \le\zeta(b-k).
$$

The chosen integer $m$ satisfies
$\zeta^2\ell=K^2\ell^3/(4m)\le Z$, including when $m=1$.

Here are exact finite coefficients for the later fixed decoder.
Write $\mathcal B_m(k)=\sum_{h=0}^m\gamma_hk^h$. Expanding the two
finite binomials in

$$
\mathcal B_m(k)=\ell^{-m}\sum_{j=0}^m
 \nu_j\binom mj(k-a)^j(b-k)^{m-j}
$$

gives

$$
\gamma_h=\ell^{-m}\sum_{j=0}^m\nu_j\binom mj
 \sum_{\substack{u+v=h\\0\le u\le j\\0\le v\le m-j}}
 \binom ju\binom{m-j}v(-a)^{j-u}b^{m-j-v}(-1)^v.
$$

Set

$$
\pi_0=A(b)-\sum_{h=0}^m\frac{\gamma_h b^{h+1}}{h+1},
\qquad
\pi_{h+1}=\frac{\gamma_h}{h+1}\quad(0\le h\le m).
$$

Then $\Pi_m(k)=\sum_{j=0}^d\pi_jk^j$.
All samples and coefficients are fixed exact real constants determined
by the band and source; zero leading coefficients are allowed.
The anchored factor $b-k$, rather than merely a constant uniform
polynomial error, supplies the slack needed at the sharp threshold.
$\square$

**Definition 7.7 (Finite equality encoding and fixed coefficient readout).**
Using Lemma 7.6, set

$$
E_*(k,\alpha,\beta)=(\xi,\mathbf f_0,\ldots,\mathbf f_d),
\qquad
\xi=k,\qquad \mathbf f_j=k^jU(\alpha).
$$

The real dimension is $1+2(d+1)=2m+5$.
For an arbitrary feature vector define

$$
M(z)=\sum_{j=0}^d\pi_j\mathbf f_j,\qquad
L_*(z)=D(M(z),0).
$$

This is one fixed linear decoder, with zero affine offset and a zero
column on $\xi$. It reads a fixed linear combination of stored
features; it does not evaluate a polynomial nonlinearly on $\xi$.

**Proposition 7.8 (Actual feature image, fibers and sharp error).**
The exact encoded image is

$$
\mathscr S_*=
 \left\{(\xi,\mathbf f_0,\ldots,\mathbf f_d):
 a\le\xi\le b,\quad \|\mathbf f_0\|_2=1,\quad
 \mathbf f_j=\xi^j\mathbf f_0\ (1\le j\le d)\right\}.
$$

The fibers of this particular encoder consist exactly of the full
$\beta$ circle at fixed $(k,\alpha)$. Its uniform original-output
error is exactly $2\sqrt{Zb}$.

**Proof.** The equations hold for every encoded ray. Conversely
$\mathbf f_0=U(\alpha)$ for a unique circle class, and $k=\xi$;
Proposition 7.2 realizes these values with every $\beta$.
This proves both the image characterization and the fiber statement.
The encoder is bounded, since

$$
\|E_*(k,\alpha,\beta)\|_2^2
 =k^2+\sum_{j=0}^d k^{2j}
 \le b^2+\sum_{j=0}^d b^{2j}.
$$

This is a property of the construction, not a hypothesis in
Theorem 7.4. On the source,
$M(E_*(x))=\Pi_m(k)U(\alpha)$.
By the original metric of Lemma 7.3,

$$
\begin{aligned}
\|L_*E_*(x)-y(x)\|_2^2
 &=4(\Pi_m(k)-A(k))^2+B(k)^2\\
 &\le4\zeta^2(b-k)^2+4Zk\\
 &\le4Z(b-k)+4Zk=4Zb.
\end{aligned}
$$

The last inequality uses $0\le b-k\le\ell$ and $\zeta^2\ell\le Z$.
At $k=b$, the first term is zero and the second is $4Zb$,
for every $\alpha,\beta$. Thus the bound is attained, not merely
approached.

All omitted $\beta$ values remain distinct actual rays in the error
supremum. Their $02$ outputs form a circle of radius $B(k)$ and
diameter $2B(k)$; the decoder uses its center. The zero decoded
$02$ pair is not an output of any positive-support native ray.
Noninjective encoding and approximate outputs outside the native
output image are permissions of Definition 7.1. Adding injectivity
or physical realizability of every decoded vector would remove
this upper witness, while preserving the necessary bound.
$\square$

**Proposition 7.9 (Exact affine operations and saturated guards).**
For every real $s,t$, define ambient affine maps by

$$
\mathcal U_s:\quad
 \xi'=\xi+s,\qquad
 \mathbf f_j'=\sum_{h=0}^j\binom jh s^{j-h}\mathbf f_h
 \quad(0\le j\le d),
$$

$$
\mathcal V_t:\quad
 \xi'=\xi,\qquad
 \mathbf f_j'=R_{t/2}\mathbf f_j
 \quad(0\le j\le d).
$$

Their exact source guards are respectively
$\{z\in\mathscr S_*:a\le\xi+s\le b\}$ and all of $\mathscr S_*$.
They intertwine $P_s,Q_t$ exactly and preserve $\mathscr S_*$
whenever lawful.

**Proof.** On an encoded state the binomial theorem gives

$$
\mathbf f_j'=(k+s)^jU(\alpha).
$$

Thus the first map is precisely $E_*(P_sx)$; its only affine
offset is $s$ in the height coordinate. The second map gives
$k^jU(\alpha+t/2)$, precisely $E_*(Q_tx)$.
The true simultaneous change in $\beta$ under $Q_t$ is present
in the native state and is invisible only because $E_*$ forgets it.

A straight probability segment from a band point stays in $[a,b]$
exactly when its endpoint does, by convexity. Every fixed-height
phase leg stays in the band. These are exactly the stated guards,
and they are constant on every encoder fiber. Thus they are
saturated guards: all actual rays represented by one feature point
agree on lawfulness. No ambiguity is introduced by forgetting
$\beta$. Substitution in the image equations proves preservation.
Zero commands, both signs, and both band endpoints are included.
For $|s|>\ell$ the probability guard is empty; for $|s|=\ell$
the appropriate endpoint-to-endpoint leg is included. The ambient
formulas do not certify arbitrary off-image vectors as native states.
$\square$

**Proposition 7.10 (Native noncommutation and its quotient).**
Whenever its probability legs are lawful, the chronological word
$P_s,Q_t,P_{-s},Q_{-t}$ fixes $k,\alpha$ and changes $\beta$ by
$-st/r$. This generally changes the actual ray, although its
encoded action under $E_*$ is the identity.

**Proof.** The two phase increments in $\alpha$ cancel. Those in
$\beta$ sum to

$$
\left(\frac12-\frac{k+s}{r}\right)t
 -\left(\frac12-\frac kr\right)t=-\frac{st}{r}.
$$

The positive $02$ radius makes this observable unless $st/r$ is
a multiple of $2\pi$. It is not a common-phase gauge of the ray.
The encoded binomial mixing commutes with the common planar
rotation of all blocks, and $E_*$ forgets precisely the changed
circle. Hence the commutator becomes the identity after encoding.
This is an exact action on an allowed quotient, not commutation
of the native controls. $\square$

### 7.4 Every finite prefix and simultaneous controls

**Theorem 7.11 (Sharp threshold and exact-real persistence).**
Definition 7.1 has a finite solution if and only if

$$
\epsilon\ge\epsilon_*:=2\sqrt{Zb}.
$$

The encoding in Definition 7.7 attains equality and stays exactly
encoded at every prefix and every intermediate time of all finite
valid command histories, with the same output error independent
of history length. The same sharp threshold holds if one also
requires exact affine updates for every prescribed simultaneous
native continuation satisfying the all-times band guard.

**Proof.** Necessity is Theorem 7.4. Propositions 7.8 and 7.9 give
existence at equality, and the same model satisfies any larger
tolerance. Starting from $z_0=E_*(x_0)$, the exact next-command
identity gives $z_{j+1}=E_*(x_{j+1})$ whenever
$z_j=E_*(x_j)$ and the next guard holds. Induction gives every
finite prefix. Applying the uniform current-state estimate at
each such prefix proves the error assertion. During a straight
leg the corresponding fractional command $P_{\tau s}$ or
$Q_{\tau t}$, $0\le\tau\le1$, gives the exact intermediate
encoding and the same bound.

For the larger command family, prescribe the original control
velocities on a finite interval $[0,T]$, in Definition 1.1's
regularity class. With $\rho(0)=0$, write

$$
k(\tau)=k+\rho(\tau),\qquad
b_c(\tau)=\dot\chi(\tau),\qquad
\Delta=\rho(T),\qquad L=\int_0^T b_c(\tau)\,d\tau,\qquad
C=\int_0^T\rho(\tau)b_c(\tau)\,d\tau.
$$

The function $\rho$ is continuous and bounded, while $b_c$ is
integrable with finite absolute integral, so $C$ exists. Integration
of the native equations, as in Theorem 3.2, gives

$$
k'=k+\Delta,\qquad
\alpha'=\alpha+\frac L2,\qquad
\beta'=\beta+\left(\frac12-\frac kr\right)L-\frac Cr.
$$

In particular the native mixed-integral term has not been discarded
from the source. The exact encoded endpoint map is

$$
\xi'=\xi+\Delta,\qquad
\mathbf f_j'=
 R_{L/2}\sum_{h=0}^j\binom jh\Delta^{j-h}\mathbf f_h.
$$

Its coefficients depend on the prescribed relative path, not the
starting state or history. The parameter $C$ disappears only after
the allowed $\beta$ quotient. Its exact source guard is

$$
a\le\xi+\rho(\tau)\le b\quad(0\le\tau\le T),
$$

equivalently

$$
a\le\xi+\min_{[0,T]}\rho,\qquad
\xi+\max_{[0,T]}\rho\le b.
$$

Compactness supplies these extrema. Endpoint lawfulness alone is
insufficient for a general nonmonotone path. This guard is again
constant on each encoder fiber. Substitution of the binomial
identity and the native $\alpha'$ formula proves exact endpoint
intertwining. Replacing $T$ by any intermediate time proves exact
encoding and the error bound throughout the path. Finite
concatenation follows by the same induction. The larger family
contains the phase commands of Theorem 7.4, so its lower bound is
unchanged.

For the history-encoder contract of Corollary 7.5, encode each
history by $E_*$ of its actual endpoint. These same identities
give the affine append maps and equality construction.

No approximate decoded output is substituted for an encoded
state in these assertions. Only readout is approximated; exact
initialization and exact real updates preserve the exact feature
point. Thus the readout error does not accumulate. Every asserted
execution has finite duration and finite variation; arbitrary
finite length is not an infinite-execution or limiting-state
claim. $\square$

### 7.5 General fixed means and precise boundaries

**Proposition 7.12 (A separate general-fixed-means necessary floor).**
Fix $0<Z<1$, $r=1-Z$, and $0<X,Y<r$. In the general native
fixed-mean fiber set

$$
p(k)=(r-X-Y+k,\ X-k,\ Z,\ Y-k,\ k),\qquad
J=\bigl(\max\{0,X+Y-r\},\min\{X,Y\}\bigr),
$$

$$
d=(1,-1,0,-1,1)^{\mathsf T},\qquad
I(k)=\frac1{p_0(k)}+\frac1{p_1(k)}
     +\frac1{p_3(k)}+\frac1k,\qquad
w_s(k)=\frac{d_s}{p_s(k)I(k)}.
$$

Use the same native law, arbitrary fixed preparation, original ten
outputs and their Euclidean norm. On any $[a,b]$ strictly inside
$J$, an arbitrary finite encoder with fixed affine original-output
readout and exact state-independent affine phase updates has
uniform error necessarily

$$
\epsilon\ge 2\sqrt{Zp_0(b)}
 =2\sqrt{Z(r-X-Y+b)}.
$$

The conclusion holds in every wall regime. It asserts neither
sharpness nor equality attainment away from the double wall.

**Proof.** The interval $J$ is nonempty: if $X+Y\le r$ its lower
end is zero and its upper end is positive; otherwise
$X+Y-r<X,Y$ because each mean is less than $r$.
The displayed probabilities are positive and sum to one on $J$,
and their derivative is the native tangent $d$.
The coefficient $w_2=0$ fixes the middle phase; $d^{\mathsf T}w=1$
and $p^{\mathsf T}w=0$ follow directly from the displayed sums.
These are the actual native coefficients, with no substituted
frequency family.

For each $k\in[a,b]$, a phase-free probability prefix from the
fixed preparation produces a zero-increment ray $x_k$. If needed,
separate its positive-fiber entry from its band continuation.
Applying $Q_t$ at that height adds $tw(k)$ to the phases.
After removing the fixed $02$ preparation rotation, its actual
response is

$$
F_t(k)=B_0(k)e^{iw_0(k)t},\qquad
B_0(k)=2\sqrt{Z(r-X-Y+k)},\qquad
w_0(k)=\frac1{p_0(k)I(k)}.
$$

The amplitude is positive and strictly increasing on the band.
Only this reachable subset is needed; no extra independent phase
controls or full-torus assertion is required here.

To prove the needed frequency spread on every wall regime, put
$S=X+Y$. Multiplication of $I$ by
$p_0(X-k)(Y-k)k$ gives the positive polynomial on $J$

$$
\begin{aligned}
\mathcal Q(k)
 &=(X-k)(Y-k)(r-S+2k)+k(r-S+k)(S-2k)\\
 &=XY(r-X-Y)+2XYk-rk^2.
\end{aligned}
$$

Consequently

$$
w_0(k)=\frac{k(X-k)(Y-k)}{\mathcal Q(k)}.
$$

The denominator is nonzero on $J$. If this rational function
were constant on any nonempty open subinterval, clearing its
denominator would give a polynomial identity. The numerator has
cubic coefficient one, whereas the denominator has degree at
most two, so that identity is impossible. This argument also
covers $X=Y$, $X+Y=r$, their intersection, and neither wall;
cancellation of common factors cannot make the displayed
polynomial identity possible. Thus $w_0$ is continuous and
nonconstant on every positive-width subinterval. No support
boundary is approached or executed for this conclusion.

If $\epsilon<B_0(b)$, choose $q\in[a,b)$ with
$B_0(q)>\epsilon$. The image $w_0([q,b])$ is a closed interval
$[\omega_-,\omega_+]$ of positive width, by continuity,
the intermediate value theorem and nonconstancy. Take
$T=2\pi/(\omega_+-\omega_-)$. For distinct integers $j,l\ge0$,
the image of $(j-l)Tw_0$ has length at least $2\pi$ and contains
an odd multiple of $\pi$. At its preimage the true responses
$F_{jT},F_{lT}$ differ by at least $2B_0(q)$.
Both affine offsets are again absorbed by
$\operatorname{span}_{\mathbb C}\{1,E_1(x_k),\ldots,E_n(x_k)\}$.
Their predicted responses belong to its bounded subspace, have
supremum norm at most $B_0(b)+\epsilon$, and are separated by
at least $2(B_0(q)-\epsilon)$. The complete norm argument of
Theorem 7.4 gives the contradiction.

For one nonzero command $t_0$, choose an integer $M>0$ with
$M|t_0|(\omega_+-\omega_-)\ge2\pi$ and use its $jM$ repetitions.
For history encoders use the same canonical probability prefixes.
These give the same proof without frequency monotonicity or
encoder regularity. Only a one-pair lower bound has been proved;
the double-wall upper construction is not transferred to this
different source. $\square$

**Proposition 7.13 (Collapsed band and full-open-domain necessity).**
At a fixed height $a=b=k_*\in(0,H)$ there is an exact finite affine
readout and affine phase-update model on the inherited full phase
torus. In contrast, on the full open double-wall source
$(0,H)\times\mathbb T^2$, the corresponding uniform approximate
contract has the necessary condition
$\epsilon\ge2\sqrt{ZH}$. No full-open-domain equality construction
is asserted here.

**Proof.** At the fixed height store the four response coordinates

$$
z=(A(k_*)U(\alpha),B(k_*)U(\beta)).
$$

The decoder is $D$, and $Q_t$ acts by the two fixed rotations
$R_{t/2}$ and $R_{(1/2-k_*/r)t}$. Only $P_0$ has a nonempty
probability guard; any band-confined simultaneous continuation has
$\rho$ identically zero. This proves exactness, even on the full
initialized torus, hence on any smaller phase subset generated by
controls confined to that height from the start. It does not assert
two-height reachability when there is only one height.

Any single finite model on the full open source restricts to
every positive closed band. Theorem 7.4 therefore gives
$\epsilon\ge2\sqrt{Zb}$ for every $b<H$.
Taking the real supremum gives $\epsilon\ge2\sqrt{ZH}$.
This restriction argument executes no zero-support state.
The constants and degree of Lemma 7.6 depend on the band, so they
supply no single finite equality attainer on the open domain.
$\square$

Part B, specifically Theorem 5.8, still gives arbitrarily small
positive error with exact affine probability updates on the same
positive band and full phase source. Its operation menu omits the
phase-update requirements responsible for Theorem 7.4. The exact
finite nonlinear full-continuation model of Theorem 3.2 is also
compatible. The sufficient dimension $2m+5$ is not an optimal
dimension claim. Neither the lower bound nor its equality witness
supplies finite precision, perturbed-initialization stability,
physical output realizability, measurement acquisition or a
learning guarantee.

## 8. Decoder-free obstruction to lossless affine phase action

### 8.1 A different contract on the same actual rays

**Definition 8.1 (Lossless current-ray affine action).** Keep the fixed
source, arbitrary preparation and positive-width band of Definition 7.1.
For a finite integer $n\ge0$, a lossless current-ray encoding is an
injective function $E:\mathcal M_{ab}\to\mathbb R^n$. The minimal
affine-action requirement considered here is a single affine map

$$
F(z)=Az+c,\qquad E(Q_{4\pi}x)=F(E(x))
 \quad\hbox{for every }x\in\mathcal M_{ab}.
$$

There is no decoder, no output requirement and no
probability-update requirement in this minimal contract.
No regularity of $E$, boundedness of its image, invertibility of $A$
or ambient group law is assumed. The coefficients are fixed across
all current heights and phases and all producing histories.

The domain remains the full native reachable band of
Proposition 7.2. Deleting update requirements does not restrict
the original generation process to powers of one command from one
initial height. The full-menu version would additionally require
affine representatives of every $P_s$ on its lawful domain and
every $Q_t$ on the whole band, with arbitrary offsets.
It contains the minimal contract as a consequence.

**Lemma 8.2 (Actual periods of the real command $4\pi$).**
Let $T=Q_{4\pi}$ and $\rho=k/H\in(0,1)$.
On actual rays, in $(k,u,v)$ coordinates,

$$
T(k,u,v)=(k,u-2\pi\rho,v-2\pi\rho).
$$

For every integer $j\ge1$,

$$
T^jx=x\quad\Longleftrightarrow\quad j\rho\in\mathbb Z.
$$

If $\rho=m/q$ is reduced, every ray at that height has least
positive period $q$; irrational $\rho$ has no positive finite
period. Every positive-width band contains rays with arbitrarily
large prime least periods, at heights strictly inside the band.

**Proof.** The native increments of $Q_{4\pi}$ in $u,v$ are

$$
4\pi\left(\frac12-\frac kr\right)=2\pi(1-\rho),
\qquad -4\pi k/r=-2\pi\rho,
$$

because $r=2H$. On their two circles these equal the displayed
common shift. Repeating gives $-2\pi j\rho$ on both circles.
The positive middle amplitude fixes the common ray phase, and
the positive bottom groups distinguish both circle values, by
Lemma 1.2 and Proposition 1.3. Thus equality of rays is exactly
$j\rho\in\mathbb Z$. Equivalently all bottom amplitudes acquire
the same factor $e^{2\pi ij\rho}$ while the middle amplitude is
unchanged, so the factor must be one. It is not a removable ray
gauge. The period and irrationality conclusions follow immediately.

Given any bound $B$, choose a prime $p>B$ so large that
$p(b-a)/H>1$. Such primes exist: if all primes formed a finite
list, any prime divisor of one plus their product would lie
outside that list. The open interval
$(pa/H,pb/H)$ has length greater than one, so contains an integer
$m$ strictly between its endpoints. For example the least
integer strictly greater than its left endpoint is at most one
above it and hence below the right endpoint. Since $0<a<b<H$,
we have $0<m<p$, so $m/p$ is reduced. The height $k=Hm/p$
lies strictly inside the band and has exact period $p$.
Proposition 7.2 makes each such ray an actual finitely reachable
state from the fixed preparation. $\square$

**Lemma 8.3 (Common exponent on affine periodic points).**
Let $F:\mathbb R^n\to\mathbb R^n$ be any affine map in finite
dimension, and let $S$ be any nonempty subset of its periodic
points. There is one positive integer $N$ such that $F^N$
fixes every point of $\operatorname{aff}(S)$, hence every point
of $S$.

**Proof.** Start with $z_0\in S$ and repeatedly select a point of
$S$ outside the affine hull of those already selected, if one
exists. Each selection increases affine dimension. After at
most $n$ additions this gives $z_0,\ldots,z_d$ with
$d\le n$ and affine hull equal to $\operatorname{aff}(S)$.
Choose a positive period $m_i$ for each selected point and put
$N=\prod_{i=0}^d m_i$. Then $F^N$ fixes each $z_i$.

The offset causes no difficulty: if $F(z)=Az+c$, induction gives

$$
F^N(z)=A^Nz+\sum_{j=0}^{N-1}A^jc,
$$

so the iterate is affine. For any affine combination
$z=\sum_i\lambda_i z_i$ with $\sum_i\lambda_i=1$,

$$
F^N(z)=\sum_i\lambda_i F^N(z_i)=\sum_i\lambda_i z_i=z.
$$

This proves the assertion. It includes singleton sets and
$n=0$, and does not require $S$ to be affine, bounded, regular
or invariant under $F$. No spectrum or ambient inverse is used.
The exponent depends on the map and its periodic points; there
is no bound solely in terms of dimension. For example, planar
rotations through $2\pi/q$ have nonzero points of exact period
$q$ for arbitrarily large $q$ as the map varies. $\square$

**Theorem 8.4 (No finite lossless affine realization of $Q_{4\pi}$).**
Definition 8.1 has no solution in any finite real dimension.
Consequently its full native operation-menu version has no
solution either.

**Proof.** Suppose $E$ is injective and $F$ satisfies the
full-domain one-step identity. Since $T$ is globally lawful,
induction gives

$$
E(T^jx)=F^j(E(x))\quad(j=0,1,2,\ldots)
$$

for every current ray $x$. Put

$$
\mathcal M_{\rm rat}=
 \{(k,\alpha,\beta)\in\mathcal M_{ab}:k/H\in\mathbb Q\},
\qquad S=E(\mathcal M_{\rm rat}).
$$

This set is nonempty. For $x\in\mathcal M_{\rm rat}$, a finite
native period $q$ implies
$F^q(E(x))=E(T^qx)=E(x)$. Thus every point of $S$ is periodic.
Lemma 8.3 supplies one $N\ge1$ fixing all of $S$.
Choose an interior height of prime period $p>N$ by Lemma 8.2
and a ray $x$ there. Then

$$
E(T^Nx)=F^N(E(x))=E(x).
$$

Injectivity forces $T^Nx=x$, contradicting least period $p>N$.
Only finite histories have been used: a finite preparation of
$x$ and finitely many repetitions of the real command $4\pi$.
No probability-update matrix or decoder appears in the proof.

Indeed the proof would already work if $E$ merely distinguished
different points within each of these prime-period cycles.
For a noninjective equivariant encoder, the same argument
forces some distinct points on an appropriate such cycle to
have equal encodings. It does not force an entire $\beta$
circle to collapse, nor classify all possible encoder fibers.
$\square$

### 8.2 Original outputs and the distinction from approximation

**Corollary 8.5 (Any deterministic exact current-output decoder).**
There is no finite current-ray encoder with the affine
$Q_{4\pi}$ identity and a deterministic decoder of its current
encoded state that returns all original ten outputs exactly.
The decoder may be arbitrarily nonlinear or irregular.

**Proof.** The original output separates current rays, as in
Proposition 2.3. Explicitly, remove the fixed preparation
rotations from the $02$ and $01$ blocks to recover

$$
z_\beta=B(k)U(\beta),\qquad z_\alpha=A(k)U(\alpha).
$$

Then $k=\|z_\beta\|_2^2/(4Z)$, and positivity of both radii
recovers the two circle classes by normalization. Finally
$u=\beta$ and $v=\beta-\alpha$ recover the ray. This holds for
arbitrary preparation; it chooses no global real-angle branch.

If $\mathcal R(E(x))=y(x)$ with a single deterministic
current-state decoder $\mathcal R$, equality of two encodings
gives equality of outputs and hence equality of rays.
Thus $E$ is injective, contradicting Theorem 8.4.
The decoder is allowed fixed task parameters but not an
additional current height or producing history input.
$\square$

The static affine-output capacity remains four by Proposition 2.3.
It concerns readout without the affine continuation requirement.
Approximate readout need not force injection, and approximate
equivariance would not give the periodic equalities in Theorem 8.4.
Theorem 7.4 supplies its own quantitative lower bound by a different
argument. No approximation bound follows merely from the
decoder-free period theorem, and the equality construction of
Definition 7.7 is not lossless.

### 8.3 Reduced phase menus and their exact exceptions

**Proposition 8.6 (Every nonzero rational multiple of $4\pi$).**
Replace $Q_{4\pi}$ in Definition 8.1 by $Q_t$ with
$t/(4\pi)\in\mathbb Q\setminus\{0\}$. The same nonexistence
conclusion holds, even when that is the sole required command.

**Proof.** Write $t/(4\pi)=\ell_0/d_0$ with
$\ell_0\in\mathbb Z\setminus\{0\}$ and $d_0$ a positive
integer. If $F$ represents $Q_t$ on all of $\mathcal M_{ab}$,
then $G=F^{d_0}$ represents $Q_{4\pi\ell_0}$ there.
Every rational-height ray is periodic under this source action,
so its encoded image is a nonempty set of periodic points of
$G$. Lemma 8.3 supplies an exponent $N$ fixing that image.

Choose an interior prime-period height $k/H=m/p$ as in
Lemma 8.2 with $p>N$ and $p>|\ell_0|$. For
$Q_{4\pi\ell_0}$, the common circle shift is
$-2\pi\ell_0m/p$, whose least period is $p$ because $p$
divides neither $\ell_0$ nor $m$. Equivariance gives
$E(Q_{4\pi\ell_0}^Nx)=G^N(E(x))=E(x)$, contradicting
injectivity. Negative $\ell_0$ is included; all repetitions
are finite and lawful. Arbitrarily small nonzero rational
steps therefore still have this obstruction. $\square$

**Proposition 8.7 (One irrational step has an irregular two-coordinate
realization).** Fix one $t$ with $t/(4\pi)$ irrational, retain
the full actual-ray band, and require only $Q_t$ and its integer
powers. In ordinary set theory with choice, there is an injective
current-ray encoder into $\mathbb R^2$ for which every such power
acts by an affine translation.

**Proof.** A fixed point of a nonzero integer power $Q_t^j$
would require the $\alpha$ shift $jt/2$ to be a multiple of
$2\pi$, or $jt/(4\pi)\in\mathbb Z$. Irrationality forbids
this. Thus the $\mathbb Z$-action generated by $Q_t$ is free
on the whole band.

Choose one representative $x_O$ from each orbit $O$. Distinct
representatives can be assigned distinct real labels $\lambda_O$.
Here is a cardinality justification: the full source embeds
into $\mathbb R^5$ by
$(k,u,v)\mapsto(k,\cos u,\sin u,\cos v,\sin v)$.
There is an injection of $\mathbb R^5$ into $\mathbb R$.
To see this directly, inject each real coordinate into $(0,1)$
by $x\mapsto(1+x/(1+|x|))/2$, choose its binary expansion
which is not eventually all ones, and interlace the five
binary digit sequences. The resulting sequence is also not
eventually all ones, so has an unambiguous such expansion;
de-interlacing recovers all five coordinates. Restricting this
injection to the chosen representatives gives the labels.
Choice is used for the orbit transversal, with no claim of
measurability or computability.

Every ray has a unique expression $x=Q_t^j x_O$ for one
orbit and one integer $j$. Define

$$
E_{\rm irr}(x)=(\lambda_O,j).
$$

The distinct labels and freeness make this function injective.
For every integer $m$,

$$
E_{\rm irr}(Q_t^m x)=E_{\rm irr}(x)+(0,m).
$$

Thus all integer powers have fixed affine translations.
Once the transversal is fixed, the integer $j$ is a function
of the actual current ray, not an external clock or the
length of a producing history. This construction gives no
regularity, affine original-output decoder, probability
updates, or simultaneous realization of additional irrational
commands. It is a realization of exactly the reduced menu
stated here. $\square$

**Proposition 8.8 (Collapsed band and probability-only lossless action).**
On an inherited full phase torus at one positive height $k_*$,
all phase commands have an injective four-real-coordinate
linear realization. On the full positive-width band,
probability commands alone, together with $Q_0$, have an
injective five-real-coordinate affine realization.

**Proof.** At the collapsed band use

$$
E_{\rm tor}(u,v)=(U(u),U(v)).
$$

This is injective on $\mathbb T^2$, and $Q_t$ is represented
by

$$
R_{(1/2-k_*/r)t}\oplus R_{-k_*t/r}.
$$

Both angles are fixed numbers for the prescribed command.
Only the zero probability displacement has a nonempty band
domain, and its map is the identity. The construction works
on the full initialized torus or any subset reachable when
generation is itself confined to that height. It does not
identify those two generation domains. The exact affine
readout construction at one height is separately given in
Proposition 7.13.

For the full band use

$$
E_0(k,u,v)=(k,U(u),U(v))\in\mathbb R^5.
$$

Equality of these coordinates gives equality of $k$ and both
circle classes, hence of rays. For every $s$, the affine
translation

$$
(\xi,\mathbf u,\mathbf v)\longmapsto
 (\xi+s,\mathbf u,\mathbf v)
$$

represents $P_s$ exactly on $a\le\xi+s\le b$ in the actual
image, and the identity represents $Q_0$.
No output decoder was required in this probability-only
contract. In particular this construction does not contradict
the exact affine-readout obstruction in Corollary 4.5.
$\square$

**Proposition 8.9 (Finite nonlinear coordinates for the full menu).**
The same $E_0$ gives a lossless finite current-state realization
of every native command and every prescribed simultaneous
continuation, with generally nonlinear updates.

**Proof.** The actual image is
$\{\xi\in[a,b],\|\mathbf u\|=\|\mathbf v\|=1\}$.
The probability update is the translation of Proposition 8.8.
A phase command acts by

$$
(\xi,\mathbf u,\mathbf v)\longmapsto
 \left(\xi,
 R_{(1/2-\xi/r)t}\mathbf u,\,
 R_{-\xi t/r}\mathbf v\right).
$$

These functions use the stored current height, require no
external selector and respect both phase circles. Their
dependence on that height makes them generally nonlinear.
For a prescribed simultaneous path with parameters and
all-times guard as in Theorem 7.11, integration or
$u=\beta,\ v=\beta-\alpha$ gives

$$
u'=u+\left(\frac12-\frac kr\right)L-\frac Cr,
\qquad
v'=v-\frac krL-\frac Cr.
$$

The exact feature update is therefore

$$
(\xi,\mathbf u,\mathbf v)\longmapsto
 \left(\xi+\Delta,
 R_{(1/2-\xi/r)L-C/r}\mathbf u,\,
 R_{-\xi L/r-C/r}\mathbf v\right),
$$

under $a\le\xi+\rho(\tau)\le b$ for all times.
It preserves the actual feature image whenever lawful.
Substituting each intermediate upper time limit and composing
finitely many such maps proves exact realization of every
finite valid history. The four-coordinate response realization
of Theorem 3.2 is another finite nonlinear model, with an exact
linear original-output decoder. Neither model asserts affine
full-menu dynamics. $\square$

### 8.4 Ray quotients, lifts and execution quantifiers

**Proposition 8.10 (Retained real lifts are a different affine source).**
On the source $[a,b]\times\mathbb R^2$ retaining real increments
$(u,v)$, the three coordinates $(k,u,v)$ have affine updates for
all native $P_s,Q_t$ and prescribed simultaneous continuations.
These coordinates do not define an encoder of actual current rays.

**Proof.** Before reducing phases modulo $2\pi$, the exact formulas
are

$$
P_s(k,u,v)=(k+s,u,v),
$$

$$
Q_t(k,u,v)=
 \left(k,\ u-\frac tr k+\frac t2,\ v-\frac tr k\right).
$$

For each fixed real command these are affine in the three
coordinates. For a simultaneous path they become

$$
\left(k+\Delta,
 u-\frac Lr k+\frac L2-\frac Cr,
 v-\frac Lr k-\frac Cr\right),
$$

again affine, on the same all-times height guard.
The positive-width reachability construction of Proposition 7.2
realizes arbitrary real representatives as lifted increments,
so these formulas do describe a possible retained-lift source.

On actual rays, however, $(k,u+2\pi,v)$ and $(k,u,v)$ are the
same point while their displayed three coordinates differ.
Thus they are not a function of the ray quotient. Selecting
wrapped representatives introduces state-dependent wrap
changes; the displayed affine formulas on real lifts do not
become affine formulas on those representatives.
A producing-history encoder can retain lifts even when the
current ray returns, and then it is a function of histories,
not a lossless current-ray encoder in Definition 8.1.

Theorem 8.4 cannot be transferred to arbitrary history encoders
by asserting that a returned ray has a returned encoded history.
Corollary 7.5 has a separate finite-function-space proof for
history features with a fixed affine approximate readout.
The retained-lift construction here supplies no such affine
readout below that floor; its usual trigonometric decoding is
nonlinear. These contracts are distinct. $\square$

**Proposition 8.11 (Realification, zero dimension and support scope).**
Theorem 8.4 also excludes finite complex affine lossless
realizations. Its actual-ray conclusion uses full positive
support and does not automatically extend to vanishing-support
sources.

**Proof.** A complex affine map on $\mathbb C^n$ becomes a real
affine map on $\mathbb R^{2n}$ with linear part

$$
\begin{pmatrix}
\operatorname{Re}A&-\operatorname{Im}A\\
\operatorname{Im}A&\operatorname{Re}A
\end{pmatrix}
$$

and offset $(\operatorname{Re}c,\operatorname{Im}c)$.
Injection and the intertwining identity are preserved, so the
real theorem applies. In real dimension zero the target is a
singleton, while the stated source contains distinct rays;
injectivity already fails. The common-exponent proof includes
that dimension. An empty source would be vacuous and a singleton
source could be encoded in dimension zero, but neither is the
source here.

Positivity of $Z$ fixes the common phase, and positivity of
$k,H-k$ makes both grouped phases observable as ray coordinates.
At $k=0$ or $k=H$ one group disappears, and its circle is no
longer a ray coordinate. At $Z=0$, in the corresponding
limiting bottom action the common bottom shift of $Q_{4\pi}$
is a common phase of the remaining support and becomes
ray-trivial. At $Z=1$ there is no positive interval $0<k<H$.
These changes prevent treating those boundary tasks as instances
of this proof. The approximation constants of Lemma 7.6 also
require the positive interior band. $\square$

All witness heights in Lemma 8.2 are strictly between $a$ and $b$.
Thus the lossless obstruction also holds with open or half-open
band conventions, using their corresponding interval guards.
Probability maps have only partial native domains; an empty
domain imposes no condition. No partial-domain identity is
promoted to an ambient affine group law. The single obstructing
phase command, in contrast, is globally lawful on the stated
source.

Every exponent, selected affine-spanning set, prime cycle and
preparing history in the lossless proof is finite. Their sizes
may depend on a proposed realization. A restriction on described
execution budgets does not remove the algebraic implication

$$
E(Tx)=F(E(x))\ \hbox{on all of }\mathcal M_{ab}
 \quad\Longrightarrow\quad
E(T^jx)=F^j(E(x))\ \hbox{for every finite }j.
$$

Consequently a finite-horizon reformulation must change the
domain or identities to which it applies; merely keeping the
same full-domain one-step contract and declaring that only a
bounded number of steps will be run does not evade Theorem 8.4.
The same care applies to the repetition argument of Theorem 7.4.
Neither theorem executes an infinite history or proves a
finite-horizon realization for an altered contract.

## 9. Mathematical contribution and unresolved boundaries

The sharp approximation result combines classical finite
function-space arguments, total boundedness in finite-dimensional
normed spaces, Bernstein polynomial weights and moments, and
finite polynomial closure under translation. Their needed
forms are proved in §7. The source-specific result is the exact
threshold $2\sqrt{Zb}$ for the original ten-output Euclidean
task with both affine offsets, no encoder regularity assumption,
the same relative commands at all heights, and all finite
valid histories. Its equality witness uses the anchored
derivative approximation, $2m+5$ explicit real features,
saturated native guards and an allowed phase quotient.
The separate general-fixed-means statement is a necessary
one-pair bound with an explicitly nonconstant native rational
frequency, not an off-wall sharpness theorem.

The decoder-free result combines elementary periodic-orbit
arithmetic with affine spanning and common multiples of finitely
many periods. Its source-specific bridge is that the real
native command $4\pi$ has unbounded prime periods on actual rays
in every positive-width band, while one finite-dimensional
affine map fixes all its periodic points after a common
iterate. The minimal theorem needs neither a probability-update
map nor a decoder. The rational-step obstruction, irrational-step
choice construction and retained-lift affine model state which
operation and source quantifiers matter. These uses of classical
ingredients carry no claim of worldwide originality or formal
verification.

For Definition 7.1, phase and simultaneous-control continuation
have the sharp finite approximation threshold proved in
Theorem 7.11. Additional injectivity, native-output realizability,
regularity, finite-precision or robustness requirements specify
different problems; the equality witness does not solve them.
The sufficient feature counts are not minimum dimensions.
The lossless theorem neither determines approximate-action
error bounds nor proves that every finite affine quotient must
forget the entire $\beta$ circle. The band equality result
does not provide a full-open-domain equality attainer, and the
general-fixed-means lower bound does not provide its own
matching upper construction.

The original alternative of an attainer at some finite $N$
versus a strict gap for every finite $N$ remains open.
No identification of that objective and its admissible
realizations with either contract here has been proved.
Finite feature dimension and arbitrary finite execution length
are not that optimization's finite-$N$ attainment, and neither
affine obstruction is its strict-gap proof.
Exact-real initialization, source access and ideal output
functions are mathematical interfaces, without a supplied
finite-measurement acquisition, training, implementation or
task-transfer guarantee.

## 9.99 追加锚

## 10. Finite affine factors of native continuation

The full native command menu determines an exact universal information
loss even when the encoder is an arbitrary function. Every finite affine
factor erases rational common turns. For each specified irrational common
turn there is a four-real-coordinate factor that distinguishes it, using
a complex field automorphism and choice. Continuous factors, and more
generally factors bounded on each common-phase orbit, erase the whole
common circle. The full difference circle remains available.

The structural statement underlying these conclusions is an **abstract
circle action by unipotent affine automorphisms** on the affine image
hull. Unipotence refers to the homogenized matrices. Neither regular
dependence on the circle parameter nor a Zariski-closed image is part of
this statement. A proper infinite translation subgroup below shows why
the latter property cannot be added in general.

### 10.1 Actual rays, native commands and the factor contract

**Definition 10.1 (Finite affine factor, without a readout).**
Fix
$0<Z<1$, $r=1-Z$, $H=r/2$ and $0<a<b<H$, and set
$I=[a,b]$, $\ell=b-a$ and $\mathbb T=\mathbb R/(2\pi\mathbb Z)$.
Keep one arbitrary fixed preparation with height $k_0\in(0,H)$
and phases $\theta^{\rm in}$. The source is
$\mathcal M_I=I\times\mathbb T^2$ of actual current rays, in
coordinates $(k,u,v)$. Its commands, for every signed real $s,t$, are

$$
P_s(k,u,v)=(k+s,u,v),\qquad
D_s=\{(k,u,v)\in\mathcal M_I:k+s\in I\},
$$

$$
Q_t(k,u,v)=
 \left(k,u+\left(\frac12-\frac kr\right)t,v-\frac kr t\right),
\qquad \operatorname{dom}Q_t=\mathcal M_I.
$$

A finite affine factor consists of an arbitrary function
$E:\mathcal M_I\to\mathbb R^n$, $0\le n<\infty$, and fixed
affine maps, one for each command,

$$
\mathcal A_s(z)=L_s z+p_s,\qquad
\mathcal B_t(z)=M_t z+q_t,
$$

satisfying

$$
E(P_sx)=\mathcal A_sE(x)\quad(x\in D_s),\qquad
E(Q_tx)=\mathcal B_tE(x)\quad(x\in\mathcal M_I).
$$

The coefficients may depend on the command and the fixed task parameters,
but not on the current state or its producing history. Both offsets are
arbitrary. No decoder, injectivity, continuity, measurability, boundedness,
computability, parameter regularity, ambient invertibility or ambient
representation law is assumed. The case $n=0$ permits the constant
factor into a singleton.

The identities apply on the entire lawful source domains and therefore
after every finite valid word, from every exactly encoded initial ray.
For $|s|=\ell$ the probability domain is one endpoint slice; for
$|s|>\ell$ it is empty. No condition is imposed on an off-domain ray
or an arbitrary off-image feature vector. No requirement that guards be
recoverable from an arbitrary factor is added. The explicit factors
constructed below do retain height and hence have saturated guards.

The common-turn maps used in the conclusions are

$$
C_c(k,u,v)=(k,u+c,v+c),\qquad c\in\mathbb T.
$$

They are defined on actual rays. They will be obtained from lawful
rectangles, not postulated as extra independently available controls.
A stronger version of the factor contract also asks for one affine
update for every prescribed simultaneous native path on its entire
all-times guard. All the universal identifications below hold for that
version as well, and all the separating witnesses supplied below satisfy
it directly.

**Proposition 10.2 (Native source and finite reachability bridge).**
Definition 10.1 has exactly the native probability, phase and ray
interpretation of §§1 and 7, for arbitrary preparation. In particular
every stated source point is exactly finitely reachable, including both
band endpoints.

**Proof.** In mode order $(0,1,2,3,13)$, the double-wall constraints
are $p_2=Z$, $p_1+p_{13}=p_3+p_{13}=H$ and total mass one.
Putting $p_{13}=k$ gives

$$
p(k)=(k,H-k,Z,H-k,k),\qquad
d=(1,-1,0,-1,1)^{\mathsf T}.
$$

The sum is $2H+Z=1$, and positivity is precisely $0<k<H$.
The declared native denominator and weights are

$$
I(k)=\frac2k+\frac2{H-k}=\frac r{k(H-k)},\qquad
w(k)=\left(\frac12-\frac kr,-\frac kr,0,
                  -\frac kr,\frac12-\frac kr\right).
$$

Thus $d^{\mathsf T}w=1$ and $p^{\mathsf T}w=0$ by direct
substitution. Integrating $d\theta=w(k)\,d\chi$, starting with
zero increments, gives $h=(u,v,0,v,u)$ and

$$
du=\left(\frac12-\frac kr\right)d\chi,\qquad
dv=-\frac kr\,d\chi,\qquad d(u-v)=\frac12\,d\chi.
$$

These are equalities of increments, not equalities of the preparation
phases. Set $\eta_j=\theta_j^{\rm in}-\theta_2^{\rm in}$.
With the native negative-phase convention, a representative is

$$
\psi(k,u,v)=\left(
 \sqrt{k}e^{-i(\eta_0+u)},
 \sqrt{H-k}e^{-i(\eta_1+v)},
 \sqrt Z,
 \sqrt{H-k}e^{-i(\eta_3+v)},
 \sqrt{k}e^{-i(\eta_{13}+u)}
 \right).
$$

Equality of two such rays forces their scalar phase to be one because
the middle entry is the same positive $\sqrt Z$. Moduli then force the
same $k$, and positive group amplitudes force equality of $u$ and $v$
independently modulo $2\pi$. These conditions also suffice. Ratios to
the middle entry, followed by normalization and removal of the fixed
$\eta_j$, recover the two unit phase pairs continuously and smoothly.
The source therefore has exactly the band-times-two-circle topology,
without a further finite quotient.

A straight probability segment changes only $k$. Convexity of $I$
makes its whole segment lawful exactly when its two endpoints belong
to $I$. A phase leg of any finite real increment $t$ stays at its
height and integrates to $Q_t$. In particular the command parameter
$t$ is real; it is not itself reduced modulo a phase period.

For $k,k+s\in I$, execute the four legs in chronological order
$P_s,Q_t,P_{-s},Q_{-t}$. The two phase contributions give

$$
t\left[\left(\frac12-\frac{k+s}{r}\right)
          -\left(\frac12-\frac kr\right)\right]
 =-\frac{st}{r},\qquad
t\left[-\frac{k+s}{r}+\frac kr\right]=-\frac{st}{r}.
$$

The resulting map is exactly $C_{-st/r}$, with height and total
real relation increment unchanged. This is a finite rectangle identity,
not an infinitesimal or limiting commutator formula.

For reachability, take an entry height $h\in I$, equal to $k_0$ if
$k_0\in I$. Otherwise first use a phase-free probability leg in
$(0,H)$ from $k_0$ to $h$. Choose $h_1\in I$ different from $h$.
For target representatives $U,V\in\mathbb R$ and target $k\in I$,
put

$$
L=2(U-V),\quad
U_0=\left(\frac12-\frac hr\right)L,\quad
V_0=-\frac hr L,\quad
c=U-U_0=V-V_0.
$$

First use the rectangle with $s=h_1-h$ and $t=-rc/s$ to add
$(c,c)$ at $h$. Then execute $Q_L$ at $h$, and finally a
probability leg from $h$ to $k$. The resulting increments are
$(U,V)$. All legs are finite, every band probability segment joins
two band points, and all phase variations are finite. Conversely the
native equations preserve the increment groups already displayed.
This proves exact reachability rather than density. If the entire
producing history is required to stay in the band, the preparation
must itself lie there.

The coordinates $\alpha=u-v$ and $\beta=u$ used earlier are
well-defined circle coordinates, with inverse $u=\beta$,
$v=\beta-\alpha$. The real relation increment along a history is
$2(u_{\rm lift}-v_{\rm lift})$; its current circle value is
$2(u-v)$, up to the fixed preparation. It does not retain the
history's real lift. A common turn fixes this difference but changes
the bottom amplitudes relative to the positive middle amplitude.
It is consequently not a global ray gauge. $\square$

### 10.2 From local affine identities to an abstract unipotent action

Write $\mathscr H=\operatorname{aff}E(\mathcal M_I)$.
Two affine maps agreeing on a set agree on its affine hull:
an affine combination $\sum_i\lambda_i z_i$, $\sum_i\lambda_i=1$,
has image $\sum_i\lambda_i F(z_i)$. This elementary principle will
be applied only after the relevant lawful set is shown to span.

**Lemma 10.3 (Every open height strip spans).**
For every nonempty open interval $J\subset(a,b)$,

$$
\operatorname{aff}E(J\times\mathbb T^2)=\mathscr H.
$$

This includes arbitrary unbounded encoder images and zero-dimensional
affine hulls.

**Proof.** Denote the hull on the left by $\mathscr H_J$.
When $J,J+s\subset(a,b)$, the factor identity gives
$\mathcal A_s\mathscr H_J=\mathscr H_{J+s}$.
On $E(J\times\mathbb T^2)$ the composition
$\mathcal A_{-s}\mathcal A_s$ is the identity, and the opposite
composition is the identity on the translated strip. Extending
these identities by affine combinations shows that the two hulls
are affinely isomorphic. Their dimensions agree.

Choose $J_0$ with the smallest possible hull dimension $d$.
Such a minimum is achieved because all these dimensions are
integers in $\{0,\ldots,n\}$. Shrink $J_0$ if necessary so that
its closure is interior and its length is strictly less than
$\ell$. The smaller hull is contained in the original one and
has dimension at least the same minimum $d$, so its dimension
is still $d$.

All translates of $J_0$ with interior closure have dimension $d$.
If two overlap, their intersection is a nonempty open interval.
Its hull has dimension at least $d$ and is contained in both
$d$-dimensional hulls. Thus the two hulls coincide. The permissible
translation parameters form an interval; any two parameters can
be joined by finitely many steps smaller than the length of
$J_0$. Consecutive translates then overlap. All their hulls
therefore equal one affine space $\mathscr H^\circ$.
These translates cover $(a,b)$, so the interior image lies in
$\mathscr H^\circ$. Every other open strip lies in this space
and has dimension at least $d$; it too spans $\mathscr H^\circ$.

Endpoints require an affine argument, since $E$ need not be
continuous. Fix $h\in(a,b)$ and set $s=a-h$.
Choose a nonempty open $J\subset(h,b)$. Both $J$ and $J+s$
are interior, so the preceding identities give
$\mathcal A_s\mathscr H^\circ=\mathscr H^\circ$.
For all $u,v$,

$$
E(a,u,v)=\mathcal A_s E(h,u,v)\in\mathscr H^\circ.
$$

For the other endpoint set $s=b-h$ and take
$J\subset(a,h)$, obtaining the same conclusion for $E(b,u,v)$.
Hence $\mathscr H=\mathscr H^\circ$. No limit or norm bound
was used. The argument with $d=0$ simply identifies nonempty
singleton hulls at every step. $\square$

**Lemma 10.4 (Inverses on the image hull).**
If $|s|<\ell$, the restriction of $\mathcal A_s$ to
$\mathscr H$ is an affine automorphism with inverse
$\mathcal A_{-s}$. Every $\mathcal B_t$ restricts to an affine
automorphism, and on $\mathscr H$,

$$
\mathcal B_t\mathcal B_h=\mathcal B_{t+h},\qquad
\mathcal B_0=\operatorname{id},\qquad
\mathcal B_t^{-1}=\mathcal B_{-t}.
$$

**Proof.** For $|s|<\ell$ choose an open $J$ with
$J,J+s\subset(a,b)$. Lemma 10.3 makes both strip hulls equal
to $\mathscr H$, so the restricted inverse identities in its
proof apply on all of $\mathscr H$.
The source maps $Q_t$ are global bijections with
$Q_tQ_h=Q_{t+h}$ and $Q_{-t}=Q_t^{-1}$. Their encoder
identities and affine spanning give the asserted restrictions
and group law. These statements concern $\mathscr H$, not
unused directions of $\mathbb R^n$. At $|s|=\ell$ the lawful
slice need not span, and no restricted automorphism assertion
about the supplied $\mathcal A_s$ is required. $\square$

**Proposition 10.5 (Exact gluing of the common circle).**
There is a unique abstract group homomorphism

$$
\mathcal R:\mathbb T\longrightarrow\operatorname{Aff}(\mathscr H)
$$

with $\mathcal R_c E(x)=E(C_cx)$ for all $x\in\mathcal M_I$.
It commutes with every restricted $\mathcal B_t$ and every
restricted $\mathcal A_s$ with $|s|<\ell$. For all such $s$
and all real $t$,

$$
\mathcal B_{-t}\mathcal A_{-s}\mathcal B_t\mathcal A_s
   =\mathcal R_{-st/r}\quad\hbox{on }\mathscr H.
$$

**Proof.** Fix $s_0$ with $0<s_0<\ell/2$. For each real
representative $c$ and for $s=s_0,-s_0$, set $t=-rc/s$ and form
the affine automorphism

$$
\mathcal R_c^{(s)}
 =\mathcal B_{-t}\mathcal A_{-s}\mathcal B_t\mathcal A_s
 \bigm|_{\mathscr H}.
$$

Proposition 10.2 and the factor identities imply
$\mathcal R_c^{(s)}E(x)=E(C_cx)$ on $D_s$.
The height domains for the two signs are $[a,b-s_0]$ and
$[a+s_0,b]$. They cover $I$ and their intersection contains
the nonempty open interval $(a+s_0,b-s_0)$.
Its encoded image spans $\mathscr H$ by Lemma 10.3.
Thus the two affine words agree on $\mathscr H$.
Their common map, denoted $\mathcal R_c$, implements $C_c$
on every source state, including endpoints.

On the actual source, $C_{c+d}=C_cC_d$, $C_0$ is the identity
and $C_{c+2\pi}=C_c$. Applying these identities to every encoded
state and using affine spanning gives

$$
\mathcal R_{c+d}=\mathcal R_c\mathcal R_d,\qquad
\mathcal R_0=\operatorname{id},\qquad
\mathcal R_{c+2\pi}=\mathcal R_c.
$$

In particular the action descends to the actual circle and has
inverse $\mathcal R_{-c}$. It is independent of the chosen
rectangle and is unique by affine spanning.

The common turn commutes with $Q_t$ on the whole source.
It commutes with $P_s$ on $D_s$, and preserves that domain.
These equalities imply commutation of the corresponding affine
maps on $E(\mathcal M_I)$ or $E(D_s)$ respectively.
For $|s|<\ell$, $D_s$ contains an open strip spanning
$\mathscr H$. This proves the stated centrality. Applying
the rectangle identity once more on such a strip proves the
last formula for every short $s$, including $s=0$.
No partial probability map has been made into a global source
bijection. Only its affine restriction on the proven hull has
an inverse. $\square$

**Theorem 10.6 (Unipotence and rational common-turn erasure).**
Every value of the abstract action in Proposition 10.5 is
unipotent after homogenization. Consequently every finite
affine factor satisfies

$$
E(C_{2\pi q}x)=E(x)
 \quad(q\in\mathbb Q,\ x\in\mathcal M_I).
$$

**Proof.** Choose affine coordinates
$\mathscr H\cong\mathbb R^d$ and put $N=d+1$.
Represent an affine automorphism $z\mapsto Lz+b$ by

$$
\widehat F=
\begin{pmatrix}L&b\\0&1\end{pmatrix}
\quad\hbox{on }\mathbb R^{d+1},
\qquad
\widehat F\binom z1=\binom{F(z)}1.
$$

This faithful, multiplication-preserving construction retains
both $p_s$ and $q_t$ after restriction. No offset has been
removed by assuming a fixed point. Complexify the homogeneous
space. Fix $c$ and an eigenvalue $\lambda$ of
$\widehat{\mathcal R}_c$. Invertibility gives $\lambda\ne0$.
Its generalized eigenspace

$$
V_\lambda=
 \ker(\widehat{\mathcal R}_c-\lambda I_N)^N
$$

has dimension $m$ with $1\le m\le N$.
Since $\mathcal R_c$ commutes with the short probability maps
and all phase maps, their homogeneous matrices, and their
inverses, preserve this kernel. Their restrictions are
automorphisms of the same $V_\lambda$.

Use the fixed $s_0$ above and $t=-rc/s_0$.
The rectangle formula restricts to

$$
\widehat{\mathcal R}_c\bigm|_{V_\lambda}
 =
 \left(\widehat{\mathcal B}_{t}\bigm|_{V_\lambda}\right)^{-1}
 \left(\widehat{\mathcal A}_{s_0}\bigm|_{V_\lambda}\right)^{-1}
 \left(\widehat{\mathcal B}_{t}\bigm|_{V_\lambda}\right)
 \left(\widehat{\mathcal A}_{s_0}\bigm|_{V_\lambda}\right).
$$

The determinant of this product is one. The restriction on the
left is $\lambda I$ plus a nilpotent map, so its determinant
is $\lambda^m$. Therefore $\lambda^m=1$.

Let $q=N!$. Apply this eigenvalue conclusion to
$\widehat{\mathcal R}_{c/q}$. Each of its eigenvalues has order
dividing an integer between $1$ and $N$, hence dividing $q$.
The abstract action law gives

$$
\widehat{\mathcal R}_c
   =\left(\widehat{\mathcal R}_{c/q}\right)^q.
$$

Every eigenvalue of this power is one. For example, triangularize
the one complex matrix by choosing an eigenvector and then
inducting on the quotient dimension; its power has the powers
of the diagonal entries. This requires no simultaneous
triangularization of the action. The characteristic polynomial
of $\widehat{\mathcal R}_c$ is consequently $(X-1)^N$, and
Cayley--Hamilton gives
$(\widehat{\mathcal R}_c-I_N)^N=0$.

If $c/(2\pi)$ is rational, some integer $j>0$ has
$jc\in2\pi\mathbb Z$. Periodicity and the action law give
$\widehat{\mathcal R}_c^j=I_N$. Its minimal polynomial divides
both $(X-1)^N$ and $X^j-1$. In characteristic zero the latter
has a simple root at one, since its derivative there is $j$.
The two polynomials have greatest common divisor $X-1$.
Thus the minimal polynomial divides $X-1$ and
$\widehat{\mathcal R}_c=I_N$. The required encoder identity
follows.

If $d=0$, $\mathscr H$ is a point and its homogeneous space
has dimension one; the same conclusion is immediate.
The proof supplies an abstract homomorphism from the underlying
group of $\mathbb T$. It supplies no continuity, measurability
or algebraic dependence on $c$, and no Zariski-closedness of
its image. $\square$

### 10.3 Four real coordinates with common-phase sensitivity

The counterexamples in this subsection use ordinary set theory with
choice. Their formulas are explicit once a field automorphism is fixed;
the choice of that automorphism is not an effective construction.

**Lemma 10.7 (The required complex-field extensions).**
An isomorphism between countable subfields of $\mathbb C$ extends
to an automorphism of $\mathbb C$. More generally, an isomorphism
$K\to K'$ extends to an isomorphism between specified algebraic
closures of $K$ and $K'$.

**Proof.** First consider algebraic closures $\Omega,\Omega'$.
Order the embeddings from intermediate fields
$K\subset L\subset\Omega$ into $\Omega'$ extending the
given isomorphism by extension of domain and map.
The union of a chain is again such a field embedding.
Zorn's lemma supplies a maximal one, $\varphi:L\to\Omega'$.
If $z\in\Omega\setminus L$, it is algebraic over $L$.
Transport its irreducible minimal polynomial by $\varphi$
and choose a root in the algebraically closed $\Omega'$.
The quotient description by the irreducible polynomial extends
$\varphi$ to $L(z)$, a contradiction. Thus $L=\Omega$.

The image of this embedding is algebraically closed: a polynomial
over the image can be pulled back coefficient by coefficient to
$\Omega$, a root found there, and the root mapped forward.
The image contains $K'$, and every element of $\Omega'$ is
algebraic over $K'$, hence over that image. An algebraically
closed field has no proper algebraic extension, since every
irreducible polynomial over it is linear. The embedding is
therefore surjective. This proves the algebraic-closure assertion
without a countability hypothesis.

For countable $K,K'\subset\mathbb C$, choose transcendence
bases $T,T'$ of $\mathbb C$ over them. Existence follows by
the same maximality principle applied to algebraically independent
sets; maximality means that the remaining extension is algebraic.
For a basis of cardinality $\kappa$, its rational-function field
has cardinality $\max(\aleph_0,\kappa)$: expressions use finitely
many variables and coefficients. An algebraic extension of an
infinite field has no greater cardinality than the field, since
there are that many polynomials and each has finitely many roots.
As $\mathbb C$ is uncountable and algebraic over $K(T)$, this
forces $|T|=|\mathbb C|$, and likewise $|T'|=|\mathbb C|$.
Choose a bijection $T\to T'$. Algebraic independence extends
the original isomorphism to $K(T)\to K'(T')$ by substitution
in rational functions. Both copies of $\mathbb C$ are algebraic
closures of these fields. The first part now extends that map to
an automorphism of $\mathbb C$. The uses of bases, a bijection
and maximal embeddings all occur under choice. $\square$

A concrete admissible starting isomorphism is

$$
\mathbb Q(\sqrt2)\longrightarrow\mathbb Q(\sqrt2),
\qquad a+b\sqrt2\longmapsto a-b\sqrt2.
$$

The irrationality of $\sqrt2$ follows from the usual parity
argument: a reduced equality $p^2=2q^2$ forces both $p$ and $q$
even. The displayed map is consequently a field automorphism
and Lemma 10.7 extends it to some
$\sigma:\mathbb C\to\mathbb C$ with $\sigma(\sqrt2)=-\sqrt2$.

It is essential to use a complex-field automorphism. Every
automorphism of the real field preserves positive numbers
because they are nonzero squares. It therefore preserves order.
It fixes $\mathbb Q$, and rational numbers between two distinct
real numbers show that an order-preserving map fixing
$\mathbb Q$ must fix every real number. No nontrivial real-field
automorphism can play the role of $\sigma$.
A complex-field automorphism need not preserve the real subfield
or commute with ordinary complex conjugation.

**Proposition 10.8 (An actual-ray factor in four real coordinates).**
Let $\sigma$ be any complex-field automorphism and define, for
real $z$,

$$
f(z)=\operatorname{Re}\sigma(z)-z.
$$

Then $f$ is additive, vanishes on $\mathbb Q$, and is periodic
with period one. Set $x=k/r$ and let
$\nu=v/(2\pi)\in\mathbb R/\mathbb Z$. The formula

$$
E_\sigma(k,u,v)=
 \left(x,\operatorname{Re}\sigma(x),
           \operatorname{Im}\sigma(x),f(\nu)\right)
 \in\mathbb R^4
$$

defines a finite affine factor on actual rays. Here $f(\nu)$
means evaluation at any real representative. In shorthand write
its coordinates as $(X,W,F)\in\mathbb R\times\mathbb C\times\mathbb R$.

**Proof.** A field automorphism fixes the prime field $\mathbb Q$.
Additivity of $\sigma$ and of real part gives additivity of $f$,
and $f(q)=0$ for $q\in\mathbb Q$. In particular
$f(z+m)=f(z)$ for all integers $m$.
Changing the representative of $v$ by $2\pi m$ therefore
does not change the encoding; changing $u$ has no effect at all.
Proposition 10.2 identifies $k,u,v$ as actual ray coordinates
relative to the fixed arbitrary preparation. Thus the encoder
descends to the ray quotient without retaining a real phase lift.

For a probability command set $\delta=s/r$. Use the affine map

$$
\mathcal A_s^\sigma(X,W,F)
 =(X+\delta,W+\sigma(\delta),F).
$$

Its real linear part is the identity and its offset, in the
four real coordinates, is

$$
(\delta,\operatorname{Re}\sigma(\delta),
          \operatorname{Im}\sigma(\delta),0).
$$

On an encoded point, additivity of $\sigma$ gives exactly
$E_\sigma(P_s(k,u,v))$ whenever $k+s\in I$.
This includes both signs and the endpoint-to-endpoint commands.
The same formula can be assigned when the source domain is empty.

For a phase command set $\tau=t/(2\pi)$ and
$\sigma(\tau)=A+iB$. Use the real linear map

$$
\mathcal B_t^\sigma(X,W,F)
 =\bigl(X,W,F+\tau X-\operatorname{Re}(\sigma(\tau)W)\bigr).
$$

Its real matrix is

$$
\begin{pmatrix}
1&0&0&0\\
0&1&0&0\\
0&0&1&0\\
\tau&-A&B&1
\end{pmatrix},
$$

with zero offset. Under the actual $Q_t$, the normalized second
group angle changes by $\nu'=\nu-x\tau$ modulo integers.
Hence

$$
\begin{aligned}
f(\nu')
 &=f(\nu)-f(x\tau)\\
 &=f(\nu)+x\tau-
       \operatorname{Re}\bigl(\sigma(x)\sigma(\tau)\bigr),
\end{aligned}
$$

which is precisely the proposed update. The first group angle
also changes according to its native equation; it is only the
encoder that ignores that angle. All coefficients are fixed by
the prescribed command, and every $Q_t$ is represented on the
full source. No assumption that $\sigma$ fixes $r$ or $\pi$
has entered: $\sigma(s/r)$ and $\sigma(t/(2\pi))$ are applied
to those real numbers as whole arguments.

The exact encoded source image is

$$
\mathscr S_\sigma=
 \{(X,\sigma(X),F):
       a/r\le X\le b/r,\ F\in f(\mathbb R)\}.
$$

Indeed all encoded points have this form; conversely any such
$F$ has a representative $\nu$ with $f(\nu)=F$, and full
native reachability realizes its phase at any indicated height.
On this image the exact probability guard is
$a\le rX+s\le b$, while the phase guard is the whole image.
They are constant on encoder fibers. The verified identities
prove image preservation on these guards and, by induction,
exact encoded continuation after every finite valid word.

For a common turn the first three coordinates stay fixed and

$$
E_\sigma(C_c(k,u,v))-E_\sigma(k,u,v)
 =(0,0,0,f(c/(2\pi))).
$$

For the specified $\sigma(\sqrt2)=-\sqrt2$,
$f(\sqrt2)=-2\sqrt2\ne0$. Thus the rays
$(k,0,0)$ and $(k,2\pi\sqrt2,2\pi\sqrt2)$ have different
encodings for every $k\in I$. They are distinct actual rays,
and the finite rectangle construction reaches one from the
other. This refutes full common-circle invariance for arbitrary
finite affine factors. $\square$

**Proposition 10.9 (All prescribed simultaneous paths, with offsets).**
The same four-coordinate factor has one exact affine update for
every prescribed native relative path, on its full all-times
band guard, and those updates compose for every finite valid
concatenation.

**Proof.** Prescribe a piecewise $C^1$ or absolutely continuous
relative path on $[0,T]$, in the native regularity class, with

$$
k(h)=k+\rho(h),\quad \rho(0)=0,\qquad
\chi(h)=\chi(0)+\gamma(h),\quad \gamma(0)=0.
$$

Set

$$
s=\rho(T),\qquad t=\gamma(T),\qquad
J=\int_0^T\rho(h)\dot\gamma(h)\,dh.
$$

Continuity makes $\rho$ bounded on this finite compact interval;
finite phase variation makes $\dot\gamma$ integrable.
Thus the integral exists. The source guard is exactly

$$
k+\rho(h)\in I\quad\hbox{for every }h\in[0,T].
$$

Its endpoints alone do not replace this condition. Direct
integration of the native equations yields

$$
k'=k+s,\qquad
u'=u+\frac t2-\frac{kt}{r}-\frac Jr,\qquad
v'=v-\frac{kt}{r}-\frac Jr.
$$

These are circle equalities induced by the integrated real
increments. Put

$$
\delta=s/r,\qquad \tau=t/(2\pi),\qquad
\eta=J/(2\pi r).
$$

Then $\nu'=\nu-x\tau-\eta$ modulo integers, so the required
ambient affine map is

$$
(X,W,F)\longmapsto
 \left(X+\delta,\ W+\sigma(\delta),\
 F+\tau X-\operatorname{Re}(\sigma(\tau)W)-f(\eta)\right).
$$

Its offset is
$(\delta,\operatorname{Re}\sigma(\delta),
\operatorname{Im}\sigma(\delta),-f(\eta))$.
Its linear last row is the same as in Proposition 10.8.
Thus both probability and phase offsets are present where
needed. The guard on $\mathscr S_\sigma$ is
$rX+\rho(h)\in I$ for every $h$; empty and singleton guards
are allowed. Applying $\sigma$ to the resulting scalar
$\eta$ makes no interchange between a discontinuous field map
and integration.

For two concatenated relative paths, the displacement on the
second part is $s_1+\rho_2$, hence

$$
s=s_1+s_2,\qquad t=t_1+t_2,\qquad
J=J_1+J_2+s_1t_2.
$$

In normalized variables,
$\eta=\eta_1+\eta_2+\delta_1\tau_2$.
Composing the two displayed affine maps produces in the last
coordinate the extra term

$$
\tau_2\delta_1-
 \operatorname{Re}\bigl(\sigma(\tau_2)\sigma(\delta_1)\bigr)
 =-f(\delta_1\tau_2).
$$

Additivity of $f$ gives exactly the combined offset
$-f(\eta_1+\eta_2+\delta_1\tau_2)$.
The guard is the first path's guard followed by the second
path's guard at the actual new height. Induction gives all
finite concatenations. Replacing $T$ by an intermediate time
gives the same identity at every point of a prescribed path.
No approximation by increasingly fine words, or limiting
evaluation of the irregular encoder, is used. $\square$

**Theorem 10.10 (A separate factor for each irrational common turn).**
For every $c\in\mathbb T$ with $c/(2\pi)$ irrational modulo
integers, there exists a factor $E_\sigma$ from Proposition
10.8 that distinguishes $x$ from $C_cx$ for every source
state $x$. It also satisfies Proposition 10.9.

**Proof.** Choose a real representative $\xi=c/(2\pi)$.
If $\xi$ is transcendental, substitution
$\xi\mapsto\xi+1$ gives an isomorphism
$\mathbb Q(\xi)\to\mathbb Q(\xi+1)$.
These fields are countable, and Lemma 10.7 extends this
isomorphism to $\sigma$ on $\mathbb C$.
Then $f(\xi)=1$.

If $\xi$ is algebraic irrational, let its irreducible polynomial
over $\mathbb Q$ have degree $d>1$. Its roots are distinct
in characteristic zero and their sum is rational.
They cannot all have real part $\xi$: otherwise the real
part of their sum would be $d\xi\in\mathbb Q$, contradicting
irrationality. Choose a root $\zeta$ with
$\operatorname{Re}\zeta\ne\xi$. The quotient construction by
the same irreducible polynomial gives an isomorphism
$\mathbb Q(\xi)\to\mathbb Q(\zeta)$ carrying $\xi$ to
$\zeta$. Extend it by Lemma 10.7. Then
$f(\xi)=\operatorname{Re}\zeta-\xi\ne0$.

In either case the common-turn identity of Proposition 10.8
proves distinction at every $x$. Changing the representative
$\xi$ by an integer does not change $f(\xi)$.
The quantifiers are “for each irrational turn, some factor.”
They do not exhibit one finite factor that distinguishes all
irrational common-turn cosets simultaneously. $\square$

### 10.4 Exact universal identifications and added regularity

**Proposition 10.11 (The retained difference circle).**
The continuous three-real-coordinate map

$$
E_\Delta(k,u,v)=\bigl(k,\cos(u-v),\sin(u-v)\bigr)
$$

is a finite affine factor. It also has exact affine updates for
every prescribed simultaneous native path. It separates every
pair of different $(k,u-v)\in I\times\mathbb T$.

**Proof.** With $\alpha=u-v$, a probability command adds
$(s,0,0)$. A phase command fixes the height and rotates the
last two coordinates by $R_{t/2}$, because
$\alpha'=\alpha+t/2$. These are fixed affine maps for each
command and hold on the full lawful domains.
For the simultaneous path of Proposition 10.9 the $J$ and
$kt$ terms cancel upon subtracting the phase equations.
Thus its update is

$$
(K,z)\longmapsto(K+s,R_{t/2}z),
\qquad z\in\mathbb R^2,
$$

with the all-times guard $K+\rho(h)\in I$.
The actual image is $I$ times the unit circle; these guards
are saturated and the formulas preserve the image whenever
lawful. Equal unit phase pairs mean equal circle classes,
so exactly $k$ and $\alpha$ are retained. Finite continuation
follows from the one-step identities. In particular
$\alpha=0$ and $\alpha=\pi$ remain distinct.
Storing only $2\alpha$ would impose an additional identification
that this contract does not force. Three is an attained
coordinate count here, not a claimed minimum. $\square$

**Theorem 10.12 (Intersection kernel and universal state equivalence).**
For a finite affine factor define

$$
K_E=\{c\in\mathbb T:
           E(C_cx)=E(x)\text{ for every }x\in\mathcal M_I\}.
$$

Then

$$
\bigcap_E K_E=2\pi\mathbb Q/(2\pi\mathbb Z).
$$

More fully, two source states have equal encodings under every
finite affine factor if and only if they differ by a rational
common turn:

$$
x\sim_{\rm all}x'
\quad\Longleftrightarrow\quad
x'=C_{2\pi q}x\text{ for some }q\in\mathbb Q.
$$

For continuous finite affine factors, the equivalence is instead

$$
(k,u,v)\sim_{\rm cont}(k',u',v')
\quad\Longleftrightarrow\quad
k=k'\ \hbox{and}\ u-v=u'-v'\ \hbox{in }\mathbb T.
$$

Every continuous factor has a continuous factorization

$$
E(k,u,v)=\overline E(k,u-v),\qquad
\overline E:I\times\mathbb T\longrightarrow\mathbb R^n.
$$

All these assertions also hold when the class of factors is
restricted to those supporting every prescribed simultaneous path.

**Proof.** By affine spanning, $K_E$ is exactly the kernel of
the abstract action $\mathcal R$ on $\mathscr H$.
Theorem 10.6 puts every rational common turn in every $K_E$.
Theorem 10.10 excludes every irrational common turn from at
least one such kernel. This proves the intersection identity.

Proposition 10.11 distinguishes two states when their heights
or difference-circle values differ. If those two quantities
agree, the two states have the form $x'=C_cx$ for a single
$c\in\mathbb T$: the differences $u'-u$ and $v'-v$ agree.
For rational $c/(2\pi)$ Theorem 10.6 erases this distinction
for every factor. For irrational $c/(2\pi)$ Theorem 10.10
gives a factor distinguishing these particular states.
This proves the full arbitrary-factor equivalence.

For continuous $E$, fix $x$ and a real representative $c$.
Choose rational numbers $q_j$ such that $2\pi q_j\to c$.
In the actual source topology,
$C_{2\pi q_j}x\to C_cx$. Rational erasure and continuity yield

$$
E(C_cx)=\lim_j E(C_{2\pi q_j}x)=E(x).
$$

Only continuity along each common orbit is needed for this
invariance statement. Full continuity of $E$ gives continuity
of the quotient factor by the explicit section

$$
\overline E(k,\alpha)=E(k,\alpha,0).
$$

The input $\alpha$ here is a circle class; no continuous real
argument branch is selected. Since
$(k,u,v)=C_v(k,u-v,0)$, this section has the required
factorization. Common invariance proves one direction of
$\sim_{\rm cont}$, and the continuous witness $E_\Delta$
proves the other.

The universal erasure statements apply to the stronger path
contract because it includes the pure commands. Both types of
separating witnesses, $E_\sigma$ and $E_\Delta$, satisfy that
stronger contract by Propositions 10.9 and 10.11. Thus the
intersection and equivalence relations are unchanged.
The continuous argument takes limits of already finitely
reachable points; it executes no infinite history. $\square$

**Theorem 10.13 (Bounded common orbits are exactly invariant orbits).**
For any finite affine factor and any source state $x$, the set

$$
\{E(C_cx):c\in\mathbb T\}
$$

is bounded if and only if it is the singleton $\{E(x)\}$.
Consequently boundedness on each common-phase orbit suffices
for set-theoretic factorization through $(k,u-v)$, without
a continuity hypothesis. Any common-phase sensitivity forces
unbounded values along finite iterates of an affected turn.

**Proof.** Use the homogeneous representation on
$\mathbb R^{d+1}$ and write
$\widehat{\mathcal R}_c=I+N_c$ with $N_c^N=0$.
For $z=(E(x),1)$, interpreted in the chosen affine coordinates,
and every integer $m\ge0$, the finite binomial identity gives

$$
\widehat{\mathcal R}_c^m z
 =\sum_{j=0}^{N-1}\binom mj N_c^jz
 =\bigl(E(C_{mc}x),1\bigr).
$$

If $N_cz\ne0$, choose the greatest $j\ge1$ with
$N_c^jz\ne0$ and a real linear functional nonzero on that
vector. Applied to the displayed sum, it gives a polynomial
in $m$ of degree $j$ with nonzero leading coefficient,
because $\binom mj$ has leading coefficient $1/j!$.
The polynomial is unbounded on nonnegative integers.
A bounded common orbit would give a bounded sequence of
homogeneous vectors and hence a bounded value under every
linear functional, a contradiction.

Thus a bounded orbit forces $N_cz=0$ for each $c$, or
$E(C_cx)=E(x)$ for each $c$. The converse is immediate.
If every orbit is bounded, the section in Theorem 10.12
defines the set-theoretic quotient factor. Its continuity
does not follow from boundedness alone. If an affected
$x,c$ has unequal encodings, the same polynomial argument
gives unboundedness of the corresponding finite iterates.
Each iterate is a finite valid sequence of finite rectangles;
no infinite execution is required. $\square$

### 10.5 Irregularity and the algebraic-group boundary

**Proposition 10.14 (Choice, unboundedness and measure limitations).**
For any $\sigma$ above with $f\ne0$, $f$ is unbounded on every
nonempty real open interval. Its induced circle function is
unbounded on every nonempty arc and is not measurable for
completed Haar measure. The corresponding $E_\sigma$ is
neither Borel measurable nor measurable for the usual completed
product measure on $I\times\mathbb T^2$.

These assertions use ordinary Lebesgue measure and its
translation invariance and regularity, the corresponding
completed circle measure, and the section theorem for finite
product measures. In the usual representations of computable
analysis, $E_\sigma$ is not a total computable function.

**Proof.** Suppose an additive $f$ vanishing on $\mathbb Q$
is bounded in absolute value by $M$ on an open interval.
Differences of two points in that interval fill a neighborhood
$(-\delta,\delta)$ of zero, on which $|f|\le2M$.
Given $\epsilon>0$, choose an integer $m>0$ with
$2M/m<\epsilon$, using any positive $m$ if $M=0$.
For $|h|<\delta/m$, additivity gives

$$
|f(h)|=\frac{|f(mh)|}{m}\le\frac{2M}{m}.
$$

Thus $f$ is continuous at zero. Additivity then gives continuity
everywhere, and density of $\mathbb Q$ forces $f=0$.
The contrapositive proves unboundedness for nonzero $f$.
Period one makes the same statement true on every circle arc.
For every fixed $k,u,v$, the fourth coordinate of
$E_\sigma(C_c(k,u,v))$ is $f(v/(2\pi)+c/(2\pi))$,
so even an arbitrarily short open common-turn arc has unbounded
image.

Suppose now that $f$ were Lebesgue measurable.
The measurable sets

$$
A_m=\{x\in[0,1]:|f(x)|\le m\},\qquad m=1,2,\ldots,
$$

cover $[0,1]$. At least one, $A$, has positive measure.
Its measure is finite. We spell out the translation step.
For any $\epsilon>0$, Lebesgue regularity provides a finite
union $U$ of bounded intervals with
$\mu(A\mathbin{\triangle}U)<\epsilon$.
One obtains such a union by placing a compact inner
approximation inside an open outer approximation and taking
a finite interval cover of the compact set inside the open
one. If $U$ uses $h_0$ intervals, translation invariance gives

$$
\mu(A\mathbin{\triangle}(A+h))
 \le 2\mu(A\mathbin{\triangle}U)
       +\mu(U\mathbin{\triangle}(U+h))
 \le 2\epsilon+2h_0|h|.
$$

First choosing $\epsilon$ small and then $h$ small proves
translation continuity of this symmetric-difference measure.
Since $\mu(A+h)=\mu(A)>0$, it follows that
$\mu(A\cap(A+h))>0$ for every sufficiently small $h$.
In particular $h\in A-A$. If $A=A_m$, additivity now bounds
$|f(h)|\le2m$ on a neighborhood of zero. The preceding
argument forces $f=0$, a contradiction.

Let $g:\mathbb T\to\mathbb R$ be
$g(v)=f(v/(2\pi))$. Completed Haar measurability of $g$
would give Lebesgue measurability of $f$ on $[0,1)$ using
the usual fundamental-domain measure identification.
Countably many integer translates and period one would make
$f$ measurable on $\mathbb R$. Thus $g$ is not measurable.
If $E_\sigma$ were Borel measurable, its restriction along
the continuous circle map $v\mapsto(k_*,u_*,v)$ would make
$g$ Borel measurable, again impossible.

For completed product measure a null slice alone would not
justify the same inference. Instead choose a Borel set
$B\subset\mathbb R$ whose preimage $A=g^{-1}(B)$ is not
Haar measurable. The preimage of $B$ under the fourth
coordinate of $E_\sigma$ is exactly

$$
I\times\mathbb T\times A.
$$

If this cylinder were measurable for the completed product
measure, the section theorem would make its $v$ section
measurable for almost every $(k,u)$. Indeed a completed
measurable set differs from a Borel representative by a
subset of a product null set; the null-set section theorem
and Borel sections give completed measurable sections
almost everywhere. Every section of this cylinder is $A$,
and the base $I\times\mathbb T$ has finite positive measure.
This is a contradiction.

In the standard real and circle representations by arbitrarily
accurate approximations, total computability entails continuity.
Thus the discontinuous $E_\sigma$ cannot be total computable
in that model. This does not claim that each of its individual
values is a noncomputable real, or exclude every possible
oracle or alternative exact-real model.

The coefficient assignments also use the irregular field map:
$\sigma(s/r)$ and $\sigma(t/(2\pi))$ are not supplied by a
continuous or measurable parameterization. For nonzero $f$,
the real part of $\sigma$ on the real line is not Lebesgue
measurable, since subtracting the identity would make $f$
measurable. In particular the real phase coefficient
$\operatorname{Re}\sigma(t/(2\pi))$ in these explicit maps
is nonmeasurable. The factor contract allows this.
All these limitations concern the constructed examples; no
classification of every merely measurable factor is asserted.
$\square$

**Proposition 10.15 (The abstract image need not be an algebraic subgroup).**
There is a choice of $\sigma$ in Proposition 10.8 for which
the common-circle image on its affine hull is a proper infinite
subgroup of a real translation line. Its Zariski closure is
the whole line, so the image itself is not Zariski closed.

**Proof.** Choose a transcendence basis $T_0$ of $\mathbb R$
over $\mathbb Q$ and put $F_0=\mathbb Q(T_0)\subset\mathbb R$.
The field $\mathbb R$ is algebraic over $F_0$, and
$\mathbb C=\mathbb R(i)$ is therefore algebraic over $F_0$.
Since $\mathbb C$ is algebraically closed, it is an algebraic
closure of $F_0$.

We need $\sqrt2\notin F_0$. Otherwise, using finitely many
elements of $T_0$, write $\sqrt2=p(T)/q(T)$ for rational
polynomials with $q(T)\ne0$. Algebraic independence would
give the polynomial identity $p^2=2q^2$ over $\mathbb Q$.
Choose a monomial order on these finitely many variables.
The leading coefficient of a product is the product of its
leading coefficients. Comparing the leading coefficients in
this identity would make the square of a nonzero rational
number equal to two, which is impossible. Thus $X^2-2$ is
irreducible over $F_0$.

The $F_0$-isomorphism of $F_0(\sqrt2)$ sending $\sqrt2$
to $-\sqrt2$ extends, by the algebraic-closure part of
Lemma 10.7, to an automorphism $\sigma$ of $\mathbb C$
fixing $F_0$ pointwise. Here $\mathbb C$ is also an
algebraic closure of $F_0(\sqrt2)$.
Let $j$ be ordinary complex conjugation; it too fixes $F_0$.

For any $x\in\mathbb R$, let $L\subset\mathbb C$ be the
splitting field of its minimal polynomial over $F_0$.
It is a finite normal separable extension: finitely many
algebraic roots generate a finite extension, all roots are
included, and characteristic zero gives separability.
Both $\sigma$ and $j$ permute those roots and preserve $L$.
Their restrictions generate a finite subgroup
$G\subset\operatorname{Aut}(L/F_0)$, since every such
automorphism is determined by its permutation of this finite
generating root set. Because $x$ is real,

$$
f(x)=\frac{\sigma(x)+j\sigma(x)}2-x\in L.
$$

Define the finite orbit sum
$T_G(y)=\sum_{g\in G}g(y)$ for $y\in L$.
Right multiplication of $G$ by $\sigma|_L$ or by
$(j\sigma)|_L$ permutes $G$. Hence

$$
T_G(f(x))
 =\frac12\sum_{g\in G}g\sigma(x)
   +\frac12\sum_{g\in G}gj\sigma(x)
   -\sum_{g\in G}g(x)=0.
$$

This is the finite Galois orbit-sum, or trace, argument; no
commutation of $\sigma$ with $j$ was assumed. If $f(x)=1$,
the same sum would equal the positive integer $|G|$ in a
characteristic-zero field. Therefore $1\notin f(\mathbb R)$.
On the other hand $f(\sqrt2)=-2\sqrt2\ne0$.
Additivity now makes $f(\mathbb R)$ a proper infinite
additive subgroup of $\mathbb R$.

For this $E_\sigma$, common turns act by the ambient translations

$$
(X,W,F)\longmapsto(X,W,F+f(c/(2\pi))).
$$

Their restriction to the affine image hull is the action
$\mathcal R$ of Proposition 10.5, since both maps agree on
every encoded state. At a fixed height, two attainable last
coordinates differ by the nonzero value $f(\sqrt2)$.
Thus the vertical coordinate direction belongs to the
direction space of the affine hull. All real translations in
that direction preserve the hull, and restriction to the hull
is faithful on this translation line. As $c$ runs over
$\mathbb T$, $c/(2\pi)$ runs over $\mathbb R/\mathbb Z$;
period one gives exactly the parameter set $f(\mathbb R)$.

In affine coordinates on the hull, the full translation line
is an algebraic subgroup: its linear part is the identity and
its translation vector lies on a fixed one-dimensional real
subspace. A polynomial in the ambient matrix entries restricts
to a polynomial in the line parameter. If it vanishes on the
infinite set $f(\mathbb R)$, it vanishes on the whole line,
since a nonzero one-variable polynomial has finitely many
roots. The Zariski closure of the common-circle image is
therefore the whole translation line, while the image omits
the translation with parameter one. It is not Zariski closed.

The matrices of all these translations are unipotent after
homogenization, so this example is fully compatible with
Theorem 10.6. It disproves the additional standard assertion
that the image must itself be an algebraic subgroup; the
abstract-action assertion is the precise structural result.
$\square$

### 10.6 Original coherence, reduced menus and source boundaries

**Corollary 10.16 (An arbitrary decoder cannot recover original coherence).**
No finite affine factor of Definition 10.1 can exactly decode
the original full coherence menu by any deterministic decoder
of its encoded current state, even an arbitrary nonlinear or
irregular decoder. Every such factor also fails to be injective
on actual rays.

**Proof.** The common turn $\pi$ is rational and is therefore
erased by Theorem 10.6. In the native negative-phase convention,
the original $02$ pair is

$$
y_{02}(k,u,v)=
 2\sqrt{kZ}\bigl(\cos(\eta_0+u),\sin(\eta_0+u)\bigr).
$$

This follows directly from
$\overline\psi_0\psi_2=\sqrt{kZ}e^{i(\eta_0+u)}$
and the two Hermitian observables in Definition 2.1.
Since $kZ>0$ throughout the source,

$$
y_{02}(C_\pi x)=-y_{02}(x)\ne y_{02}(x),
\qquad E(C_\pi x)=E(x).
$$

A deterministic function of that one latent value cannot
return both different pairs. Thus it cannot return the
whole original output either. The two actual rays are
distinct by Proposition 10.2, so injectivity also fails.
No decoder hypothesis entered the classification proof.
This supplies an explicit forced collision for the full
menu; the one-command exact-decoding obstruction in §8
has a separate proof and weaker update requirements.
No approximation error bound is being inferred here.
$\square$

**Proposition 10.17 (Static four coordinates and affine continuation differ).**
The exact static four-coordinate response of §2 and the
four-coordinate factors of §10.3 solve different tasks.

**Proof.** Set $\alpha=u-v$, $\beta=u$, and write the static
response coordinates as

$$
z_\alpha=2\sqrt{k(H-k)}\,U(\alpha),\qquad
z_\beta=2\sqrt{kZ}\,U(u).
$$

The five native increment differences in edge order are
$\alpha,u,\alpha,-\alpha,-\alpha$.
Thus the original output is the fixed linear image

$$
y=O(z_\alpha,z_\beta,z_\alpha,Jz_\alpha,Jz_\alpha),
\qquad J=\operatorname{diag}(1,-1),
$$

where $O$ is the block diagonal matrix of the fixed preparation
rotations. The first two blocks recover both pairs after
undoing their rotations. This proves the exact static readout
without an affine update claim.

Under a probability command,

$$
z_\beta'=\sqrt{\frac{k+s}{k}}\,z_\beta.
$$

Take $0<|s|<\ell$, so there is an open interval of lawful
starting heights. If an affine map on these four coordinates
represented this command, its last two coordinates would have
the form

$$
c+M z_\alpha+N z_\beta
 =\sqrt{\frac{k+s}{k}}\,z_\beta
$$

at every such height and all phases. At a fixed height,
$\alpha$ and $u$ range independently over their circles.
Comparing opposite $\alpha$ at fixed $u$ forces $M=0$,
since the positive-radius $\alpha$ circle spans its plane.
Comparing opposite $u$ then forces $c=0$ and
$N=\sqrt{(k+s)/k}\,I_2$.
For two different lawful heights this is impossible:
the square of the scalar is $1+s/k$, which is nonconstant
when $s\ne0$. Thus these static coordinates already fail
this one short nonzero affine probability update.

The $E_\sigma$ coordinates instead obey all the affine
continuation requirements, but cannot decode the same
coherence by Corollary 10.16. Equality of coordinate counts
does not identify the representations or their readout
contracts. No coordinate optimality statement is added.
$\square$

**Proposition 10.18 (Why the command and support hypotheses matter).**
The classification uses a positive-width interval of positive
support and the full lawful real probability and phase
commands. The following changes specify different problems.

**Proof and examples.** For a fixed-height closed-loop
endpoint task, initialize at a positive height $h$ and query
only histories returning to that height with total relation
increment $t=2\pi m$, $m\in\mathbb Z$.
Then the actual endpoint difference is
$\alpha=\pi m$ modulo $2\pi$, relative to the preparation.
The endpoint states have coordinates
$(h,u,v)$ with $\alpha=u-v\in\{0,\pi\}$.
Every common phase at either parity is attainable by a
finite two-height rectangle and a phase leg, provided a
positive-width native interval is available to the producing
loops.

On this endpoint source use

$$
E_{\rm loop}(h,u,v)=
 \bigl(\cos u,\sin u,\varepsilon\bigr),\qquad
\varepsilon=e^{i(u-v)}\in\{1,-1\}.
$$

For a prescribed loop with total $t=2\pi m$, zero final
probability displacement and mixed integral $J$, its native
first-group increment is the fixed real number

$$
\gamma=\pi m-\frac{2\pi mh}{r}-\frac Jr.
$$

The endpoint update is the linear map

$$
(z,\varepsilon)\longmapsto
 (R_\gamma z,(-1)^m\varepsilon).
$$

It retains common phase and both parity values. If all
producing and continued loops have zero winding, then
$\alpha=0$ and $U(u)$ alone gives the corresponding
two-coordinate endpoint realization. These endpoint
contracts do not require an affine representation of
every intermediate $P_s$ and $Q_t$ state. Their updates
therefore do not contradict Theorem 10.12.
Likewise the reduced relation angle $2(u-v)$ is a different
read quantity from the full retained difference circle
$u-v$ on the actual source.

If the band collapses to $a=b=k_*\in(0,H)$, there are no
two-height rectangles. On the inherited full torus, the
continuous map

$$
E_{\rm tor}(u,v)=(\cos u,\sin u,\cos v,\sin v)
$$

is injective and has phase update
$R_{(1/2-k_*/r)t}\oplus R_{-k_*t/r}$.
Only $P_0$ has a nonempty domain. Histories confined from
the start to that one height can reach a smaller subset
than this formal full torus; the example does not assert
full singleton-band reachability.

For probability commands alone on a positive-width band,
$(k,U(u),U(v))$ is an injective continuous affine factor:
$P_s$ just adds $s$ to the first coordinate. It supplies
no full phase-update contract. More generally no
classification of all reduced real command menus follows
from the full-menu argument.

For any nondegenerate interval $J\subset(0,H)$ with open,
closed or half-open endpoint convention, the same factor
classification applies with guard $k,k+s\in J$.
To see this, put $a=\inf J$, $b=\sup J$ in the open-strip
argument. All strip translates and overlaps are interior.
Add the endpoint step of Lemma 10.3 only for endpoints
actually in $J$. The two short-rectangle domains still
cover $J$ with an open overlap. The affine, spectral and
separating arguments then apply exactly as stated.
This includes the full open positive fiber $(0,H)$;
its excluded endpoints are never used as states.
An extremal displacement has only an endpoint slice when
both endpoints are included, and otherwise has empty
domain. Such commands are never promoted to global source
bijections.

Support assumptions cannot be dropped by endpoint notation.
At $k=0$ or $k=H$ one group has zero amplitude, so its
phase circle is no longer recoverable from the ray.
At $Z=0$ the common bottom phase becomes global phase
on the remaining support. At $Z=1$ there is no positive
height interval. The source quotient changes in these
cases. Generic fixed means, a single wall, and these
support boundaries have no factor classification proved
by this appendix.

Finally, a retained-lift source
$I\times\mathbb R^2$ has different equality of states.
There the three coordinates $(k,u,v)$ do have affine
updates

$$
P_s(k,u,v)=(k+s,u,v),\qquad
Q_t(k,u,v)=
 \left(k,u-\frac tr k+\frac t2,v-\frac tr k\right),
$$

and the integrated path formulas of Proposition 10.9 are
also affine in those coordinates. But $(k,u+2\pi,v)$
and $(k,u,v)$ represent the same actual ray and different
retained-lift coordinates. This is not a current-ray
factor. In particular a history encoder may retain a
different lift after a returned ray; the universal
current-ray equivalences do not automatically apply to
such history encoders. $\square$

### 10.7 Contribution, finite execution and remaining questions

The source-specific content here is the exact classification of
universal identifications under the full native guarded affine
factor contract. The common circle has the exact intersection
kernel $2\pi\mathbb Q/(2\pi\mathbb Z)$ across arbitrary finite
factors, while continuous factors have precisely the universal
quotient $(k,u-v)$. Boundedness on each common orbit already
forces the common-circle quotient. These conclusions combine
the actual-ray preparation bridge, strip spanning, exact
rectangle gluing, unipotent action and four-coordinate
separating constructions. They do not classify every individual
finite affine representation.

The ingredients are classical: finite-dimensional affine
spanning and homogenization, determinants on generalized
eigenspaces, divisibility and characteristic-zero unipotence,
transcendence bases and extension of algebraic-closure
isomorphisms by Zorn's lemma, the regularity obstruction for
nonlinear solutions of Cauchy's additive equation, the
Steinhaus difference-set argument in its measure proof, and
finite Galois orbit sums. Their required bridges are proved
above. The use of these ingredients and their native
composition does not assert worldwide novelty or an exhaustive
literature comparison. These are ordinary handwritten
mathematical proofs, not kernel-certified declarations.

All source points, witness turns and command words used here
have exact finite native realizations from the fixed
preparation, with finite phase variation. The divisibility,
finite-order and unbounded-orbit arguments quantify over
arbitrarily long but individually finite words. They impose
no uniform speed, duration, phase-height or variation budget,
and perform no infinite-history execution. The unregularized
counterexamples are evaluated directly; no continuity-based
passage from approximate trajectories to their encodings
is available. Exact initialization, exact reals and exact
affine identities remain the contract.

The existence or impossibility of a single finite factor
separating all irrational common-turn cosets simultaneously
is unresolved here. So are minimum coordinate dimensions,
a general classification under mere measurability, and the
other reduced command and support regimes not covered above.
The nonmeasurability theorem describes the supplied
choice-based examples; it is not a substitute for that
general measurable classification.

Finite real coordinate count supplies no finite-bit memory,
finite-precision stability, robustness, finite-shot source
acquisition, effective evaluation, physical implementation,
training or actual machine-learning benefit. The pathological
coefficients and choice dependence are part of the examples.
No output-approximation construction or full-open approximation
settlement is added by this classification.

The unrelated original alternative of an attainer at some
finite $N$ versus a strict gap for every finite $N$ remains
unresolved. No bridge identifying that objective with this
factor contract has been proved. The static results, the
earlier band approximation results and the one-command
lossless obstruction retain their own hypotheses and proof
scope; they are not being restated as new solutions of that
alternative.

## 10.99 追加锚
