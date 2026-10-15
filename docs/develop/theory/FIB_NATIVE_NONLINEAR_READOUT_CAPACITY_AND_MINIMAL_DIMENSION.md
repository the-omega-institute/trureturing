# Native nonlinear readout capacity and minimal real dimension

This volume is reference input. Its proofs are ordinary handwritten
mathematics, unverified by Lean. They do not carry kernel-verified status.

Keep the actual full-open native current-ray source, all real probability
and phase commands, exact state-independent finite affine updates, and the
original ten-output Euclidean error. Allow the readout to be one arbitrary
fixed deterministic function of the current encoding. Then two real
coordinates attain the unavoidable error

$$
e_*=2\sqrt{ZH}=\sqrt{2Z(1-Z)},\qquad H=(1-Z)/2,
$$

for every $0<Z<1$. A single real coordinate has exactly the same minimax
error as a constant prediction. Below $Z=2/3$ this error is strictly
larger than $e_*$, making two the sharp minimum dimension at the floor.
At and above that transition, a constant factor attains the floor under
literal domain identities, while recovering command lawfulness requires
one coordinate. The complete dimension and tolerance tables are in §9.

The common-turn collision and the retained quotient $(k,\alpha)$ are
prior results. The increment here is the sharp minimax and minimum real
dimension classification after changing only the readout class. Sections
1 and 3 reconstruct the source and the prior collision mechanism needed
for the lower proofs. Section 10 gives the precise correspondence to the
factor, full-open affine-readout, and observation/purity sources.

## 1. Actual native rays and the unchanged output metric

**Definition 1.1 (Source, preparation and controls).** Fix $0<Z<1$,
$r=1-Z$ and $H=r/2$. In mode order $(0,1,2,3,13)$ put

$$
p(k)=(k,H-k,Z,H-k,k),\qquad 0<k<H,
\qquad d=(1,-1,0,-1,1)^{\mathsf T}.
$$

Fix one arbitrary preparation height $k_0\in(0,H)$ and arbitrary
preparation phases $\theta^{\rm in}$. All producing histories start
from that preparation. The negative-phase convention and native law are

$$
\psi_j=\sqrt{p_j}\,e^{-i\theta_j},\qquad
\dot p=d\dot k,\qquad
\dot\theta_j=\frac{d_j}{p_j(k)I(k)}\dot\chi,
\qquad
I(k)=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}.
$$

A history is piecewise $C^1$ or absolutely continuous on a finite
compact time interval, stays strictly inside $0<k<H$ at every time,
and has finite phase variation. Its initial real relation lift agrees
with $d^{\mathsf T}\theta^{\rm in}$. A query may occur at any finite
prefix; no closing loop or winding restriction is imposed. The state
queried is the actual ray, rather than a history or a retained real lift.
Write $\mathbb T=\mathbb R/(2\pi\mathbb Z)$.

**Lemma 1.2 (Native circle coordinates).** The phase increments
$h=\theta-\theta^{\rm in}$ have the form $(u,v,0,v,u)$, and

$$
I(k)=\frac r{k(H-k)},\qquad
du=\left(\frac12-\frac kr\right)d\chi,\qquad
dv=-\frac kr\,d\chi.
$$

Set $\alpha=u-v$ and $\beta=u$. They are independent circle
coordinates, with inverse $u=\beta$, $v=\beta-\alpha$, and

$$
d\alpha=\frac12d\chi,\qquad
d\beta=\left(\frac12-\frac kr\right)d\chi.
$$

With $\eta_j=\theta_j^{\rm in}-\theta_2^{\rm in}$, a representative is

$$
\psi(k,u,v)=\left(
\sqrt{k}e^{-i(\eta_0+u)},
\sqrt{H-k}e^{-i(\eta_1+v)},
\sqrt Z,
\sqrt{H-k}e^{-i(\eta_3+v)},
\sqrt{k}e^{-i(\eta_{13}+u)}
\right).
$$

Two such representatives define the same ray exactly when their heights
and both circle coordinates agree.

**Proof of Lemma 1.2.** The probabilities sum to $2H+Z=1$ and are
strictly positive. The reciprocal sum is $2/k+2/(H-k)=r/[k(H-k)]$.
The positive-group rate is $(H-k)/r=1/2-k/r$, the negative-group rate
is $-k/r$, and the middle rate is zero. Integration from zero increments
gives the two groups. This equates increments only; it imposes no
equality on preparation phases. Subtraction proves the difference
equation. The coordinate changes and their inverses have integer
coefficients, so they descend to inverse maps on $\mathbb T^2$.
Along actual real lifts, $d^{\mathsf T}h=2(u-v)=\chi-\chi(0)$.

The displayed gauge fixes the middle amplitude at the positive number
$\sqrt Z$. Equality of rays therefore forces their common scalar phase
to be one. Moduli determine $k$, and the nonzero amplitudes in the two
groups determine $u,v$ separately modulo $2\pi$. These conditions also
suffice. In particular a common bottom turn is observable relative to
the middle mode and is not a removable ray gauge. $\square$

**Proposition 1.3 (Exact reachability and all real relative commands).**
The current-ray source is exactly

$$
\mathcal M=(0,H)\times\mathbb T^2,
$$

with coordinates $(k,\alpha,\beta)$. Every point is reachable by a
finite native history from the fixed preparation. The straight commands,
for every signed real $s,t$, are

$$
P_s(k,\alpha,\beta)=(k+s,\alpha,\beta),\qquad
\operatorname{dom}P_s=\{(k,\alpha,\beta):0<k+s<H\},
$$

$$
Q_t(k,\alpha,\beta)=
\left(k,\alpha+\frac t2,\beta+\left(\frac12-\frac kr\right)t\right),
\qquad \operatorname{dom}Q_t=\mathcal M.
$$

The command parameter $t$ is real and is not reduced modulo a period.

**Proof of Proposition 1.3.** A probability leg holds $\chi$ fixed;
a phase leg holds $k$ fixed. Integrating Lemma 1.2 gives the stated
commands. A straight probability segment remains interior exactly when
its endpoint is interior, by convexity. Every finite real phase leg
is lawful at every interior height.

Choose $k_1\ne k_0$ in $(0,H)$. For any target real representatives
$u,v$ put

$$
L=2(u-v),\qquad
u_L=\left(\frac12-\frac{k_0}{r}\right)L,\qquad
v_L=-\frac{k_0}{r}L,\qquad c=u-u_L=v-v_L.
$$

The chronological rectangle $P_s,Q_t,P_{-s},Q_{-t}$, whenever its
probability legs are lawful, fixes $k,\alpha$ and adds $-st/r$ to
$\beta$, equivalently to both $u,v$. Indeed the two phase rates differ
by $-s/r$. Take $s=k_1-k_0$ and $t=-rc/s$ to add $(c,c)$ at $k_0$.
Then perform $Q_L$ there and $P_{k-k_0}$ to the target height. The
endpoint increments are $(u,v)$. All heights along these legs lie
between interior endpoints, and all parameters and variations are
finite. Lemma 1.2 gives the converse inclusion and the exact equality
of rays. No extra independent phase control was introduced. $\square$

**Definition 1.4 (The original ten outputs).** Keep the ordered edges

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)).
$$

For $(i,j)\in\mathcal E$ use

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,
\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|.
$$

With $\delta_{ij}=\theta_i^{\rm in}-\theta_j^{\rm in}$, their
expectation pair is

$$
y_{ij}=2\sqrt{p_ip_j}
\binom{\cos(\delta_{ij}+h_i-h_j)}
      {\sin(\delta_{ij}+h_i-h_j)}.
$$

Concatenation in that edge order defines $y:\mathcal M\to\mathbb R^{10}$.
All errors use its original Euclidean norm. No pair is normalized,
whitened or reweighted in the task.

**Lemma 1.5 (Exact metric factorization).** Put

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

Here $a,b\in\mathbb R^2$. Then

$$
y(k,\alpha,\beta)=D(A(k)U(\alpha),B(k)U(\beta)),\qquad
D^{\mathsf T}D=4I_2\oplus I_2,
$$

$$
\|D(a,b)\|_2^2=4\|a\|_2^2+\|b\|_2^2,\qquad
\|y(k,\alpha,\beta)\|_2^2=16k(H-k)+4Zk.
$$

**Proof of Lemma 1.5.** The negative phase convention gives
$\overline\psi_i\psi_j=\sqrt{p_ip_j}e^{i(\theta_i-\theta_j)}$.
The two Hermitian expectations are twice its real and imaginary parts.
The five increment differences are $\alpha,\beta,\alpha,-\alpha,-\alpha$.
Since $U(-\alpha)=JU(\alpha)$, the output is exactly $D$ as written.
Four blocks contain the first pair, and one contains the second pair;
their coordinate supports are disjoint. The preparation rotations and
$J$ are orthogonal. Summing squared block norms proves every displayed
identity. The factor of four is a consequence of the original metric,
not a replacement for it. $\square$

## 2. Arbitrary readout, dimension budgets and distinct contracts

**Definition 2.1 (Literal affine factor with arbitrary readout).** For
some finite integer $m\ge0$, take any function
$E:\mathcal M\to\mathbb R^m$. For each real $s,t$ take fixed ambient
affine maps

$$
\mathcal U_s(z)=A_sz+b_s,\qquad
\mathcal V_t(z)=C_tz+d_t,
$$

and require exactly

$$
E(P_sx)=\mathcal U_s(E(x))\quad(x\in\operatorname{dom}P_s),\qquad
E(Q_tx)=\mathcal V_t(E(x))\quad(x\in\mathcal M).
$$

An empty probability domain imposes no identity. The coefficients may
depend on the fixed task, preparation, model and command, but not on
the current state or its producing history. Both update offsets are
allowed. No ambient invertibility or group law is assumed.

The readout is one fixed deterministic function
$\mathcal R:E(\mathcal M)\to\mathbb R^{10}$. Define

$$
q(x)=\mathcal R(E(x)),\qquad
\operatorname{err}(E,\mathcal R)
=\sup_{x\in\mathcal M}\|q(x)-y(x)\|_2\in[0,+\infty].
$$

There is no continuity, measurability, computability, boundedness or
injectivity requirement on $E$ or $\mathcal R$, and no parameter
regularity requirement on the command maps. An arbitrary affine readout
$c+Lz$, with any offset $c$, is included in this readout class. Thus the
change of class does not discard a readout offset. An ambient extension
of $\mathcal R$ is optional. Its only varying input is the current
encoded point: neither height, an angle lift, a history, nor an external
selector is supplied separately. Decoded vectors need not be native
physical outputs. Initialization and affine updates are exact real
operations.

**Definition 2.2 (Capacities and tolerances).** For an integer $n\ge0$
let $\mathfrak F_{\le n}^{\rm arb}(Z)$ be the models of Definition 2.1
with some $0\le m\le n$. Set

$$
e_n^{\rm arb}(Z)=
\inf_{F\in\mathfrak F_{\le n}^{\rm arb}(Z)}\operatorname{err}(F),
$$

$$
\mathcal A_n^{\rm arb}(Z)=
\{\epsilon\in[0,\infty):
\exists F\in\mathfrak F_{\le n}^{\rm arb}(Z),\quad
\operatorname{err}(F)\le\epsilon\}.
$$

The infimum of an empty class is $+\infty$. Preparation is fixed in
each class and arbitrary in all results; it is suppressed in the notation.
Its phases change only the fixed orthogonal $O$, and its height changes
producing paths, not $\mathcal M$.

These are dimension-at-most budgets. A model in $\mathbb R^m$ can be
padded into $\mathbb R^n$ by $E'(x)=(E(x),0)$, extending every update
by the identity on unused coordinates and making readout ignore them.
This preserves the error and every identity. It does not enlarge the
actual affine hull of the image. No assertion is made about a different
class requiring that hull to have dimension exactly $n$. No identification
of these capacities with the original finite-hidden-$N$ objective is assumed.

**Definition 2.3 (Recoverable guards).** The guard subclass additionally
requires, for every real $s$, a function

$$
g_s:E(\mathcal M)\to\{0,1\},\qquad
g_s(E(k,\alpha,\beta))=1
\ \Longleftrightarrow\ 0<k+s<H.
$$

Its capacity and finite tolerance set are denoted
$e_{n,g}^{\rm arb}(Z)$ and $\mathcal A_{n,g}^{\rm arb}(Z)$.
No regularity is required of the predicates. The phase guard is always
true. Literal intertwining on a lawful domain does not itself require
the encoding to determine membership in that domain.

**Definition 2.4 (Prescribed-path classes).** A prescribed relative path
specifies the original velocities $a_c=\dot k$, $b_c=\dot\chi$ on
$[0,T]$ in Definition 1.1's regularity class. Write
$\rho(\tau)=\int_0^\tau a_c(v)\,dv$. Its source guard is

$$
0<k+\rho(\tau)<H\quad\text{for every }\tau\in[0,T].
$$

The stronger literal class requires one fixed ambient affine map for
each such prescribed path on that entire guard, including every
intermediate truncation. The stronger guard class additionally requires
its lawfulness indicator to be a function of the current encoding.
Superscript $\mathrm{arb,path}$ denotes the corresponding capacities
and tolerance sets. Every execution and concatenation is finite, with
finite phase variation, but there is no uniform command magnitude,
duration, length or variation bound. Section 8 derives the endpoint
formula directly from the native equations and verifies these stronger
contracts for the optimal witnesses.

## 3. The prior rational collision, with its full-open bridge

This section reconstructs the rational common-turn erasure of the factor
source [F, §10]. It is used as prior mathematical content, not claimed
as a new factor classification. Its proof is included to keep the
arbitrary-readout lower bound independent of any regularity or affine-
observable assumption.

Let $\mathscr L=\operatorname{aff}E(\mathcal M)$ for any factor in
Definition 2.1. Affine maps agreeing on a set agree on its affine hull,
because they preserve finite affine combinations with coefficients
summing to one.

**Lemma 3.1 (Every open height strip spans the actual affine hull).**
For every nonempty open interval $I\subset(0,H)$,

$$
\operatorname{aff}E(I\times\mathbb T^2)=\mathscr L.
$$

**Proof of Lemma 3.1.** Denote the hull for $I$ by $\mathscr L_I$.
If $I,I+s\subset(0,H)$, the lawful identities give
$\mathcal U_s\mathscr L_I=\mathscr L_{I+s}$ and the reverse equality
for $-s$. The two compositions are identities on the respective encoded
strips and hence on their hulls. These hulls are affinely isomorphic.

Choose an open interval $I_0$ whose hull has the minimum possible
dimension $d$. A minimum exists among the finitely many integer values
$0,\ldots,m$. Shrink $I_0$ to have interior closure and length less
than $H$. Inclusion and minimality leave its hull dimension equal to
$d$. Every translate with interior closure has the same hull dimension.
If two such translates overlap, the intersection is a nonempty open
interval. Its hull has dimension at least $d$ and lies in both hulls of
dimension $d$, so those hulls coincide.

The permissible translation parameters form an interval. Any two can
be joined by finitely many steps smaller than the length of $I_0$,
giving an overlapping chain. Thus all these translates have the same
hull. They cover $(0,H)$, so their common hull is $\mathscr L$.
Any other open strip has its hull contained in this space and dimension
at least $d$, and therefore has that same hull. This also covers $d=0$.
Only finite affine combinations and lawful translations were used; no
limit of encoder values at any height was taken. $\square$

**Lemma 3.2 (Derived automorphisms on the hull).** For $|s|<H$,
$\mathcal U_s|_{\mathscr L}$ is an affine automorphism with inverse
$\mathcal U_{-s}|_{\mathscr L}$. Every $\mathcal V_t$ restricts to an
affine automorphism, and on $\mathscr L$,

$$
\mathcal V_t\mathcal V_h=\mathcal V_{t+h},\qquad
\mathcal V_0=\operatorname{id},\qquad
\mathcal V_t^{-1}=\mathcal V_{-t}.
$$

**Proof of Lemma 3.2.** For $|s|<H$ choose a nonempty open strip
whose translate by $s$ remains interior. Both hulls in the preceding
proof are now $\mathscr L$, proving the inverse assertion. Every
$Q_t$ is a global source bijection. Its source composition, inverse
and identity laws hold on $E(\mathcal M)$ and extend by affine
spanning. They are laws on the actual hull, not on unused ambient
directions. A probability command remains a partial source map, even
when its affine restriction to $\mathscr L$ is invertible. $\square$

**Proposition 3.3 (Gluing the abstract common-circle action).** Define
$C_c(k,\alpha,\beta)=(k,\alpha,\beta+c)$ for $c\in\mathbb T$.
There is a unique abstract homomorphism

$$
\mathcal T:\mathbb T\to\operatorname{Aff}(\mathscr L),\qquad
\mathcal T_cE(x)=E(C_cx).
$$

It commutes with every restricted $\mathcal V_t$ and each restricted
$\mathcal U_s$ with $|s|<H$. On $\mathscr L$ the rectangle identity is

$$
\mathcal V_{-t}\mathcal U_{-s}\mathcal V_t\mathcal U_s
=\mathcal T_{-st/r}\qquad(|s|<H).
$$

**Proof of Proposition 3.3.** Choose $0<s_0<H/2$. For a real
representative $c$, use $s=s_0$ and $s=-s_0$ separately, with
$t=-rc/s$. Lemma 3.2 makes each affine word in the display an
automorphism of $\mathscr L$. Proposition 1.3's native rectangle
calculation makes it implement $C_c$ on the domain of its first
probability leg. The two height domains are $(0,H-s_0)$ and
$(s_0,H)$. They cover the whole open interval and overlap in the
nonempty strip $(s_0,H-s_0)$. Lemma 3.1 makes that strip span
$\mathscr L$, so the two words agree on all of $\mathscr L$.
Their common value implements $C_c$ on every source point.

The source identities $C_{c+d}=C_cC_d$, $C_0=\operatorname{id}$
and $C_{c+2\pi}=C_c$ transfer by affine spanning. This proves the
abstract circle homomorphism, its inverses and uniqueness. Common turns
commute with $Q_t$ everywhere and with $P_s$ on its unchanged lawful
domain. That domain contains an open strip when $|s|<H$, so these
commutation identities transfer to the hull as well. Finally the
rectangle identity for any such $s,t$ holds on a spanning lawful
strip and hence on the hull. No independently available common-turn
control or continuity of the action is assumed. $\square$

**Theorem 3.4 (Rational common turns have identical encodings).** Every
finite factor of Definition 2.1 obeys

$$
E(k,\alpha,\beta+2\pi q)=E(k,\alpha,\beta)
\qquad(q\in\mathbb Q).
$$

**Proof of Theorem 3.4.** If $\mathscr L$ is a point the assertion
is immediate. Otherwise choose affine coordinates of dimension
$d=\dim\mathscr L$, set $N=d+1$, and homogenize every affine
automorphism as

$$
z\mapsto Mz+b
\quad\longmapsto\quad
\widehat F=\begin{pmatrix}M&b\\0&1\end{pmatrix}.
$$

This faithful representation preserves multiplication and retains all
offsets. Complexify the homogeneous space. Fix $c$ and an eigenvalue
$\lambda\ne0$ of $\widehat{\mathcal T}_c$. Its generalized
eigenspace

$$
V_\lambda=\ker(\widehat{\mathcal T}_c-\lambda I)^N
$$

has some dimension $1\le j\le N$. Centrality in Proposition 3.3
makes all rectangle factors and their inverses preserve this space.
Taking $s=s_0$ and $t=-rc/s_0$, the rectangle restricted to it gives

$$
\widehat{\mathcal T}_c|_{V_\lambda}
=(\widehat{\mathcal V}_t|_{V_\lambda})^{-1}
 (\widehat{\mathcal U}_{s_0}|_{V_\lambda})^{-1}
 (\widehat{\mathcal V}_t|_{V_\lambda})
 (\widehat{\mathcal U}_{s_0}|_{V_\lambda}).
$$

The determinant on the right is one. The left is $\lambda I$ plus
a nilpotent map, with determinant $\lambda^j$. Hence $\lambda^j=1$.

Apply this conclusion to $\widehat{\mathcal T}_{c/N!}$. Each of its
eigenvalues has order dividing an integer between $1$ and $N$, hence
dividing $N!$. The abstract action law gives

$$
\widehat{\mathcal T}_c
=(\widehat{\mathcal T}_{c/N!})^{N!}.
$$

Every eigenvalue of this power is one. This follows, for example, by
upper triangularizing the single complex matrix, using an eigenvector
and induction on the quotient dimension; powers raise its diagonal
entries to those powers. Cayley–Hamilton now gives
$(\widehat{\mathcal T}_c-I)^N=0$.

For $c=2\pi q$ with $q\in\mathbb Q$, some integer $a>0$ also
gives $\widehat{\mathcal T}_c^a=I$ by the circle law. Its minimal
polynomial divides both $(X-1)^N$ and $X^a-1$. In characteristic zero
the root one of $X^a-1$ is simple, since its derivative there is $a$.
The greatest common divisor is $X-1$, so
$\widehat{\mathcal T}_c=I$. Evaluating at $E(x)$ proves the theorem.

This is a direct full-open proof of the mechanism in [F, Theorem 10.6
and Proposition 10.18]. Equivalently, a full-open model restricts to
each positive closed interior band, and the same prior theorem on a
band containing a given height proves its collision there. Neither
argument evaluates an encoder at an excluded endpoint. No common fixed
point, bounded image, regularity, or decoder hypothesis entered the
proof. $\square$

## 4. An arbitrary decoder still has a positive floor

**Theorem 4.1 (Universal original-output floor).** Every model of
Definition 2.1 satisfies

$$
\operatorname{err}(E,\mathcal R)\ge e_*=2\sqrt{ZH}.
$$

**Proof of Theorem 4.1.** At any interior height compare
$x=(k,\alpha,\beta)$ and $x'=(k,\alpha,\beta+\pi)$. They are
actual reachable rays. Theorem 3.4 makes their encodings equal, so
their deterministic predictions are the same vector $v$. Their four
bottom-edge pairs agree, while their $02$ pairs are opposite. By
Lemma 1.5,

$$
\|y(x)-y(x')\|_2
=\|D(0,2B(k)U(\beta))\|_2=2B(k).
$$

The triangle inequality gives
$\max\{\|v-y(x)\|_2,\|v-y(x')\|_2\}\ge B(k)$.
Taking the supremum of $B(k)=2\sqrt{Zk}$ over $0<k<H$ proves the
bound. This is a supremum of explicit target values; there is no
endpoint encoding or limiting evaluation of the decoder. Infinite
error satisfies the bound as well. $\square$

**Proposition 4.2 (Exact residual on a rational orbit with prediction
fixed).** Suppose a model has error at most a finite $\epsilon$.
For each $x=(k,\alpha,\beta)$ decompose its single prediction uniquely as

$$
q(x)=D(a_x,b_x)+w_x,\qquad w_x\perp\operatorname{im}D.
$$

Then

$$
\|w_x\|_2^2+4\|a_x-A(k)U(\alpha)\|_2^2
+(\|b_x\|_2+B(k))^2\le\epsilon^2.
$$

At $\epsilon=e_*$ this is equivalently

$$
\|w_x\|_2^2+4\|a_x-A(k)U(\alpha)\|_2^2
+\|b_x\|_2^2+2B(k)\|b_x\|_2\le4Z(H-k).
$$

**Proof of Proposition 4.2.** Since $D^{\mathsf T}D$ is invertible,
put $(a_x,b_x)=(D^{\mathsf T}D)^{-1}D^{\mathsf T}q(x)$ and
$w_x=q(x)-D(a_x,b_x)$. This gives the unique orthogonal
decomposition, including predictions outside $\operatorname{im}D$.
Every rational-turn state $x_q=(k,\alpha,\beta+2\pi q)$ has exactly
the same prediction by Theorem 3.4. Its squared error is

$$
\|w_x\|_2^2+4\|a_x-A(k)U(\alpha)\|_2^2
+\|b_x-B(k)U(\beta+2\pi q)\|_2^2.
$$

The rational turns are dense in the circle. With $q(x)$ fixed, this
explicit target expression is continuous in the angle. Its supremum
over rational turns is its maximum over the circle. The last term has
maximum $(\|b_x\|_2+B(k))^2$, by choosing the opposite unit direction
to $b_x$ when $b_x\ne0$; when $b_x=0$ it is constant. This proves
the first inequality. Subtracting $B(k)^2=4Zk$ from the floor value
$e_*^2=4ZH$ gives the second.

The continuity used here belongs only to the displayed target response
with its prediction frozen. The assertion does not make $q(x)$
independent of $\beta$ on different irrational common-turn cosets.
It does not turn an arbitrary readout into an affine observable.
$\square$

## 5. A two-coordinate attainer with linear native updates

**Definition 5.1 (The annular representation and its fixed readout).**
Set

$$
E_2(k,\alpha,\beta)=\exp(k/H)U(\alpha)\in\mathbb R^2,
\qquad
\mathscr S_2=\{z\in\mathbb R^2:1<\|z\|_2<\exp(1)\}.
$$

On $\mathscr S_2$ define

$$
K(z)=H\log\|z\|_2,\qquad
\mathcal R_2(z)=D\left(A(K(z))\frac{z}{\|z\|_2},0\right).
$$

This is one fixed nonlinear readout. If an ambient function is desired,
assign the value zero to every $z\notin\mathscr S_2$. No operation
ever uses that extension on a lawfully encoded execution.

**Proposition 5.2 (Exact image, fibers and branch-free decoding).**
The actual image of $E_2$ is exactly $\mathscr S_2$. Its fibers are
exactly the $\beta$ circles at fixed $(k,\alpha)$. The functions in
Definition 5.1 are well-defined on this image and use no angle branch
or extra input.

**Proof of Proposition 5.2.** The norm of an encoded vector is
$\exp(k/H)$, which lies strictly between $1$ and $\exp(1)$.
Conversely, for any $z\in\mathscr S_2$, the height
$k=H\log\|z\|_2$ is interior and the unit vector $z/\|z\|_2$
is $U(\alpha)$ for one circle class. Proposition 1.3 realizes that
height and circle class with every $\beta$. Thus all and only points
of the annulus occur. Equality of encodings gives equal norms, then
equal heights and unit directions, hence equal $\alpha$. Conversely
those two equalities suffice, independently of $\beta$.

The norm is positive and its logarithm gives $0<K(z)<H$. The
square-root argument in $A(K(z))$ is positive, and division by the
norm is defined. The readout uses the unit vector itself, not a chosen
real argument for it. The sole varying input is $z$. In particular
this is a different coordinate realization of the already known
quotient $(k,\alpha)$, not a new discovery of that quotient.
$\square$

**Proposition 5.3 (All signed affine commands and exact guards).** For
every real $s,t$ define ambient linear maps

$$
\mathcal U_s^{(2)}(z)=\exp(s/H)z,\qquad
\mathcal V_t^{(2)}(z)=R_{t/2}z.
$$

They satisfy all identities in Definition 2.1. On the actual image the
probability guard is exactly

$$
0<K(z)+s<H
\quad\Longleftrightarrow\quad
1<\exp(s/H)\|z\|_2<\exp(1),
$$

and the phase guard is all of $\mathscr S_2$.

**Proof of Proposition 5.3.** Direct substitution gives

$$
\mathcal U_s^{(2)}E_2(k,\alpha,\beta)
=\exp((k+s)/H)U(\alpha)=E_2(P_s(k,\alpha,\beta))
$$

whenever the source command is lawful. Similarly rotation gives
$\exp(k/H)U(\alpha+t/2)=E_2(Q_t(k,\alpha,\beta))$.
The actual change of $\beta$ under $Q_t$ is present in the source;
only this encoder ignores it. The displayed guard is precisely the
original height guard, since $K(E_2(x))=k$. It is equivalent to the
norm condition by strict monotonicity of the exponential. These
identities prove image preservation on the guard, and every rotation
preserves the whole annulus. All coefficients depend only on the
command and fixed $H$. Both signs and zero commands are included.
When $|s|\ge H$ the source guard is empty, while the same ambient
linear formula remains defined. $\square$

**Theorem 5.4 (Attainment of the floor in two real coordinates).** The
model $(E_2,\mathcal R_2)$ has

$$
\|\mathcal R_2(E_2(k,\alpha,\beta))-y(k,\alpha,\beta)\|_2^2
=4Zk,
\qquad \operatorname{err}(E_2,\mathcal R_2)=e_*.
$$

It recovers every straight-command guard. From exact initialization it
stays exactly encoded at every finite lawful command prefix and at
every intermediate point of each straight leg, with the same uniform
readout error.

**Proof of Theorem 5.4.** On the source the readout is exactly
$D(A(k)U(\alpha),0)$. Lemma 1.5 makes the squared error
$\|D(0,B(k)U(\beta))\|_2^2=B(k)^2=4Zk$. Its supremum is $4ZH$.
Every individual lawful state has strictly smaller error than $e_*$;
attainment refers to this model's error supremum. Neither boundary
circle of the annulus, nor $k=0,H$, is encoded as a source state.

At the fixed preparation the increments are zero, so initialize

$$
z_0=\exp(k_0/H)\binom{1}{0}.
$$

All arbitrary preparation phases remain in the fixed matrix $D$.
Alternatively, initialize any actual current ray $x_0$ exactly at
$E_2(x_0)$. If the current latent point is $E_2(x)$, Proposition 5.3
makes the next lawful affine update exactly $E_2$ of the next ray.
Induction proves every finite prefix. Applying $P_{\tau s}$ or
$Q_{\tau t}$ for $0\le\tau\le1$ from the preceding point proves
every intermediate state on a straight leg. The same pointwise error
formula applies at each state. The approximate output is never
substituted for a latent state.

The four bottom-edge pairs are read exactly; the $02$ prediction is
their omitted reference pair's center. Every native ray has a positive
$02$ radius, so this decoded vector is outside the exact native output
image. Definition 2.1 permits that. It changes neither the actual
source ray nor its guard. $\square$

## 6. The sharp affine-line obstruction without regularity

Define the finite constant

$$
R_0=\sup_{0<k<H}\sqrt{16k(H-k)+4Zk}.
$$

The following proof depends on the affine dimension of the actual image,
not on any topology or intrinsic dimension of the source.

**Lemma 6.1 (Real phase actions on an affine line have positive slopes).**
If $\dim\operatorname{aff}E(\mathcal M)=1$, choose any affine
coordinate on that line. The restricted phase maps have the form
$F_t(z)=a_tz+b_t$ with $a_t>0$. For any affine map $F(z)=az+b$ with
$a>0$, every finite-period point is a fixed point.

**Proof of Lemma 6.1.** Global source bijectivity of each $Q_t$ makes
$\mathcal V_t$ map the affine hull onto itself. Its restriction has
an inverse, and the group law follows by equality on the encoded
source and affine spanning, as in Lemma 3.2. Thus $a_t\ne0$ and

$$
a_t=a_{t/2}^2>0.
$$

The full real command menu, including halves, supplies this positivity;
no continuity in $t$ was invoked. For a fixed $F(z)=az+b$, iteration
and telescoping give

$$
F^j(z)-z=(1+a+\cdots+a^{j-1})(F(z)-z)\qquad(j\ge1).
$$

One way to see the identity is that
$F^{h+1}(z)-F^h(z)=a^h(F(z)-z)$ for each $h\ge0$. The coefficient
in the sum is strictly positive, so $F^j(z)=z$ implies $F(z)=z$.
This includes $a=1$, every offset $b$, and does not require a common
fixed point of the action. $\square$

**Theorem 6.2 (One-dimensional affine hull forces output antipodes to
collide).** If $\dim\operatorname{aff}E(\mathcal M)\le1$, then

$$
E(k,\alpha+\pi,\beta+\pi)=E(k,\alpha,\beta)
$$

for all actual source points. Every deterministic readout of such a
factor therefore has error at least $R_0$.

**Proof of Theorem 6.2.** A zero-dimensional hull is a point, so its
collision is immediate. Otherwise use the affine line and its phase
action from Lemma 6.1. At the interior height $h=H/2$,

$$
\frac12-\frac hr=\frac14,\qquad
Q_{2\pi}(h,\alpha,\beta)
=(h,\alpha+\pi,\beta+\pi/2).
$$

The fourth power of this source command is the identity on that
height's entire torus. Equivariance gives
$F_{2\pi}^4(E(h,\alpha,\beta))=E(h,\alpha,\beta)$.
Lemma 6.1 forces $F_{2\pi}$ to fix this encoded point. Consequently

$$
E(h,\alpha+\pi,\beta+\pi/2)=E(h,\alpha,\beta).
$$

The common turn $\pi/2$ is rational and is erased by Theorem 3.4.
Removing it from the left side gives
$E(h,\alpha+\pi,\beta)=E(h,\alpha,\beta)$.

Now fix any target height $k\in(0,H)$. The single probability command
$P_{k-h}$ is lawful on the whole torus at $h$, and its entire straight
segment is interior. Apply its fixed affine map to the last equality.
This transfers it to

$$
E(k,\alpha+\pi,\beta)=E(k,\alpha,\beta).
$$

Only preservation of equality by that lawful map was used; this transfer
does not assume an off-domain probability identity or an ambient inverse.
Another erased common turn, now $\pi$, gives the claimed collision.

Both phase pairs in Lemma 1.5 change sign under
$(\alpha,\beta)\mapsto(\alpha+\pi,\beta+\pi)$. Hence

$$
y(k,\alpha+\pi,\beta+\pi)=-y(k,\alpha,\beta).
$$

A single prediction $v$ at their common encoding must obey

$$
\max\{\|v-y(k,\alpha,\beta)\|_2,
         \|v+y(k,\alpha,\beta)\|_2\}
\ge\|y(k,\alpha,\beta)\|_2
$$

by the triangle inequality. All witness rays and all commands used
are reachable and finite by Proposition 1.3. Taking the height
supremum proves the lower bound $R_0$. No continuity, boundedness,
measurability, injectivity or affine-readout assumption entered this
argument. It also applies to an affine line embedded in a larger
ambient feature space. $\square$

**Proposition 6.3 (Rational difference-turn erasure on a line and its
limit).** Under the same affine-hull hypothesis,

$$
E(k,\alpha+2\pi q,\beta)=E(k,\alpha,\beta)
\qquad(q\in\mathbb Q).
$$

This conclusion does not force every such factor to ignore all phase
distinctions. In ordinary set theory with choice there is a one-real-
coordinate factor sensitive to an irrational difference-phase turn.

**Proof of Proposition 6.3.** At $h=H/2$, the command $Q_{4\pi q}$
shifts $\alpha$ by $2\pi q$ and $\beta$ by $\pi q$. It has finite
order on this source torus: if $q=p/a$ with $a>0$ integral, $2a$
repetitions return both circles. Lemma 6.1 fixes each encoded point
already after one repetition. Theorem 3.4 removes the rational
$\beta$ shift, and the same lawful transfer from $h$ to $k$ as in
Theorem 6.2 proves the display. The singleton case again is immediate.

For the example choose an irrational $\xi$. Under choice, extend the
$\mathbb Q$-independent set $\{1,\xi\}$ to a basis of $\mathbb R$
over $\mathbb Q$. Define a $\mathbb Q$-linear function
$f:\mathbb R\to\mathbb R$ by $f(1)=0$, $f(\xi)=1$, and zero on
the other basis elements. It is additive and vanishes on $\mathbb Q$.
Set

$$
E_f(k,\alpha,\beta)=f(\alpha/(2\pi)),
$$

where any real representative of $\alpha$ may be used. Another
representative adds an integer to the argument, so the value is
unchanged. This is a function of the current ray, not a retained lift.
Every probability command acts by the identity, and every phase
command acts by the affine translation

$$
z\longmapsto z+f(t/(4\pi)).
$$

These assertions follow directly from the source formulas and
additivity. The states with $\alpha=0$ and $\alpha=2\pi\xi$
have different encodings. Moreover the values at
$\alpha=2\pi j\xi$ are $j$ for integers $j$, so the phase image
is unbounded. This construction provides no regularity or effective
evaluation assertion. It ignores height and cannot recover probability
guards. The zero readout makes it a finite-error model of Definition
2.1, and Theorem 6.2 still supplies its minimax lower bound. For a
prescribed path its exact translation is $z\mapsto z+f(L/(4\pi))$,
where $L$ is the total phase increment in §8; this follows directly
from the path's difference-phase equation. Thus even requiring those
literal path identities does not justify full phase blindness.
$\square$

## 7. Height guards and the low-dimensional optimum

**Proposition 7.1 (All probability guards are equivalent to height
recovery on fibers).** An arbitrary encoder admits all predicates in
Definition 2.3 if and only if each of its fibers has one height.
Equivalently there is a well-defined function
$K_E:E(\mathcal M)\to(0,H)$ with $K_E(E(k,\alpha,\beta))=k$.

**Proof of Proposition 7.1.** Suppose a fiber contains heights
$k<l$. Choose $s=H-(k+l)/2$. Then

$$
k+s=H-(l-k)/2\in(0,H),\qquad l+s=H+(l-k)/2>H.
$$

The two states disagree on the lawfulness of this same command.
A single predicate at their common encoding cannot report both
indicators. Conversely, if height is constant on each fiber, the
assignment $K_E(E(k,\alpha,\beta))=k$ is unambiguous, and
$g_s(z)=1$ exactly when $0<K_E(z)+s<H$ gives all guards. No
continuity or measurable selection is needed: every represented value
has its unique height. $\square$

**Lemma 7.2 (Symbolic value of the constant-prediction radius).**

$$
R_0=
\begin{cases}
1-Z/2,&0<Z<2/3,\\
e_*,&2/3\le Z<1.
\end{cases}
$$

For $Z<2/3$,

$$
R_0^2-e_*^2=\frac{(4H-Z)^2}{4}>0.
$$

**Proof of Lemma 7.2.** Complete the square in the original squared
output norm:

$$
16k(H-k)+4Zk
=-16\left(k-\frac{4H+Z}{8}\right)^2
+\frac{(4H+Z)^2}{4}.
$$

If $Z<4H$, its vertex lies in $(0,H)$, so
$R_0=(4H+Z)/2=1-Z/2$. Subtracting $4ZH$ from its square gives
the displayed positive excess. If $Z\ge4H$, use instead

$$
16k(H-k)+4Zk=4ZH+4(H-k)(4k-Z).
$$

The last term is strictly negative at every interior height and tends
to zero as $k$ tends to $H$ from below. Thus the supremum is $4ZH$.
At $Z=4H$ the difference is exactly $-16(H-k)^2$, so equality of
the parameters is included. Finally $Z<4H=2(1-Z)$ is exactly
$Z<2/3$. These scalar extrema do not require a source state at a
missing endpoint. $\square$

**Proposition 7.3 (Constant and height witnesses).** The literal class
has a zero-dimensional model of error exactly $R_0$. The guard class
has a one-dimensional model of that error and has no zero-dimensional
model at any tolerance.

**Proof of Proposition 7.3.** In $\mathbb R^0$ let $E_0$ be the
unique function to its singleton, use the unique affine map for every
command, and read out zero in $\mathbb R^{10}$. Every lawful identity
holds, including identities on empty domains, and Lemma 1.5 gives
error supremum $R_0$. Theorem 6.2 proves that no constant prediction,
and no competing one-coordinate factor with arbitrary readout, has
smaller error.

For the guard witness use

$$
E_1(k,\alpha,\beta)=k,\qquad
\mathcal U_s^{(1)}(K)=K+s,\qquad
\mathcal V_t^{(1)}(K)=K,\qquad \mathcal R_1(K)=0.
$$

Its actual image is $(0,H)$, its exact probability guard is
$0<K+s<H$, and every phase command is lawful. The identities follow
by substitution. The error is again $R_0$. Initialize at $K=k_0$,
or exactly at any desired current height; the exact updates preserve
that encoding at every lawful finite prefix and intermediate straight
leg. The zero-dimensional encoder has a single fiber containing all
heights, contradicting Proposition 7.1's necessary condition. This
exclusion is independent of the tolerance. $\square$

## 8. Every prescribed path and its full all-times guard

**Proposition 8.1 (Integrated native path and chronological composition).**
For a path in Definition 2.4 put

$$
\rho(\tau)=\int_0^\tau a_c(v)\,dv,\qquad
\Delta=\rho(T),\qquad
L=\int_0^T b_c(\tau)\,d\tau,\qquad
C=\int_0^T\rho(\tau)b_c(\tau)\,d\tau.
$$

Its exact guard is equivalently

$$
0<k+\rho(\tau)<H\ (0\le\tau\le T)
\quad\Longleftrightarrow\quad
k+\min\rho>0,\quad k+\max\rho<H.
$$

On this guard its endpoint is

$$
k'=k+\Delta,\qquad
\alpha'=\alpha+L/2,\qquad
\beta'=\beta+\left(\frac12-\frac kr\right)L-\frac Cr.
$$

For two paths in chronological order, their combined triple is

$$
(\Delta_1+\Delta_2,\ L_1+L_2,\ C_1+C_2+\Delta_1L_2).
$$

Writing $m_i=\min\rho_i$, $M_i=\max\rho_i$, the combined extrema
are

$$
m_{12}=\min(m_1,\Delta_1+m_2),\qquad
M_{12}=\max(M_1,\Delta_1+M_2).
$$

**Proof of Proposition 8.1.** The continuous $\rho$ is bounded and
attains its extrema on the compact time interval. The phase velocity
$b_c$ is integrable with finite absolute integral, so $C$ exists.
The actual height is $k+\rho(\tau)$, proving both guard descriptions,
including their strict inequalities. Direct integration of Lemma 1.2
gives the phase increments; in particular

$$
\int_0^T\left(\frac12-\frac{k+\rho(\tau)}r\right)b_c(\tau)\,d\tau
=\left(\frac12-\frac kr\right)L-\frac Cr.
$$

This fixes the negative sign of the mixed term. The formulas become
circle equalities after integration and retain no past real lift as
state. In the second part of a concatenation the displacement relative
to the original starting height is $\Delta_1+\rho_2$. Integration
therefore adds $\Delta_1L_2$ to $C_1+C_2$, and taking extrema gives
the displayed $m_{12},M_{12}$. Substitution in the endpoint formula
agrees with successive application, including the term
$-(\Delta_1/r)L_2$ in the second phase increment. These derivations
allow mixed signs and nonmonotone paths. $\square$

**Theorem 8.2 (Direct affine path realizations by all optimal witnesses).**
For every prescribed path the annular model has the fixed ambient
linear map

$$
\mathcal W_{\rm path}^{(2)}(z)=\exp(\Delta/H)R_{L/2}z.
$$

Its exact guard on $\mathscr S_2$ is

$$
0<H\log\|z\|_2+\rho(\tau)<H\quad(0\le\tau\le T),
$$

or, equivalently,

$$
1<\exp(\rho(\tau)/H)\|z\|_2<\exp(1)
\quad(0\le\tau\le T).
$$

The height witness has the affine map $K\mapsto K+\Delta$ with
guard $0<K+\rho(\tau)<H$ at all times. The constant witness has
the unique literal affine map on the actual source guard. Each witness
is exactly encoded at every intermediate truncation and every prefix
of every finite lawful concatenation, with its previously proved
uniform output error.

**Proof of Theorem 8.2.** On an encoded source point,

$$
\exp(\Delta/H)R_{L/2}\bigl(\exp(k/H)U(\alpha)\bigr)
=\exp((k+\Delta)/H)U(\alpha+L/2).
$$

By Proposition 8.1 this is exactly $E_2$ of the true endpoint.
The mixed term $C$ is present in that true endpoint and disappears
only because this particular encoder forgets $\beta$. The coefficient
matrix depends on the prescribed path and $H$, not on the starting
ray. The recovered height in Proposition 5.2 proves the two equivalent
guard formulas. Endpoint image preservation follows from the exact
identity on this full guard. Substitution proves the height and
constant identities as well; the latter supplies no guard recovery.

For an intermediate time $\tau$, use $\Delta_\tau=\rho(\tau)$,
$L_\tau=\int_0^\tau b_c$ and
$C_\tau=\int_0^\tau\rho b_c$. The same calculation directly gives
the exact encoding of the current ray at that time. This is not a
limit of split commands evaluated through an irregular encoder.

For chronological concatenation the annular matrices multiply to

$$
\exp((\Delta_1+\Delta_2)/H)R_{(L_1+L_2)/2},
$$

because scalar dilations commute with planar rotations. The actual
source has the combined mixed integral from Proposition 8.1; the
encoding consistently discards it. The combined guard is the first
path's guard followed by the second path's guard at the actual new
height $k+\Delta_1$, equivalently the combined extrema in that
proposition. Height translations and constant maps compose consistently
too. Induction gives every finite concatenation and prefix. At each
exactly encoded ray the same readout error formula is applied afresh.
No perturbed initialization, rounding or approximate latent propagation
is covered by this exact-real assertion. $\square$

**Proposition 8.3 (Path lawfulness is additional to its endpoint map).**
All prescribed-path guards are recoverable exactly when height is
constant on encoder fibers, provided straight probability guards are
included. An affine endpoint map alone does not determine these guards.

**Proof of Proposition 8.3.** If height is constant on fibers,
Proposition 7.1 defines $K_E$ and the path guard is precisely
$K_E(z)+\min\rho>0$, $K_E(z)+\max\rho<H$. Conversely the larger
guard contract contains all straight probability guards, so
Proposition 7.1 gives height recovery.

For the endpoint distinction, compare the stationary path with a
probability excursion from relative displacement zero to $a$ and back,
where $0<a<H$, while $\chi$ stays fixed. Both have
$(\Delta,L,C)=(0,0,0)$ and identity endpoint maps in all three
witnesses. The stationary path is lawful at every interior height;
the excursion is lawful only for $0<k<H-a$. Thus the prescribed
path's full guard must accompany the endpoint map. Native rectangles
also need not be ray-trivial: they change $\beta$ by $-st/r$ even
though the annular matrices commute. Equal encoded maps do not equate
native commands or their partial domains. $\square$

## 9. Exact capacities, tolerance endpoints and minimum dimensions

**Theorem 9.1 (Complete arbitrary-readout capacity table).** For every
fixed arbitrary preparation and every $0<Z<1$, put

$$
e_*=\sqrt{2Z(1-Z)},\qquad
R_0=
\begin{cases}
1-Z/2,&0<Z<2/3,\\
e_*,&2/3\le Z<1.
\end{cases}
$$

The literal and guard-recoverable capacities and finite tolerance sets
are exactly the following. Every finite value in the table is attained
by a single model.

| Dimension budget | $e_n^{\rm arb}(Z)$ | $\mathcal A_n^{\rm arb}(Z)$ | $e_{n,g}^{\rm arb}(Z)$ | $\mathcal A_{n,g}^{\rm arb}(Z)$ |
| --- | --- | --- | --- | --- |
| $n=0$ | $R_0$ | $[R_0,\infty)$ | $+\infty$; class empty | $\varnothing$ |
| $n=1$ | $R_0$ | $[R_0,\infty)$ | $R_0$ | $[R_0,\infty)$ |
| $n\ge2$ | $e_*$ | $[e_*,\infty)$ | $e_*$ | $[e_*,\infty)$ |

Every entry is unchanged when all prescribed paths and intermediate
truncations of Definition 2.4 are required. In particular, with that
superscript convention,

$$
e_n^{\mathrm{arb,path}}=e_n^{\rm arb},\qquad
e_{n,g}^{\mathrm{arb,path}}=e_{n,g}^{\rm arb},
$$

and the corresponding finite tolerance sets are equal as well.

**Proof of Theorem 9.1.** Theorem 6.2 gives the lower bound $R_0$
for every model with dimension at most one, including a constant
encoder. Proposition 7.3 supplies matching zero- and one-dimensional
witnesses. Thus the first two literal capacities equal $R_0$ and
are attained. Proposition 7.1 excludes every zero-dimensional guard
model, while the height witness attains $R_0$ with guards in dimension
one. Since the guard class is a subclass of the literal class, its
one-dimensional lower bound is the same.

For every larger finite dimension budget, Theorem 4.1 gives the lower
bound $e_*$. The annular witness in Theorem 5.4 attains it in two
coordinates with exact guards. Padding as in Definition 2.2 makes it
available at every budget $n\ge2$. Lemma 7.2 gives the stated values
and transition. A witness of error at most $\epsilon$ works for every
larger tolerance. The attained lower bounds exclude every smaller
tolerance and include equality, proving exactly the displayed closed
intervals. The empty class has no finite tolerance.

For the path claims, each stronger class is a subclass of its
straight-command class. All preceding lower bounds and the
zero-dimensional guard exclusion therefore persist. Conversely,
Theorem 8.2 puts each matching optimal witness directly in the
corresponding stronger class, with Proposition 8.3 providing the
all-times guards when required. These two directions prove equality
of the capacities and of their attained tolerance sets. No equality
of classes, or guard recovery for an arbitrary literal factor, is
inferred from equality of their numerical capacities. $\square$

**Corollary 9.2 (Sharp minimum dimension at every finite tolerance).**
Let $d^{\rm arb}(\epsilon;Z)$ be the least ambient real dimension
of any literal model with error at most $\epsilon$, with value
$+\infty$ if none exists. Define $d_g^{\rm arb}$ similarly with
guard recovery. For finite $\epsilon\ge0$,

| Tolerance | $d^{\rm arb}(\epsilon;Z)$ | $d_g^{\rm arb}(\epsilon;Z)$ |
| --- | --- | --- |
| $0\le\epsilon<e_*$ | $+\infty$ | $+\infty$ |
| $e_*\le\epsilon<R_0$ | $2$ | $2$ |
| $\epsilon\ge R_0$ | $0$ | $1$ |

The middle interval is empty when $Z\ge2/3$. At the floor itself,

| Parameter range | Literal minimum dimension at $e_*$ | Guard-recoverable minimum at $e_*$ |
| --- | --- | --- |
| $0<Z<2/3$ | $2$ | $2$ |
| $2/3\le Z<1$ | $0$ | $1$ |

The same statements hold with all prescribed paths. In both literal
and guard classes the infimum over all finite dimensions is $e_*$
and is attained for every allowed $Z$.

**Proof of Corollary 9.2.** Below $e_*$, Theorem 4.1 excludes
every finite dimension. Between $e_*$ and $R_0$, Theorem 6.2 excludes
dimensions zero and one, and Theorem 5.4 supplies dimension two.
At or above $R_0$, Proposition 7.3 gives the constant literal model
and the height guard model, while Proposition 7.1 excludes dimension
zero in the guard class. These are actual witnesses at the stated
dimensions; padding does not change the least dimension. Theorem 9.1
and Lemma 7.2 give the floor specialization, path assertions and
all-finite infimum. $\square$

**Proposition 9.3 (The precise distinction from affine-readout
nonattainment).** The floor $e_*$ in Theorem 4.1 is a constraint
imposed by exact finite affine dynamics even with arbitrary readout.
The annular readout attains that floor using a scalar output component
that is not an affine functional of its latent coordinates. Thus the
fixed-affine-readout premise used in [A]'s full-open nonattainment
and fixed-dimension gap proofs is absent here.

**Proof of Proposition 9.3.** Theorem 4.1 used equal encodings and
the resulting equality of two deterministic predictions, without any
linearity of the prediction. This establishes the asserted dynamical
constraint.

For the second assertion undo $D$ on its image and take the first
component of the predicted $\alpha$ pair. On the annulus it is

$$
g(z)=A(H\log\|z\|_2)\frac{z_1}{\|z\|_2}.
$$

If $g$ were a fixed affine scalar function $c+\ell_1z_1+\ell_2z_2$
on this image, evaluating at $z=\exp(k/H)U(\alpha)$ for all
$\alpha$ at a fixed height would force $c=0$, $\ell_2=0$ and
$\ell_1=A(k)\exp(-k/H)$. For example opposite directions remove
$c$, the directions with first coordinate zero remove $\ell_2$,
and $\alpha=0$ gives the last identity. This last positive quantity
cannot be constant over all interior heights: it tends to zero as
$k\downarrow0$ through interior values and is positive at $k=H/2$.
Only the explicit function $A(k)\exp(-k/H)$ is used in that scalar
comparison. Therefore $g$ is not affine on the image.

In [A], a single fixed affine scalar readout evaluated along repeated
probability commands factors the corresponding scalar arrays through
the finite homogeneous latent dimension. That premise supports its
finite-rank nonattainment and uniform fixed-dimension gap arguments.
The displayed $g$ does not satisfy the premise. Below $Z=2/3$ the
annular witness therefore attains a floor which the affine-readout
class cannot attain in any finite dimension. The numerical floor
itself agrees in the two classes. At and above the transition,
constant zero readout already suffices, as in [A, §11.5]. No prior
affine-readout theorem is contradicted or extended to arbitrary
observables by this comparison. $\square$

## 10. Source correspondence, credited results and open boundaries

The following source labels refer to the corresponding repository theory
texts. Their statements are reference-input mathematics; no Lean status
is inferred from their presence. The source equations and lower-bound
premises used in this volume have their explicit proofs above.

- **[F]** *Native FIB continuation: exact affine obstruction and
  compact-band approximation*. Sections 1–3 give the native source,
  arbitrary preparation, original outputs and path law. Section 4
  gives the all-finite obstruction for exact affine readout with
  probability continuation; §7 gives the positive-band approximation
  threshold. In §10, Lemmas 10.3–10.4, Proposition 10.5 and Theorem
  10.6 give the affine-hull, common-circle and rational-erasure
  mechanism. Proposition 10.18 includes the full open interval.
  Corollary 10.16 already excludes exact deterministic full-output
  decoding, with no affine-readout restriction. Proposition 10.11
  already retains $(k,\alpha)$ in three real affine coordinates
  and supplies its prescribed-path action and guards.
- **[A]** *Native FIB on the full open domain: affine approximation
  and finite attainment*, including §11, *Fixed-dimension uniform
  gaps and finite Hankel certificates*. Theorem 2.2 gives the
  all-finite affine-readout tolerance intervals; Theorem 3.3 concerns
  bounded affine observables, and §§4–6 give its residual and
  nonattainment proof. Theorem 11.1 strengthens nonattainment to a
  positive model-uniform gap at every fixed dimension below $Z=2/3$.
  Section 11.5 supplies the exact constant-prediction radius, the
  literal zero-dimensional witness, the guard exclusion in dimension
  zero, and the high-$Z$ height witness. Sections 9 and 11.7 supply
  the prescribed-path comparison. These stronger fixed-dimension
  results, as well as the original nonattainment result, concern
  fixed affine readout.
- **[O]** *AURIC FIB-ATOM: observation graphs, purity certification
  and stable future response — continuation*. Proposition 10.4 and
  Theorems 10.5–10.6 give the calibrated double-wall response and
  exact base-only future quotient with lawfulness, topology, smooth
  section and path action. Mathematical input 10.8 distinguishes
  nonlinear current-state continuation from the shared-affine-
  readout all-future obstruction. Chapter 11 addresses different
  observation menus and pure versus arbitrary-PSD comparison classes.

The native conventions in these texts are attributed there to *AURIC
FIB-ATOM: Probability, Phase Transport and Holonomy*. That is source
context; no unquoted theorem from that parent is needed for the proofs
in this volume.

### 10.1 Parameter and observation correspondence

Our $k$ is the $\kappa$ of [O], and our $H$ is its $L=r/2$.
After removing the fixed preparation rotations, its coherences are

$$
z=C_{01}=\frac{A(k)}2e^{i\alpha},\qquad
w=C_{02}=\frac{B(k)}2e^{i\beta}.
$$

The other bottom edges are the copy and conjugates specified by $D_0$.
Restoring the factor two and the preparation rotations gives exactly
our ten-vector $D(A(k)U(\alpha),B(k)U(\beta))$. In particular the
error is not the unweighted Euclidean norm on $(z,w)$: Lemma 1.5
keeps the original fourfold first-pair weight and reference-pair weight.

The quotient $(k,e^{i\alpha})$ is already the exact future behavior
for the four bottom edges plus refusal/lawfulness in [O, Theorem 10.6].
Its two-real-coordinate annular realization here reads those same
bottom edges exactly while predicting zero for the original reference
edge. The full ten-output task still includes that edge in every error
supremum. Reusing the base quotient is therefore an approximation of
the full task with its exact error proved, not a deletion of the
reference observable from the task.

The three-dimensional intrinsic ray source, its static four-coordinate
affine readout, and its finite exact nonlinear full-current update
model are prior facts in [F] and [O]. None of those coordinate counts
proves the two-coordinate minimum here. The lower argument is the
affine-line finite-cycle proof of §6; the upper argument is the actual
annulus and its fixed readout of §5.

### 10.2 Prior observation and purity results retain their own tasks

The following are credited comparison results of [O], not additional
claims of reconstruction, certification or stability proved here.
They are not premises of Theorems 4.1, 6.2 or 9.1.

| Prior observation result | Menu and comparison class | Relation to this volume |
| --- | --- | --- |
| Pure reconstruction and base quotient, Proposition 10.4 and Theorems 10.5–10.6 | Calibrated full-support pure current rays; full native menu recovers the ray, whereas bottom edges with lawfulness have quotient $(k,e^{i\alpha})$ | The quotient and its guarded path action are reused and credited; our prediction retains its base response and incurs reference-pair error. |
| Native purity threshold, Theorem 11.5 | All PSD trace-one candidates with the same means and native coherences as a calibrated double-wall pure target of height $k_{\rm tar}$ | The compatible heights are $[k_{\rm tar},\max(k_{\rm tar},H-k_{\rm tar})]$; native certification holds for $k_{\rm tar}\ge H/2$. This target-height threshold differs from the parameter threshold $Z=2/3$ here. |
| Native menu plus $12$, Theorem 11.8 | Original five complex edges plus the additional complex coherence $12$, with fixed legal means, compared against arbitrary PSD trace-one matrices | This larger menu certifies a full-support pure target. The extra edge is not supplied to our decoder or included in our original ten-output metric. |
| Native inverse instability, Proposition 11.9 | Whole open calibrated pure source, also any fixed finite stack of globally lawful native commands | This is an inverse-recovery limitation, not a perturbed-latent-state estimate for the annular model. |
| Two-reference stable recovery, Theorem 11.10 | Coherences $02,12$ within the known calibrated pure family, with doubled real outputs | Its trace-distance bound has constant $1/\sqrt{2Z}$. The extra $12$ edge and the pure-family comparison are distinct from our observation and approximation task. |
| Full reference-star certificate, Theorem 11.11 | All four complex reference coherences $C_{i2}$ for $i\ne2$, and known $Z$, against arbitrary PSD trace-one states | Its exact residual purity certificate and trace-distance bound use a different menu and comparison class; no such certificate is inferred from our quotient coordinates. |

Proposition 10.9 of [O] already distinguishes pure reconstruction from
mixed-state tomography. Its Proposition 11.7 applies native commands
componentwise to specified ensembles, with their preparation labels;
it does not define a universal nonlinear dynamics on arbitrary mixed
matrices. Our source and all error suprema contain only the declared
actual pure rays. No mixed-state transport or learning-performance
transfer is assumed or obtained.

### 10.3 What changes with readout, and what remains unresolved

The new classification has two logically separate lower mechanisms.
The prior rational common-turn erasure forces equal encodings with
opposite reference outputs, yielding $e_*$ for every arbitrary fixed
deterministic readout. The affine-line action additionally forces
antipodes of the complete original output to collide, yielding $R_0$
in at most one coordinate. The annular realization attains $e_*$ in
two, matching both bounds and all tolerance endpoints. The high-$Z$
constant/height witnesses and the zero-dimensional guard distinction
are already contained in [A, §11.5]; they are retained in the complete
table rather than presented as separate new discoveries.

Below $Z=2/3$, [A]'s affine-readout capacity has a positive gap above
$e_*$ at every fixed finite dimension, even when all model parameters
vary. Its all-finite infimum still equals $e_*$. Here the arbitrary-
readout capacity already equals and attains $e_*$ at dimension two.
Theorem 3.3 of [A] establishes full $\beta$ independence for bounded
affine observables. It is not a theorem about arbitrary deterministic
decoders. Proposition 4.2 supplies the needed residual by keeping the
prediction fixed on a forced rational orbit. It does not silently
import that stronger independence claim.

The mathematical ingredients are classical affine spanning,
homogenization, determinants on generalized eigenspaces,
characteristic-zero unipotence, divisibility of real command time,
finite-order affine-line dynamics, Euclidean antipode bounds and
exponential polar coordinates. Choice enters only the explicit
pathological example, not either lower bound or any optimal witness.
Their applications needed for the classification are proved above.
This is a repository-derived synthesis; no external literature search,
worldwide originality or independently verified literature-priority
claim is made.

The remaining boundaries are part of the result:

- Full positive support, $0<Z<1$ and $0<k<H$, is essential to this
  source. At a height endpoint one group disappears; at $Z=0$ the
  positive middle reference disappears; at $Z=1$ the open interval
  is empty. Limits of scalar error expressions do not include these
  different ray spaces in the theorem.
- Current rays, arbitrary producing histories, retained real lifts,
  loop-only endpoints and reduced command menus are different
  domains or contracts. The full-domain one-step identities here
  imply every finite lawful iterate. Merely declaring a short
  execution horizon without changing those identities does not
  weaken their algebraic consequences.
- Rational-turn erasure does not classify every individual factor's
  fibers or its behavior on all irrational turns. Proposition 6.3
  explicitly prevents the stronger assertion that every one-real-
  coordinate factor is phase-blind. No general measurable-factor or
  simultaneous separation classification is supplied.
- Requiring physical decoded outputs, injective encodings, or
  approximate instead of exact latent equivariance changes the
  problem. The optimal decoded vectors here are permitted to leave
  the native output image. Literal domain identities, encoded guard
  recovery and all-times prescribed-path requirements remain
  separately defined even when their attainable errors agree.
- Exact real coordinate counts do not provide finite-bit storage,
  efficient implementation, conditioning, stability under noisy
  initialization or rounding, measurement acquisition, training or
  empirical machine-learning performance. Nonaccumulation here is
  only the repeated evaluation of the same readout bound at an
  exactly encoded current state.
- The fixed-positive-dimension affine-readout capacities and their
  optimal rates left unresolved in [A] are not computed by the
  changed-readout table. The original finite-hidden-$N$ alternative
  of a finite attainer versus a strict gap at every finite $N$ also
  remains unresolved. No identification of its objective or
  admissible realizations with $e_n^{\rm arb}(Z)$ is established,
  and no completion of a broader research objective follows.

## 10.99 追加锚
