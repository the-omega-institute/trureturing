# FIB harmonic-edge load: intrinsic tilt rigidity and the unpaid second-order balance

For a fixed finite producer, preservation of every original intrinsic
probability space by the actual loss-cocycle exponential kernels is
equivalent to vanishing of that cocycle on finite legal modifications.
The result assumes the posterior band, square-root erasure summability,
and the stated handwritten cocycle interface below. The existing
all-length response balances supply only the first derivative of this
preservation condition. Its first unpaid equation is a conditional
square-contrast balance. Under those all-length balances it vanishes
on the already controlled pair span and defines a functional on the quotient.
No nonzero quotient, productive direction, or original attainment
alternative is established. These are ordinary handwritten arguments,
without a Lean or kernel-verification claim.

## 1. Original scope and the same actual law

**Convention 1.1 (Canonical objective and producer).** Use the complete
domain of [Universal, §§1 and 4][U], with the following correspondence.
For $n\ge1$,

$$
B_n=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

$B_0$ consists of the empty word. The open-path graph $\Gamma_n$ has
every vertex of $B_n$ and every legal Hamming-one edge; endpoint
insertions use $w_0=w_{n+1}=0$, without joining the endpoints. Retain

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\quad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\quad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\quad
c_\star=\lim_n\kappa_n/n.
\tag{1.1}
$$

For every finite $N\ge1$ the original parameter domain remains

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
\ M_0,M_1\ge0,\ A=M_0+M_1,\ A\mathbf1=\mathbf1,
\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.2}
$$

Here $\lambda$ is a row and $M_0,M_1$ are $N\times N$ exact-real
matrices. Fix $\theta\in\Theta_N$. All objects use precisely
[Universal, Proposition 4.2][U]'s stationary joint law and its visible
marginal $P=P_\theta$:

$$
\begin{aligned}
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
&=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\\
P([w]_a)&=\lambda M_w\mathbf1.
\end{aligned}
\tag{1.3}
$$

$[w]_a$ specifies the emitted bits at $a,\ldots,a+|w|-1$;
$M_w$ is their ordered product and $M_\varnothing=I$.
Structural zeros, zero stationary masses, reducibility and periodicity
are allowed. No trimming, hidden minimality or change of visible law is
made. The scalar last condition in (1.2) is not replaced by entrywise
$M_1^2=0$. Every seam uses the actual product $\lambda M_uM_v\mathbf1$;
all-zero words, legal endpoint ones and zero-mass edges remain present.

**Convention 1.2 (Original posteriors).** Let $(Tx)_i=x_{i+1}$,
$\mathcal E_i=\sigma(X_j:j\ne i)$ and
$F_i=\{X_{i-1}=X_{i+1}=0\}$. Choose an exterior-measurable Borel
version $q_0=\mathbb E_P[X_0\mid\mathcal E_0]$ in $[0,1]$, and put
$q_i=q_0\circ T^i$, $\ell_i(x)=(x_i-q_i(x))^2$.
For $r\ge0$ use the actual finite predictor

$$
q_{r,i}=\mathbb E_P[X_i\mid
\sigma(X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r})],\qquad
D_r(P)=\mathbb E_P(X_0-q_{r,0})^2.
$$

At radius zero this is the prior mean, not the full posterior $q_i$.
A retained neighbor one forces the center posterior to zero; an omitted
neighbor supplies no such information. Null finite fibers contribute
zero and require no division. [Universal, §§1–3][U] supplies
$D_r(P)\downarrow d(P)=\mathbb E_P\ell_0=\lim_n\Phi_n(P_n)/n\le c_\star$
and $nc_\star\le\kappa_n\le(n+1)c_\star$.
At modified configurations and throughout every tilt, $q_i$ and
$\ell_i$ remain these fixed original-$P$ functions.

**Convention 1.3 (Reused intrinsic spaces).** For an interval $C=[a,b]$
of length $L$, let $\mathcal H_C=\sigma(X_j:j\notin C)$,
$Y=X_{C^c}$, $\mu_C=P\circ Y^{-1}$, and

$$
\begin{aligned}
\mathcal K_C(P)&=\{f\in\mathbb R^{B_L}:
\mathbb E_P[f(X_C)\mid\mathcal H_C]=0\},\\
V_C&=\mathcal K_C(P)^\perp,\qquad r_C=\dim V_C.
\end{aligned}
\tag{1.4}
$$

The orthogonal complement uses the ordinary coordinate pairing over
all of $B_L$. [Intrinsic, Theorem 2.2 and Corollary 2.3][I] gives,
after translating $C$, $\mathcal K_C(P)=\ker E_{\theta,L}$ and
$V_C=\operatorname{range}(E_{\theta,L}^{\mathsf T})$, where

$$
E_{\theta,L}((u,v),w)=\lambda M_uM_wM_v\mathbf1,
\qquad u,v\in\{0,1\}^{N-1},\quad w\in B_L.
\tag{1.5}
$$

Illegal collar concatenations give zero rows; $N=1$ has an empty
collar. The same finite-realization factorization gives $r_C\le N^2$:
each row is obtained by applying a linear functional on $N\times N$
matrices to the family $(M_w)_w$. This is the inherited rank bound,
not a new collar or minimality theorem. Choose actual conditional masses
$p_C(w;y)=P(X_C=w\mid Y=y)$ at $C=[1,L]$ for each $L$, and translate
these versions to other intervals; stationarity justifies the choices.
Finite bases in (1.4) give
$p_C(\cdot;y)\in V_C$ almost everywhere. The spaces depend on $P$,
even when two presentations have different dimensions or collars.
Their finite dimension implies no visible Markov order or posterior
locality.

## 2. Explicit hypotheses and the cocycle supplier

**Hypothesis 2.1 (Band and square-root tail).** The conditional results
use the following additional assumptions on this same $P$:

$$
\begin{aligned}
\mathsf B(P):&\quad q_i=0\text{ on }F_i^c,\quad
\tfrac14\le q_i\le\tfrac12\text{ on }F_i,
\quad P\text{-almost surely for every }i,\\
p^L_j&=\mathbb E_P[X_0\mid X_{-j},\ldots,X_{-1},X_1,X_2,\ldots],\\
p^R_j&=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_j],\\
e_L(j)&=\mathbb E_P(q_0-p^L_j)^2,\qquad
e_R(j)=\mathbb E_P(q_0-p^R_j)^2,\\
A_P&=\sum_{j\ge0}(\sqrt{e_L(j)}+\sqrt{e_R(j)})<\infty.
\end{aligned}
\tag{2.1}
$$

The opposite half-line remains entire, including at $j=0$.
Neither $e_L(0)$ nor $e_R(0)$ is discarded on account of a forcing
neighbor absent from its field. The band is necessary for attainment
by [Universal, Theorem 3.1][U]; $A_P<\infty$ is an extra premise,
not a general finite-hidden conclusion. It implies
$\sum_j(e_L(j)+e_R(j))<\infty$, but no bound for a parameter family.

**Standing interface 2.2 (Conditional use of the actual cocycle).**
We use [Cocycle, Theorem 3.1][L] at its stated ordinary handwritten
status, with exactly (1.2), (1.3) and (2.1) as its input correspondence.
The results here are conditional on that construction and the properties
listed next; this volume does not independently establish the supplier.

Write $wy$ for filling $C$ with $w$, and call $w$ compatible with $y$
when $wy\in\mathsf X$. Besides internal legality, this means exactly
$y_{a-1}w_1=w_Ly_{b+1}=0$. The zero word is always compatible.
The supplied support statement, on a conull exterior set, is

$$
p_C(0^L;y)\ge2^{-L},\qquad
3^{-k(w)}p_C(0^L;y)\le p_C(w;y)\le p_C(0^L;y)
\quad(w\text{ compatible}),\quad k(w)=\sum_jw_j.
\tag{2.2}
$$

Incompatible completions have mass zero; every compatible completion
therefore has mass at least $2^{-L}3^{-k(w)}$.
The total map $R_{C,w}$ replaces $C$ by $w$ on compatible exteriors
and is the identity otherwise. Each such map preserves $P$-null sets.
For $Z_Cx=0^Lx_{C^c}$ the supplier gives

$$
\mathbb E_P\sum_{i\in\mathbb Z}
|\ell_i(X)-\ell_i(Z_CX)|
\le L+2(1+2^{L/2})A_P.
\tag{2.3}
$$

There is a Borel, shift-invariant, $P$-conull set $\Omega$, saturated
under all finite legal changes, on whose finite-modification relation

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z))
\tag{2.4}
$$

is absolutely convergent, measurable, antisymmetric and additive:
$\Delta_P(x,z)=\Delta_P(x,u)+\Delta_P(u,z)$.
It satisfies $\Delta_P(Tx,Tz)=\Delta_P(x,z)$.
For any two choices of original posterior versions these constructions
agree on a common saturated conull set. This is not a single set for
every conceivable version. No separate sum $\sum_i\ell_i$ is defined.
By (2.2) and finite disintegration, almost every exterior has every
compatible completion in $\Omega$, not just a selected completion.

The same nonsingularity permits simultaneous versions throughout this
volume. Intersect the countably many required Borel conull events with
their preimages under the countable monoid generated by shifts and all
$R_{C,w}$. The result is still conull, shift invariant and saturated.
For original conditional probabilities, include the countably many
nested-interval chain-rule identities; use finite bases for intrinsic
spaces. Positivity in (2.2) then transfers each identity to every legal
completion of almost every exterior. Null exterior records may be
assigned arbitrary versions and carry no asserted pointwise identity.

**Reused balance 2.3 (First order, with its own premise).** Write
$\mathsf Z(P)$ for the assertion that every intrinsic-null direction on
every finite interval has absolutely convergent response
$S_P(f_C)=\sum_i\mathbb E_P[f(X_C)\ell_i]=0$.
Under (2.1), [Cocycle, Theorem 4.2][L] identifies this with

$$
\sum_{w:\,wy\in\mathsf X} p_C(w;y)f(w)\Delta_P(wy,0^Ly)=0
\quad(f\in\mathcal K_C(P)),\quad\mu_C\text{-almost everywhere},
\tag{2.5}
$$

simultaneously for all intervals and directions. Its reference-invariant
contrast is integrable by (2.3). We reuse this localization; it is not
proved again or assumed for arbitrary $P$ satisfying (2.1).
The inherited attained-law response theorem, as supplied in
[Cocycle, Convention 1.3][L], gives $d(P)=c_\star\Rightarrow\mathsf Z(P)$.
It does not give the higher-order identities below.

## 3. Conditional exponential kernels and exact preservation

**Definition 3.1 (Fixed-loss tilt).** On the good exterior fibers above put

$$
\begin{aligned}
d_C(w;y)&=\Delta_P(wy,0^Ly),\\
Z_C(t;y)&=\sum_w p_C(w;y)e^{t d_C(w;y)},\\
\pi_C^t(w;y)&=\frac{p_C(w;y)e^{t d_C(w;y)}}{Z_C(t;y)},\qquad t\in\mathbb R.
\end{aligned}
\tag{3.1}
$$

In these finite sums take $d_C(w;y)=0$ on incompatible coordinates,
whose probabilities are zero. Compatible contrasts are finite by (2.4),
so $0<Z_C(t;y)<\infty$ for every real $t$ at each good fiber.
For fixed $t$ these are measurable conditional kernels, with positive
mass on exactly the compatible words. No expectation of an exponential
over exteriors is needed. On a null exterior set choose any legal
probability vector, without imposing compatibility statements there.

Cocycle additivity makes (3.1) independent of the reference completion:
using a compatible $z$ instead of $0^L$ changes every compatible score
by the common constant $-\Delta_P(zy,0^Ly)$. That factor cancels in the
normalization. This invariance of the kernel does not require $f$.

**Finite-sum compatibility.** For intervals $C\subset D$, fix a good
exterior $y$ of $D$ and a configuration $v$ on $D\setminus C$ having
a legal completion. In formulas $wv$ denotes the combined assignment
on $D$, and $vy$ the exterior of $C$. The sums in this compatibility
calculation run over compatible completions; other coordinates are zero.
Define

$$
r(v;y)=\sum_s p_D(sv;y)>0.
$$

The simultaneous original conditional versions give
$p_D(wv;y)=r(v;y)p_C(w;vy)$. Moreover

$$
d_D(wv;y)=d_C(w;vy)+b(v;y),\qquad
b(v;y)=\Delta_P(0_Cvy,0_Dy).
\tag{3.2}
$$

The zero fillings in (3.2) are legal. The second term is independent of
$w$. Thus conditioning the tilted $D$-kernel on $v$ gives exactly

$$
\frac{\pi_D^t(wv;y)}{\sum_s\pi_D^t(sv;y)}
=\frac{r(v;y)p_C(w;vy)e^{t(d_C(w;vy)+b(v;y))}}
{r(v;y)e^{t b(v;y)}\sum_s p_C(s;vy)e^{t d_C(s;vy)}}
=\pi_C^t(w;vy).
\tag{3.3}
$$

This proves the nested resampling identity by finite summation over $v$.
Incompatible $v$ has zero mass and is never divided by. Stationarity of
the chosen original versions and shift invariance of $\Delta_P$ give
shift covariance. The same good sets work for all real $t$, since (3.3)
is an algebraic identity of finite sums once its ingredients are fixed.

These are full-exterior kernels on the stated conull domain. Their
compatibility is not a construction of a global stationary law $P_t$,
a finite hidden realization, or an implementable intervention.
No continuity in exterior records, finite-boundary dependence, Gibbs
interaction, or identification of $\Delta_P$ with the original
conditional log-density ratio is assumed or derived.

**Definition 3.2 (Preservation of the original intrinsic spaces).** Set

$$
\mathsf{RP}(P):\quad
\forall C\ \text{for }\mu_C\text{-almost every }y\quad
\exists\varepsilon(C,y)>0\quad
\forall t\in(-\varepsilon(C,y),\varepsilon(C,y)):\quad
\pi_C^t(\cdot;y)\in V_C.
\tag{3.4}
$$

The space is the original $V_C$ from (1.4), fixed as $t$ varies.
No uniform $\varepsilon$ is required. The entire interval of $t$ is
required at almost every exterior of every finite block; a tangent
condition or a condition at one block is not (3.4).
Finite continuity makes (3.4) measurable: one can test rational $t$ in
some rational-radius interval, using a finite basis of $\mathcal K_C$.

## 4. Closure rigidity on the actual finite-modification relation

**Theorem 4.1 (Intrinsic tilt rigidity).** Fix any finite $N\ge1$ and
$\theta$ in the entire domain (1.2). Assume (2.1) and the supplied
cocycle interface 2.2 for its same actual $P$. Then $\mathsf{RP}(P)$
holds if and only if there is a Borel, shift-invariant, saturated
$P$-conull set $\Omega_0\subseteq\Omega$ such that

$$
\Delta_P(x,z)=0
\quad\text{whenever }x,z\in\Omega_0
\text{ agree outside a finite set}.
\tag{4.1}
$$

In this case $\pi_C^t(\cdot;y)=p_C(\cdot;y)$ for every real $t$ on
almost every exterior of each interval. The theorem requires neither
$\mathsf Z(P)$ nor attainment; it does not assert that either supplies
$\mathsf{RP}(P)$.

**Proof.** Suppose first that (3.4) holds. Use the saturation procedure
in §2 to obtain a common good $\Omega_1\subseteq\Omega$ on which
all intervalwise preservation conclusions hold after every legal
replacement. The measurability observation after (3.4) justifies this
use of conull events despite the real $t$ parameter.

Fix $C,y$. Let $a_1,\ldots,a_m$ be the distinct values of $d_C(w;y)$
among compatible words, and define vectors

$$
v_j(w)=p_C(w;y)\mathbf1_{\{d_C(w;y)=a_j\}}.
$$

They have disjoint, nonempty positive supports, so are linearly
independent. The unnormalized curve is

$$
u(t)=Z_C(t;y)\pi_C^t(\cdot;y)
=\sum_{j=1}^m e^{ta_j}v_j.
\tag{4.2}
$$

Under (3.4), $u(t)$ lies in the closed finite-dimensional subspace
$V_C$ near zero. Its derivatives there also lie in $V_C$; in particular
$u^{(k)}(0)=\sum_j a_j^kv_j\in V_C$ for $0\le k<m$.
The Vandermonde matrix $(a_j^k)_{0\le k<m,1\le j\le m}$ is invertible
because the $a_j$ are distinct. Consequently every $v_j\in V_C$, and

$$
m\le r_C\le N^2.
\tag{4.3}
$$

The classical exponential-curve argument has supplied a cardinality
bound. It supplies no bound on the magnitude of a score value.

For $x\in\Omega_1$ and $C_n=[-n,n]$, $n\ge1$, set

$$
\mathcal A_n(x)=\{\Delta_P(z,x):z\in\mathsf X, z_{C_n^c}=x_{C_n^c}\}.
\tag{4.4}
$$

Every such completion belongs to $\Omega_1$ by saturation and has
positive conditional mass on this good exterior by (2.2).
Additivity expresses its value as
$d_{C_n}(z_{C_n};x_{C_n^c})-d_{C_n}(x_{C_n};x_{C_n^c})$.
Thus $0\in\mathcal A_n(x)$, $|\mathcal A_n(x)|\le N^2$, and
$\mathcal A_n(x)\subseteq\mathcal A_{n+1}(x)$.
Their union has at most $N^2$ elements: any larger finite selection
would already occur in one $\mathcal A_n(x)$.
Every finite modification is contained in some $C_n$, so the cocycle
has finitely many values on the entire modification class of $x$.

Write $[x]_{\rm fin}$ for that class. The elementary finite-range
potential construction now gives

$$
F(x)=\max_{z\in[x]_{\rm fin}}\Delta_P(x,z),\qquad x\in\Omega_1.
\tag{4.5}
$$

It is finite and nonnegative, since $z=x$ is allowed. Finite legal
modifications are enumerated by intervals and their finitely many
replacement words. Hence (4.5) is a supremum of countably many
measurable functions $\Delta_P(x,R_{C,w}x)$, and is measurable.
For $x,z$ in one class, additivity and equality of their classes give

$$
F(x)=\Delta_P(x,z)+F(z),\qquad
\Delta_P(x,z)=F(x)-F(z).
\tag{4.6}
$$

The shift maps $[x]_{\rm fin}$ bijectively to $[Tx]_{\rm fin}$;
shift invariance of $\Delta_P$ therefore gives $F(Tx)=F(x)$.
No integrability of $F$ is used.

Now use exactly [Universal, Theorem 5.1][U]'s actual component theorem
for (1.3). After merging identical visible laws it gives

$$
P=\sum_{j=1}^J\omega_jR_j,\qquad \omega_j>0,\quad
\sum_j\omega_j=1,
\tag{4.7}
$$

with finitely many distinct stationary ergodic visible laws of the
same joint process. Its labels are determined by all past finite-word
frequencies. More explicitly, on a conull set these limits satisfy

$$
\nu_w(x)=\lim_{n\to\infty}\frac1n
\sum_{k=|w|}^{n}\mathbf1_{[w]_0}(T^{-k}x)
=R_j([w]_0)\quad\text{on component }j.
\tag{4.8}
$$

Distinct laws differ on some finite cylinder, so this collection labels
them. A finite coordinate modification changes only finitely many
summands for each fixed $w$, and therefore preserves every limit in
(4.8), hence the label. This uses actual visible labels, not an
unobserved class assignment from a different representation.
Periodic hidden classes are included in the supplier's ergodicity
statement under the one-step shift; mixing is not required.

Because $F$ is finite, measurable and shift invariant, ergodicity makes
it a finite constant $c_j$ almost surely under $R_j$.
For example apply ergodicity to the bounded invariant function
$F/(1+F)$, which takes values strictly below one.
Positive weights in (4.7) make these constancy statements valid on
a $P$-conull set. Intersect that set, the frequency-label set, and
their preimages under all legal replacements and shifts. Nonsingularity
from interface 2.2 gives a saturated shift-invariant conull
$\Omega_0\subseteq\Omega_1$.
If $x,z\in\Omega_0$ differ finitely, their common label $j$ yields
$F(x)=c_j=F(z)$. Equation (4.6) proves (4.1).

Conversely assume (4.1). Finite disintegration and the strictly positive
compatible masses (2.2) imply that almost every exterior has all its
compatible completions, including $0^L$, in $\Omega_0$.
Every compatible $d_C(w;y)$ is then zero. Thus (3.1) gives
$Z_C(t;y)=1$ and $\pi_C^t(\cdot;y)=p_C(\cdot;y)\in V_C$ for all real
$t$. Incompatible coordinates remain zero; null exterior records
are irrelevant. The kernels retain (3.3), so the converse introduces
no new compatibility or global-law premise. $\square$

The conclusion is a statement on a saturated conull relation, not on
every topological configuration or prescribed null exterior.
Version independence follows from interface 2.2; presentation
independence uses the original-law definition of $V_C$.
Theorem 4.1 does not prove that a finite producer cannot satisfy (4.1).

## 5. The first unpaid identity and the failed iteration

At a fixed good $C,y$, abbreviate $p_w=p_C(w;y)$, $d_w=d_C(w;y)$ and

$$
m=\sum_wp_wd_w,\qquad \sigma^2=\sum_wp_w(d_w-m)^2.
$$

Differentiation of the finite normalized sum (3.1) gives

$$
\left.\frac{d\pi_C^t(w;y)}{dt}\right|_{t=0}=p_w(d_w-m),\qquad
\left.\frac{d^2\pi_C^t(w;y)}{dt^2}\right|_{t=0}
=p_w\bigl((d_w-m)^2-\sigma^2\bigr).
\tag{5.1}
$$

Indeed $Z(0)=1$, $Z'(0)=m$, $Z''(0)=\sum_wp_wd_w^2$;
the quotient rule yields (5.1). These are finite-fiber derivatives,
not derivatives of measures or of an infinite total loss.
Because $p\in V_C$, the supplied balance (2.5) is exactly
$(\pi_C^t)'|_0\in V_C$. Assuming that balance, pairing the second
derivative with any $f\in\mathcal K_C(P)$ cancels both the constant
and linear terms and leaves

$$
f\mathbin{\cdot}(\pi_C^t)''|_0
=R_{C,f}(y),\qquad
R_{C,f}(y):=\sum_{w:\,wy\in\mathsf X}
p_C(w;y)f(w)\Delta_P(wy,0^Ly)^2.
\tag{5.2}
$$

This is the exact first unpaid preservation equation: $R_{C,f}=0$ for
every intrinsic $f$, almost everywhere, is required at order two.
It is not supplied by (2.5). Under (2.5), changing the reference by a
constant $b$ changes (5.2) by
$-2b\sum_wp_wf(w)d_w+b^2\sum_wp_wf(w)=0$.
Thus this unpaid equation is also reference independent under the
already stated first-order premise.

The precise all-order condition at the fiber is

$$
\sum_wp_wf(w)d_w^k=0
\quad\text{for every }f\in\mathcal K_C(P),\quad k=0,1,2,\ldots.
\tag{5.3}
$$

For $k=0$ the factor is the constant polynomial one.
If (3.4) holds there, pair $f$ with the unnormalized exponential curve
and differentiate to obtain (5.3). Conversely (5.3), together with
the convergent exponential series in this finite set of coordinates,
makes $\sum_wp_wf(w)e^{td_w}=0$ for every real $t$ and every $f$.
Division by $Z_C(t;y)>0$ yields membership in $V_C$ for every real $t$.
Equivalently, if there are $s$ distinct compatible scores, grouping
them and applying Vandermonde uses the moments $0\le k<s$.
Finite bases and countably many intervals and orders permit simultaneous
conull sets. This finite-fiber equivalence does not infer those moments
from finite hidden rank.

The tempting iteration would fix $y$ and replace $f$ by
$g_y(w)=f(w)d_C(w;y)$. Equation (2.5) says only
$\sum_wp_C(w;y)g_y(w)=0$ at that matching exterior.
To apply (2.5) again one needs the fixed vector $g_y$ to belong to
the original $\mathcal K_C(P)$, which requires, after translation,

$$
\lambda M_u\left(\sum_wf(w)d_C(w;y)M_w\right)M_v\mathbf1=0
\quad\text{for every finite binary context }u,v.
\tag{5.4}
$$

By (1.5) it suffices to check its original collar, but those are still
cross-context equations. A single matching conditional integral is
not (5.4); the coefficients also depend on the chosen exterior.
The localized theorem allows a fixed intrinsic $f$ times an exterior
function, and does not remove this missing membership requirement.

Each $R_{C,f}(y)$ is a finite measurable number on a good fiber.
The first-order $L^1$ estimate (2.3), by itself, is not a bound for
the square. The present argument uses no exterior integral estimate
for $R_{C,f}$ and exchanges no second derivative with an exterior
expectation. It makes no claim that square integrability is impossible
to derive from the supplier's additional bounds.
Even a nonzero $R_{C,f}$ would demonstrate departure of this
tilt from $V_C$, not a nonzero original response or a finite strict
certificate. Paying order two alone would still leave higher orders.

**Diagnostic 5.1 (Abstract linear obstruction only).** On three abstract
coordinates take

$$
p=(1,1,1)/3,\quad d=(0,1,2),\quad
V=\operatorname{span}\{(1,1,1),(0,1,2)\},\quad f=(1,-2,1).
$$

Then $p$ and $p\mathbin{\odot}d$ belong to $V$ and $f\perp V$, since
$1-2+1=0$ and $0-2+2=0$. But
$\sum_jp_jf_jd_j^2=(0-2+4)/3=2/3$.
In fact the normalized exponential curve has pairing

$$
f\mathbin{\cdot}\frac{(1,e^t,e^{2t})}{1+e^t+e^{2t}}
=\frac{(e^t-1)^2}{1+e^t+e^{2t}}>0\quad(t\ne0).
\tag{5.5}
$$

This refutes only a general linear implication from first-order tangency
to preservation. These coordinates are not legal words of a constructed
producer; $d$ is not an actual Brier-loss cocycle. The diagnostic is
not a counterexample in the original necessary-attainer domain and
does not refute a possible bridge using all-length actual-law structure.

## 6. The pair span and the remaining quotient

Assume (2.1), interface 2.2 and $\mathsf Z(P)$ in this section.
Define $\mathcal K_C^{\rm pair}(P)$ to be the linear span of all
positive two-word intrinsic directions
$f=\alpha\mathbf1_a-\beta\mathbf1_b$ with $a\ne b$,
$\alpha,\beta>0$ and $P(X_C=a),P(X_C=b)>0$.
No pair is presumed to exist. Actual nullity gives
$\alpha p_C(a;y)=\beta p_C(b;y)$ almost everywhere.

Apply [Two-word, Theorem 2.1][W] directly: on the pair's common
conditional exterior law, the original posterior restrictions agree
at every exterior site, including both seams.
[Cocycle, Theorem 5.1][L], using $\mathsf Z(P)$, supplies equality
of the two finite interior loss totals. Hence, wherever the common
conditional mass is positive, their entire loss difference is zero:
$\Delta_P(ay,by)=0$, and so $d_C(a;y)=d_C(b;y)$.
The pair result and its interior balance are reused, not new cancellation
theorems here. Their original derivation needs no independent tail
premise; (2.1) is used here to put them in the common cocycle notation.

For every integer $k\ge0$ this immediately gives

$$
\sum_wp_C(w;y)f(w)d_C(w;y)^k
=\alpha p_C(a;y)d_C(a;y)^k
-\beta p_C(b;y)d_C(b;y)^k=0.
\tag{6.1}
$$

When both conditional masses are zero, the same equality holds without
evaluating a conditional pair law. Thus (6.1) holds $\mu_C$-almost
everywhere. Choose a finite basis of the pair span from its generating
pairs and intersect its conull sets. Linearity then proves (6.1)
simultaneously for every vector in that span and every $k$.

In particular (5.2) annihilates $\mathcal K_C^{\rm pair}(P)$ and defines
the pointwise linear functional

$$
\overline R_{C,y}:\mathcal K_C(P)/\mathcal K_C^{\rm pair}(P)\longrightarrow
\mathbb R,\qquad [f]\longmapsto R_{C,f}(y),
\tag{6.2}
$$

on a common good exterior set. No integrability norm is assigned to
this quotient functional. All moments are already paid on the pair
span. Neither a nonzero quotient nor a nonzero $\overline R_{C,y}$
follows from dimension counting. If the two spaces happen to coincide
at every interval, (6.1) and (5.3) do imply $\mathsf{RP}(P)$ and hence
(4.1), but no such spanning property is asserted for a remaining law.
If a positive-coefficient pair uses a zero-mass word, nullity forces
both weighted masses to vanish; it gives no positive pair or witness.

## 7. Original obligations, boundaries and mathematical credit

The original alternatives retain the entire domain (1.2): with
$C_N=\sup_{\theta\in\Theta_N}d(P_\theta)$ and
$U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta)$, decide whether some
finite producer attains $c_\star$, or whether $C_N<c_\star$ for every
finite $N$. [Universal, Theorem 6.2][U] owns the equivalence of the
latter with

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\kappa_m/(m+1).
\tag{7.1}
$$

A hypothetical same-law attainer also obeys the supplied full support
bounds $P([0^m]_a)\ge2^{-m}$ and
$P([w]_a)\ge2^{-(n+2)}3^{-k(w)}$, the bulk bounds
$nc_\star\le\Phi_n(P_n)\le\kappa_n\le(n+1)c_\star$, and the
attained-law projection budget $D_r(P)-c_\star\le c_\star/(r+1)$.
Its actual positive-weight components attain by [Universal, Theorem 5.1][U].
These conditions and $\mathsf Z(P)$ keep their supplier ownership.
The smaller premise list used in Theorem 4.1 is not a definition of
the full necessary-attainer domain or a sufficient test for attainment.
In particular the all-$n$ bulk lower bound itself implies attainment
after taking the limit; a low-risk example cannot satisfy that bound.

**Open Problem 7.1 (Unpaid actual-law bridge).** Under hypothetical
same-law attainment and the additional $A_P<\infty$ hypothesis, do
the supplied all-length balances imply $R_{C,f}=0$ for every interval
and every intrinsic direction, almost everywhere? The unpaid part
is precisely (6.2). The question is unproved and unrefuted here.
An affirmative answer pays only the first missing order. Applying
Theorem 4.1 still requires all orders, or an equivalent proof of RP.
Even RP would need a separate incompatibility argument before it could
exclude a finite attainer. Failure of a continuation argument does
not decide either alternative in (7.1).

No new $S_P(f_C)\ne0$ is supplied to the existing response or finite
dual-residual certificate. A second-order tilt defect is not such an
input. Strict finite certificates can also contradict an attainer's
projection budget, so their existence is not identified with a
nonzero full response. There is no universal productivity, exclusion
of a specific remaining producer, efficient radius, uniform family
rate or fixed-$N$ margin in this volume.

The $N=1$ original domain is retained: scalar legality forces $M_1=0$
and gives the all-zero law, whose free posterior fails (2.1).
Thus the conditional theorem does not remove that law from $\Theta_1$.
At any $N$, positivity of compatible visible completions under the
band does not force positive hidden entries. Forced sites and both
seams remain in (2.4); null exterior records remain outside the
pointwise assertions. No visible locality, conditional log-density
identity, global tilted law or Gibbs conclusion follows from the
finite collar or from finite-sum compatibility.

**Attribution 7.2 (Reuse and the compound increment).** The
`repo-derived` increment is Theorem 4.1's passage from preservation in
the original spaces through finite classwise cocycle range to zero,
and the exact placement of the unpaid square balance on (6.2).
The calculus, Vandermonde independence and finite-range potential
construction are classical support inside this argument. First-order
localization, pair cancellation, finite rank and actual component
reduction are reused. No worldwide priority or exhaustive literature
absence is claimed.

| Source | Exact contribution and limit |
| --- | --- |
| [Universal][U], Definitions 1.1–1.2 and 4.1, Proposition 4.2, Theorems 3.1, 5.1 and 6.2 | Original objective and entire producer domain, same actual $J_\theta/P_\theta$, necessary band/support, actual finite visible components and original separation equivalence. |
| [Intrinsic][I], Theorem 2.2, Corollary 2.3 and §§3–4 | Exact collar, intrinsic annihilator and finite-realization framework; the existing dual residual and tail-qualified response norm remain separate consumers. |
| [Cocycle][L], Theorems 3.1, 4.2 and 5.1 | Stated handwritten supplier for nonsingular legal replacements, saturated actual cocycle and its $L^1$ estimate, all-length conditional balance and the pair's pointwise interior balance. Our conclusions remain conditional on these inputs; no stronger proof status is attributed. |
| [Two-word][W], Theorem 2.1 | Common actual exterior law and equality of exterior posterior restrictions for each positive intrinsic pair, including seams. No universal pair existence. |
| [Balle–Panangaden–Precup][BPP], arXiv:1501.06841v3, §§2.2 and 3.1 | `literature-attested`: weighted finite realizations, Hankel rank and forward/backward factorization. Correspondence is $\Sigma=\{0,1\}$, $\alpha_0^{\mathsf T}=\lambda$, $A_x=M_x$, $\alpha_\infty=\mathbf1$. No minimality, SVD or approximation result is imported; the stationary cylinder series has total mass one at every length and is not an $\ell^1$ distribution over all finite words. |
| [Dawid–Lauritzen–Parry][DLP], arXiv:1104.2224v2, §4.2, Example 4.4 and (14) | `literature-attested`: the binary conditional Brier summand is exactly $(x_i-q_i)^2$. The everywhere-positive full-product strict-propriety argument is not transferred to hard no11 or used to prove preservation under score powers. |
| [Chandgotia–Meyerovitch][CM], arXiv:1305.0808v3, §2.2 and the main §3 before §3.1 | `literature-attested`: finite-modification equivalence, additive cocycles and reference-independent exponential normalization. Their Markov specification correspondence additionally requires finite-boundary dependence and uses conditional log ratios. Here (3.3) is proved directly for full exteriors; their global Markov/Gibbs existence conclusions are not imported. |

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[I]: FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md
[L]: FIB_LEGAL_EDGE_LOAD_EXTERIOR_LOCALIZATION_AND_ACTUAL_LOSS_COCYCLE_BALANCE.md
[W]: FIB_LEGAL_EDGE_LOAD_TWO_WORD_EXTERIOR_CANCELLATION_AND_VANISHING_CERTIFICATE.md
[BPP]: https://arxiv.org/html/1501.06841v3 "Borja Balle, Prakash Panangaden and Doina Precup, A Canonical Form for Weighted Automata and Applications to Approximate Minimization"
[DLP]: https://arxiv.org/html/1104.2224v2 "A. Philip Dawid, Steffen Lauritzen and Matthew Parry, Proper Local Scoring Rules on Discrete Sample Spaces"
[CM]: https://arxiv.org/html/1305.0808v3 "Nishant Chandgotia and Tom Meyerovitch, Markov Random Fields, Markov Cocycles and The 3-colored Chessboard"

## 追加锚（本行以下为增补区）

## 8. Guarded insertion, finite-record obstruction and label recovery

**Definition 8.1 (Same mixture and common domain).** Reuse precisely
[Universal, Proposition 7.2][U]'s four-state mixture, writing
$P=(R^{1/3}+R^{1/4})/2$. Let $H\in\{1/3,1/4\}$ denote its persistent
component label, not its time-indexed hidden state. Under $R^a$, either
one-sided empirical frequency of ones converges to $a/(1+a)$; these
distinct limits identify $H=a$ and survive every finite coordinate
change. On the no11 space $\mathsf X$, write
$F_i=\{x:x_{i-1}=x_{i+1}=0\}$. The free-site full-exterior predictor
values are

$$
r_{1/3}=\frac37,\qquad r_{1/4}=\frac4{13},\qquad
q_i(x)=r_{H(x)}\mathbf1_{F_i}(x).
\tag{8.1}
$$

These $r_a$ predict the visible bit given its entire exterior. They are
not finite-record posterior probabilities of $H$.

Use Standing interface 2.2 at its stated ordinary mathematical status.
Choose one Borel, shift-invariant, saturated $P$-conull domain $\Omega$
on which the two frequency labels, all identities (8.1), and that
interface agree, by its countable intersection and nonsingularity
procedure. It is conull under both components. The band in (2.1) holds.
For $j\ge1$, either erasure field in (2.1) retains an entire half-line
identifying $H$ and both neighbors of the center, so $p_j^L=p_j^R=q_0$
almost surely. Thus $e_L(j)=e_R(j)=0$ for $j\ge1$, while the two
$j=0$ terms are bounded, proving $A_P<\infty$. This verifies the
additional hypotheses for consuming Theorem 4.1 with this finite producer
and the supplied interface.

Define the cylinder and total center insertion by

$$
E=\{x:x_{-2}=x_{-1}=x_0=x_1=x_2=0\},\qquad
(Rx)_i=\begin{cases}
1,&i=0\text{ and }x_{-1}=x_1=0,\\
x_i,&\text{otherwise}.
\end{cases}
\tag{8.2}
$$

Thus $R=R_{\{0\},1}$ is the identity on incompatible inputs and on
inputs whose center is already one. All pathwise statements use
$x,Rx\in\Omega$; in particular $H(Rx)=H(x)$. For
$\ell_i(x)=(x_i-q_i(x))^2$, the sign convention is
$\Delta_P(x,z)=\sum_i(\ell_i(x)-\ell_i(z))$.
In comparing losses we keep the fixed original law $P$ and its fixed
posterior versions $q_i$, rather than recomputing predictors under the
image law of $R$.

**Proposition 8.2 (Guarded cocycle and failure of preservation).** Put
$D(x)=\Delta_P(x,Rx)$. On $E\cap\Omega$, only losses at $-1,0,1$
change, and

$$
D(x)=2r_{H(x)}-1+2r_{H(x)}^2
=\begin{cases}
11/49,&H(x)=1/3,\\
-33/169,&H(x)=1/4.
\end{cases}
\qquad
R^{1/3}(E)=\frac4{27},\quad R^{1/4}(E)=\frac{81}{320}.
\tag{8.3}
$$

Consequently, under (2.1), checked here in ordinary mathematics, and
Standing interface 2.2,
Theorem 4.1 implies $\neg\mathsf{RP}(P)$.

Proof. For any nontrivial legal insertion, $x_{-1}=x_0=x_1=0$.
Write $r=r_{H(x)}$ and
$m(x)=\mathbf1_{\{x_{-2}=0\}}+\mathbf1_{\{x_2=0\}}$.
The center loss difference is $r^2-(1-r)^2=2r-1$. Each adjacent
site has visible bit zero; its predictor changes from $r$ to zero
exactly when its other neighbor is zero, contributing $r^2$ in that
case. For $|i|\ge2$, the bit, its neighbors and $H$ are unchanged,
so its loss is unchanged by (8.1). Hence legality alone yields

$$
D(x)=2r_{H(x)}-1+m(x)r_{H(x)}^2,
\qquad m(x)\in\{0,1,2\}.
\tag{8.4}
$$

The radius-two guard in $E$ is required to set $m=2$; legality does
not do so. When $Rx=x$, $D(x)=0$. The component transition probabilities
in [Universal, (7.1)][U] give
$R^a(E)=(1-a)^4/(1+a)$, yielding the two positive probabilities in
(8.3). Substitution gives its two distinct, nonzero cocycle values.
If $\mathsf{RP}(P)$ held, Theorem 4.1 would supply a saturated conull
$\Omega_0$ on which all finite-change cocycles vanish. But
$E\cap\Omega_0$ has positive probability, and saturation places
$Rx$ in $\Omega_0$ there, contradicting (8.3). $\square$

**Proposition 8.3 (Finite-coordinate minimax obstruction).** For every
finite $K\subset\mathbb Z$ and every real-valued estimator $g$ based
only on the original/modified records
$Y_K(x)=(x|_K,(Rx)|_K)$,

$$
\operatorname*{ess\,sup}_{x\sim P(\,\cdot\mid E)}
\left|g(Y_K(x))-D(x)\right|
\ \ge\ \frac12\left|\frac{11}{49}+\frac{33}{169}\right|
=\frac{1738}{8281}.
\tag{8.5}
$$

Different finite sets for the two records are included by taking their
union. The lower bound is sharp for every $K$: the constant estimator
$g=121/8281$, the midpoint of the two target values, attains it.

Proof. On $E$, the modification changes only the known center zero to
one. Every positive-probability $Y_K$ fiber within $E$ therefore fixes
only finitely many original bits and is a nonempty legal cylinder.
Both component laws have positive probability on every such cylinder,
by [Universal, Proposition 7.2][U]. Removing $\Omega^c$ preserves these
probabilities. Thus the same observed record occurs with both labels
on sets of positive conditional probability. For any value $z$ assigned
to it, the triangle inequality gives
$\max(|z-11/49|,|z+33/169|)\ge1738/8281$.
There are only finitely many record fibers, proving (8.5); the midpoint
proves sharpness. Independent randomization cannot lower this bound:
condition on the seed and apply the same argument, with essential
supremum taken over the joint conditional law. $\square$

This is a conditional essential-supremum absolute-error bound, not a
mean-square, mean-absolute, or fixed error-probability bound. Its
boundary-locality consumer is [Exterior Localization, §6][L]: a
finite visible collar for the center cocycle is a special case of
$K$, so finite hidden presentation does not supply that missing
finite-boundary-dependence hypothesis. Three changing summands do not
make their values recoverable from a finite visible boundary.

**Proposition 8.4 (Almost-surely-finite coordinate queries and recovery
boundary).** Let a protocol query original visible coordinates
$X_{i_1},X_{i_2},\ldots$, with indices in $\mathbb Z$. Its choices,
stopping rule and real output are measurable functions only of the finite
transcript of queried indices and revealed bits and a random seed $S$ independent
of $(H,X)$, with a common law $\nu$ under both components. Suppose
it terminates after $T<\infty$ queries $(P\otimes\nu)$-almost surely;
no deterministic query bound is imposed. Then its output $\widehat D$
cannot recover $D$ exactly even on $E$:

$$
(P\otimes\nu)(\widehat D\ne D\mid E)>0.
\tag{8.6}
$$

Proof. Suppose exact recovery held almost surely on $E$. Since both
mixture weights and both component probabilities of $E$ are positive,
Fubini gives a seed for which termination and exactness hold on $E$
almost surely under each component. Fix that seed. There are countably
many finite stopping transcripts. Their leaves cover $E$ up to null
sets, so some stopping leaf has positive $R^{1/3}$ probability within
$E$. For a fixed seed, following that transcript and stopping is
determined by precisely its finitely many revealed original bits.
Its intersection with $E$ is therefore a nonempty legal cylinder,
positive also under $R^{1/4}$. The same leaf has the same output under
both laws, whereas exactness requires $11/49$ under one and $-33/169$
under the other, a contradiction. This positive common-support leaf
argument proves (8.6) without a uniform error-probability constant.
$\square$

The contract excludes tail queries, source-correlated advice and a
supplied $H$ label. It does not apply to arbitrary finite-valued
summaries: $H$ itself is a two-valued tail summary. If $H$ and the five
local bits $x_{-2},\ldots,x_2$ are supplied, the identity cases and
(8.4) recover $D$ on all of $\Omega$; on $E$, $H$ alone suffices.
Acquisition of this label and retention of it for the comparison are
separate obligations; its finite number of values supplies neither.

This `repo-derived` application reuses the four-state construction,
the cocycle interface and Theorem 4.1; its minimax and stopping-leaf
steps are elementary common-support arguments, with no priority claim.
It is ordinary mathematics with no Lean/kernel verification. It gives
no new $c_\star$ conclusion, nonzero intrinsic response or all-$N$
separation, and supplies no native-operation, metric, transport or
physical three-dimensional bridge.

## 追加锚（本行以下为增补区）

## 8.99 Scope of the adaptive-query application

**Scope clarification 8.5 (independent finite-query argument).**
Proposition 8.4 is a source-specific ordinary-mathematical application, not
an invocation of a generic DEV finite-query theorem. Its proof uses only the
displayed mixture, the positive mass of $E$ under both components, a
source-independent seed, almost-surely finite stopping, the countable family
of finite stopping transcripts, and the fact that every nonempty legal finite
cylinder in $E$ has positive mass under both component laws. Its contract is
therefore limited to adaptive queries of original visible coordinates and
exact recovery of $D$ on $E$ under $P\otimes\nu$. It makes no claim for tail
queries, source-correlated advice or seeds, an externally supplied $H$ label,
arbitrary finite-valued summaries, approximate recovery, or a different
source/response contract. A result from another DEV source may be reused only
after an explicit correspondence of source, responses, seed law, stopping
semantics and target; no such transfer is asserted here. The proposition
remains unverified by Lean or the kernel.

## 追加锚（本行以下为增补区）
