# FIB harmonic-edge load: exterior localization and actual loss-cocycle balance

This volume constructs an integrable loss-difference cocycle on finite legal
modifications and localizes intrinsic-null responses at individual exterior
environments. The general construction assumes the necessary posterior band
and explicit square-root summability of actual one-sided erasure defects.
The positive-pair refinement instead consumes the existing two-word exterior
cancellation directly and needs no independent tail premise. These are
ordinary mathematical proofs; neither universal productivity nor finite
attainment or all-dimension strict separation is established.

## 1. Complete domain, original law and supplied interfaces

**Definition 1.1 (Original objective and producer).** For $n\ge1$, retain
the entire legal open-path word set $B_n$ and configuration space

$$
B_n=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

The graph $\Gamma_n$ has every legal Hamming-one edge. Endpoint insertions
use $w_0=w_{n+1}=0$, without joining the endpoints. On the whole simplex,

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\quad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\quad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\quad
c_\star=\lim_n\kappa_n/n.
$$

Zero masses do not remove vertices or edges. For each finite $N\ge1$ use
[Universal, Definition 4.1 and Proposition 4.2][U]'s entire domain

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
\ M_0,M_1\ge0,\ A=M_0+M_1,\ A\mathbf1=\mathbf1,
\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.1}
$$

Here $\lambda$ is a row and $M_0,M_1$ are $N\times N$ exact-real matrices.
The fixed parameter $\theta$ supplies one actual stationary joint law

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P([w]_a)=\lambda M_w\mathbf1,
\tag{1.2}
$$

where $P=P_\theta$ is its visible marginal, $M_w$ is the ordered product,
and the empty product is $I$. All coordinates are original emitted bits.
Structural zeros, zero stationary masses, reducibility, periodicity and
noncontractive presentations remain allowed. Scalar stationary legality
in (1.1) is not replaced by entrywise $M_1^2=0$. A seam $uv$ always has
mass $\lambda M_uM_v\mathbf1$, with no independence assumption.

**Convention 1.2 (Fixed original-law losses).** Let $(Tx)_i=x_{i+1}$,
$\mathcal E_i=\sigma(X_j:j\ne i)$ and
$F_i=\{X_{i-1}=X_{i+1}=0\}$. Choose a $[0,1]$ Borel exterior version of
$q_0=\mathbb E_P[X_0\mid\mathcal E_0]$ and set $q_i=q_0\circ T^i$.
Stationarity makes these versions of the actual posteriors. Define

$$
\ell_i(x)=(x_i-q_i(x))^2,\qquad
q_{r,i}=\mathbb E_P[X_i\mid\sigma(X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r})],
\quad D_r(P)=\mathbb E_P(X_0-q_{r,0})^2.
$$

At $r=0$ the field is trivial, so $q_{0,i}=\mathbb E_PX_i$, where the
two-index symbol denotes the radius-zero predictor, not the full $q_i$.
A retained neighbor one forces a finite posterior to zero; an omitted
neighbor supplies no such information. Full posteriors are zero on $F_i^c$
almost surely.
Null finite fibers have arbitrary versions and zero weighted contribution.
The actual risk and growth facts supplied in [Universal, §§1–3][U] are

$$
D_r(P)\downarrow d(P)=\mathbb E_P\ell_0=\lim_n\Phi_n(P_n)/n\le c_\star,
\qquad nc_\star\le\kappa_n\le(n+1)c_\star.
\tag{1.3}
$$

In every expression below, including at a modified configuration,
$q_i$ and $\ell_i$ remain these original $P$ functions. No posterior is
recomputed under a replacement pushforward.

**Convention 1.3 (Intrinsic directions and existing consumers).** For a
finite interval $C=[a,b]$, of length $L=b-a+1$, let
$\mathcal H_C=\sigma(X_j:j\notin C)$ and

$$
\mathcal K_C(P)=\{f\in\mathbb R^{B_L}:\mathbb E_P[f(X_C)\mid\mathcal H_C]=0\}.
$$

For $C=[1,L]$, [Intrinsic, Theorem 2.2][I] identifies this space exactly
with $\ker E_{\theta,L}$, where
$E_{\theta,L}((u,v),w)=\lambda M_uM_wM_v\mathbf1$ and both collar words
have length $N-1$. Translation handles other intervals. Illegal collar
concatenations give zero rows; $N=1$ has an empty collar. This law-invariant
kernel, its row-space annihilator and its infinity/one dual norm are reused
interfaces. The stronger matrix condition $\sum_w f(w)M_w=0$ is sufficient
but is not required here.

Write $S_P(f_C)=\sum_{i\in\mathbb Z}\mathbb E_P[f(X_C)\ell_i]$ only when
that response is absolutely convergent. The supplied attained-law property
is

$$
\mathsf Z(P):\quad
\text{every finite-interval intrinsic-null direction has absolutely
convergent response equal to zero}.
\tag{1.4}
$$

[Multiword, equation (1.3)][M] and [Two-word, §1][W] supply
$d(P)=c_\star\Rightarrow\mathsf Z(P)$, together with the attained-law
budget $D_r(P)-c_\star\le c_\star/(r+1)$ and ceiling
$c_\star\le\bar c:=3-2\sqrt2<1/4$. Their underlying conditional-response
result retains its ownership. These statements do not assume the existence
of an attainer.

## 2. Exact hypotheses and legal replacements

**Definition 2.1 (Band and actual erasure summability).** The general
construction uses the following two explicit hypotheses on this same $P$:

$$
\begin{aligned}
\mathsf B(P):&\quad q_i=0\text{ on }F_i^c,\quad
\tfrac14\le q_i\le\tfrac12\text{ on }F_i,\quad P\text{-almost surely},\\
p^L_j&=\mathbb E_P[X_0\mid X_{-j},\ldots,X_{-1},X_1,X_2,\ldots],\\
p^R_j&=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_j],\\
e_L(j)&=\mathbb E_P(q_0-p^L_j)^2,\qquad
e_R(j)=\mathbb E_P(q_0-p^R_j)^2,\\
A_P&:=\sum_{j\ge0}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr)<\infty.
\end{aligned}
\tag{2.1}
$$

The band is required at every integer site. The entire opposite half-line
remains in each erasure field, also at $j=0$.
[Universal, Theorem 3.1][U] supplies $\mathsf B(P)$ as necessary for
attainment. Square-root summability is an additional hypothesis here;
this volume supplies no general finite-hidden theorem establishing it.
It is stronger than $\tau_P(0)<\infty$, where
$\tau_P(R)=\sum_{j\ge R}(e_L(j)+e_R(j))$. Since the defects lie in $[0,1]$,
(2.1) implies $\tau_P(0)\le A_P$ and $\tau_P(R)\to0$.

**Definition 2.2 (Compatible fibers and finite surgery).** Let $Y=X_{C^c}$
and $\mu_C=P\circ Y^{-1}$. Use a regular conditional mass
$p_C(w;y)=P(X_C=w\mid Y=y)$ on the finite set $B_L$.
Exterior records are taken in the projection of $\mathsf X$ to $C^c$.
Write $wy$ for the configuration obtained by filling $C$ with $w$, and

$$
K_C(w)=\{y:wy\in\mathsf X\},\qquad k(w)=\sum_{t=1}^Lw_t.
$$

Internal legality is already imposed by $w\in B_L$; compatibility asks
exactly that $y_{a-1}w_1=w_Ly_{b+1}=0$. The zero word is always compatible.
Let $Z_Cx=0^Lx_{C^c}$. For a fixed $w$, use the total legal map
$R_{C,w}x=wx_{C^c}$ when $x_{C^c}\in K_C(w)$, and $R_{C,w}x=x$ otherwise.
The identity on incompatible exteriors avoids assigning an illegal image.
Conditional masses on a $\mu_C$-null set may be chosen arbitrarily; all
support assertions below concern a specified conull exterior set.

## 3. Legal surgery and an integrable actual loss cocycle

**Theorem 3.1 (Same-law legal loss-cocycle construction).** Fix any
$\theta\in\Theta_N$ whose actual law satisfies (2.1). For every finite
interval $C$ of length $L$, almost every exterior satisfies

$$
p_C(0^L;y)\ge2^{-L},\qquad
3^{-k(w)}p_C(0^L;y)\le p_C(w;y)\le p_C(0^L;y)
\quad(y\in K_C(w)),
\tag{3.1}
$$

and $p_C(w;y)=0$ for incompatible $w$. In particular, every compatible
completion has conditional mass at least $2^{-L}3^{-k(w)}$.
Every fixed finite legal replacement preserves $P$-null sets. Moreover,

$$
\mathbb E_P\sum_{i\in\mathbb Z}|\ell_i(X)-\ell_i(Z_CX)|
\le L+2(1+2^{L/2})A_P.
\tag{3.2}
$$

There is a Borel $P$-conull set $\Omega\subseteq\mathsf X$, invariant under
shifts and saturated under all finite legal modifications, such that

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z))
\tag{3.3}
$$

is absolutely defined whenever $x,z\in\Omega$ differ at finitely many
coordinates. It is measurable on that relation, antisymmetric, shift
invariant, and obeys $\Delta_P(x,z)=\Delta_P(x,u)+\Delta_P(u,z)$ for any
three configurations in one such class. For any two choices of original
posterior versions, the resulting cocycles agree on a common saturated
conull set. The full construction uses neither visible finite memory nor
a change of the actual joint law (1.2).

Proof. First derive the fiber domination that will make evaluations of
original versions after surgery legitimate. The supplied band, integrated
against any $B\in\mathcal E_i$, gives

$$
\begin{aligned}
P(B,X_i=0)&\ge\tfrac12P(B) &&(B\in\mathcal E_i),\\
\tfrac13P(B,X_i=0)\le P(B,X_i=1)&\le P(B,X_i=0)
&&(B\in\mathcal E_i,\ B\subseteq F_i).
\end{aligned}
\tag{3.4}
$$

These inequalities are used here as the existing band/insertion mechanism,
not as a separate result. To pass them to $Y$-fibers, test against arbitrary
$\{Y\in H\}$ and a specification of other coordinates of $C$. Such an
event is external to $i$. Order the $L$ coordinates of $C$ and successively
specify zero. At each step the first inequality of (3.4) costs at most
$1/2$. Consequently $P(Y\in H,X_C=0^L)\ge2^{-L}\mu_C(H)$ for every $H$,
which is the first inequality of (3.1) by conditional integration.

Fix $w$ and restrict $H$ to $K_C(w)$. Starting from the zero block, insert
its $k(w)$ ones in any order. For each insertion all other block positions
are specified. Both neighbors of that insertion are zero: inserted ones
are nonadjacent, and an endpoint neighbor outside $C$ is zero by
compatibility. Thus the second pair of inequalities in (3.4) compares the
two entire-block events, with the same exterior event $H$. Iterating gives
$3^{-k(w)}P(Y\in H,X_C=0^L)\le P(Y\in H,X_C=w)
\le P(Y\in H,X_C=0^L)$. Conditional integration gives (3.1).
Incompatible completions have zero mass by legality. There are finitely
many words at each interval and countably many intervals, so these
conditional statements can be chosen simultaneously. This argument covers
$L=1$, both endpoint ones when legal, and every zero or forced seam.

For the zero replacement let $Q_C^0=(Z_C)_*P$. Disintegration against any
nonnegative Borel function $v$ proves the density identity

$$
\int v\,dQ_C^0=\int v(0^Ly)\,d\mu_C(y)
=\int v(x)\frac{\mathbf1_{\{x_C=0^L\}}}{p_C(0^L;x_{C^c})}\,dP(x),
\qquad Q_C^0\le2^LP.
\tag{3.5}
$$

All ratios are used only on the conull set where their denominators are
positive; set them to zero elsewhere. For another word, the pushforward
of $\mathbf1_{\{Y\in K_C(w)\}}P$ under replacement by $w$ is a
subprobability $Q_C^w$ with

$$
\frac{dQ_C^w}{dP}(x)=
\frac{\mathbf1_{\{x_C=w\}}\mathbf1_{K_C(w)}(x_{C^c})}
{p_C(w;x_{C^c})},\qquad Q_C^w\le2^L3^{k(w)}P.
\tag{3.6}
$$

The identity part of $R_{C,w}$ adds a measure bounded by $P$. Hence
$(R_{C,w})_*P\ll P$, as do finite compositions of such maps. More
generally, a measurable choice among these finitely many replacements is
nonsingular by partitioning its domain according to the selected word.
Neither $Q_C^0$ nor $Q_C^w$ is asserted stationary; these measures serve
only to dominate integrals of the fixed original losses and predictors.

Translate $C$ to $[1,L]$. For $i\le0$, let $a_i^C$ be a $[0,1]$ Borel
version of $\mathbb E_P[X_i\mid\sigma(X_j:j\le0,j\ne i)]$; for
$i\ge L+1$ use $\mathbb E_P[X_i\mid\sigma(X_j:j\ge L+1,j\ne i)]$.
Each is a function of the indicated coordinates, so
$a_i^C(Z_Cx)=a_i^C(x)$ pointwise. Stationarity identifies the exact defects

$$
\mathbb E_P(q_{-j}-a_{-j}^C)^2=e_R(j),\qquad
\mathbb E_P(q_{L+1+j}-a_{L+1+j}^C)^2=e_L(j),\quad j\ge0.
\tag{3.7}
$$

For example the left field retains the entire left half-line and exactly
$j$ bits to the right of the site $-j$ before the cut. At $j=0$ it omits
the right neighbor inside $C$. A full forced center therefore need not
have zero reduced defect. Both terms at $j=0$ are retained in (3.7).

For either exterior site write $e$ for its defect in (3.7). Cauchy–Schwarz
under the probability $P$, then under the probability $Q_C^0$, gives

$$
\begin{aligned}
\mathbb E_P|q_i-a_i^C|&\le\sqrt e,\\
\mathbb E_P|q_i(Z_CX)-a_i^C(X)|
&=\mathbb E_{Q_C^0}|q_i-a_i^C|
\le\bigl(\mathbb E_{Q_C^0}(q_i-a_i^C)^2\bigr)^{1/2}
\le2^{L/2}\sqrt e.
\end{aligned}
\tag{3.8}
$$

The exterior emitted bit is unchanged by $Z_C$. The elementary bound
$|(x-u)^2-(x-v)^2|\le2|u-v|$ for $x\in\{0,1\}$ and $u,v\in[0,1]$
therefore bounds that site's expected absolute loss difference by
$2(1+2^{L/2})\sqrt e$. The $L$ interior sites each cost at most one.
Tonelli's theorem and (2.1) now give (3.2), with all original offsets.
In particular $V_C(x):=\sum_i|\ell_i(x)-\ell_i(Z_Cx)|$ is finite almost
surely for every $C$.

It remains to turn these individual almost-sure statements into one
pathwise construction. Choose a Borel conull set $B$ on which every $V_C$
is finite, the band and forced identities hold at every site, and all the
countably many conditional-version agreements and support identities used
above hold. Countable intersections are legitimate here. Let $\mathcal G$
be the countable monoid of finite compositions generated by all $R_{C,w}$,
the shifts $T,T^{-1}$ and the identity. Every member is nonsingular for
$P$: this was proved for replacements and follows from stationarity for
shifts. Thus

$$
\Omega=\bigcap_{G\in\mathcal G}G^{-1}B
\tag{3.9}
$$

is Borel and conull. Closure of $\mathcal G$ under composition implies
$G\Omega\subseteq\Omega$ for every generator. Since both shifts occur,
$T\Omega=\Omega$. If $x\in\Omega$ and $z\in\mathsf X$ differs from it
only in a finite interval $C$, then $z=R_{C,z_C}x$; hence $z\in\Omega$.
This proves saturation under every finite legal modification, including
ones whose location or replacement word was chosen from the configuration.

For such $x,z$, $Z_Cx=Z_Cz$. The pointwise triangle inequality yields

$$
\sum_i|\ell_i(x)-\ell_i(z)|\le V_C(x)+V_C(z)<\infty.
\tag{3.10}
$$

Thus (3.3) does not depend on a containing interval or an order of summation.
Antisymmetry and additivity follow by termwise identities in absolutely
convergent series; for a triple use an interval containing all changes.
Our chosen versions satisfy $\ell_i(T^kx)=\ell_{i+k}(x)$ pointwise, so
reindexing gives $\Delta_P(T^kx,T^kz)=\Delta_P(x,z)$. Symmetric finite
partial sums of Borel functions converge to (3.3), proving measurability
on the finite-modification relation restricted to $\Omega$.

Finally any other actual posterior versions agree with these $P$-almost
surely at every site. Add those countably many agreement sets to $B$ and
repeat (3.9); nonsingularity preserves all agreements after every finite
replacement. The two cocycles are then identical on the resulting relation.
The same reasoning treats alternative actual reduced predictors and
conditional-mass versions wherever used. This is independence for any
fixed choices, not a claim of one null set accommodating an uncountable
collection of every conceivable version. No values are transported from
the posterior of a different law. $\square$

## 4. Exterior localization and all-length conditional balance

**Definition 4.1 (Integrable conditional loss contrast).** Under (2.1),
use the cocycle just constructed and set, for $f\in\mathcal K_C(P)$,

$$
\begin{aligned}
T_{C,f}(y)
&=\sum_{w:\,y\in K_C(w)}p_C(w;y)f(w)\Delta_P(wy,0^Ly)\\
&=\mathbb E_P[f(X_C)\Delta_P(X,Z_CX)\mid\mathcal H_C](y).
\end{aligned}
\tag{4.1}
$$

These versions agree almost surely. Indeed $P(\Omega)=1$ and finite
disintegration imply that for almost every $y$ every positive conditional
completion belongs to $\Omega$; (3.1) makes this every compatible
completion, including zero. Define the expression to be zero on the
remaining exterior null set. Equation (3.2) gives

$$
\|T_{C,f}\|_{L^1(\mu_C)}\le
\|f\|_\infty\bigl[L+2(1+2^{L/2})A_P\bigr].
\tag{4.2}
$$

Pointwise on this conull exterior set, any other compatible reference
completion gives the same contrast: cocycle additivity changes each
$\Delta_P(wy,0^Ly)$ by one common number, whose coefficient sum is
$\sum_w p_C(w;y)f(w)=0$. This reference invariance uses intrinsic nullity.

The supplied response norm, when $\tau_P(0)<\infty$, is
$\gamma_L(P)=\max\{|S_P(f_{[1,L]})|:f\in\mathcal K_{[1,L]}(P),
\ \|f\|_\infty\le1\}$. Its finiteness and attainment follow from
[Intrinsic, Proposition 4.1][I]; (2.1) supplies its tail hypothesis here.

**Theorem 4.2 (Localization across block lengths).** Assume (2.1). For
every $f\in\mathcal K_C(P)$, every bounded finite-coordinate exterior
function $g$, and every finite interval $D$ containing $C$ and the
coordinates used by $g$, define the block direction

$$
h_D(X_D)=f(X_C)g(X_{D\setminus C}).
$$

Then $h_D\in\mathcal K_D(P)$, and its absolutely convergent response is

$$
S_P(h_D)=\mathbb E_P[g(Y)T_{C,f}(Y)].
\tag{4.3}
$$

Consequently, if the supplied full-response norms $\gamma_L(P)$ vanish
for every finite $L$, then $T_{C,f}=0$ $\mu_C$-almost surely for every
finite interval $C$ and every intrinsic $f$. These balances can be imposed
simultaneously. Conversely, if any one $T_{C,f}$ is nonzero on a set of
positive actual exterior probability, there is a finite exterior-cylinder
indicator $g$ for which (4.3) is nonzero. It gives an intrinsic-null
direction on a finite enlarged block with $\gamma_{|D|}(P)>0$.

Proof. The fields satisfy $\mathcal H_D\subseteq\mathcal H_C$. Since $g$
is $\mathcal H_C$-measurable, the tower property gives

$$
\mathbb E_P[h_D\mid\mathcal H_D]
=\mathbb E_P[g\mathbb E_P[f(X_C)\mid\mathcal H_C]\mid\mathcal H_D]=0.
\tag{4.4}
$$

Thus [Intrinsic, Theorem 2.2][I] accepts $h_D$ in the exact collar kernel
after translating $D$. This is true even when $g$ depends on exterior
bits immediately adjacent to $C$ or on both sides. Values on unsupported
finite patterns can be specified boundedly; their actual integrals are
zero. There is no matrix-null requirement or change of presentation.

For each individual $i$, the bounded function $\ell_i(Z_CX)$ depends
only on $Y$. Hence intrinsic nullity gives

$$
\mathbb E_P[h_D\ell_i]=
\mathbb E_P[h_D(\ell_i(X)-\ell_i(Z_CX))].
\tag{4.5}
$$

Subtract this one reference term before doing any infinite summation.
The total expected absolute value of the right-hand integrands is at most
$\|f\|_\infty\|g\|_\infty\mathbb E_PV_C<\infty$. Therefore the response
on the left converges absolutely, and summation under the integral on the
right is justified. Its sum is
$\mathbb E_P[g f(X_C)\Delta_P(X,Z_CX)]$, which disintegrates to (4.3).
Neither $\sum_i\ell_i$ nor a response of a nonnull word indicator has
been introduced. In particular, there is no subtraction of two possibly
infinite total losses or total expectations.

The inherited norm $\gamma_L$ is available: (2.1) gives $\tau_P(0)<\infty$,
so [Intrinsic, Proposition 4.1][I] and [Multiword, Lemma 2.1][M] apply on
every intrinsic kernel. Under all-length zero response, choose $g$ to be
the indicator of any finite exterior cylinder. Equation (4.3) makes its
integral against $T_{C,f}$ zero. These integrals define a finite signed
measure $\nu_f(H)=\int_H T_{C,f}\,d\mu_C$, by (4.2). Finite cylinders,
including the whole space, form a generating intersection-stable family;
finite signed-measure uniqueness implies $\nu_f=0$ on the full exterior
field. Taking its positive and negative sets proves $T_{C,f}=0$ almost
surely. This obtains an exterior-by-exterior conclusion from tests at all
enlarged block lengths, rather than only the original averaged response.

For simultaneity, choose a finite basis of each finite-dimensional
$\mathcal K_C(P)$. The formula (4.1) is pointwise linear in $f$ where
defined. Intersect the conull sets for the finitely many basis vectors
and then over the countably many intervals. Every real linear combination
therefore has the asserted balance on its corresponding exterior fiber.
Equivalently these can be pulled back to one conull subset of $\mathsf X$.

If $\mu_C(T_{C,f}\ne0)>0$, its signed measure is nonzero. Were the integral
on every finite cylinder zero, the same uniqueness argument would give
the contradiction $T_{C,f}=0$ almost surely. Thus one cylinder has nonzero
integral. Its indicator defines a bounded finite-coordinate $g$ and some
finite $D$ as above; $D$ can be enlarged further while $h_D$ ignores the
extra coordinates. Equation (4.3) gives a nonzero response;
normalizing the nonzero direction $h_D$ proves $\gamma_{|D|}(P)>0$.
No sign of this integral is presumed, and no bound on $D$ is obtained.
$\square$

For a hypothetical attainer satisfying the additional $A_P<\infty$
hypothesis, (1.4) gives all the zero responses required by Theorem 4.2.
Conversely zero conditional contrasts for every $C,f$ imply all-length
zero response simply by taking $g=1$ in (4.3). This equivalence concerns
the response route; it is not an equivalence with attainment.

## 5. Tail-free pointwise refinement for existing positive pairs

**Theorem 5.1 (Conditional interior-score balance using old cancellation).**
Let $P=P_\theta$ be any original stationary legal law satisfying
$\mathsf Z(P)$, with no band or independent erasure-tail premise required
for this statement. Suppose distinct words $v,w\in B_L$ have positive
actual masses and
$f_C=\alpha\mathbf1_{\{X_C=v\}}-\beta\mathbf1_{\{X_C=w\}}$
belongs to $\mathcal K_C(P)$, with $\alpha,\beta>0$.
On their common conditional exterior support,

$$
\sum_{i\in C}(v_i-q_i(vY))^2
=\sum_{i\in C}(w_i-q_i(wY))^2
\quad\text{almost surely}.
\tag{5.1}
$$

Here $v_i,w_i$ denote the block coordinates at site $i$; the exterior
measure can be either of the two equal normalized conditional laws.
In particular every hypothetical attainer satisfies (5.1) for each such
pair it possesses. This asserts no positive-pair existence.

Proof. Apply [Two-word, Theorem 2.1][W] directly. It supplies the common
exterior law $\nu$, the positive balance
$J=\alpha P(X_C=v)=\beta P(X_C=w)$, and, for every $i\notin C$, equality
of the original restricted posteriors $q_i(vY)=q_i(wY)$ $\nu$-almost
surely. The resulting losses agree there too. These are exactly the
existing cancellation result, including both seam sites; they are not
reproved here. Its countable conull choice lets us multiply each equality
by any bounded exterior function, even one involving $X_i$.

Set $B_C(v;y)=\sum_{i\in C}\ell_i(vy)$ and similarly for $w$, and put
$a(y)=\alpha p_C(v;y)=\beta p_C(w;y)$. Intrinsic nullity gives this last
identity as an identity of conditional masses, and
$a\,d\mu_C=J\,d\nu$. Thus $a>0$ on the common positive conditional
support, up to its null set. No assertion is made on exteriors where
both conditional masses vanish.

Given any finite exterior-cylinder function $g$, form $h_D=f_Cg$ as in
(4.4). That tower calculation requires neither (2.1) nor a cocycle, and
still proves $h_D\in\mathcal K_D(P)$. For every $i\notin C$ the supplied
posterior restriction gives $\mathbb E_P[h_D\ell_i]=0$. The remaining
sum is finite, and disintegration yields

$$
S_P(h_D)=\mathbb E_{\mu_C}[g\,a(B_C(v;Y)-B_C(w;Y))]
=J\mathbb E_\nu[g(B_C(v;Y)-B_C(w;Y))].
\tag{5.2}
$$

Its absolute response sum is at most $LJ\|g\|_\infty$, since each
conditional loss difference has absolute value at most one. Property
$\mathsf Z(P)$ makes (5.2) zero for every finite exterior-cylinder
indicator. The bounded difference $B_C(v;Y)-B_C(w;Y)$ defines a finite
signed measure against $\nu$. Cylinder uniqueness makes it zero
$\nu$-almost surely, which is (5.1). Equivalently the weighted contrast
$a(B_C(v;Y)-B_C(w;Y))$ is zero $\mu_C$-almost surely. Conditional on
$a>0$ this is the same pointwise equality.

Positive-event conditioning and the common exterior law preserve all
original $P$-null posterior exceptions, precisely as in the cited theorem.
There is no need for a zero-block surgery or its integrability here. If
one selected word has zero mass, intrinsic nullity with positive
coefficients forces both masses to be zero; then $f_C=0$ almost surely,
and no conditional pair law or productive witness is obtained. $\square$

The added conclusion is the pointwise interior balance obtained from
all-length tests. The cancellation itself is reused support. For a pair
whose interior difference is nonzero on positive $\nu$ probability, the
same cylinder argument in (5.2) produces a nonzero enlarged-block response
and contradicts $\mathsf Z(P)$. This is conditional on an actual such
contrast. [Multiword, Proposition 4.2][M] already exhibits a finite law
without any positive pair at any length, so pair reasoning does not
replace the general intrinsic multiword construction.

## 6. Faithful finite consumers and mathematical boundaries

Under (2.1), $\eta_P(R):=\tau_P(R)$ is an attainment-independent finite
vanishing allowance, although the assertion gives no effective way to
evaluate it. If Theorem 4.2 supplies a nonzero $S_P(h_D)$, [Multiword,
Theorem 3.1][M] applies directly: some finite integers $R,r\ge0$ give

$$
\left|\sum_{i\in[a_D-R,b_D+R]}
\mathbb E_P[h_D(X_D)(X_i-q_{r,i})^2]\right|
>\|h_D\|_\infty\left[\eta_P(R)+2(|D|+2R)\sqrt{\bar c/(r+1)}\right],
\tag{6.1}
$$

where $D=[a_D,b_D]$. The consumer therefore certifies $d(P)<c_\star$.
[Intrinsic, Corollary 3.4][I] translates existence of a normalized
intrinsic witness at these radii into the corresponding strict
$\ell^1$ distance from the finite loss vector to
$\operatorname{range}(E_{\theta,|D|}^{\mathsf T})$. Its exact collar,
annihilator and dual threshold are used unchanged. Neither criterion
provides the missing nonzero contrast.

Every finite predictor in (6.1) uses actual cylinder masses. For a positive
radius-$r$ exterior fiber $(u,v)$ its value is
$\lambda M_uM_1M_v\mathbf1/(\lambda M_uAM_v\mathbf1)$; empty words give
the prior at $r=0$. Zero denominators contribute zero and are not divided
by; retained forcing neighbors give zero numerator. All block/window
overlaps and both endpoint seams remain. The finite-certificate converse
to a nonzero full response is not asserted: a certificate can contradict
an attainer's projection budget without demonstrating $S_P(h_D)\ne0$.

For a law with the stated band, suppose one separately supplies an actual-law allowance
$\tau_P(R)\le B\rho^{\lfloor R/m\rfloor}$ for every $R\ge0$, with finite
$B\ge0$, integer $m\ge1$ and $0\le\rho<1$. It verifies the remaining
$A_P<\infty$ hypothesis of the general construction:

$$
\sqrt{e_L(j)}+\sqrt{e_R(j)}
\le\sqrt{2B}\rho^{\lfloor j/m\rfloor/2},\qquad
A_P\le\frac{\sqrt{2B}\,m}{1-\sqrt\rho}.
\tag{6.2}
$$

Indeed $e_L(j)+e_R(j)\le\tau_P(j)$ and
$(\sqrt u+\sqrt v)^2\le2(u+v)$; each exponent in the resulting geometric
sum occurs $m$ times. For $\rho=0$ use $0^0=1$; only the first $m$ terms
can remain. If $B=0$, every defect vanishes. This is a conditional
consumption calculation, not a supplied general finite-hidden rate theorem.
Mere summability of $e_L+e_R$ does not justify the square-root sum used in
(3.8), and an attained-law projection budget is not substituted for it.

The band restricts only the hypotheses of the conditional construction;
it does not redefine $\Theta_N$. For example deterministic all-zero laws
remain in (1.1) and fail the free posterior band. Structural hidden zeros
are still permitted even when the band derives positivity of compatible
visible conditional completions. An incompatible seam always has zero
conditional mass; null exterior records carry no asserted pointwise
balance. Nonzero $T_{C,f}$ means nonzero on positive $\mu_C$ probability,
not a value chosen on a null record. A zero direction, a direction zero
on actual support, or positive kernel dimension alone gives no witness.

The cocycle is a measurable function on a saturated conull
finite-modification relation. No continuous extension to all legal
configurations, finite-boundary dependence, finite-range potential,
visible Markov order or identity with a conditional log-probability ratio
has been proved. The original finite hidden presentation supplies none of
these missing bridges. In particular a finite-visible-order cancellation
argument has a different hypothesis and cannot be applied to (1.1).

## 7. Attribution and the unchanged productive obligation

The compound results are the legal, version-preserving construction of
(3.3), the localization (4.3), and the ensuing conditional balances.
The construction and conditional balances are established here in
Theorems 3.1, 4.2 and 5.1, using the canonical results of [Universal][U],
[Intrinsic][I], [Multiword][M] and [Two-word][W] with the uses and limits
specified below. It is a synthesis
relative to the supplied results; abstract cocycle algebra, conditional
expectation and signed-measure uniqueness are mature ingredients.

| Source or ingredient | Exact use and limit |
| --- | --- |
| [Universal][U], §§1–4 and Theorem 6.2 | Complete original objective, actual $J_\theta/P_\theta$, necessary posterior band and insertion inequalities, and the fixed-$N$ separation equivalence. No new attainment implication is attributed to the band. |
| [Intrinsic][I], Theorem 2.2, Theorem 3.2, Corollary 3.4 and Proposition 4.1 | Exact intrinsic collar, annihilator/dual residual and tail-qualified response norm. These are consumers and support, not new independent theorems here. |
| [Multiword][M], Lemma 2.1 and Theorem 3.1 | Actual erasure offsets, exterior response control, finite certificate and detectability. Square-root summability is stated separately. |
| [Two-word][W], Theorem 2.1 | Equality of the two actual exterior laws and posterior restrictions, including seams. Theorem 5.1 consumes it directly to obtain the additional conditional interior equality. |
| [Dawid–Lauritzen–Parry][DLP], §4.2, especially Example 4.4 and (14) | Conditional Brier scoring and squared conditional discrepancy. The full-product strict-propriety argument assumes everywhere-positive distributions; it is not imported into hard no11. |
| [Chandgotia–Meyerovitch][CM], §§2.2–3 | Finite-modification equivalence and additive cocycles are established language. Their Markov cocycles require finite-boundary dependence, and their specification correspondence uses conditional log ratios. Those additional conclusions are not asserted for (3.3). |

Zero is a safe legal replacement symbol for no11, but that fact alone does
not provide the Markov-cocycle hypothesis in [CM]. Even on this support,
one must prove the missing locality and probability-ratio bridges before
using its Markov or Gibbs conclusions. The bounded comparison credits
these mature ingredients without a worldwide priority claim or an
empirical statistical-performance claim.

**Open Problem 7.1 (Original finite attainment and all-$N$ separation).**
With the entire unchanged domain (1.1), let
$C_N=\sup_{\theta\in\Theta_N}d(P_\theta)$ and
$U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta)$.
Still decide whether some finite exact producer attains $c_\star$, or
whether $C_N<c_\star$ for every finite $N$. The latter is equivalent, by
[Universal, Theorem 6.2][U], to

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\kappa_m/(m+1).
$$

For the response route the remaining obligation is to prove, for each
intended remaining producer, a conditional contrast nonzero on positive
actual exterior probability, or another productive intrinsic direction.
No such remaining producer is exhibited here, and no universal
$\gamma_L(P)>0$ is obtained. General finite-hidden square-root
integrability, uniform parameter-family constants, an efficient enlarged
block or detecting radius, and a fixed-$N$ uniform margin are also not
provided. The pair refinement does not owe integrability but still owes
pair existence and a nonzero interior contrast to produce a witness.

A fixed lawful necessary-band example with $A_P<\infty$ satisfying every
conditional balance would obstruct this full-response route on that law; it would
prove neither attainment nor failure of all finite budget certificates.
No such obstruction is established here. Strict nonattainment alone is
not identified with nonzero full response. The next structural question
is whether the same finite producer can obey every balance of Theorem 4.2,
or whether one actual intrinsic relation violates it on a finite exterior
cylinder. The cocycle construction makes that question precise without
settling either alternative.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[I]: FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md
[M]: FIB_LEGAL_EDGE_LOAD_MULTIWORD_RESPONSE_STABILITY_AND_VANISHING_TAIL_CERTIFICATE.md
[W]: FIB_LEGAL_EDGE_LOAD_TWO_WORD_EXTERIOR_CANCELLATION_AND_VANISHING_CERTIFICATE.md
[DLP]: https://arxiv.org/html/1104.2224v2 "A. Philip Dawid, Steffen Lauritzen and Matthew Parry, Proper Local Scoring Rules on Discrete Sample Spaces"
[CM]: https://arxiv.org/html/1305.0808v3 "Nishant Chandgotia and Tom Meyerovitch, Markov Random Fields, Markov Cocycles and The 3-colored Chessboard"

## 追加锚（本行以下为增补区）
