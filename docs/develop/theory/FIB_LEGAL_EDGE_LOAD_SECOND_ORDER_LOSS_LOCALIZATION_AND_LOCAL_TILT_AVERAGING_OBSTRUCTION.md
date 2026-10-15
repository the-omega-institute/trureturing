# FIB harmonic-edge load: second-order loss localization and local tilt averaging obstruction

This volume strengthens the actual loss cocycle to an absolute $L^2$ series, identifies its centered
score, and localizes its integrable square contrast. It gives finite detection with a paid error
allowance, twice differentiable integrated conditional tilts, and a total-variation limit for averaging
one fixed local tilt. These are handwritten mathematical results under the stated hypotheses. Neither
cancellation of the square contrast nor the original finite-attainment alternative is established.

## 1. Original domain, common realization and hypothesis layers

**Convention 1.1 (Complete original objective and producer).** For $n\ge1$, retain

$$
B_n=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

$\Gamma_n$ has every legal Hamming-one edge on all of $B_n$. Endpoint insertions use $w_0=w_{n+1}=0$,
without identifying the endpoints. Put

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\quad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\quad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\quad
c_\star=\lim_n\kappa_n/n.
\tag{1.1}
$$

Zero masses retain their vertices and edges. For every finite $N\ge1$, the entire domain of [Universal,
Definition 4.1][U] is

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
\ M_0,M_1\ge0,\ A=M_0+M_1,\ A\mathbf1=\mathbf1,
\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.2}
$$

The row $\lambda$ and the $N\times N$ matrices have exact-real entries. Fix $\theta\in\Theta_N$. All
quantities use [Universal, Proposition 4.2][U]'s one actual stationary joint law and its visible marginal
$P=P_\theta$:

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P([w]_a)=\lambda M_w\mathbf1.
\tag{1.3}
$$

$M_w$ is the ordered product, with empty product $I$. Coordinates keep the original emitted-bit clock.
Structural zeros, zero stationary masses, reducibility, periodicity and nonminimal presentations remain
permitted. The scalar legality equation is not replaced by entrywise $M_1^2=0$. Every seam $uv$ uses
$\lambda M_uM_v\mathbf1$, without independence.

**Convention 1.2 (Fixed original-law functions).** With $(Tx)_i=x_{i+1}$, choose a Borel exterior version
of $q_0$ and its translates $q_i=q_0\circ T^i$:

$$
\mathcal E_i=\sigma(X_j:j\ne i),\quad q_i=\mathbb E_P[X_i\mid\mathcal E_i],
\quad \ell_i(x)=(x_i-q_i(x))^2,\quad F_i=\{X_{i-1}=X_{i+1}=0\}.
$$

Let $q_{r,i}$ be the same-law posterior given the radius-$r$ exterior window and
$\ell_{r,i}=(X_i-q_{r,i})^2$. The two-index $q_{0,i}$ is the prior $\mathbb E_PX_i$, distinct from the
full posterior $q_0$ at site zero. [Universal, §1][U] supplies

$$
D_r(P)=\mathbb E_P\ell_{r,0}\downarrow d(P)=\mathbb E_P\ell_0
=\lim_n\Phi_n(P_n)/n\le c_\star,\qquad
\|q_i-q_{r,i}\|_2^2=D_r(P)-d(P).
\tag{1.4}
$$

All norms without another measure are under $P$. Every posterior evaluated at a replaced configuration or
inside a tilt remains this original $P$ function. No posterior is recalculated under a replacement or
tilted law. A retained neighbor one forces a finite posterior to zero; an omitted neighbor gives no such
information. Null finite fibers have arbitrary versions and zero weighted contribution.

**Definition 1.3 (Band and square-root erasure premise).** The analytic construction assumes the
following on the same $P$, at every integer site:

$$
\mathsf B(P):\quad q_i=0\text{ on }F_i^c,\qquad
\tfrac14\le q_i\le\tfrac12\text{ on }F_i,\quad P\text{-almost surely},
\tag{1.5}
$$

$$
\begin{aligned}
p^L_j&=\mathbb E_P[X_0\mid X_{-j},\ldots,X_{-1},X_1,X_2,\ldots],\\
p^R_j&=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_j],\\
e_L(j)&=\mathbb E_P(q_0-p^L_j)^2,\qquad e_R(j)=\mathbb E_P(q_0-p^R_j)^2,\\
A_P(R)&=\sum_{j\ge R}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr),\qquad
A_P=A_P(0)<\infty.
\end{aligned}
\tag{1.6}
$$

The whole opposite half-line is retained, including at $j=0$; both zero-offset defects remain. A forcing
neighbor erased from the field can leave a nonzero defect. The band is necessary for attainment by
[Universal, Theorem 3.1][U]. The root-sum premise is additional, with no asserted general finite-hidden
supplier, effective rate or uniform bound.

**Convention 1.4 (Intrinsic kernel and first-order balance).** For a nonempty finite interval $C=[a,b]$
of length $L$, write

$$
\mathcal H_C=\sigma(X_j:j\notin C),\quad Y=X_{C^c},\quad
\mu_C=P\circ Y^{-1},\quad p_C(w;y)=P(X_C=w\mid Y=y),\quad
\mathcal K_C(P)=\{f\in\mathbb R^{B_L}:\mathbb E_P[f(X_C)\mid\mathcal H_C]=0\}.
\tag{1.7}
$$

For $C=[1,L]$, [Intrinsic, Theorem 2.2 and Corollary 2.3][I] identify this law-invariant kernel with
$\ker E_{\theta,L}$, where $E_{\theta,L}((u,v),w)=\lambda M_uM_wM_v\mathbf1$ and both collar words have
length $N-1$. All actual zero rows remain; $N=1$ has an empty collar. The matrix-null condition
$\sum_w f(w)M_w=0$ is only sufficient. Set $\mathcal V_C=\mathcal K_C(P)^\perp$; the supplied finite
realization bounds its dimension by $N^2$. Neither that bound nor positive kernel dimension supplies a
productive direction.

The separate first-order premise is the supplied property

$$
\mathsf Z(P):\quad
\sum_{i\in\mathbb Z}\bigl|\mathbb E_P[f(X_C)\ell_i]\bigr|<\infty,
\qquad S_P(f_C):=\sum_i\mathbb E_P[f(X_C)\ell_i]=0
\quad(C\text{ finite},\ f\in\mathcal K_C(P)).
\tag{1.8}
$$

[Cocycle, Convention 1.3 and Theorem 4.2][E] supply attainment $\Rightarrow
\mathsf Z(P)$ and, under (1.5)–(1.6), its equivalence with the all-length
conditional balances in (2.3) below. The $L^2$ estimates, general $C^2$
integrals and local-law averaging do not assume $\mathsf Z(P)$.

Under hypothetical $d(P)=c_\star$, retain all the original necessary conditions, as supplied in
[Universal, Theorems 3.1 and 5.1][U] and [Two-word, §1][W]: for all locations, legal $w\in B_n$, and
$m,n\ge1$,

$$
\begin{gathered}
P([0^m]_a)\ge2^{-m},\qquad P([w]_a)\ge2^{-(n+2)}3^{-k(w)},\\
nc_\star\le\Phi_n(P_n)\le\kappa_n\le(n+1)c_\star,\qquad
0\le D_r(P)-c_\star\le\frac{c_\star}{r+1},\quad r\ge0,\\
c_\star\le\bar c:=3-2\sqrt2<\tfrac14.
\end{gathered}
\tag{1.9}
$$

Here $k(w)$ counts ones. Positive-weight actual hidden closed classes also attain, including periodic
classes. These conclusions do not establish an attainer. The band alone gives neither attainment nor
(1.9)'s risk budget. In particular, the all-$n$ bulk lower bound already implies attainment on taking its
limit; a low-risk band-only law cannot falsify a claim retaining that lower bound. The original $N=1$
all-zero law remains in (1.2), although it fails (1.5), so the band-qualified construction does not apply
to it.

## 2. Reused legal fibers and the actual cocycle

**Convention 2.1 (Supplier correspondence and versions).** Exterior records lie in the projection of
$\mathsf X$ to $C^c$. Write $wy$ for completion of $y$ by $w$ on $C$, and $Z_Cx=0^Lx_{C^c}$. A word is
compatible with $y$ exactly when it is in $B_L$ and both boundary seams are legal. [Cocycle, Theorem 3.1
and equations (3.5)–(3.7)][E] supply, almost surely,

$$
\begin{gathered}
p_C(0^L;y)\ge2^{-L},\qquad
3^{-k(w)}p_C(0^L;y)\le p_C(w;y)\le p_C(0^L;y)
\quad(w\text{ compatible}),\\
p_C(w;y)\ge c_L:=2^{-L}3^{-\lceil L/2\rceil}\quad(w\text{ compatible}),
\qquad (Z_C)_*P\le2^LP.
\end{gathered}
\tag{2.1}
$$

Incompatible words have mass zero. All finite legal replacement maps are nonsingular. There is a
shift-invariant, finite-modification-saturated Borel conull set $\Omega$ on which the original absolutely
convergent cocycle is

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z)),\qquad
\Delta_P(x,z)=\Delta_P(x,u)+\Delta_P(u,z)
\tag{2.2}
$$

whenever the configurations differ only finitely. It is measurable, antisymmetric and shift invariant.
These are reused results, not new cocycle or support claims of this volume.

For almost every $y$, finite disintegration and (2.1) place every compatible completion, including zero,
in $\Omega$. Put, on this set,

$$
\begin{aligned}
D_C(x)&=\Delta_P(x,Z_Cx),&d_C(w;y)&=\Delta_P(wy,0^Ly),\\
m_C(y)&=\sum_w p_C(w;y)d_C(w;y),&a_C(w;y)&=d_C(w;y)-m_C(y),\\
T_{C,f}(y)&=\sum_w p_C(w;y)f(w)d_C(w;y).
\end{aligned}
\tag{2.3}
$$

All word sums are over compatible words; zero values may be assigned to incompatible terms and to
exceptional exterior records. The supplier gives $D_C\in L^1(P)$ and $T_{C,f}\in L^1(\mu_C)$. Under
(1.5)–(1.6), $\mathsf Z(P)$ is equivalent to $T_{C,f}=0$ almost surely for every $C,f$. In particular
$p_C(\cdot;y)\in\mathcal V_C$, and under these balances $p_C(\cdot;y)d_C(\cdot;y)\in\mathcal V_C$. These
are linear annihilator statements; closure under multiplying by $d_C$ does not follow.

For $C=[1,L]$ the supplier's reduced original predictor $b_i^C$ conditions only on the exterior half-line
containing $i$, with $i$ omitted. It is unchanged by $Z_C$, and the exact offsets are

$$
\|q_{-j}-b_{-j}^C\|_2^2=e_R(j),\qquad
\|q_{L+1+j}-b_{L+1+j}^C\|_2^2=e_L(j),\qquad j\ge0.
\tag{2.4}
$$

Translations give the corresponding predictors for any $C$. They and every loss in (2.2) belong to
(1.3)'s original law, not to a surgery pushforward.

All subsequent almost-sure statements admit simultaneous choices for countably many intervals and sites.
For statements linear in $f$, take a finite basis of each $\mathcal K_C(P)$ and then use linearity. To
evaluate new identities after replacements, intersect their Borel conull sets with the inverse images
under the countable monoid of shifts and fixed finite legal replacements. Nonsingularity makes this
intersection conull and saturated. Finite disintegration and positive compatible masses then give
identities at every compatible completion on almost every exterior. For any fixed two collections of
original-law versions, the same construction makes them agree there; no universal null set for all
conceivable versions is asserted.

## 3. Absolute second moments and a sharper centered score

**Theorem 3.1 (Same-law $L^2$ bounds without first-order balance).** Assume (1.5)–(1.6). Define the
constants $\mathsf B_L$ and $K_L$ and the variables

$$
\begin{aligned}
\mathsf B_L&=L+2(1+2^{L/2})A_P,& K_L&=L/2+2A_P,\\
V_C^{\rm abs}&=\sum_i|\ell_i(X)-\ell_i(Z_CX)|,&
u_{C,i}&=\ell_i-\mathbb E_P[\ell_i\mid\mathcal H_C].
\end{aligned}
\tag{3.1}
$$

The different typography distinguishes the constant $\mathsf B_L$ from the legal word set $B_L$. Then

$$
\|V_C^{\rm abs}\|_2\le\mathsf B_L,\quad \|D_C\|_2\le\mathsf B_L,
\quad \left\|\sum_i|u_{C,i}|\right\|_2\le K_L,\qquad
a_C(X_C;Y)=\sum_i u_{C,i}
\quad\text{in }L^2(P)\text{ and almost surely}.
\tag{3.2}
$$

Both series are absolutely convergent almost surely. In particular the normalized score $a_C$ is a series
of centered original losses.

Proof. Translate to $C=[1,L]$. For an exterior site let $e$ be its defect in (2.4). Domination and
invariance of $b_i^C$ under replacement give

$$
\|q_i-b_i^C\|_2=\sqrt e,\qquad
\|q_i\circ Z_C-b_i^C\|_2^2
=\int(q_i-b_i^C)^2\,d((Z_C)_*P)\le2^Le.
\tag{3.3}
$$

For $x\in\{0,1\}$ and $s,t\in[0,1]$, $|(x-s)^2-(x-t)^2|\le2|s-t|$. Exterior bits are unchanged, so (3.3)
and the triangle inequality imply

$$
\|\ell_i-\ell_i\circ Z_C\|_2\le2(1+2^{L/2})\sqrt e.
\tag{3.4}
$$

Each interior absolute difference is at most one. Minkowski therefore bounds every finite sum of absolute
differences by $\mathsf B_L$ in $L^2$. Exhaust the sites increasingly; monotone convergence applied to
the squares gives $\mathbb E_P(V_C^{\rm abs})^2\le\mathsf B_L^2$, hence finiteness almost surely. Since
$|D_C|\le V_C^{\rm abs}$, its bound follows. This strengthens the supplier's $L^1$ conclusion using its
bounded density and actual $L^2$ defects; $L^1$ alone would not supply the second moment.

For the sharper estimate, denote conditional projection onto $\mathcal H_C$ by $\Pi_C$. At an exterior
site, $g_i=(X_i-b_i^C)^2$ is $\mathcal H_C$-measurable. Orthogonal projection and the same loss
inequality give

$$
\|u_{C,i}\|_2=\|(I-\Pi_C)(\ell_i-g_i)\|_2
\le\|\ell_i-g_i\|_2\le2\sqrt e.
\tag{3.5}
$$

At an interior site, $0\le\ell_i\le1$. If $z=\Pi_C\ell_i$, its conditional variance is at most
$z-z^2\le1/4$, so $\|u_{C,i}\|_2\le1/2$. Minkowski and monotone convergence now bound the absolute sum by
$K_L$.

For completeness, let $F_n$ exhaust $\mathbb Z$ by finite sets and put
$D_{C,n}=\sum_{i\in F_n}(\ell_i-\ell_i\circ Z_C)$. The square-integrable majorant just proved gives
$D_{C,n}\to D_C$ in $L^2$. Conditional projection is continuous in $L^2$, and each $\ell_i\circ Z_C$ is
$\mathcal H_C$-measurable. Thus

$$
D_C-\Pi_CD_C
=\lim_n(D_{C,n}-\Pi_CD_{C,n})
=\lim_n\sum_{i\in F_n}u_{C,i}=\sum_i u_{C,i}.
\tag{3.6}
$$

The last series also converges almost surely and in $L^2$ by its absolute majorant. Disintegration
identifies $\Pi_CD_C=m_C(Y)$ and $D_C=d_C(X_C;Y)$, proving (3.2). Only differences and centered losses
were summed; no infinite raw total loss was subtracted from another. The centered estimate itself uses
stationarity and (1.6); the band and supplied cocycle supply its identification at legal completions.
$\square$

**Theorem 3.2 (Integrable square residual and two-site expansion).** Under (1.5)–(1.6), for
$f\in\mathcal K_C(P)$ set

$$
R_{C,f}(y)=\sum_w p_C(w;y)f(w)d_C(w;y)^2.
\tag{3.7}
$$

It belongs to $L^1(\mu_C)$ with norm at most $\|f\|_\infty\mathsf B_L^2$. If additionally $T_{C,f}=0$
almost surely, then

$$
\begin{aligned}
R_{C,f}&=\mathbb E_P[f(X_C)a_C(X_C;Y)^2\mid\mathcal H_C]\\
&=\sum_{i,j\in\mathbb Z}\mathbb E_P[f(X_C)u_{C,i}u_{C,j}\mid\mathcal H_C],
\qquad \|R_{C,f}\|_1\le\|f\|_\infty K_L^2.
\end{aligned}
\tag{3.8}
$$

The double series converges absolutely in $L^1$ and almost surely, dominated by an integrable conditional
sum of absolute products.

Proof. The first assertion is conditional integration of $|f|D_C^2$ and Theorem 3.1. Write $d_C=a_C+m_C$.
Intrinsic nullity gives $\sum p_Cf=0$; $T_{C,f}=0$ then gives $\sum p_Cfa_C=0$. Expanding the square
leaves $\sum p_Cfd_C^2=\sum p_Cfa_C^2$. This is also an identity of integrable conditional quantities:
$m_C(Y)\in L^2$ by conditional contraction, and all mixed terms are integrable by Cauchy–Schwarz. The
centered bound gives the sharper norm estimate. Finally, Tonelli and Theorem 3.1 yield

$$
\sum_{i,j}\mathbb E_P|f(X_C)u_{C,i}u_{C,j}|
\le\|f\|_\infty\mathbb E_P\left(\sum_i|u_{C,i}|\right)^2
\le\|f\|_\infty K_L^2.
\tag{3.9}
$$

Conditional Tonelli makes the conditional absolute majorant integrable and finite almost surely. Absolute
summation therefore commutes with conditional expectation, and (3.2) proves (3.8). The two factors refer
to the same actual configuration under $P$, not independent copies. $\square$

## 4. Reference changes, pairs and exact exterior localization

**Proposition 4.1 (Reference invariance and the already controlled pair span).** Under (1.5)–(1.6),
intrinsic nullity and $T_{C,f}=0$ make $R_{C,f}$ invariant under replacing the zero reference by any
measurable compatible completion $s(y)y$. Under $\mathsf Z(P)$ it vanishes on the span
$\mathcal K_C^{\rm pair}$ of positive two-word intrinsic relations.

Proof. Let $b(y)=d_C(s(y);y)$. The finite choices and (2.1) give

$$
|b(y)|^2\le c_L^{-1}\sum_w p_C(w;y)d_C(w;y)^2,
\qquad \|b\|_{L^2(\mu_C)}\le c_L^{-1/2}\mathsf B_L.
\tag{4.1}
$$

Additivity changes $d_C$ to $d_C-b$. All square and cross terms are integrable, and the change in (3.7)
is $-2bT_{C,f}+b^2\sum p_Cf=0$. Also $m_C$ changes to $m_C-b$, so $a_C$ itself is reference independent,
even without first-order balance.

For a generator $f=\alpha\mathbf1_v-\beta\mathbf1_w$, $\alpha,\beta>0$, with positive actual word masses,
[Two-word, Theorem 2.1][W] gives a common exterior law, $\alpha p_C(v;y)=\beta p_C(w;y)$, and equality of
original exterior losses on its support. [Cocycle, Theorem 5.1][E] uses $\mathsf Z(P)$ to give equality
of the interior total losses there. Consequently $d_C(v;y)=d_C(w;y)$ on the common positive conditional
support. Their weighted squares cancel, and both weighted masses vanish elsewhere. Linearity proves the
span assertion. The same finite-fiber argument gives pointwise identities for every nonnegative integer
power on this span; it does not assert integrability of higher powers. Zero-mass word pairs give only a
zero actual direction and no conditional pair law. $\square$

Thus $f\mapsto R_{C,f}$ factors through $\mathcal K_C(P)/\mathcal K_C^{\rm pair}$ under all first-order
balances. Neither a nontrivial quotient nor a nonzero functional on it is asserted.

**Theorem 4.2 (Square-residual localization and all-length equivalence).** Assume (1.5)–(1.6) and
$\mathsf Z(P)$. Let $f\in\mathcal K_C(P)$, let $g$ be a bounded function of finitely many exterior
coordinates, and let $D$ be any finite interval containing $C$ and these coordinates. Define
$h_D(X_D)=f(X_C)g(Y)$. Then $h_D\in\mathcal K_D(P)$ and

$$
R_{D,h_D}=\mathbb E_P[g(Y)R_{C,f}(Y)\mid\mathcal H_D],\qquad
\mathbb E_P[h_DD_D^2]=\int gR_{C,f}\,d\mu_C.
\tag{4.2}
$$

In particular, these conditions are equivalent:

- $R_{C,f}=0$ almost surely for every finite $C$ and $f\in\mathcal K_C(P)$;
- $\mathbb E_P[f(X_C)D_C^2]=0$ for every such $C,f$.

If any $R_{C,f}$ is nonzero on positive actual exterior probability, some finite exterior-cylinder
indicator $g$ makes the right side of (4.2) nonzero, producing a finite enlarged intrinsic direction
outside $\mathcal K_D^{\rm pair}$.

Proof. Since $\mathcal H_D\subseteq\mathcal H_C$,
$\mathbb E_P[h_D\mid\mathcal H_D] =\mathbb E_P[g\mathbb E_P[f(X_C)\mid\mathcal H_C]\mid\mathcal H_D]=0$.
The exact collar accepts this direction, including adjacent seam bits and coordinates on either side of
$C$. Bounded values on unsupported patterns are immaterial. Cocycle additivity on the saturated set gives

$$
D_D=D_C+b,\qquad b(X)=\Delta_P(Z_CX,Z_DX)=D_D-D_C.
\tag{4.3}
$$

Both configurations defining $b$ ignore $X_C$, so $b$ is $\mathcal H_C$-measurable. Theorem 3.1 gives
$b\in L^2$. Expand $fg(D_C+b)^2$. All terms are integrable, and conditioning on $\mathcal H_C$ removes
the cross term $2gb\mathbb E_P[fD_C\mid\mathcal H_C]=2gbT_{C,f}=0$ and the term
$gb^2\mathbb E_P[f\mid\mathcal H_C]=0$. The remaining term is $gR_{C,f}$. Unbounded $b$ causes no
module-property gap: truncate it, apply conditional expectation, and pass in $L^1$ using Cauchy–Schwarz.
The tower property gives (4.2).

By Theorem 3.2, $\nu(H)=\int_H R_{C,f}\,d\mu_C$ is a finite signed measure on the exterior. Finite
cylinders, including the whole space, form an intersection-stable generating family. If all their
integrals were zero, signed-measure uniqueness would give $\nu=0$, hence $R_{C,f}=0$ almost surely.
Therefore a nonzero residual has a cylinder with nonzero integral, and (4.2) gives the asserted
direction. Proposition 4.1 excludes membership in its pair span. If all integrated all-length identities
hold, apply them to these $h_D$ and invoke the same uniqueness argument. The reverse implication is
direct integration of (3.7). Finite kernel bases and countably many intervals give simultaneous
conditional identities as in Convention 2.1. $\square$

For a single localization identity it suffices to assume $T_{C,f}=0$; all-length $\mathsf Z(P)$ supplies
this uniformly and the pair conclusion. The cylinder and enlarged block have no effective or uniform size
bound. Under the theorem's hypotheses $S_P(h_D)=0$ remains true. A nonzero square contrast supplies no
new nonzero first-order response or strict-risk certificate, and no actual nonzero square contrast is
asserted here.

## 5. Finite predictors and paid square-detection errors

**Theorem 5.1 (Fixed-law finite approximation and detection).** Assume (1.5)–(1.6). For integers
$R,r\ge0$ put

$$
\begin{aligned}
I_R&=[a-R,b+R]\cap\mathbb Z,\qquad \delta_r=\sqrt{D_r(P)-d(P)},\\
D_{C,R,r}(x)&=\sum_{i\in I_R}\bigl(\ell_{r,i}(x)-\ell_{r,i}(Z_Cx)\bigr),\\
\varepsilon_{C,R,r}&=2(1+2^{L/2})\bigl[A_P(R)+(L+2R)\delta_r\bigr].
\end{aligned}
\tag{5.1}
$$

Then $\|D_C-D_{C,R,r}\|_2\le\varepsilon_{C,R,r}$. For $f\in\mathcal K_C(P)$ and a bounded
finite-coordinate exterior $g$, set

$$
I=\int gR_{C,f}\,d\mu_C,\qquad
W_{R,r}=\mathbb E_P[f(X_C)g(Y)D_{C,R,r}^2],\qquad
\sigma_{R,r}=\|D_{C,R,r}\|_2.
$$

For every justified finite upper allowance $\widehat\varepsilon\ge\varepsilon_{C,R,r}$,

$$
|W_{R,r}-I|\le\|f\|_\infty\|g\|_\infty
\widehat\varepsilon(2\sigma_{R,r}+\widehat\varepsilon).
\tag{5.2}
$$

A strict excess of $|W_{R,r}|$ over this threshold proves $I\ne0$. If $I\ne0$ and justified allowances
can be made arbitrarily small by choosing $R$ and then $r$, a finite strict test exists. Neither the
approximation nor (5.2) needs first-order balance; its interpretation as the normalized tilt's
second-order obstruction uses $T_{C,f}=0$.

Proof. The omitted left and right exterior sites have exactly offsets $j\ge R$ in (2.4), including $j=0$
when $R=0$. Equation (3.4) and Minkowski bound their sum in $L^2$ by $2(1+2^{L/2})A_P(R)$. At each
retained site, (1.4) and the loss inequality give

$$
\|\ell_i-\ell_{r,i}\|_2\le2\delta_r,\qquad
\|(\ell_i-\ell_{r,i})\circ Z_C\|_2\le2^{L/2}\,2\delta_r.
\tag{5.3}
$$

The second bound uses (2.1), with the same original losses at the modified configuration. There are
$L+2R$ retained sites; summing proves (5.1)'s error bound. By definition, $I=\mathbb E_P[fgD_C^2]$. The
factorization of a difference of squares and Cauchy–Schwarz give

$$
|W_{R,r}-I|\le\|f\|_\infty\|g\|_\infty
\|D_{C,R,r}-D_C\|_2\bigl(\|D_{C,R,r}\|_2+\|D_C\|_2\bigr).
$$

Use $\|D_C\|_2\le\sigma_{R,r}+\widehat\varepsilon$ to obtain (5.2). For detectability, $A_P(R)\to0$ and,
for fixed $R$, $\delta_r\to0$. First make the tail small by choosing $R$, then the finite-window error
small by choosing $r$. Also $\sigma_{R,r}\le\mathsf B_L+\widehat\varepsilon$. Thus if valid upper
allowances tend to zero in that selection order, the right side of (5.2) becomes smaller than $|I|/2$.
Then $|W_{R,r}|\ge|I|-|W_{R,r}-I|$ strictly exceeds the threshold. $\square$

Both $W_{R,r}$ and $\sigma_{R,r}^2$ are finite observables determined by the single actual cylinder
marginal covering $[a-R-r,b+R+r]$ and the coordinates of $g$. The latter is a second moment, not a
centered variance. Every positive radius-$r$ exterior fiber $(u,v)$ uses

$$
q_{r,i}=\frac{\lambda M_uM_1M_v\mathbf1}{\lambda M_uAM_v\mathbf1}.
\tag{5.4}
$$

Empty $u,v$ give the prior at $r=0$. Zero denominators require no division; choose zero there.
Nonsingularity of $Z_C$ preserves their nullity even at modified evaluations. Retained forcing neighbors
give zero numerator. All overlaps, every legal seam and every endpoint remain in this one finite
marginal; unspecified coordinates are summed, never factorized.

The analytic premise gives existence of vanishing $A_P(R)$, not an effective upper allowance. Under
hypothetical attainment only, (1.9) permits $\delta_r\le\sqrt{\bar c/(r+1)}$; any root-tail allowance
must still be justified for the same $P$. No finite test value or strict margin is supplied. If
$\mathsf Z(P)$ also holds, Theorem 4.2 turns a nonzero conditional residual into an $I\ne0$ to which this
test applies. It still does not contradict attainment: that would require an additional theorem making
$R=0$ necessary. This is distinct from [Intrinsic, Corollary 3.4][I]'s existing first-order strict-risk
certificate.

## 6. Integrated normalized conditional tilts are twice differentiable

**Theorem 6.1 ($C^2$ without exponential moments).** Under (1.5)–(1.6), for each real $t$ and almost
every exterior define

$$
\pi_C^t(w;y)=\frac{p_C(w;y)e^{t d_C(w;y)}}{\sum_vp_C(v;y)e^{t d_C(v;y)}}
=\frac{p_C(w;y)e^{t a_C(w;y)}}{\sum_vp_C(v;y)e^{t a_C(v;y)}}.
\tag{6.1}
$$

Incompatible words have probability zero; on exceptional exteriors choose $p_C$. These measurable finite
kernels are unchanged by reference choice. For any bounded $f:B_L\to\mathbb R$ and bounded exterior $g$,
the function

$$
\Psi_{C,f,g}(t)=\int g(y)\sum_w f(w)\pi_C^t(w;y)\,d\mu_C(y)
\tag{6.2}
$$

is $C^2$ on all of $\mathbb R$, with $|\Psi''(t)|\le2\|f\|_\infty\|g\|_\infty c_L^{-1}K_L^2$. If
$f\in\mathcal K_C(P)$ and $T_{C,f}=0$, then

$$
\Psi(0)=\Psi'(0)=0,\qquad \Psi''(0)=\int gR_{C,f}\,d\mu_C.
\tag{6.3}
$$

Proof. Subtracting the common $m_C(y)$ cancels in the quotient. All scores are finite on each compatible
fiber. Define $M(y)=\max_w|a_C(w;y)|$ over that fiber, and set it to zero on the exceptional set.
Positive support and Theorem 3.1 give the actual integrable bound

$$
M(y)^2\le c_L^{-1}\sum_wp_C(w;y)a_C(w;y)^2,\qquad
\int M^2\,d\mu_C\le c_L^{-1}K_L^2.
\tag{6.4}
$$

At a fixed exterior let $\bar a_t=\sum_w\pi_C^t(w;y)a_C(w;y)$ and
$v_t=\sum_w\pi_C^t(w;y)(a_C(w;y)-\bar a_t)^2$. Finite differentiation gives $\bar a_t'=v_t$ and

$$
(\pi_w^t)'=\pi_w^t(a_w-\bar a_t),\qquad
(\pi_w^t)''=\pi_w^t\bigl((a_w-\bar a_t)^2-v_t\bigr).
\tag{6.5}
$$

In particular, on each compatible word, $\left.\partial_t\log\pi_C^t(w;y)\right|_{t=0}=a_C(w;y)$. Thus
Theorem 3.1 identifies the normalized logarithmic score with the centered original-loss series.

Since $v_t\le\sum_w\pi_w^ta_w^2\le M^2$, Cauchy–Schwarz and the triangle inequality give bounds
independent of $t$:

$$
\sum_w|(\pi_w^t)'|\le\sqrt{v_t}\le M,\qquad
\sum_w|(\pi_w^t)''|\le2v_t\le2M^2.
\tag{6.6}
$$

Multiplication by $\|f\|_\infty\|g\|_\infty$ gives integrable majorants for the first two derivatives of
the integrand. Its value is bounded by $\|f\|_\infty\|g\|_\infty$. The fundamental theorem of calculus
for each finite fiber and dominated convergence justify differentiating the integral twice; pointwise
continuity of (6.5) and the same majorants give continuity of both derivatives. No integral of an
unnormalized exponential has been assumed finite.

At zero, $\bar a_0=0$. Intrinsic nullity gives $\sum p_Cf=0$, while $T_{C,f}=0$ gives $\sum p_Cfa_C=0$.
In the second derivative the term $-v_0\sum p_Cf$ vanishes, leaving $\sum p_Cfa_C^2=R_{C,f}$ by Theorem
3.2. This proves (6.3) and the uniform second-derivative bound. $\square$

If (6.3)'s last integral is nonzero, then $\Psi(t)=\tfrac12t^2\int gR_{C,f}\,d\mu_C+o(t^2)$ is nonzero
for every sufficiently small nonzero $t$. Thus $\sum_w f(w)\pi_C^t(w;y)$ is nonzero on positive $\mu_C$
probability: one original intrinsic relation fails. Conversely, zero second derivative for all finite
exterior-cylinder indicators $g$ forces $R_{C,f}=0$ by signed-measure uniqueness. The theorem gives
neither higher integrated moments nor preservation of $\mathcal V_C$ beyond first order. Finite-fiber
analyticity alone supplies no higher dominated differentiation.

## 7. Averaging one fixed local tilted law returns to the original law

**Theorem 7.1 (One-block realization and total-variation obstruction).** Assume (1.5)–(1.6), with no
$\mathsf Z(P)$ premise. Fix one finite $C$ and one $t\in\mathbb R$. The density

$$
\rho_{C,t}(x)=\frac{\pi_C^t(x_C;x_{C^c})}{p_C(x_C;x_{C^c})},\qquad
Q_{C,t}=\rho_{C,t}P
\tag{7.1}
$$

is well defined on the positive actual fibers. Set it to one on the exceptional null set. Then

$$
0\le\rho_{C,t}\le c_L^{-1}\quad P\text{-almost surely},\qquad
\mathbb E_P[\rho_{C,t}\mid\mathcal H_C]=1,\qquad
\left\|\frac1n\sum_{k=0}^{n-1}(T^k)_*Q_{C,t}-P\right\|_{\rm TV}\longrightarrow0.
\tag{7.2}
$$

This includes reducible and periodic producers. Total variation here is $\sup_A|Q(A)-P(A)|$. No
convergence rate is asserted.

Proof. Conditional summation of (7.1) gives one, and $\pi_C^t\le1$ together with (2.1) bounds the
density. Thus it is in $L^2(P)$ and $Q_{C,t}$ is a probability with the same complete exterior marginal
$\mu_C$. More explicitly, for any exterior event $H$,
$Q_{C,t}(X_C=w,Y\in H)=\int_H\pi_C^t(w;y)\,d\mu_C(y)$. It realizes precisely this block kernel.

Let $\mathcal I$ be the shift-invariant sigma-field modulo $P$-null sets. [Universal, Theorem 5.1][U]
decomposes this same actual law into finitely many distinct visible ergodic laws with positive weights.
Their labels are measurable from past word frequencies. These frequencies can be taken entirely to the
left of $C$; deleting finitely many terms has no effect on a limit. Equivalently, modifying $C$ changes
only finitely many occurrences for each fixed word, so it cannot change those frequencies. The labels
therefore have $\mathcal H_C$-measurable versions. An invariant event has probability zero or one in each
ergodic component and is, modulo $P$, a union of their labels. Conversely the labels are invariant. Hence
$\mathcal I\subseteq\mathcal H_C$ modulo null sets, and

$$
\mathbb E_P[\rho_{C,t}\mid\mathcal I]=1.
\tag{7.3}
$$

These are actual component labels; no independently chosen hidden or visible decomposition is
substituted. Irreducible periodic classes are ergodic for the one-step shift as supplied there; mixing is
unnecessary.

Use the classical Hilbert mean ergodic theorem in [Tao, Theorem 2 and the conditional-expectation
Corollary 2][ME], with $Uv=v\circ T^{-1}$ on $L^2(P)$. Finite cylinder simple functions are dense, so
this Hilbert space is separable. To exhibit the precise application, $U$ is unitary by invertibility and
stationarity, and

$$
L^2(P)=\operatorname{Fix}(U)\mathbin{\oplus}
\overline{\operatorname{range}(I-U)},\qquad
\operatorname{Fix}(U)=L^2(\mathcal I,P).
\tag{7.4}
$$

Indeed the orthogonal complement of the range is $\ker(I-U^*)=\operatorname{Fix}(U)$, and invariant
functions have invariant level sets. On $(I-U)v$, the averaging operator is $(v-U^nv)/n$, whose norm is
at most $2\|v\|_2/n$. Averages have operator norm at most one, so this convergence extends to the closure
of the range; on the fixed subspace they are the identity. Thus (7.3)–(7.4) yield

$$
\bar\rho_n:=\frac1n\sum_{k=0}^{n-1}U^k\rho_{C,t}\longrightarrow1
\quad\text{in }L^2(P).
\tag{7.5}
$$

Stationarity identifies $U^k\rho_{C,t}$ as the density of $(T^k)_*Q_{C,t}$ with respect to $P$.
Consequently the distance in (7.2) is $\tfrac12\|\bar\rho_n-1\|_1\le\tfrac12\|\bar\rho_n-1\|_2$, proving
it. The Hilbert theorem and this norm comparison are classical; the content of this application is the
exterior normalization preserving the actual invariant components of the given producer. $\square$

$C$ and $t$ are fixed before averaging. The construction supplies no stationary law simultaneously
realizing all interval kernels, and no finite hidden realization of $Q_{C,t}$. Even if a local
second-order defect exists, these translate averages recover $P$. A different stationary continuation
would require its own construction and control of joint modifications, original losses and any desired
rank preservation; this result neither provides nor rules out such a continuation. No growing-block or
positive-density modification limit is taken.

## 8. Attribution, precise increment and unresolved mathematical obligations

The increment relative to the canonical suppliers is the absolute $L^2$ bound and sharper centered score,
their integrable two-site square expansion, the second-order localization and paid finite detection,
integrated $C^2$ control, and the application of mean ergodic convergence to one actual local tilt.
Support, the original cocycle, intrinsic kernels, first-order balance and pair cancellation retain their
existing ownership. The results are a synthesis, with no worldwide-priority or empirical
statistical-performance claim.

| Source | Correspondence and limit |
| --- | --- |
| *FIB 合法边调和负载：普适后验缺陷与有限隐藏维数分离* [U], §§1, 3–6 | Original objective, exact $\Theta_N$, $J_\theta/P_\theta$, band, all-$n$ attained bounds, actual ergodic components and fixed-$N$ separation equivalence. The band is not sufficient for attainment. |
| *FIB harmonic-edge load: intrinsic null kernel, dual residual and presentation obstruction* [I], Theorem 2.2, Corollary 2.3, §3 | Original collar kernel, annihilator and finite first-order certificate. No new kernel, dual wrapper or productive sign is introduced. |
| *FIB harmonic-edge load: exterior localization and actual loss-cocycle balance* [E], Theorems 3.1, 4.2, 5.1 | Positive compatible fibers, nonsingular surgery, actual cocycle, first-order localization and conditional pair balance. Its explicit density and $L^2$ defects pay Theorem 3.1 here. |
| *FIB harmonic-edge load: two-word exterior cancellation and a vanishing certificate* [W], Theorem 2.1 and §1 | Original common exterior laws, posterior restriction including seams, attained response and projection budget. Pair cancellation is reused, not a new quotient witness. |
| Dawid–Lauritzen–Parry, *Proper Local Scoring Rules on Discrete Sample Spaces* [DLP], §4.2, Example 4.4, (14) | Conditional binary Brier scores are exactly the losses $\ell_i$; squared conditional discrepancies use original-law weights. Full-product strict propriety assumes everywhere-positive distributions and is not transferred to hard no11. |
| Chandgotia–Meyerovitch, *Markov Random Fields, Markov Cocycles and The 3-colored Chessboard* [CM], §§2.2–3 | Finite-modification relations, cocycle algebra and normalized exponential specifications are mature. Their Markov cocycles require finite-boundary dependence; their specification correspondence uses conditional log ratios. Neither bridge is proved for $\Delta_P$. Zero being a safe symbol does not supply them. |
| Balle–Panangaden–Precup, *A Canonical Form for Weighted Automata and Applications to Approximate Minimization* [BPP], §§2.2, 3.1 | The parameter correspondence is $\alpha_0^{\mathsf T}=\lambda$, $A_x=M_x$, $\alpha_\infty=\mathbf1$; algebraic forward/backward factorization is applicable. Stationary cylinder masses sum to one at each length, not over all strings. No summable-series, bounded-Hankel, SVD, minimality or nonlinear tilt-closure theorem is imported. |
| Tao, *254A, Lecture 8: The mean ergodic theorem* [ME], Theorem 2 and conditional-expectation Corollary 2 | Von Neumann's classical Hilbert theorem and Riesz's range/telescoping proof apply to $U:v\mapsto v\circ T^{-1}$, with invariant projection $\mathbb E_P[\cdot\mid\mathcal I]$. No mixing or rate is required. |

Conditional $L^2$ projections, Minkowski, monotone convergence, conditional Tonelli, finite
signed-measure uniqueness and finite exponential-family differentiation are also classical ingredients.
Their use here does not make them new discoveries. The references supply only the indicated
correspondences, not cancellation of the square residual.

**Open Problem 8.1 (Unpaid square cancellation and the original target).** Even under (1.5)–(1.6) and
all-length $\mathsf Z(P)$, whether every $R_{C,f}$ vanishes remains unproved and unrefuted here. The same
question under hypothetical attainment, retaining all of (1.9), remains unresolved. No actual nonzero
$R$, universal productive direction or counterexample to this full necessary-attainer assertion is
supplied. A value on a null exterior, positive quotient dimension, or a low-risk band-only example would
not establish such a counterexample.

A proof would need to cancel the signed two-site expansion on the unpaid quotient. A first-order identity
at one exterior does not put the vector $w\mapsto f(w)d_C(w;y)$ in the original intrinsic kernel: that
kernel requires fixed coefficients satisfying every actual exterior context. Finite rank does not provide
this multiplication rule. Even square cancellation would leave higher orders, full preservation of
conditional spaces, a stationary global construction and any finite-hidden realization unpaid. No
locality, Gibbs property or conditional-log-ratio identity for the original loss cocycle has been
established.

Finally retain the entire (1.2) and set $C_N=\sup_{\theta\in\Theta_N}d(P_\theta)$ and
$U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta)$. The original problem is still whether some finite exact
producer attains $c_\star$, or whether $C_N<c_\star$ for every finite $N$. [Universal, Theorem 6.2][U]
supplies the equivalence of the latter with

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\kappa_m/(m+1).
\tag{8.1}
$$

None of these alternatives is settled. General finite-hidden root-tail summability, effective exterior
cylinders and detection radii, uniform parameter-family allowances, a fixed-$N$ margin and a valid bridge
from second-order continuation to the original risk objective remain absent. All bounds here concern the
stated law and block; no uncontrolled joint limit or new coverage of all finite producers is inferred.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[I]: FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md
[E]: FIB_LEGAL_EDGE_LOAD_EXTERIOR_LOCALIZATION_AND_ACTUAL_LOSS_COCYCLE_BALANCE.md
[W]: FIB_LEGAL_EDGE_LOAD_TWO_WORD_EXTERIOR_CANCELLATION_AND_VANISHING_CERTIFICATE.md
[DLP]: https://arxiv.org/html/1104.2224v2
[CM]: https://arxiv.org/html/1305.0808v3
[BPP]: https://arxiv.org/html/1501.06841v3
[ME]: https://terrytao.wordpress.com/2008/01/30/254a-lecture-8-the-mean-ergodic-theorem/

## 追加锚（本行以下为增补区）

## 9. Conditional spectral interface and triplet boundary capacity

The preceding sections produce finite exterior tests for a scalar square
residual. They do not by themselves identify three spatial channels. The
following result records exactly what would follow if a future realization
supplies such channels with a common rotation action.

**Definition 9.1 (Finite response contract).** Let

$$
\mathcal V=\mathbb R^m\otimes\mathbb R^3,
\qquad
\mathcal Y=\mathbb R^q,
$$

and let $\mathscr R:\mathcal V\to\mathcal Y$ be the linear map formed by a
finite list of declared measurements. A measurement may be one of the finite
tests from §§4–5 after a three-channel interface has been specified. Put

$$
G=\mathscr R^{\mathsf T}\mathscr R.
$$

Assume, as an additional interface hypothesis, that for every
$Q\in SO(3)$ there is an orthogonal $W_Q$ on $\mathcal Y$ such that

$$
\mathscr R(I_m\otimes Q)=W_Q\mathscr R.
\tag{9.1}
$$

This is an equivariance contract, not a consequence of (1.5)–(1.6),
$\mathsf Z(P)$, or the finite-cylinder construction.

**Lemma 9.2 (Equivariant Gram form).** Under (9.1), there is a positive
semidefinite $m\times m$ matrix $A$ such that

$$
\boxed{G=A\otimes I_3.}
\tag{9.2}
$$

**Proof.** Since $W_Q$ is orthogonal, (9.1) gives

$$
(I_m\otimes Q)^{\mathsf T}G(I_m\otimes Q)=G.
$$

Write $G$ as an $m\times m$ block matrix with $3\times3$ blocks. Every
block commutes with every $Q\in SO(3)$. Commutation with half-turns about
the coordinate axes first removes all off-diagonal entries. Commutation with
a quarter-turn taking one coordinate axis to another then makes the three
diagonal entries equal. Hence each block is a scalar multiple of $I_3$;
symmetry and positivity give (9.2). $\square$

**Theorem 9.3 (Exact spectral boundary capacity).** Let the nonzero
eigenvalues of $A$ be

$$
\lambda_1\ge\cdots\ge\lambda_s>0.
$$

Then

$$
\boxed{\operatorname{rank}\mathscr R=3s.}
\tag{9.3}
$$

Every exact linear boundary $S:\mathcal V\to\mathbb R^k$ for which there
exists a linear decoder $D:\mathbb R^k\to\mathcal Y$ satisfying
$$
\mathscr R=DS
$$
for all $v$ satisfies

$$
k\ge3s.
$$

Conversely, $3s$ coordinates suffice by retaining a basis of
$\operatorname{im}\mathscr R$. Thus each nonzero spectral mode is a complete
three-component response; the additional capacity is a multiplicity space,
not a fourth local spatial direction.

**Proof.** The rank of $A\otimes I_3$ is $3\operatorname{rank}A$. If
$\mathscr R=DS$ for some linear decoder $D$, then
$\operatorname{rank}\mathscr R\le\operatorname{rank}S\le k$. Choosing a
row-space basis of $\mathscr R$ gives a summary with $k=\operatorname{rank}
\mathscr R$. $\square$

**Theorem 9.4 (Finite-precision triplet selection).** Suppose the source
coefficient $v$ is centered and whitened, namely
$$
\mathbb E[v]=0,
\qquad
\mathbb E[vv^{\mathsf T}]=I_{3m},
$$
and restrict compression to the equivariant orthogonal projections

$$
P=P_m\otimes I_3,
\qquad
P_m=P_m^{\mathsf T}=P_m^2,
\qquad
0\le r:=\operatorname{rank}P_m\le m.
$$

Write the complete spectrum of $A$ as
$$
\lambda_1\ge\cdots\ge\lambda_m\ge0.
$$

The minimum squared response error is

$$
\boxed{
\min_P\mathbb E\|\mathscr R(v-Pv)\|^2
 =3\sum_{i=r+1}^{m}\lambda_i.
}
\tag{9.4}
$$

The optimal $P_m$ retains eigenvectors for the $r$ largest eigenvalues.
If $r<m$, adding the next complete three-component response lowers the error
by $3\lambda_{r+1}$; if $r=m$, there is no next response group and the gain
is zero.

**Proof.** The error is

$$
\operatorname{tr}\bigl(G(I-P)\bigr)
 =3\operatorname{tr}\bigl(A(I-P_m)\bigr).
$$

The spectral theorem and the finite-dimensional Ky Fan variational principle
select the $r$ largest eigenvalues of $A$, giving (9.4). $\square$

For example, if $A=\operatorname{diag}(9,4)$, the response spectrum is
$9,9,9,4,4,4$ when the multiplicity spaces are written explicitly, and
keeping only the first triplet leaves squared error $12$ under the stated
identity-covariance convention. The example is a response-capacity
calculation, not a claim about the present FIB source.

**Scope 9.5 (What the triplet result does and does not establish).** If a
future source-level bridge identifies three local FIB channels with the
equivariant contract (9.1), Theorems 9.3–9.4 show that exact or approximate
boundary maintenance should count complete three-component response groups.
They do not supply that bridge, a native $SO(3)$ action, a metric, transport
closure, a Green kernel, or a physical dimension theorem. Under the current
DEV assumptions, the established content remains finite response
localization and its square-residual detection; the triplet conclusion is
conditional on the separately stated interface.

## 10. Finite path-family composition and shared triplet modes

Section 9 treats one finite list of measurements as one response map. A
recursive source normally supplies several declared paths, and those paths
can probe the same hidden mode. The correct capacity is therefore computed
after taking their joint Gram operator, rather than by adding the ranks of the
individual path maps.

**Definition 10.1 (Finite equivariant path family).** Let $\mathcal W$ be a
finite set of declared paths. For every $w\in\mathcal W$, let

$$
\mathscr R_w:\mathcal V\longrightarrow\mathcal Y_w,
\qquad
G_w=\mathscr R_w^{\mathsf T}\mathscr R_w,
$$

and suppose that each path has the same source rotation action and an
orthogonal output action:

$$
\mathscr R_w(I_m\otimes Q)=W_{w,Q}\mathscr R_w,\qquad Q\in SO(3).
\tag{10.1}
$$

Put

$$
\mathscr R_{\mathcal W}v=(\mathscr R_wv)_{w\in\mathcal W},\qquad
\mathcal Y_{\mathcal W}=\bigoplus_{w\in\mathcal W}\mathcal Y_w.
$$

The direct-sum output carries the block-diagonal orthogonal action
$W_{\mathcal W,Q}=\bigoplus_wW_{w,Q}$.

**Theorem 10.2 (Joint path Gram and exact capacity).** If

$$
G_w=A_w\otimes I_3,\qquad A_w\succeq0,
$$

for every $w\in\mathcal W$, then

$$
\boxed{
G_{\mathcal W}:=\mathscr R_{\mathcal W}^{\mathsf T}\mathscr R_{\mathcal W}
 =A_{\mathcal W}\otimes I_3,\qquad
A_{\mathcal W}:=\sum_{w\in\mathcal W}A_w.
}
\tag{10.2}
$$

Consequently, in the same linear-decoder sense as Theorem 9.3, the exact
linear boundary capacity of the joint path family is

$$
\boxed{
\operatorname{rank}\mathscr R_{\mathcal W}
 =3\operatorname{rank}A_{\mathcal W}.
}
\tag{10.3}
$$

If one path family is enlarged from $\mathcal W$ to
$\mathcal W\cup\{u\}$, its exact additional capacity is

$$
\boxed{
3\bigl(\operatorname{rank}(A_{\mathcal W}+A_u)
       -\operatorname{rank}A_{\mathcal W}\bigr),
}
$$

which can be zero even when $\mathscr R_u$ has positive rank.

**Proof.** The joint map is a direct sum, so

$$
G_{\mathcal W}=\sum_{w\in\mathcal W}G_w
 =\left(\sum_{w\in\mathcal W}A_w\right)\otimes I_3.
$$

The rank identity for a Kronecker product gives (10.3). The last formula is
the difference of the two joint ranks. Since the summands are positive
semidefinite, adding a path cannot decrease the rank, but it need not add a
new multiplicity direction. $\square$

This gives a precise distinction between a new path and a new response mode.
For example, with two multiplicity coordinates,

$$
A_1=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
A_2=\begin{pmatrix}1&0\\0&0\end{pmatrix},
$$

each path has rank-three response, but their joint family still has capacity
$3$. In contrast, replacing $A_2$ by

$$
\begin{pmatrix}0&0\\0&1\end{pmatrix}
$$

gives joint capacity $6$. The distinction is invisible to a count that adds
the individual ranks.

**Corollary 10.3 (Finite-precision joint selection).** Under the centered
whitened source law and the equivariant orthogonal compression class of
Theorem 9.4, let

$$
\lambda_1^{\mathcal W}\ge\cdots\ge\lambda_m^{\mathcal W}\ge0
$$

be the complete spectrum of $A_{\mathcal W}$. Retaining $r$ complete
three-component multiplicity groups has minimum joint response error

$$
\boxed{
3\sum_{i=r+1}^{m}\lambda_i^{\mathcal W},\qquad 0\le r\le m.
}
\tag{10.4}
$$

Thus path addition changes the finite-precision budget through the spectrum of
the summed Gram matrix, not through a separate per-path dimension count.

**Scope 10.4.** The result is finite: $\mathcal W$ is finite, all maps share
one source and one $SO(3)$ action, and the source moments and projection class
are those explicitly stated in Theorem 9.4. An infinite path closure requires
its own operator convergence and summability hypotheses. The theorem still
does not establish that the FIB source has this rotation action, that its
paths are metric transports, or that the multiplicity rank is an ambient
space dimension.

**Scope clarification 10.5.** The finite path result uses the interface
hypothesis (9.1), together with the centered/whitened source and
orthogonal-projection assumptions of Theorem 9.4. These are the assumptions
that make the joint response calculation conditional; they do not identify
the FIB source with an $SO(3)$ representation or with a physical ambient
space.

## 10.99 追加锚（本行以下为增补区）

## 11. Source-level finite-rank certificate

Sections 9–10 leave the rotation interface explicit. A separate finite
certificate can connect a predictive-dimension claim to actual FIB sources
without asserting that the native source already carries that interface.

**Definition 11.1 (Affine response minor).** Let $S$ be a source set, let
$p_1,p_2,p_3$ be continuations that are legal for every source under
consideration, and let $y$ be a scalar readout. For sources
$s_0,s_1,s_2,s_3\in S$, define

$$
M_{ij}=y(T_{p_i}s_j)-y(T_{p_i}s_0),
\qquad 1\le i,j\le3.
\tag{11.1}
$$

An affine predictive boundary of dimension $k$ for these responses is a map
$z:S\to\mathbb R^k$ for which, for each $i$, there are $a_i\in\mathbb R$ and
$\ell_i\in(\mathbb R^k)^*$ satisfying

$$
y(T_{p_i}s)=a_i+\ell_i(z(s))
\qquad\text{for every }s\in S.
\tag{11.2}
$$

**Theorem 11.2 (Finite minor lower bound).** If an affine predictive boundary
as in Definition 11.1 exists and

$$
\det M\ne0,
\tag{11.3}
$$

then $k\ge3$. If a three-dimensional affine boundary exists, the minimum
dimension for this response task is therefore exactly three.

**Proof.** Let $Z$ be the $k\times3$ matrix whose $j$-th column is
$z(s_j)-z(s_0)$, and let $L$ be the $3\times k$ matrix whose $i$-th row is
$\ell_i$. Subtracting the $s_0$ response in (11.2) gives

$$
M=LZ.
$$

Thus $3=\operatorname{rank}M\le\operatorname{rank}Z\le k$. The last
statement follows by comparing with the supplied three-dimensional
realization. $\square$

The minor condition is a source-and-task statement: it uses the same actual
sources in every row and the same legal continuation family in every column.
It cannot be replaced by three unrelated response ranks from different
source domains.

**Proposition 11.3 (A source-compatible FIB witness).** Put

$$
q(\alpha)=e_1,\qquad q(\beta)=e_2,
$$

$$
q(\langle s,t\rangle)=q(s)\times q(t),
\qquad q(\rho t)=Rq(t),
$$

where

$$
R=
\begin{pmatrix}
0&0&-1\\
1&0&0\\
0&-1&0
\end{pmatrix}\in SO(3).
$$

Using the FIB recursion
$\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle$ and the identity
$R(u\times v)=(Ru)\times(Rv)$, these clauses are compatible. Define the
source readout by

$$
y(s)=e_1^{\mathsf T}q(s);
$$

equivalently, the vector readout is $\widetilde y(v)=e_1^{\mathsf T}v$ and
$y=\widetilde y\circ q$. Take sources

$$
s_0=\langle\alpha,\alpha\rangle,
\quad s_1=\alpha,
\quad s_2=\beta,
\quad s_3=\langle\beta,\alpha\rangle,
$$

and continuations $p_1=\varepsilon$, $p_2=\rho$, $p_3=\rho^2$. They are
all legal on these FIB terms. Since

$$
q(s_0)=0,
\quad q(s_1)=e_1,
\quad q(s_2)=e_2,
\quad q(s_3)=-e_3,
$$

the response minor is

$$
M=
\begin{pmatrix}
1&0&0\\
0&0&1\\
0&1&0
\end{pmatrix},
\qquad
\det M=-1.
\tag{11.4}
$$

The map $q$ itself is a three-dimensional affine predictive boundary for
this finite response family, so Theorem 11.2 makes its dimension minimal.

This is a finite source-compatible continuation certificate, not a native
closed-loop holonomy result: for example, $\rho^3\alpha\ne\alpha$ as FIB
terms. Restricting the source set or changing the readout can change the
minor rank. The witness therefore supplies the missing source-level
instantiation for this task only; it does not establish a native $SO(3)$
action, metric transport, or physical ambient dimension for FIB.

## 11.99 追加锚（本行以下为增补区）

## 12. The common-realization gate

The joint Gram construction in Section 10 has a source-level prerequisite
that is easy to lose under conditioning. A jointly realized path family
consists of one source set $S$, one state map $z:S\to\mathcal V$, and one
legal continuation/readout contract such that every path response factors
through that same $z$. If a path uses a separately chosen state map after
conditioning on a complement $\eta$, a joint lift to one $z$ must be supplied
before its Gram operator can be added to the other paths.

**Definition 12.1 (Joint-realization gate).** A collection of finite
responses $\{\mathscr R_w\}_{w\in\mathcal W}$ passes the gate when there are
a single source domain $S$, a single boundary map $z:S\to\mathcal V$, and
linear maps $L_w$ such that

$$
\mathscr R_w=L_w\circ z
\qquad(w\in\mathcal W),
\tag{12.1}
$$

with all $L_w$ using the same source coordinates and the same declared
continuation domain. The maps may have different output spaces, but their
inputs are one common realized state.

**Proposition 12.2 (Independent local fits do not pass the gate).** Local
conditional minimizers do not by themselves establish (12.1). In particular,
the stationary common-matrix comparison law in the latest
[DEV global/local rank result](FIB_LEGAL_EDGE_LOAD_GLOBAL_LOCAL_RANK_COMPATIBILITY_AND_RESET_VARIANCE_OBSTRUCTION.md)
has, for every fixed block length $m$, independently minimized
conditional defects whose total tends to zero, while every one global
rank-two candidate for that same family obeys the following bound. For the
same stationary law $P$ and its marginals $\mu_n=P_{[1,n]}$, with $N=2$,
$n\ge5$, and $(n-1)\Delta\ge8$, where $v>0$ and $\Delta>0$ are the constants
defined in Theorem 5.1 of the cited result,

$$
\mathscr R_{2,n}(\mu_n)
\ge
(n-4)\left[
v-2\exp\!\left(-\frac{(n-1)\Delta^2}{64}\right)
\right],
\qquad v>0.
\tag{12.2}
$$

Thus those local minimizers cannot be slices of a common global candidate in
the same rank-two family. Consequently they cannot be used as the individual
summands of a joint response Gram operator without an additional common lift.

**Proof.** The lower bound and the vanishing fixed-block sums are the two
conclusions of the cited comparison law. If the independently selected
conditional minimizers had a common lift satisfying the same global rank-two
constraint, that lift would be an admissible global candidate and would
inherit the vanishing total discrepancy, contradicting (12.2). The failure is
therefore a failure of joint realization, not a failure of either local
conditional calculation. $\square$

This proposition is an obstruction to an inference, not a claim that the
comparison law itself satisfies the $SO(3)$ interface of Section 9. It says
that even before asking for three equivariant channels, one must preserve the
common source, continuation legality, and cross-path correlations. A
three-component local response can remain efficient while the global boundary
requires additional memory or multiplicity to represent the same source.

## 12.99 追加锚（本行以下为增补区）

## 13. Spectral decimation is not an ambient dimension

The latest DEV also contains an exact Riesz/CMV decimation package. Its
relevant facts are spectral: the moment form makes Laurent monomials with
different residues modulo four orthogonal, the exponent map

$$
J(T^i)=T^{4i}
\tag{13.1}
$$

is an isometry between the corresponding moment forms, and the associated
projection norms agree across the scale-four replacement. These facts
describe a graded spectral address, not four local spatial axes.

**Definition 13.1 (Finite residue sectors).** For a finite Laurent-polynomial
window, let

$$
\mathcal P_r
=\operatorname{span}\{T^i:i\equiv r\pmod4\},
\qquad r\in\{0,1,2,3\}.
\tag{13.2}
$$

The DEV residue-orthogonality theorem says that distinct $\mathcal P_r$ are
orthogonal for the Riesz moment form. Every finite Laurent polynomial is the
sum of its four residue components, so this is an orthogonal sector
decomposition of the finite spectral window. Equation (13.1) transports the
zero-residue address under decimation; it does not identify the residue label
with a coordinate direction.

**Proposition 13.2 (Sector count and response rank are different quantities).**
Let a finite response map respect a direct-sum decomposition

$$
\mathcal V=\bigoplus_{r=0}^{3}\mathcal V_r,
\qquad
\mathcal Y=\bigoplus_{r=0}^{3}\mathcal Y_r,
\qquad
\mathscr R_r:\mathcal V_r\to\mathcal Y_r,
\qquad
\mathscr R=\bigoplus_{r=0}^{3}\mathscr R_r.
\tag{13.3}
$$

Then

$$
\boxed{
\operatorname{rank}\mathscr R
=\sum_{r=0}^{3}\operatorname{rank}\mathscr R_r.
}
\tag{13.4}
$$

The four-sector index therefore gives no value for
$\operatorname{rank}\mathscr R$ without separate information about the four
sector maps.

**Proof.** In bases adapted to the two direct sums, $\mathscr R$ is block
diagonal. Its image is the direct sum of the four block images inside the
mutually disjoint summands $\mathcal Y_r$, so the dimensions add. $\square$

Consequently, scale-four self-similarity can coexist with a one-component
sector, a three-component local response, or any larger multiplicity. The
number four records a decimation and residue structure; it does not prove
$d=4$, $d=3$, or an $SO(3)$ action. To obtain a three-dimensional local
claim, one still needs a source-level certificate such as Proposition 11.3
or an independently supplied equivariant interface from Section 9.

This distinction also limits how the new Riesz results can be transferred to
FIB. The exact DEV statements establish the spectral identities for their
declared moment forms and walks. They do not by themselves provide a FIB
source map, a common legal continuation family, a physical metric, or a
transport-to-space correspondence. Under the common-realization gate of
Section 12, they can supply a graded response decomposition only after such
a bridge is constructed.

## 13.99 追加锚（本行以下为增补区）
