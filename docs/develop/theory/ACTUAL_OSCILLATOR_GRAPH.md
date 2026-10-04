# Actual oscillator differential graph

## 1. Gaussian and differential tests

**Definition 1.1 (Schwartz Gaussian).** For a real inner product space $V$,
put $G_V(x)=\exp(-\|x\|^2/2)$. A Schwartz map is a smooth function whose
iterated real Fréchet derivatives decay faster than every inverse polynomial.

**Theorem 1.2 (Gaussian Schwartz existence).** For every real normed inner
product space $V$, without a completeness or finite-dimensionality assumption,
there exists $u\in\mathcal S(V,\mathbb R)$ such that
$u(x)=\exp(-\|x\|^2/2)$ for every $x\in V$.

*Proof.* The construction of Gregory J. Loges in PhysLean,
`Physlib/Mathematics/InnerProductSpace/Gaussian.lean`, revision
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142`, bounds the $n$th derivatives of
$\langle x,x\rangle$ by $(2+\|x\|^2)^n$. The chain rule bounds the $n$th
derivative of $G_V$ by $n!G_V(x)(2+\|x\|^2)^n$. For every $k,n$, exponential
decay and a maximum on a compact interval bound
$t^{k/2}(2+t)^n\exp(-t/2)$ on $t\ge0$. Taking $t=\|x\|^2$ gives the
Schwartz estimates. This is the cited source construction.

**Definition 1.3 (physical differential expression).** Let $d\in\mathbb N$,
$V=\mathbb R^d$ with its Euclidean norm and Lebesgue volume, and let
$\hbar>0$, $m_j>0$, $\omega_j>0$ for every $j<d$. Write
$\ell_j=\sqrt{\hbar/(m_j\omega_j)}$ and
$$
H_0\varphi=\sum_{j<d}\left[-\frac{\hbar^2}{2m_j}\partial_j^2\varphi
+\frac{m_j\omega_j^2}{2}x_j^2\varphi\right].
$$
The normalized physical Hermite functions are
$$
\Phi_\alpha(x)=\prod_{j<d}
\frac{\operatorname{He}_{\alpha_j}(\sqrt2 x_j/\ell_j)
\exp(-x_j^2/(2\ell_j^2))}
{\sqrt{\sqrt\pi\,\ell_j\,\alpha_j!}},\qquad
E_\alpha=\sum_{j<d}\hbar\omega_j(\alpha_j+1/2).
$$
Here $\operatorname{He}_n$ is the probabilists' Hermite polynomial,
$\operatorname{He}_0=1$ and
$\operatorname{He}_{n+1}=X\operatorname{He}_n-\operatorname{He}'_n$.
Empty sums and products have their usual values, including $d=0$.

**Theorem 1.4 (Hermite lowering).** For every $n\in\mathbb N$, the real
probabilists' Hermite polynomial satisfies
$\operatorname{He}'_{n+1}=(n+1)\operatorname{He}_n$.

*Proof.* Leonardo Pedro's Timepiece,
`BookProof/ChapterHermiteFunctions.lean`, revision
`61595bca99e3b8d8b8df51a2c3043b64597e24f9`, proves this by induction.
Differentiating the defining recursion gives the successor step; substitution
of the induction hypothesis and the recursion reduces it to the claimed
multiple of $\operatorname{He}_{n+1}$.

## 2. Closure and compact tests

**Definition 2.1 (actual Hilbert space and weak relation).** Set
$\mathcal H=L^2(V,\mathbb C;\mathrm{volume})$, and let $J$ be the actual
Schwartz embedding into this space. Let $S(J\varphi)=JH_0\varphi$ on every
Schwartz map and let $T$ be its restriction to the finite physical Hermite
span. The compact-test relation $\mathrm{Weak}(f,g)$ means
$\langle JH_0\psi,f\rangle=\langle J\psi,g\rangle$ for every smooth compactly
supported $\psi$. This tests the sum $H_0\psi$; no separate square-integrability
of the potential or second-derivative terms is assumed for $f$ or $g$.

**Theorem-form 2.2 (compact cutoff graph limits).** For all parameters of
Definition 1.3 and every Schwartz map $\varphi$, a fixed smooth scalar bump
$\chi$, equal to one on $[-1,1]$ and supported in $[-2,2]$, gives
$\theta_N(x)=\prod_{j<d}\chi(x_j/(N+1))$ with
$$
J(\theta_N\varphi)\longrightarrow J\varphi,\qquad
JH_0(\theta_N\varphi)\longrightarrow JH_0\varphi
$$
in $\mathcal H$. The products are smooth and compactly supported, also for
$d=0$. The required commutator is
$$
H_0(\theta_N\varphi)-\theta_N H_0\varphi
=-\sum_{j<d}\frac{\hbar^2}{2m_j}
\left[2(\partial_j\theta_N)(\partial_j\varphi)
+(\partial_j^2\theta_N)\varphi\right].
$$

*Derivation to be established.* Product and chain rules give first and second
cutoff derivatives bounded by $C_1/(N+1)$ and $C_2/(N+1)^2$. Squared dominated
convergence controls $(\theta_N-1)u$ for each square-integrable Schwartz $u$.
The finite sum in the displayed commutator then gives the simultaneous limits.

**Theorem-form 2.3 (full actual graph objective).** For every dimension and
all positive parameters of Definition 1.3, the actual operator $T$ is closable.
For its genuine closure $K=\overline T$ and arbitrary $f,g\in\mathcal H$,
$$
\mathrm{Weak}(f,g)\quad\Longleftrightarrow\quad
(f,g)\in\overline{\operatorname{graph}T}\quad\Longleftrightarrow\quad
\forall\alpha,\ c_\alpha(g)=E_\alpha c_\alpha(f),
\qquad c_\alpha(f)=\langle J\Phi_\alpha,f\rangle.
$$
The weighted domain is $\{f:(E_\alpha c_\alpha(f))_\alpha\in\ell^2\}$.
Moreover $S\subseteq K$, $S$ is closable, $\overline S=K$, and $K$ is
self-adjoint and nonnegative. Every graph point is approximated by finite
Hermite sums with simultaneous convergence of the vectors and their actual
$H_0$ images, using the same finite sets for both sums. No division by an
energy is used. For $d=0$, volume is the unit Dirac measure, $\Phi=1$, $E=0$,
$K=0$ on the whole space, and the weak relation is equivalent to $g=0$.

*Derivation to be established.* The physical family's orthonormality and
totality are a separate prerequisite. The compact cutoff limits extend weak
tests to each physical Hermite function. Real-bilinear integration by parts
twice gives all-Schwartz symmetry and the coefficient identity for $H_0$.
Hilbert expansion with the same finite coefficient sets for a vector and its
image gives the actual closed graph. Resolvents at $\pm i$, rather than at
zero energy, yield self-adjointness; nonnegative energies yield nonnegativity.

## 追加锚（本行以下为增补区）




## 3. Real eigenbasis closure

**Theorem 3.1 (real eigenbasis closure).** Let $\mathcal H$ be a complete
complex inner product space and $e:I\to\mathcal H$ a Hilbert basis, with no
restriction on the index type $I$. Let $T$ be a complex linear partial
operator whose domain is exactly the algebraic span of $e(I)$, and let
$\lambda:I\to\mathbb R$. If $Te_i=\lambda_i e_i$ for every $i$, then $T$ is
closable and its genuine closure is self-adjoint. Zero eigenvalues and
repeated eigenvalues are allowed.

*Proof.* Tom Ole Diem's PhysLean source,
`PhyslibAlpha/AlgebraicFramework/HilbertSpace/Unbounded/RealAnalytic.lean`,
revision `b9043cc548ef6d63a28454cf3a57fb12a0c2e142`, constructs the resolvent
coefficients $c_i/(\lambda_i-\zeta)$ for $\zeta=\pm i$. Their square sum is
bounded by that of $c$, because $|\lambda_i-\zeta|\ge1$. The same finite sums
converge in both graph coordinates. Finite-combination symmetry and the
closed adjoint first give genuine closability. The two surjective resolvents
of the closure identify it with its adjoint. The supporting unbounded-operator
arguments are due to Adam Bornemann and Gregory J. Loges in
`Physlib/QuantumMechanics/Operators/Unbounded.lean` at the same revision.

## 追加锚（本行以下为增补区）


## 4. Schwartz cutoff graph convergence

**Theorem 4.1 (scaled Schwartz cutoff).** Let $d\in\mathbb N$,
$V=\operatorname{EuclideanSpace}_{\mathbb R}(\operatorname{Fin}d)$ and
$\mathcal H=L^2(V,\mathbb C;\mathrm{volume})$. Let $a,b:\operatorname{Fin}d\to\mathbb R$
be arbitrary, and let $\varphi\in\mathcal S(V,\mathbb C)$. For a real Schwartz
function $\chi$ with compact support, $\chi(0)=1$ and $|\chi(x)|\le1$ for every $x$,
put $R_N=N+1$, $\theta_N(x)=\chi(R_N^{-1}x)$ and
$\psi_N=\theta_N\varphi$. Then $\psi_N$ is smooth and compactly supported and
$$
J\psi_N\longrightarrow J\varphi,\qquad
JH_{a,b}\psi_N\longrightarrow JH_{a,b}\varphi,
\quad
H_{a,b}u=\sum_{j<d}[-a_j\partial_j^2u+b_jx_j^2u]
$$
in the actual complex Lebesgue $L^2$ space. The dimension may be zero, and no
sign restriction on $a,b$ is required. With $a_j=\hbar^2/(2m_j)$ and
$b_j=m_j\omega_j^2/2$, this is convergence for the physical differential sum.

*Proof.* Scaling multiplies each first cutoff derivative by $R_N^{-1}$ and
each second derivative by $R_N^{-2}$. Compact support makes their unscaled
values bounded. The second-derivative product identity expresses the graph
error as a finite sum of cutoff errors against Schwartz functions.
Squared dominated convergence gives the simultaneous $L^2$ limits.
This adapts the cutoff, product and dominated-convergence method of
`W21_approximation` in the frozen trureturing
`D5/S3/Weil/ZetaPntBase/Sobolev.lean` to the actual multidimensional $L^2$
graph norm. That supplier's original one-dimensional norm uses $L^1$ and
is not the present statement.

## 追加锚（本行以下为增补区）

## 5. Compact weak tests and the Schwartz adjoint

**Theorem 5.1 (actual compact-test adjoint graph).** For every natural
dimension $d$ and arbitrary real coordinate coefficients $a,b$, let
$H_{a,b}$ be the differential sum of Theorem 4.1, let $J$ be the actual
complex Lebesgue $L^2$ embedding and define the partial linear operator
$S(J\varphi)=JH_{a,b}\varphi$ on the range of all complex Schwartz functions.
Then $S$ has dense domain, is symmetric and is closable. For arbitrary
$f,g\in L^2(V,\mathbb C;\mathrm{volume})$,
$$
\bigl[\forall\psi\in\mathcal S(V,\mathbb C),\quad
\operatorname{supp}\psi\text{ compact}\ \Longrightarrow\
\langle JH_{a,b}\psi,f\rangle=\langle J\psi,g\rangle\bigr]
\quad\Longleftrightarrow\quad (f,g)\in\operatorname{graph}(S^*).
$$
No separate derivative or potential integrability is imposed on $f$ or $g$,
and the dimension may be zero.

*Proof.* Choose a smooth compact bump equal to one near zero and bounded
between zero and one. The simultaneous limits in Theorem 4.1 and continuity
of the Hilbert inner product extend compact tests to every Schwartz test.
The dense embedding identifies this identity with the actual partial-map
adjoint graph. Real-bilinear integration by parts twice, with the pairing
$\overline z w$, gives symmetry of the second derivatives. Multiplication
by each real quadratic potential is symmetric. The adjoint is closed and
contains $S$, so $S$ is closable.

## 追加锚（本行以下为增补区）

## 6. Weighted coefficients and a simultaneous finite core

**Theorem 6.1 (actual eigenbasis graph and core).** Let $\mathcal H$ be a
complete complex inner product space, let $e:I\to\mathcal H$ be a Hilbert
basis with arbitrary index type $I$, and let $T$ be a complex linear partial
operator with domain exactly $\operatorname{span}_{\mathbb C}e(I)$.
For arbitrary real $\lambda:I\to\mathbb R$, assume $Te_i=\lambda_i e_i$
for every $i$. Write $K=\overline T$ for the genuine operator closure and
$c_i(x)=\langle e_i,x\rangle$. For every $x,y\in\mathcal H$,
$$
(x,y)\in\operatorname{graph}K
\quad\Longleftrightarrow\quad
\forall i\in I,\ c_i(y)=\lambda_i c_i(x).
$$
Whenever these equivalent conditions hold, the finite sums
$x_F=\sum_{i\in F}c_i(x)e_i$, directed by inclusion of finite subsets of $I$,
belong to the actual domain of $T$ and satisfy
$$
x_F\longrightarrow x,\qquad
Tx_F=\sum_{i\in F}\lambda_i c_i(x)e_i\longrightarrow y.
$$
In particular, $x\in\operatorname{dom}K$ if and only if
$(\lambda_i c_i(x))_{i\in I}\in\ell^2(I,\mathbb C)$.
Zero and repeated eigenvalues are included; no division by $\lambda_i$ occurs.

*Proof.* Theorem 3.1 supplies closability and the self-adjoint genuine closure.
Symmetry paired with each eigenvector gives the coefficient identity on its
graph. Conversely, the Hilbert expansions of $x$ and $y$ converge along the
same finite subsets. The coefficient identity places each pair of finite
sums in the actual graph of $T$, hence their limit in its graph closure.
The Hilbert-basis isometry identifies square-summable weighted coefficients
with a unique image vector and proves the domain characterization.

## 追加锚（本行以下为增补区）


## 7. Physical Hermite differential tests

**Theorem 7.1 (physical Hermite Schwartz and cutoff tests).** For every natural
$d$, every $\hbar>0$, every family $m_j>0$, $\omega_j>0$ indexed by $j<d$,
and every $\alpha:\{0,\ldots,d-1\}\to\mathbb N$, there exists a complex
Schwartz function $\varphi_\alpha$ on the Euclidean space $V$ with
$\varphi_\alpha(x)=\Phi_\alpha(x)$ for every $x$, where $\Phi_\alpha$ is the
physical product in Definition 1.3. Its actual differential expression satisfies
$H_0\varphi_\alpha=E_\alpha\varphi_\alpha$ as an equality of Schwartz functions.
There are compactly supported smooth Schwartz functions $\psi_N$ such that,
for the actual complex Lebesgue $L^2$ embedding $J$,
$$
J\psi_N\longrightarrow J\varphi_\alpha,\qquad
JH_0\psi_N\longrightarrow E_\alpha J\varphi_\alpha.
$$
The construction includes $d=0$, when $\Phi_\alpha=1$ and $E_\alpha=0$.
It assumes neither orthonormality nor totality of the physical family.

*Construction.* Compose the standard Schwartz Gaussian with the invertible
coordinate map $x\mapsto(x_j/\ell_j)_j$ and multiply by the normalized tensor
Hermite polynomial. The lowering identity gives the polynomial differential
equation. Differentiating each scaled polynomial times half Gaussian twice
and multiplying by the other coordinate factors gives the stated physical
energy. The differentiation argument is from Leonardo Pedro's Timepiece,
`BookProof/ChapterHermiteFunctions.lean`, revision
`61595bca99e3b8d8b8df51a2c3043b64597e24f9`; its one-dimensional bindings are
used within the physical construction. Apply a smooth compact bump at scales
$N+1$ and the simultaneous cutoff limits of Theorem 4.1.


## 追加锚（本行以下为增补区）

## 8. Conditional physical closure and nonnegativity

**Theorem 8.1 (actual physical graph, conditional on the physical basis).**
For every natural dimension $d$, positive $\hbar$, positive coordinate masses
$m_j$ and frequencies $\omega_j$, suppose that $e$ is a complex Hilbert basis
of the actual Lebesgue $L^2(V,\mathbb C)$ and that each $e_\alpha$ is exactly
the $L^2$ class of a Schwartz function $\varphi_\alpha$ whose pointwise
value is the physical function $\Phi_\alpha$ of Definition 1.3.
Let $S$ be the actual differential operator on all Schwartz classes from
Theorem 5.1, $C=\operatorname{span}_{\mathbb C}e(I)$, $T=S|_C$, and
$K=\overline T$ the genuine operator closure. Then $S\le K$, $S$ is
closable, $\overline S=K=S^*$, $K$ is self-adjoint and closed, and $C$
is a core of $K$. For every $f,g$ in the actual Hilbert space,
$$
\mathrm{Weak}(f,g)\iff(f,g)\in\operatorname{graph}K
\iff\forall\alpha,\ \langle e_\alpha,g\rangle
=E_\alpha\langle e_\alpha,f\rangle.
$$
The domain of $K$ is exactly the set of vectors whose weighted coefficients
$(E_\alpha\langle e_\alpha,f\rangle)_\alpha$ belong to $\ell^2$.
For each graph pair $(f,g)$, finite physical Hermite sums indexed by the
same finite set converge simultaneously to $f$ and, under $T$, to $g$.
For every $u\in\operatorname{dom}K$,
$\operatorname{Re}\langle u,Ku\rangle\ge0$.
The empty coordinate sum gives $E_\alpha=0$ in dimension zero; no energy
division and no separate nonsmooth derivative or potential $L^2$ hypothesis
is used. The assertion remains conditional on the exact physical Hilbert
basis input; it does not prove physical orthonormality or totality.

*Proof.* Theorem 7.1 supplies the actual differential eigenaction of the
pointwise-identical Schwartz representatives. The finite physical restriction
therefore satisfies Theorems 3.1 and 6.1. Schwartz symmetry pairs every
vector in $S^*$ with each physical eigenfunction and gives the weighted
coefficient identity, hence $S^*\le K$. The closed adjoint contains $S$
and $T$, so it contains $K$ as well. Closure monotonicity then identifies
the Schwartz closure with $K$. The compact-test equivalence follows from
Theorem 5.1, and the finite core and domain characterization from Theorem 6.1.
On each simultaneous finite graph approximant, orthonormality expresses the
real quadratic form as $\sum_{\alpha\in F} E_\alpha
|\langle e_\alpha,u\rangle|^2\ge0$. Continuity of the inner product
and closedness of the nonnegative real half-line pass this inequality to
the genuine graph limit.
