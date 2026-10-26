# FIB atomic biased boundary spectral counting

## 1. The inherited source, trace and comparison clock

**Definition 1.1 (the fixed source-specific operator).**
Write IV for [Boundary Geometry IV](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md).
Retain its Definitions 92.1–92.2 and 98.1 and Theorems 98.2, 99.1,
111.2–111.4, with all their original objects. In particular,

$$
\begin{gathered}
T_0=\alpha,\quad T_1=\beta,\quad
T_n=\langle T_{n-1},T_{n-2}\rangle,\quad N_n=2F_{n+1}-1,\\
\mathscr H=\ell^2(\{L,R\}^+),\qquad
\Omega=\{L,R\}^{\mathbb N},\qquad \mathscr G=L^2(\Omega,M),\\
\varphi=(1+\sqrt5)/2,\quad a=\varphi^{-1},\quad b=\varphi^{-2},
\quad a+b=1,\\
\sigma(p)=\#_L(p)+2\#_R(p),\qquad
m(p)=M([p])=\varphi^{-\sigma(p)},\qquad m(\varnothing)=1.
\end{gathered}
\tag{1.1}
$$

Here $F_j$ are the Fibonacci numbers of IV, Definition 92.2;
$\sigma$ denotes the address weight called $s(p)$ in IV, §98.
The scalar $s$ below remains comparison time, with finite semigroup
$S_n(s)=e^{-N_nsL_n}$. Each $L_n$ is the closed counting-measure
unit-edge occurrence Laplacian, with no root killing term. Every
occurrence, including interior vertices and the root, has mass $1/N_n$.
For a reached address $p$, its entire descendant source is
$T_{n-\sigma(p)}$, and its descendant mass is exactly
$N_{n-\sigma(p)}/N_n$; reachability additionally requires
$n-\sigma(p^-)\ge2$ for $p\ne\varnothing$ (IV, (98.4)).
Its limit is the $m(p)$ in (1.1).

The compact map $J:\mathscr H\to\mathscr G$ is the bounded extension
of $Jz=\sum_{p\preceq\omega}z_p$ on finitely supported increments.
Set $\mathscr G_0=\mathbf1^\perp$, let
$\Pi:\mathscr G\to\mathscr G_0$ be $\Pi F=F-\int F\,dM$, and regard
$C=\Pi J$ as a map $\mathscr H\to\mathscr G_0$. Its covariance is
$`\Sigma=C^*C=J^*J-v\otimes v`$, with $`v=J^*\mathbf1`$.
Put $\mathscr K=(\ker\Sigma)^\perp$ and $\Sigma_{\mathscr K}=\Sigma|_{\mathscr K}$.
The domain and energy are exactly IV, (111.2):

$$
\begin{aligned}
\mathcal D&=\{c\mathbf1+Jz:c\in\mathbb R,\ z\in\mathscr H\},\\
\mathcal E(F)&=\inf_{F=c\mathbf1+Jz}\|z\|_{\mathscr H}^2.
\end{aligned}
\tag{1.2}
$$

Thus the root value is free and the extension energy is the sum of
squared increments on the original unit-edge address tree. Let $H$
be the self-adjoint operator of this closed form. The least-norm
increment $z_F\in\mathscr K$ satisfies $Cz_F=\Pi F$ and
$\mathcal E(F)=\|z_F\|^2$. These are the existing form and operator,
not a new construction.

For the unitary $W:\mathscr K\to\mathscr G_0$ of IV, (111.8),

$$
\begin{gathered}
C|_{\mathscr K}=W\Sigma_{\mathscr K}^{1/2},\qquad
H|_{\mathscr G_0}=W\Sigma_{\mathscr K}^{-1}W^*,\qquad H\mathbf1=0,\\
\mathcal D\cap\mathscr G_0=W\operatorname{ran}\Sigma_{\mathscr K}^{1/2},
\qquad \operatorname{Dom}(H)\cap\mathscr G_0
       =W\operatorname{ran}\Sigma_{\mathscr K}.
\end{gathered}
\tag{1.3}
$$

In particular the unitary and the inverse act only on their indicated
spaces. The possibly large edge kernel of $\Sigma$ is not a family of
boundary zero modes: the kernel of $H$ is precisely
$\mathbb R\mathbf1$ (IV, Theorem 111.2).
The equal-split vector $q_p=2^{-|p|}$ of IV, Theorem 99.1 supplies
$Jq=\mathbf1$ and the constant-trace constraint; it does not change
the biased law $M$ into the fair harmonic law.

**Definition 1.2 (multiplicity and global counting).**
List the positive eigenvalues of $H$, with multiplicity, as
$0<\lambda_1\le\lambda_2\le\cdots$. Their existence, exhaustion and
divergence are included in Theorem 2.1. For $\lambda\ge0$ put

$$
N_H^+(\lambda)=\dim\operatorname{ran}\mathbf1_{(0,\lambda]}(H),
\qquad N_H(\lambda)=1+N_H^+(\lambda).
\tag{1.4}
$$

The second count includes the single constant eigenfunction, including
at $\lambda=0$. The first counts eigenvalues equal to the positive
threshold, without requiring a simple spectrum.

## 2. Two-sided counting on the actual biased boundary

**Theorem 2.1 (source-specific linear global counting).**
For the exact $M$, unit-edge free-root form and $H$ of Definition 1.1,
$H$ has compact resolvent, its zero eigenvalue is simple, and its positive
eigenvalues form the infinite sequence in Definition 1.2. Set
$B=2\varphi/b=2\varphi^3$. Then

$$
\begin{aligned}
N_H^+(\lambda)&=0 &&(0\le\lambda<\varphi^{-1}),\\
N_H^+(\lambda)&\le B\lambda &&(\lambda\ge0),\\
N_H^+(\lambda)&\ge b\lambda-1 &&(\lambda>b^{-1}),\\
\frac b2\lambda\le N_H^+(\lambda)&\le B\lambda
                              &&(\lambda\ge2b^{-1}),\\
\frac jB\le\lambda_j&\le\frac j b &&(j\ge1).
\end{aligned}
\tag{2.1}
$$

All bounds concern the same operator; their constants are not asserted
optimal. No simplicity of positive eigenvalues is assumed.

*Proof.* First, IV, (98.5) with $h=0$ gives

$$
\|C\|^2\le\|J\|^2\le\frac a{1-a}=\varphi.
\tag{2.2}
$$

Compactness of $C$ and density of its range in the infinite-dimensional
$\mathscr G_0$ are supplied by IV, §§98 and 111. The spectral theorem for
the positive compact injective operator $\Sigma_{\mathscr K}$ gives
positive eigenvalues $\mu_1\ge\mu_2\ge\cdots\downarrow0$, each of finite
multiplicity, and an orthonormal eigenbasis of $\mathscr K$. It has
infinitely many eigenvalues because $\mathscr G_0$ is infinite-dimensional
and $W$ in (1.3) is unitary. Equation (1.3) makes
$\lambda_j=\mu_j^{-1}$, including multiplicities. It also gives

$$
(H+I)^{-1}
 =P_{\mathbf1}+W\Sigma_{\mathscr K}
                   (I_{\mathscr K}+\Sigma_{\mathscr K})^{-1}W^*
\quad\text{on }\mathbb R\mathbf1\oplus\mathscr G_0,
\tag{2.3}
$$

where the $W$ term acts on $\mathscr G_0$ and is zero on constants.
The first term has rank one and the second is compact, proving compact
resolvent and exhaustion of the spectrum. The inherited zero-energy
statement gives the simple zero mode. From (2.2), $\mu_j\le\varphi$,
proving the first line of (2.1).

For $0<t<1$, let $A_t$ be the first mass crossing along each ray:

$$
A_t=\{p\ne\varnothing:m(p)\le t<m(p^-)\},\qquad k_t=|A_t|.
\tag{2.4}
$$

Equality $m(p)=t$ is a stopping event. Since $m(p)\le a^{|p|}$, all
rays stop by a common finite depth. Thus $A_t$ is a finite prefix-free
set, its cylinders partition $\Omega$, and every one of its masses
obeys

$$
bt<m(p)\le t,\qquad
\sum_{p\in A_t}m(p)=1,\qquad
\frac1t\le k_t<\frac1{bt}.
\tag{2.5}
$$

Indeed a child mass is either $a$ or $b$ times its parent mass, and
$a\ge b>0$. The strict lower inequality follows from $m(p^-)>t$.
This uses the actual masses $a,b$, not masses $1/2,1/2$.

Let $V_t\subset\mathscr G$ be the $k_t$-dimensional space of functions
constant on each $[p]$, $p\in A_t$, and let $Q_t:\mathscr G\to V_t$
be its orthogonal projection:

$$
(Q_tF)|_{[p]}=\frac1{m(p)}\int_{[p]}F\,dM.
\tag{2.6}
$$

It fixes constants and commutes with $\Pi$. Consequently
$Q_t|_{\mathscr G_0}$ has range $V_t\cap\mathscr G_0$, of dimension
$k_t-1$.
For $z\in\mathscr H$, let $z^p\in\mathscr H$ have coordinates
$(z^p)_u=z_{pu}$ for nonempty suffixes $u$. This retains only strict
descendants of $p$. Under the conditional law on $[p]$, the suffix
has exactly law $M$. For finite increments, the path-sum identity is

$$
(Jz)(p\omega)=\sum_{\varnothing\ne u\preceq p}z_u+(Jz^p)(\omega).
\tag{2.7}
$$

For general $z$, approximate by finite increments. Restriction to the
fixed cylinder $[p]$ is bounded from $\mathscr G$ to its conditional
$L^2$ space, with norm at most $m(p)^{-1/2}$; the suffix-coordinate
map is a contraction on $\mathscr H$. Boundedness of $J$ therefore
extends (2.7) in conditional $L^2$. Subtracting the conditional mean
cancels both its prefix constant and the global centering constant.
Thus, on the conditional suffix space,

$$
\begin{aligned}
((I-Q_t)Cz)(p\omega)&=(Cz^p)(\omega),\\
\|(I-Q_t)Cz\|_{\mathscr G}^2
 &=\sum_{p\in A_t}m(p)\|Cz^p\|_{\mathscr G_0}^2\\
 &=\sum_{p\in A_t}m(p)\langle z^p,\Sigma z^p\rangle
 \le\varphi t\sum_{p\in A_t}\|z^p\|^2
 \le\varphi t\|z\|^2.
\end{aligned}
\tag{2.8}
$$

The strict-descendant coordinate sets are pairwise disjoint. Edges at
or above the stopping vertices contribute nothing to these restrictions,
which justifies the final inequality without assigning them a new energy.
In (2.8), $Cz$ is included in $\mathscr G$ before applying $I-Q_t$;
$Cz^p$ lies in the copy of $\mathscr G_0$ on suffixes. The displayed
identification is composition with $\omega\mapsto p\omega$, not an
identification of the conditional and unconditioned measures.

Suppose $\lambda\ge\varphi^{-1}$ and take $t=(2\varphi\lambda)^{-1}$,
so $0<t\le1/2$. The eigenspace of $\Sigma_{\mathscr K}$ for
$\mu\ge1/\lambda$ has dimension $N_H^+(\lambda)$. If this exceeded
$k_t-1$, the map $Q_tC$ on that space would have a nonzero kernel
vector $z$. The spectral theorem and (2.8) would then give

$$
\frac1\lambda\|z\|^2\le\langle z,\Sigma z\rangle
 =\|Cz\|^2=\|(I-Q_t)Cz\|^2
 \le\frac1{2\lambda}\|z\|^2,
\tag{2.9}
$$

a contradiction. Hence
$N_H^+(\lambda)\le k_t-1<(bt)^{-1}=B\lambda$.
Together with the gap below $\varphi^{-1}$ this proves the global
upper bound, including all eigenvalues at the threshold.

For the lower bound, the same cylinder space $V_t$ is contained in
$\mathcal D$: if $F=\sum_{p\in A_t}x_p\mathbf1_{[p]}$, use the actual
increment vector $z=\sum_{p\in A_t}x_p\delta_p$ and root value zero.
It has trace $F$ and energy $\sum x_p^2$. Accordingly, for $F\ne0$,

$$
\|F\|_{\mathscr G}^2=\sum_{p\in A_t}m(p)|x_p|^2
   >bt\sum_{p\in A_t}|x_p|^2,\qquad
\mathcal E(F)\le\sum_{p\in A_t}|x_p|^2
   <\frac1{bt}\|F\|_{\mathscr G}^2.
\tag{2.10}
$$

Minimality of $z_F$ can only improve this bound; no equality between
this chosen extension and the minimizing one is required.
The space $V_t\cap\mathscr G_0$ has dimension $k_t-1$ and obeys the
same estimate. For $\lambda>b^{-1}$, take $t=(b\lambda)^{-1}<1$.
The form version of the min-max principle now gives at least $k_t-1$
positive eigenvalues strictly below $\lambda$. Explicitly, otherwise
the spectral projection onto $(0,\lambda)$ would have a nonzero kernel
on this trial space; a vector in that kernel has spectral support in
$[\lambda,\infty)$ and hence energy at least $\lambda\|F\|^2$,
contradicting (2.10). Therefore

$$
N_H^+(\lambda)\ge k_t-1\ge b\lambda-1.
\tag{2.11}
$$

For $\lambda\ge2/b$ the right side is at least $b\lambda/2$.
Finally $j\le N_H^+(\lambda_j)\le B\lambda_j$ gives the eigenvalue
lower bound. If $\lambda>j/b$, (2.11) gives
$N_H^+(\lambda)>j-1$, so the integer count is at least $j$.
Letting $\lambda\downarrow j/b$ gives $\lambda_j\le j/b$.
This proves (2.1).

The variational and finite-rank arguments are established spectral
methods, not a claim of a new min-max principle: see Gerald Teschl,
[*Mathematical Methods in Quantum Mechanics*, online 2009 edition,
§§4.3–4.4, Theorem 4.10 and its form-domain statement, and Theorem 4.12(i)](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
The new deduction here is the source-specific mass stopping estimate
(2.8), its trial-space companion (2.10), and their application to the
already constructed biased covariance and boundary operator of IV.
These deductions are repo-derived; the cited variational methods are
literature-attested intermediate supplies. $\square$

## 3. Global heat trace, logarithmic growth and covariance ideals

**Theorem 3.1 (actual global spectral consumers).**
For $s>0$ define

$$
Z_H^+(s)=\operatorname{Tr}_{\mathscr G_0}(e^{-sH}|_{\mathscr G_0})
       =\sum_{j\ge1}e^{-s\lambda_j},\qquad
Z_H(s)=1+Z_H^+(s).
\tag{3.1}
$$

These traces are finite, and the constant $B$ of Theorem 2.1 satisfies

$$
\frac b s e^{-s/b}\le Z_H^+(s)\le\frac B s\quad(s>0),
\qquad
\frac b{es}\le Z_H^+(s)\le\frac B s\quad(0<s\le b).
\tag{3.2}
$$

In particular,

$$
\begin{gathered}
\lim_{\lambda\to\infty}\frac{\log N_H^+(\lambda)}{\log\lambda}=1,
\qquad
\lim_{j\to\infty}\frac{\log\lambda_j}{\log j}=1,\\
\lim_{s\downarrow0}\frac{\log Z_H^+(s)}{\log(1/s)}
 =\lim_{s\downarrow0}\frac{\log Z_H(s)}{\log(1/s)}=1.
\end{gathered}
\tag{3.3}
$$

For $r>0$, writing $\mathcal S_r$ for the class of compact operators
whose singular values have summable $r$th powers, one also has

$$
\Sigma\in\mathcal S_r\ \Longleftrightarrow\ r>1,
\qquad
C\in\mathcal S_r\ \Longleftrightarrow\ r>2.
\tag{3.4}
$$

Thus the actual centered edge covariance is Hilbert–Schmidt and is
not trace class, despite its compactness.

*Proof.* For each eigenvalue and $s>0$,
$e^{-s\lambda_j}=s\int_{\lambda_j}^{\infty}e^{-su}\,du$.
Tonelli's theorem, with nonnegative integrands and counting multiplicity,
gives the identity, initially even if the sum were infinite,

$$
Z_H^+(s)=s\int_0^\infty e^{-su}N_H^+(u)\,du.
\tag{3.5}
$$

Theorem 2.1 bounds this by $B/s$, proving finiteness. Its lower bound
$N_H^+(u)\ge bu-1$ for $u>1/b$ gives

$$
Z_H^+(s)\ge s\int_{1/b}^{\infty}(bu-1)e^{-su}\,du
          =\frac b s e^{-s/b}.
\tag{3.6}
$$

For $s\le b$ this is at least $b/(es)$. The bounds in (2.1) and
(3.2), after taking logarithms and dividing by their diverging positive
logarithmic denominators, give (3.3). The addition of the one constant
mode does not alter that limit.

The positive eigenvalues of $\Sigma$ are precisely
$\mu_j=1/\lambda_j$, with the same multiplicities; its other eigenvalues
are zero. From (2.1),

$$
\frac b j\le\mu_j\le\frac B j.
\tag{3.7}
$$

Comparing with the positive series $\sum j^{-r}$ proves the first
assertion of (3.4). Since $C^*C=\Sigma$, the nonzero singular values
of $C$ are $\sqrt{\mu_j}$; the same comparison proves the second.
The Laplace-transform identity and summability comparison are standard
intermediate methods. Equations (3.2)–(3.4) are their repo-derived
consequences for the source-specific $H,C,\Sigma$. $\square$

## 4. The scope of spectral growth and of its reference measures

**Definition 4.1 (global logarithmic exponent and separate bridges).**
For this comparison operator define the global logarithmic heat exponent
by the last limit in (3.3). If a convention calls twice this exponent
a global spectral dimension, its value here is two. This definition
uses the global trace and the comparison clock $s$; it does not define
a spatial metric, a pointwise heat kernel dimension, a state dimension
or the dimension of a physical realization.
The physical-space, physical-clock and native-operation correspondences
remain the separate assumptions of IV, Assumption 111.8. Its
Theorem 111.7 also retains its precise obstruction to direct
same-clock local-form realizations. No new bridge is included in the
definition of $N_H^+$ or $Z_H$.

The assertions in (2.1) and (3.2) are two-sided multiplicative bounds.
No exact coefficient in $N_H^+(\lambda)\sim c\lambda$, no bounded
additive remainder, and no limit of $-s\,d\log Z_H(s)/ds$ is part of
these statements. The logarithmic quotients in (3.3) are the stated
limits; differentiating their bounded logarithmic remainders is not
an inference supplied by the bounds.

**Definition 4.2 (mathematical attribution and applicability).**
The trace, closure, constant mode, polar decomposition and finite-source
comparison in Definition 1.1 are reused from IV, §§98, 99 and 111.
The contribution of Theorems 2.1 and 3.1 is their source-specific global
counting and its consumers, with no exhaustive novelty claim.
The following references specify the established background and its
applicability boundaries.

Wolfgang Woess, [*On the duality between jump processes on ultrametric
spaces and random walks on trees*, arXiv:1211.7216v1, §3.B,
(3.19)–(3.24), Theorem 3.23, and §4](https://arxiv.org/pdf/1211.7216v1),
constructs tree boundary forms using the harmonic reference measure
$\nu_o$ of a transient nearest-neighbour random walk. This is primary
trace-form background, already used in IV. For the unit-conductance
binary tree the harmonic law has first-cylinder probabilities
$1/2,1/2$, whereas (1.1) has $a,b$. Its harmonic-law formulas are
not substitutions for $C$ or $M$ here; the required biased conditional
trace identity is (2.7)–(2.8).

The precise spectral variational supply used in Theorem 2.1 is Teschl's
Theorem 4.10, including its explicit permission to use the quadratic
form domain, and Theorem 4.12(i), cited in that proof. Here the inherited
closed nonnegative form supplies the form domain, (2.3) supplies compact
resolvent, and (2.10) supplies the actual finite-dimensional trial
inequality. No estimate for a different tree Hardy operator is used
as an exact specialization to $C$.

Alexander Bendikov, Alexander Grigor'yan, Eryan Hu and Jiaxin Hu,
[*Heat kernels and non-local Dirichlet forms on ultrametric spaces*,
Ann. Sc. Norm. Super. Pisa Cl. Sci. (5) XXII (2021), 399–461,
Theorem 2.8](https://doi.org/10.2422/2036-2145.201901_011), assume a
proper ultrametric space and their volume condition (V), jump-tail
condition (TJ) and Poincaré condition (PI) to obtain their pointwise
heat-kernel estimates. Under (V) and (TJ) their stated equivalence
still requires (PI). Theorems 2.1 and 3.1 do not instantiate those
hypotheses for the actual biased form. That primary pointwise theorem
is therefore background delimiting a separate problem, not a supplier
for the global trace proof (3.5)–(3.6).

## 4.99 追加锚（本行以下为增补区）
