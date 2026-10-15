# Native long-time phase diffusion on the complete winding cover

## 35. The inherited native source and its complete phase cover

**Definition 35.1 (fixed data and comparison realization).** Let
[G](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md),
[C](FIB_NATIVE_CRITICAL_CUTOFF_SPECTRAL_LIMITS.md),
[N](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md), and
[F](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md) denote the indicated
native theories. Retain G Definition 25.1: fixed $0<Z<1$,
$H=(1-Z)/2$, $I=(l,u)\Subset(0,H)$, $\varepsilon>0$, its exact
probabilities and coefficients $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$
in G (25.4), covariance $\operatorname{diag}(\varepsilon^2,1)$, raw
measure, original clock, and killing at both height endpoints.
Retain its $\lambda$ and positive $L^2(dk)$-normalized $\phi$ in
G (25.5). All statements below fix these data.

Choose once and for all a closed interval
$\mathcal K=[-\kappa_*,\kappa_*]$ small enough for G (26.6), (26.12)
and (32.2) on a slightly larger height interval. In particular all
probabilities are positive there and the coefficient functions and
their derivatives are uniformly bounded. This is a two-sided choice
independent of all subsequent times. Write

$$
\mathcal C=I\times\mathbb R^3,\qquad
q=(\theta,v,x),\qquad d\nu=dk\,dq,\qquad
\mathscr A_\kappa=\varepsilon^2\partial_k^2+
                 (c_\kappa(k)\cdot\partial_q)^2.
\tag{35.1}
$$

This is the all-real-phase realization used in G §32, now considered
at large times. Its nonnegative Dirichlet Friedrichs operator is
$-\mathscr A_\kappa$. Let $g_\kappa^I(t;k,k';r)$ be its transition
density relative to $dk'\,dq'$, with $r=q'-q$. Thus there is no angular
Haar normalization in this density. Its stochastic realization, until
$\zeta=\inf\{t:K_t\notin I\}$, is

$$
dK_t=\sqrt2\varepsilon\,dW_t^1,\qquad
dq_t=\sqrt2c_\kappa(K_t)\,dW_t^2,
\tag{35.2}
$$

where the two Brownian motions are independent. The coefficients have
no phase dependence and the second field has no height component, so
the Itô and Stratonovich equations agree. Smooth coefficients on
the larger interval give uniqueness up to exit; closing its symmetric
smooth-core form gives exactly (35.1), with no added drift or clock.
The phases in (35.1) record winding. At nonzero $\kappa$, the original
lifted coordinate is $D=\kappa x$. At zero this comparison $x$ is not
an additional coordinate of the actual native zero leaf.

The native conclusions below are `repo-derived`. The inherited scalar
fibres and coercivity are G (26.5)--(26.12); C (32.4) supplies the
already established one-direction perturbation method, not an
all-phase local limit. The classical bounded-perturbation, Fourier,
Gaussian and martingale arguments used inside the proofs are
`literature-attested` tools. For the classical abelian-cover setting,
Geng--Iyer, *Long time asymptotics of heat kernels and Brownian winding
numbers on manifolds with boundary*,
[arXiv:1804.00368](https://arxiv.org/html/1804.00368), §§1--2, assumes
a compact Riemannian base and its Laplace--Beltrami heat operator.
The rank-two operator (35.1) on a four-dimensional cover does not meet
that ellipticity hypothesis; none of the limits below is imported
from that theorem. No assertion of global literature novelty is made.

## 36. The native tensor and the full point-kernel limit

**Theorem 36.1 (uniform native ground band and all-phase local limit).**
Define from the original coefficients, before taking any scaling limit,

$$
M_\kappa=\int_I c_\kappa(k)c_\kappa(k)^{\mathsf T}\phi(k)^2\,dk
=\begin{pmatrix}
\langle A_\kappa^2\rangle&\langle A_\kappa B_\kappa\rangle&\langle A_\kappa b_\kappa\rangle\\
\langle A_\kappa B_\kappa\rangle&\langle B_\kappa^2\rangle&\langle B_\kappa b_\kappa\rangle\\
\langle A_\kappa b_\kappa\rangle&\langle B_\kappa b_\kappa\rangle&\langle b_\kappa^2\rangle
\end{pmatrix},\qquad
\langle f\rangle=\int_I f\phi^2\,dk.
\tag{36.1}
$$

There are constants $0<m\le M<\infty$ such that
$m\,\mathrm{Id}\le M_\kappa\le M\,\mathrm{Id}$ for every
$\kappa\in\mathcal K$, including zero. Put

$$
\Gamma_{\kappa,s}(z)=
\frac{\exp[-z^{\mathsf T}M_\kappa^{-1}z/(4s)]}
     {(4\pi s)^{3/2}\sqrt{\det M_\kappa}},\qquad
\Gamma_\kappa=\Gamma_{\kappa,1}.
\tag{36.2}
$$

This is the probability density of a centered Gaussian of covariance
$2sM_\kappa$. For any compact $E\Subset I\times I$,
$B\subset\mathbb R^3$ and $[a,b]\Subset(0,\infty)$,

$$
\sup_{\substack{\kappa\in\mathcal K,\ (k,k')\in E\\
                         z\in B,\ a\le s\le b}}
\left|T^{3/2}e^{\lambda Ts}
g_\kappa^I(Ts;k,k';\sqrt Tz)
-\phi(k)\phi(k')\Gamma_{\kappa,s}(z)\right|
\longrightarrow0\qquad(T\to\infty).
\tag{36.3}
$$

In particular this gives the stated $t^{3/2}$ limit at $s=1$.
There is no relation required between $T$ and $\kappa$: arbitrary
$\kappa(T)\in\mathcal K$, including arbitrary approaches to zero
through both signs, satisfy (36.3). In fact the absolute estimate
holds uniformly for $z\in\mathbb R^3$ and $k,k'\in I$.
If $\Lambda_\kappa(\eta)$ is the lowest eigenvalue of G (26.5), then

$$
\Lambda_\kappa(\eta)=\lambda+
\eta^{\mathsf T}M_\kappa\eta+O(|\eta|^4),\qquad
\nabla_\eta^2\Lambda_\kappa(0)=2M_\kappa,
\tag{36.4}
$$

with uniform remainder near $\eta=0$.

Proof. First (36.1) is not a fitted tensor. If a vector $e$ has
$e^{\mathsf T}M_\kappa e=0$, positivity of $\phi$ makes
$e\cdot c_\kappa$ identically zero on $I$. Its first two derivatives
also vanish. G (32.2) says
$\det(c_\kappa,c_\kappa',c_\kappa'')\ne0$ throughout the fixed
parameter-height rectangle, so $e=0$. Continuity in $\kappa$ and
compactness of $\mathcal K$ and the unit sphere give the uniform
positive lower bound. Bounded coefficients give the upper bound.

The exact Fourier transform convention is

$$
\widehat f(k,\eta)=\int_{\mathbb R^3}e^{-i\eta\cdot q}f(k,q)\,dq,
\qquad
g_\kappa^I(t;k,k';r)=\frac1{(2\pi)^3}
\int_{\mathbb R^3}e^{i\eta\cdot r}
K_{\kappa,\eta}(t;k,k')\,d\eta.
\tag{36.5}
$$

The fibre is precisely
$H_{\kappa,\eta}=-\varepsilon^2\partial_k^2+
|\eta\cdot c_\kappa(k)|^2$ with form domain $H_0^1(I)$ and operator
domain $H^2(I)\cap H_0^1(I)$. Plancherel on the smooth core followed
by closure identifies this direct integral with the entire free
operator, not a restricted sector. G (26.12), which is valid for every
real $\eta$ and both height endpoints, makes (36.5) absolutely
convergent for all sufficiently large times. Its same endpoint-splitting
proof, with the fixed splitting time chosen below half any given
positive time, gives absolute convergence at that time too.
It identifies the kernel pointwise
by Fourier inversion and interior continuity. Thus no trace has been
substituted for a point kernel.

Here is a useful boundary-strengthened version of that supplier. For
$\phi_n(k)=\sqrt{2/(u-l)}\sin(n\pi(k-l)/(u-l))$, one has
$|\phi_n(k)|\le n\phi(k)$. The height sine series therefore gives
$h_I(2\delta;k,k)\le C_\delta\phi(k)^2$ for fixed $\delta>0$.
Splitting a fibre semigroup at $\delta,t-2\delta,\delta$, using
nonnegative-potential domination and Cauchy--Schwarz for its endpoint
evaluation vectors, gives, for $t\ge1$ after choosing $\delta=1/4$,

$$
|e^{\lambda t}K_{\kappa,\eta}(t;k,k')|
\le C\phi(k)\phi(k')\exp[-ct\Psi(|\eta|)],\qquad
\Psi(r)=\begin{cases}r^2&r\le1,\\r^{2/3}&r\ge1.\end{cases}
\tag{36.6}
$$

Indeed the endpoint evaluation norms squared are
$K_{\kappa,\eta}(2\delta;k,k)\le h_I(2\delta;k,k)$, while the
middle operator norm is at most
$e^{-(t-2\delta)(\lambda+c\Psi(|\eta|))}$. Absorbing the fixed
$2\delta\lambda$ and using $t-2\delta\ge t/2$ proves (36.6).
This controls every height level, including limits towards the faces.

For completeness the multivariate version of C (32.4) follows on the
same fixed scalar domain. Write $V_\eta=|\eta\cdot c_\kappa|^2$;
$\|V_\eta\|_\infty\le C|\eta|^2$ uniformly. Min-max gives
$\lambda\le\Lambda_\kappa(\eta)\le\lambda+C|\eta|^2$, and the second
eigenvalue is at least $4\lambda$. For a fixed small radius the first
eigenvalue lies below $2\lambda$. The first normalized eigenfunction
$v_{\kappa,\eta}$ is positive and simple by the scalar Dirichlet
equation and its Wronskian. Decompose it as $z\phi+h$, with
$h\perp\phi$ and $z>0$. Its projected equation is

$$
(H_I-\Lambda_\kappa(\eta))h
=-(1-|\phi\rangle\langle\phi|)V_\eta(z\phi+h).
\tag{36.7}
$$

The inverse on $\phi^\perp$ is uniformly bounded from $L^2$ to
$H^2\cap H_0^1$, since its unperturbed spectrum starts at $4\lambda$.
Consequently $\|h\|_{H^2}\le C|\eta|^2$ and
$z=1+O(|\eta|^4)$. Projecting onto $\phi$ gives
$\Lambda-\lambda=\langle V_\eta\phi,\phi\rangle+O(|\eta|^4)$,
which is (36.4). The Hessian exists, for example by expanding the
resolvent of $H_I+V_\eta$ on a fixed circle around $\lambda$ as the
uniformly convergent bounded-perturbation Neumann series; its Riesz
projection and simple eigenvalue are analytic in the real components
of $\eta$. This is the elementary bounded-perturbation argument
underlying the classical min-max and perturbation tools cited in
C Definition 31.1; no native limit is supplied by those tools.

The $H^2$ bound also bounds the first derivative of $h$. Since $h$
vanishes at both faces and $\phi$ is comparable to distance from the
boundary, it follows that
$v_{\kappa,\eta}(k)/\phi(k)=1+O(|\eta|^2)$ uniformly for $k\in I$.
The complementary spectral subspace has spectrum at least $4\lambda$.
The same fixed-time endpoint splitting used above therefore gives

$$
K_{\kappa,\eta}(t;k,k')
=e^{-t\Lambda_\kappa(\eta)}
 v_{\kappa,\eta}(k)v_{\kappa,\eta}(k')
+R_{\kappa,\eta}(t;k,k'),\qquad
|R_{\kappa,\eta}|\le C\phi(k)\phi(k')e^{-4\lambda t}
\tag{36.8}
$$

for $t\ge1$ and that small fixed frequency ball. In obtaining the
remainder, insert the orthogonal complementary projection in the
middle semigroup; the endpoint evaluation norms are bounded by the
full dominated semigroup. This justifies the bound without an
uncontrolled sum over excited eigenfunctions.

Change variables $\eta=\xi/\sqrt T$ in (36.5). On every bounded
$\xi$ set, (36.4), (36.8) give, uniformly in the stated parameters,

$$
e^{\lambda Ts}K_{\kappa,\xi/\sqrt T}(Ts;k,k')
\longrightarrow
\phi(k)\phi(k')e^{-s\xi^{\mathsf T}M_\kappa\xi}.
\tag{36.9}
$$

All frequencies have an actual integrable majorant. For $T\ge1$,

$$
T\Psi(|\xi|/\sqrt T)=
\begin{cases}|\xi|^2&|\xi|\le\sqrt T,\\
T^{2/3}|\xi|^{2/3}&|\xi|>\sqrt T,
\end{cases}
\quad\ge\min(|\xi|^2,|\xi|^{2/3}).
\tag{36.10}
$$

Equations (36.6) and $s\ge a$ bound the transformed integrand by
$C\phi(k)\phi(k')\exp[-ca\min(|\xi|^2,|\xi|^{2/3})]$, integrable
on $\mathbb R^3$. The limiting integrand has the uniform Gaussian
majorant from $M_\kappa\ge m\,\mathrm{Id}$. First integrate the
uniform error on a bounded frequency ball, then send its radius to
infinity using these two majorants. This proves convergence in
$L^1(d\xi)$ uniformly in $\kappa,s,k,k'$. The factor
$e^{i\xi\cdot z}$ has modulus one, giving the stronger spatial
uniformity. The Gaussian Fourier integral with exactly $(2\pi)^{-3}$
is (36.2); its covariance is $2sM_\kappa$. This proves (36.3). $\square$

**Proposition 36.2 (explicit wall tensor and cross terms).** At the
resolved wall set $\mu_j=\langle k^j\rangle$ for $j=1,2$ and
$\nu_j=\langle k^{-j}\rangle$ for $j=1,2$. Then

$$
M_0=\begin{pmatrix}
\frac14-\frac{\mu_1}{2H}+\frac{\mu_2}{4H^2}
&-\frac{\mu_1}{4H}+\frac{\mu_2}{4H^2}
&\frac{\nu_1}{2}-\frac1H+\frac{\mu_1}{2H^2}\\
-\frac{\mu_1}{4H}+\frac{\mu_2}{4H^2}
&\frac{\mu_2}{4H^2}&-\frac1{2H}+\frac{\mu_1}{2H^2}\\
\frac{\nu_1}{2}-\frac1H+\frac{\mu_1}{2H^2}
&-\frac1{2H}+\frac{\mu_1}{2H^2}
&\nu_2-\frac{2\nu_1}{H}+\frac1{H^2}
\end{pmatrix}.
\tag{36.11}
$$

In particular the tensor is not implicitly assumed diagonal.

Proof. Substitute G (21.7), namely
$c_0=((H-k)/(2H),-k/(2H),1/k-1/H)$, into (36.1), multiply each pair
of entries, and use $\langle1\rangle=1$. All inverse moments are
finite since $l>0$. Positivity is Theorem 36.1, not a supposition
about these moments. For example $\langle A_0B_0\rangle<0$ because
$0<k<H$ on $I$. $\square$

## 37. Killing, the ground-state process, and terminal survival

**Definition 37.1 (three probability conventions).** Let
$\mathbb P_{k,q}^{\kappa}$ be (35.2), sent to a cemetery state at
$\zeta$. Write $S_k(t)=\mathbb P_k(\zeta>t)$ and
$J_\phi=\int_I\phi(k)\,dk$. For $T>0$ the terminal-survivor law
on the entire path interval $[0,T]$ is

$$
\mathbb P_{k,q}^{\kappa,T}(A)
=\frac{\mathbb P_{k,q}^{\kappa}(A,\zeta>T)}{S_k(T)}.
\tag{37.1}
$$

The ground-state process, denoted $\mathbb Q_{k,q}^{\kappa}$, has
transition density and generator

$$
\begin{aligned}
p^{Q,\nu}_\kappa(t;(k,q),(k',q'))
 &=e^{\lambda t}\frac{\phi(k')}{\phi(k)}
                      g_\kappa^I(t;k,k';q'-q),\\
\mathscr A_\kappa^Qf
 &=\phi^{-1}(\mathscr A_\kappa+\lambda)(\phi f)
 =\varepsilon^2\partial_k^2f
   +2\varepsilon^2\frac{\phi'}{\phi}\partial_kf
   +(c_\kappa\cdot\partial_q)^2f.
\end{aligned}
\tag{37.2}
$$

The displayed density is relative to raw $d\nu'=dk'\,dq'$.
Relative instead to $d\mu^Q=\phi(k')^2dk'\,dq'$, it is
$p^{Q,\mu}_\kappa=e^{\lambda t}g_\kappa^I/(\phi(k)\phi(k'))$.
This is the classical ground-state/Doob transform; compare
Champagnat--Villemonais,
[arXiv:1404.1349, Theorem 3.1(ii)](https://arxiv.org/html/1404.1349).
Its identities here are proved directly below. The invariant-probability
conclusion for their uniformly mixing setting is not assumed for the
noncompact phase cover. Likewise
[S §50](FIB_ATOM_STATISTICAL_LAWS.md) concerns a different finite-chain
and mixed-boundary model, not (35.1). The height survival series below
is the same Dirichlet series as G (29.1)--(29.2), with $k$ in place
of $k_0$. These classical height and transform identities are the
suppliers for the native endpoint factorization (37.7) and the
whole-horizon limit (38.1).

**Theorem 37.2 (exact survival, finite-horizon correspondence and endpoint laws).**
For every $k\in I$ and $t>0$,

$$
S_k(t)=\sum_{n=1}^\infty e^{-n^2\lambda t}\phi_n(k)J_n,
\qquad
J_n=\begin{cases}2\sqrt{2(u-l)}/(n\pi)&n\text{ odd},\\0&n\text{ even}.
\end{cases}
\tag{37.3}
$$

The series is absolutely convergent, independent of $\kappa$, and

$$
S_k(t)=e^{-\lambda t}\phi(k)J_\phi
       [1+O(e^{-8\lambda t})]\qquad(t\ge1)
\tag{37.4}
$$

uniformly in $k\in I$. The Q-process is conservative; its height has
invariant probability $\phi^2dk$. The full process is symmetric with
infinite invariant reference measure $\mu^Q$, and has no invariant
probability on $\mathcal C$.

For every $0\le r\le T$ the exact change of measure on $\mathcal F_r$
is

$$
\left.\frac{d\mathbb P_{k,q}^{\kappa,T}}
              {d\mathbb Q_{k,q}^{\kappa}}\right|_{\mathcal F_r}
=\frac{e^{-\lambda r}\phi(k)S_{K_r}(T-r)}
       {\phi(K_r)S_k(T)}.
\tag{37.5}
$$

At $r=T$ this is
$w_T=\phi(K_T)^{-1}/\mathbb E_k^Q[\phi(K_T)^{-1}]$.
For each fixed finite $r$, (37.5) tends to one uniformly as
$T\to\infty$; in particular the fixed-prefix laws converge in total
variation to Q. This fixed-prefix statement is separate from the
whole-moving-horizon theorem in §38.

The terminal heights satisfy, in total variation uniformly in $k$,

$$
\mathcal L_{\mathbb Q_k}(K_T)\longrightarrow\phi(k')^2dk',\qquad
\mathcal L_{\mathbb P_k^{\kappa,T}}(K_T)
\longrightarrow\frac{\phi(k')}{J_\phi}\,dk'.
\tag{37.6}
$$

The second is the Yaglom height law, distinct from the first. For
initial heights in interior compact sets, the endpoint densities obey
the following locally uniform limits in $(k',z)\in I\times\mathbb R^3$,
uniformly in $\kappa\in\mathcal K$:

$$
\begin{aligned}
T^{3/2}p^{Q,\nu}_\kappa(T;(k,q),(k',q+\sqrt Tz))
 &\longrightarrow\phi(k')^2\Gamma_\kappa(z),\\
\frac{T^{3/2}g_\kappa^I(T;k,k';\sqrt Tz)}{S_k(T)}
 &\longrightarrow\frac{\phi(k')}{J_\phi}\Gamma_\kappa(z).
\end{aligned}
\tag{37.7}
$$

Proof. Integrating (35.2) over phases leaves exactly killed Brownian
height. Integrating its sine kernel proves (37.3). The bound
$|\phi_n|\le n\phi$ and $J_n=J_\phi/n$ for odd $n$ bounds the
relative remainder by $\sum_{n\ge3,\ n\mathrm{\ odd}}
e^{-(n^2-1)\lambda t}$, proving (37.4). No survival probability or
height prior has been chosen by adjusting the phase tensor.

Since $\int h_I(t;k,k')\phi(k')dk'=e^{-\lambda t}\phi(k)$,
the first density in (37.2) integrates to one. Its semigroup identity
follows by cancellation of the middle $\phi$ factors. This constructs
the conservative Markov law; equivalently on each finite interval its
Radon--Nikodym derivative relative to the killed law, restricted to
survival, is $e^{\lambda t}\phi(K_t)/\phi(k)$. These consistent
finite-interval laws have continuous paths and no boundary hit in
finite time. On compact interior sets their generator is the product
calculation (37.2). They can also be realized by

$$
dK_t=\sqrt2\varepsilon\,d\widetilde W_t^1
       +2\varepsilon^2(\phi'/\phi)(K_t)dt,\qquad
dq_t=\sqrt2c_\kappa(K_t)dW_t^2,
\tag{37.8}
$$

where $W^2$ remains independent of the complete height path: the
finite-horizon change of measure depends only on height. Thus the
transform changes the height drift, not the two-control covariance.
Symmetry of $g$ makes $p^{Q,\mu}$ symmetric; conservativity and Tonelli
then make $\mu^Q$ invariant. The height process has normalized
invariant measure $\phi^2dk$; the full reference measure is its product
with infinite phase Lebesgue measure. The projection of that full
infinite measure onto height is not a probability marginal.

For the height alone its density relative to $\phi(k')^2dk'$ is

$$
R_t(k,k')=\frac{e^{\lambda t}h_I(t;k,k')}{\phi(k)\phi(k')}
=\sum_{n\ge1}e^{-(n^2-1)\lambda t}
             \frac{\phi_n(k)}{\phi(k)}
             \frac{\phi_n(k')}{\phi(k')},\qquad
\sup_{k,k'}|R_t-1|\le Ce^{-3\lambda t}\quad(t\ge1).
\tag{37.9}
$$

This follows from the same sine bound, now summing
$n^2e^{-(n^2-1)\lambda t}$. It proves the first height limit and
uniqueness of that invariant height probability. Dividing the raw
height kernel by (37.4) proves the second, including its total
variation claim. The two limiting densities differ because the sine
$\phi$ is nonconstant on $I$.

For the full cover, integrating (36.6) in frequency gives
$p^{Q,\mu}_\kappa(t;y,y')\le Ct^{-3/2}$ for $t\ge1$, uniformly in
both points: the integral of $e^{-ct\Psi(|\eta|)}$ is at most
$Ct^{-3/2}$, by splitting $|\eta|\le1$ and its complement or by
(36.10). If $\pi$ were an invariant probability and $E$ had finite
$\mu^Q$ measure, then
$\pi(E)=\int Q_t(y,E)\pi(dy)\le Ct^{-3/2}\mu^Q(E)$, so $\pi(E)=0$.
A countable exhaustion by such sets contradicts $\pi(\mathcal C)=1$.

The Markov property of the killed law on $\mathcal F_r$ gives its
survivor density $\mathbf1_{\{\zeta>r\}}S_{K_r}(T-r)/S_k(T)$.
Dividing by the Q density yields (37.5), including the endpoint
formula with $S_{K_T}(0)=1$. Formula (37.4) proves its fixed-prefix
uniform convergence; no terminal-horizon approximation has been made.
Finally (36.3), (37.2), (37.4) give (37.7), with their exact raw
density factors. $\square$

## 38. Whole-horizon phase paths and their terminal heights

**Theorem 38.1 (uniform path limits at the moving terminal horizon).**
For deterministic $k\in K\Subset I$ and arbitrary initial phase $q$,
put $X_T(s)=(q_{Ts}-q)/\sqrt T$, $0\le s\le1$. Let
$\mathcal W_\kappa$ be Brownian path measure on
$C([0,1],\mathbb R^3)$ with covariance
$\mathbb E[B_sB_r^{\mathsf T}]=2\min(s,r)M_\kappa$.
In the bounded Lipschitz metric for the uniform path topology and the
ordinary height topology, uniformly in $\kappa\in\mathcal K$ and
$k\in K$,

$$
\begin{aligned}
\mathcal L_{\mathbb Q_{k,q}^{\kappa}}(X_T,K_T)
 &\Longrightarrow\mathcal W_\kappa\otimes(\phi^2dk'),\\
\mathcal L_{\mathbb P_{k,q}^{\kappa,T}}(X_T,K_T)
 &\Longrightarrow\mathcal W_\kappa\otimes(\phi\,dk'/J_\phi).
\end{aligned}
\tag{38.1}
$$

Thus in each convention the entire scaled phase path and its terminal
height become independent, with the two different height laws shown.
The assertions also hold on every fixed finite macroscopic interval
$[0,b]$ with $X_T(s)=(q_{Ts}-q)/\sqrt T$: use Q, or condition the
original law on $\zeta>Tb$, and pair the path with $K_{Tb}$.
The Brownian covariance on that interval remains $2\min(s,r)M_\kappa$.
All statements allow arbitrary simultaneous parameter sequences,
including $\kappa(T)\to0$ with no rate condition. For example, if
$\kappa_n\to\bar\kappa\in\mathcal K$, $T_n\to\infty$ and
$k_n\in K$, the fixed limiting Brownian covariance is
$2M_{\bar\kappa}$, with no convergence of $k_n$ required.

Proof. We first establish the uniform occupation estimate actually
needed here. Let $f_\kappa$ be any of the nine bounded functions
$c_{\kappa,i}c_{\kappa,j}-(M_\kappa)_{ij}$. Its mean under $\phi^2dk$
is zero and its supremum norm has a common bound. Equation (37.9)
and the Markov contraction for $t\le1$ give

$$
\sup_k|\mathbb E_k^Q f_\kappa(K_t)|
\le C e^{-3\lambda t}\quad(t\ge1),\qquad
\mathbb E_k^Q\left|\int_0^L f_\kappa(K_r)dr\right|^2\le C(L+1).
\tag{38.2}
$$

For the second estimate expand the square over the triangle
$0\le r\le s\le L$. Conditional expectation at $r$ bounds its
integrand in absolute value by $C$ when $s-r\le1$ and by
$Ce^{-3\lambda(s-r)}$ otherwise. The integral is $O(L)$; adding a
constant covers all $L$. These bounds do not require a stationary
initial height and are independent of $\kappa$.

At each fixed macroscopic time (38.2) gives $L^2$ convergence of the
occupation average. A finite grid of times, followed by the common
deterministic Lipschitz bound on the integrated functions, gives

$$
\sup_{0\le s\le b}\left|
\frac1T\int_0^{Ts}c_\kappa(K_r)c_\kappa(K_r)^{\mathsf T}dr
-sM_\kappa\right|\longrightarrow0
\quad\text{in Q probability, uniformly in }\kappa,k.
\tag{38.3}
$$

This already identifies the stochastic quadratic variation as
$2sM_\kappa$, agreeing with the independent band Hessian (36.4).
More explicitly, $X_T$ is a continuous square-integrable martingale
under Q, starts at zero, and its predictable quadratic covariation is
twice the integral in (38.3). All jumps of it and of this bracket are
zero. These check exactly the hypotheses of the classical martingale
FCLT in Whitt, *Proofs of the martingale FCLT*,
[arXiv:0712.1929v2, Theorem 2.1(ii)](https://arxiv.org/html/0712.1929v2).
For a converging parameter subsequence its covariance matrix there is
$C=2M_{\bar\kappa}$. That classical theorem alone neither supplies a
point kernel nor proves the terminal-survivor assertion.

To prove the latter on its entire moving horizon, use the exact
endpoint density $w_T$ from (37.5), not a fixed-prefix replacement.
For each $1<p<3$, (37.9) yields, uniformly for $T\ge1$,

$$
\mathbb E_k^Q[\phi(K_T)^{-p}]
\le C\int_I\phi^{2-p}dk'<\infty.
\tag{38.4}
$$

The integral is finite since $\phi$ vanishes linearly at each face.
Its first-moment denominator tends uniformly to $J_\phi>0$, also by
(37.9); for all sufficiently large $T$ the random densities $w_T$
have a common $L^p(\mathbb Q)$ bound. Hölder's inequality transfers
every uniform probability convergence in (38.3) to the full terminal
survivor law. The same argument applies with $T$ replaced by $Tb$.

We give the additional argument that proves terminal independence,
rather than deducing it from the FCLT. Under either law, condition on
the complete height path on $[0,Tb]$. The Brownian motion $W^2$ remains
independent of it, because both changes of measure depend only on
height. Thus the conditional phase path is centered Gaussian with
conditional covariance

$$
\mathbb E[X_T(s)X_T(r)^{\mathsf T}\mid(K_v)_{0\le v\le Tb}]
=\frac2T\int_0^{T\min(s,r)}
                   c_\kappa(K_v)c_\kappa(K_v)^{\mathsf T}dv.
\tag{38.5}
$$

All its conditional fourth increment moments are bounded by
$C|s-r|^2$, since the coefficient norm is uniformly bounded and a
centered Gaussian fourth moment is bounded by a constant times the
square of its variance. This is a uniform conditional tightness
bound in the continuous path space, with initial value zero.
Equation (38.3), also under the survivor law, makes every finite
conditional covariance matrix converge in probability to the Brownian
one. These two facts imply, with $d_{\rm BL}$ denoting bounded
Lipschitz distance on continuous paths,

$$
\mathbb E\,d_{\rm BL}\!\left(
 \mathcal L(X_T\mid(K_v)_{0\le v\le Tb}),\mathcal W_\kappa\right)
\longrightarrow0.
\tag{38.6}
$$

The convergence is uniform in the stated parameters. Here is a direct
conditional proof that also controls the supremum over test functions.
On the dyadic grid of $[0,b]$ with $2^n$ intervals, let $D_n$ be the
maximum neighboring increment of a conditional Gaussian path. Its
fourth-moment bound gives
$\mathbb E[D_n^4\mid K]\le C2^{-n}$ and hence
$\mathbb E[D_n\mid K]\le C2^{-n/4}$. Dyadic chaining and continuity
bound the expected uniform error of piecewise-linear interpolation on
that grid by $C\sum_{j\ge n}2^{-j/4}\le C'2^{-n/4}$, for every
height path. The same bound holds for every target Brownian law.
For a fixed grid, (38.3) and (38.5) give convergence in probability of
the conditional covariance matrix to its target, uniformly in
$\kappa,k$. Centered Gaussian laws depend continuously on their
covariance matrices, uniformly on this bounded set of matrices: couple
them as $\Sigma^{1/2}Z$ with one standard finite-dimensional Gaussian
$Z$ and use continuity of the positive matrix square root. The
boundedness of the distance turns this probability convergence into
convergence in mean. Comparing the two grid interpolations and then
sending $n\to\infty$ proves (38.6), without any coupling of the
different height probability spaces.

For a joint bounded Lipschitz function $F(x,k')$, condition on height
and apply (38.6) to the path function $F(\cdot,K_{Tb})$; its norm is
bounded uniformly even though it depends on the height path. The
result differs by a quantity tending uniformly to zero from
$\mathbb E[\int F(x,K_{Tb})\mathcal W_\kappa(dx)]$.
The height total-variation limits (37.6) turn this last expression into
the required product integral, uniformly over the joint test class.
This proves exactly the bounded Lipschitz uniformity in (38.1),
including terminal independence on the full moving horizon.
Translation invariance removes all dependence on the initial phase.
The same estimates already used on $[0,b]$ prove the fixed finite
$b$ version. $\square$

**Proposition 38.2 (compensation and the original unconditioned law).**
The total mass of the raw killed kernel is exactly $S_k(t)$.
Exponential compensation has total mass
$e^{\lambda t}S_k(t)\to\phi(k)J_\phi$, not in general one. In
particular its scaled endpoint measure converges to

$$
\phi(k)\phi(k')\Gamma_\kappa(z)\,dk'\,dz.
\tag{38.7}
$$

This is a finite measure, and its normalized probability is the
terminal-survivor endpoint limit. At every fixed positive macroscopic
time the original unconditioned killed/cemetery law tends to the
cemetery state. If instead phases are explicitly continued by the
stopped convention $q_t^{\rm stop}=q_{t\wedge\zeta}$, then

$$
\sup_{0\le s\le b}
\frac{|q_{Ts}^{\rm stop}-q_0|}{\sqrt T}\longrightarrow0
\quad\text{almost surely}.
\tag{38.8}
$$

Proof. The mass identities are (37.3)--(37.4). The phase endpoint
law in (38.1) and the survival factor prove weak convergence of the
entire finite measure (38.7), not just its density on compact sets.
For simultaneous varying $\kappa$ this statement compares to the
corresponding $\Gamma_\kappa$, or uses any limiting parameter as in
Theorem 38.1. Since $\zeta<\infty$ almost surely and $S_k(Ts)\to0$
for $s>0$, the cemetery assertion follows. The stopped stochastic
integral has a continuous extension to the finite interval
$[0,\zeta]$, because its coefficient is bounded and its bracket there
is finite. Its sample-path supremum is finite, which proves (38.8)
for each fixed $\kappa$. Uniformly in the parameter family the same
zero limit holds in probability: conditional Doob inequality and
$\mathbb E_k\zeta=(k-l)(u-k)/(2\varepsilon^2)$ bound the expected
squared stopped supremum by one common constant. The almost sure
statement does not identify sample paths across different parameter
values. None of these laws is a postulated conservative physical
diffusion. $\square$

## 39. Original-coordinate lifts and the actual zero leaf

**Theorem 39.1 (signed winding lift and its uniform normalization).**
For $\kappa\ne0$ let $y=(\theta,v,D)=J_\kappa q$, where
$J_\kappa=\operatorname{diag}(1,1,\kappa)$. Let
$g^{\rm orig}_\kappa$ denote the all-real winding-lift kernel in
$dk\,dy$, with coefficient vector
$(A_\kappa,B_\kappa,\kappa b_\kappa)$. Then exactly

$$
g^{\rm orig}_\kappa(t;k,k';J_\kappa r)
=|\kappa|^{-1}g_\kappa^I(t;k,k';r),\qquad
\widehat M_\kappa=J_\kappa M_\kappa J_\kappa^{\mathsf T}.
\tag{39.1}
$$

The original-coordinate phase covariance is $2\widehat M_\kappa$.
The $13$ and $23$ entries of $\widehat M_\kappa$ are respectively
$\kappa(M_\kappa)_{13}$ and $\kappa(M_\kappa)_{23}$, its $33$ entry
is $\kappa^2(M_\kappa)_{33}$, and
$\det\widehat M_\kappa=\kappa^2\det M_\kappa>0$.
Both signs therefore have the same positive rank, with their actual
signed cross covariances. The corresponding original-coordinate
Gaussian density is exactly
$\widehat\Gamma_{\kappa,s}(y)=|\kappa|^{-1}
\Gamma_{\kappa,s}(J_\kappa^{-1}y)$, a probability density in raw $dy$.
For each fixed nonzero parameter,
$T^{3/2}e^{\lambda Ts}g^{\rm orig}_\kappa(Ts;k,k';\sqrt Ty)
\to\phi(k)\phi(k')\widehat\Gamma_{\kappa,s}(y)$,
locally uniformly in interior height endpoints, $y$, and positive $s$.
Uniformly in the sets of Theorem 36.1,

$$
|\kappa|T^{3/2}e^{\lambda Ts}
g^{\rm orig}_\kappa(Ts;k,k';J_\kappa\sqrt Tz)
\longrightarrow\phi(k)\phi(k')\Gamma_{\kappa,s}(z)
\tag{39.2}
$$

for all nonzero $\kappa\in\mathcal K$, with no rate relation at the
wall. The path laws transform by the same $J_\kappa$. At fixed
nonzero parameter their phase rank is three. If $\kappa(T)\to0$
and the original coordinates are scaled by $\sqrt T$ without dividing
$D$ by $\kappa(T)$, their Brownian path limit instead has covariance
$2J_0M_0J_0^{\mathsf T}$ and rank two.

Proof. The invertible linear map has signed third coordinate
$D=\kappa x$ and absolute volume Jacobian $|\kappa|$. It pushes
(35.2), its height deaths, and each of the two conditional laws to
the stated original lift in the unchanged clock. Reducing all three
original phases modulo $2\pi$ gives exactly G Definition 25.1's
wrapped SDE, hence its killed law by uniqueness; no observation of
the winding is inferred from this mathematical projection.
Changing density
therefore proves (39.1); changing the Gaussian covariance proves the
congruence and its entry formulas. Equation (39.2) is the exact
pullback of (36.3). The continuous mapping theorem applied to (38.1)
gives the fixed-parameter path result. For a vanishing parameter,
$J_{\kappa(T)}\to J_0$ and the resolved paths are uniformly tight;
the same theorem with these converging linear maps gives the last
limit. The positive upper $2\times2$ principal block of $M_0$ makes
its rank exactly two. No uniform nondegeneracy in unnormalized
original $D$ coordinates is asserted. $\square$

**Theorem 39.2 (two-phase native zero-leaf counterpart).** On the
actual zero leaf $D=D_0$, write $a_0=(A_0,B_0)$ and
$N_0=\langle a_0a_0^{\mathsf T}\rangle$, the upper principal block of
$M_0$. The all-real winding cover of its two native phases has raw
kernel $g^{\rm leaf}$ on $I\times\mathbb R^2$, generator
$\varepsilon^2\partial_k^2+(a_0\cdot\partial_{\theta,v})^2$, and

$$
T e^{\lambda Ts}g^{\rm leaf}(Ts;k,k';\sqrt Tz)
\longrightarrow
\phi(k)\phi(k')
\frac{e^{-z^{\mathsf T}N_0^{-1}z/(4s)}}
     {4\pi s\sqrt{\det N_0}}.
\tag{39.3}
$$

The uniformity in height, $z$ and positive compact $s$ sets is that
of Theorem 36.1, now with $z\in\mathbb R^2$. Its Q and terminal
survivor phase-path limits are two-dimensional Brownian motion of
covariance $2N_0$, with the respective independent terminal heights
$\phi^2dk'$ and $\phi\,dk'/J_\phi$. On the actual wrapped zero leaf
$I\times\mathbb T^2$, the raw point-kernel limit is instead

$$
e^{\lambda t}p^{\rm leaf}_{\rm wrapped}(t;k,\vartheta;k',\vartheta')
\longrightarrow\frac{\phi(k)\phi(k')}{(2\pi)^2}.
\tag{39.4}
$$

In the four original coordinates the transition law at zero has the
factor $\delta_{D_0}(dD')$; it has no raw four-dimensional point
density. The three-phase resolved zero cover in (35.1) and the
two-phase zero-leaf winding cover in (39.3) consequently have
different effective ranks, three and two.
The collapsed original-coordinate limit in Theorem 39.1 has exactly
the covariance $2N_0$ in its two moving phase coordinates, in agreement
with this native zero-leaf counterpart.

Proof. At zero the original $D$ coefficient is exactly zero. Removing
this frozen coordinate leaves exactly $a_0$, not a guessed limiting
diffusion. Here
$A_0=(H-k)/(2H)$ and $B_0=-k/(2H)$, and
$\det(a_0,a_0')=-1/(4H)\ne0$. Hence a linear combination vanishing
on $I$ has both coefficients zero; its Gram tensor $N_0$ is positive
definite. Its scalar fibres are exactly $H_{0,(\eta_1,\eta_2,0)}$,
so (36.6) restricts to all their frequencies. The perturbation proof
(36.7)--(36.8) now gives the quadratic form $\eta^{\mathsf T}N_0\eta$.
Fourier inversion has factor $(2\pi)^{-2}$, and the change
$\eta=\xi/\sqrt T$ has Jacobian $T^{-1}$. The two-dimensional
integrable version of (36.10) gives full domination and proves
(39.3) with the displayed Gaussian factor. This is an argument for
every real frequency, not an inference from a marginal trace.

The height laws (37.3)--(37.9) are identical. Conditional on height,
the two-phase stochastic integral has covariance
$2\int a_0a_0^{\mathsf T}dt$. Applying the occupation estimate
(38.2) to its four entries, the endpoint-weight bound (38.4), and
the conditional Gaussian tightness and product argument
(38.5)--(38.6), proves precisely the stated two-phase path and
terminal-height limits.

For the wrapped leaf, use its exact Fourier series over
$(n,m)\in\mathbb Z^2$. The zero frequency is $h_I/(2\pi)^2$;
every other frequency has a positive gap above $\lambda$ by
G (26.6) at $(n,m,0)$. The absolute sum of its remainder is bounded
by $C\phi(k)\phi(k')\sum_{(n,m)\ne0}
e^{-ct\Psi(\sqrt{n^2+m^2})}$ from (36.6). This tends to zero
exponentially, since half the exponent extracts a positive constant
gap and the other half is summable for $t\ge1$. The height sine
series then proves (39.4). Thus no termwise asymptotic periodization
of (39.3) has been used. The frozen-coordinate delta assertion
follows directly from $dD_t=0$. $\square$

## 40. What the effective phase rank measures

**Proposition 40.1 (temporal averaging, bounded height and observation).**
In the original clock, the instantaneous covariance of the resolved
four-coordinate process, under either the original killed or Q law,
is

$$
2\begin{pmatrix}\varepsilon^2&0\\0&c_\kappa(k)c_\kappa(k)^{\mathsf T}\end{pmatrix}dt,
\tag{40.1}
$$

of rank two. Its instantaneous phase block has rank one. The
large-time phase tensor $2M_\kappa$ has rank three because temporal
height occupation averages the distinct phase directions
$c_\kappa(k)$ with the height weight $\phi^2dk$. Bounded height
itself supplies no fourth diffusive coordinate:
$\sup_{s\le b}|K_{Ts}-K_0|/\sqrt T\le(u-l)/\sqrt T$ under the two
surviving conventions. On the actual zero leaf the corresponding
large-time phase rank is two, with the same bounded-height statement.

These limits do not give a smooth same-clock elliptic factor of
dimension three, nor identify phase coordinates with physical space.
They distinguish a full winding record from an observation of wrapped
phases. They supply no physical rotation symmetry, spatial-selection
principle, or observation and conditioning operation furnished by FIB.

Proof. Equation (40.1) is the quadratic variation of (35.2) or
(37.8); its height coefficient is positive and its phase vector is
nonzero, so its rank is exactly two. Its phase rank is exactly one.
Equations (36.1), (38.3) explain how its time average becomes positive
on all three phase directions. This uses different height levels
along one actual stochastic history, not three independent native
phase actuators. The bounded-height inequality is deterministic.
Together with Theorems 38.1 and 39.2 it gives the stated ranks after
discarding that bounded direction.

For any smooth observation $R$ into a space of dimension $d$, the
second-order symbol pushed forward from the two original fields is
$\varepsilon^2dR(P)dR(P)^{\mathsf T}
+dR(Q)dR(Q)^{\mathsf T}$, of rank at most two. Lower-order drifts,
including the Q height drift, do not alter it. Thus it cannot equal
a positive definite $d\times d$ elliptic symbol when $d\ge3$.
This is exactly the reused same-clock obstruction in N Theorem 10.5 and F;
the singular time-and-space limit in (36.3) or (38.1) does not
contradict it. Likewise the local homogeneous heat dimensions seven
on the resolved cover and four on the actual zero leaf are the
inherited bracket-growth quantities in G §34, not these effective
covariance ranks or physical dimensions.

The resolved cover has topological dimension four and three real
phase coordinates. The zero-leaf winding cover has topological
dimension three and two real phase coordinates. Its height is bounded
and its phase limit has rank two. Current-ray dimensions refer to
the underlying native control and observation geometry of N and F;
they are not defined by counting nonzero eigenvalues of $M_\kappa$.
Thus none of these distinct counts is silently identified with the
rank-three limiting phase law or a dimension of physical space.

The wrapping map identifies phase representatives differing by a
nonzero lattice vector. Thus a wrapped endpoint has many distinct
winding lifts. A complete continuous wrapped path with a specified
initial lift has a unique mathematical lift, whereas an endpoint
alone does not. These are different observation conventions; the
cover theorem does not supply a device that acquires the path. In
particular the native wrapped nonzero phases have the long-time
compact mixing law of G (26.4), not the real-cover density (36.3).
Their exact Fourier series, and the leaf proof of (39.4), already
distinguish these objects without interchanging an uncontrolled
infinite winding sum with a limit.

Finally a linear whitening by $M_\kappa^{-1/2}$ makes the limiting
Gaussian covariance a scalar matrix in new mathematical coordinates.
Neither the raw native coefficients nor their observation and
operation rules are thereby proved invariant under physical $SO(3)$.
The two different changes of probability law in §37 likewise define
analytic laws and do not construct a preparation or survival service.
FIB alone does not specify the imposed diffusion covariance, raw
density, clock, winding observation, or conditioning convention.
No Green-tail, Coulomb, binding, empirical, resource, or formal-kernel
certification conclusion is a consequence asserted here. $\square$

## 追加锚（本行以下为增补区）

## 41. All-time estimates for the native threshold kernel

**Definition 41.1 (unchanged operator and three Green conventions).**
Retain exactly §§35--40 and G Definition 25.1. Write
$B_\kappa=-\mathscr A_\kappa$, $F_\kappa(t;k,k';r)
=e^{\lambda t}g_\kappa^I(t;k,k';r)$, and $p=\phi(k)\phi(k')$.
For $m\ge0$ define the nonnegative extended integral

$$
\mathcal G_{\kappa,m}(k,k';r)
=\int_0^\infty e^{-mt}F_\kappa(t;k,k';r)\,dt.
\tag{41.1}
$$

For $m>0$ this is the raw kernel of $(B_\kappa-\lambda+m)^{-1}$.
The original unshifted killed Green is $\mathcal G_{\kappa,\lambda}$,
not $\mathcal G_{\kappa,0}$. Its unit source is relative to $dk\,dq$.
The massive Q Green relative to raw measure is
$\phi(k')\mathcal G_{\kappa,m}/\phi(k)$; relative to
$\phi(k')^2dk'\,dq'$ it is $\mathcal G_{\kappa,m}/p$.
These are exact consequences of (37.2), not new conditioning operations.
All constants below depend only on the fixed data and $\mathcal K$.

**Lemma 41.2 (native global spatial bounds and integrable band error).**
For the fixed interval $\mathcal K$ of Definition 35.1, for all its parameters,
all $k,k'\in I$ and $r\in\mathbb R^3$, there are $c,C>0$ such that

$$
\begin{aligned}
0\le F_\kappa(t;k,k';r)
 &\le Cp\,t^{-6}
       \exp[-c(|r|^2+|k-k'|^2)/t],&&0<t\le1,\\
F_\kappa(t;k,k';r)
 &\le Cp\,t^{-3/2}e^{-c|r|^2/t},&&t\ge1,\\
|F_\kappa(t;k,k';r)-p\Gamma_{\kappa,t}(r)|
 &\le Cp\,t^{-5/2}
       e^{-c\min(|r|^2/t,|r|)},&&t\ge1.
\end{aligned}
\tag{41.2}
$$

The small-time power is an upper bound, not the sharp homogeneous power.
These estimates include both height faces and every real frequency.

Proof. The additional spatial estimates can be obtained directly from the
same scalar fibres as (36.5). Here are details of the complex-frequency
step, including the bounds needed for its integration. For real $\eta,\rho$
the Brownian-bridge/Feynman--Kac formula for the scalar bounded potential
$( (\eta+i\rho)\cdot c_\kappa)^2$ gives

$$
|K_{\kappa,\eta+i\rho}(t;k,k')|
\le e^{C t|\rho|^2}K_{\kappa,\eta}(t;k,k').
\tag{41.3}
$$

Indeed the real part of the potential is
$(\eta\cdot c_\kappa)^2-(\rho\cdot c_\kappa)^2$, and the last square
is bounded by $C|\rho|^2$. This formula follows also by the bounded
multiplication Trotter products, so does not assume ellipticity in phases.
It applies to the killed height bridge with both faces.

The one-dimensional reflection formula for the Dirichlet interval kernel
implies, for $0<t\le1$,

$$
h_I(t;k,k')\le C\phi(k)\phi(k')t^{-3/2}
                 e^{-c|k-k'|^2/t}.
\tag{41.4}
$$

For clarity, the usual reflection bound before this simplification is
$Ct^{-1/2}(1\wedge d(k)/\sqrt t)(1\wedge d(k')/\sqrt t)
 e^{-c|k-k'|^2/t}$, where $d(k)=\min(k-l,u-k)$.
It follows by pairing each reflected Gaussian with its negative image at
each endpoint; the mean value theorem bounds the paired differences by
the corresponding endpoint distance divided by $\sqrt t$, with polynomial
Gaussian derivatives absorbed by a larger Gaussian constant. The remaining
images are a convergent Gaussian series. Since $d\asymp\phi$, it gives
(41.4).

Split the fibre semigroup at $t/4,t/2,t/4$. The endpoint norms are bounded
by $h_I(t/2;k,k)^{1/2}\le C\phi(k)t^{-3/4}$, and (26.6) controls
the middle norm. Consequently
$e^{\lambda t}|K_{\kappa,\eta}(t;k,k')|
 \le Cp t^{-3/2}e^{-ct\Psi(|\eta|)}$ for $t\le1$.
Take the geometric mean with (41.4), using potential domination for that
second bound. The result retains $p t^{-3/2}$ and has both the height
Gaussian and $e^{-ct\Psi(|\eta|)}$, with smaller constants in the exponents.
For $t\ge1$ use (36.6) instead. The frequency integrals are respectively
bounded by $Ct^{-9/2}$ and $Ct^{-3/2}$. This explains the first power
$t^{-6}$ in (41.2) and gives the large-time on-diagonal bound.

All fibre kernels are entire in complex frequency: on every bounded
complex set their bounded-potential expansion converges in operator norm,
and endpoint splitting gives the same fact for kernels. Equation (41.3)
and the preceding integrable frequency bounds permit shifting the Fourier
contour to $\eta+i\rho$. One can first use finite rectangular contours;
the vertical face integrals vanish along expanding rectangles because
$e^{-ct\Psi(|\eta|)}$ dominates every polynomial, uniformly on a fixed
imaginary strip. The factor in inversion is then
$e^{-\rho\cdot r+C t|\rho|^2}$. Optimizing over all real $\rho$ gives
the first two lines of (41.2), retaining the height Gaussian in the first.

We give the band-error argument as well, since an on-diagonal heat limit
alone does not control its time integral. In a fixed complex ball write
$z=\eta+i\rho$. The bounded-potential Neumann series used in (36.7)
is analytic there and gives a bilinearly normalized analytic eigenfunction
$v_z$ and eigenvalue $\Lambda(z)$ satisfying

$$
\Lambda(z)=\lambda+z^{\mathsf T}M_\kappa z+O(|z|^4),\qquad
v_z(k)/\phi(k)=1+O(|z|^2).
\tag{41.5}
$$

The constants are uniform. Bilinear normalization means $\int_Iv_z^2=1$;
thus the rank-one kernel is $v_z(k)v_z(k')$, without complex conjugation.
The $H^2$ estimates and zero boundary values in (36.7) prove the displayed
pointwise quotient estimate also for complex $z$. The complementary
semigroup has bound $Cp e^{-(\lambda+d)t}$ for some $d>0$, $t\ge1$.
To see the needed uniform gap without an assumption on nonnormal spectra,
identify its spectral subspace with $\phi^\perp$ using the analytic Riesz
projection, which is $O(|z|^2)$ from the unperturbed projection. The
conjugated generator there is $H_I|_{\phi^\perp}$ plus a bounded
$O(|z|^2)$ operator. The unperturbed semigroup decays at $4\lambda$;
Duhamel's formula and Gronwall give decay at $4\lambda-C|z|^2$.
Endpoint splitting as above supplies the factors $p$. Choose the complex
ball small enough to leave a fixed positive $d$.

In a smaller real-frequency ball, subtract the Gaussian band, use (41.5),
and absorb the fourth-order real-frequency error into its positive
quadratic form. On the line $z=\eta+i\rho$ the integral of the absolute
error is at most

$$
Cp\,t^{-5/2}[1+(\sqrt t|\rho|)^4]e^{Ct|\rho|^2}
 +Cp e^{-dt+Ct|\rho|^2},\qquad |\rho|\le\rho_0.
\tag{41.6}
$$

Explicitly the pointwise integrand is bounded by
$Cp(|z|^2+t|z|^4)e^{-ct|\eta|^2+Ct|\rho|^2}$; integration of its
Gaussian moments gives (41.6). Outside that ball, (41.3), (36.6) and
$\Psi(|\eta|)\ge c_0>0$ give the second exponentially decaying term;
the Gaussian outside the ball has the same bound. Thus the complete
contour integral, rather than a truncated Fourier kernel, obeys (41.6).
Choose $\rho$ parallel to $r$ with length
$\min(\rho_1,|r|/(C_1t))$, with $\rho_1$ fixed sufficiently small and
$C_1$ sufficiently large. The Fourier factor absorbs the polynomial in
(41.6) and its exponential remainder. For $|r|\le C_1\rho_1t$ it gives
$Cp t^{-5/2}e^{-c|r|^2/t}$; on the complementary range it gives
$Cp t^{-5/2}e^{-c|r|}$. This proves the last line of (41.2).
No sum over height eigenfunctions or large-frequency remainder was omitted.
$\square$

## 42. The three-real-phase threshold Green law

**Theorem 42.1 (native Green asymptotics including zero mass).**
Put $d_\kappa(r)=\sqrt{r^{\mathsf T}M_\kappa^{-1}r}$. For $r\ne0$,

$$
Y_{\kappa,m}(r)=\int_0^\infty e^{-mt}\Gamma_{\kappa,t}(r)dt
=\frac{e^{-\sqrt m\,d_\kappa(r)}}
       {4\pi\sqrt{\det M_\kappa}\,d_\kappa(r)},\qquad m\ge0.
\tag{42.1}
$$

The actual native Green is finite at every distinct full point, including
$r=0$, $k\ne k'$, at $m=0$. Uniformly for every $m\ge0$, $|r|\ge1$,
$\kappa\in\mathcal K$ and both heights in $I$,

$$
|\mathcal G_{\kappa,m}(k,k';r)-pY_{\kappa,m}(r)|
\le Cp|r|^{-3}.
\tag{42.2}
$$

In particular, as $R\to\infty$,

$$
R\mathcal G_{\kappa,\mu/R^2}(k,k';Rz)
=p\frac{e^{-\sqrt\mu d_\kappa(z)}}
 {4\pi\sqrt{\det M_\kappa}\,d_\kappa(z)}+O(pR^{-2})
\tag{42.3}
$$

uniformly for $\mu$ in every compact subset of $[0,\infty)$ and $z$ in
every compact subset of $\mathbb R^3\setminus\{0\}$. The normalized error
is uniform even as either height approaches either absorbing face. No
relation between $R$ and $\kappa$ is required. For the original real lift,
replace the left side by
$|\kappa|R\mathcal G^{\rm orig}_{\kappa,\mu/R^2}
 (k,k';J_\kappa Rz)$ when $\kappa\ne0$.
Its tensor is exactly $J_\kappa M_\kappa J_\kappa^{\mathsf T}$,
including the signed cross terms in (39.1).

Proof. The first two lines of (41.2) prove off-diagonal finiteness at both
time endpoints. For the error on $t\ge1$, split at $t=|r|$ if $|r|\ge1$.
The part below that time is exponentially small in $|r|$, and the rest is
bounded by
$Cp\int_0^\infty t^{-5/2}e^{-c|r|^2/t}dt=C'p|r|^{-3}$.
The small-time native and Gaussian integrals are exponentially small for
$|r|\ge1$. Multiplication by $e^{-mt}\le1$ preserves every estimate,
including $m=0$. This proves (42.2). Formula (42.1) follows by substituting
$u=d_\kappa(r)/(2\sqrt t)$ in its Gaussian integral (or differentiating
that integral in $\sqrt m$ and fixing its value at zero).
It has the displayed unit-source constant because
$-\nabla\cdot M_\kappa\nabla+m$ becomes $-\Delta+m$ after
$r=M_\kappa^{1/2}y$, whose volume Jacobian is $\sqrt{\det M_\kappa}$.
The native unit-source identity is also retained at $m=0$:
$(B_\kappa-\lambda+m)\mathcal G_{\kappa,m}=\delta$
in distributions relative to raw measure. Integrate the heat equation
against a compactly supported smooth test; its boundary terms are the
unit delta at time zero and zero at infinity, the latter by (41.2).
Scaling proves (42.3); (39.1) proves its signed pushforward.
Thus the time-zero and time-infinity tails are controlled by native bounds,
not by a formal Laplace transform of (36.3). $\square$

**Proposition 42.2 (the projected pole is not a height-separated value).**
For $k\ne k'$, $\mathcal G_{\kappa,m}(k,k';0)$ is finite and strictly
positive for $m\ge0$. No finite value can be assigned to $Y_{\kappa,m}(0)$
to extend (42.3) to those points. In particular at fixed distinct heights
$R\mathcal G_{\kappa,\mu/R^2}(k,k';0)\to+\infty$.

Proof. The first line of (41.2) retains $e^{-c|k-k'|^2/t}$ and the second
is integrable. Positivity is inherited from the bracket-generating native
heat kernel. Dominated convergence at $m=0$ proves the last assertion.
The effective phase kernel has its genuine three-dimensional pole at zero.
As $r\to0$ with these distinct heights fixed, the native kernel stays
finite by the same local bounds, while $Y_{\kappa,m}(r)\to\infty$.
This is an obstruction in the original height-dependent model, not in a
replacement elliptic operator. Bounded or collapsing phase displacements
must therefore retain the native finite part specified in §44. $\square$

## 43. Two real visible phases and the actual hidden circle

**Definition 43.1 (exact cylinder, Fourier convention and response).**
For $\kappa\ne0$ set $a=|\kappa|$, $L=2\pi/a$, $w=(\theta,v)\in\mathbb R^2$
and $x=D/\kappa\in\mathbb R/(L\mathbb Z)$.
There is no wrapping of $\theta$ or $v$. The resolved raw measure is
$dk\,dw\,dx$; the original raw measure is $dk\,dw\,dD=a\,dk\,dw\,dx$.
The original positive-probability margin gives $\kappa_*<l/2<1/4$,
so the already fixed parameter interval has $L\ge1$.
Let $F^L_\kappa=e^{\lambda t}g^L_\kappa$. Exactly,

$$
\begin{aligned}
g^L_\kappa(t;k,k';w,x)
 &=\sum_{j\in\mathbb Z}g^I_\kappa(t;k,k';w,x+jL)\\
 &=\frac1{L(2\pi)^2}\sum_{j\in\mathbb Z}\int_{\mathbb R^2}
 e^{i\eta\cdot w+i\kappa jx}K_{\kappa,(\eta,\kappa j)}(t;k,k')d\eta,\\
g^{D}_\kappa(t;k,k';w,D)&=a^{-1}g^L_\kappa(t;k,k';w,D/\kappa).
\end{aligned}
\tag{43.1}
$$

Define $\mathcal G^L_{\kappa,m}=\int_0^\infty e^{-mt}F^L_\kappa dt$.
For $m>0$ and nonzero phase point modulo $L$, define the effective response

$$
E^L_{\kappa,m}(w,x)=\int_0^\infty e^{-mt}
       \sum_{j\in\mathbb Z}\Gamma_{\kappa,t}(w,x+jL)dt
 =\sum_{j\in\mathbb Z}Y_{\kappa,m}(w,x+jL).
\tag{43.2}
$$

Both expressions are nonnegative convergent expressions on that domain.
Their source is exactly $\delta_0(dw)\delta_0(dx)$ relative to raw
$dw\,dx$ on $\mathbb R^2\times(\mathbb R/L\mathbb Z)$:
$(-\nabla\cdot M_\kappa\nabla+m)E^L_{\kappa,m}=\delta_0$.
This follows by integrating its normalized heat equation; it includes
no angular probability-Haar factor and no height delta in the effective
operator. The native point source and its height factors are those in
(41.1) and (43.6).
Write the original tensor, without dropping any cross term, as

$$
M_\kappa=\begin{pmatrix}N_\kappa&h_\kappa\\h_\kappa^{\mathsf T}&d_\kappa^*\end{pmatrix},
\quad S_\kappa=d_\kappa^*-h_\kappa^{\mathsf T}N_\kappa^{-1}h_\kappa>0,
\quad y=x-h_\kappa^{\mathsf T}N_\kappa^{-1}w,\quad
b=\sqrt{w^{\mathsf T}N_\kappa^{-1}w}.
\tag{43.3}
$$

Here $d_\kappa^*$ is a tensor entry, not the distance in (42.1).
Uniform positivity of $M_\kappa$ bounds $N_\kappa,S_\kappa$ above and below.
The complete effective heat kernel is

$$
\Gamma^L_{\kappa,t}(w,x)
=\frac{e^{-b^2/(4t)}}{4\pi t\sqrt{\det N_\kappa}}\,
 \frac1L\sum_{j\in\mathbb Z}
 e^{-S_\kappa\kappa^2j^2t}e^{i\kappa jy}.
\tag{43.4}
$$

For $w\ne0$ its time integral also has the absolutely convergent expression

$$
E^L_{\kappa,m}(w,x)
=\frac1{2\pi L\sqrt{\det N_\kappa}}
 \sum_{j\in\mathbb Z}e^{i\kappa jy}
 K_0\!\left(b\sqrt{m+S_\kappa\kappa^2j^2}\right),
\quad
K_0(z)=\frac12\int_0^\infty s^{-1}e^{-s-z^2/(4s)}ds.
\tag{43.5}
$$

For $w=0$, $x\notin L\mathbb Z$, use (43.2), not an ordinary convergent
sum of separately integrated modes: each integral of (43.4)'s individual
mode then diverges at $t=0$.

Proof. Projecting the native stochastic law gives the first image identity
in (43.1); (41.2) makes its heat sum locally uniformly convergent.
Fourier transformation in $w$ and the raw circle Fourier series give its
second identity with exactly the displayed prefactor. The bound (36.6),
or its small-time version proved in Lemma 41.2, is integrable in $\eta$
and summable in $j$ at each $t>0$, so this is an identity of point kernels
for the complete operator. The sign of $\kappa$ reverses the hidden lattice
and is retained in $e^{ijD}$ and the cross terms. Its density factor is the
absolute Jacobian $a^{-1}$.

Tonelli gives (43.2). Completing the square in the two continuous Gaussian
frequencies yields (43.4), including the shift $y$ and the Schur complement.
Integrating a mode gives (43.5) by its displayed definition of $K_0$.
For $b>0$ the inequality $s+z^2/(4s)\ge z$ and a split at $s=z/2$
give exponential decay of $K_0(z)$ for large positive $z$, with a polynomial
factor; thus the full sum is absolutely convergent. If $b=0$, each mode
contains $\int_0^1dt/t=\infty$, whereas the image integral is finite at a
nonzero hidden separation. This explicitly identifies the failed
interchange, including visible-coincident hidden-separated points. $\square$

**Theorem 43.2 (native point comparison and the full crossover).**
Let $r_j=(w,x+jL)$ and suppose $\min_j|r_j|\ge1$. Then for every $m>0$,

$$
|\mathcal G^L_{\kappa,m}(k,k';w,x)-pE^L_{\kappa,m}(w,x)|
\le Cp\sum_{j\in\mathbb Z}|r_j|^{-3}.
\tag{43.6}
$$

For $m=\mu/R^2$, $w=Rz_w$, $x=Rz_x$ modulo $L$, and $\rho=L/R$,

$$
R\mathcal G^L_{\kappa,\mu/R^2}(k,k';Rz_w,Rz_x)
=pE^\rho_{\kappa,\mu}(z_w,z_x)
 +O\!\left(pR^{-2}\sum_{j\in\mathbb Z}|(z_w,z_x+j\rho)|^{-3}\right).
\tag{43.7}
$$

Here $E^\rho$ is exactly (43.2) with circumference $\rho$, tensor
$M_\kappa$ and mass $\mu$. This quantitative formula requires only the
stated minimum separation, and allows all relative rates and both signs.
In particular for $\mu$ in positive compact sets:

- If $\rho\to\infty$ and $z$ stays in a compact subset of
  $\mathbb R^3\setminus\{0\}$, then $E^\rho_{\kappa,\mu}(z)
  -Y_{\kappa,\mu}(z)\to0$ uniformly.
- If $\rho$ stays in a positive compact set, (43.7) is a uniform absolute
  approximation on compact phase sets separated from its wrapped pole.
  These sets may have $z_w=0$ and $z_x\notin\rho\mathbb Z$.
- If $\rho\to0$ and $z_w$ stays in a compact set bounded away from zero,
  uniformly in $z_x$ modulo $\rho$,

$$
L\mathcal G^L_{\kappa,\mu/R^2}(k,k';Rz_w,Rz_x)
-p\frac{K_0(\sqrt\mu\sqrt{z_w^{\mathsf T}N_\kappa^{-1}z_w})}
        {2\pi\sqrt{\det N_\kappa}}\longrightarrow0.
\tag{43.8}
$$

The third statement includes fixed nonzero $\kappa$ and $R\to\infty$.
It concerns long visible distance; it is not a native absolute
approximation at a fixed native endpoint. Original $D$ densities acquire
$a^{-1}$ in every statement.

Proof. Integrate the positive image identity by Tonelli. Apply (42.2) to
each image and sum its absolute error, whose $|j|^{-3}$ tail converges.
This proves (43.6). Scaling the explicit Gaussian response proves (43.7).
For the first endpoint, the noncentral Yukawa images are bounded by a
geometric exponential tail, uniformly on the prescribed mass and point
sets. In the second case the sum of inverse cubes is uniformly bounded.
For the third case comparison with the integral in the hidden variable gives

$$
\sum_j|(z_w,z_x+j\rho)|^{-3}\le C(1+\rho^{-1})
\tag{43.9}
$$

when $|z_w|\ge\delta>0$. After multiplying (43.7) by $\rho$, the
error is $O(pR^{-2}(1+\rho))$. In (43.5), with period $\rho$, all
nonzero modes decay exponentially in $|z_w|/\rho$; their complete sum
tends to zero after multiplication by $\rho$. The zero mode is precisely
the expression in (43.8). This proves all endpoints without deleting a
periodic phase or replacing a joint point kernel by a marginal. $\square$

**Proposition 43.3 (joint-point mixing scale).**
The hidden heat mixing coefficient in the native small-wall, long-time
joint-point regime is $S_\kappa$, not $d_\kappa^*=\langle b_\kappa^2\rangle$.
The scale is $a^2t$ with exponent $S_0a^2j^2t$ in the wall limit.
For a fixed small parameter, the bottom of hidden block $j$ is

$$
\Delta_j(\kappa)=\inf_{\eta\in\mathbb R^2}
       [\Lambda_\kappa(\eta,\kappa j)-\lambda],\qquad
\Delta_j(\kappa)=S_\kappa\kappa^2j^2+O((\kappa j)^4)
\quad(|\kappa j|\to0).
\tag{43.10}
$$

The slowest nonzero block has gap comparable to $a^2$.
Neither equality of its exact fixed-parameter gap with $S_\kappa a^2$,
nor equality with the fully wrapped trace coefficient of G §33, is claimed.

Proof. For $\xi$ small, uniform coercivity excludes minimizers outside a
fixed small frequency ball. In that ball (36.4) and positivity of its
Hessian give the unique minimizing visible frequency
$\eta=-N_\kappa^{-1}h_\kappa\xi+O(\xi^3)$ by the implicit function
theorem. Substitution gives $S_\kappa\xi^2+O(\xi^4)$.
Coercivity (26.6) gives $\Delta_j\ge c\Psi(a|j|)$ for all $j$;
the trial frequency at $j=1$ gives the matching $Ca^2$ upper bound.
Thus the gap and all other blocks are controlled, not only finitely many.
For joint point heat kernels (43.4) displays the coefficient directly.
The periodized last line of (41.2) has error at most
$Cp t^{-5/2}(1+\sqrt t/L)$, uniformly in phases: to bound its image sum,
split $|r_j|\le t$ and its complement, compare the Gaussian part with its
one-dimensional integral, and sum the exponential tail. At
$t=s/a^2$, $s$ in a positive compact set, this is smaller by a factor
$O(a^2)$ than the main $t^{-1}/L$ scale. Hence (43.4) supplies the
actual native joint-point scaling there. By contrast integration over
visible endpoints forces $\eta=0$ before expansion and gives
$d_\kappa^*$; fully wrapping them also removes the continuous saddle.
Those operations do not compute this joint-point coefficient.
Indeed $\langle A_\kappa b_\kappa\rangle>0$ by the original positive
coefficients, so $h_\kappa\ne0$ and $S_\kappa<d_\kappa^*$ strictly.
$\square$

## 44. Native finite parts, collapsed sources and the zero-mass tail

**Theorem 44.1 (an exact composite formula on the whole off-diagonal domain).**
For every $L=2\pi/|\kappa|$, define

$$
\begin{aligned}
H^L_{\kappa,m}(w,x)&=\int_1^\infty e^{-mt}\Gamma^L_{\kappa,t}(w,x)dt,\\
C^L_{\kappa,m}(k,k';w,x)
&=\int_0^1 e^{-mt}F^L_\kappa(t;k,k';w,x)dt\\
&\quad+\int_1^\infty e^{-mt}
  [F^L_\kappa(t;k,k';w,x)-p\Gamma^L_{\kappa,t}(w,x)]dt.
\end{aligned}
\tag{44.1}
$$

At every distinct full point, including $w=x=0$ with $k\ne k'$, the
second quantity is finite for all $m\ge0$ and continuous at $m=0$.
For $m>0$ the following is an exact equality:

$$
\mathcal G^L_{\kappa,m}=C^L_{\kappa,m}+pH^L_{\kappa,m}.
\tag{44.2}
$$

In particular (44.2), rather than an evaluation at an effective phase pole,
is the native formula in the height-only and source-collapse layers.
The short-time term in $C^L$ is strictly positive; it is not discarded.
For nonzero phase points the alternative finite correction
$C^L_{\kappa,m}-p\int_0^1e^{-mt}\Gamma^L_{\kappa,t}dt$
may be added to $pE^L_{\kappa,m}$.

Proof. Periodize (41.2). The time-large error has absolute bound
$Cp[t^{-5/2}+L^{-1}t^{-2}]$, integrable independently of $m\ge0$.
The small-time native bound is a convergent sum of
$Cp t^{-6}e^{-c(|r_j|^2+|k-k'|^2)/t}$.
It is integrable precisely on the stated off-diagonal domain, locally
uniformly on its compact subsets. This proves existence and continuity
by dominated convergence. Splitting the native integral at one and adding
and subtracting its effective large-time kernel proves (44.2).
The cutoff at one is fixed in the original clock and defines the finite
part's normalization; it is not a new physical resolution or clock.
Other positive splitting times give the same equality with correspondingly
changed summands.

This correction cannot uniformly be replaced by zero at fixed native
endpoints. Fix $k\ne k'$, $m>0$ and a nonzero small phase vector tending
to zero. The native Green stays finite, whereas the central effective
Yukawa image diverges. Thus their difference is nonzero and unbounded
on this family. This proves failure of a uniform effective absolute
approximation in the actual model, even at fixed $\kappa$.
If heights also coalesce, the original native point singularity remains;
(44.1) retains it rather than changing its local homogeneous dimension.
$\square$

**Theorem 44.2 (positive logarithmic infrared tail and its normalization).**
For each fixed nonzero $\kappa$, each fixed pair of heights and phases,

$$
F^L_\kappa(t;k,k';w,x)
=\frac{A_\kappa(k,k')}{t}+O(t^{-2}),\qquad
A_\kappa(k,k')=\frac{p}{4\pi L\sqrt{\det N_\kappa}}>0.
\tag{44.3}
$$

The remainder is locally uniform in points, including distinct heights
at coincident phases; fixed-parameter constants are allowed here.
Consequently $\mathcal G^L_{\kappa,0}=+\infty$ at every point.
There is no finite nonnegative threshold Green on this cylinder.
At distinct full points the precisely normalized subtraction is

$$
\begin{aligned}
\mathcal G^L_{\kappa,m}-A_\kappa\log(1/m)&\longrightarrow
\mathfrak F^L_\kappa,\qquad m\downarrow0,\\
\mathfrak F^L_\kappa
&=\int_0^1F^L_\kappa(t)dt
 +\int_1^\infty[F^L_\kappa(t)-A_\kappa/t]dt
 -\gamma A_\kappa,
\end{aligned}
\tag{44.4}
$$

where $\gamma=-\lim_{m\downarrow0}
 [\int_1^\infty e^{-mt}dt/t+\log m]$ is Euler's constant.
The finite part may have either sign and is not a nonnegative Green.
For original raw $D$ measure the logarithmic coefficient is
$p/(8\pi^2\sqrt{\det N_\kappa})$.

Proof. In (43.4) the zero hidden mode is
$(4\pi L t\sqrt{\det N_\kappa})^{-1}e^{-b^2/(4t)}$;
all other modes have exponential suppression for fixed $L$.
The periodized band error is $O(p[t^{-5/2}+L^{-1}t^{-2}])$.
This proves (44.3) directly for the native kernel with no marginalization.
Its positive leading coefficient proves divergence, independently of the
small-time behavior. Subtract $A_\kappa/t$ only on $t\ge1$;
the remaining integrals are absolutely convergent off the full source.
The elementary exponential-integral identity defining $\gamma$ proves
(44.4) by dominated convergence. Finally divide by $a$ and use $aL=2\pi$.
The logarithm uses the fixed mass unit of (41.1); replacing that unit changes
the finite part by the corresponding explicit multiple of $A_\kappa$.
$\square$

**Theorem 44.3 (simultaneous zero mass and hidden decompactification).**
Let $L\to\infty$, $\kappa=\pm2\pi/L$, and $m=m(L)>0$ arbitrary.
For full points in a fixed compact off-diagonal set and a bounded chosen
phase representative $r=(w,x)$, uniformly in both signs,

$$
\begin{aligned}
\mathcal G^L_{\kappa,m}(k,k';w,x)
&=\mathcal G_{\kappa,m}(k,k';w,x)+pT_\kappa(L,m)+O(pL^{-2}),\\
T_\kappa(L,m)
&=-\frac1{2\pi L\sqrt{\det N_\kappa}}
       \log\!\left(1-e^{-L\sqrt{m/S_\kappa}}\right).
\end{aligned}
\tag{44.5}
$$

The formula retains $r=0$, $k\ne k'$. Its error is uniform in $m>0$;
it does not require $L\sqrt m$ bounded away from zero. When
$L\sqrt m\to0$ its additional tail is

$$
T_\kappa(L,m)=\frac1{2\pi L\sqrt{\det N_\kappa}}
 \log\!\frac{\sqrt{S_\kappa}}{L\sqrt m}+o(L^{-1}).
\tag{44.6}
$$

Thus this tail can vanish, converge to a nonzero constant, or diverge.
For example $m=L^{-4}$ gives a vanishing tail,
$m=L^{-2}e^{-cL}$ gives $c/(4\pi\sqrt{\det N_0})$ for $c>0$,
and $m=L^{-2}e^{-L^2}$ gives a tail growing as
$L/(4\pi\sqrt{\det N_0})$.
The product $|\kappa|R$ alone does not determine a simultaneous
zero-mass/decompactification limit when $mR^2$ may also tend to zero.
More generally, for $|r|\le c_0L$ with one sufficiently small fixed $c_0$,
the error in the first line of (44.5) is bounded by
$Cp(|r|L^{-2}+L^{-3})$. Hence the same additional tail also controls
long-distance sequences $r=Rz$, $L/R\to\infty$: after multiplication
by $R$ their error is $O(p[(R/L)^2+R/L^3])$ for bounded $z$.
The central native term remains exact even at phase-coincident points.

Proof. Keep the central image as the exact native Green, also when its
phase vector is zero. For every noncentral image (42.2) has summable error
$O(pL^{-3}|j|^{-3})$. Replace those images by their Yukawa values.
For $r=0$ their sum is exactly $T_\kappa(L,m)$, because
$(M_\kappa^{-1})_{33}=1/S_\kappa$ and
$\det M_\kappa=(\det N_\kappa)S_\kappa$, so the paired $j$ terms are

$$
\frac1{2\pi L\sqrt{\det N_\kappa}}
 \sum_{j\ge1}\frac{e^{-jL\sqrt{m/S_\kappa}}}{j}.
\tag{44.7}
$$

The series is $-\log(1-e^{-L\sqrt{m/S_\kappa}})$ for every $m>0$.
Moving its argument by bounded $r$ changes each image by at most
$C|r|/(jL)^2$, uniformly in $m$: differentiate
$e^{-\sqrt m s}/s$ and use $(1+\sqrt m s)e^{-\sqrt m s}\le C$.
Summing these errors proves (44.5). Expanding $1-e^{-b}=b(1+O(b))$
proves (44.6) and its examples. If also $m\to0$, the central native term
converges to its finite zero-mass value, uniformly on these compact
sets, by (41.2). This proves the stated distinct outcomes in the original
native cylinder, rather than merely in an effective comparison.
For instance take the same $R=L^2$ in the last two exponential examples:
$|\kappa|R=2\pi L$ is identical, while their additional tails differ.
$\square$

**Proposition 44.4 (hidden separation with coincident visible point).**
Let $w=0$, $x=\alpha L$, $\alpha$ in a compact subset of $(0,1)$,
and $b_0=L\sqrt{m/S_\kappa}>0$. Then

$$
\begin{aligned}
E^L_{\kappa,m}(0,\alpha L)
 &=\frac1{4\pi L\sqrt{\det N_\kappa}}
   \sum_{j\in\mathbb Z}\frac{e^{-b_0|j+\alpha|}}{|j+\alpha|},\\
\sum_{j\in\mathbb Z}\frac{e^{-b_0|j+\alpha|}}{|j+\alpha|}
 &=-2\log b_0+\mathcal P(\alpha)+o(1),\qquad b_0\downarrow0,\\
\mathcal P(\alpha)&=\frac1\alpha+
 \sum_{j\ge1}\left(\frac1{j+\alpha}+\frac1{j-\alpha}-\frac2j\right).
\end{aligned}
\tag{44.8}
$$

The last series converges absolutely and uniformly on these compact sets.
For $L\to\infty$, the actual native value is $p$ times the first line
plus $O(pL^{-3})$, uniformly for all $m>0$. For fixed $L$, the finite
native correction in (44.1) must instead be retained; it does not vanish
merely because $m\downarrow0$.

Proof. At $w=0$, $d_\kappa(0,x)=|x|/\sqrt{S_\kappa}$;
(43.2) therefore gives the first line. Subtract
$2\sum_{j\ge1}e^{-b_0j}/j=-2\log(1-e^{-b_0})$.
The difference tends to $\mathcal P(\alpha)$: its zero-mass paired
terms are $O(j^{-3})$, and the derivatives of the exponential terms add
bounds $C b_0 e^{-c b_0j}/j$ and $C b_0^2e^{-c b_0j}$, whose sums tend
to zero. This justifies the limit uniformly in $\alpha$, not a termwise
sum of divergent integrated modes. Finally (43.6) has error
$CpL^{-3}\sum|j+\alpha|^{-3}$. This proves the native assertion and
explains its fixed-parameter limitation. $\square$

## 45. Killing, threshold recurrence and the actual zero leaf

**Theorem 45.1 (source factors, finite lifetime and different infrared laws).**
The following statements refer to the unchanged original clock and both
absorbing faces.

1. On each cover or quotient used here, the unshifted killed Green has
   finite off-diagonal values and total raw mass

$$
\int G^{\rm killed}(k,q;k',q')\,dk'\,dq'
=\mathbb E_k\zeta=\frac{(k-l)(u-k)}{2\varepsilon^2}.
\tag{45.1}
$$

   It is the unit-source inverse of the original $B_\kappa$.
   It has no unshifted Coulomb tail: on the resolved real cover its
   large-phase value is bounded by $Cp e^{-c|r|}$ for $|r|\ge1$.
2. The resolved three-real-phase Q law is transient, with a finite
   zero-mass off-diagonal Green and the rank-three anisotropic infrared
   coefficient (42.3). The two-visible-real/hidden-periodic Q law is
   recurrent with infinite invariant measure and has the logarithmic
   threshold divergence (44.3)--(44.4).
3. On the actual native zero leaf, $D$ is frozen. Its two-real-phase cover
   has tensor $N_0$ from (39.3), not a third diffusing coordinate.
   Its threshold and Q Greens diverge logarithmically at zero mass, with
   raw threshold coefficient $p/(4\pi\sqrt{\det N_0})$ multiplying
   $\log(1/m)$. For $\mu$ in positive compact sets and $z\ne0$ in
   compact sets,

$$
\mathcal G^{\rm leaf}_{\mu/R^2}(k,k';Rz)
\longrightarrow
\frac{p}{2\pi\sqrt{\det N_0}}
 K_0\!\left(\sqrt\mu\sqrt{z^{\mathsf T}N_0^{-1}z}\right).
\tag{45.2}
$$

   There is no extra factor $R$. A finite part is normalized exactly as
   in (44.4) with the stated leaf coefficient. The original unshifted
   leaf Green remains finite and has (45.1), as already supplied in
   G §§9--11. In the original four-coordinate space its law carries
   $\delta_{D_0}(dD')$, not a four-dimensional raw density.

Proof. Integration over phases in any of these stochastic laws gives
exactly the original killed height Brownian motion. Tonelli therefore
reduces the total Green mass to $\int_0^\infty S_k(t)dt$.
The function on the right of (45.1) is the unique zero-boundary solution
of $-\varepsilon^2f''=1$; the stopped Itô formula, or integration of
the height sine kernel, identifies it with $\mathbb E_k\zeta$.
This proves its normalization without conditioning or source renormalization.
The first two lines of (41.2), now multiplied by $e^{-\lambda t}$,
give finiteness and exponential large-phase decay by splitting the integral
at a constant multiple of $|r|$, or using
$\lambda t+c|r|^2/t\ge c'|r|$.
The same reasoning applies after periodization and to the leaf.

The Q factors are exactly those in Definition 41.1; dividing the real-cover
heat bound by $p$ bounds its occupation of every finite-reference-measure
set at large times by $Ct^{-3/2}$, which is integrable. Small-time occupation
is finite off the starting point. This is transience of its irreducible
symmetric Q process. For the cylinder and leaf, recurrence can also be
checked independently of a point Green calculation. In Q reference measure
take cutoff functions independent of height (and of the hidden circle),
equal to one for visible radius at most $n$, zero beyond $n^2$, and linear
in $\log|w|$ on the intervening annulus. Their energies are at most
$C\int_{n<|w|<n^2}|w|^{-2}(\log n)^{-2}dw\le C/\log n$;
the finite height mass is one, and the circle contributes its fixed length.
These cutoffs increase to one after taking a monotone radial choice.
The symmetric Markov form recurrence criterion identifies recurrence
from precisely this approximation of one by bounded form-domain functions
of vanishing energy. Its hypotheses hold here: multiplication by $\phi$
is the unitary ground-state transform of the original closed regular form,
compactly supported smooth height approximations to $\phi$ show that the
displayed cutoffs are in its domain, and the native positive kernel gives
irreducibility. Conservativity was proved in §37.
Equivalently, a finite-energy zero potential $u$ of a nonzero nonnegative
compactly supported test $f$ would satisfy
$|\int f\chi_n\,d\mu^Q|^2
 \le \mathcal E^Q(u,u)\mathcal E^Q(\chi_n,\chi_n)\to0$,
contrary to $\int f>0$; this is the potential-theoretic content of the
criterion for this irreducible form.
There is no invariant probability: its two-real-phase heat bound tends
to zero on every set of finite reference measure, by the same exhaustion
argument as in (37.9). Thus recurrence here has infinite invariant measure.

For the leaf, restrict every scalar-fibre argument of Lemma 41.2 to
$\eta=(\eta_1,\eta_2,0)$. The native independence of its two coefficients
and its tensor are already proved in (39.3). The identical contour proof
now has two frequency integrals; at $t\ge1$ it gives
$Cp t^{-1}e^{-c|w|^2/t}$ and band error
$Cp t^{-2}e^{-c\min(|w|^2/t,|w|)}$. The small-time bound has some
finite polynomial power and the same full off-diagonal Gaussian factors,
by the same scalar splitting. Integrating the band error at $|w|\ge1$
gives $Cp|w|^{-2}$, uniformly in mass. Integrating its Gaussian main term
with $m=\mu/R^2$, $w=Rz$ gives (45.2) by the definition of $K_0$.
At fixed $w$, the native compensated heat is
$p/(4\pi\sqrt{\det N_0}\,t)+O(t^{-2})$; the proof of (44.4) gives
its logarithm and finite part. This proves all the new threshold assertions
without repeating the supplied unshifted stability/binding proofs.
$\square$

**Theorem 45.2 (fully wrapped poles and their domains).**
At each fixed nonzero $\kappa$, on the original fully wrapped
$I\times\mathbb T^3$ with raw measure, write $\mathcal G^{\rm wr}_{\kappa,m}$
for its threshold resolvent. Off the full source,

$$
\mathcal G^{\rm wr}_{\kappa,m}(k,q;k',q')
=\frac{p}{(2\pi)^3m}+\mathfrak R_\kappa(k,q;k',q')+o(1),
\qquad m\downarrow0,
\tag{45.3}
$$

where
$\mathfrak R_\kappa=\int_0^\infty
 [e^{\lambda t}p^{\rm wr}_\kappa(t)-p/(2\pi)^3]dt$.
The fully wrapped actual zero leaf has the analogous formula with
$(2\pi)^2$ instead of $(2\pi)^3$. Their Q laws are positive recurrent,
with invariant probabilities $\phi(k')^2dk'\,dq'/(2\pi)^d$, $d=3,2$.
Their Q reference Green poles are $1/((2\pi)^dm)$ and raw Q poles
$\phi(k')^2/((2\pi)^dm)$. Zero-mass threshold and Q kernels diverge.
These fixed-parameter finite parts are not uniform assertions across
$\kappa=0$.

Proof. The ground eigenfunction in G Theorem 26.1 is
$(2\pi)^{-3/2}\phi$ and its remaining spectral gap is comparable to
$a^2$; its complete Fourier estimates give exponential convergence to
$p/(2\pi)^3$ at fixed $a>0$. Integrating the ground term gives its exact
pole. The remainder is integrable at infinity, and is integrable at zero
off the full source by the native local bounds and image formula.
This proves (45.3), including the specified finite part. At zero use the
actual leaf heat limit (39.4) and its positive gap for the nonzero visible
lattice modes; the same proof has two angular factors. Applying (37.2)
gives the two Q density conventions and normalized invariant measures.
Conservativity, irreducibility and this finite invariant measure give
positive recurrence. The gap shrinks as $a\to0$, and the actual zero law
has a frozen-coordinate delta, so these formulas cannot be passed to zero
as raw four-dimensional point densities. In particular this compact pole
is not the logarithm of the two-real-phase cylinder. $\square$

## 46. What the Green bridge establishes about three dimensions

**Proposition 46.1 (cover-dependent infrared rank and preserved obstructions).**
The new Green conclusion is an anisotropic rank-three threshold infrared
law on the declared all-real winding cover, with tensor exactly (36.1).
Its Coulomb endpoint is the zero-mass response (42.1), multiplied by the
original height/source factors. Restoring the actual hidden circle yields
the crossover (43.7), the joint-point coefficient $S_\kappa$, and a
logarithmic zero-mass tail. Restoring all actual periods yields the compact
pole (45.3). Restoring the actual zero leaf leaves only two moving phases.
Keeping the original killing without a threshold shift instead gives a
finite-lifetime Green with exponentially suppressed far field.

None of these assertions selects a physical spatial dimension or changes
the instantaneous rank two in (40.1). They supply no winding acquisition,
conditioning service, physical $SO(3)$ invariance, additional control,
new attractive interaction, or new binding/stability theorem.
The full point-attraction collapse away from the double wall, the strict
stable double-wall regime, the actual leaf-cover binding results and the
heat-cutoff classification in G remain their supplied statements with their
original domains, source conventions and hypotheses.

Proof. The changes of geometry, spectral parameter and reference measure
are explicit in (41.1), (43.1), (44.3), (45.1)--(45.3).
Their different finite, logarithmic and pole behaviors prohibit identifying
them as one unshifted field. The resolved tensor averages the original
rank-one phase covariance over height histories, as proved in (40.1);
its long-time rank does not alter the same-clock symbol. The signed
coordinate map changes covariance by congruence and density by its absolute
Jacobian, not by an additional actuator. The retained conclusions about
native operations and physical interpretation are therefore exactly the
obstructions in §40, N Theorem 10.5 and F. Attraction is absent from all
operators in this appendix, so the cited attraction results are reused
without a new inference about their stability. $\square$

## 47. Mathematical suppliers and the scope of the bridge

**Mathematical correspondence 47.1 (reuse and classical comparisons).**
The source snapshots for the native premises are the six indicated volumes
at commit
[`b669ef36ee32627638ed55edc90152bf606a9df0`](https://github.com/the-omega-institute/trureturing/tree/b669ef36ee32627638ed55edc90152bf606a9df0/docs/develop/theory).
The mathematical dependencies and limits of comparison are as follows.

| Supplier | Precise role and applicability |
| --- | --- |
| G Definition 25.1, (26.5)--(26.12), (32.2) | Original rational coefficients, fixed interval, raw measures, both deaths, all-real-frequency coercivity and uniform bracket independence. Lemma 41.2 extends their scalar argument to a spatial estimate and an integrable band error; no elliptic heat bound is assumed for the rank-two native operator. |
| This volume §§35--40 | The tensor, signed pushforward, point heat limit and Q/source conventions are reused. The new inference is the all-time Green comparison, its periodic crossover and its corrected finite parts, not another derivation of that tensor or heat limit. |
| C (32.4)--(32.5) | Isolated scalar Dirichlet band perturbation is reused through the multivariate proof already in §36. Its visible-zero-block coefficient is not the joint-point Schur complement. |
| N Theorems 10.3 and 10.5; F §§2--3 | Native controls and same-clock symbol/quotient boundaries. They do not identify a hidden integral with a full point response. |
| S §50 | A finite-state FIB chain with a different mixed height boundary. Its quasi-stationary and Doob constructions are comparisons, not a supplier of the present two-Dirichlet-face Green. |
| X. Geng and G. Iyer, *Long Time Asymptotics of Heat Kernels and Brownian Winding Numbers on Manifolds with Boundary*, [arXiv:1804.00368v1, Theorem 2.1, §2](https://arxiv.org/html/1804.00368v1) | Compact smooth Riemannian base, finitely generated abelian deck group and Laplace--Beltrami operator with mixed Dirichlet/Neumann conditions. The native four-dimensional symbol has rank two and is not that elliptic operator. The comparison explains the ground-band method but supplies neither Lemma 41.2 nor its time-integrated uniformity. |
| M. Kha, *Green's function asymptotics of periodic elliptic operators on abelian coverings of compact manifolds*, [arXiv:1511.00276v3, Theorem 3.4 and Assumption A1--A4](https://arxiv.org/html/1511.00276v3) | Spectral-edge Green asymptotics for a second-order periodic selfadjoint elliptic operator, deck rank at least three, a unique nondegenerate band minimum and separation from other bands. Its effective Hessian is a useful comparison, but native ellipticity fails. Its theorem does not prove a uniform small-wall result for this hypoelliptic family or a rank-two cylinder endpoint. |
| T. Ballu, *Asymptotics of Green functions for Markov-additive processes: an approach via dyadic splitting of integrals*, [arXiv:2407.10685v2, Theorem 1.5, Assumptions 1.2 and 1.4](https://arxiv.org/html/2407.10685v2) | Irreducible aperiodic discrete-time process on $\mathbb Z^d\times\{1,\ldots,p\}$, finite exponential moments and nonzero stationary drift. Here height is continuous and the conservative Q additive martingale is centered. Its noncentered Green theorem cannot be applied by naming this a Markov-additive process. |
| N. Champagnat and D. Villemonais, *Exponential convergence to quasi-stationary distribution and Q-process*, [arXiv:1404.1349v2, Theorem 3.1(ii)--(iii), Assumption (A)](https://arxiv.org/html/1404.1349v2) | The transform formula has the same algebra as (37.2). Their uniform conditional minorization/mixing hypothesis is not available for phase translations on this noncompact cover; its probability-invariant conclusion is not imported. The height and fully wrapped invariant probabilities here are computed directly. |

The classical reflection, bounded-potential product formula, analytic
simple-eigenvalue perturbation, Fourier inversion, Gaussian integration
and recurrence criterion are tools, not new general results.
For the last criterion the precise classical statement is
Fukushima--Oshima--Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
[second revised and extended edition (2011)](https://doi.org/10.1515/9783110218091),
Theorem 1.6.3: recurrence is
equivalent to a sequence $0\le u_n\le1$ in the form domain tending to one
almost everywhere with $\mathcal E(u_n,u_n)\to0$. This is applied to the
conservative regular symmetric Q form, not to the killed form. In particular
the symmetric-form criterion used in Theorem 45.1 is the equivalence between
recurrence and existence of bounded form-domain functions tending to one
with energies tending to zero; it applies to the conservative symmetric
regular Q form. The displayed logarithmic cutoffs check that criterion
for the actual cylinder and leaf, including their height reference weight.
The explicit $K_0$ integral in (43.5) fixes its normalization without
requiring a special-function convention from a secondary source.

The native assertions are repository-derived ordinary mathematical proofs.
The comparison results above do not certify the new global estimates.
No exhaustive literature survey or originality certification follows from
these correspondences. The three-phase Coulomb law is conditional on the
specified cover, threshold shift, covariance, density, clock and source;
the physical and operation boundaries in §46 remain part of its statement.

## 追加锚（本行以下为增补区）
