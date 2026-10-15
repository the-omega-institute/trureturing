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
