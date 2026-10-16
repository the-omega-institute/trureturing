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

## 48. Ground-height response in the original domains

**Definition 48.1 (source, compression and stationary law).** Retain all
of Definition 35.1, including the fixed two-sided interval $\mathcal K$,
the original clock and both absorbing faces. Write $d=u-l$,
$\gamma=3\lambda$, $J=\int_I\phi(k)dk$, and
$\pi(dk)=\phi(k)^2dk$. References G, N, F and C retain their meanings
in §35; write Q for
[Quantitative native long-time phase paths and terminal heights](FIB_NATIVE_LONG_TIME_PHASE_QUANTITATIVE_BOUNDS.md).
Write O for
[Native observation quotient, hidden Green harmonics and attractive response](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md).
Its attractive compression and restricted-source conclusions retain their
separate hypotheses; no attractive potential is inserted here.
The native statements used here are those at the immutable revision
[`8f6e990562ff8d80f0e8a1715512cf18791a101d`](https://github.com/the-omega-institute/trureturing/tree/8f6e990562ff8d80f0e8a1715512cf18791a101d/docs/develop/theory):
G Definition 25.1, N's native constant relation, F Proposition 5.1,
this volume §§35–47, and Q §§41–46. In particular, the previous Green
appendix and the Q endpoint upper estimate are premises, not additional
conclusions of the present construction.

Here are the actual operator conventions. On $L^2(I,dk)$ put

$$
\begin{aligned}
H_I&=-\varepsilon^2\partial_k^2,
& D(H_I)&=H^2(I)\cap H_0^1(I),\\
A&=H_I-\lambda,
& P&=|\phi\rangle\langle\phi|,\qquad P^\perp=1-P,\\
v_{\kappa,\eta}(k)&=(\eta\cdot c_\kappa(k))^2,
& T_{\kappa,\eta}&=A+v_{\kappa,\eta}.
\end{aligned}
\tag{48.1}
$$

Every real frequency $\eta\in\mathbb R^3$ has the same Dirichlet
operator domain $D(H_I)$ and form domain $H_0^1(I)$; its potential is
bounded for that frequency. The full killed operator $L_\kappa$ on
$L^2(I\times\mathbb R^3,dk\,dq)$ is the Friedrichs operator of
(35.1). More explicitly, its Fourier-side form domain consists of the
functions with $\widehat f(\eta)\in H_0^1(I)$ almost everywhere and

$$
\int_{\mathbb R^3}\int_I
 \left(\varepsilon^2|\partial_k\widehat f|^2+
 v_{\kappa,\eta}|\widehat f|^2\right)dk\,d\eta<\infty.
\tag{48.2}
$$

Its operator domain consists of $\widehat f(\eta)\in D(H_I)$ almost
everywhere with
$\int\|(H_I+v_{\kappa,\eta})\widehat f(\eta)\|_2^2d\eta<\infty$.
Fourier Plancherel constants are understood as in (36.5).
These are direct-integral domains, not isotropic four-dimensional
Sobolev assertions. Define the isometry
$\mathcal J h(k,q)=\phi(k)h(q)$ and the bounded compression

$$
\begin{aligned}
C_\kappa(t)&=\mathcal J^*e^{-t(L_\kappa-\lambda)}\mathcal J,\\
u_\kappa(t,\eta)&=\langle\phi,e^{-tT_{\kappa,\eta}}\phi\rangle,\\
\mathfrak m_\kappa(t,r)&=
 e^{\lambda t}\int_{I^2}\phi(k)g_\kappa^I(t;k,k';r)
                      \phi(k')dk\,dk'.
\end{aligned}
\tag{48.3}
$$

Thus $C_\kappa(t)$ is convolution by the probability measure
$\mathfrak m_\kappa(t,dr)$ and has multiplier $u_\kappa(t,\eta)$.
At $t=0$ that measure is $\delta_0$; positive-time densities in (48.3)
are taken in raw $dr$. No hidden circle has been averaged.

The generic Schur/Feshbach elimination used below is credited to
Dusson–Sigal–Stamm,
[*The Feshbach–Schur map and perturbation theory*, arXiv:2105.02058v1,
Theorem 1.2](https://arxiv.org/html/2105.02058v1).
The distinction between projected and orthogonal evolution is also
standard in Gouasmi–Parish–Duraisamy,
[*A priori estimation of memory effects in coarse-grained nonlinear
systems using the Mori–Zwanzig formalism*, arXiv:1611.06277v2](https://arxiv.org/html/1611.06277v2).
Here the bounded potential on each fixed original Dirichlet domain
allows an explicit construction; an unbounded global block matrix is
not an additional premise.

**Theorem 48.2 (exact raw-source, killed and Q correspondence).** For
all $t\ge0$ and real $\eta$, (48.3) is exactly the characteristic
function and endpoint law of $q_t-q_0$ under the Q-process initialized
with height $K_0\sim\pi$. In particular it is stationary in height,
although the real phases themselves have no invariant probability.
The unshifted ground-height response is $e^{-\lambda t}\mathfrak m_\kappa(t)$.
For an integrable phase source $\rho$, the original raw source
$\sigma(k,q)=\phi(k)\rho(q)$ has total charge $J\int\rho$, and

$$
\int_I\phi(k')\big(e^{-tL_\kappa}\sigma\big)(k',q')dk'
 =e^{-\lambda t}(\mathfrak m_\kappa(t)*\rho)(q').
\tag{48.4}
$$

Its ground-height readout has total mass $e^{-\lambda t}\int\rho$;
this is different from the total raw charge of the source.

More generally, for nonnegative height weights $a,b$, the exact
identity, whenever the integrals are finite, is

$$
\begin{aligned}
&e^{\lambda t}\int_{I^2}a(k)g_\kappa^I(t;k,k';r)b(k')dk\,dk'\,dr\\
&\quad=
\mathbb E_\pi^Q\left[
 \frac{a(K_0)}{\phi(K_0)}\frac{b(K_t)}{\phi(K_t)}
 \mathbf1_{\{q_t-q_0\in dr\}}\right].
\end{aligned}
\tag{48.5}
$$

Signed weights follow by absolute integrability. In particular, a fixed
initial height has the raw point-source identity

$$
e^{\lambda t}\int_I g_\kappa^I(t;k_0,k';r)dk'\,dr
 =\phi(k_0)\mathbb E_{k_0}^Q\left[
 \phi(K_t)^{-1}\mathbf1_{\{q_t-q_0\in dr\}}\right].
\tag{48.6}
$$

The original killed total mass here is $S_{k_0}(t)$, not one.
Normalization by that survival probability gives the terminal-survivor
law of §37, not (48.3). Even starting the killed height from the
normalized source $\phi/J$ gives instead the terminal-survivor multiplier

$$
\frac1J\langle\phi,e^{-tT_{\kappa,\eta}}1\rangle;
\tag{48.7}
$$

its survival probability is exactly $e^{-\lambda t}$. These source and
terminal weights cannot be discarded.

For $\kappa\ne0$, put $J_\kappa=\operatorname{diag}(1,1,\kappa)$ as in
§39. The original lifted compressed density is
$|\kappa|^{-1}\mathfrak m_\kappa(t,J_\kappa^{-1}y)$ in raw $dy$.
On the actual three phase circles, all of period $2\pi$, its Fourier
coefficients are exactly

$$
u_\kappa(t,(n,m,\kappa j)),\qquad (n,m,j)\in\mathbb Z^3.
\tag{48.8}
$$

The corresponding Fourier series uses $(2\pi)^{-3}$ in raw angular
measure; the unshifted version has the additional $e^{-\lambda t}$.
At the actual zero leaf use only the two moving phases, restrict to
$\eta=(\eta_1,\eta_2,0)$, and attach $\delta_{D_0}(dD')$.
This is different from keeping the resolved three-phase zero cover.

Proof. The raw Q transition density in (37.2) is
$e^{\lambda t}\phi(k')g_\kappa^I(t;k,k';r)/\phi(k)$.
Multiplying by $\pi(dk)$ gives exactly the integrand in (48.3).
Conservativity proves its mass one, and Fourier transformation gives
$u_\kappa$. This also constructs the bounded convolution operator,
without a pointwise Fourier assertion at $t=0$.
The direct-integral identification and domains are (36.5) and its
closed-form construction: bounded multiplication changes neither scalar
Dirichlet domain, and the direct-integral operator domain has precisely
the displayed squared-integrability condition. Positivity and Tonelli
prove (48.4)–(48.6), first for nonnegative sources and then by subtraction.
The normalized initial density $\phi/J$ evolves in height as
$e^{-\lambda t}\phi/J$; hence its survival mass and the two endpoint
weights give (48.7). At frequency zero it equals one, as required.
The absolute Jacobian and signed dual-frequency map are exactly (39.1).
Wrapping tests against the integer characters proves (48.8), with no
change of source or clock. The actual zero-leaf assertion follows from
$dD_t=0$ and Theorem 39.2. $\square$

## 49. Exact native height-return memory

**Theorem 49.1 (all-frequency complement, memory and self-energy).** For
fixed real $\eta$ abbreviate $v=v_{\kappa,\eta}$ and set

$$
\begin{aligned}
a&=\int_I v\,d\pi=\eta^{\mathsf T}M_\kappa\eta,\\
w&=(v-a)\phi\in\phi^\perp,\\
B&=A|_{\phi^\perp}+P^\perp vP^\perp,
& D(B)&=D(H_I)\cap\phi^\perp,\\
K_\kappa(t,\eta)&=\langle w,e^{-tB}w\rangle,
& \Sigma_\kappa(z,\eta)&=\langle w,(z+B)^{-1}w\rangle.
\end{aligned}
\tag{49.1}
$$

The complement form domain is $H_0^1(I)\cap\phi^\perp$.
The operator $B$ is selfadjoint on that domain and

$$
B\ge\gamma+\min_{\overline I}v\ge\gamma,
\qquad
0\le K_\kappa(t,\eta)\le C|\eta|^4e^{-\gamma t}.
\tag{49.2}
$$

All constants are independent of $\kappa\in\mathcal K$, of its sign,
and of time; the displayed frequency factor is explicit. The exact
scalar response satisfies

$$
\partial_t u_\kappa(t,\eta)
 =-a u_\kappa(t,\eta)
   +\int_0^t K_\kappa(t-s,\eta)u_\kappa(s,\eta)ds,
\qquad u_\kappa(0,\eta)=1.
\tag{49.3}
$$

For every complex $z$ with $\operatorname{Re}z>0$,

$$
\begin{aligned}
\widetilde u_\kappa(z,\eta)
 &=\int_0^\infty e^{-zt}u_\kappa(t,\eta)dt
   =\frac1{z+a-\Sigma_\kappa(z,\eta)},\\
\Sigma_\kappa(z,\eta)
 &=\int_0^\infty e^{-zt}K_\kappa(t,\eta)dt,
& |\Sigma_\kappa(z,\eta)|&\le
 \frac{C|\eta|^4}{\gamma+\operatorname{Re}z}.
\end{aligned}
\tag{49.4}
$$

The self-energy itself is well defined on $\operatorname{Re}z> -\gamma$.
The first equality is asserted on $\operatorname{Re}z>0$, and also
at $z=0$ for $\eta\ne0$. At that real endpoint
$a-\Sigma_\kappa(0,\eta)>0$. At $\eta=0$, $u=1$, $K=\Sigma=0$,
and $\widetilde u(z,0)=1/z$; its zero-frequency threshold pole is
not removed. The original unshifted multiplier
$u^{\rm kill}(t,\eta)=e^{-\lambda t}u(t,\eta)$ therefore obeys

$$
\begin{aligned}
\partial_tu^{\rm kill}(t,\eta)
 &=-(\lambda+a)u^{\rm kill}(t,\eta)
   +\int_0^t e^{-\lambda(t-s)}K_\kappa(t-s,\eta)
                    u^{\rm kill}(s,\eta)ds,\\
\widetilde u^{\rm kill}(z,\eta)
 &=\frac1{z+\lambda+a-\Sigma_\kappa(z+\lambda,\eta)},
 \qquad\operatorname{Re}z>-\lambda.
\end{aligned}
\tag{49.4a}
$$

Thus the threshold shift changes both the instantaneous term and the
time weight of the return kernel. Uniformly for every real frequency
and $t\ge0$,

$$
e^{-at}\le u_\kappa(t,\eta)\le
 \exp[-c t\Psi(|\eta|)]\le1,
\qquad
\Psi(r)=\begin{cases}r^2,&r\le1,\\r^{2/3},&r\ge1.
\end{cases}
\tag{49.5}
$$

The lower constant in the exponent is the native all-real-frequency
coercivity supplier of G (26.12), as used in (36.6).

Proof. The sine spectrum of $A$ is $(n^2-1)\lambda$, $n\ge1$.
The complement therefore starts at $\gamma=3\lambda$.
Since $P$ preserves the scalar Dirichlet operator and form domains,
restriction of $A$ to $\phi^\perp$ has exactly the stated domains.
The complementary multiplication is a bounded selfadjoint perturbation
for fixed $\eta$, proving the domain and lower bounds. Moreover
$\|w\|_2^2=\operatorname{Var}_\pi(v)\le C|\eta|^4$ uniformly.
The spectral theorem proves (49.2) and the resolvent estimates.

Decompose the actual scalar-domain solution as
$e^{-tT_{\kappa,\eta}}\phi=u(t)\phi+h(t)$ with $h(t)\perp\phi$.
Its two equations are
$u'=-au-\langle w,h\rangle$ and $h'=-Bh-wu$, with $h(0)=0$.
Variation of constants in the complementary Hilbert space yields
$h(t)=-\int_0^t e^{-(t-s)B}wu(s)ds$ and hence (49.3).
This argument is legitimate for a generator plus a bounded off-diagonal
coupling on $\mathbb C\oplus\phi^\perp$; it can equivalently be read
as a mild-solution calculation. It does not assert that the full
unbounded-frequency projection preserves $D(L_\kappa)$.

For $\operatorname{Re}z>0$, $z+T_{\kappa,\eta}$ is invertible because
$T_{\kappa,\eta}\ge0$. Solving its two domain equations gives the
first line of (49.4); in particular its denominator cannot vanish.
The exponential bound on $K$ justifies the Laplace convolution and
the second line by absolute integration. For $\eta\ne0$, the native
coercivity bound gives $T_{\kappa,\eta}\ge c\Psi(|\eta|)>0$, so the
same equations work at $z=0$. Its compressed inverse is positive,
which gives the strict positive denominator there.
Finally the scalar spectral measure of $T_{\kappa,\eta}$ in $\phi$
is a probability with mean $a$. Jensen's inequality gives the lower
bound in (49.5), and the spectral bottom gives its upper bound.
All inputs are on the same fixed interval and compact two-sided
coefficient family, proving the declared uniformity. $\square$

**Proposition 49.2 (the finite-frequency return uses tilted dynamics).**
The kernel in (49.1) is identically zero precisely when $v$ is
constant. Otherwise $K_\kappa(t,\eta)>0$ for every finite $t\ge0$.
It cannot be replaced by the untilted height covariance at a general
finite frequency. For example, with $v=(\eta\cdot c_\kappa)^2$ and
$w=(v-a)\phi$, the derivative difference at zero is

$$
\left.\frac d{dt}\right|_{t=0}
\left[\langle w,e^{-tB}w\rangle-
      \langle w,e^{-tA|_{\phi^\perp}}w\rangle\right]
 =-\int_I v(v-a)^2\,d\pi<0
\tag{49.6}
$$

whenever $v$ is nonconstant. Other initial height vectors also add a
source term: if the initial vector is $u_0\phi+h_0$ with
$h_0\perp\phi$, (49.3) has the additional forcing
$-\langle w,e^{-tB}h_0\rangle$ and initial value $u_0$.

Proof. The spectral measure in $w$ of $B$ is nonnegative and has
strictly positive Laplace transform unless $w=0$. Smoothness of $v$
and its boundary-vanishing product with $\phi$ put $w$ in $D(H_I)$,
so both derivatives in (49.6) exist. Their difference is
$-\langle w,P^\perp vP^\perp w\rangle$, the displayed integral.
If this integral were zero, continuity would force $v(v-a)^2=0$
on $I$. A nonconstant nonnegative continuous $v$ takes an interval
of values, contradicting that identity. This supplies an original-model
falsifier of untilted finite-frequency replacement. The same variation
of constants with $h(0)=h_0$ gives the forcing term. $\square$

## 50. Exhaustive autonomous directions and actual characters

**Theorem 50.1 (native converse and all linear projections).** On the
resolved three-phase cover, for each $\kappa\in\mathcal K$ the entire
set of frequencies whose compressed response has a semigroup law is

$$
\mathcal A_\kappa
 =\{t(2,-2,\kappa):t\in\mathbb R\}.
\tag{50.1}
$$

For such a frequency $u_\kappa(s,\eta)=e^{-t^2s}$, and the memory
kernel vanishes. Every other frequency has nonzero return memory and
$u_\kappa(2s,\eta)>u_\kappa(s,\eta)^2$ for all $s>0$.

For any real matrix $R$ defining the linear phase projection $Rq$,
its complete stationary-height compressed transition family is a
convolution semigroup if and only if every row of $R$ lies in
$\mathcal A_\kappa$. Thus its nonconstant autonomous part has rank
at most one. More strongly, that part of the actual Q path is
Brownian and independent of the complete height path. The autonomous
coordinate is the already owned native relation
$2\theta-2v+\kappa x$, not a newly discovered control.

On the original three-torus for $\kappa\ne0$, the exhaustive integer
character lattice is

$$
(n,m,j)=j(2,-2,1),\qquad j\in\mathbb Z.
\tag{50.2}
$$

Its primitive character is $\exp i(2\theta-2v+D)$ and its circle
heat generator is $\partial_\alpha^2$ for
$\alpha=[2\theta-2v+D]$ of period $2\pi$. This holds for both signs
of $\kappa$, with no absolute value in the dual-frequency map.

On the genuine zero leaf $D=D_0$, the moving real autonomous line is
$\mathbb R(1,-1)$ and its entire integer character lattice is
$\mathbb Z(1,-1)$. The primitive circle is
$\beta=[\theta-v]$, again of period $2\pi$, with heat generator
$\tfrac14\partial_\beta^2$. In the original three coordinates one
may also include any multiple of the frozen $D$: these projections
have a deterministic constant component. In particular the pure $D$
projection is error free and has zero diffusion. The restriction of
(50.2) to this leaf gives only the even sublattice of the primitive
moving character, multiplied by the constant $e^{ijD_0}$. Equivalently,
among restrictions of original three-torus characters the complete
zero-leaf set is $(n,-n,j)$ with arbitrary integers $n,j$; among real
linear projections in $(\theta,v,D)$ each row has first two entries
opposite and an arbitrary third entry.

Proof. The selfadjoint compression defect is the identity of F
Proposition 5.1, here on the scalar fibre:

$$
u(2s,\eta)-u(s,\eta)^2
 =\|P^\perp e^{-sT_{\kappa,\eta}}\phi\|_2^2.
\tag{50.3}
$$

If it is zero for one $s>0$, the spectral probability of
$T_{\kappa,\eta}$ in $\phi$ has zero variance under the strictly
injective function $x\mapsto e^{-sx}$. It is supported at one point.
Thus $\phi$ is an eigenvector of $T_{\kappa,\eta}$, which says
$v\phi=a\phi$. Conversely a constant $v$ makes $\phi$ an eigenvector
and gives the exponential law. Since $I$ is connected,
$(\eta\cdot c_\kappa)^2$ is constant if and only if
$\eta\cdot c_\kappa$ is constant; a continuous function with a
nonzero constant square cannot switch sign. The zero-square case
is included.

To establish the exhaustive native converse, put $\eta=(p,q,r)$,
$s_\kappa=H+\kappa$, $\alpha_\kappa=\kappa+\kappa^2/H$.
The original rational formula is exactly

$$
2H(k-\alpha_\kappa)(\eta\cdot c_\kappa)
 =-(p+q)k^2+
 [p(s_\kappa+2\kappa)+2\kappa q-2r]k
 +2s_\kappa(r-\kappa p).
\tag{50.4}
$$

For this to be a constant times $2H(k-\alpha_\kappa)$, its quadratic
coefficient must vanish, so $q=-p$. Matching the remaining two
coefficients gives

$$
\frac{(H-\kappa)s_\kappa}{H}(2r-\kappa p)=0.
\tag{50.5}
$$

The prefactor is nonzero throughout the chosen small family. Therefore
$r=\kappa p/2$ and the constant is $p/2$. Conversely the inherited
identity $2A_\kappa-2B_\kappa+\kappa b_\kappa=1$ realizes every one
of these solutions. This proves (50.1), including zero and both signs,
and the strict defect follows from (50.3).

For a projected convolution semigroup every real projected Fourier
frequency $\xi$ must have an exponential multiplier at $R^{\mathsf T}\xi$.
The scalar converse says precisely
$\operatorname{Ran}R^{\mathsf T}\subset\mathcal A_\kappa$.
Conversely, if the rows are $t_i(2,-2,\kappa)$, their path increments
are $\sqrt2(t_i)_iW_t^2$ directly from (35.2) and (37.8).
The phase Brownian driver is independent of height, proving also the
path assertion. No covariance-matching inference is used.

An original torus character has resolved frequency $(n,m,\kappa j)$,
not $(n,m,j)$. For $\kappa\ne0$, (50.1) forces $t=j$, yielding
(50.2). The integer vector $(2,-2,1)$ is primitive, so its character
has the full original $2\pi$ circle. Its coefficient is one.
At zero the moving coefficients are
$A_0=(H-k)/(2H)$ and $B_0=-k/(2H)$, and a moving combination is
constant exactly when its two coefficients sum to zero. Its primitive
integer vector is $(1,-1)$ and $A_0-B_0=1/2$, proving the claimed
circle generator and all frozen-coordinate assertions.
The resolved zero cover still has the moving coefficient $b_0$ in
its $x$ direction; it is governed by (50.1), not by adjoining a frozen
$D$ to that three-phase process. $\square$

## 51. The native quartic coefficient, finite-time cumulants and band

**Definition 51.1 (explicit native coefficient).** Let $\mathcal L$ be
the positive height Q operator on $L^2(\pi)$, unitarily equivalent to
$A$ under $f\mapsto\phi f$. Thus

$$
\mathcal L f=-\frac{\varepsilon^2}{\phi^2}(\phi^2f')',\qquad
D(\mathcal L)=\{f:\phi f\in H^2(I)\cap H_0^1(I)\}.
\tag{51.1}
$$

Use this unitary domain, not a new reflecting boundary for the original
killed process. On centered functions its inverse
$\mathcal R=(\mathcal L|_{1^\perp})^{-1}$ has norm at most $1/\gamma$.
For every real vector $e$ set

$$
\begin{aligned}
a_e(k)&=
\frac{(k-2\kappa)[e_1(s_\kappa-k)-e_2 k]
                   +2e_3(s_\kappa-k)}{2H(k-\alpha_\kappa)},\\
m_e&=\int_I a_e^2\,d\pi,
& f_e&=a_e^2-m_e,\\
F_e(k)&=\int_l^k \phi(y)^2f_e(y)dy,
& \mathcal B_\kappa(e)&=
 \frac1{\varepsilon^2}\int_l^u\frac{F_e(k)^2}{\phi(k)^2}dk.
\end{aligned}
\tag{51.2}
$$

This is an explicit scalar quadrature in the original rational
coefficients and the fixed sine weight, with no unknown corrector.
It is homogeneous of degree four in $e$. Generic diffusivity-covariance,
inverse-generator and quadrature formulas, and formal Gaussian
corrections, are already present in Alexandre et al.,
[*Non-Gaussian diffusion near surfaces*, arXiv:2207.01880v3,
Supplement S1–S16 and S25–S39](https://arxiv.org/html/2207.01880v3).
Their transverse equilibrium model is a comparison, not an identification
of its boundary law with the original two-Dirichlet source. The native
coefficient, exhaustive vanishing set and uniform estimates below use
precisely (51.1)–(51.2).

**Theorem 51.2 (sign, exact zero set and finite-time fourth cumulant).**
For all $\kappa\in\mathcal K$ and $e\in\mathbb R^3$,

$$
\begin{aligned}
\mathcal B_\kappa(e)
 &=\langle f_e,\mathcal R f_e\rangle_\pi
  =\int_0^\infty\langle f_e,e^{-s\mathcal L}f_e\rangle_\pi ds\\
 &=\sum_{n\ge2}
 \frac{\left(\int_I\phi_n(k)\phi(k)a_e(k)^2dk\right)^2}
      {(n^2-1)\lambda}\ \ge0,\\
\mathcal B_\kappa(e)=0
 &\quad\Longleftrightarrow\quad e\in\mathcal A_\kappa.
\end{aligned}
\tag{51.3}
$$

In particular $e=(0,0,1)$ gives a strictly positive native coefficient
uniformly bounded away from zero on $\mathcal K$.
For $Y_t=e\cdot(q_t-q_0)$ under the stationary-height Q law, all odd
cumulants vanish, and its second and fourth cumulants are exactly

$$
\begin{aligned}
\operatorname{cum}_2(Y_t)&=2m_e t,\\
\operatorname{cum}_4(Y_t)
 &=24\int_0^t(t-s)\langle f_e,e^{-s\mathcal L}f_e\rangle_\pi ds\\
 &=24\left[t\mathcal B_\kappa(e)
 -\langle f_e,\mathcal R^2(1-e^{-t\mathcal L})f_e\rangle_\pi\right].
\end{aligned}
\tag{51.4}
$$

For $t>0$ the fourth cumulant is strictly positive exactly off the
autonomous line. At a fixed finite time the general cumulant law is

$$
\operatorname{cum}_{2n}(Y_t)
 =\frac{(2n)!}{n!}\operatorname{cum}_n
       \left(\int_0^t a_e(K_s)^2ds\right),\qquad n\ge1.
\tag{51.5}
$$

It is an identity of derivatives at zero, not a globally convergent
logarithm at all complex frequencies.

Proof. Centering gives $F_e(l)=F_e(u)=0$. Near either face $\phi^2$
is comparable to the squared distance and $F_e$ is of order at least
the cubed distance. Define $h'$ by
$h'=-F_e/(\varepsilon^2\phi^2)$, and choose the additive constant
so that $\pi(h)=0$. This gives a bounded smooth-interior corrector
with derivative tending to zero at both faces. The identity
$-\varepsilon^2(\phi^2h')'=\phi^2f_e$ and integration by parts,
or its unitary Dirichlet formulation, put $h$ in $D(\mathcal L)$
and give $h=\mathcal R f_e$. Its energy is precisely the last
integral in (51.2). The height spectral decomposition gives the other
expressions in (51.3); all sums and integrals converge by the gap.
The inverse is strictly positive on the centered subspace, so its
quadratic form is zero exactly when $f_e=0$. Theorem 50.1 classifies
that condition completely. The coefficient $b_\kappa$ is positive
and strictly decreasing on the fixed interval by G (12.9), hence its
square is nonconstant. Continuity and compactness give the asserted
strict uniform positivity for $e=(0,0,1)$.

Conditional on the complete height history, $Y_t$ is a centered
Gaussian of variance $2S_t$, where $S_t=\int_0^t a_e(K_s)^2ds$.
Since $S_t$ is bounded at fixed $t$, its exponential moments exist
near zero and
$\mathbb E e^{rY_t}=\mathbb E e^{r^2S_t}$ there. Comparing derivatives
of their logarithms proves (51.5). In particular
$\operatorname{cum}_4(Y_t)=12\operatorname{Var}(S_t)$.
Stationarity and reversibility give
$\operatorname{Var}(S_t)=2\int_0^t(t-s)
\langle f_e,e^{-s\mathcal L}f_e\rangle_\pi ds$.
Integrating each positive spectral term proves (51.4) and its strict
sign. The same positive spectrum shows why there is no cancellation
of a nonzero quartic coefficient in a nonautonomous direction. $\square$

**Theorem 51.3 (controlled band and memory correspondence).** There are
$r_0>0$ and $C<\infty$, independent of $\kappa$ and of the unit vector
$e$, such that for $|r|\le r_0$ the original lowest Dirichlet band obeys

$$
\Lambda_\kappa(re)
 =\lambda+m_e r^2-\mathcal B_\kappa(e)r^4+E_\kappa(r,e),
\qquad |E_\kappa(r,e)|\le C\mathcal B_\kappa(e)|r|^6.
\tag{51.6}
$$

The quartic band coefficient is negative, with the exact vanishing
set (50.1). In contrast, its contribution to the logarithm of the
phase characteristic function is positive. More explicitly, at fixed
$t$,

$$
\log u_\kappa(t,re)
 =-m_e t r^2+r^4\int_0^t(t-s)
       \langle f_e,e^{-s\mathcal L}f_e\rangle_\pi ds+O_t(r^6).
\tag{51.7}
$$

At leading small frequency the exact memory satisfies

$$
\begin{aligned}
K_\kappa(t,re)
 &=r^4\langle f_e,e^{-t\mathcal L}f_e\rangle_\pi
   +O(\mathcal B_\kappa(e)|r|^6t e^{-\gamma t}),\\
\Sigma_\kappa(0,re)
 &=r^4\mathcal B_\kappa(e)+O(\mathcal B_\kappa(e)|r|^6).
\end{aligned}
\tag{51.8}
$$

These are controlled small-frequency statements. If
$\mathcal B_\kappa(e)>0$, globally exponentiating the band polynomial
would give $\exp[-t(m_er^2-\mathcal B_\kappa(e)r^4)]>1$ for large
$|r|$, contradicting (49.5). It is therefore not a characteristic
semigroup generator for the original model.

Proof. A uniform estimate needed here also controls the degeneracies.
Every $f_e$ has the form
$p(k)/(k-\alpha_\kappa)^2$ with $p$ of degree at most four and
$\pi(f_e)=0$. On this finite-dimensional family,

$$
\|f\|_\infty^2\le C\langle f,\mathcal R f\rangle_\pi
\quad\text{for every centered }
 f(k)=p(k)/(k-\alpha_\kappa)^2,\quad\deg p\le4.
\tag{51.9}
$$

Indeed the denominator stays uniformly away from zero. Polynomial
coefficient norms and the supremum norm on the fixed interval are
uniformly equivalent. If (51.9) failed, normalize a countersequence
to supremum norm one and take converging parameter and polynomial
coefficients. Its limit is centered, nonzero, and has zero positive
inverse-generator energy, an impossibility. This argument includes
limits in which the original unnormalized $f$ tends to zero.
In particular $\|f_e\|_2^2\le C\mathcal B_\kappa(e)$.

Set $s=r^2$, $v=a_e^2$, and $\delta=\Lambda_\kappa(re)-\lambda$.
The scalar perturbation is $A+sv$. For small fixed $s$ its lowest
simple eigenvalue satisfies $0\le\delta\le s\|v\|_\infty<\gamma/2$
by the same min-max argument as §36. Its eigenvector has nonzero
$\phi$ component. Complement elimination on the domain of (49.1)
therefore gives exactly

$$
\delta=s m_e-s^2
\left\langle f_e\phi,
 (A|_{\phi^\perp}+sP^\perp vP^\perp-\delta)^{-1}
 f_e\phi\right\rangle.
\tag{51.10}
$$

Both inverses in the resolvent identity comparing this inverse with
$(A|_{\phi^\perp})^{-1}$ are uniformly bounded, and their difference
has norm at most $Cs$. The quadratic error is consequently at most
$Cs\|f_e\|_2^2\le Cs\mathcal B_\kappa(e)$, which proves (51.6).
The complementary eigenvector has norm
$O(s\|f_e\|_2)$; thus the squared ground-overlap amplitude in the
stationary compression is $1+O(\mathcal B_\kappa(e)r^4)$.
There is no order-$r^2$ source-overlap term in this particular law.

Equation (51.7) is also the direct finite-time cumulant expansion
(51.4). Finally $w=r^2f_e\phi$ in (49.1). Duhamel's identity
compares $e^{-t(A|_{\phi^\perp}+r^2P^\perp vP^\perp)}$ with
$e^{-tA|_{\phi^\perp}}$ by a norm bound
$Cr^2t e^{-\gamma t}$, since both generators are bounded below
by $\gamma$ and $v$ is uniformly bounded. Use (51.9), then integrate
in time, to obtain (51.8). The band identity evaluates the exact
self-energy at $z=-\delta$, whereas (51.8) evaluates it at zero;
the resolvent identity shows that their first difference is order
$\mathcal B_\kappa(e)r^6$. This reconciles the negative band quartic,
the positive finite-time fourth cumulant and the tilted return memory
without equating their full finite-frequency evolutions. $\square$

**Proposition 51.4 (one closed native quartic value).** Put
$k_c=(l+u)/2$, $d=u-l$, and take the real-cover projection vector
$e_*=(-2k_c,2k_c-2H,0)$ at $\kappa=0$. Its native coefficient is
$a_{e_*}(k)=k-k_c$, on both the resolved zero cover and the actual
two-phase zero leaf. Its quadratic and first quartic coefficients are

$$
\begin{aligned}
m_{e_*}&=d^2\left(\frac1{12}-\frac1{2\pi^2}\right),\\
\mathcal B_0(e_*)&=
\frac{d^6}{\varepsilon^2}
 \left(-\frac1{720\pi^2}+\frac5{48\pi^4}-\frac7{8\pi^6}\right)>0.
\end{aligned}
\tag{51.11}
$$

Thus the coefficient of $r^4$ in its original lowest band is the
negative of the second displayed number. This is a real projection;
its coefficients do not by themselves assert an integer torus character.

Proof. The formulas for $A_0,B_0$ give $e_*\cdot c_0=k-k_c$ exactly.
Write $x=(k-l)/d$ and $g(x)=x^2-x+1/6$. Integration against
$2\sin^2(\pi x)dx$ gives the first line of (51.11), so the dimensionless
centered square is $f(x)=g(x)+1/(2\pi^2)$. Define

$$
Q(x)=\frac{x(2x-1)(x-1)}{12\pi},\qquad
P(x)=-\frac{g(x)}{4\pi^2},\qquad
y(x)=P(x)\sin(\pi x)+Q(x)\cos(\pi x).
\tag{51.12}
$$

Direct differentiation gives
$-(\partial_x^2+\pi^2)y=f(x)\sin(\pi x)$ and $y(0)=y(1)=0$.
Subtracting its component along $\sin(\pi x)$ gives the orthogonal
Dirichlet inverse; this subtraction has zero inner product with
$f(x)\sin(\pi x)$. Rescaling the inverse in (51.3) therefore gives
$\mathcal B_0(e_*)=(2d^6/\varepsilon^2)
\int_0^1 f(x)\sin(\pi x)y(x)dx$.
Using $(\sin^2\pi x)'=2\pi\sin\pi x\cos\pi x$ and the endpoint
zeros of $Q$, the quantity $2\int_0^1 f(x)\sin(\pi x)y(x)dx$ equals
$-\pi^{-2}\int_0^1 f g\sin^2(\pi x)dx
-\pi^{-1}\int_0^1 f'Q\sin^2(\pi x)dx$.
Integrating these polynomials gives
$-1/(720\pi^2)+5/(48\pi^4)-7/(8\pi^6)$, proving (51.11).
Strict positivity also follows without a numerical comparison from
(51.3), since $(k-k_c)^2$ is nonconstant on $I$. $\square$

## 52. Uniform stationary signed-Gaussian correction

**Theorem 52.1 (controlled three-phase correction and attained order).**
Initialize Q height with $\pi$ and put $X_{\kappa,T}=(q_T-q_0)/\sqrt T$.
For $i,j\in\{1,2,3\}$ define centered native matrix entries and their
inverse-height covariance tensor by

$$
\begin{aligned}
f_{ij}(k)&=c_{\kappa,i}(k)c_{\kappa,j}(k)-(M_\kappa)_{ij},\\
\mathcal C_{ij,ab}(\kappa)&=\langle f_{ij},\mathcal R f_{ab}\rangle_\pi,\\
\mathcal H_\kappa(z)&=
 \sum_{i,j,a,b=1}^3\mathcal C_{ij,ab}(\kappa)
 \partial_i\partial_j\partial_a\partial_b\Gamma_\kappa(z).
\end{aligned}
\tag{52.1}
$$

Here $\Gamma_\kappa$ is the raw Gaussian density in (36.2), with
covariance $2M_\kappa$. The summation uses all ordered index pairs;
there is no additional tensor-symmetry factor. With
$\|\sigma\|_{{\rm var},1}=\int(1+|z|)d|\sigma|(z)$, for all $T\ge1$,

$$
\sup_{\kappa\in\mathcal K}
\left\|\mathcal L(X_{\kappa,T})-
 \left[\Gamma_\kappa+T^{-1}\mathcal H_\kappa\right]dz
\right\|_{{\rm var},1}\le C T^{-3/2}.
\tag{52.2}
$$

The correction has zero total mass and Fourier transform

$$
\widehat{\mathcal H}_\kappa(\xi)
 =\mathcal B_\kappa(\xi)e^{-\xi^{\mathsf T}M_\kappa\xi}.
\tag{52.3}
$$

It is a signed density, not an all-frequency exponential truncation.
For some $T_0,c,C>0$ independent of $\kappa$,

$$
\frac cT\le
\left\|\mathcal L(X_{\kappa,T})-\Gamma_\kappa dz\right\|_{\rm var}
\le\frac CT,\qquad T\ge T_0.
\tag{52.4}
$$

Thus the already owned Q $O(1/T)$ upper is attained in bounded
measurable tests for the full stationary resolved law, uniformly for
unrestricted sequences $\kappa(T)\in\mathcal K$. The new assertion
is the controlled correction and lower order, not that upper estimate
by itself. An equivalent formulation holds at time $Ts$ with scaling
$\sqrt T$, uniformly on each $0<a\le s\le b<\infty$, by the exact
change $T\mapsto Ts$ and spatial dilation by $\sqrt s$.

Proof. Conditional on height, $X_{\kappa,T}$ is Gaussian with random
covariance

$$
A_T=\frac2T\int_0^T c_\kappa(K_r)c_\kappa(K_r)^{\mathsf T}dr,
\qquad B=2M_\kappa,\qquad D_T=A_T-B.
\tag{52.5}
$$

This is Q (41.6), with its original factor two. The matrices $A_T$
are positive semidefinite and uniformly bounded; $B$ has a common
strictly positive lower bound. Stationarity gives $\mathbb ED_T=0$.
For each pair of entries, stationarity and selfadjointness give the
exact covariance identity

$$
\begin{aligned}
\mathbb E[(D_T)_{ij}(D_T)_{ab}]
 &=\frac8{T^2}\int_0^T(T-s)
       \langle f_{ij},e^{-s\mathcal L}f_{ab}\rangle_\pi ds\\
 &=\frac8T\mathcal C_{ij,ab}+O(T^{-2}).
\end{aligned}
\tag{52.6}
$$

The error is uniform: on centered functions the semigroup contracts
by $e^{-\gamma s}$, and the difference of the time integral from
$T\mathcal C$ is bounded by
$\int_0^\infty s\|f_{ij}\|_2\|f_{ab}\|_2e^{-\gamma s}ds$.
In particular $\mathbb E\|D_T\|_F^2\le C/T$.

Here is a fourth-moment bound with no independent-increments assumption
on height. For any bounded centered real $f$ and ordered times
$t_1\le t_2\le t_3\le t_4$, reversibility and the Markov property give

$$
\begin{aligned}
\big|\mathbb E_\pi\prod_{j=1}^4 f(K_{t_j})\big|
&=\big|\langle e^{-(t_2-t_1)\mathcal L}f,
 f e^{-(t_3-t_2)\mathcal L}
       (f e^{-(t_4-t_3)\mathcal L}f)\rangle_\pi\big|\\
&\le \|f\|_\infty^2\|f\|_2^2
 e^{-\gamma[(t_2-t_1)+(t_4-t_3)]}.
\end{aligned}
\tag{52.7}
$$

Integration over the ordered simplex gives
$\mathbb E(\int_0^T f(K_r)dr)^4\le C\|f\|_\infty^2\|f\|_2^2T^2$
for $T\ge1$. Apply this to the finitely many entries to obtain
$\mathbb E\|D_T\|_F^4\le C/T^2$, and hence
$\mathbb E\|D_T\|_F^3\le C/T^{3/2}$ by Cauchy–Schwarz.

For clarity the needed Gaussian Taylor step extends Q Lemma 46.2
by one order, with an actual remainder. Write $p_B$ for the centered
Gaussian density of covariance $B$. In weighted variation, for any
positive semidefinite bounded $A$ and $D=A-B$,

$$
\mathcal N_A=p_Bdz+
 \frac12\sum_{i,j}D_{ij}\partial_i\partial_jp_Bdz+
 \frac18\sum_{i,j,a,b}D_{ij}D_{ab}
                   \partial_i\partial_j\partial_a\partial_bp_Bdz
 +\mathcal E_{A,B},
\quad \|\mathcal E_{A,B}\|_{{\rm var},1}\le C\|D\|_F^3.
\tag{52.8}
$$

To prove it, first suppose $\|D\|_{\rm op}$ is at most half the
common lower eigenvalue bound for $B$. The entire segment $B+tD$
is then uniformly positive. Its density derivatives with respect to
$t$ are $(\tfrac12\sum D_{ij}\partial_i\partial_j)^jp_{B+tD}$.
For $j\le3$ these have weighted $L^1$ bounds $C\|D\|_F^j$ by
Gaussian moments of polynomials of degree at most six, with one
extra moment for the weight. Taylor's integral remainder proves
(52.8). On the complementary region $\|D\|_F$ is bounded below.
The weighted variation of $\mathcal N_A$ is uniformly bounded, even
for singular $A$, and the three displayed Taylor terms have bounds
$C$, $C\|D\|_F$, $C\|D\|_F^2$. Since $D$ is bounded, their sum is
at most $C\|D\|_F^3$ on this region. This proves the global assertion,
without assuming densities for singular conditional covariances.

Mix (52.8) with (52.5). The linear term cancels exactly. Equation
(52.6) and the factor $1/8$ give precisely $T^{-1}\mathcal H_\kappa$;
the covariance error contributes $O(T^{-2})$, and (52.7) bounds the
remaining weighted variation by $O(T^{-3/2})$. Testing signed kernels
against all functions bounded by $1+|z|$ justifies mixing their
weighted variations exactly as in Q (46.8)–(46.9). This proves (52.2).
Fourier transformation of the four derivatives multiplies by
$\xi_i\xi_j\xi_a\xi_b$; contracting (52.1) gives
$\langle f_\xi,\mathcal R f_\xi\rangle=\mathcal B_\kappa(\xi)$.
This proves (52.3) and the zero mass.

For a bounded-test lower bound use $\cos z_3$. Its expectation
difference from the Gaussian is
$T^{-1}\mathcal B_\kappa(e_3)e^{-(M_\kappa)_{33}}+O(T^{-3/2})$.
The leading coefficient has a strictly positive common lower bound
by Theorem 51.2. This gives the left side of (52.4) for one common
$T_0$. The right side follows from (52.2), or directly from the owned
Q endpoint estimate. No fixed relation between $T$ and $\kappa$ has
entered the proof. $\square$

## 53. Degenerating directions, signed coordinates and the zero leaf

**Theorem 53.1 (coefficient-sensitive projection error).** For a unit
resolved vector $e$, let $\mu_{\kappa,e,T}$ be the stationary Q law of
$e\cdot(q_T-q_0)/\sqrt T$, and let

$$
G_{m_e}(z)=\frac{1}{\sqrt{4\pi m_e}}e^{-z^2/(4m_e)},
\qquad B_e=\mathcal B_\kappa(e).
\tag{53.1}
$$

There is one constant $C$ such that, uniformly for $\kappa\in\mathcal K$,
all unit $e$ and $T\ge1$,

$$
\left\|\mu_{\kappa,e,T}-
 [G_{m_e}+T^{-1}B_e\partial_z^4G_{m_e}]dz
\right\|_{{\rm var},1}
 \le C\left(\frac{B_e}{T^2}+
                 \frac{B_e^{3/2}}{T^{3/2}}\right).
\tag{53.2}
$$

For one common $T_0,c,C>0$,

$$
 c\frac{B_e}{T}\le
 \|\mu_{\kappa,e,T}-G_{m_e}dz\|_{\rm var}
 \le C\frac{B_e}{T},\qquad T\ge T_0.
\tag{53.3}
$$

At $B_e=0$ the equality with the Gaussian is exact for every time,
and both sides are zero. The constants do not assert a positive
lower bound independent of $B_e$. In fact, uniformly on unit vectors,

$$
 c\operatorname{dist}(e,\mathcal A_\kappa)^2
 \le\mathcal B_\kappa(e)\le
 C\operatorname{dist}(e,\mathcal A_\kappa)^2.
\tag{53.4}
$$

Consequently arbitrary directions approaching autonomy have the
coefficient-sensitive order $\mathcal B_\kappa(e)/T$, including
sequences with arbitrarily rapid approach and exact autonomous terms.

Proof. Apply the scalar version of (52.8) to
$D_T=(2/T)\int_0^T f_e(K_r)dr$ and $B=2m_e$.
For unit vectors $m_e$ stays between the fixed positive bounds in
(36.1). The spectral identity sharpens (52.6) to

$$
\mathbb ED_T^2=\frac8T B_e
 -\frac8{T^2}\langle f_e,\mathcal R^2
                   (1-e^{-T\mathcal L})f_e\rangle_\pi.
\tag{53.5}
$$

The last inner product is between zero and $B_e/\gamma$.
The variance is at most $8B_e/T$. By (51.9), (52.7) gives
$\mathbb ED_T^4\le C B_e^2/T^2$, and hence
$\mathbb E|D_T|^3\le C B_e^{3/2}/T^{3/2}$.
There is no division by $B_e$ in these estimates. Mixing the scalar
Taylor formula proves (53.2). The Fourier test $\cos z$ has leading
difference $B_e e^{-m_e}/T$. Its error relative to $B_e/T$, when
$B_e>0$, is at most $C(T^{-1}+\sqrt{B_e/T})$. The coefficients $B_e$
are uniformly bounded, so one common $T_0$ gives the lower bound.
The derivative $\partial_z^4G_{m_e}$ has a common finite $L^1$ bound,
giving the upper. If $B_e=0$, the constant-diffusivity path in
Theorem 50.1 proves exact equality, not only an asymptotic bound.

For (53.4), put $r_\kappa=(2,-2,\kappa)$ and decompose the unit vector
as $e=t r_\kappa+h$ with $h\perp r_\kappa$. Then

$$
f_e=2t\,h\cdot(c_\kappa-\pi(c_\kappa))+
       (h\cdot c_\kappa)^2-\pi((h\cdot c_\kappa)^2).
\tag{53.6}
$$

The inverse-height energy norm of the last term is at most $C|h|^2$.
The linear map $h\mapsto h\cdot(c_\kappa-\pi(c_\kappa))$ has kernel
exactly $\mathcal A_\kappa$, by (50.4)–(50.5). On its perpendicular
unit sphere its energy norm has a positive common minimum by
compactness and continuity. For small $|h|$, $|t|$ has a common
positive lower bound, so (53.6) gives lower and upper energy norms
comparable to $|h|$. Away from that neighborhood, compactness and
the exact zero set give the same quadratic comparison after adjusting
constants. Squaring the energy norm proves (53.4). $\square$

**Proposition 53.2 (explicit native degeneration and scaling limits).**
The fixed original projection $2\theta-2v$, with no $D$ term, has
height coefficient $1-\kappa b_\kappa(k)$. Its quartic coefficient is

$$
\mathcal B_\kappa(2,-2,0)
 =4\kappa^2\left\langle b_0-\pi(b_0),
                 \mathcal R(b_0-\pi(b_0))\right\rangle_\pi
   +O(|\kappa|^3),\qquad b_0(k)=\frac1k-\frac1H.
\tag{53.7}
$$

The leading constant is strictly positive. The projected bounded-test
error therefore has order $\kappa^2/T$ uniformly for small nonzero
$\kappa$ and large $T$, and is exactly zero at the actual zero leaf.
This is an original-model counterexample to a direction-uniform positive
$c/T$ lower bound near autonomy.

For arbitrary nonzero real projections, the scale-invariant coefficient
is $\mathcal B_\kappa(e)/m_e^2$. After standardizing the scalar phase
by its standard deviation $\sqrt{2m_eT}$, its correction to the standard
normal density $g$ is

$$
\frac{\mathcal B_\kappa(e)}{4m_e^2T}\,\partial_z^4g.
\tag{53.8}
$$

The bounds in (53.2)–(53.3) have the corresponding scale-invariant
form, with $B_e$ replaced by $\mathcal B_\kappa(e)/m_e^2$ and adjusted
universal constants. They follow by normalizing $e$ and dilating the
scalar variable. The zero projection is deterministic and is treated
separately.

For $\kappa\ne0$, pushing the full law and its signed correction
forward by $J_\kappa$ preserves unweighted variation exactly.
Thus (52.2) and (52.4) hold in original lifted coordinates, comparing
with the Gaussian of covariance $2J_\kappa M_\kappa J_\kappa^{\mathsf T}$,
for arbitrary nonzero sequences approaching either side of zero.
The lower bound allows parameter-dependent bounded tests; for example
the resolved test $\cos z_3$ becomes $\cos(y_3/\kappa)$ in the
$\sqrt T$-scaled original coordinates. It is not a uniform bound for
fixed-Lipschitz-constant tests on those collapsing coordinates.
For the pure original $D$ projection, the variance collapses like
$\kappa^2$ while the standardized nonGaussian coefficient need not
vanish. Small unstandardized coefficients alone do not imply a smaller
scale-invariant bounded-test distance. At exact zero $D$ is frozen,
so the pure $D$ law is a point mass, not that standardized limit.

On the genuine zero leaf, all of (51.2)–(53.3) have a separate
 two-dimensional version with $c$ replaced by $(A_0,B_0)$ and $M$
by $N_0$. Its full two-phase correction is nonzero and its bounded-test
Gaussian error is of order $1/T$, while its autonomous primitive
$\theta-v$ is exactly Gaussian at every time. There is no third moving
coordinate in that statement.

Proof. The native constant relation gives the coefficient in the first
sentence. Center its square to obtain
$-2\kappa(b_\kappa-\pi(b_\kappa))+
\kappa^2(b_\kappa^2-\pi(b_\kappa^2))$.
The coefficients depend smoothly on $\kappa$ on the fixed compact
height interval. Substitution in the positive quadratic form
$\langle f,\mathcal R f\rangle$ proves (53.7), with a uniform cubic
error. Strict monotonicity of $b_0$ proves positivity. The proof of
Theorem 53.1 applies unchanged to this fixed nonunit vector, whose
variance coefficient tends to one; equivalently normalize and dilate.
This proves the stated joint small-parameter, large-time order.

Homogeneity gives $m_{ae}=a^2m_e$ and
$\mathcal B_\kappa(ae)=a^4\mathcal B_\kappa(e)$.
Scalar dilation of four derivatives gives the factor $1/(2m_e)^2$
in (53.8). Normalized vectors have uniformly positive $m_e$, proving
the scale-invariant estimates. Invertible measurable pushforward
preserves variation by its dual characterization in bounded tests;
the signed Jacobian is handled by its absolute value as in (39.1).
The weighted remainder remains uniform because $|J_\kappa z|\le C|z|$
on the fixed parameter interval; no uniform inverse-Jacobian estimate
is required for that upper bound.
For a fixed original projection vector $a$, its resolved vector is
$J_\kappa^{\mathsf T}a$. The pure $D$ case is $\kappa e_3$, which
explains both the collapsing variance and unchanged standardized
coefficient for nonzero $\kappa$.

Finally the actual zero-leaf coefficient vector is exactly
$(A_0,B_0)$, with positive tensor $N_0$ by Theorem 39.2. Its entries
are bounded, its centered products are still members of the rational
family in (51.9), and the identical height operator has the same gap.
Every covariance and Taylor argument restricts to indices $1,2$.
For a strict lower bound choose the second moving phase: $B_0^2$
is nonconstant on $I$, so its coefficient is positive. The autonomous
line is exactly the two-phase line already proved in Theorem 50.1.
This proves the separate leaf conclusions. $\square$

## 54. Predictive closure and the retained geometric boundaries

**Proposition 54.1 (precise closure refinement).** The averaged quadratic
phase operator $\sum_{ij}(M_\kappa)_{ij}\partial_i\partial_j$ predicts
the infinitesimal stationary compressed generator and the Gaussian
infrared covariance. Its full finite-time compressed response is a
Markov convolution semigroup only on the projections of Theorem 50.1.
Off those projections the exact response requires the height-return
term (49.3), or retention of the original height state. Its first
stationary departure from the Gaussian is (52.1)–(52.2), with the
coefficient-sensitive exceptions in §53.

These statements concern the specified compression and source law.
They neither replace the full point heat/Green kernel nor transfer
unchanged to a fixed initial height, a different raw source, or a
terminal survival-conditioned law. The exact weights are (48.5)–(48.7)
and (37.5). They give no observer an operation preparing $\pi$,
conditioning on future survival, acquiring windings, resetting height,
or changing the native clock. A torus character is a well-defined
mathematical function on the original phase torus; its existence
alone is not acquisition of that function from a chosen current-ray
readout. A complete continuous wrapped path with an initial lift and
a single wrapped endpoint retain their distinct meanings in §40.

The instantaneous phase symbol is still rank one and the full
same-clock symbol is still rank two. The resolved infrared rank is
three, while the genuine zero leaf has only two moving phases.
Complementary height modes are spectral modes of one bounded height
variable, not additional spatial axes, and their elimination proves
no minimum nonlinear observer dimension or impossibility of retaining
height. There is no physical rotation symmetry, universal choice of
three physical spatial dimensions, empirical realization, finite
bit/shot/CPU cost, new observation service, attraction, or binding
assertion in these conclusions. All Green, circle, source-charge,
zero-leaf and attraction statements of §§41–47 and their G/C/O/F/N
suppliers retain their original domains and meanings.

Proof. Differentiating (48.3) at zero time gives multiplier
$-\eta^{\mathsf T}M_\kappa\eta$, but the strict defect (50.3) shows
why this derivative alone cannot determine the complete response.
The exact elimination restores its missing return, and (51.4),
(51.6) and (52.2) relate that return to the first nonGaussian term
without a global polynomial-generator assertion. The exhaustive
projection classification includes both zero and nonzero error-free
cases; §53 supplies the uniform vanishing estimates at their boundary.
Equations (48.5)–(48.7) prove the source distinctions, not merely an
asymptotic qualification. The raw coordinate and period maps in
Theorems 48.2 and 50.1 preserve the preceding circle and leaf meanings.
The rank and observation restrictions are exactly (40.1) and its
same-clock factor argument. None of the new operators contains an
attractive potential, so none changes the earlier attraction domains
or conclusions. $\square$

**Mathematical correspondence 54.2 (scope of the ordinary proof).**
The generic Gaussian-mixture mechanism also belongs to Chechkin et al.,
[*Brownian yet non-Gaussian diffusion: from superstatistics to
subordination of diffusing diffusivities*, arXiv:1611.06202v2](https://arxiv.org/html/1611.06202v2).
The inverse-height cumulant and formal Gaussian correction overlap
with the explicitly credited supplement of Alexandre et al.; they
are not claimed as new generic results. The source-specific additions
are the exhaustive rational and integer-lattice converse, its exact
zero-leaf distinction, the native coefficient and vanishing locus,
and the controlled uniform and degenerating-direction conclusions.
The domain elimination is included only to fix their original-law
meaning and their all-real-frequency response.

Hervé–Pène,
[*The Nagaev–Guivarc'h method via the Keller–Liverani theorem*,
arXiv:0901.4617v3, §8](https://arxiv.org/html/0901.4617v3),
and Ferré–Hervé–Ledoux,
[*Limit theorems for stationary Markov processes with $L^2$-spectral
gap*, arXiv:1201.4579v1](https://arxiv.org/html/1201.4579v1),
provide different Markov additive/Edgeworth frameworks, including their
moment and nonlattice hypotheses. Their one-dimensional first-order
Edgeworth theorems are not silently substituted for the present
stationary even-cumulant, weighted-variation expansion. Here the
remainder follows directly from the exact conditional Gaussian law,
the fixed height gap, and the global Gaussian Taylor estimate (52.8).
These comparisons confer no worldwide originality certificate.
All statements in §§48–54 are ordinary mathematical arguments under
the stated native premises, not Lean-kernel certificates or empirical
claims about a physical system.

## 追加锚（本行以下为增补区）

## 55. Causal native height from a complete phase record

**Definition 55.1 (source, observations and mathematical conventions).**
Retain Definition 35.1 and G Definition 25.1, with their fixed closed
parameter interval $\mathcal K$, original clock and coefficient functions.
The premises in §§35–54 and G (25.1)–(25.5) are taken at
[`11e2a65d554143d0e3f38b37f1b686453451e3c4`](https://github.com/the-omega-institute/trureturing/tree/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory).
In this and the following sections the principal probability is

$$
\mathbf Q_\kappa=\int_I\pi(dk)\,\mathbb Q_{k,q_0}^\kappa,
\qquad \pi(dk)=\phi(k)^2dk,
\qquad \sigma=\sqrt2\varepsilon.
\tag{55.1}
$$

The initial phase $q_0$ and native parameters are known, whereas $K_0$
is the actual unobserved random variable with law $\pi$. The height
and phase equations are exactly (37.8), with independent drivers.
This stationary-height probability is an additional specified law;
it is not a preparation operation supplied by the native controls.
At nonzero $\kappa$ the original phases are
$y=(\theta,v,D)=(\theta,v,\kappa x)$. At zero the actual source has
$D=D_0$, and the comparison process with a moving $x$ remains separate.
More precisely, (55.1) on the resolved space is denoted
$\mathbf Q^{\rm res}_\kappa$ when a distinction is needed. Its
pushforward on increments under
$y_t=y_0+\operatorname{diag}(1,1,\kappa)(q_t-q_0)$
is $\mathbf Q^{\rm act}_\kappa$, with the prescribed known
initial $y_0=(\theta_0,v_0,D_0)$. At zero this map forgets the moving
$x$ and retains the known frozen $D_0$. Both laws have exactly the same
$(K,\theta,v)$ marginal. An observation involving comparison $x$
at zero is taken under $\mathbf Q^{\rm res}_0$; assertions involving
only $v$, including every risk below, hold for the actual source.
No observation of comparison $x$ is inferred from frozen $D$.

For an ideal supplied real phase projection $Y=Rq$, define

$$
\mathcal H_t^R=\sigma(Y_s:0\le s\le t)\vee\mathcal N_\kappa,
\qquad
\mathcal H_t^v=\sigma(e^{iv_s}:0\le s\le t)\vee\mathcal N_\kappa,
\tag{55.2}
$$

where $\mathcal N_\kappa$ denotes the null sets in the complete
underlying probability space. These are the completed causal
filtrations, without adjoining observations at times greater than $t$.
In particular we do not replace $\mathcal H_0^v$ by
$\mathcal H_{0+}^v=\bigcap_{t>0}\mathcal H_t^v$: Theorem 55.2
will put $K_0$ in the latter, while it is absent from the former.
A null-set completion supplies no positive-time observations.
For an integer matrix $N$, the lawful original torus observation is
the vector of characters $\exp(iNy_s)$, with componentwise exponential;
its filtration is defined in the same way. A real projection of a
cover is asserted supplied only in the ideal real experiment.
For a separately stipulated finite stopped record with an observed
stop tag $T$, its data field means
$\sigma(T,Y_{s\wedge T}:s\in\mathbb Q_+)\vee\mathcal N_\kappa$.
This definition supplies neither a stopping operation nor a stop tag
to any other experiment. Raw cemetery paths retain their death
record instead of an implicitly frozen live phase.

A continuous circle path with its known initial value has a unique
continuous real lift after fixing any initial argument. Its increments
are independent of this choice. Path lifting is Borel and causal:
on a compact interval, subdivide until each image segment lies in a
circle arc of length less than $\pi$ and concatenate the local arguments;
the first successful subdivisions can be selected from a countable
family. This construction uses only the supplied prefix. Consequently
continuous character records give the corresponding real character
increments, including windings, but finitely many circle values do not.

All new source-specific assertions in §§55–60 are `repo-derived` in
the ordinary proof sense. Quadratic variation, Itô's formula, Gaussian
conditioning and the integration-by-parts information inequality used
inside their proofs are `literature-attested` tools, with the
correspondence specified in Definition 61.1.

**Theorem 55.2 (complete wrapped $v$ history recovers height causally).**
For every $\kappa\in\mathcal K$, including the genuine zero leaf,
there is a causal Borel construction from the continuous wrapped $v$
record such that, outside one null set, it recovers $K_t$ at every
$t>0$. For every such $t$ it also recovers the complete height prefix
$(K_s)_{0\le s\le t}$. At time zero alone the phase record carries no
height information: the conditional law of $K_0$ is $\pi$.

Put $a_\kappa(k)=2B_\kappa(k)^2$. On the entire fixed family there
are constants $0<a_-<a_+<\infty$ and $c_a>0$ such that

$$
a_-\le a_\kappa(k)\le a_+,
\qquad a_\kappa'(k)\ge c_a\quad(k\in\overline I).
\tag{55.3}
$$

Writing $[v]$ for the quadratic variation of the lifted record, the
reconstruction at a positive time is

$$
K_t=a_\kappa^{-1}\left(
 \lim_{h\downarrow0,\ h<t}\frac{[v]_t-[v]_{t-h}}h\right).
\tag{55.4}
$$

The inverse is on the range of $a_\kappa$; the construction can take
an arbitrary value when its prescribed limits fail.

Proof. Let $\alpha=\kappa+\kappa^2/H$. Polynomial division of G (25.4)
gives

$$
B_\kappa(k)=-\frac1{2H}
 \left(k+\alpha-2\kappa+
       \frac{\alpha(\alpha-2\kappa)}{k-\alpha}\right),
\qquad
B_\kappa'(k)=-\frac1{2H}
 \left(1-\frac{\alpha(\alpha-2\kappa)}{(k-\alpha)^2}\right).
\tag{55.5}
$$

Positivity of the original probabilities gives $k>2\kappa$ when
$\kappa>0$; the fixed small family has $|\kappa|<H$ and $k-\alpha>0$.
Moreover
$\alpha(\alpha-2\kappa)=\kappa^2(\kappa^2/H^2-1)\le0$.
Thus $B_\kappa<0$ and $B_\kappa'\le-1/(2H)$.
Compactness, strict positivity and the fixed margins in Definition
35.1 prove (55.3), since $a_\kappa'=4B_\kappa B_\kappa'$.
This argument does not shrink $\mathcal K$ with time or with $n$.

Conditional on the height path the lifted phase is
$\sqrt2\int_0^\cdot B_\kappa(K_s)dW_s^2$, and hence

$$
[v]_t=\int_0^t a_\kappa(K_s)ds.
\tag{55.6}
$$

For precision about versions, take sums of squared increments along
dyadic partitions of each bounded time interval. With bounded diffusion
coefficient, the martingale isometry and the maximal inequality give
an $L^2$ bound $C2^{-m}$ for the squared uniform error of the level-$m$
variation sums. One may use the step sums at partition endpoints;
the largest intervening increment tends to zero by continuity.
Markov's inequality at threshold $2^{-m/8}$ and Borel–Cantelli give
almost sure uniform convergence. The same assertion for a continuous
semimartingale with locally bounded coefficients follows by stopping
on compact sets; a bounded-variation part has zero quadratic variation
and its cross sums tend to zero by Cauchy–Schwarz. These facts also
apply to the nested variations below. A countable union over integer
time horizons and compact stopping sets produces a single null set.
The sums and their limits are Borel functions of the supplied prefixes.

The integrand in (55.6) is continuous. Therefore its left derivatives
exist with the asserted value simultaneously at every positive time.
Only times at most $t$ occur in (55.4). Applying this construction at
all positive times and taking the right limit at zero recovers the
height prefix. The known initial phases are constant random variables,
so $\mathcal H_0^v$ is trivial modulo null sets and leaves the
nondegenerate law $\pi$ unchanged. Since $v$ is an original phase,
the complete original phase record also identifies height, including
the actual two-moving-phase zero leaf. At $\kappa=0$ the same calculation
uses $B_0=-k/(2H)$ and requires no comparison $x$. $\square$

## 56. Exhaustive real scalar path observations

**Theorem 56.1 (the rational classification, including folded failures).**
Fix a resolved real frequency $\eta=(p,q,r)$ and put
$f(k)=\eta\cdot c_\kappa(k)$. There are unique real numbers
$A_\eta,D_\eta,C_\eta$ such that

$$
f(k)=A_\eta(k-\alpha_\kappa)+D_\eta
                      +\frac{C_\eta}{k-\alpha_\kappa},
\qquad A_\eta=-\frac{p+q}{2H},
\tag{56.1}
$$

and the residue is

$$
C_\eta=\frac{(H+\kappa)(H-\kappa)}{2H^3}
 \bigl(2Hr-\kappa(H-\kappa)p+\kappa^2q\bigr).
\tag{56.2}
$$

Under the actual unknown-height source (55.1), the complete real path
of $Y=\eta\cdot q$ identifies height at every positive time, in the
sense of Theorem 55.2, exactly in the following cases:

- $C_\eta\ne0$;
- $C_\eta=0$, $p+q\ne0$, and
  $r_*:=\kappa+Hp/(p+q)\notin I$.

The other cases have positive endpoint conditional uncertainty at
every fixed $t>0$:

$$
\mathbf E_{\mathbf Q_\kappa}
   \operatorname{Var}(K_t\mid\mathcal H_t^\eta)>0.
\tag{56.3}
$$

More precisely, $C_\eta=0$, $p+q=0$ is exactly the autonomous line
(50.1), on which the entire height and observation paths are
independent. If $C_\eta=0$, $p+q\ne0$ and $r_*\in I$, the coefficient
is a nonconstant multiple of $k-r_*$; it has an actual reflection
ambiguity, even with continuous observation. The boundary cases
$r_*=l,u$ identify height. The classification holds for both signs
and for the resolved comparison at $\kappa=0$.

Proof. Division of (50.4) gives (56.1)–(56.2). On the residue-zero
plane it simplifies further to

$$
f(k)=\frac{p(H+\kappa)+\kappa q-(p+q)k}{2H}.
\tag{56.4}
$$

If $p+q=0$, the residue equation forces $r=\kappa p/2$ and
$f=p/2$. This is precisely (50.1). Otherwise (56.4) is
$-(p+q)(k-r_*)/(2H)$. Its square is one-to-one on $I$ exactly when
$r_*\notin I$. The left derivative of $[Y]/2$ then recovers $f(K)^2$
and its inverse recovers height, including when the zero is an endpoint.

It remains to prove identification for every nonzero residue, rather
than assume that the first covariance is injective. Put
$g=f^2$. The path $Y$ gives the continuous path $g(K)$ at all positive
times by the same left derivative. Its value at zero is a limit from
positive times on any nontrivial prefix. Itô's formula on compact
height intervals and the constant height diffusion coefficient give

$$
[g(K)]_t=\sigma^2\int_0^t g'(K_s)^2ds.
\tag{56.5}
$$

Thus nested variation gives the pair $(g(K_s),g'(K_s)^2)$ causally
at every $s>0$. The height drift, although unbounded at the two
endpoints, is bounded on every compact interval visited up to a
finite time, so the localization used for (56.5) is legitimate.

For this native rational function the pair is injective except at
finitely many heights. Here is an explicit algebraic proof. Write
$y=k-\alpha>0$ and $f=Ay+D+C/y$, with $C\ne0$. Exclude the finitely
many zeros of $f$. Equality of the two pairs at $y,z$ implies
$f(y)=\pm f(z)$ and $f'(y)=\pm f'(z)$. Equal derivatives force $y=z$,
since $f'(y)=A-C/y^2$. Opposite derivatives give

$$
2A=C(y^{-2}+z^{-2}).
\tag{56.6}
$$

If in addition $f(y)=f(z)$ and $y\ne z$, subtraction gives
$A=C/(yz)$, which combined with (56.6) gives $(y-z)^2=0$,
a contradiction. In the remaining case $f(y)=-f(z)$, put
$U=1/y,V=1/z,S=U+V$. Equation (56.6) says
$U^2+V^2=2A/C$. Multiplying the equation for opposite values by
$UV$ and substituting $UV=(S^2-2A/C)/2$ gives

$$
\frac C2 S^3+D(S^2-2A/C)=0.
\tag{56.7}
$$

This is a nonzero cubic, and each of its finitely many roots fixes
$UV$ and hence an unordered pair $U,V$. If (56.6) has no positive
solutions there are no such pairs. Consequently the exceptional
heights form a finite set $E$. Outside $E$ the pair has a Borel
inverse, obtained, for example, by selecting the unique solution
of its rational equations on $I\setminus E$.

For each positive rational $s$, stationarity gives
$\mathbf Q_\kappa(K_s\in E)=0$. On the complement of one null set,
all positive rational heights are therefore recovered by this inverse.
Their limits along rationals below $t$ recover $K_t$ simultaneously
for every $t>0$ by continuity; rational limits towards zero recover
$K_0$ from any positive prefix. This uses no future derivative at $t$.
It also proves why noninjectivity of the first covariance alone would
not establish a negative case.

For the negative folded case take $r=r_*\in I$ and a closed symmetric
interval $J=[r-\delta,r+\delta]\Subset I$. Reflect a height prefix by
$\mathcal R K_s=2r-K_s$ and replace $W^2$ by $-W^2$. Since
$f(2r-k)=-f(k)$, this transformation leaves the entire observed
$Y$ prefix unchanged, including its known initial value.

This is an ambiguity in the actual source, not in an enlarged model.
Indeed on paths staying in $J$ the stationary Q height law has density

$$
e^{\lambda t}\phi(K_0)\phi(K_t)
\tag{56.8}
$$

relative to $\int_J dk\,\mathbb P_k^{\rm BM}$ restricted to those
paths, where the Brownian variance rate is $\sigma^2$.
Formula (56.8) is exactly $\pi(dk)$ times the Doob factor (37.2).
The reference measure is reflection invariant. The density ratio
of the reflected Q restriction to the original one is therefore

$$
\frac{\phi(2r-K_0)\phi(2r-K_t)}
     {\phi(K_0)\phi(K_t)},
\tag{56.9}
$$

which is bounded above and below by positive constants on $J$.
The independent Brownian phase driver is invariant under sign reversal.
Choose a terminal subinterval $J_+\Subset(r,r+\delta)$ and its
reflection $J_-$. The event that the height stays in $J$ and ends in
$J_+$ has positive probability, by the positive killed Brownian
kernel inside $J$ and (56.8). Its reflected counterpart ends in
$J_-$, has the identical observation under the transformation, and
has an equivalent observation measure by (56.9).

Disintegrating these two subprobabilities with respect to the full
observation prefix shows that, on a set of observation values of
positive probability, the actual posterior puts positive mass on
both $J_+$ and $J_-$. Indeed let $\nu_\pm$ be the observation
submeasures of the two events and let $\nu_Y$ be the full observation
probability. Equivalence gives a positive-$\nu_Y$ set on which both
$w_\pm=d\nu_\pm/d\nu_Y$ are positive. The actual posterior masses
of $J_\pm$ are at least $w_\pm$. If $d>0$ is their separation,
the posterior-independent-copy formula for variance gives
$\operatorname{Var}(K_t\mid\mathcal H_t^\eta)\ge d^2w_+w_->0$
on that set. Integration proves (56.3).
If $f$ is constant, the observation is a multiple of the independent
$W^2$ and the posterior is exactly $\pi$; this includes the
identically zero observation. These cases exhaust (56.1). $\square$

**Proposition 56.2 (known initial height and stopped prefixes).**
If instead the initial height is a known fixed $k_0\in I$, the
positive-time scalar classification of Theorem 56.1 is unchanged.
In every negative case its expected conditional variance at every
fixed $t>0$ is still positive. Knowledge of $k_0$ only makes its
recovery at time zero trivial. For any identifying record, the same
single pathwise reconstruction also applies at an observed finite
stop $T>0$, on $T<\zeta$ under a killed law, and recovers $K_T$
from that stopped prefix. No classification for a new
height-dependent stopping rule is inferred from the deterministic-time
negative statements.

Proof. The positive proofs use the same variation identities.
Where Theorem 56.1 used stationarity to avoid the finite set $E$
at positive rational times, use instead the fixed-start Q height
density $e^{\lambda s}h_I(s;k_0,k)\phi(k)/\phi(k_0)$.
It is absolutely continuous for $s>0$, so gives zero mass to $E$.
For an autonomous coefficient the record remains independent of
the height path, and this strictly positive interior density has
positive variance at every $t>0$.

For a folded coefficient with center $r\in I$, let
$\varsigma=\inf\{s\ge0:K_s=r\}$. The event
$\varsigma<t/2$ has positive probability from every $k_0\in I$:
a Brownian path can reach $r$ inside $I$ by that time, and its
fixed-start Q weight on surviving paths is strictly positive.
After $\varsigma$, restrict height to a closed symmetric
$J\Subset I$ about $r$ and require its endpoint to belong to
$J_+\Subset J\cap(r,u)$. This event has positive probability by
the strong Markov property and the positive killed heat kernel in
$J$. Reflect height only after $\varsigma$, and reverse the phase
driver only after that time. The transformed record is exactly the
same because $f(2r-k)=-f(k)$, and the initial height is unchanged.

For killed Brownian height the transformation preserves the reference
measure on these paired events, by the strong Markov property and
reflection symmetry of the post-hitting increments. Conditional on
height, reversal of the phase driver after the fixed time
$\varsigma(K)$ preserves its independent Wiener law. The fixed-start
Q weight is $e^{\lambda t}\phi(K_t)/\phi(k_0)$, so the ratio of
paired Q weights is $\phi(2r-K_t)/\phi(K_t)$, bounded above and
below on $J$. The disintegration argument of Theorem 56.1 therefore
gives positive posterior mass on the two separated terminal intervals
$J_+$ and its reflection. This proves positive conditional variance
with the same known $k_0$.

Finally all identifying constructions hold simultaneously at every
positive time outside one null set. Evaluating their left limits
and left variation derivatives at $T$ uses only the supplied stopped
prefix, so proves the stopped assertion. At a death time, the
predeath limit gives an absorbing face, with the cemetery meaning
specified in Proposition 60.2. A stopping tag selected from hidden
height can itself encode height; the negative classification above
assumes the stated deterministic horizon and does not add such a
tag to its observations. $\square$

## 57. Matrix observations and lawful original characters

**Theorem 57.1 (all real matrices).**
For a real matrix $R$ with any finite number of rows write
$F(k)=Rc_\kappa(k)$. Apply the residue (56.2) to each row.
If at least one residue is nonzero, its complete path identifies height.
If all residues vanish, write uniquely

$$
F(k)=a k+b\quad(a,b\in\mathbb R^d).
\tag{57.1}
$$

The matrix record fails to identify height exactly when either
$a=0$, or $a\ne0$ and $b=-r a$ for some $r\in I$.
In every other case it identifies the complete height prefix at
positive times. Every failure has the positive conditional variance
(56.3), with the matrix observation filtration.

Proof. A nonzero-residue row is already sufficient by Theorem 56.1.
Otherwise the left derivative of the observed matrix quadratic
variation is $2F(K_t)F(K_t)^{\mathsf T}$. For two vectors, equality
of their outer products implies that they are equal or negatives,
including the common zero case. If $a\ne0$, equality with the same
sign implies equal heights. Opposite signs at distinct heights imply

$$
a(k+k')+2b=0.
\tag{57.2}
$$

Thus $b=-ra$, with $k+k'=2r$. If $b$ is not a multiple of $a$, or
if its corresponding $r$ is outside $I$, the covariance is injective
on $I$. Its continuous inverse on compact subintervals gives causal
recovery just as in (55.4). An endpoint $r=l,u$ does not create two
heights in $I$. If $a=0$, the vector observation is one Brownian
motion with a constant vector multiplier and is independent of height.
If $b=-ra$ with $r\in I$, the reflection and driver reversal used
in (56.8)–(56.9) preserve every component simultaneously. Their
two separated actual posterior masses prove failure. $\square$

**Theorem 57.2 (signed character classification and both zero objects).**
For $\kappa\ne0$ an original scalar torus character
$e^{i(n\theta+mv+jD)}$, $(n,m,j)\in\mathbb Z^3$, has resolved
frequency $(n,m,\kappa j)$. Define

$$
E_\kappa(n,m,j)=2Hj-(H-\kappa)n+\kappa m.
\tag{57.3}
$$

Its complete continuous record identifies height if
$E_\kappa\ne0$. If $E_\kappa=0$ and $n+m\ne0$, it identifies
height exactly when

$$
\kappa+\frac{Hn}{n+m}\notin I.
\tag{57.4}
$$

The remaining $E_\kappa=0$, $n+m=0$ cases are precisely the
independent autonomous characters (50.2). The cases failing (57.4)
have the actual positive posterior ambiguity of Theorem 56.1.
This includes all integer characters, primitive or not, for either
sign of $\kappa$.

For a vector of original characters, substitute each row
$(n,m,j)\mapsto(n,m,\kappa j)$ in Theorem 57.1. This is the complete
integer-matrix classification; individually folded characters with
different fold centers can jointly identify height.

At the resolved comparison zero, a supplied real frequency $(p,q,r)$
has residue $r$. Frequencies with $r\ne0$ identify; those with $r=0$
follow the affine criterion with fold center $Hp/(p+q)$ and autonomous
line $p+q=0$. In contrast, on the actual frozen-$D$ zero leaf every
original character has moving coefficient

$$
f_{n,m,j}(k)=\frac{Hn-(n+m)k}{2H}.
\tag{57.5}
$$

The integer $j$ contributes only a known constant phase. Such a
character identifies height exactly when $n+m\ne0$ and
$Hn/(n+m)\notin I$. If $n+m=0$ it is independent of height;
otherwise its interior fold is a positive-ambiguity case.
The full matrix criterion on that leaf is (57.1)–(57.2) with row
slope $-(n+m)/(2H)$ and row intercept $n/2$.

Proof. Substitute the signed frequency into (56.2); its parenthesis
is $\kappa E_\kappa$. When it vanishes, (56.4) gives the fold
center (57.4). If $m=-n$, equation (57.3) forces $n=2j$, precisely
(50.2). Continuous lifting of the supplied character path, as in
Definition 55.1, gives its real increments; taking a nonprimitive
character therefore loses no increments of that character itself.
No division by a wrapped endpoint or an unavailable cover coordinate
is used. The matrix claim follows componentwise from the same lifting
and Theorem 57.1. At actual zero, insert $A_0=(H-k)/(2H)$,
$B_0=-k/(2H)$ and $dD=0$ to obtain (57.5). At comparison zero,
(56.2) instead gives $C_\eta=r$, because $b_0=1/k-1/H$ remains
moving. These are different observations and different laws. $\square$

**Corollary 57.3 (all real original projections, including actual zero).**
Suppose a real linear cover record $Ry$, $y=(\theta,v,D)$, is
supplied, with arbitrary finite real matrix $R$. For nonzero
$\kappa$, replace each row $(p_i,q_i,r_i)$ by
$(p_i,q_i,\kappa r_i)$ in Theorem 57.1. This classifies every
such record for both signs. On the actual frozen-$D$ zero leaf put

$$
a_i=-\frac{p_i+q_i}{2H},\qquad b_i=\frac{p_i}{2}.
\tag{57.6}
$$

It fails to recover height exactly when $a=0$, or $a\ne0$ and
$b=-ra$ for one common $r\in I$; each failure has positive expected
posterior variance at every fixed positive time under (55.1).
In particular a real scalar row identifies exactly when
$p+q\ne0$ and $Hp/(p+q)\notin I$. The third real coefficient
only changes the known initial value at actual zero. A real cover
projection descends to the original torus as a character precisely
when all its coefficients are integers; Theorem 57.2 classifies
these lawful observations separately.

Proof. For nonzero $\kappa$, the exact signed differential map is
$dy=\operatorname{diag}(1,1,\kappa)dq$, proving the substitution.
At actual zero the observed increments have coefficient
$F_i(k)=p_iA_0(k)+q_iB_0(k)=a_i k+b_i$ and no moving $D$ term.
The affine outer-product argument and reflection proof in Theorem
57.1 apply verbatim to these real vectors. This proves both
sufficiency and actual-source ambiguity, rather than inferring a
negative conclusion just from noninjectivity of a covariance.
For a scalar row its root is $Hp/(p+q)$, including the identifying
endpoint cases. Finally invariance under adding $2\pi$ separately
to each original coordinate requires and suffices that every
frequency coefficient be an integer. $\square$

## 58. The finite wrapped sample experiment and an attained upper bound

**Definition 58.1 (one fixed known-parameter Bayes experiment).**
Fix $\tau>0$, $t_j=j\tau/n$ and $\Delta=\tau/n$. The data and risk are

$$
\mathcal D_n=\sigma(e^{iv_{t_j}}:0\le j\le n),\qquad
R_{n,\kappa}=\inf_g\mathbf E_{\mathbf Q_\kappa}
 (K_\tau-g(e^{iv_{t_0}},\ldots,e^{iv_{t_n}}))^2.
\tag{58.1}
$$

The infimum is over Borel estimators with the common known parameters
and initial phases. All expectations refer to the one source (55.1).
The Bayes estimator is the conditional mean and
$R_{n,\kappa}=\mathbf E\operatorname{Var}(K_\tau\mid\mathcal D_n)$.
There is no supplied interpolation, height, Brownian driver, winding
increment or additional observation between the sample times.

**Theorem 58.2 (exact finite-$n$ ambiguity and full interior support).**
For each finite $n\ge1$ and every $\kappa\in\mathcal K$ the posterior
law of $K_\tau$ is equivalent to $\pi$, and in particular has support
$\overline I$ and gives positive mass to every nonempty open
subinterval of $I$. Hence $R_{n,\kappa}>0$.

Proof. Given the entire height path, let

$$
V_j=\int_{t_{j-1}}^{t_j}a_\kappa(K_s)ds,
\qquad a_-\Delta\le V_j\le a_+\Delta.
\tag{58.2}
$$

The real increments are independent centered normals with variances
$V_j$, by independence of $W^2$ and height. For circle increments
$z_j\in[-\pi,\pi)$ their exact conditional density, relative to
ordinary angular Lebesgue measure, is

$$
L_z(K)=\prod_{j=1}^n\sum_{m\in\mathbb Z}
 \frac{\exp[-(z_j+2\pi m)^2/(2V_j)]}{\sqrt{2\pi V_j}}.
\tag{58.3}
$$

The map from the original circle samples with fixed initial value to
these circle increments is bijective. For fixed $n$, each factor is
continuous and strictly positive on the compact product of its circle
and $[a_-\Delta,a_+\Delta]$. Thus there are constants
$0<c_n<C_n<\infty$ bounding $L_z(K)$ uniformly in $z$, height paths
and $\kappa$. Stationarity gives $K_\tau\sim\pi$. Disintegrate the
height path given its endpoint and apply Bayes' formula:

$$
\pi_z(dk)=\pi(dk)
 \frac{\mathbf E[L_z(K)\mid K_\tau=k]}{\mathbf E L_z(K)}.
\tag{58.4}
$$

Choosing the conditional height-path kernel once gives a version for
all $z$; its density is bounded above and below by positive constants
for $\pi$-almost every $k$. The resulting posterior is nondegenerate
and has the asserted full support. Its variance is positive for every
such data value, so its expected variance is positive. In fact its
density relative to $\pi$ is at least $c_n/C_n$. For any real $b$,
$\int(k-b)^2\pi_z(dk)\ge(c_n/C_n)\int(k-b)^2\pi(dk)$;
minimizing over $b$ gives the uniform finite-$n$ bound
$R_{n,\kappa}\ge(c_n/C_n)\operatorname{Var}_\pi(K)>0$.
This bound depends on $n$ and is distinct from the sharp order
proved in Theorem 59.1. $\square$

**Theorem 58.3 (uniform wrapped-sample upper bound).**
There are constants $C_\tau<\infty$ and $n_0$, independent of
$\kappa\in\mathcal K$, such that

$$
R_{n,\kappa}\le C_\tau n^{-1/2}\qquad(n\ge n_0).
\tag{58.5}
$$

Proof. Let $m=\lceil\sqrt n\rceil$, $h=m\Delta$, and use the final
$m$ increments. For an initial bound pretend they are unwrapped and
put $S=(m\Delta)^{-1}\sum_{j=n-m+1}^n(\Delta_jv)^2$.
Conditional on height,

$$
\mathbf E[S\mid K]=\frac1h\int_{\tau-h}^\tau a_\kappa(K_s)ds,
\qquad
\operatorname{Var}(S\mid K)=\frac{2\sum V_j^2}{(m\Delta)^2}
 \le\frac{2a_+^2}{m}.
\tag{58.6}
$$

The actual stationary height drift is
$\mu(k)=2\varepsilon^2\phi'(k)/\phi(k)$. Its squared stationary
moment is finite, explicitly

$$
\mathbf E_\pi\mu(K)^2=4\varepsilon^4\int_I\phi'(k)^2dk<\infty.
\tag{58.7}
$$

The height SDE, Cauchy–Schwarz and stationarity therefore imply, for
$0\le u-s\le\tau$,

$$
\mathbf E|K_u-K_s|^2
 \le2\sigma^2(u-s)+2(u-s)^2\mathbf E_\pi\mu^2
 \le C_\tau(u-s).
\tag{58.8}
$$

Uniform boundedness of $a_\kappa'$ and Jensen's inequality give

$$
\mathbf E\left|
 \frac1h\int_{\tau-h}^\tau a_\kappa(K_s)ds-a_\kappa(K_\tau)
 \right|^2\le C_\tau h.
\tag{58.9}
$$

Clip $S$ to $[a_\kappa(l),a_\kappa(u)]$ and apply the inverse
$a_\kappa^{-1}$. Clipping cannot increase its distance from
$a_\kappa(K_\tau)$, and (55.3) makes this inverse uniformly Lipschitz.
Equations (58.6)–(58.9) bound its height risk by $C_\tau(m^{-1}+h)$.

For the actual estimator replace each increment by the principal
argument of its observed circle increment, then use the same clipping
and inverse. It agrees with the preceding estimator whenever all
of the final $m$ real increments have absolute value less than $\pi$.
The exact conditional normal law and (58.2) imply

$$
\mathbf Q_\kappa(\text{one of these increments wraps})
 \le2m\exp\left(-\frac{\pi^2}{2a_+\Delta}\right).
\tag{58.10}
$$

Both height estimates lie in $[l,u]$. The wrapped estimator's risk
is therefore at most the unwrapped estimator's risk plus
$2(u-l)^2m\exp[-\pi^2/(2a_+\Delta)]$. With the chosen $m$ this
proves (58.5). No assumption about a Brownian interpolation of the
data has entered the estimator. $\square$

## 59. A lower bound inside the same stationary native source

**Theorem 59.1 (sharp order of endpoint Bayes squared risk).**
For each fixed $\tau>0$ there are constants $0<c_\tau<C_\tau<\infty$
and $n_0$ such that, simultaneously for all $\kappa\in\mathcal K$,

$$
c_\tau n^{-1/2}\le R_{n,\kappa}\le C_\tau n^{-1/2}
\qquad(n\ge n_0).
\tag{59.1}
$$

In particular this holds along every sequence $\kappa(n)$ in the
same fixed two-sided family, including sequences with actual zero
values. The assertion is an order bound, not an exact leading
constant or a larger-class minimax assertion.

Proof. The upper bound is Theorem 58.3. We prove the lower bound by
giving extra information about this same actual probability, retaining
its exact weights.

Choose a grid-aligned final interval of length $h=m\Delta$, where
$m=\lceil\sqrt n\rceil$ and $s=\tau-h$. Write $x=K_s$, $z=K_\tau$,
and express the final height segment in the coordinates

$$
K_{s+r}=x+\frac rh(z-x)+b_r,\qquad
0\le r\le h,\qquad b_0=b_h=0.
\tag{59.2}
$$

Enlarge the data to contain the full height and phase-driver past up
to $s$, the bridge $b$ in (59.2), and the $m$ exact unwrapped phase
increments on this final interval. They determine all original
wrapped samples. Crucially, they do not contain $z$. This is a
comparison experiment on the original probability space; no such
additional service is asserted in (58.1).

Let $\beta_h$ be the centered Brownian bridge measure with variance
rate $\sigma^2$, and let
$\gamma_h(w)=(2\pi\sigma^2h)^{-1/2}\exp[-w^2/(2\sigma^2h)]$.
Given the past ending at $x$, the exact Q joint kernel of $(b,z)$ is

$$
\beta_h(db)\,\gamma_h(z-x)\,dz\,
 e^{\lambda h}\frac{\phi(z)}{\phi(x)}
 \mathbf1\left\{x+\frac rh(z-x)+b_r\in I\text{ for all }r\le h\right\}.
\tag{59.3}
$$

Indeed an ordinary Brownian segment disintegrates into its endpoint
normal density and an independent centered bridge: the covariance
of the bridge with its endpoint is zero, so joint Gaussianity gives
independence. Killing restricts that segment to staying in $I$, and
the exact Doob derivative is $e^{\lambda h}\phi(z)/\phi(x)$.
Thus (59.3) is the actual conditional Q kernel, not an approximation
by a flat height prior. Conditional on $(x,b,z)$ the final unwrapped
increments $y_j$ are independent $N(0,V_j(z))$, with

$$
V_j(z)=\int_{(j-1)\Delta}^{j\Delta}
 a_\kappa\left(x+\frac rh(z-x)+b_r\right)dr,
\quad 1\le j\le m.
\tag{59.4}
$$

Select a closed interval $J\Subset I$ of positive length and a fixed
$\rho>0$ such that every $x\in J$ is at distance at least $3\rho$
from the boundary. Take a nonzero $\psi\in C_c^\infty((-1,1))$ with
$0\le\psi\le1$. For sufficiently small $h$, form a subprobability
$\nu_h$ by multiplying the exact joint law of the enlarged experiment
and its target by

$$
\mathbf1_{\{x\in J\}}
\mathbf1_{\{\sup_{r\le h}|b_r|\le\rho\}}
\psi\left(\frac{z-x}{\sqrt h}\right)^2.
\tag{59.5}
$$

The multiplier is at most one, so every nonnegative loss has
$\mathbf E_{\mathbf Q_\kappa}\text{loss}\ge\int\text{loss}\,d\nu_h$.
On this support $|z-x|\le\sqrt h\le\rho$ and the full segment
in (59.2) stays in an interior compact set. The indicator in (59.3)
is identically one wherever the multiplier is nonzero, with a
positive margin from the actual absorbing faces.

There are constants $c_0>0,C_0<\infty$, independent of small $h$ and
of $\kappa$, such that

$$
\nu_h(1)\ge c_0,
\qquad
\int |\partial_z\log p_{\nu_h}|^2d\nu_h
 \le C_0(h^{-1}+m).
\tag{59.6}
$$

Here the density is with respect to the actual Q law of the past,
$\beta_h(db)$, Lebesgue $dz$ and Lebesgue measure in the final
unwrapped increments. Its derivative is taken at fixed past and fixed
bridge, which are precisely the coordinates revealed to the estimator.

To prove the mass bound, stationarity gives
$\mathbf Q_\kappa(x\in J)=\pi(J)>0$. The bridge maximal second
moment is at most $C\sigma^2h$: write it as
$\sigma(W_r-rW_h/h)$ and apply the Brownian maximal inequality.
Thus its displayed cutoff has probability at least $1/2$ for small
$h$. On the remaining support $\phi(z)/\phi(x)$ is bounded above
and below by positive constants. Substitution $z=x+\sqrt h\,u$
in the endpoint integral gives a positive constant times
$\int_{-1}^1\psi(u)^2\exp[-u^2/(2\sigma^2)]du$.
Integration of the normal observation densities gives one.
This proves $\nu_h(1)\ge c_0$.

For the information bound, the part of the logarithmic derivative
coming from the endpoint kernel and cutoff is

$$
S_0=-\frac{z-x}{\sigma^2h}+\frac{\phi'(z)}{\phi(z)}
       +\frac{2}{\sqrt h}
          \frac{\psi'((z-x)/\sqrt h)}{\psi((z-x)/\sqrt h)}.
\tag{59.7}
$$

The ratio involving $\psi$ is used only where $\psi>0$. Its squared
integral is well defined because the factor $\psi^2$ cancels the
denominator, leaving $4\psi'^2/h$. The first term has squared
integral at most $C/h$ by the scaled support; the second is bounded
on the fixed interior compact set. Thus $\int S_0^2d\nu_h\le C/h$.
There is no hidden derivative of a survival indicator on this support.

From (55.3), the bounded derivative of $a_\kappa$, and (59.4),

$$
V_j\ge a_-\Delta,
\qquad |V_j'|\le \|a_\kappa'\|_\infty\Delta,
\qquad |V_j'/V_j|\le C.
\tag{59.8}
$$

A centered normal observation of variance $V_j(z)$ has score

$$
S_j=\frac{V_j'}{2V_j}\left(\frac{y_j^2}{V_j}-1\right),
\qquad
\mathbf E[S_j\mid x,b,z]=0,
\qquad
\mathbf E[S_j^2\mid x,b,z]=\frac{(V_j')^2}{2V_j^2}\le C.
\tag{59.9}
$$

The conditional scores are independent, and their cross terms with
$S_0$ vanish as well. Summing proves the second part of (59.6),
including the genuine Q factor $\phi(z)/\phi(x)$ in its score.

For completeness, the information inequality needed here follows
from one integration by parts. For any estimator $g$ measurable in
the enlarged data, it is a function of the past, $b$ and the $y_j$,
so it has no $z$ derivative in these coordinates. The cutoff makes
the density vanish at its $z$ integration boundaries. Therefore

$$
\int(g-z)\,\partial_z\log p_{\nu_h}\,d\nu_h=\nu_h(1).
\tag{59.10}
$$

This identity follows first for bounded $g$ by integrating
$\partial_z((g-z)p_{\nu_h})$. For finite-risk $g$ it follows by
truncation and Cauchy–Schwarz using (59.6); infinite-risk estimators
already satisfy the required bound. A second Cauchy–Schwarz gives

$$
\mathbf E_{\mathbf Q_\kappa}(g-K_\tau)^2
 \ge\int(g-z)^2d\nu_h
 \ge\frac{\nu_h(1)^2}{\int|\partial_z\log p_{\nu_h}|^2d\nu_h}
 \ge\frac{c}{h^{-1}+m}.
\tag{59.11}
$$

This is the Bayesian information argument applied to a dominated
subprobability of the same source. It does not change its drift,
height prior, independent phase driver or target.

If $R^{\rm more}_{n,\kappa}$ is the Bayes risk with the enlarged
data, information inclusion has the direction

$$
R_{n,\kappa}\ge R^{\rm more}_{n,\kappa}
 \ge\frac{c}{h^{-1}+m}.
\tag{59.12}
$$

With $h=m\tau/n$ and $m=\lceil\sqrt n\rceil$, the last quantity is
at least $c_\tau n^{-1/2}$ for large $n$. All constants used depend
only on the fixed native data, the fixed horizon and the chosen
interior cutoffs. The height law, $\phi$ and the bridge measure do
not depend on $\kappa$; the observation bounds are uniform on the
original fixed $\mathcal K$. At actual zero, $v$ and its variance
function are exactly the same limiting native coordinates, so every
step applies without adjoining $x$. This completes (59.1). $\square$

## 60. Memory, Gaussian limits and the three actual path laws

**Proposition 60.1 (what continuous recovery changes).**
Theorem 55.2 refines, without altering, the eliminated-height memory
and autonomous classification of §§49–54. Under (55.1), continuous
$v$ history contains height at positive times, whereas a single
current $v$ value and every finite sample set retain positive height
uncertainty. The process $e^{iv_t}$ is not Markov in its completed
natural filtration. The autonomous directions of Theorem 50.1 remain
Brownian and independent of the entire height path. The folded
nonautonomous directions of Theorem 56.1 are additional examples of
continuous-path nonidentification; independence is not necessary for
such failure.

On every fixed nontrivial time interval the native continuous $v$
path law is singular to the constant-variance Brownian law with the
same averaged variance. More generally every nonconstant scalar
native coefficient in Theorem 56.1 has this singularity, including
the folded negative cases. Constant coefficients give exactly the
Brownian exception. The full resolved native path and its rank-three
Gaussian infrared approximation also have singular path laws; on the
actual zero leaf the analogous comparison is between one instantaneous
moving phase direction and the positive rank-two averaged covariance.
These statements do not obstruct the weak long-time limits or the
quantitative path-transport upper bounds already proved in Q.

Proof. The first two assertions are Theorems 55.2 and 58.2; a single
positive-time $v$ value is the $n=1$ experiment with that time as its
horizon. For the Markov assertion fix $t>0$. The continuous-past
conditional expectation of a small future circle increment satisfies

$$
\lim_{h\downarrow0}\frac1h
 \mathbf E[2(1-\cos(v_{t+h}-v_t))\mid\mathcal H_t^v]
 =a_\kappa(K_t)\quad\text{in }L^1.
\tag{60.1}
$$

To see this, condition first on height: its value is
$2(1-\exp[-\tfrac12\int_t^{t+h}a_\kappa(K_s)ds])$.
Boundedness of $a_\kappa$, continuity and conditional contraction
prove the limit, because $K_t$ is $\mathcal H_t^v$-measurable.
If the circle phase were Markov, every expression on the left
would be measurable in its current circle value. The $L^1$ limit
would be too. Strict monotonicity of $a_\kappa$ would make $K_t$
measurable in that single value, contradicting Theorem 58.2.
The independence and folded statements are already proved in
Theorems 50.1 and 56.1, respectively. In a folded nonconstant case,
the record reveals $f(K_0)^2$ by variation and the limit towards
zero on any positive prefix. This is a nondegenerate random variable
under $\pi$, measurable in both height and observation histories;
these histories therefore cannot be independent.

For a scalar coefficient $f$, quadratic variation of its path is
$2\int_0^t f(K_s)^2ds$. A nonconstant native rational $f$ has a
nonconstant analytic square on $I$. Almost surely the height path
on a nontrivial interval is not constant: its quadratic variation is
$\sigma^2t>0$. The continuous image of such a height path contains
an interval, on which an analytic nonconstant square cannot be
constant. Consequently its phase quadratic variation is not a
constant multiple of time. The matched Brownian law has deterministic
linear quadratic variation. These disjoint Borel path events prove
the scalar singularity. Circle path lifting preserves the same test.
This uses the classical quadratic-variation distinction, not a new
general singularity theorem.

For the full resolved path the variation derivative is
$2c_\kappa(K_s)c_\kappa(K_s)^{\mathsf T}$ of rank one, whereas the
Gaussian in §36 has constant derivative $2M_\kappa$ of rank three.
On the genuine zero leaf replace these by
$2(A_0,B_0)(A_0,B_0)^{\mathsf T}$ and $2N_0$ of rank two.
Again these are disjoint measurable path events. Weak convergence
and convergence in a transport metric on continuous paths do not
assert equivalence of path laws or preservation of quadratic variation;
that functional is not continuous for the uniform topology. Thus
there is no contradiction with §§36–40 or Q §§45–46. In particular
Gaussian infrared rank measures temporal covariance accumulation,
not the number of native phase drivers or physical spatial axes.
$\square$

**Proposition 60.2 (exact source weights and death boundaries).**
Let $\rho$ be any common initial height probability on $I$, and use
the same known initial phases for its killed and Q mixtures. Put
$S_\rho(T)=\int_I S_k(T)\rho(dk)$. On full paths up to $T$,

$$
\frac{d\mathbb P_\rho^\kappa(\,\cdot\,,\zeta>T)}
     {d\mathbb Q_\rho^\kappa}
 =e^{-\lambda T}\frac{\phi(K_0)}{\phi(K_T)}.
\tag{60.2}
$$

For the law obtained by conditioning that mixture on survival to $T$,
its density on a prefix $\mathcal F_r$, $r\le T$, is

$$
\frac{d\mathbb P_\rho^\kappa(\,\cdot\mid\zeta>T)}
     {d\mathbb Q_\rho^\kappa}\bigg|_{\mathcal F_r}
 =\frac{e^{-\lambda r}\phi(K_0)S_{K_r}(T-r)}
        {\phi(K_r)S_\rho(T)}.
\tag{60.3}
$$

If instead each fixed-start law is first conditioned and then mixed
with $\rho$, the denominator in (60.3) is $S_{K_0}(T)$.
These are generally distinct initial-height laws. Formula (37.5)
is their common fixed-start specialization.

The pathwise identifying constructions above apply before death to
the raw killed law and to a terminal-survivor law, with their own
completed observation filtrations and exceptional null sets. Under
an unknown initial law with positive density on the symmetric interval
used in (56.8), the folded negative argument also persists on surviving
compact-prefix events. The numerical risk theorem (59.1), however,
is a theorem for $\rho=\pi$ under Q; no unchanged Bayes risk constant
or uniform rate under a different source is asserted here.

Proof. The finite-horizon Doob derivative at each fixed starting
height is $e^{\lambda r}\phi(K_r)/\phi(K_0)$. Invert it on surviving
paths and mix the same initial law to obtain (60.2). For a prefix
conditioned on survival to $T$, multiply the killed prefix density
by its actual remaining survival factor $S_{K_r}(T-r)$ and divide
by $S_\rho(T)$. This proves (60.3). Performing conditioning before
mixing instead divides by $S_{K_0}(T)$, as stated. All factors are
positive at interior endpoints and are the original source factors,
not observation-independent constants.

For fixed finite $T$, these path laws are equivalent on survival;
therefore any Q-almost-sure path identity has the asserted surviving
version. For recovery at arbitrary times before the raw death,
use countably many rational horizons and the same local variation
identities. At death there is no surviving interior height: the raw
process is at its cemetery state. If its record includes that state
and one takes the limit of reconstructed predeath heights, this gives
the absorbing face approached, not a continuation past death or a
conservative raw law. The Q process itself has no finite death.

On a compact symmetric interval the factors in (60.2)–(60.3) are
bounded and positive; the reflection comparison consequently retains
its two separated posterior possibilities for positive-density
unknown initial laws. This is a local ambiguity assertion, not a
transfer of the stationary endpoint risk. Globally $1/\phi(K_r)$
is unbounded near either face. Integrability of the weights follows
from the probability identities themselves, but uniform squared-risk
bounds do not follow from mere absolute continuity. In (59.3) and
(59.7) the actual Q factor and its derivative were explicitly kept;
in (58.7)–(58.9) stationarity was explicitly used. These are the
source-specific hypotheses that a different risk theorem would have
to replace. No conditioning, reset, height sensor, changed clock or
additional physical resource is provided by these measure identities.
$\square$

## 61. Mathematical suppliers and the scope of the observation theorem

**Definition 61.1 (credited methods and native scope).**
The quadratic-variation and Itô tools used inside §§55–60 are the
classical continuous-semimartingale calculus; compare H. Föllmer,
*Calcul d'Itô sans probabilités*, Séminaire de probabilités XV,
[primary text](https://www.numdam.org/item/SPS_1981__15__143_0/).
A supplied path and a refining partition with convergent squared
increments are needed for that calculus. Here convergence and causal
left differentiation are supplied in the proof of Theorem 55.2,
and nested Itô variation is localized on interior compact sets.
No arbitrary continuous record is presumed to have those properties.

K. D. Elworthy, Y. Le Jan and X.-M. Li,
*The Geometry of Filtering*,
[arXiv:0810.2253v1](https://arxiv.org/html/0810.2253v1),
§§2, 4–5, treats diffusion projection, filtering and non-Markovian
observations, including the geometric role of the symbol. Its
projectible-symbol framework is not an identification theorem for
$f(K)^2$ with unknown stationary initial height in the present
rational family: a folded scalar symbol here need not be a function
of the current observed phase. The proofs above instead compute the
native residue, its nested variation and its actual reflected source.
F's full-class projection and reversible compression criteria remain
separate premises and do not supply this path classification.

M. E. Mancino, T. Mariotti and G. Toscano,
*Asymptotic Normality for the Fourier spot volatility estimator in
the presence of microstructure noise*,
[arXiv:2209.08967v1](https://arxiv.org/html/2209.08967v1),
§3 and its distinction from §4, places the noiseless $n^{1/4}$
spot-volatility error scale in its classical Itô-semimartingale
setting; the noisy scale is different. The present observations have
no additive measurement noise. Their variance $a_\kappa(K)$ is a
continuous Itô semimartingale after interior localization, but its
stationary height drift has boundary singularities, and the target
is the endpoint height on a circle-sampled known-parameter source.
No interior-time Fourier central limit theorem, periodic extension,
unknown-volatility minimax bound or noisy-data rate is imported as
a proof of (59.1). The one-sided estimator and stationary moment
bound (58.7)–(58.10) handle the endpoint and wrapping directly.

M. Reiß, *Asymptotic equivalence for inference on the volatility
from noisy observations*,
[arXiv:1105.2128v1](https://arxiv.org/html/1105.2128v1),
Theorem 6.2 and §8, gives Gaussian-experiment comparisons and
nonparametric minimax conclusions for an unknown volatility function
observed with additive Gaussian measurement error. Its equivalence
theorem requires Hölder exponent $\alpha>(1+\sqrt5)/4$ and positive
measurement-noise scale with its stated asymptotic relation. Here
there is no additive measurement noise, and Itô's formula and (55.3)
give $[a_\kappa(K)]_t=\sigma^2\int_0^t a_\kappa'(K_s)^2ds>0$.
A Hölder path of exponent greater than $1/2$ has zero quadratic
variation along uniform partitions, by summing its squared increment
bound. Thus the smoothness hypothesis of that equivalence theorem
does not hold for this native random variance. Its larger-function-class
minimax conclusions are not a Bayes lower bound for the single native
law (55.1); (59.3)–(59.12) supply that missing original-source argument.

E. García-Portugués, M. Sørensen, K. V. Mardia and T. Hamelryck,
*Langevin diffusions on the torus: estimation and applications*,
[arXiv:1705.00296v1](https://arxiv.org/html/1705.00296v1),
§2 and Proposition 1, describes wrapping densities and distinguishes
toroidal diffusions from wrapped Euclidean processes whose projected
histories can retain winding information. Its Proposition 1 assumes
an ergodic Euclidean diffusion with a stationary density. The real
$v$ lift here is not such an ergodic Euclidean source; it has a
separate latent stationary height. That proposition is not applied
as a native Markov or recovery theorem. Here the wrapped likelihood
(58.3) follows directly by summing the conditional Gaussian increments,
and (58.10) bounds its high-frequency winding error under the actual
height mixture. Continuous path lifting and finite wrapped sampling
therefore remain distinct observation resources.

The lower-bound mechanism is the classical Bayesian information
inequality, as in R. D. Gill and B. Y. Levit,
*Applications of the van Trees Inequality: A Bayesian Cramér–Rao
Bound*, Bernoulli 1 (1995),
[DOI 10.2307/3318681](https://doi.org/10.2307/3318681).
The relevant hypotheses are a differentiable dominated density,
vanishing boundary terms, a target with derivative one, and finite
integrated squared score. They are proved for the actual native
bridge disintegration and its compact cutoff in (59.3)–(59.10), and
the inequality itself is derived there. In particular a minimax
bound over variable diffusion coefficients is not substituted for
a Bayes bound under the single fixed coefficient and prior here.

The native content is the exhaustive rational and lawful-character
classification, its reflection ambiguity under the actual source,
and the attained two-sided endpoint-height risk with the original
wrapped data and uniform fixed-family constants. Generic variation,
Gaussian bridge, filtering and information methods are not asserted
as new results. These mathematical statements provide no physical
$SO(3)$ symmetry, spatial-dimension selection, source-supplied sensor,
finite-precision acquisition, finite CPU/bit/shot bound, minimum
nonlinear observer dimension, new attraction or binding assertion,
or Lean-kernel certificate. They preserve the earlier raw, Q,
terminal-survivor, zero-leaf, memory and infrared meanings.

## 追加锚（本行以下为增补区）

## 62. An unknown fixed native calibration

**Definition 62.1 (the experiment and its target).** Retain exactly G
Definition 25.1, Definition 35.1 and the actual stationary-height law
(55.1), with known $H,I=(l,u),\varepsilon$, original clock, initial
original phases and height law. These native premises are taken at
[`6198ac3642d19f48f815df872aef049954aca64b`](https://github.com/the-omega-institute/trureturing/tree/6198ac3642d19f48f815df872aef049954aca64b/docs/develop/theory).
Choose once, before observing,

$$
w=u-l,\qquad
\delta=\min\{\kappa_*/2,w/8\}>0,\qquad
\mathcal K_{\rm cal}=[-\delta,\delta].
\tag{62.1}
$$

Here $\kappa_*$ is the fixed admissible radius of Definition 35.1;
in particular the margins and $|\kappa|<H$ used in (55.5) hold.
The parameter $\kappa\in\mathcal K_{\rm cal}$ is fixed and unknown.
For every parameter the height has the same stationary Q law,
$K_0\sim\pi=\phi^2dk$, and satisfies (37.8). The initial height is
unobserved. Write $\mathbf Q_\kappa$ for the actual original-coordinate
law, including frozen $D=D_0$ at actual zero. The supplied data at $t$
are only the ideal continuous record $(e^{iv_s})_{0\le s\le t}$.
The target is $T_t=(\kappa,K_{[0,t]})$.

A family recovery means one Borel function of that record, independent
of the unknown parameter, correct $\mathbf Q_\kappa$-almost surely
for every $\kappa$. Lawwise null completion is allowed, as in (55.2),
but a different decoder selected using $\kappa$ is not family recovery.
No right-continuization at zero is made. If a parameter prior $\nu$ is
explicitly supplied, its experiment is
$\mathbf P_\nu(d\kappa,d\omega)=\nu(d\kappa)\mathbf Q_\kappa(d\omega)$;
conditional on every parameter the height law remains exactly $\pi$
and (37.8). A completed-prior estimator has a Borel version under its
observation law; all data fields in that experiment use its own null
completion. The parameterwise and prior meanings are distinct.

**Definition 62.2 (shifted native coordinates).** Put

$$
\begin{aligned}
r&=|\kappa|,&\alpha_\kappa&=\kappa+\kappa^2/H,&
U_s&=K_s-\alpha_\kappa,\\
d_r&=2r^2/H,& b_r&=r^2(1-r^2/H^2),&
F_r(u)&=u+d_r-b_r/u.
\end{aligned}
\tag{62.2}
$$

The symbol $b_r$ here is a scalar polynomial, distinct from the
coefficient $b_\kappa(k)$ in G (25.4). All admissible shifted heights
are positive. Polynomial division in (55.5) gives the exact identity

$$
-2HB_\kappa(K_s)=F_r(U_s)>0.
\tag{62.3}
$$

Thus the change $(\kappa,K)\mapsto(-\kappa,K-2\kappa)$ preserves
the entire $v$ coefficient wherever both height paths are admissible.
This algebra alone is not an assertion about equivalence of source laws.
The law comparison is part of Theorem 64.1 below. The source-specific
results in §§63–67 are `repo-derived` ordinary mathematical consequences
of these fixed premises. Their classical intermediate tools are credited
in Definition 68.1.

## 63. Calibration magnitude from nested variation

**Theorem 63.1 (one causal construction for the whole fixed family).**
There is a parameter-independent Borel causal construction from the
wrapped $v$ history which recovers

$$
Q_t=(r,U_{[0,t]})\qquad(t>0).
\tag{63.1}
$$

For each fixed $\kappa$ there is one $\mathbf Q_\kappa$-null set
outside which the construction is correct simultaneously at every
positive time. For any supplied prior there is likewise one joint
null set. The construction identifies actual zero exactly and there
recovers $K_{[0,t]}$. It does not require a moving comparison $x$.

Proof. Use the causal circle lift and dyadic variation construction of
Definition 55.1 and Theorem 55.2. For a continuously differentiable
variation function write $\partial_- [X]_s$ for its left derivative
at $s>0$. First form the continuous observable path

$$
Z_s=H\sqrt{2\partial_-[v]_s}=F_r(U_s),\qquad s>0,
\tag{63.2}
$$

and recover its value at zero by its right limit. Since the height
variance rate is the known $\sigma^2=2\varepsilon^2$, Itô variation
of this recovered path gives

$$
J_s=\sqrt{\partial_-[Z]_s/\sigma^2}
    =1+b_r/U_s^2.
\tag{63.3}
$$

The positive square root is justified by
$F_r'(u)=1+b_r/u^2>0$. Recover $J_0$ by continuity and repeat once:

$$
L_s=\sqrt{\partial_-[J]_s/\sigma^2}=2b_r/U_s^3.
\tag{63.4}
$$

When $J_s=1$ we have $b_r=0$. Since $r<H$, this is precisely $r=0$;
then $U=K=Z$. Otherwise $J_s>1,L_s>0$, and the explicit inverses are

$$
U_s=\frac{2(J_s-1)}{L_s},\qquad
 d_r=Z_s+(J_s-2)U_s,\qquad
 r=\sqrt{Hd_r/2}.
\tag{63.5}
$$

Indeed (63.3) gives $b_r=(J_s-1)U_s^2$, and substitution into
$Z_s=U_s+d_r-b_r/U_s$ proves (63.5). These formulas use no unknown
calibration in their inputs. In particular no inversion of a supplied
$a_\kappa$ is hidden in the construction.

Here every recovered continuous path used in a subsequent variation
is evaluated from prefixes only. On $[0,t]$ its zero value is the limit
of its already recovered positive-time values, using times at most $t$.
For any finite horizon the Q height stays in a compact subset of $I$.
On such a subset the coefficients, the Q drift and all derivatives
appearing in (63.2)–(63.4) are bounded. The localized dyadic convergence
argument in Theorem 55.2 therefore applies successively to $v,Z,J$.
Intersect its full-measure events for the three levels, countably many
compact localizations and integer horizons. This gives one exceptional
null set for each law, not a separately chosen exception at every time.
Left differentiation then works at every positive real time, including
the terminal time, because the variation integrands are continuous.
Continuity supplies the whole prefix and its initial value.

All sums, left derivative limits, square roots and continuous extensions
are Borel operations on the supplied path; derivatives can be taken
through rational positive increments tending to zero. On failure of
limits, range tests or positivity tests assign a fixed default output.
For a continuous prefix output, use the recovered rational-time values
and their unique continuous extension; the requisite uniform continuity
and range tests use only countably many rational comparisons.
This defines the same decoder for all parameters. The success event is
measurable jointly with the parameter, so integration of its lawwise
null sections proves the assertion for every supplied prior. No claim
of a uniform finite-precision bound near $r=0$ follows from the divisions
in (63.5). $\square$

## 64. The complete target quotient and its actual source laws

**Theorem 64.1 (finite-prefix quotient modulo actual-law null sets).**
Fix $t>0$. For $r\in(0,\delta]$ define

$$
\alpha_\pm=\pm r+r^2/H,\qquad
I_\pm=I-\alpha_\pm,\qquad
E_\pm=\{u\in C([0,t]):u_s\in I_\pm\ \hbox{for all }s\le t\}.
\tag{64.1}
$$

The recovered $(r,u)$ has the candidate target set

$$
\mathcal C_t(r,u)
 =\{(sr,u+\alpha_s):s\in\{+,-\},\ u\in E_s\}.
\tag{64.2}
$$

At $r=0$ it is the singleton $(0,u)$. At $r>0$ it has one or two
members, always including the actual target. Both sign laws give
positive mass to $E_+\cap E_-$. Their restrictions there are equivalent,
with the exact height-path density ratio

$$
\frac{\phi(u_0+\alpha_+)\phi(u_t+\alpha_+)}
     {\phi(u_0+\alpha_-)\phi(u_t+\alpha_-)}.
\tag{64.3}
$$

The equivalence includes the entire observed wrapped $v$ prefix.
Outside this overlap the single admissible candidate is recovered.
Consequently the family has no exact recovery of $T_t$, of its signed
parameter, or of any one height $K_s$, $0\le s\le t$, at any fixed
finite positive horizon. On each sign law the singleton event also
has positive probability. Thus nonrecovery is a local overlap
obstruction, not equivalence of the two full observation laws.

More completely, let $h(\kappa,k)$ be any Borel target function on
$\mathcal K_{\rm cal}\times C([0,t],I)$ with values in a standard Borel
space. It has exact family recovery if and only if, for every
$r\in(0,\delta]$,

$$
h(r,u+\alpha_+)=h(-r,u+\alpha_-)
\quad\hbox{for }\Lambda_t\hbox{-almost every }u\in E_+\cap E_-.
\tag{64.4}
$$

Here $\Lambda_t=\int_{\mathbb R}da\,\mathbb P_a^{\sigma\rm BM}$
is the Brownian-height reference measure, with variance rate
$\sigma^2$. Thus (63.1), with (64.2) understood, is a complete
recoverable quotient relative to this target. Equality is required
modulo the actual common-law null sets, not on every algebraically
possible continuous path. The observation still contains ancillary
phase randomness; no equality of its entire sigma-field with the
quotient sigma-field is asserted.

Proof. The exact stationary Q density of height relative to Brownian
height on $[0,t]$ is the already proved (56.8). Translating height by
$\alpha_s$ therefore gives

$$
f_s(u)=e^{\lambda t}\phi(u_0+\alpha_s)\phi(u_t+\alpha_s)
             \mathbf1_{E_s}(u)
\tag{64.5}
$$

relative to $\Lambda_t$. This is an identity for the actual source:
its initial density is $\phi(k_0)^2$, its Doob factor is
$e^{\lambda t}\phi(k_t)/\phi(k_0)$, and translation preserves Brownian
increments and Lebesgue initial measure. In particular the two laws
are not obtained by replacing the Q drift with a translation-invariant
one. Their shifted drifts generally differ.

Conditional on $u$, both sign laws have the identical original phase
kernel $\Gamma_r(dv\mid u)$: its continuous real increments are

$$
v_a-v_0=-\frac1{\sqrt2H}\int_0^a F_r(u_s)\,dW_s^2,
\qquad 0\le a\le t,
\tag{64.6}
$$

then wrapped with the prescribed common initial phase. The driver is
independent of height. On paths outside the two admissible domains
extend this kernel arbitrarily; the densities (64.5) vanish there.
The joint densities of $(u,v)$ are exactly $f_s(u)$ with respect to
$\Lambda_t(du)\Gamma_r(dv\mid u)$. Both are strictly positive on
the overlap. This proves (64.3), equivalence there and the absence of
any additional sign information from the conditional phase noise.

The interval $I_+\cap I_-$ has length $w-2r\ge3w/4>0$.
Brownian height started with Lebesgue measure in a smaller interior
interval has positive probability of remaining there for any fixed
finite $t$. The endpoint weights in (64.5) are positive. Hence the
common overlap has positive probability under both actual laws.
Conversely, under the plus law $K_0\in(l,l+2r)$ has positive
probability and implies $u_0\notin I_-$; under the minus law use
$K_0\in(u-2r,u)$. These are positive-probability singleton events.
Membership of $E_s$ is Borel: on a compact time interval it is exactly
the strict lower and upper bounds on the continuous path's extrema.
Any actual finite Q path belongs to its own $E_s$.

Theorem 63.1 supplies $r,u$ from the observation. If (64.4) holds,
select the plus candidate when admissible and otherwise the minus
candidate, and output $h$ of that target. This is Borel, also jointly
in $r$. For the true minus law its only possible error is the subset
of the overlap where (64.4) fails. Equation (64.5) makes that subset
null. The plus and zero laws are handled directly. This proves
sufficiency with the parameterwise quantifiers in Definition 62.1.

For necessity suppose a common observation decoder recovers $h$ for
both parameters $r,-r$. Restrict their joint laws to the overlap.
By their equivalence, both equalities for that same decoder hold
almost everywhere under the common reference restricted there.
Their right sides are respectively the two sides of (64.4), functions
of $u$ alone. Integrating out the probability kernel $\Gamma_r$ forces
(64.4) for $\Lambda_t$-almost every such $u$. Apply this argument for
each $r$. The signed targets differ by $2r$ and their heights differ
by the constant $2r$ at every time, proving all the stated failures.
This argument is a witness under actual source measures, and not
merely a collision of (62.3). $\square$

**Proposition 64.2 (the exact supplied-prior posterior).** Disintegrate
any Borel parameter prior over $r=|\kappa|$. For almost every nonzero
$r$ under its magnitude marginal, let $p_+(r),p_-(r)$ be its
conditional sign probabilities. After observing a positive prefix
with recovered $(r,u)$ the posterior weights of the two targets
in (64.2) are

$$
P_s(r,u)=
\frac{p_s(r)\phi(u_0+\alpha_s)\phi(u_t+\alpha_s)
                  \mathbf1_{E_s}(u)}
 {\sum_{j\in\{+,-\}}p_j(r)\phi(u_0+\alpha_j)
                       \phi(u_t+\alpha_j)\mathbf1_{E_j}(u)}.
\tag{64.7}
$$

The denominator is positive almost surely. At zero the posterior
target is $(0,u)$. In particular with positive prior weight on both
signs at a fixed magnitude, both posterior weights are strictly
positive throughout the overlap modulo null sets. With only one
prior sign the parameter and heights are exactly recoverable.

Proof. Conditional on $r$, multiply (64.5) by $p_s(r)$ and use the
same phase kernel (64.6). Bayes' formula cancels this kernel and
$e^{\lambda t}$. Since $r,u$ are themselves recovered, conditioning
on the entire observation yields (64.7). Standard Borel
disintegration defines $p_s$ up to the stated marginal null sets;
no conditional probability at an unspecified zero-mass magnitude
is required. The zero case follows from Theorem 63.1. $\square$

## 65. A positive all-estimator task-risk obstruction

**Theorem 65.1 (one explicit paired native experiment).** Fix any
$r\in(0,\delta]$ and finite $t>0$. Supply exactly the prior
$\nu_r=(\delta_r+\delta_{-r})/2$, independent of the same stationary
Q height source, with the same original clock and initial phases.
For every estimator $(\widehat\kappa,\widehat k)$ based on the complete
wrapped $v$ prefix, including completed-data or independently randomized
estimators, there is an explicit $m_{r,t}>0$ such that

$$
\begin{aligned}
\mathbf E_{\nu_r}(\widehat\kappa-\kappa)^2&\ge r^2m_{r,t},\\
\mathbf E_{\nu_r}(\widehat k-K_t)^2&\ge r^2m_{r,t},\\
\mathbf E_{\nu_r}\bigl[(\widehat\kappa-\kappa)^2+
                              (\widehat k-K_t)^2\bigr]&\ge2r^2m_{r,t}.
\end{aligned}
\tag{65.1}
$$

For sign classification the error probability is at least
$m_{r,t}/2$. Each bound also lower-bounds the maximum of the two
corresponding parameterwise risks. It does not say that every
estimator has positive parameter risk at each individual parameter:
a constant correct parameter estimator is the elementary exception.
No prior is implicit in a parameterwise statement.

Proof. Set $m=(l+u)/2$ and choose the closed common interval

$$
J=[m-r^2/H-w/8,\ m-r^2/H+w/8],\qquad L=|J|=w/4.
\tag{65.2}
$$

For either sign, $J+\alpha_s$ is centered at $m+sr$ and has radius
$w/8$; since $r\le w/8$, it lies strictly inside $I$. Put

$$
a_J=\min_{s\in\{+,-\},\ z\in J}\phi(z+\alpha_s)>0,
\qquad
m_{r,t}=e^{\lambda t}a_J^2\frac{8L}{\pi^2}
                   \exp(-\varepsilon^2\pi^2t/L^2)>0.
\tag{65.3}
$$

In fact $J+\alpha_s\subset[m-w/4,m+w/4]$, so $a_J^2\ge1/w$
and $m_{r,t}\ge(2/\pi^2)e^{-15\lambda t}$ throughout this fixed
nonzero family. The task-risk bound still has the factor $r^2$.

Let $\Lambda_{J,t}$ be Brownian height with Lebesgue initial measure
on the interior of $J$, restricted to paths staying in that interior
up to $t$. Define a common submeasure of the two actual joint laws by

$$
M(du,dv)=e^{\lambda t}
 \min_{s\in\{+,-\}}\{\phi(u_0+\alpha_s)\phi(u_t+\alpha_s)\}
 \Lambda_{J,t}(du)\Gamma_r(dv\mid u).
\tag{65.4}
$$

This is dominated by each sign's joint law in (64.5)–(64.6), retaining
its actual target. Its mass is at least $m_{r,t}$: integration of the
Dirichlet sine kernel over both endpoints of an interval of length $L$
gives

$$
\Lambda_{J,t}(1)=\sum_{n\ge1,\ n\ {
\rm odd}}\frac{8L}{n^2\pi^2}
                  e^{-\varepsilon^2n^2\pi^2t/L^2},
\tag{65.5}
$$

and its first term suffices. This is the same killed Brownian
calculation as (37.3); it is only a reference submeasure inside the
unchanged conservative Q experiment, not a new killed observation law.

On this common submeasure put $c=u_t+r^2/H$. The two target pairs
are $(r,c+r)$ and $(-r,c-r)$. For any real $a,b$,

$$
\frac{(a-r)^2+(a+r)^2}{2}\ge r^2,\qquad
\frac{(b-c-r)^2+(b-c+r)^2}{2}\ge r^2.
\tag{65.6}
$$

Integrating these inequalities against $M$ proves (65.1), because
each source risk dominates its $M$ loss and the prior weights are
$1/2,1/2$. A binary decision is wrong for at least one of the two
labels at every common data value, giving $M(1)/2$. Adding the same
independent randomization kernel preserves the argument. Completed
estimators have Borel versions under the mixture law, whose null sets
are null under both components. Finally an average of two risks is
at most their maximum. The lower bound may tend to zero with $r$ or
with increasing $t$; neither a uniform positive bound near zero nor
an infinite-window obstruction is claimed. No Q risk is transferred
to a survivor or raw killed source here. $\square$

## 66. The least original-coordinate augmentations

**Theorem 66.1 (either other original phase is sufficient and minimal).**
Among augmentations of the stipulated $v$ record by subsets of the
other original continuous wrapped coordinate records $\theta,D$,
the two inclusion-minimal sufficient choices are $\{\theta\}$ and
$\{D\}$. Each recovers the signed parameter and whole height prefix
at every positive time by one parameter-independent causal Borel
construction, with one lawwise null set for all positive times.
The assertion includes actual zero with frozen $D$.

Proof. Lift each supplied circle path causally using its known initial
phase. Use polarization of the dyadic variation sums for cross
variations. Theorem 63.1 first gives $r,U$. At a positive time put
$c=U+r^2/H=K-\kappa$. By the original probability margins,

$$
H-c=H+\kappa-K>0,\qquad
c^2-r^2=K(K-2\kappa)>0.
\tag{66.1}
$$

From $v,\theta$ compute

$$
q_\theta=\frac{\partial_-[\theta,v]}{\partial_-[v]}
        =\frac{A_\kappa(K)}{B_\kappa(K)},\qquad
R=1-q_\theta=\frac{H+\kappa}{K}.
\tag{66.2}
$$

Here $\partial_-[v]>0$ and $R-1=(H-c)/K>0$. Since
$R(c+\kappa)=H+\kappa$, the signed recovery formula is

$$
\kappa=\frac{H-Rc}{R-1},\qquad K=c+\kappa.
\tag{66.3}
$$

It works also at zero. Alternatively, from $v,D$ compute

$$
q_D=\frac{\partial_-[D,v]}{\partial_-[v]}
   =\frac{\kappa b_\kappa(K)}{B_\kappa(K)}
   =-\frac{2\kappa(H-c)}{c^2-r^2}.
\tag{66.4}
$$

Both factors in (66.1) are strictly positive. Hence for $r>0$,
$\kappa=-r\operatorname{sign}(q_D)$; for $r=0$, set $\kappa=0$.
Then $K=U+\kappa+r^2/H$. At zero (66.4) is exactly zero because
the actual $D$ is frozen; it is not an observation of comparison $x$.
All cross variations and left derivatives are available from the
supplied prefixes, and the single-null-set localization argument of
Theorem 63.1 applies to these finitely many additional operations.
Continuity recovers the entire prefix, including $K_0$.

The empty augmentation is insufficient by Theorem 65.1 under the
explicit paired actual-source prior. Both singleton augmentations
are sufficient by the formulas just proved, and the pair
$\{\theta,D\}$ contains either sufficient singleton. These exhaust
the four stipulated subsets and prove minimality in that comparison.
No assertion about arbitrary sensors or a minimum nonlinear observer
state dimension is used. $\square$

## 67. Finite windows, infinite histories and the time-zero boundary

**Theorem 67.1 (resolution in time and the initial germ).** For the
original $v$ experiment the following distinctions hold.

For each $r>0$ and either actual sign, the candidate set (64.2)
eventually becomes a singleton at some finite random positive horizon,
almost surely. Nevertheless no deterministic finite horizon suffices
almost surely for family signed-parameter recovery. On the infinite
continuous history,

$$
\inf_{s\ge0}U_s=l-\alpha_\kappa,\qquad
\sup_{s\ge0}U_s=u-\alpha_\kappa,\qquad
\kappa=l-\inf_{s\ge0}U_s-r^2/H,
\tag{67.1}
$$

almost surely; thus the full target history is recovered. At zero
there is already positive-prefix recovery by Theorem 63.1.

At time zero alone, known initial phases leave $K_0$ with law $\pi$;
under any supplied parameter prior the posterior joint law of
$(\kappa,K_0)$ is exactly $\nu\otimes\pi$. The positive-time germ
$\mathcal H_{0+}^v=\bigcap_{t>0}\mathcal H_t^v$ contains $r,U_0$.
For the paired prior $\nu_r$ its sign posterior, conditional on that
germ, is

$$
P_s^{0+}(r,a)=
\frac{\phi(a+\alpha_s)^2\mathbf1_{I_s}(a)}
 {\phi(a+\alpha_+)^2\mathbf1_{I_+}(a)+
  \phi(a+\alpha_-)^2\mathbf1_{I_-}(a)}.
\tag{67.2}
$$

In particular the germ does not resolve the signs on the initial
interval overlap, which has positive probability. Null completion
alone never converts $\mathcal H_0^v$ into this germ.

Proof. By (37.9), choose a fixed $T$ large enough that the Q height
transition density relative to $\pi$ is at least $1/2$ everywhere.
For any nonempty open $A\Subset I$, the conditional chance of
$K_{nT}\in A$ is at least $\pi(A)/2$, uniformly in the preceding
history. Iterating the conditional bound shows that avoiding $A$
for $n$ such trials has probability at most
$(1-\pi(A)/2)^n$. The same argument from every trial index proves
visits at arbitrarily large times. Apply it to countably many
intervals approaching each endpoint. Thus $\inf K=l,\sup K=u$
almost surely, proving (67.1).

For the plus sign, a visit to $(l,l+2r)$ excludes the minus
candidate, since its translated candidate height is $K-2r\notin I$.
For the minus sign a visit to $(u-2r,u)$ excludes the plus candidate.
Such visits occur in finite time by the same argument. Candidate
sets decrease as the horizon grows. This proves eventual resolution;
Theorem 65.1 supplies the positive obstruction at every deterministic
finite horizon. The bounds are consistent because their overlap
mass need not stay bounded away from zero as $t\to\infty$.

For the germ statement Theorem 63.1 gives $r,U_0$ on every positive
prefix, using the same maps and null conventions. Under $\nu_r$,
(64.7) is the posterior of the sign on each $\mathcal H_t^v$.
Let $t\downarrow0$ along $1/n$. For an initial point strictly inside
both $I_s$, continuity keeps the path inside both for all sufficiently
small times. If it is outside one interval, that candidate is already
excluded at zero. Initial points at the finitely many interval
endpoints have probability zero under the continuous initial density.
Since $U_t\to U_0$, (64.7) converges to (67.2). To justify conditioning
on the intersection, put $p_n=\mathbf E[\mathbf1_{\{\kappa=sr\}}
\mid\mathcal H_{1/n}^v]$. For $m>n$, nested conditional expectation
and orthogonality give
$\|p_n-p_m\|_2^2=\|p_n\|_2^2-\|p_m\|_2^2$.
The decreasing bounded squared norms make $(p_n)$ Cauchy in $L^2$.
Its limit has a version measurable in every completed
$\mathcal H_{1/n}^v$, hence in their intersection; integrating against
any bounded intersection-measurable function identifies it as the
conditional expectation on that intersection. The explicit bounded
pointwise limit (67.2) is the same $L^2$ limit. This is the classical
reverse-martingale projection argument, applied here to the native
posterior, and proves the claim for $\mathcal H_{0+}^v$.
Both weights are positive on the initial overlap; the corresponding
heights differ by $2r$. This proves the claimed initial-target
ambiguity even for the germ. At time zero the raw observation is
constant, and completion changes conditional laws only on null sets,
which proves the separate $\nu\otimes\pi$ assertion. $\square$

**Proposition 67.2 (sampling and calibration are separate limitations).**
For every finite collection of deterministic phase sample times in a
positive finite window, the original wrapped $v$ samples do not recover
height even at a supplied known parameter. A prior giving positive
weight to two distinct parameters prevents exact signed-parameter
recovery from those samples. Exact magnitude recovery also fails when
the two absolute values differ, and sign classification fails when
the two nonzero signs differ. These facts coexist with Theorem 63.1
and the infinite-history conclusion above.

Proof. Reuse Theorem 58.2, whose strictly positive conditional wrapped
Gaussian density argument applies also to unequal positive spacings.
The single-time sample case is included. In the paired experiment,
under either parameter the vector of noninitial wrapped phase samples
has a strictly positive density with respect to the same finite
product of circle Lebesgue measures: condition on height and use the
positive Gaussian periodization (58.3), then integrate. Thus the two
sample laws are equivalent, for any two distinct parameters in the
fixed family, including a zero and a nonzero one. No exact test can
separate either signs or distinct magnitudes from those finite samples.
For height use the already proved known-parameter result; removing
calibration information cannot improve an exact recovery task.
A finite ideal continuous prefix supplies infinitely many variation
increments, so is a different experiment. $\square$

## 68. Native correspondence, credited tools and geometric scope

**Definition 68.1 (suppliers and the remaining interpretation boundary).**
The hypotheses and coefficients in §§62–67 are exactly G (25.1)–(25.5),
L (35.1)–(35.2), (37.2), (37.8)–(37.9) and Definition 55.1.
Theorem 55.2 is reused for causal lifting, variation versions and
known-calibration height recovery; Theorems 56.1 and 57.1–57.3 concern
known-parameter rational projections and characters. They do not supply
an unknown signed calibration. Theorems 58.2–59.1 keep their
known-parameter finite-sample meanings and their stationary Q risk.
The new native content is (63.2)–(63.5), the translated actual-law
quotient (64.4) and posterior (64.7), its paired-source risk (65.1),
and the signed minimal original-coordinate recovery (66.2)–(66.4).
These statements are `repo-derived`; no worldwide priority is asserted.

The intermediate quadratic-variation and Itô operations are classical.
H. Föllmer, *Calcul d'Itô sans probabilités*,
[primary text, pp.143–150](https://www.numdam.org/item/SPS_1981__15__143_0/),
defines variation along fixed refining subdivisions and proves the
$C^2$ change-of-variable formula. Here the localized semimartingale
convergence and common versions are supplied by Theorem 55.2; arbitrary
continuous paths are not presumed to satisfy them. Iterating that
calculus gives (63.3)–(63.4), while their rational inverse is native.
The ground-state density calculation is the classical Doob transform
already proved in Theorem 37.2. The common-submeasure testing argument
and Bayes disintegration in §§64–65 are classical statistical tools;
the exact common measures and targets here are (64.5) and (65.4),
and the squared-loss bounds are derived directly in (65.6).
The classical decreasing-field $L^2$ projection argument is supplied
inside the proof identifying the germ conditional expectation (67.2).

K. D. Elworthy, Y. Le Jan and X.-M. Li,
*The Geometry of Filtering*,
[arXiv:0810.2253v1](https://arxiv.org/html/0810.2253v1), §§2.4 and 5.1,
provides the projectible-symbol and non-Markovian filtering background.
Section 2.4 assumes a projectible constant-rank symbol; §5.1 assumes
conservative cohesive descent with a conservative reference and a
horizontal drift correction. The projection onto $v$ has variance
$2B_\kappa(K)^2$ depending on the hidden height, so merely supplying
its history does not meet that projectible-symbol hypothesis. No
identification theorem from that framework replaces the explicit
translated stationary density or unknown-parameter inverse here.
The [fixed-probability relative-phase torus bijection](https://github.com/the-omega-institute/trureturing/blob/6198ac3642d19f48f815df872aef049954aca64b/D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber.lean)
concerns a different target: phases conditional on supplied basis
probabilities. Its private reconstruction proof and public bijection do
not supply the missing native parameter or unobserved height in this
stochastic experiment.

**Proposition 68.2 (compatibility with memory and effective phase rank).**
The family quotient above refines the observation question without
altering Theorems 49.1, 50.1, 54.1 or 60.1. In particular it implies
no physical spatial dimension, physical $SO(3)$ symmetry or acquisition
service. The instantaneous native phase rank, effective long-time
phase rank and current-state manifold dimension remain different
quantities.

Proof. At each fixed parameter the same height source, coefficient
functions and original clock are used. Thus the compression defect
of F Proposition 5.1 and its native consequences (49.3), (50.1)–(50.2)
are unchanged. Pathwise height recovery at known calibration was already
compatible with nonzero eliminated-height memory in Proposition 60.1.
With unknown calibration (63.1) initially leaves the two translated
possibilities, and (64.3) explains their finite-prefix overlap without
making $v$ autonomous. At a resolved sign, the old known-parameter
inverse (55.4) and the new reconstruction agree on the actual height.
At actual zero they both give $K=Z$ and frozen $D$.

Theorem 40.1 still gives instantaneous phase rank one and full symbol
rank two, whereas the temporal covariance averages have effective
phase rank three at fixed nonzero parameter and rank two on the actual
zero leaf. The state-manifold and current-ray counts in §§39–40 have
their own definitions; a statistical parameter is not another moving
spatial coordinate. N Theorem 10.5 still obstructs a smooth same-clock
elliptic three-dimensional factor. Neither recovery of a parameter
nor adding an observed original phase changes that symbol. Therefore
no implication to physical three-space, a minimum nonlinear state
count, finite bit/shot/CPU resources or an empirical realization follows.
The native physical-observation bridge remains unspecified. The risk
and posterior assertions here concern conservative stationary Q only;
Proposition 60.2 retains its distinct raw and terminal-survivor weights,
and no unchanged risk is inferred for those laws. $\square$

## 追加锚（本行以下为增补区）

## 69. The full-state attractive threshold problem

**Definition 69.1 (weak-binding continuation).** On the fixed nonzero signed-$\kappa$ cover of Definition 35.1, let $S=B_\kappa-\lambda$ and fix $a,\tau>0$.
The cutoff field $W_\tau=\int_\tau^\infty e^{\lambda t}g_\kappa^I(t;k_0,k;q)dt$ and the full-domain form $a\|S^{1/2}\psi\|_2^2-g\int W_\tau|\psi|^2$ are treated in [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), §§70–74.

## 追加锚（本行以下为增补区）
