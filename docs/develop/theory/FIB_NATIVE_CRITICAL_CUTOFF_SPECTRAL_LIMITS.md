# Native critical-cutoff energies and complete ground-state laws

## 31. The original critical families and scalar comparison

**Definition 31.1 (inherited native contract and critical parameters).**
Let [G] denote
[Native two-control Green stability](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md).
Retain exactly [G, Definition 25.1], its fixed data, pole, raw measure,
original clock, both absorbing height faces, complete form domain and
two interaction conventions. In particular, every phase has period
$2\pi$, $a=|\kappa|$, and the sign of $\kappa$ is unrestricted.
The symbols $I,B,\Omega,\phi,\lambda,A_\kappa,B_\kappa,b_\kappa,
S,V,W_\sigma,T_\kappa,\mathcal F_\kappa,E_\sigma$ have precisely their
meanings in [G, (23.3), (25.3)--(25.9)]. Set

$$
\begin{aligned}
J_\phi&=\int_I\phi(k)\,dk,&
b_0(k)&=\frac{H-k}{Hk},&
\beta&=\int_I b_0(k)^2\phi(k)^2\,dk>0,\\
G_t(D)&=\frac1{2\pi}\sum_{j\in\mathbb Z}e^{-tj^2}e^{ijD}
\quad(t>0),&
\rho(D)&=\operatorname{dist}_{\mathbb T}(D,0),\\
L_a&=\log(1/a),&
\tau_s&=\frac{L_a-\frac12\log L_a}{\lambda}+s,
\qquad s\in\mathbb R,\\
\tau_b&=b/a^2,\qquad b>0,&
r_s&=a\sqrt{\tau_s},\\
c_0&=\frac1{\lambda J_\phi(2\pi)^2},&
c_s&=\frac{\phi(k_0)e^{-\lambda s}}
                 {(2\pi)^2\sqrt{4\pi\beta\lambda}}.
\end{aligned}
\tag{31.1}
$$

The two times exceed $\tau_{\min}$ for all sufficiently small $a$.
$G_t$ is a density relative to raw $dD$, so $\int_{\mathbb T}G_t\,dD=1$.
For $c\ge0$ let $e(c)$ and $u_c$ be the lowest eigenvalue and positive
$L^2(dk)$-normalized eigenfunction of the scalar Dirichlet operator

$$
H_c=-\varepsilon^2\partial_k^2-c\phi(k),
\qquad Q(H_c)=H_0^1(I).
\tag{31.2}
$$

Thus $e(0)=\lambda$ and $u_0=\phi$. All limits below fix the original
$s,b,g$ and every datum in [G, (25.1)]; none is an
$\varepsilon\to0$ or shrinking-coupling assertion.
The native statements below are repository-derived consequences of the
exact suppliers [G, §§23,25--29]. The classical tools used inside their
proofs are bounded selfadjoint form perturbation, the min-max principle,
and the bounded-potential Trotter formula, in the scopes of G. Teschl,
*Mathematical Methods in Quantum Mechanics*, GSM 99, author text,
[Theorems 6.24, 4.10 and 5.11](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)
(printed pp.150, 119 and 132), respectively. These are
literature-attested tools, not suppliers of a
native critical limit. The unsmoothed restricted theorem in
[Observation quotient, Theorem 11.1](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md)
has a strict small-coupling hypothesis and a different field; it is not
used as a critical-cutoff convergence theorem here.

## 32. Sharp slow modes, fields and sources on the original circles

**Theorem 32.1 (native long-time local and circle limits).**
Write $p_\kappa(t,y)=p_\kappa(t,o,y)$. If $\kappa\to0$ through either
sign, $t\to\infty$, and $r=a\sqrt t\to0$, then

$$
\sup_{k,\theta,v,D}\left|
r e^{\lambda t}p_\kappa(t,k,\theta,v,D)
-\frac{\phi(k_0)\phi(k)}{(2\pi)^2\sqrt{4\pi\beta}}
 \sum_{h\in\mathbb Z}
 \exp\!\left(-\frac{(D+2\pi h)^2}{4\beta r^2}\right)
\right|\longrightarrow0.
\tag{32.1}
$$

Represent $D$ in $[-\pi,\pi]$ in this formula; the sum is periodic.
If instead $a^2t\to b\in(0,\infty)$, then uniformly on $\Omega$,

$$
e^{\lambda t}p_\kappa(t,k,\theta,v,D)
\longrightarrow
\frac{\phi(k_0)\phi(k)}{(2\pi)^2}G_{\beta b}(D).
\tag{32.2}
$$

Proof. Use precisely the scalar operators and complete Fourier
decomposition of [G, (26.5), (26.12)--(26.14)]. Their resolved frequency
is $\eta=(n,m,\kappa j)$, not $(n,m,j)$. The part with $(n,m)\ne(0,0)$
satisfies, for all sufficiently large $t$,

$$
e^{\lambda t}\sup_y\left|
\frac1{(2\pi)^3}\sum_{(n,m)\ne(0,0),j}
 e^{i(n\theta+mv+jD)}K_{\kappa,(n,m,\kappa j)}(t;k_0,k)
\right|
\le Ce^{-dt}(1+r^{-1})
\tag{32.3}
$$

for fixed $d>0$. Indeed the separation inequality preceding [G, (26.14)]
extracts a fixed exponential from the nonzero visible frequency; the
remaining three sums are bounded by the same integral comparison as
there. This justifies absolute summation and is uniform up to both
height faces.

For the remaining modes put $q=\kappa j$ and consider
$H_I+q^2b_\kappa^2$, where $H_I=-\varepsilon^2\partial_k^2$ is
Dirichlet. Denote its first eigenvalue and positive normalized
eigenfunction by $\Lambda_\kappa(q)$ and $v_{\kappa,q}$. Uniformly for
small $|q|$ and small $|\kappa|$,

$$
\begin{aligned}
\Lambda_\kappa(q)&=\lambda+\beta_\kappa q^2+O(q^4),
&\beta_\kappa&=\int_I b_\kappa^2\phi^2\,dk\longrightarrow\beta,\\
\|v_{\kappa,q}-\phi\|_{H^2(I)}&\le Cq^2.
\end{aligned}
\tag{32.4}
$$

Here is a direct justification of the perturbative estimate. Bounded
real multiplication leaves the scalar Dirichlet form closed (the
relative form bound in Teschl's Theorem 6.24 is zero). Its operator
domain is fixed as well: in the form representation equation the bounded
term can be moved to the $L^2$ right side, leaving exactly the defining
equation for membership in $D(H_I)$. Min-max gives
$\lambda\le\Lambda_\kappa(q)\le\lambda+Cq^2$ and second eigenvalue
at least $4\lambda$. Take $|q|$ small so the first is below $2\lambda$.
Existence follows from scalar compactness; the first eigenfunction can
be chosen positive by the one-dimensional Dirichlet equation and is
simple by the constant-Wronskian argument. Write
$v=z\phi+h$ with $h\perp\phi$ and $z>0$. Projecting its equation gives

$$
(H_I-\Lambda_\kappa(q))h
 =-q^2(1-|\phi\rangle\langle\phi|)(b_\kappa^2v).
$$

The inverse on $\phi^\perp$ has uniformly bounded norm from $L^2$ to
$H^2\cap H_0^1$, since that spectrum starts at $4\lambda$ and
$\Lambda<2\lambda$. Hence $\|h\|_{H^2}\le Cq^2$ and
$z=1+O(q^4)$. Projection onto $\phi$ now gives (32.4).
Sobolev embedding makes its eigenfunction error uniform in height.

For $|q|$ in this small fixed interval the scalar kernel is

$$
K_{\kappa,(0,0,q)}(t;k_0,k)
 =e^{-t\Lambda_\kappa(q)}v_{\kappa,q}(k_0)v_{\kappa,q}(k)
  +R_{\kappa,q}(t;k_0,k),
\qquad |R_{\kappa,q}|\le C e^{-4\lambda t}.
\tag{32.5}
$$

For the last bound, split off fixed positive smoothing intervals at both
ends of the semigroup. Scalar domination by $h_I$, obtained by the
bounded-potential Trotter formula, bounds their evaluation norms
uniformly. The remaining semigroup on the complement of its first
eigenfunction has norm at most $e^{-4\lambda(t-2\delta)}$.
Absorb the fixed $e^{8\lambda\delta}$ in $C$. No infinite sum of the
unsummed remainder bound in (32.5) is taken.

In the regime $r\to0$, set $z_j=rj$. On $|z_j|\le R$ one has
$q^2=z_j^2/t$, and therefore, uniformly on this set and in $k$,

$$
e^{\lambda t}K_{\kappa,(0,0,\kappa j)}(t;k_0,k)
 -\phi(k_0)\phi(k)e^{-\beta z_j^2}\longrightarrow0.
\tag{32.6}
$$

The number of these summands times $r$ is bounded for each fixed $R$.
For the tails use [G, (26.12)] with
$\Psi(x)=x^2$ for $x\le1$ and $x^{2/3}$ for $x\ge1$.
Where $a|j|\le1$, its exponential is bounded by $Ce^{-c z_j^2}$.
Thus its $r$-weighted sum over $|z_j|>R$ tends uniformly to zero as
$R\to\infty$, by the elementary Gaussian integral comparison on a
lattice of spacing $r\to0$. Where $a|j|>1$, that weighted sum is at most

$$
Cr e^{-ct}+C\sqrt t\int_1^\infty e^{-ct x^{2/3}}\,dx
\longrightarrow0.
$$

The comparison Gaussian has the same Gaussian tail bound. Taking
$\kappa\to0$ first and $R\to\infty$ second proves

$$
r\sum_j\sup_k\left|
e^{\lambda t}K_{\kappa,(0,0,\kappa j)}(t;k_0,k)
-\phi(k_0)\phi(k)e^{-\beta r^2j^2}\right|\longrightarrow0.
\tag{32.7}
$$

The Fourier coefficients of the periodized Gaussian, computed by
integrating its translates on $\mathbb R$, give the identity

$$
G_{\beta r^2}(D)=\frac1{\sqrt{4\pi\beta}\,r}
 \sum_{h\in\mathbb Z}e^{-(D+2\pi h)^2/(4\beta r^2)}.
\tag{32.8}
$$

Combining (32.7), (32.3) and the original prefactor $(2\pi)^{-3}$
proves (32.1). The visible zero modes supply a factor $2\pi G$, so
the remaining visible normalization is $(2\pi)^{-2}$.

For $a^2t\to b>0$, each fixed $j$ in (32.4)--(32.5) converges instead
to $\phi(k_0)\phi(k)e^{-\beta b j^2}$. There is a summable dominator:
for $a\le1$, $\Psi(a|j|)/a^2\ge\Psi(|j|)$, and eventually
$a^2t\ge b/2$. Thus [G, (26.12)] bounds the summand by
$Ce^{-cb\Psi(|j|)/2}$, uniformly in height. Dominated summation and
(32.3) prove (32.2). These arguments cover arbitrary sequences satisfying
the stated scales, so all convergences also hold uniformly when time is
in a fixed bounded window about either prescribed cutoff. $\square$

**Theorem 32.2 (critical multipliers and effective source measures).**
For each fixed $s\in\mathbb R$ and $b>0$, uniformly on $\Omega$,

$$
\begin{aligned}
V_{\kappa,\tau_s}(k,\theta,v,D)
 &=c_s\phi(k)\exp\!\left(-\frac{\rho(D)^2}{4\beta r_s^2}\right)+o(1),\\
W_{\rm unit}(\kappa,\tau_b;k,\theta,v,D)
 &=c_0\phi(k)G_{\beta b}(D)+o(1).
\end{aligned}
\tag{32.9}
$$

The unit effective source, as a density relative to $d\mu$, satisfies

$$
\frac{p_\kappa(\tau_b,o,y)}{S(\tau_b)}
\longrightarrow
\frac{\phi(k)}{J_\phi}\,
 \frac1{(2\pi)^2}G_{\beta b}(D)
\quad\hbox{uniformly}.
\tag{32.10}
$$

At the raw cutoff the same conditional source has, under the actual
representative $D/r_s\in[-\pi/r_s,\pi/r_s]$, the limiting probability law

$$
\frac{\phi(k)}{J_\phi}\,dk\,
\frac{d\theta\,dv}{(2\pi)^2}\,
\frac{e^{-x^2/(4\beta)}}{\sqrt{4\pi\beta}}\,dx.
\tag{32.11}
$$

Its unscaled hidden marginal consequently tends to $\delta_0$.
Source charges and field masses remain distinct:

$$
\begin{aligned}
S(\tau_s)&=\phi(k_0)J_\phi\,
 a\sqrt{L_a}e^{-\lambda s}(1+o(1)),&
\int_\Omega V_{\kappa,\tau_s}\,d\mu&\longrightarrow0,\\
S(\tau_b)&=\phi(k_0)J_\phi\,e^{-\lambda b/a^2}(1+o(1)),&
\int_\Omega W_{\rm unit}(\kappa,\tau_b)\,d\mu
 &\longrightarrow1/\lambda.
\end{aligned}
\tag{32.12}
$$

Proof. The exact height survival expansion [G, (29.1)--(29.2)] gives

$$
S(t)=\phi(k_0)J_\phi e^{-\lambda t}(1+O(e^{-8\lambda t})).
\tag{32.13}
$$

Indeed $\phi(k_0)J_\phi=4\sin(\pi(k_0-l)/d_I)/\pi$, which is its
first sine coefficient. Also

$$
r_s\to0,\qquad \tau_s\to\infty,\qquad
\frac{e^{-\lambda\tau_s}}{r_s}\longrightarrow
\sqrt\lambda e^{-\lambda s}.
\tag{32.14}
$$

Integrate $p_\kappa(\tau_s+v,o,y)$ over $v\ge0$. On every fixed
$0\le v\le R$, (32.1) applies uniformly and
$a\sqrt{\tau_s+v}/r_s\to1$. Uniformly for real $x$,
$e^{-x^2/(4\beta(1+v/\tau_s))}-e^{-x^2/(4\beta)}\to0$;
this follows either by a bounded derivative in the variance parameter or
by splitting $|x|\le M$ and its Gaussian tails. All nonnearest translates
in (32.8) have sum tending uniformly to zero when $r_s\to0$.
The contribution on this time window is therefore, in supremum norm,

$$
\frac{e^{-\lambda\tau_s}}{r_s}
\frac{\phi(k_0)\phi(k)}{(2\pi)^2\sqrt{4\pi\beta}}
e^{-\rho(D)^2/(4\beta r_s^2)}
\int_0^R e^{-\lambda v}\,dv+o(1).
$$

For the omitted tail, the all-time bound [G, (26.1)] gives

$$
\int_R^\infty p_\kappa(\tau_s+v,o,y)\,dv
\le C e^{-\lambda\tau_s}(1+r_s^{-1})e^{-\lambda R}.
\tag{32.15}
$$

The prefactor is bounded by (32.14). Let $R\to\infty$ after taking
the parameter limit. The resulting factor $1/\lambda$ gives exactly
$c_s$ in (31.1), proving the first line of (32.9).

At $\tau_b$, divide (32.2) by (32.13). This proves (32.10). For a
bounded time increment $v$, the divided kernel converges uniformly to
$e^{-\lambda v}\phi(k)G_{\beta b}(D)/(J_\phi(2\pi)^2)$.
For every $v\ge0$, [G, (26.1)] and (32.13) bound it by
$C_b e^{-\lambda v}$. Dominated time integration proves the second
line of (32.9), including its exact $1/\lambda$ factor. Thus neither
time integration requires an interchange without a uniform tail bound.

For (32.11), change variables $D=r_sx$ in (32.1) at time $\tau_s$
and use (32.13). The densities converge uniformly on every bounded
$x$ interval to the displayed density. They are tight in $x$:
conditional on the killed height path up to $\tau_s$, the unwrapped
hidden displacement is centered Gaussian of variance
$2\kappa^2\int_0^{\tau_s}b_\kappa(K_t)^2\,dt\le2M^2r_s^2$,
where $M$ is the uniform coefficient bound in [G, §26].
This is the same original second Brownian driver; the survival event
depends only on the first driver. The actual distance of a wrapped
displacement from zero is no greater than its unwrapped absolute value.
Hence its conditional probability of $\rho(D)>Rr_s$ is bounded by
the centered Gaussian tail with variance $2M^2$, independently of
$\kappa$. Local density convergence and this tightness prove the
probability limit, including its normalization. No independence of the
visible and hidden paths before the limit is asserted.

Finally (32.13), (32.14), and the exact identities
$\int V_{\kappa,\tau}\,d\mu=\int_\tau^\infty S(t)\,dt$ and
$\int W_{\rm unit}\,d\mu=(\int_\tau^\infty S(t)\,dt)/S(\tau)$
from [G, Proposition 29.1] prove (32.12). The unit source in (32.10)
integrates to one, whereas its field in (32.9) integrates to
$c_0J_\phi(2\pi)^2=1/\lambda$. $\square$

## 33. Full minima and all ground-state families

**Theorem 33.1 (sharp complete-domain energies).**
For every fixed $s\in\mathbb R$, $b>0$ and $g>0$, through both signs,

$$
\begin{aligned}
E_{\rm raw}(\kappa,\tau_s;g)&\longrightarrow e(gc_s),\\
E_{\rm unit}(\kappa,\tau_b;g)&\longrightarrow
 e\!\left(gc_0G_{\beta b}(0)\right).
\end{aligned}
\tag{33.1}
$$

These are infima over exactly $\mathcal F_\kappa$ of [G, (25.9)],
not restricted infima.

Proof. For either line put $M=c_s$ or $M=c_0G_{\beta b}(0)$,
respectively, and $c=gM$. Since $\rho\ge0$ and

$$
G_t(0)-G_t(D)=\frac1\pi\sum_{j\ge1}
 e^{-tj^2}(1-\cos(jD))\ge0,
\tag{33.2}
$$

(32.9) gives $W_\kappa\le M\phi+o(1)$ uniformly. By [G, (26.13)],
or by the height-slice Dirichlet inequality on its complete domain,

$$
T_\kappa[f]-c\int_\Omega\phi|f|^2\,d\mu
\ge e(c)\|f\|_2^2.
\tag{33.3}
$$

Indeed each scalar Fourier summand is $H_c$ plus the nonnegative
potential $(nA_\kappa+mB_\kappa+\kappa j b_\kappa)^2$.
Summing its scalar variational inequality is legitimate on the exact
completed domain. This proves the lower limit for every normalized
state, without a compactness assumption.

For the upper limit take a real $F\in C_c^\infty((-1,1))$ with
$\int_{\mathbb R}F^2=1$ and define, in the actual circle chart,

$$
f_\kappa(k,\theta,v,D)=\frac{u_c(k)}{2\pi}
 \ell_\kappa^{-1/2}F(D/\ell_\kappa),
\qquad
\ell_\kappa=
\begin{cases}
a\tau_s^{1/4},&\text{raw},\\
\sqrt a,&\text{unit}.
\end{cases}
\tag{33.4}
$$

For small $a$ its support avoids the phase seam. Height approximation
and the smooth periodic bump put it in $\mathcal F_\kappa$.
The raw Jacobian and visible volume give $\|f_\kappa\|_2=1$ exactly.
Directly from the original $Q_\kappa$,

$$
T_\kappa[f_\kappa]
=\varepsilon^2\|u_c'\|_2^2
 +\frac{a^2}{\ell_\kappa^2}\|F'\|_2^2
                  \int_I b_\kappa^2u_c^2\,dk.
\tag{33.5}
$$

The second term tends to zero. In the raw case
$\ell_\kappa/r_s=\tau_s^{-1/4}\to0$; in the unit case
$\ell_\kappa\to0$. Thus (32.9) shows that the potential expectation
converges to $M\int_I\phi u_c^2\,dk$ in either case. The limiting trial
energy is $e(c)$. Min-max now proves both upper limits and hence (33.1).
No assertion about actual ground-state limits has been inferred from
these trial states. $\square$

**Theorem 33.2 (ground-state laws, base normalization and loss of compactness).**
Choose any normalized ground state $f_\kappa$ for each of the original
forms in either line of (33.1), and put
$c=gc_s$ in the raw case and $c=gc_0G_{\beta b}(0)$ in the unit case.
For every such family its actual probability measures satisfy

$$
|f_\kappa|^2d\mu\ \Longrightarrow
u_c(k)^2\,dk\,\frac{d\theta\,dv}{(2\pi)^2}\,\delta_0(dD).
\tag{33.6}
$$

Their base marginal densities converge in the stronger sense

$$
\left\|\int_{\mathbb T_D}|f_\kappa(k,\theta,v,D)|^2\,dD
       -\frac{u_c(k)^2}{(2\pi)^2}\right\|_{L^1(B,\nu_B)}
\longrightarrow0.
\tag{33.7}
$$

In the raw case, for each $\delta>0$,

$$
\int_{\{\rho(D)>\delta r_s\}}|f_\kappa|^2\,d\mu\longrightarrow0.
\tag{33.8}
$$

On the common raw-measure space $L^2(\Omega,\mu)$, every such normalized
amplitude family converges weakly to zero and has no strongly convergent
subsequence. In particular the limiting probability in (33.6) is not
the square of an $L^2(\mu)$ strong limit.

Proof. At each nonzero parameter, existence of these ground states is
already part of [G, Definition 25.1 and Theorem 20.2]. Their possible
phases and multiplicities play no role below. Define the nonnegative
complete-domain form

$$
\mathcal A_{\kappa,c}[f]
=T_\kappa[f]-c\int\phi|f|^2\,d\mu-e(c)\|f\|_2^2\ge0.
\tag{33.9}
$$

Put

$$
P_\kappa(D)=
\begin{cases}
c_s\exp(-\rho(D)^2/(4\beta r_s^2)),&\text{raw},\\
c_0G_{\beta b}(D),&\text{unit}.
\end{cases}
\qquad M=P_\kappa(0),\quad c=gM.
\tag{33.10}
$$

Then $M-P_\kappa\ge0$, and (32.9), (33.1) give for actual ground states

$$
\mathcal A_{\kappa,c}[f_\kappa]
 +g\int_\Omega\phi(k)(M-P_\kappa(D))|f_\kappa|^2\,d\mu
\longrightarrow0.
\tag{33.11}
$$

Both summands are nonnegative, so both tend to zero.

We next establish the visible-mode separation needed to extract the
base law. For this fixed $c$, there is $d_c>0$, uniform for small
$|\kappa|$, such that whenever $(n,m)\ne(0,0)$ and $q\in\mathbb R$,

$$
\inf\sigma\left(H_c+(nA_\kappa+mB_\kappa+q b_\kappa)^2\right)
\ge e(c)+d_c.
\tag{33.12}
$$

To verify uniformity, regard $\eta=(n,m,q)$ first as a real vector with
$|\eta|\ge1$. The large-frequency bound [G, (26.6)] minus
$c\|\phi\|_\infty$ makes its scalar bottom tend uniformly to infinity
as $|\eta|\to\infty$. On every bounded annulus in $\eta$, the bottom
is continuous in $(\kappa,\eta)$ by the multiplier supremum bound and
min-max. It is strictly greater than $e(c)$: equality at an attained
minimum would force the scalar amplitude to be a multiple of $u_c$
and $(\eta\cdot a_\kappa)u_c=0$ almost everywhere. The positivity of
$u_c$ on $I$ would force the polynomial [G, (26.7)] to vanish
identically. Its coefficient map is invertible on the same closed small
parameter interval, so this would give $\eta=0$. Compactness of the
annulus now gives a positive common gap. Since a nonzero integer pair
$(n,m)$ implies $|\eta|\ge1$, (33.12) follows, including arbitrarily
large compensating hidden frequencies. This last quantifier prevents
silently discarding the original cross terms in $Q_\kappa$.

Let $\Pi_{\rm vis}$ be orthogonal averaging over the two visible phases.
The exact Fourier domain, (33.9), and (33.12) imply

$$
\|(1-\Pi_{\rm vis})f_\kappa\|_2^2
\le d_c^{-1}\mathcal A_{\kappa,c}[f_\kappa]\longrightarrow0.
\tag{33.13}
$$

The scalar operator $H_c$ has a simple first eigenvalue and a positive
gap $\gamma_c$ to its next eigenvalue. These facts follow from the same
scalar compactness and Dirichlet Wronskian argument used in (32.4).
Apply its spectral gap on each height slice; the remaining $Q$ energy
is nonnegative. Projection in height onto $u_c$ therefore also has
squared error at most $\mathcal A_{\kappa,c}[f_\kappa]/\gamma_c$.
This projection commutes with $\Pi_{\rm vis}$. Consequently there are
$h_\kappa\in L^2(\mathbb T,dD)$ with

$$
\left\|f_\kappa-
        \frac1{2\pi}u_c(k)h_\kappa(D)\right\|_{L^2(\mu)}\to0,
\qquad \|h_\kappa\|_2\to1.
\tag{33.14}
$$

For clarity, the gap on height slices is valid without an isotropic
domain assertion: the Fourier characterization gives an $H_0^1(I)$
height derivative in $L^2$ and its Dirichlet spectral decomposition;
equivalently apply the scalar gap to each height coefficient and sum.

For any $f,z\in L^2$, the inequality
$\||f|^2-|z|^2\|_1\le(\|f\|_2+\|z\|_2)\|f-z\|_2$
turns (33.14) into convergence of their densities in $L^1$.
Integrating in $D$ proves (33.7), including all raw angular factors.
Moreover (33.11) and (33.14) give

$$
\left(\int_I\phi u_c^2\,dk\right)
\int_{\mathbb T}(M-P_\kappa(D))|h_\kappa(D)|^2\,dD
\longrightarrow0.
\tag{33.15}
$$

The prefactor is strictly positive and finite. In the raw case the
deficit on $\rho(D)>\delta r_s$ is at least
$c_s(1-e^{-\delta^2/(4\beta)})>0$. In the unit case (33.2), already
its $j=1$ term, makes the deficit strictly positive for $D\ne0$;
by continuity its minimum on $\rho(D)\ge\delta>0$ is positive.
Equation (33.15) thus proves (33.8) in the first case and hidden
concentration at zero in the second. The $L^1$ density approximation
in (33.14) transfers these assertions to the actual ground states.

The approximating densities in (33.14) are products of the fixed
normalized base density and $|h_\kappa|^2dD$, whose total masses tend
to one and which concentrate at zero. This proves (33.6). One can test
against bounded continuous functions on the compact closure of the
cylinder; the fixed base law has no height-boundary mass. Thus the
assertion also gives the usual weak probability limit on the open
cylinder and preserves both height faces.

Finally let $z\in L^2(\mu)$ be fixed. Splitting at $\rho(D)<\delta$,
Cauchy--Schwarz bounds $|\langle z,f_\kappa\rangle|$ by
$\|z1_{\{\rho<\delta\}}\|_2$ plus
$\|z\|_2\|f_\kappa1_{\{\rho\ge\delta\}}\|_2$.
The second term tends to zero for each $\delta>0$, and the first
tends to zero as $\delta\downarrow0$ by absolute continuity of the
integral. Hence $f_\kappa\rightharpoonup0$ for arbitrary phases as
well. A strong subsequence would have the same zero weak limit but
norm one, which is impossible. $\square$

## 34. Actual zero leaf, complete restriction and equality boundary

**Theorem 34.1 (same-clock native comparisons and their probability laws).**
Let $E^0_\sigma(\tau;g)$ denote the actual three-coordinate native
zero-leaf minimum of [G, Definition 23.2], with its raw measure,
unit pole and coupling $g$. Let $E^{\rm sec}_\sigma(\kappa,\tau;g)$
denote the infimum of the original four-coordinate form over the
complete $D$-independent subspace. It has exactly the domain and
isometry of [G, (23.5)]. Then

$$
\begin{array}{c|c|c|c}
\text{original convention and moving time}
 &\text{full nonzero leaf}&\text{actual zero leaf}&\text{complete sector}\\ \hline
\mathrm{raw},\ \tau_s
 &e(gc_s)&\lambda&\lambda\\
\mathrm{unit},\ \tau_b
 &e(gc_0G_{\beta b}(0))&e(gc_0)&e(gc_0/(2\pi))
\end{array}
\tag{34.1}
$$

Each entry is the corresponding limit for every fixed original
$s\in\mathbb R$, $b>0$, $g>0$, through both signs where applicable.
For every normalized ground-state family on the actual zero leaf, its
probability densities on $B$ converge in $L^1$ to
$\phi^2/(2\pi)^2$ in the raw case and to
$u_{gc_0}^2/(2\pi)^2$ in the unit case. For every normalized
sector-ground-state family, its base densities converge in $L^1$ to
$\phi^2/(2\pi)^2$ and $u_{gc_0/(2\pi)}^2/(2\pi)^2$, respectively.
Its full probability is the base probability times $dD/(2\pi)$.

There is a unique $b_*\in(0,\infty)$ such that

$$
G_{\beta b_*}(0)=1.
\tag{34.2}
$$

For $b<b_*$ the full unit-limit energy is strictly below the actual
zero-leaf limit; for $b>b_*$ it is strictly above it. Equality holds
exactly at $b=b_*$. At this parameter, the full limiting ground-state
probability (33.6) equals the actual zero-leaf limiting probability
embedded by $D=0$. For all finite $b>0$ the full unit-limit energy
is strictly below the complete-sector limit. In the raw regime the
full limit is strictly below both comparison energies and its height
law differs from theirs.

Proof. Integrating (32.9) in raw $dD$ and using the exact identity
[G, (23.4)] gives uniformly on $B$

$$
\overline V_{\kappa,\tau_s}\longrightarrow0,
\qquad
\frac{\overline V_{\kappa,\tau_b}}{S(\tau_b)}
\longrightarrow c_0\phi.
\tag{34.3}
$$

The first assertion also follows directly from [G, (29.7)]. At the
actual zero leaf there are only the two visible Fourier indices.
Their nonzero terms have the fixed gap in [G, (26.6)], with
$\eta=(n,m,0)$ and $\kappa=0$; that proof applies to these scalar
operators at zero. The zero angular term is the scalar killed height
kernel. Absolute summation, followed by its sine expansion, yields
uniformly on $B$

$$
e^{\lambda t}p_0(t,q_0,q)
\longrightarrow\frac{\phi(k_0)\phi(k)}{(2\pi)^2}.
\tag{34.4}
$$

The same exponential bound on the nonzero modes gives a uniform time
tail. Thus, with $S$ still the identical height survival law,

$$
V_{0,\tau_s}\longrightarrow0,
\qquad V_{0,\tau_b}/S(\tau_b)\longrightarrow c_0\phi
\quad\hbox{uniformly on }B.
\tag{34.5}
$$

This is a density on the actual three-coordinate leaf, not a
four-coordinate Lebesgue density at zero.

Under $Jh=(2\pi)^{-1/2}h$, the sector form is precisely
$\overline T_\kappa[h]-(g/(2\pi))\int\overline W_\kappa|h|^2\,d\nu_B$,
by [G, (23.5)]. The factor survives division by $S$ unchanged.
For $d\ge0$, the base comparison form
$\overline T_\kappa-d\int\phi|h|^2$ has exact minimum $e(d)$:
every angular Fourier summand is $H_d+(nA_\kappa+mB_\kappa)^2$,
and the normalized angular-constant state $(2\pi)^{-1}u_d$ attains
the lower bound. It is the unique ground ray. Indeed the nonzero
visible modes have a common positive gap above $e(d)$ by the proof of
(33.12) with $q=0$, and the zero angular mode has the scalar gap.
These statements hold uniformly for small $\kappa$, including zero.
Uniform multiplier errors in (34.3)--(34.5) now prove all remaining
energy entries in (34.1) by the variational principle. The same gaps
force the orthogonal complement of $(2\pi)^{-1}u_d$ in every
normalized actual minimizer to tend to zero. Taking absolute squares
proves all asserted $L^1$ base-density limits. The sector's full
$dD/(2\pi)$ law follows exactly from $J$, not from a limiting
approximation.

For completeness $e(c)$ is strictly decreasing. If $c_2>c_1$, its
Rayleigh quotient at $u_{c_1}$ gives

$$
e(c_2)\le e(c_1)-(c_2-c_1)\int_I\phi u_{c_1}^2\,dk<e(c_1).
\tag{34.6}
$$

Also $u_{c_2}^2\ne u_{c_1}^2$: equality would give identical positive
normalized eigenfunctions, and subtraction of their equations would
make $(c_2-c_1)\phi$ constant on $I$, contrary to its sine profile.
The series $G_{\beta b}(0)=(2\pi)^{-1}(1+2\sum_{j\ge1}
e^{-\beta b j^2})$ is continuous and strictly decreasing in $b$,
with limit $1/(2\pi)$ at infinity. Formula (32.8) at zero gives its
limit $+\infty$ as $b\downarrow0$. Since $1/(2\pi)<1$, it crosses
one exactly once. These facts and (34.6) prove all the energy and
height-law comparisons, including their equality exception. $\square$

**Theorem 34.2 (source and domain obstruction despite the equality exception).**
In the unit critical regime the limiting conditional source law of the
full original problem is

$$
\frac{\phi(k)}{J_\phi}\,dk\,
\frac{d\theta\,dv}{(2\pi)^2}\,G_{\beta b}(D)\,dD.
\tag{34.7}
$$

The actual zero-leaf conditional source, embedded in the original
coordinate space, instead tends to

$$
\frac{\phi(k)}{J_\phi}\,dk\,
\frac{d\theta\,dv}{(2\pi)^2}\,\delta_0(dD).
\tag{34.8}
$$

The source obtained by Haar-smearing the original hidden pole, which
implements the averaged field appearing in the complete sector, has
unit conditional limit

$$
\frac{\phi(k)}{J_\phi}\,dk\,
\frac{d\theta\,dv}{(2\pi)^2}\,\frac{dD}{2\pi}.
\tag{34.9}
$$

For every finite $b>0$ these are three different measures. In particular
the energy and ground-probability equality at $b_*$ does not identify
the original source, form domain or killed diffusion with the native
zero leaf. The complete sector is also not the full limiting
ground-state theory. In the raw regime the conditional sources have
the weak zero-leaf limit (34.8), but the full energies and height laws
still differ as in (34.1). Conditional weak source convergence therefore
does not imply convergence of these attractive minima to the zero-leaf
minimum.

Proof. Equation (34.7) is (32.10). Equation (34.4) divided by (32.13)
gives the actual base conditional source; on the actual native histories
$D=0$ identically, so its embedding is (34.8). Hidden translation
averaging commutes with the free operator and height killing; [G,
Theorem 23.3] identifies its source as
$\delta_{q_0}\otimes dD/(2\pi)$ before propagation. Its conditional
density at cutoff is
$\overline p_\kappa(\tau,q_0,q)/(2\pi S(\tau))$. Integrating
(32.10) in $D$ proves (34.9). The heat density $G_{\beta b}$ is smooth
and strictly positive, as is seen from (32.8), and is nonconstant for
finite $b$ because its first Fourier coefficient is nonzero. Thus
(34.7) is neither the singular (34.8) nor the uniform (34.9), even
when its value at zero happens to be one.

These source distinctions use the same raw measures and original
clock. The actual zero-leaf Hilbert space is $L^2(B,\nu_B)$; its
$D=0$ embedding is an embedding of measures, not an isometry into
$L^2(\Omega,\mu)$. The sector, in contrast, is the closed subspace
$\operatorname{Ran}J\subset L^2(\Omega,\mu)$ with the complete domain
in [G, (23.5)]. The full amplitudes are in $\mathcal F_\kappa$ and
have the loss of strong compactness proved in Theorem 33.2. Their
probabilities concentrate at $D=0$, while every sector amplitude has
uniform conditional $D$ law. These facts exhibit the domain and law
obstructions directly, without claiming a general operator-convergence
theorem. In the raw case (32.11) gives the conditional weak source
limit, and (33.1), (34.6) prove the asserted failure of continuity of
the attractive minimum under that weak comparison.

Finally the conditional source is a statement about the original killed
free law at one time. Its normalization does not remove either height
death from $L_\kappa^{-1}$, and neither it nor the amplitude ground
measure specifies a preparation or extra actuator. The finite native
histories and state dimensions remain those of
[Probability, phase transport and holonomy, Theorems 8.2 and 10.3](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md).
Accordingly none of the measure embeddings or spectral equalities
asserts an operational identification or a spatial-dimension selection.
$\square$

## 追加锚（本行以下为增补区）

## 35. Every fixed full eigenvalue and the actual lowest gap

**Definition 35.1 (ordered spectra of the original attractive forms).**
Retain every datum, control, preparation, coefficient, raw measure,
period, source, covariance, clock and boundary of Definition 31.1 and
[G, Definition 25.1]. For nonzero $\kappa$, let

$$
\mathscr H_{\sigma,\kappa,\tau}
 =L_\kappa-gM_{W_\sigma(\kappa,\tau)},\qquad
Q(\mathscr H_{\sigma,\kappa,\tau})=\mathcal F_\kappa,
\qquad D(\mathscr H_{\sigma,\kappa,\tau})=D(L_\kappa).
\tag{35.1}
$$

Write its eigenvalues in increasing order, with multiplicity, as
$\Lambda_{\sigma,1}(\kappa,\tau)\le
\Lambda_{\sigma,2}(\kappa,\tau)\le\cdots$, and set
$\Delta_\sigma(\kappa,\tau)=
\Lambda_{\sigma,2}(\kappa,\tau)-\Lambda_{\sigma,1}(\kappa,\tau)$.
Existence of this discrete enumeration is the compact-resolvent assertion
of [G, (25.9)], applied separately at each parameter and cutoff.
In particular $\Lambda_{\sigma,1}=E_\sigma$.

**Theorem 35.2 (complete-domain fixed-index collapse).**
For every fixed positive integer $N$, every fixed original $s\in\mathbb R$,
$b>0$ and $g>0$, and through either sign of $\kappa\to0$,

$$
\begin{aligned}
\Lambda_{{\rm raw},N}(\kappa,\tau_s)&\longrightarrow e(gc_s),\\
\Lambda_{{\rm unit},N}(\kappa,\tau_b)&\longrightarrow
 e\!\left(gc_0G_{\beta b}(0)\right).
\end{aligned}
\tag{35.2}
$$

Proof. Put $M=c_s$ or $M=c_0G_{\beta b}(0)$ as appropriate, and $c=gM$.
Equation (32.9) gives numbers $\eta_\kappa\to0$ such that
$W_\sigma\le M\phi+\eta_\kappa$ everywhere. The complete-domain
inequality (33.3) therefore gives

$$
\mathfrak q_{\sigma,\kappa}[f]
 \ge \bigl(e(c)-g\eta_\kappa\bigr)\|f\|_2^2
 \qquad(f\in\mathcal F_\kappa).
\tag{35.3}
$$

Its Fourier justification keeps the entire square
$(nA_\kappa+mB_\kappa+\kappa j b_\kappa)^2$ in every summand.
Thus this bound includes arbitrary compensating hidden frequencies
and gives the required lower bound for every ordered eigenvalue.

For the upper bound choose $N$ real normalized functions
$F_1,\ldots,F_N\in C_c^\infty((-1,1))$ with pairwise disjoint supports.
Use the actual $D\in(-\pi,\pi)$ chart and the same length as in (33.4):

$$
\ell_\kappa=
\begin{cases}a\tau_s^{1/4},&\mathrm{raw},\\
\sqrt a,&\mathrm{unit},\end{cases}
\qquad
f_{i,\kappa}(k,\theta,v,D)
 =\frac{u_c(k)}{2\pi\sqrt{\ell_\kappa}}
                  F_i(D/\ell_\kappa).
\tag{35.4}
$$

These are orthonormal for the original raw measure: the visible volume
is $(2\pi)^2$, the hidden Jacobian is $\ell_\kappa$, and
$\|u_c\|_{L^2(dk)}=\|F_i\|_{L^2(dx)}=1$.
Scalar Dirichlet approximation of $u_c$ puts every $f_{i,\kappa}$ in
the original completed domain. Their supports avoid the circle seam.
Both the kinetic and multiplier cross forms between distinct $i$ vanish
by disjoint support. For each $i$ the exact kinetic energy is

$$
T_\kappa[f_{i,\kappa}]
 =\varepsilon^2\|u_c'\|_2^2
  +\frac{a^2}{\ell_\kappa^2}\|F_i'\|_2^2
                 \int_I b_\kappa^2u_c^2\,dk.
\tag{35.5}
$$

No cross term has been dropped from $Q_\kappa$: these trial functions
are constant in both visible angles, so its action on them is exactly
$\kappa b_\kappa\partial_D$. The lower bound (35.3), in contrast,
has no such restriction.

The second term of (35.5) tends to zero. On the union of the supports,
$\rho(D)/r_s\le\ell_\kappa/r_s=\tau_s^{-1/4}\to0$ in the raw
regime; in the unit regime $\rho(D)\le\ell_\kappa\to0$.
The uniform field limits (32.9) consequently give, for all $i\le N$,

$$
\int W_\sigma|f_{i,\kappa}|^2\,d\mu
 \longrightarrow M\int_I\phi u_c^2\,dk,
\qquad
\mathfrak q_{\sigma,\kappa}[f_{i,\kappa}]\longrightarrow e(c).
\tag{35.6}
$$

Since $N$ is fixed and the cross forms vanish, the supremum of the
Rayleigh quotient on their $N$-dimensional span tends to $e(c)$.
The form-domain min-max principle, [Teschl, Theorem 4.10,
printed pp.118--119](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
now gives the upper bound for the $N$th full eigenvalue. Its hypotheses
are selfadjointness, semiboundedness and the discrete ordered spectrum,
all supplied by (35.1); it requires neither invariant trial subspaces
nor a common operator domain as $\kappa$ varies. Together with (35.3)
this proves (35.2). All estimates use $a=|\kappa|$ or the uniform
two-sided coefficient bounds. $\square$

**Corollary 35.3 (fixed-parameter isolation and vanishing limiting gaps).**
At each admissible nonzero parameter and positive cutoff the original
attractive ground eigenvalue is simple, and $\Delta_\sigma>0$.
Nevertheless, for both critical families,

$$
\Delta_{\rm raw}(\kappa,\tau_s)\longrightarrow0,
\qquad
\Delta_{\rm unit}(\kappa,\tau_b)\longrightarrow0.
\tag{35.7}
$$

More generally the difference between the $(N+1)$st and $N$th full
eigenvalues tends to zero for every fixed $N$. Thus no fixed finite
initial cluster has a positive gap to its complement uniform in this
limit.

Proof. The original killed free heat kernel is strictly positive on the
connected cylinder, as supplied by [G, Proposition 2.1 and Theorem 20.2].
For each fixed parameter $W_\sigma$ is bounded and nonnegative.
The bounded-potential Trotter formula [Teschl, Theorem 5.11] gives

$$
e^{-t\mathscr H_{\sigma,\kappa,\tau}}h
 \ge e^{-tL_\kappa}h>0\quad(t>0,\quad 0\ne h\ge0).
\tag{35.8}
$$

Indeed every multiplication factor $e^{tgW_\sigma/n}$ is at least
one, and every free factor preserves positivity. The strong product
limit preserves this inequality. This heat operator is real and
selfadjoint, and its norm $e^{-t\Lambda_{\sigma,1}}$ is an eigenvalue
by compact resolvent. The positive-eigenvector argument of [Teschl,
Theorem 10.11, printed p.236] therefore makes it simple. That argument
uses only the order and inner product of $L^2$, so applies here with
the raw cylinder measure as it does on $L^2(\mathbb R^n)$.
Discreteness then gives $\Delta_\sigma>0$. Subtract the limits in
(35.2), first at $N=1,2$ and then at consecutive fixed indices.
These are statements about eigenvalue differences, not an assertion
about the spectral type of an unspecified limiting operator. $\square$

## 36. The complete three-coordinate comparison spectra

**Definition 36.1 (all visible modes of the actual zero leaf).**
On exactly $L^2(B,\nu_B)$ of [G, Definition 23.2] define
$\mathcal K_c=\overline L_0-cM_\phi$ for $c\ge0$, with form domain
$\overline{\mathcal F}_0$ and operator domain $D(\overline L_0)$.
For $(n,m)\in\mathbb Z^2$, let $\nu_r(n,m;c)$, $r\ge1$, be the
increasing Dirichlet eigenvalues of

$$
\begin{aligned}
K_{n,m}(c)
 &=-\varepsilon^2\partial_k^2
    +\left(\frac{nH-(n+m)k}{2H}\right)^2-c\phi(k),\\
Q(K_{n,m}(c))&=H_0^1(I),\qquad
D(K_{n,m}(c))=H^2(I)\cap H_0^1(I).
\end{aligned}
\tag{36.1}
$$

The numerator follows literally from (25.4):
$A_0=(H-k)/(2H)$ and $B_0=-k/(2H)$.
Let $e_r(c)=\nu_r(0,0;c)$, so $e_1(c)=e(c)$ and $e_r(0)=r^2\lambda$.
Denote by $\zeta_N(c)$ the increasing enumeration, with multiplicity,
of the multiset

$$
\Sigma(c)=\mathop{\bigsqcup}_{(n,m)\in\mathbb Z^2}
                     \{\nu_r(n,m;c):r\ge1\}.
\tag{36.2}
$$

This uses both visible circles. It is not the smaller two-coordinate
bottom-output quotient occurring in the observation-quotient volume.

**Theorem 36.2 (exact complete spectrum and complete base gap).**
The spectrum of $\mathcal K_c$ is exactly (36.2), with multiplicities
added whenever distinct triples $(r,n,m)$ have the same value.
Its bottom is the simple eigenvalue $\zeta_1(c)=e(c)$ and its actual
lowest spectral gap is

$$
\begin{aligned}
\Gamma(c)&=\zeta_2(c)-e(c)\\
 &=\min\left\{e_2(c)-e(c),
       \min_{(n,m)\ne(0,0)}[\nu_1(n,m;c)-e(c)]\right\},\\
0<\Gamma(c)&\le\min\{e_2(c)-e(c),1/4\}.
\end{aligned}
\tag{36.3}
$$

Proof. In the raw orthonormal expansion
$h=(2\pi)^{-1}\sum_{n,m}h_{nm}(k)e^{i(n\theta+mv)}$, the complete
base form domain is precisely

$$
\left\{h\in L^2(\nu_B):
 h_{nm}\in H_0^1(I),\quad
 \sum_{n,m}\left(\varepsilon^2\|h_{nm}'\|_2^2+
              \|(nA_0+mB_0)h_{nm}\|_2^2\right)<\infty\right\}.
\tag{36.4}
$$

This is the $j=0$ completed-domain argument of [G, (26.13)], now
on the actual base at zero; finite Fourier truncation and scalar
Dirichlet approximation give both inclusions. Bounded multiplication
by $c\phi$ leaves it unchanged. Thus $\mathcal K_c$ is the orthogonal
sum of exactly the scalar operators (36.1), including their complete
domains. Their normalized eigenfunctions multiplied by
$e^{i(n\theta+mv)}/(2\pi)$ constitute a complete orthonormal basis.
The scalar regular separated Dirichlet problem has simple discrete
eigenvalues by the Wronskian argument; see also [Teschl, §9.2,
Theorems 9.6 and 9.10, printed pp.187--192]. This scalar simplicity
does not remove coincidences between different angular modes, including
the equal spectra at $(n,m)$ and $(-n,-m)$.

The bound [G, (26.6)] at $\kappa=0$, $\eta=(n,m,0)$, implies

$$
\nu_1(n,m;c)\ge
 \lambda+C\Psi(\sqrt{n^2+m^2})-c\|\phi\|_\infty
 \longrightarrow+\infty\quad\text{as }|(n,m)|\to\infty.
\tag{36.5}
$$

Here and below $C>0$ is a suitable fixed lower-bound constant and
$\Psi$ is exactly [G, (26.6)]. Also
$\nu_r(n,m;c)\ge r^2\lambda-c\|\phi\|_\infty$ by scalar min-max.
Consequently only finitely many triples contribute below any fixed
energy; the multiset enumeration is well defined and has no finite
accumulation point.

Every scalar summand is $H_c$ plus a nonnegative square. Equality of
its bottom with $e(c)$ would force its normalized minimizer to be
$u_c$ up to phase and $(nA_0+mB_0)u_c=0$ almost everywhere.
The positivity of $u_c$ in $I$ would make the affine numerator in
(36.1) identically zero, forcing $n=m=0$.
Thus all nonzero angular bottoms are strictly larger than $e(c)$.
Equation (36.5) makes their infimum an attained positive separation.
The zero angular block contributes its positive scalar first gap.
This proves the equality and positivity in (36.3). Finally the actual
modes $(n,m)=(1,-1),(-1,1)$ have constant square $1/4$ and hence
eigenvalues $e_r(c)+1/4$. This gives the upper bound $1/4$.
In particular the scalar height gap alone is not the complete base
gap. $\square$

**Theorem 36.3 (actual leaf and complete restriction at the moving times).**
Let $\Lambda^0_{\sigma,N}(\tau)$ denote the ordered eigenvalues on
the actual native zero leaf with unit pole, raw measure and coupling $g$.
Let $\Lambda^{\rm sec}_{\sigma,N}(\kappa,\tau)$ denote the ordered
eigenvalues of the closed form restricted to the entire
$D$-independent subspace. At every admissible cutoff their exact
operator identifications on $L^2(B,\nu_B)$ are

$$
\begin{aligned}
\mathscr H^0_{\sigma,\tau}
 &=\overline L_0-gM_{W^0_{\sigma,\tau}},\\
J^*\mathscr H^{\rm sec}_{\sigma,\kappa,\tau}J
 &=\overline L_\kappa-\frac{g}{2\pi}
                         M_{\overline W_{\sigma,\kappa,\tau}},\\
W^0_{\rm raw,\tau}&=V_{0,\tau},\quad
W^0_{\rm unit,\tau}=V_{0,\tau}/S(\tau),\\
\overline W_{{\rm raw},\kappa,\tau}&=\overline V_{\kappa,\tau},\quad
\overline W_{{\rm unit},\kappa,\tau}
                         =\overline V_{\kappa,\tau}/S(\tau),\qquad
Jh=(2\pi)^{-1/2}h.
\end{aligned}
\tag{36.6}
$$

Their form domains are respectively $\overline{\mathcal F}_0$ and
$\overline{\mathcal F}_\kappa$ under this isometry; their operator
domains are those of the corresponding free base operators.
The sector operator here represents the restricted form, without an
assertion that the full attractive operator preserves that subspace.
For every fixed $N\ge1$, with all original parameters fixed as before,

$$
\begin{array}{c|c|c|c}
\text{family}&\lim\Lambda_{\sigma,N}
 &\lim\Lambda^0_{\sigma,N}&\lim\Lambda^{\rm sec}_{\sigma,N}\\ \hline
\mathrm{raw},\ \tau_s&e(gc_s)&\zeta_N(0)&\zeta_N(0)\\
\mathrm{unit},\ \tau_b&e(gc_0G_{\beta b}(0))
 &\zeta_N(gc_0)&\zeta_N(gc_0/(2\pi))
\end{array}
\tag{36.7}
$$

All limits involving nonzero $\kappa$ hold through both signs and count
multiplicity. In particular the actual lowest gaps have limits

$$
\begin{array}{c|c|c|c}
\text{family}&\text{full}&\text{actual zero leaf}&\text{complete sector}\\ \hline
\mathrm{raw},\ \tau_s&0&\Gamma(0)&\Gamma(0)\\
\mathrm{unit},\ \tau_b&0&\Gamma(gc_0)&\Gamma(gc_0/(2\pi))
\end{array}
\tag{36.8}
$$

Each comparison gap displayed is strictly positive for the stated fixed
data. The values $\zeta_N$ and $\Gamma$ are the exact complete spectral
quantities (36.1)--(36.3), rather than scalar-height replacements.

Proof. Equation (36.6) is exactly [G, (23.4)--(23.5)] and its
surviving-charge version. Both absorbing height faces and the same
survival function persist. The bounded fields give the stated operator
domains. Theorem 34.1 already proves the uniform multiplier limits

$$
\begin{array}{c|cc}
 &\mathrm{raw},\ \tau_s&\mathrm{unit},\ \tau_b\\ \hline
W^0_{\sigma,\tau}&0&c_0\phi\\
\overline W_{\sigma,\kappa,\tau}&0&c_0\phi.
\end{array}
\tag{36.9}
$$

For the actual zero leaf, bounded-multiplier min-max comparison with
$\mathcal K_0$ or $\mathcal K_{gc_0}$ proves every fixed-index limit
directly. To handle the changing complete sector domain, consider the
reference base operator
$\overline{\mathcal K}_{\kappa,c}=\overline L_\kappa-cM_\phi$.
Its scalar blocks have potentials $(nA_\kappa+mB_\kappa)^2-c\phi$.
For each fixed $(n,m)$ these potentials converge uniformly on $[l,u]$
to (36.1), so every fixed scalar eigenvalue converges by min-max.

There is no loss of angular modes in passing from this statement to the
ordered complete spectrum. The uniform version of [G, (26.6)], now
with $\eta=(n,m,0)$, bounds every block bottom from below by the right side
of (36.5), with $C$ independent of small $\kappa$, including zero.
Its $r$th eigenvalue is at least
$r^2\lambda-c\|\phi\|_\infty$ as well. The first $N$ eigenfunctions
of $H_c$ in the zero angular block provide a uniform $N$th
eigenvalue upper bound $e_N(c)\le N^2\lambda$.
Choose an energy strictly above this bound. Only a fixed finite set
of angular modes and height indices can lie below it, by the two
lower bounds. On that finite set all eigenvalues converge, and sorting
finite multisets preserves convergence, including collisions and
multiplicity. Hence the $N$th eigenvalue of
$\overline{\mathcal K}_{\kappa,c}$ tends to $\zeta_N(c)$.

Apply this with $c=0$ or $gc_0/(2\pi)$.
The difference between the actual sector multiplier and its reference
tends to zero in supremum norm by (36.9). On the same complete
$\kappa$-domain, min-max bounds the difference of every ordered
eigenvalue by that multiplier norm, including the factor $g/(2\pi)$.
This proves the sector limits without identifying varying domains or
asserting general operator convergence. The full column is Theorem 35.2.
Subtract the first two limits and use (36.3) to obtain (36.8).
The actual base and sector operators also have simple ground states at
each fixed admissible cutoff: their connected base free heat kernels
are strictly positive, and the bounded-potential argument (35.8)
applies on $B$. Thus their first ordered differences are their actual
lowest spectral gaps. $\square$

## 37. The spectral boundary of the ground-coincidence parameter

**Corollary 37.1 (ground coincidence never extends to the full low spectrum).**
At the unique $b_*$ in (34.2), the unit critical families have equal
limiting full and actual-zero-leaf ground energies and equal limiting
ground probabilities after the measure embedding $D=0$. Nevertheless,
for every fixed $N\ge2$,

$$
\begin{aligned}
\lim_{\kappa\to0}\Lambda_{{\rm unit},N}(\kappa,\tau_{b_*})
 &=e(gc_0),\\
\lim_{\kappa\to0}\Lambda^0_{{\rm unit},N}(\tau_{b_*})
 &=\zeta_N(gc_0)\ge e(gc_0)+\Gamma(gc_0)>e(gc_0).
\end{aligned}
\tag{37.1}
$$

The limiting full lowest gap is zero and the actual-zero-leaf lowest
gap tends to $\Gamma(gc_0)>0$ at this same parameter. For $b\ne b_*$
their limiting ground energies already differ. For every finite $b>0$
and every fixed $N$, the full unit $N$th eigenvalue has a limit strictly
below the limiting sector ground energy. In the raw family, every fixed
full eigenvalue has a limit strictly below the limiting ground energies
of both comparisons.

Proof. At $b_*$ the full value in (36.7) is $e(gc_0)$ for every $N$,
while the simple base ground and (36.3) give (37.1).
The other full-versus-zero ground comparisons and ground-probability
coincidence are exactly Theorem 34.1. For the sector comparison use
$G_{\beta b}(0)>1/(2\pi)$ at every finite $b$ and strict decrease of
$e$ in (34.6). In the raw family use $c_sg>0$ and
$\zeta_1(0)=e(0)=\lambda$. These strict limiting inequalities also
hold between the corresponding actual eigenvalues for all sufficiently
small $|\kappa|$, separately for each fixed $N$. $\square$

**Proposition 37.2 (scope of the spectral obstruction).**
Within the original two critical families, bounded attained attractive
ground energy and concentration of ground probabilities do not suffice
to preserve the isolated simple low-energy spectrum of the actual native
three-coordinate leaf. This remains true at the unit ground-coincidence
parameter. The comparison with the complete sector is a different
comparison, with the factor $1/(2\pi)$ and the entire spectrum (36.2).

Proof. Theorems 33.1--33.2 supply bounded attained minima and the
concentrated ground laws; (35.7) and (36.8) supply respectively the
vanishing full gap and strictly positive comparison gaps. Equation
(37.1) gives the obstruction even when the ground energy and probability
match. Fixed-parameter isolation from Corollary 35.3 is consistent with
this failure of uniform isolation. A constant fixed-index limit is not
itself an identification of a limiting operator or its spectral type.
The construction fixes $N$ before taking $\kappa\to0$; the derivative
norms and supports chosen in (35.4) may depend on $N$. It supplies no
assertion for a prescribed growing $N(\kappa)$, no spacing rate,
transverse fluctuation profile, Weyl law or resolvent convergence.

The general methods are classical variational and bounded-perturbation
methods; the additional native conclusions are (35.2), the complete
comparison (36.7)--(36.8), and the excited-level separation (37.1).
The sharp heat, source, field and ground limits are reused from
§§31--34 and [G, §§23,25--29], rather than rederived. The singular
point-field strict-ground result in
[Fixed-pole strict ground-energy gap, Theorem 7.2 and Boundary 8.2](FIB_NATIVE_FIXED_POLE_STRICT_GROUND_ENERGY_GAP.md)
compares two actual minima in its strict stable regime; it is neither an
excited spectral gap nor a critical-cutoff spectral limit. The restricted
singular-field limit in
[Observation quotient, Theorem 11.1](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md)
also retains its different field and small-coupling hypotheses.
Neither replaces the completed attractive forms (35.1).

For the classical semiclassical comparison, B. Simon,
*Semiclassical Analysis of Low Lying Eigenvalues. I. Non-degenerate
Minima: Asymptotic Expansions*, Ann. Inst. H. Poincaré A 38 (1983),
295--308, [§1, hypotheses (A1)--(A4) and Theorem 1.1](https://www.numdam.org/item/AIHPA_1983__38_3_295_0/),
treats $-\Delta+\Lambda^2h+\Lambda g_1$ with smooth fixed scalar
potentials, finitely many zeros of $h$, positive definite Hessians there,
and the stated lower and exterior bounds. Those hypotheses do not
identify the present full form with that scalar family: here
$\varepsilon$ stays fixed, only the hidden direction loses kinetic
control, the raw critical field itself narrows, and the original visible
cross terms remain. No harmonic-oscillator expansion or sharp gap rate
is imported from that theorem. The finite-dimensional proof above
requires only (32.9), the complete-domain lower bound and classical
min-max, not a new general semiclassical theorem. These native deductions
are `repo-derived`; the cited classical methods are
`literature-attested`, without a worldwide novelty assertion.

The source and domain obstructions of Theorem 34.2 persist independently
of the spectra. The zero-leaf embedding is an embedding of measures,
whereas $J$ is a raw-measure Hilbert-space isometry for the complete
sector. Conditional source charge is still different from field mass;
normalization still changes neither height death nor the original free
clock. The free quotient criteria in
[Free diffusion quotient rigidity, Theorem 3.1 and Definition 6.2](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md)
do not make an attractive fixed-pole multiplier invariant or identify
different source laws. None of these statements adds a reset, projection
actuator, independent driver, preparation of ground amplitudes,
acquisition procedure or mean selector. The native finite-history and
principal-symbol boundaries in
[Probability, phase transport and holonomy, Theorems 8.2, 10.3 and 10.5](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)
remain in force. State dimension is not a conclusion about physical
spatial axes. All parameters other than $\kappa$ are fixed; no
$\varepsilon\to0$ limit or other cutoff family is asserted. $\square$

## 追加锚（本行以下为增补区）
