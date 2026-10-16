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

## 38. Independent scalar data and the two fluctuation scales

**Definition 38.1 (quantitative data in the original model).**
Keep all of Definition 31.1 and (35.1), including the two signs of
$\kappa$, every fixed $s\in\mathbb R$, $b>0$, $g>0$, and the complete
original domains. The results in §§38--43 concern only these two
critical families. For $c>0$ define independent scalar data

$$
\mathfrak b(c)=\int_I b_0(k)^2u_c(k)^2\,dk>0,
\qquad
\mathfrak m(c)=\int_I\phi(k)u_c(k)^2\,dk>0.
\tag{38.1}
$$

Here $u_c$, $b_0$, $\phi$ and $\beta$ are exactly (31.1)--(31.2).
In particular $\mathfrak b(c)$ uses the attractive scalar ground,
whereas $\beta$ uses the free scalar ground $\phi$. Set

$$
\begin{array}{c|cc}
 &\mathrm{raw},\ \tau_s&\mathrm{unit},\ \tau_b\\ \hline
 c_\sigma&gc_s&gc_0G_{\beta b}(0)\\
 d_{\sigma,\kappa}&r_s&1\\
 h_{\sigma,\kappa}=a/d_{\sigma,\kappa}&\tau_s^{-1/2}&a\\
 \ell_{\sigma,\kappa}=d_{\sigma,\kappa}\sqrt{h_{\sigma,\kappa}}
      &a\tau_s^{1/4}&\sqrt a\\
 \mathcal B_\sigma&\mathfrak b(gc_s)
       &\mathfrak b(gc_0G_{\beta b}(0))\\
 \mathcal C_\sigma&\displaystyle\frac{gc_s}{4\beta}\mathfrak m(gc_s)
       &\displaystyle-\frac{gc_0}{2}G_{\beta b}''(0)
                         \mathfrak m(gc_0G_{\beta b}(0)) .
\end{array}
\tag{38.2}
$$

Every entry in the last two rows is finite and strictly positive:

$$
-G_t''(0)=\frac1\pi\sum_{j\ge1}j^2e^{-tj^2}>0\qquad(t>0).
\tag{38.3}
$$

The resulting frequency, Gaussian parameter and original-coordinate
harmonic length are

$$
\omega_\sigma=\sqrt{\mathcal B_\sigma\mathcal C_\sigma},
\qquad
\gamma_\sigma=\sqrt{\mathcal C_\sigma/\mathcal B_\sigma},
\qquad
w_{\sigma,\kappa}
   =\ell_{\sigma,\kappa}
       (\mathcal B_\sigma/\mathcal C_\sigma)^{1/4}.
\tag{38.4}
$$

These scales are specified by the original parameters and the scalar
Dirichlet problem (31.2). No full unknown gap, ground width or selected
Fourier eigenvalue defines them. In the raw family,
$h_{\rm raw,\kappa}\sim\sqrt{\lambda/L_a}$ and
$w_{\rm raw,\kappa}/r_s
=(\mathcal B_{\rm raw}/\mathcal C_{\rm raw})^{1/4}\tau_s^{-1/4}\to0$.
The field width $r_s$ is therefore distinct from the ground fluctuation
length. No parameter limit in $s,b,g$ or $\varepsilon$ is implicit.

**Definition 38.2 (exact visible average and a scalar common center).**
In each family let $W_\kappa$ denote its original multiplier in (35.1),
and define its average over the two visible phases by

$$
U_\kappa(k,D)=\frac1{(2\pi)^2}
       \int_{\mathbb T^2}W_\kappa(k,\theta,v,D)\,d\theta\,dv.
\tag{38.5}
$$

This is an auxiliary analytic average of the actual field; it changes
neither the specified physical source nor the full operator being
studied. On $L^2(I,dk)$ put

$$
H_\kappa^{\rm ht}=-\varepsilon^2\partial_k^2-gU_\kappa(k,0),
\qquad Q(H_\kappa^{\rm ht})=H_0^1(I),
\tag{38.6}
$$

and let $\xi_\kappa$ and $v_\kappa>0$ be its first eigenvalue and
normalized ground. This one-dimensional center is computable without
any full attractive eigenvalue. It will cancel from centered spacings;
no estimate of $\xi_\kappa-e(c_\sigma)$ at order $h_{\sigma,\kappa}$
is assumed.

## 39. Native derivative limits and error below the spacing scale

**Lemma 39.1 (visible error, hidden symmetry and differentiated limits).**
For the data of Definition 38.1, write $h=h_{\sigma,\kappa}$ and
$d=d_{\sigma,\kappa}$. Then

$$
\|W_\kappa-U_\kappa\|_\infty=o(h),
\qquad
U_\kappa(k,0)-U_\kappa(k,D)\ge0.
\tag{39.1}
$$

The second difference is even in $D$. For every integer $0\le p\le4$,
with $D$ represented in $[-\pi,\pi]$,

$$
\begin{aligned}
\sup_{k,\ |x|\le\pi/r_s}
\left|\partial_x^p U_{\rm raw,\kappa}(k,r_sx)
       -c_s\phi(k)\partial_x^p e^{-x^2/(4\beta)}\right|&\longrightarrow0,\\
\sup_{k,\ D\in\mathbb T}
\left|\partial_D^p U_{\rm unit,\kappa}(k,D)
       -c_0\phi(k)G_{\beta b}^{(p)}(D)\right|&\longrightarrow0.
\end{aligned}
\tag{39.2}
$$

Consequently, on each bounded $y$ interval, uniformly in $k$,

$$
\frac g h\bigl[U_\kappa(k,0)
             -U_\kappa(k,d\sqrt h\,y)\bigr]
       \longrightarrow C_\sigma(k)y^2,
\quad
C_\sigma(k)=
\begin{cases}
 gc_s\phi(k)/(4\beta),&\mathrm{raw},\\
 -gc_0G_{\beta b}''(0)\phi(k)/2,&\mathrm{unit}.
\end{cases}
\tag{39.3}
$$

In addition, for every closed nonempty interval $J\Subset I$, there is
$\eta_J>0$ such that for all sufficiently small $a$,

$$
U_\kappa(k,0)-U_\kappa(k,dx)
 \ge\eta_J\min\{x^2,1\}
\quad(k\in J,\ |x|\le\pi/d).
\tag{39.4}
$$

All these assertions hold through both signs, without a restriction on
the fixed positive coupling.

Proof. Throughout this proof $K_{\kappa,q}$ abbreviates the exact
scalar kernel $K_{\kappa,(0,0,q)}$ of (32.4)--(32.5). The complete
Fourier identity [G, (26.13)] gives

$$
U_\kappa(k,D)
 =\frac1{(2\pi)^3Z_\kappa}
     \sum_{j\in\mathbb Z}e^{ijD}
           \int_\tau^\infty K_{\kappa,\kappa j}(t;k_0,k)\,dt,
\quad
Z_\kappa=
\begin{cases}1,&\mathrm{raw},\\S(\tau_b),&\mathrm{unit}.
\end{cases}
\tag{39.5}
$$

The time is $\tau_s$ or $\tau_b$, respectively. The scalar potential
is $q^2b_\kappa^2$. Since $0<m\le b_\kappa\le M$ on the entire
closed height interval for small parameters, positivity and the
bounded-potential Trotter formula imply, for all large $t$,

$$
0<K_{\kappa,q}(t;k_0,k)
 \le e^{-m^2q^2t}h_I(t;k_0,k)
 \le C e^{-\lambda t}e^{-m^2q^2t}.
\tag{39.6}
$$

The last inequality is uniform in height by the killed sine series.
It is used only for the visible-zero kernels; no estimate of a general
compensated frequency by $q^2$ is made. Every coefficient in (39.5)
is positive and invariant under $j\mapsto-j$. Subtracting its cosine
series at $D$ from its value at zero proves the second assertion in
(39.1), including evenness. Gaussian summability also justifies each
fixed finite number of derivatives and the time integrals.

For completeness, the differentiated local limit follows directly
from the existing scalar perturbation (32.4), rather than from
formal differentiation of an $o(1)$ field error. Put $r=a\sqrt t$.
For each fixed $p\le4$, whenever $t\to\infty$ and $r\to0$,

$$
r\sum_j|rj|^p\sup_k
 \left|e^{\lambda t}K_{\kappa,\kappa j}(t;k_0,k)
            -\phi(k_0)\phi(k)e^{-\beta r^2j^2}\right|
 \longrightarrow0.
\tag{39.7}
$$

Indeed, on $|rj|\le R$ one has $q^2=(rj)^2/t$. Equations
(32.4)--(32.5) make the difference tend uniformly to zero there;
the number of lattice points times $r$ is bounded. The weighted
Gaussian majorant (39.6) makes both tails bounded by a constant times
$\int_{|z|>R-1}(1+|z|^p)e^{-c z^2}\,dz$, for small $r$.
Take the parameter limit and then $R\to\infty$. The nonsummed
remainder in (32.5) has only been used on the bounded lattice window,
so no infinite multiple of that remainder has occurred.

Multiplying each Fourier summand by $(irj)^p$ now proves the
corresponding derivative version of (32.1), with the differentiated
periodized Gaussian. For $t=\tau_s+v$ in a fixed bounded $v$ interval,
$r/r_s\to1$ and (32.14) supplies its amplitude. To integrate beyond
such an interval, (39.6) and the Gaussian lattice estimate give

$$
\sum_j(r_s|j|)^p K_{\kappa,\kappa j}(t;k_0,k)
 \le C_p e^{-\lambda t}(1+r_s^{-1}),\qquad t\ge\tau_s.
\tag{39.8}
$$

For $p=0$ this includes the zero summand; for $p>0$ it is the same
Gaussian moment estimate, using $r_s/(a\sqrt t)\le1$.
Since $e^{-\lambda\tau_s}/r_s$ is bounded, the omitted integral
from $\tau_s+R$ onward is at most $C_pe^{-\lambda R}$ in every
rescaled derivative norm. Integrating first on a bounded window,
then sending $R\to\infty$, gives the first line of (39.2), with
exactly the coefficient $c_s$ of (31.1). On the expanding chart,
all nonnearest Gaussian translates and their first four derivatives
tend uniformly to zero. The nearest term is the displayed Gaussian.

For the unit family, each fixed $j$ in (32.4)--(32.5), at
$t=\tau_b+v$, gives

$$
\frac{K_{\kappa,\kappa j}(\tau_b+v;k_0,k)}{S(\tau_b)}
 \longrightarrow
 \frac{\phi(k)}{J_\phi}e^{-\lambda v}e^{-\beta b j^2}.
\tag{39.9}
$$

Equation (39.6), (32.13), and $a^2\tau_b=b$ dominate its $p$th
Fourier derivative by $C_b|j|^p e^{-\lambda v}e^{-m^2b j^2}$
(with the zero term interpreted separately when $p=0$).
This majorant is summable in $j$ and integrable in $v$. Thus dominated
summation and integration prove the second line of (39.2).
The raw factor $(2\pi)^{-3}$ in (39.5), the Fourier normalization
of $G$, and $\int_0^\infty e^{-\lambda v}dv=1/\lambda$ give
$c_0$, without a change of measure.

The nonzero visible modes obey exactly (32.3). Integrating that
bound, and dividing by $Z_\kappa$ where appropriate, yields

$$
\|W_\kappa-U_\kappa\|_\infty
 \le
\begin{cases}
 C e^{-d_*\tau_s},&\mathrm{raw},\\
 C_b e^{-d_*\tau_b},&\mathrm{unit},
\end{cases}
\tag{39.10}
$$

for a fixed $d_*>0$. In the raw case this uses
$e^{-\lambda\tau_s}(1+r_s^{-1})=O(1)$; in the unit case it uses
$S(\tau_b)\asymp e^{-\lambda\tau_b}$.
These errors are respectively $o(\tau_s^{-1/2})$ and $o(a)$,
proving the first assertion of (39.1).

Write $\widetilde U_\kappa(k,x)=U_\kappa(k,dx)$. Exact evenness
gives $\partial_x\widetilde U_\kappa(k,0)=0$, so the centered
Taylor identity is

$$
\frac g h[\widetilde U_\kappa(k,0)
              -\widetilde U_\kappa(k,\sqrt h\,y)]
 =-g y^2\int_0^1(1-t)
       \partial_x^2\widetilde U_\kappa(k,t\sqrt h\,y)\,dt.
\tag{39.11}
$$

Equation (39.2) in this identity proves (39.3). In particular no
undifferentiated global field error has been divided by $h$.
On $J$, the limiting negative second derivative at zero is
bounded away from zero. The same formula gives (39.4) on a fixed
small $|x|\le\delta$. Outside that interval, the raw limiting deficit
is at least
$c_s\min_J\phi\,(1-e^{-\delta^2/(4\beta)})$ on its entire expanding
chart, by the uniform first line of (39.2). In the unit case, (33.2)
makes $G_{\beta b}(0)-G_{\beta b}(D)$ strictly positive off zero;
its minimum on $\delta\le|D|\le\pi$ is positive. The uniform limits
then give a positive lower bound outside $\delta$ in both cases.
Decreasing $\eta_J$ combines these bounds into (39.4). $\square$

## 40. Compactness at the centered native energy scale

**Definition 40.1 (the exact visible-zero block).**
Under the isometry $f(k,D)\mapsto f(k,D)/(2\pi)$ into the
visible-constant subspace of the original raw-measure space, the
operator with averaged multiplier $L_\kappa-gU_\kappa$ has block form

$$
\mathfrak a_\kappa[f]
 =\int_{I\times\mathbb T}
   \left(\varepsilon^2|\partial_k f|^2
       +a^2b_\kappa(k)^2|\partial_D f|^2
       -gU_\kappa(k,D)|f|^2\right)dk\,dD.
\tag{40.1}
$$

At each nonzero parameter this block domain is the periodic $H^1$
space with zero trace at both height faces. Indeed the exact completed
Fourier domain [G, (26.13)] restricted to $n=m=0$, and
$0<m\le b_\kappa\le M$, give precisely this characterization.
It asserts no isotropic domain for the full operator. Denote the
ordered block eigenvalues by $\nu_{\kappa,N}$. Compactness here also
follows from this fixed-parameter elliptic form on the compact
cylinder with Dirichlet height faces.

For the remainder of §40 abbreviate $h=h_{\sigma,\kappa}$,
$d=d_{\sigma,\kappa}$, $\ell=d\sqrt h$ and $c=c_\sigma$.
In the actual hidden chart set

$$
F(k,y)=\sqrt\ell\, f(k,\ell y),
\qquad -\pi/\ell<y<\pi/\ell.
\tag{40.2}
$$

This is a unitary change of coordinates with the raw Jacobian. Extend
$F$ by zero outside that interval only when viewing it as an $L^2$
function on $I\times\mathbb R$; its actual domain retains the periodic
condition at the two ends of the chart.

**Lemma 40.2 (positive decomposition, tightness and lower limit).**
One has $\xi_\kappa\to e(c)$ and $v_\kappa\to u_c$ in $H^2(I)$.
The height gap above $\xi_\kappa$ is bounded below by a fixed
$\gamma_*>0$ for small $a$. The rescaled centered form is exactly

$$
\begin{aligned}
\mathcal R_\kappa[F]
 &:={\mathfrak a_\kappa[f]-\xi_\kappa\|f\|_2^2\over h}\\
 &=\frac1h\int
       \langle F(\cdot,y),(H_\kappa^{\rm ht}-\xi_\kappa)
                                  F(\cdot,y)\rangle\,dy\\
 &\quad+\int b_\kappa(k)^2|\partial_yF|^2\,dk\,dy
       +\int V_\kappa(k,y)|F|^2\,dk\,dy,\\
V_\kappa(k,y)
 &=\frac g h[U_\kappa(k,0)-U_\kappa(k,\ell y)]\ge0.
\end{aligned}
\tag{40.3}
$$

The first integral is interpreted as a height quadratic form.
As $\kappa\to0$, every sequence with bounded norms and bounded
$\mathcal R_\kappa$ has an $L^2(I\times\mathbb R)$ strongly
convergent subsequence, after zero extension as in (40.2). Every limit
is $u_c(k)z(y)$, where $z\in H^1(\mathbb R)$ and
$yz\in L^2(\mathbb R)$. Along each such convergent subsequence,

$$
\liminf_{\kappa\to0}\mathcal R_\kappa[F_\kappa]
 \ge\mathcal R_\sigma[z]
 :=\mathcal B_\sigma\int_{\mathbb R}|z'|^2dy
       +\mathcal C_\sigma\int_{\mathbb R}y^2|z|^2dy.
\tag{40.4}
$$

Conversely, for every $z\in C_c^\infty(\mathbb R)$,
$F_\kappa(k,y)=v_\kappa(k)z(y)$ belongs to the rescaled block domain
for small $a$, has norm $\|z\|_2$, and its form converges to
$\mathcal R_\sigma[z]$.

Proof. By (39.2), $U_\kappa(k,0)\to(c/g)\phi(k)$ uniformly.
Bounded-multiplier min-max gives convergence of the first two height
eigenvalues to those of $H_c$. The latter has a simple positive ground
and a strictly positive first gap. The scalar Dirichlet equation,
normalization and bounded multipliers bound $v_\kappa$ in $H^2$.
Every convergent subsequence has the positive normalized ground $u_c$
as its only possible limit. The equation then gives convergence in
$H^2$ as well, and the first two eigenvalue limits give $\gamma_*$.
These are the same fixed-domain scalar arguments as in (32.4).

Subtract the height ground energy at $D=0$ from (40.1). All three
terms so obtained are nonnegative by (39.1) and the height spectral
theorem. Since $a^2/\ell^2=h$, the coordinate change (40.2) gives
exactly (40.3), initially on the core and then on its completion.
No cross term or field error enters this identity.

Let

$$
z_\kappa(y)=\int_I v_\kappa(k)F_\kappa(k,y)\,dk,
\qquad
R_\kappa(k,y)=F_\kappa(k,y)-v_\kappa(k)z_\kappa(y).
\tag{40.5}
$$

The height gap and the kinetic term in (40.3) imply

$$
\|R_\kappa\|_2^2\le C h/\gamma_*\longrightarrow0,
\qquad
\|\partial_yF_\kappa\|_2+\|z_\kappa'\|_2\le C.
\tag{40.6}
$$

The derivative estimates apply inside the chart with its periodic
ends; they are not assertions about derivatives of the zero extension
at its seam. The norms of $z_\kappa$ are bounded as well.

Here is a tightness argument that retains the absorbing height faces,
where $\phi$ vanishes. Fix any interval $J\Subset I$ of positive
length. Positivity and convergence of $v_\kappa$ imply
$\int_Jv_\kappa^2\,dk\ge\alpha_J>0$. Equation (39.4) gives, on $J$,

$$
V_\kappa(k,y)\ge g\eta_J\min\{y^2,h^{-1}\}.
\tag{40.7}
$$

For $R\ge1$ and $hR^2\le1$, boundedness of (40.3) therefore gives
$\int_{J\times\{|y|>R\}}|F_\kappa|^2\le C/R^2$.
The pointwise inequality $|A+B|^2\ge|A|^2/2-|B|^2$, applied to
(40.5), gives

$$
\frac{\alpha_J}{2}\int_{|y|>R}|z_\kappa|^2dy
 \le\int_{J\times\{|y|>R\}}|F_\kappa|^2+\|R_\kappa\|_2^2.
\tag{40.8}
$$

It follows that

$$
\int_{|y|>R}\int_I|F_\kappa|^2\,dk\,dy
 \le C/R^2+Ch\qquad(hR^2\le1).
\tag{40.9}
$$

Thus no mass can disappear either to the growing hidden chart or
into the height faces. In particular tightness did not require a
positive lower bound for $\phi$ on all of $I$.

On every fixed bounded $y$ interval the one-dimensional compact
embedding for $z_\kappa$, (40.6), and $v_\kappa\to u_c$ give a
subsequence with $F_\kappa\to u_cz$ strongly in $L^2$ there.
A diagonal selection and (40.9) give strong convergence globally.
They also preserve the full norm of each convergent sequence.
On bounded intervals the weak derivative limit is $u_cz'$, and
$b_\kappa\to b_0$ uniformly. Weak lower semicontinuity gives the
kinetic contribution $\mathfrak b(c)\int|z'|^2$ in (40.4).
By (39.3), $V_\kappa\to C_\sigma(k)y^2$ uniformly on each such
interval. Strong local $L^2$ convergence gives its potential
contribution
$\int_I C_\sigma u_c^2\,dk\int y^2|z|^2dy$.
The height term can be dropped because it is nonnegative.
Increasing the bounded intervals to $\mathbb R$ proves (40.4),
including $yz\in L^2$; its coefficient is exactly $\mathcal C_\sigma$
in (38.2).

For the converse sequence the height term vanishes identically.
Its compact hidden support avoids the seam for small $a$; scalar
height approximation places it in the exact completed domain.
Uniform coefficient convergence and (39.3) give convergence of
both remaining terms. Polarization gives the same convergence of
cross forms for every fixed finite collection of such trials.
$\square$

**Theorem 40.3 (the entire low block spectrum and its actual ground).**
For every fixed $N\ge1$,

$$
\nu_{\kappa,N}
 =\xi_\kappa+h_{\sigma,\kappa}(2N-1)\omega_\sigma
                     +o(h_{\sigma,\kappa}).
\tag{40.10}
$$

The eigenvalues count multiplicity. For any normalized block ground
$f_\kappa^{\rm bl}$, suitable constant phases make the rescaled
amplitudes in (40.2) converge strongly to

$$
u_{c_\sigma}(k)\psi_\sigma(y),
\qquad
\psi_\sigma(y)
  =\left(\frac{\gamma_\sigma}{\pi}\right)^{1/4}
                 e^{-\gamma_\sigma y^2/2}.
\tag{40.11}
$$

Proof. The limiting form in (40.4) is the one-dimensional oscillator
$-\mathcal B_\sigma\partial_y^2+\mathcal C_\sigma y^2$.
Rescaling $y=(\mathcal B_\sigma/\mathcal C_\sigma)^{1/4}z$
identifies it with
$\omega_\sigma(-\partial_z^2+z^2)$.
The classical Hermite basis therefore gives its simple ordered
spectrum $\mu_N=(2N-1)\omega_\sigma$ and the normalized ground
(40.11). This is precisely the one-dimensional calculation in
[Teschl, §8.3, (8.35)--(8.41), printed pp.178--179](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
Its form domain is $\{z\in H^1(\mathbb R):yz\in L^2\}$ and
$C_c^\infty$ is a form core, by cutoff and smoothing. Thus its first
$N$ eigenfunctions can be approximated by an $N$-dimensional space
of compactly supported smooth functions whose largest quotient is
arbitrarily close to $\mu_N$.

Apply the recovery part of Lemma 40.2 to a basis of that space.
Its exact preservation of norms and convergence of all cross forms,
followed by min-max, give

$$
\limsup\frac{\nu_{\kappa,N}-\xi_\kappa}{h}\le\mu_N.
\tag{40.12}
$$

For the reverse bound choose the first $N$ orthonormal eigenfunctions
of the exact block. Their rescaled centered energies are nonnegative
by (40.3), and bounded by (40.12). On any subsequence realizing a
lower limit of the $N$th centered eigenvalue, pass to a further
subsequence so that all first $N$ centered eigenvalues converge and
Lemma 40.2 applies simultaneously to their eigenfunctions.
Their strong limits are $u_cz_1,\ldots,u_cz_N$, with the $z_i$
orthonormal on $\mathbb R$. For any fixed coefficients $t_i$, the
lower-limit inequality applied to their linear combination gives

$$
\mathcal R_\sigma\left[\sum_{i=1}^Nt_i z_i\right]
 \le\lim\sum_{i=1}^N|t_i|^2
                    \frac{\nu_{\kappa,i}-\xi_\kappa}{h}
 \le\left(\lim\frac{\nu_{\kappa,N}-\xi_\kappa}{h}\right)
                       \sum_{i=1}^N|t_i|^2.
\tag{40.13}
$$

Min-max for the limiting oscillator implies that the last limit is
at least $\mu_N$. This proves (40.10). The argument controls every
possible sequence of low eigenfunctions; it does not assume an
adiabatic ansatz or discard high hidden Fourier frequencies.

For the block ground, every subsequential strong limit has norm one
and limiting form at most $\mu_1$. It must be the simple oscillator
ground times $u_c$, up to a constant phase. Choosing the nonnegative
block ground fixes that phase: the fixed-parameter block form is
elliptic with a bounded real potential on the connected cylinder.
Its free heat kernel is the integral of the original strictly positive
full heat kernel over the two visible output phases, so it is strictly
positive. The bounded-potential argument of (35.8) on this block
therefore gives a simple positive ground.
Every subsequence then has the same limit, which proves (40.11)
for the full family and for arbitrary normalized ground choices
after constant phases. $\square$

## 41. Sharp centered spacings of the complete ordered spectrum

**Theorem 41.1 (common centering for the full native form).**
For every fixed $N\ge1$, all the original fixed parameters in
Definition 38.1, and both signs of $\kappa\to0$,

$$
\Lambda_{\sigma,N}(\kappa,\tau)
 =\xi_\kappa+(2N-1)\omega_\sigma h_{\sigma,\kappa}
                          +o(h_{\sigma,\kappa}),
\qquad
\tau=\tau_s\ \hbox{or}\ \tau_b.
\tag{41.1}
$$

This is the full ordered spectrum with multiplicity of (35.1).
In particular, for every fixed $N\ge2$,

$$
\begin{aligned}
\Lambda_{{\rm raw},N}(\kappa,\tau_s)
       -\Lambda_{{\rm raw},1}(\kappa,\tau_s)
 &=\frac{2(N-1)\omega_{\rm raw}}{\sqrt{\tau_s}}
                       +o(\tau_s^{-1/2}),\\
\Lambda_{{\rm unit},N}(\kappa,\tau_b)
       -\Lambda_{{\rm unit},1}(\kappa,\tau_b)
 &=2(N-1)\omega_{\rm unit}\,a+o(a).
\end{aligned}
\tag{41.2}
$$

The actual lowest full gaps, rather than height or sector gaps, are

$$
\Delta_{\rm raw}(\kappa,\tau_s)
 \sim2\omega_{\rm raw}\tau_s^{-1/2},
\qquad
\Delta_{\rm unit}(\kappa,\tau_b)
 \sim2\omega_{\rm unit}|\kappa|.
\tag{41.3}
$$

Every fixed consecutive full spacing has the corresponding leading
coefficient $2\omega_\sigma$. Each fixed finite initial list is
therefore simple for all sufficiently small nonzero parameters.
The assertion is pointwise in the fixed original data, not uniform
as $g\downarrow0$ or $b\to\infty$.

Proof. Let
$\widehat{\mathscr H}_\kappa=L_\kappa-gM_{U_\kappa}$ on exactly
$\mathcal F_\kappa$. This bounded multiplier preserves the completed
form domain and compact resolvent. Lemma 39.1 and min-max give, for
every ordered index,

$$
|\Lambda_{\sigma,N}-\widehat\Lambda_{\kappa,N}|
 \le g\|W_\kappa-U_\kappa\|_\infty=o(h).
\tag{41.4}
$$

This is a comparison between full forms on the same exact domain.
No restriction of the original attractive operator is presumed
invariant.

The auxiliary averaged operator does preserve each visible Fourier
pair $(n,m)$. Its free square in hidden Fourier mode $j$ is still

$$
(nA_\kappa+mB_\kappa+\kappa j b_\kappa)^2.
\tag{41.5}
$$

By (39.2), $gU_\kappa(k,0)\to c_\sigma\phi(k)$ uniformly, and
by (39.1), $U_\kappa(k,D)\le U_\kappa(k,0)$.
The complete-domain separation (33.12) consequently gives, on the
sum of every nonzero visible pair,

$$
\widehat{\mathscr H}_\kappa
 \ge e(c_\sigma)+d_{c_\sigma}-o(1).
\tag{41.6}
$$

To spell out its use when the potential couples hidden frequencies,
first replace $gU_\kappa(k,D)$ by the upper bound
$c_\sigma\phi(k)+o(1)$. The resulting lower comparison is diagonal
in all three phase indices. Apply (33.12) to each of its scalar
summands with $q=\kappa j$, and sum the form inequalities on
[G, (26.13)]. This proves (41.6) for the entire nonzero visible
subspace, uniformly over all integers and every compensating hidden
frequency. The nonnegative square (41.5) has not been expanded into
separately bounded or discarded cross terms.

The zero visible block is exactly (40.1). Its first $N$ eigenvalues
are $\xi_\kappa+O(h)=e(c_\sigma)+o(1)$ by Theorem 40.3.
For each fixed $N$ they lie strictly below (41.6) for small $a$.
The direct-sum characterization of the completed Fourier domain
then implies

$$
\widehat\Lambda_{\kappa,i}=\nu_{\kappa,i}
 \qquad(1\le i\le N)
\tag{41.7}
$$

with their full multiplicities. Equations (40.10), (41.4) and
(41.7) prove (41.1). Subtracting the common first eigenvalue gives
(41.2); $\omega_\sigma>0$ gives (41.3) and the consecutive-spacing
assertion. Applying this at the successive fixed indices proves
simplicity of each fixed initial list for small parameters, even
though no simplicity of the complete unperturbed Fourier multiset
was assumed. $\square$

## 42. Fluctuation laws of actual full ground probabilities

**Theorem 42.1 (original-coordinate ground law with exact normalization).**
Choose any normalized actual full ground $f_\kappa$ of (35.1) in either
critical family. Set $c=c_\sigma$, $\ell=\ell_{\sigma,\kappa}$ and
$w=w_{\sigma,\kappa}$ from (38.2)--(38.4). With the actual representative
$D\in[-\pi,\pi]$, the rescaled probability densities, extended by zero
outside their displayed charts, satisfy

$$
\left\|
 \ell\,|f_\kappa(k,\theta,v,\ell y)|^2
          1_{\{|y|<\pi/\ell\}}
 -\frac{u_c(k)^2}{(2\pi)^2}
           \sqrt{\frac{\gamma_\sigma}{\pi}}e^{-\gamma_\sigma y^2}
\right\|_{L^1(dk\,d\theta\,dv\,dy)}\longrightarrow0.
\tag{42.1}
$$

Equivalently, in the independent length $w$ the law is

$$
\left\|
 w\,|f_\kappa(k,\theta,v,wz)|^2
          1_{\{|z|<\pi/w\}}
 -\frac{u_c(k)^2}{(2\pi)^2}\frac{e^{-z^2}}{\sqrt\pi}
\right\|_{L^1(dk\,d\theta\,dv\,dz)}\longrightarrow0.
\tag{42.2}
$$

These are laws of the entire normalized ground state on the original
completed domain, not of a prescribed ansatz. They hold for every
fixed original $s\in\mathbb R$, $b>0$, $g>0$ through both signs.
They include tightness on the shrinking scale and independence of the
limiting hidden fluctuation from the normalized height and visible
laws. They assert no such independence of the native processes at
finite parameter.

In particular, for every $R\ge0$,

$$
\mathbb P_{|f_\kappa|^2d\mu}\{\rho(D)\le Rw\}
 \longrightarrow\operatorname{erf}(R)
 :=\frac1{\sqrt\pi}\int_{-R}^{R}e^{-z^2}\,dz.
\tag{42.3}
$$

For $0<p<1$, let $q_\kappa(p)$ be the least radius containing ground
probability $p$. Then

$$
\frac{q_\kappa(p)}{w_{\sigma,\kappa}}
       \longrightarrow\operatorname{erf}^{-1}(p).
\tag{42.4}
$$

Thus $w$ specifies an actual ground fluctuation width, including the
leading coefficient of every fixed probability radius, without being
defined by such a radius. No convergence of unbounded moments is
needed for (42.1)--(42.4).

Proof. Let $\widehat f_\kappa$ be the normalized positive ground of
$\widehat{\mathscr H}_\kappa=L_\kappa-gU_\kappa$.
For small parameters, (41.6)--(41.7) identify it with
$(2\pi)^{-1}f_\kappa^{\rm bl}$. Theorem 40.3 and the same exclusion
of nonzero visible pairs give its actual full gap

$$
\widehat\Delta_\kappa
 =2\omega_\sigma h+o(h).
\tag{42.5}
$$

Put $\delta_\kappa=\|W_\kappa-U_\kappa\|_\infty=o(h)$.
For the original normalized ground, bounded perturbation comparison
gives

$$
\widehat{\mathfrak q}_\kappa[f_\kappa]
 \le\Lambda_{\sigma,1}+g\delta_\kappa
 \le\widehat\Lambda_{\kappa,1}+2g\delta_\kappa.
\tag{42.6}
$$

The spectral theorem and (42.5) therefore imply

$$
\|(1-|\widehat f_\kappa\rangle
                  \langle\widehat f_\kappa|)f_\kappa\|_2^2
 \le\frac{2g\delta_\kappa}{\widehat\Delta_\kappa}
 \longrightarrow0.
\tag{42.7}
$$

Consequently, after constant phases,
$\|f_\kappa-\widehat f_\kappa\|_2\to0$.
This step uses the attained actual eigenstate, its full Rayleigh
quotient and the proved auxiliary full gap. It does not infer an
eigenstate law from upper-bound trials.

The change of variables $D=\ell y$ is unitary after multiplying
amplitudes by $\sqrt\ell$. Equation (40.11) now gives, with zero
extension outside the chart,

$$
\sqrt\ell\,f_\kappa(k,\theta,v,\ell y)
 \longrightarrow\frac{u_c(k)}{2\pi}\psi_\sigma(y)
 \quad\hbox{strongly in }L^2(dk\,d\theta\,dv\,dy),
\tag{42.8}
$$

up to constant phases. The elementary bound
$\||F|^2-|G|^2\|_1\le(\|F\|_2+\|G\|_2)\|F-G\|_2$
proves (42.1) without any phase convention on probabilities.
The further fixed rescaling $y=z/\sqrt{\gamma_\sigma}$ gives
(42.2). Its normalization is exact:
$\int_Iu_c^2dk=1$, the raw visible volume is $(2\pi)^2$, and
$\int_{\mathbb R}e^{-z^2}dz=\sqrt\pi$.
Thus neither the hidden Jacobian nor a circle-volume factor has
been absorbed into an unspecified constant.

Integrating (42.2) over $k,\theta,v$ and $|z|\le R$ proves (42.3).
For any fixed $0<p<1$, strict continuity and monotonicity of
$\operatorname{erf}$, tested at radii on either side of
$\operatorname{erf}^{-1}(p)$, squeeze $q_\kappa(p)/w$ to (42.4).
Tightness and uniqueness of the ground limit were supplied by
Lemma 40.2 and the simple oscillator bottom; (42.7) transfers both
to every original normalized full ground family. $\square$

## 43. Quantitative reduction, source distinctions and classical scope

**Corollary 43.1 (what the quantitative reduction preserves).**
For either critical family and every fixed $N$, subtracting the actual
full ground energy and dividing by the explicit native scale gives

$$
\frac{\Lambda_{\sigma,N}-\Lambda_{\sigma,1}}
                         {h_{\sigma,\kappa}}
 \longrightarrow2(N-1)\omega_\sigma.
\tag{43.1}
$$

The corresponding rescaled actual ground law is (42.2). These statements
provide a centered fixed-index oscillator description retaining the
hidden fluctuation. They do not identify the complete theory with its
actual native $\kappa=0$ three-coordinate leaf or with its complete
$D$-independent restriction, even at $b_*$ of (34.2).

Proof. Equations (41.2) and (42.2) prove the quantitative assertions.
For the actual zero leaf and complete sector, reuse the complete
ordered spectra and strictly positive gaps (36.7)--(36.8). Their
unscaled first spacings tend respectively to
$\Gamma(0)$ in the raw regime and to
$\Gamma(gc_0)$ and $\Gamma(gc_0/(2\pi))$ in the unit regime.
Every one is positive, whereas the full spacings in (41.2) have
positive finite limits only after division by a scale tending to
zero. Thus even subtracting the respective actual ground energies
cannot match their fixed low spectra. At $b_*$ the equality of
unscaled ground energies and embedded probabilities in (37.1)
persists, but the hidden oscillator and its collapsing original-clock
gap persist as well. Away from $b_*$ the original ground comparisons
of Theorem 34.1 already distinguish the actual leaf.

The complete restriction is exactly the closed-form restriction in
(36.6), under $Jh=(2\pi)^{-1/2}h$. It therefore retains coupling
$g/(2\pi)$ against the raw $D$-integrated field, with both height
faces and the original clock. It is distinct from the visible-zero
block (40.1), which retains the entire hidden circle and its
fluctuations. A normalized $D$-independent amplitude has uniform
hidden probability $dD/(2\pi)$, in contrast to (42.1)--(42.3).
No invariance of that restricted subspace under the original
attractive operator is used or concluded.

The actual zero leaf instead has raw measure $d\nu_B$, unit pole
and $D=0$ on its native histories. Embedding its probabilities at
$D=0$ is not a Hilbert-space embedding into the original raw
$L^2(d\mu)$ space. The full amplitudes still lose unscaled strong
compactness as in Theorem 33.2; the strong statement (42.8) uses
an explicitly changing hidden coordinate and its Jacobian.
This proves the asserted limits of replacement. $\square$

**Proposition 43.2 (the fluctuation law changes no source or native law).**
The measures in (42.1)--(42.2) are attractive ground probabilities.
They neither describe the original free diffusion nor implement a
source conditioning, reset, preparation, projection or new driver.
The comparisons retain the original fixed data, controls,
preparations, covariance, raw measures, $2\pi$ periods, clock and
both absorbing height faces.

Proof. All full spectral and eigenstate comparisons used exactly
(35.1). The visible average (38.5) was removed with an error below
the spacing scale in (41.4) and (42.7); it was not substituted for
the specified source. The coordinate changes (40.2) and (42.2)
are probability and form changes of variables with their explicit
Jacobians, not changes to the original generator or its clock.

The actual raw conditional source already has the $D/r_s$ law
(32.11), with height density $\phi/J_\phi$ and hidden Gaussian
variance $2\beta$. Its ground has the narrower length
$w/r_s\to0$, height density $u_{gc_s}^2$, and the different
normalization in (42.2). At the unit cutoff the original conditional
source retains the nonconstant circle density $G_{\beta b}(D)$
of (32.10), whereas its ground concentrates on length $w\to0$.
The three source laws (34.7)--(34.9), including their distinctions
at $b_*$, remain unchanged. Source charge still differs from field
mass as in (32.12). Dividing by survival changes neither subsequent
height death nor the original free clock.

The results of the free-diffusion quotient classification and its
scope in [Free diffusion quotient rigidity, Theorem 3.1 and
Definition 6.2](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md)
therefore supply no additional attractive invariance or preparation
claim. The native history and principal-symbol boundaries in
[Probability, phase transport and holonomy, Theorems 10.3 and
10.5](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)
also persist: rank-two principal covariance is unchanged by a
spectral fluctuation calculation or a coordinate map. These are
statements about the specified state variables, not a derivation
of three physical spatial axes or an autonomous operational
interface. $\square$

**Source correspondence 43.3 (classical overlap and the native increment).**
The differentiated native estimates (39.1)--(39.4), the positive
centered compactness argument (40.3)--(40.9), and their full-form
consequences (41.1)--(42.4) are ordinary mathematical deductions
from the exact native suppliers. They extend the unscaled endpoint
of §§35--37 without revising it. The original scalar ground data,
critical times and field profiles, uniform visible separation,
fixed-parameter simplicity, and complete comparison spectra are
reused from §§31--37 and [G, §§23,25--29]. They are not new claims
of this increment.

The classical overlap and its applicability boundaries are as follows.

- G. Teschl, *Mathematical Methods in Quantum Mechanics*, GSM 99,
  [author text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
  Theorems 4.10, 5.11 and 6.24 supply respectively form-domain
  min-max, the semibounded selfadjoint Trotter formula and closed
  bounded-multiplier perturbations. All perturbations used here are
  bounded at each fixed parameter, with relative form bound zero.
  Compact resolvent and the domains are explicitly supplied above
  before min-max is applied. The one-dimensional oscillator in
  §8.3, (8.35)--(8.41), supplies its Hermite eigenvalues and normalized
  Gaussian; the new task is its earned native correspondence.
- B. Simon, *Semiclassical Analysis of Low Lying Eigenvalues. I.
  Non-degenerate Minima: Asymptotic Expansions*, Ann. Inst. H.
  Poincaré A 38 (1983), 295--308,
  [§1, (A1)--(A4), Theorem 1.1](https://www.numdam.org/item/AIHPA_1983__38_3_295_0.pdf),
  gives the classical fixed-index harmonic approximation for fixed
  smooth scalar potentials with finitely many nondegenerate minima
  and its exterior assumptions. Here only the hidden kinetic scale
  vanishes, $\varepsilon$ is fixed, the raw field narrows, and the
  original full square has compensating frequencies. Thus that theorem
  is not invoked as a direct full-form theorem. Lemma 40.2 and
  (41.6) supply the required native lower limit and exclusion.
  The [1984 erratum, p.224](https://www.numdam.org/item/AIHPA_1984__40_2_224_0.pdf)
  corrects Theorem 5.1's higher-order expansion in a degenerate
  oscillator level without an additional parity condition. No
  higher-order or degenerate-level expansion is claimed here.
- A. Martinez, *Développements asymptotiques dans l'approximation de
  Born-Oppenheimer*, Journées Équations aux dérivées partielles
  (1988), article X,
  [§2, (H1)--(H4) and stated theorem](https://proceedings.centre-mersenne.org/item/10.5802/jedp.354.pdf),
  considers $-h^2\Delta_x-\Delta_y+V$ on Euclidean product spaces.
  Its smooth lower-bounded potential, derivative/common-domain
  conditions, unique nondegenerate lowest-band minimum and exterior
  and discrete-fibre assumptions are material hypotheses. They do
  not automatically cover the original completed degenerate form,
  its Dirichlet cylinder or its moving raw field. The article refers
  elsewhere for its theorem's proof; it is a comparison of methods,
  not a proof supplier used to bypass (39.3) or (40.4).
- J. Lampart and S. Teufel, *The adiabatic limit of Schrödinger
  operators on fibre bundles*,
  [arXiv:1402.0382v2, Conditions 1--3, Proposition 2.5 and §4.2](https://arxiv.org/pdf/1402.0382v2),
  treat Riemannian fibre bundles with compact fibres, allowed
  Dirichlet fibre boundary, complete base, bounded geometry, a
  uniformly isolated eigenband and uniform coefficient bounds.
  Proposition 2.5's exclusion of other bands also uses the stated
  lower bound on the horizontal perturbation. The original full
  rank-two principal form is not a Riemannian Laplacian on its
  four-coordinate state space. No direct application of that theorem
  or general adiabatic norm-resolvent estimate is asserted. The
  native full-frequency exclusion and centered compactness needed
  here have instead been proved in (41.6) and Lemma 40.2.

Harmonic localization, Hermite spectra, fast-band separation and
variational compactness are classical methods. The substantive
native increment is the correspondence at the actual centered
spacing scale for both original fields and the probability law of
actual full grounds, including all the original frequencies and raw
normalizations. This is a `repo-derived` application and derivation;
no global priority or exhaustive no-overlap assertion is made.
The singular fixed-pole comparison in
[Fixed-pole strict ground-energy gap, Theorem 7.2 and Boundary
8.2](FIB_NATIVE_FIXED_POLE_STRICT_GROUND_ENERGY_GAP.md)
and the small-coupling singular restricted limit in
[Observation quotient, Theorem 11.1](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md)
retain their different hypotheses and are not substituted for the
critical-cutoff full forms.

The conclusions here are ordinary proofs, without a claim of Lean
verification or physical validation. Their exact scope is fixed-index
centered spacings and the normalized ground fluctuation law for the
two stated critical families and every fixed original datum. They do
not assert growing-index or Weyl laws, an absolute subleading
expansion about the frozen scalar energy, general norm-resolvent
convergence, another cutoff family, uniformity in a further parameter
limit, empirical spatial selection, a preparation or acquisition
procedure, or many-body stability. None of those assertions is
needed in (41.2) or (42.2).

## 追加锚（本行以下为增补区）


## 44. The original amplitude boundary and independent coefficient data

**Definition 44.1 (fixed-time response on the whole base).**
Retain Definition 31.1, the two critical families and every original
fixed datum, with both signs of $\kappa\to0$. Write
$\mathscr H_B=L^2(B,d\nu_B)$ and $\mathscr H=L^2(\Omega,d\mu)$.
The operators below are those of the entire completed forms (25.9),
not their restrictions:

$$
\begin{aligned}
H_{{\rm raw},\kappa}&=L_\kappa-gM_{V_{\kappa,\tau_s}},&
H_{{\rm unit},\kappa}&=L_\kappa-gM_{W_{\rm unit}(\kappa,\tau_b)},\\
Jh(q,D)&=(2\pi)^{-1/2}h(q),&
J^*f(q)&=(2\pi)^{-1/2}\int_{\mathbb T}f(q,D)\,dD,\\
C_{\sigma,\kappa}(t)&=J^*e^{-tH_{\sigma,\kappa}}J,&
\mathcal D_{\sigma,\kappa}(t)
 &=C_{\sigma,\kappa}(2t)-C_{\sigma,\kappa}(t)^2.
\end{aligned}
\tag{44.1}
$$

All fields are bounded at each parameter, and (32.9) bounds them
uniformly along either critical family. Their selfadjoint generators
have the original operator domains $D(L_\kappa)$ and form domains
$\mathcal F_\kappa$, with a common finite lower bound for fixed
data and $g$; the semigroups act on all of $\mathscr H$. Put, using exactly the
full-base operators of Definition 36.1,

$$
S_t=e^{-t\mathcal K_0},\qquad
T_c(t)=e^{-t\mathcal K_c},\qquad
F(x)=e^{-x^2/(4\beta)},\qquad
m_s=c_s\sqrt{4\pi\beta}.
\tag{44.2}
$$

Define the following bounded operators independently of the unknown
native response:

$$
\begin{aligned}
A_s(t)&=\frac1{2\pi}\int_{\mathbb R}
              [T_{gc_sF(x)}(t)-S_t]\,dx,\\
D_s(t)&=\frac1{2\pi}\int_{\mathbb R}
              [T_{gc_sF(x)}(t)-S_t]^2\,dx,\\
B_b(t)&=\frac1{2\pi}\int_{\mathbb T}
                    T_{gc_0G_{\beta b}(D)}(t)\,dD,\\
V_b(t)&=\frac1{2\pi}\int_{\mathbb T}
             [T_{gc_0G_{\beta b}(D)}(t)-B_b(t)]^2\,dD.
\end{aligned}
\tag{44.3}
$$

These are norm Bochner integrals. Indeed bounded-multiplier Duhamel
estimates give, for $0\le c\le c_{\max}$,

$$
\|T_c(t)-S_t\|
 \le t c\|\phi\|_\infty e^{tc_{\max}\|\phi\|_\infty}.
\tag{44.4}
$$

Consequently the first two integrands are dominated in norm by
constants times $F$ and $F^2$, respectively. The circle integrands
are norm continuous. In particular $D_s(t)$ and $V_b(t)$ are positive
operators. All modes $(n,m)$ of (36.1) remain in (44.3).

**Theorem 44.2 (native fixed-time limits and the sharp raw scale).**
For every fixed $t>0$, every fixed original $s\in\mathbb R$,
$b>0$, $g>0$ and model datum, through both signs, the following
limits hold strongly on the entire space $\mathscr H_B$:

$$
\begin{aligned}
C_{{\rm raw},\kappa}(t)&\longrightarrow S_t,&
\frac{C_{{\rm raw},\kappa}(t)-S_t}{r_s}
 &\longrightarrow A_s(t),\\
\frac{\mathcal D_{{\rm raw},\kappa}(t)}{r_s}
 &\longrightarrow D_s(t),&
C_{{\rm unit},\kappa}(t)&\longrightarrow B_b(t),\\
\mathcal D_{{\rm unit},\kappa}(t)&\longrightarrow V_b(t).
\end{aligned}
\tag{44.5}
$$

Strong convergence here means convergence on each fixed base $L^2$
input, without a visible-mode or smoothness restriction. The scaled
raw operator families in (44.5) are uniformly bounded. On the fixed
unit base vector

$$
h_*(k,\theta,v)=\frac{\phi(k)}{2\pi}
\tag{44.6}
$$

which belongs to $D(\mathcal K_c)$ for every fixed $c\ge0$ by
(36.1), one has, for every such $t$,

$$
\langle A_s(t)h_*,h_*\rangle>0,\qquad
\langle D_s(t)h_*,h_*\rangle>0,\qquad
\langle V_b(t)h_*,h_*\rangle>0.
\tag{44.7}
$$

Thus $r_s=|\kappa|\sqrt{\tau_s}$ is the first nonzero raw correction
and equal-step defect scale on this declared test. The leading raw
family is autonomous, but its first correction contains a nonzero
composition defect. The unit limiting family fails the equal-step
semigroup law at every positive time. No small-coupling hypothesis
is imposed. The proof is given in §§45--47.

## 45. Native error control at the field-width scale

**Lemma 45.1 (an integrated native remainder and its boundary estimate).**
For the raw field set

$$
P_\kappa(q,D)=c_s\phi(k)F(D/r_s),
\qquad -\pi\le D\le\pi,
\tag{45.1}
$$

with periodic interpretation. Its values match at the seam; no
regularity of its derivative at that seam is needed. Then

$$
\sup_{q\in B}\int_{\mathbb T}
       |V_{\kappa,\tau_s}(q,D)-P_\kappa(q,D)|\,dD=o(r_s),
\qquad
\sup_q\int_{\mathbb T}V_{\kappa,\tau_s}(q,D)\,dD=O(r_s).
\tag{45.2}
$$

If $C^P_\kappa(t)=J^*e^{-t(L_\kappa-gM_{P_\kappa})}J$, then,
in operator norm on the whole base,

$$
\|C_{{\rm raw},\kappa}(t)-C^P_\kappa(t)\|=o(r_s).
\tag{45.3}
$$

Proof. The exact marginal identity [G, (23.4)] sets $j=0$ in
[G, (26.13)]. The zero visible mode is the scalar killed height
kernel. Its sine expansion and the uniformly separated nonzero
visible modes give, uniformly on $B$,

$$
\begin{aligned}
\overline V_{\kappa,\tau_s}(q)
 &=\frac{\phi(k_0)\phi(k)}{\lambda(2\pi)^2}
       e^{-\lambda\tau_s}+o(e^{-\lambda\tau_s}),\\
\frac1{r_s}\int_{\mathbb T}V_{\kappa,\tau_s}(q,D)\,dD
 &\longrightarrow m_s\phi(k).
\end{aligned}
\tag{45.4}
$$

For the first line, (26.12) with $(n,m)\ne(0,0)$ and $j=0$
has a summable bound $Ce^{-(\lambda+d)t}$ after decreasing a
fixed $d>0$; the higher height modes decay at least as
$e^{-4\lambda t}$. Time integration preserves these relative
errors. The second line uses (32.14); its coefficient is
$\phi(k_0)e^{-\lambda s}/((2\pi)^2\sqrt\lambda)
 =c_s\sqrt{4\pi\beta}$.

For each fixed $R$, (32.9) gives

$$
\sup_{q,\ |x|\le R}
 |V_{\kappa,\tau_s}(q,r_sx)-c_s\phi(k)F(x)|\longrightarrow0.
\tag{45.5}
$$

Both fields in (45.1)--(45.5) are nonnegative. Their total
$D$ integrals divided by $r_s$ converge uniformly to the same
$m_s\phi(k)$. Their integrals on $|D|\le Rr_s$, divided by
$r_s$, also converge uniformly to the same
$c_s\phi(k)\int_{-R}^R F(x)dx$. Subtracting gives

$$
\limsup_{\kappa\to0}\frac1{r_s}\sup_q
 \int_{|D|>Rr_s}V_{\kappa,\tau_s}(q,D)\,dD
 \le c_s\|\phi\|_\infty\int_{|x|>R}F(x)dx.
\tag{45.6}
$$

The model has the same tail bound. On the inner interval (45.5)
controls the absolute difference by $o(r_s)$ for fixed $R$.
Taking the parameter limit and then $R\to\infty$ proves (45.2).
This argument needs neither a rate in (32.9) nor an estimate
obtained by dividing its uniform $o(1)$ by $r_s$.

Here is the compression estimate used to pass from (45.2) to
(45.3). The free semigroup $U_\kappa(t)=e^{-tL_\kappa}$ is positive,
and exactly
$U_\kappa(t)J=J\overline S_\kappa(t)$, where
$\overline S_\kappa(t)=e^{-t\overline L_\kappa}$ on the complete
base domain [G, (23.3)--(23.5)]. For bounded real fields
$0\le W_1,W_2\le M$, Trotter's formula gives

$$
|e^{-t(L_\kappa-gM_{W_i})}Jh|
 \le e^{gMt}J\overline S_\kappa(t)|h|.
\tag{45.7}
$$

This is the bounded selfadjoint, semibounded case of Teschl's
Theorem 5.11; bounded multiplication leaves the operator domain
unchanged, so its hypotheses hold. Duhamel's formula, tested between
$Jz$ and $Jh$, and (45.7) bound the compressed difference by

$$
\begin{aligned}
&\left|\left\langle
 J^*\bigl[e^{-t(L_\kappa-gM_{W_1})}
          -e^{-t(L_\kappa-gM_{W_2})}\bigr]Jh,z
 \right\rangle\right|\\
&\quad\le\frac{g e^{gMt}}{2\pi}
 \int_0^t\int_B
   (\overline S_\kappa(u)|h|)(q)
   (\overline S_\kappa(t-u)|z|)(q)
   \left[\int_{\mathbb T}|W_1-W_2|(q,D)dD\right]d\nu_B\,du\\
&\quad\le\frac{gt e^{gMt}}{2\pi}
 \sup_q\int_{\mathbb T}|W_1-W_2|(q,D)dD\,\|h\|_2\|z\|_2.
\end{aligned}
\tag{45.8}
$$

The last step uses the base $L^2$ contraction and Cauchy--Schwarz.
The common bound $M$ is supplied by (32.9). Taking the supremum
over unit $h,z$ and using (45.2) proves (45.3). This controls the
actual full field, including its nonzero visible frequencies, at
the required native scale. The auxiliary field (45.1) has not
been declared the original source. $\square$

## 46. The raw response and its first returning hidden component

**Theorem 46.1 (raw expansion with all native cross terms).**
The raw assertions of (44.5)--(44.7) hold with the coefficients
(44.3).

Proof. First, the free base difference is smaller than the proposed
scale:

$$
\|\overline S_\kappa(t)-S_t\|=O_t(a)=o(r_s).
\tag{46.1}
$$

To see the operator-norm estimate, use the exact complete Fourier
sum on the base. In its $(n,m)$ block the two scalar operators
have the same domain $H^2(I)\cap H_0^1(I)$ and their bounded
potentials differ by at most $Ca(n^2+m^2)$. The coefficient
functions converge in supremum norm at rate $O(a)$ by (25.4).
Both scalar bottoms are at least
$\lambda+c\Psi(\sqrt{n^2+m^2})$ by [G, (26.6)] with $j=0$,
including $\kappa=0$ as in §36. Scalar Duhamel estimates therefore
give a block difference at most

$$
Ca t(n^2+m^2)e^{-t[\lambda+c\Psi(\sqrt{n^2+m^2})]}.
\tag{46.2}
$$

Its supremum over the lattice is $O_t(a)$. The zero block agrees
exactly. This proves (46.1) on the complete base, without promoting
an interior form core to an operator core.

For the auxiliary field (45.1) we now compute its compressed
response. The following representation uses precisely the native
killed law [G, (16.4), (25.4)] from a starting point $q=(k,\theta,v)$:

$$
\begin{aligned}
K_u&=k+\sqrt2\varepsilon B_u^1,\qquad
 \zeta=\inf\{u:K_u\notin I\},\\
q_{\kappa,u}
 &=\left(K_u,\theta+\sqrt2\int_0^u A_\kappa(K_w)dB_w^2,
                    v+\sqrt2\int_0^u B_\kappa(K_w)dB_w^2\right),\\
Y_{\kappa,u}&=\sqrt2\int_0^u b_\kappa(K_w)dB_w^2,\qquad
D_u=D+\kappa Y_{\kappa,u}\pmod {2\pi}.
\end{aligned}
\tag{46.3}
$$

The phase integrals are stopped at $\zeta$ when necessary. The weights
$R_\kappa$ and $R_0$ below are defined on $\{t<\zeta\}$ by their
displayed formulas and set to zero on $\{\zeta\le t\}$. Both visible
phase entries are read modulo $2\pi$. The two
original Brownian motions are used throughout, and the same $B^2$
drives all three angular increments. Thus (46.3) retains every
cross term in the original square $|Q_\kappa f|^2$.
The free-law/Friedrichs correspondence and its marginal are those
of [G, §23]. The bounded-potential path formula used here follows
by applying the Trotter product formula to this killed free law:
the product weights are exponentials of time Riemann sums, which
converge along continuous surviving paths. Their absolute values
are bounded by $e^{gMt}$, so bounded convergence identifies the
formula first on bounded continuous inputs and then on $L^2$.
Only bounded continuous potentials are needed below.

Let $L=2\pi/r_s$, let $F_L$ denote the periodic function equal to
$F$ on $[-L/2,L/2]$, and put
$\eta_\kappa=\kappa/r_s$, so $|\eta_\kappa|=\tau_s^{-1/2}\to0$.
Integrating the initial $D$ in (44.1), then changing variables
$D=r_sx$, gives exactly

$$
\begin{aligned}
\frac{[C^P_\kappa(t)-\overline S_\kappa(t)]h(q)}{r_s}
 &=\mathbb E_q\left[
       R_\kappa h(q_{\kappa,t});\ t<\zeta\right],\\
R_\kappa
 &=\frac1{2\pi}\int_{-L/2}^{L/2}
 \left\{\exp\left(gc_s\int_0^t
       \phi(K_u)F_L(x+\eta_\kappa Y_{\kappa,u})du\right)-1\right\}dx.
\end{aligned}
\tag{46.4}
$$

This exact formula has already integrated the entire hidden circle;
no spectral-index expansion or oscillator approximation is involved.
If $M_0=gc_s\|\phi\|_\infty$, the inequality
$e^z-1\le e^{M_0t}z$ for $0\le z\le M_0t$ and translation
invariance on that circle give the deterministic bound

$$
0\le R_\kappa\le
 \frac{gc_s t\|\phi\|_\infty e^{M_0t}}{2\pi}
                     \int_{\mathbb R}F(x)dx=:K_t.
\tag{46.5}
$$

Consequently the operators on the first line of (46.4) have norm
at most $K_t$, since the right side is dominated by
$K_t\overline S_\kappa(t)|h|$.

Define, on the same killed height paths,

$$
R_0=\frac1{2\pi}\int_{\mathbb R}
 \left\{\exp\left(gc_sF(x)\int_0^t\phi(K_u)du\right)-1\right\}dx.
\tag{46.6}
$$

Then $\mathbb E_q|R_\kappa-R_0|\to0$, uniformly in the starting
point. Here are bounds that justify both the expanding circle and
the moving hidden phase. The total variation of $F_L$ on its
circle is at most $\|F'\|_{L^1(\mathbb R)}$. Hence

$$
\int_{-L/2}^{L/2}|F_L(x+z)-F_L(x)|dx
 \le |z|\|F'\|_1.
\tag{46.7}
$$

The stopped stochastic integral in (46.3) satisfies
$\mathbb E_q|Y_{\kappa,u}|\le C\sqrt u$, uniformly for $u\le t$,
by its isometry and the uniform bound on $b_\kappa$. The exponential
is Lipschitz on $[0,M_0t]$. Replacing each shifted $F_L$ in
(46.4) by the unshifted one therefore changes $R_\kappa$ in
expected absolute value by at most $C_t|\eta_\kappa|$.
Extending the remaining unshifted integral from $[-L/2,L/2]$ to
$\mathbb R$ costs at most
$C_t\int_{|x|>L/2}F(x)dx\to0$. This proves the assertion.
In particular these errors are errors of the already divided
response in (46.4), rather than an unscaled error divided later.

The base angular increments in $q_{\kappa,t}$ converge to those
in $q_{0,t}$ in mean square, uniformly in the starting point,
because $A_\kappa-A_0$ and $B_\kappa-B_0$ are $O(a)$ uniformly.
The height path and its two-sided killing time agree exactly.
For bounded smooth base inputs, (46.5)--(46.7) therefore show
uniform, hence base $L^2$, convergence of (46.4) to

$$
\mathbb E_q[R_0h(q_{0,t});\ t<\zeta]
 =\frac1{2\pi}\int_{\mathbb R}
       [T_{gc_sF(x)}(t)-S_t]h(q)dx=A_s(t)h(q).
\tag{46.8}
$$

The equality uses the same bounded-potential path formula on the
actual base operator $\mathcal K_c$ of §36. Bounded smooth inputs
with compact height support are dense in $\mathscr H_B$.
The uniform operator bound (46.5) and boundedness of $A_s(t)$
extend (46.8) to every fixed base $L^2$ input. Combining it with
(45.3) and (46.1) proves the raw response expansion in (44.5),
including its uniform scaled bound and both signs.

Write $\Delta_x(t)=T_{gc_sF(x)}(t)-S_t$. Strong expansion of the
bounded products, using the uniform scaled bound just proved, gives

$$
\begin{aligned}
\frac{\mathcal D_{{\rm raw},\kappa}(t)}{r_s}
 &\longrightarrow A_s(2t)-S_tA_s(t)-A_s(t)S_t\\
 &=\frac1{2\pi}\int_{\mathbb R}\Delta_x(t)^2dx=D_s(t).
\end{aligned}
\tag{46.9}
$$

The second identity follows from the semigroup law of each fixed
$T_c$ and $S$: the integrand before simplification is
$T_c(t)^2-S_t^2-S_t(T_c(t)-S_t)-(T_c(t)-S_t)S_t
 =(T_c(t)-S_t)^2$. No commutation of $T_c(t)$ with $S_t$
is assumed. Their norm integrability follows from (44.4).

Finally, on the angular-constant vector $h_*$, the killed height
path formula reads

$$
T_c(t)h_*(q)=\frac1{2\pi}\mathbb E_k\left[
 e^{c\int_0^t\phi(K_u)du}\phi(K_t);\ t<\zeta\right].
\tag{46.10}
$$

For $c>0$ this is strictly larger than $S_th_*(q)$ at every
interior height: survival has positive probability and $\phi$ is
positive throughout $I$. Thus
$\langle A_s(t)h_*,h_*\rangle>0$ and

$$
\langle D_s(t)h_*,h_*\rangle
 =\frac1{2\pi}\int_{\mathbb R}\|\Delta_x(t)h_*\|_2^2dx>0.
\tag{46.11}
$$

Together with (44.5), these strict inequalities prove that neither
raw leading coefficient disappears on this fixed nonzero test.
The field width $r_s$ differs from both the ground width
$a\tau_s^{1/4}$ and the spacing scale $\tau_s^{-1/2}$ of §38.
Their ratios are not used as error estimates. $\square$

## 47. The complete unit boundary limit and strict finite-time variance

**Theorem 47.1 (unit limit without a coupling restriction).**
The unit assertions of (44.5)--(44.7) hold on the whole base.
Moreover, for every fixed $t>0$,

$$
B_b(2t)-B_b(t)^2=V_b(t)\ge0,
\qquad \langle V_b(t)h_*,h_*\rangle>0.
\tag{47.1}
$$

Proof. By (32.9), the original unit field converges uniformly on
the full cylinder to $c_0\phi(k)G_{\beta b}(D)$. The potentials
are uniformly bounded; all original positive $g$ are allowed.
Use (46.3) in the bounded-potential path formula. On each fixed
time interval the hidden displacement $\kappa Y_{\kappa,u}$
tends to zero in expected supremum, by the martingale maximal
inequality and bounded $b_\kappa$. The base angular increments
converge to those at zero as before. Uniform continuity of the
circle heat density and uniform field convergence show, for bounded
smooth $h$, convergence of the compressed path formula to

$$
\frac1{2\pi}\int_{\mathbb T}\mathbb E_q\left[
 \exp\left(gc_0G_{\beta b}(D)\int_0^t\phi(K_u)du\right)
 h(q_{0,t});\ t<\zeta\right]dD=B_b(t)h(q).
\tag{47.2}
$$

The convergence is uniform in $q$. The uniform semigroup bound
$e^{gMt}$ and density of those inputs extend it strongly to all
$\mathscr H_B$. Formula (47.2) is the boundary compression of the
direct integral of $T_{gc_0G_{\beta b}(D)}(t)$ over the unchanged
raw hidden circle. It is not evolution in the averaged potential.

Uniform boundedness permits the strong limit of the squared
compressed operators. With $T_D=T_{gc_0G_{\beta b}(D)}(t)$,
selfadjointness and the semigroup law in each fixed fibre give

$$
\begin{aligned}
B_b(2t)-B_b(t)^2
 &=\frac1{2\pi}\int_{\mathbb T}T_D^2dD-B_b(t)^2\\
 &=\frac1{2\pi}\int_{\mathbb T}(T_D-B_b(t))^2dD.
\end{aligned}
\tag{47.3}
$$

Thus the defect equals $V_b(t)$. This is the native evaluation of
the compression identity already owned by [Free quotient,
Proposition 5.1](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md),
not a transfer of the singular attractive hypotheses in
[Observation quotient, §6](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md).
Every semigroup here comes from the actual bounded critical field.

For strictness, (46.10) shows that $c\mapsto T_c(t)h_*$ is strictly
increasing pointwise on the interior for every $t>0$. The circle
function $G_{\beta b}$ is continuous and nonconstant for every
finite $b>0$, since its first Fourier coefficient is nonzero.
Therefore $D\mapsto T_Dh_*$ is a continuous, nonconstant
$\mathscr H_B$-valued function, and

$$
\langle V_b(t)h_*,h_*\rangle
 =\frac1{2\pi}\int_{\mathbb T}
        \|T_Dh_*-B_b(t)h_*\|_2^2dD>0.
\tag{47.4}
$$

This proves strict failure at each fixed positive time, for every
original $g>0$, and completes the proof of Theorem 44.2. $\square$

## 48. The actual ground pole has vanishing amplitude boundary residue

**Theorem 48.1 (vanishing residue for every normalized actual ground).**
In either original critical family, through both signs and for every
fixed original datum and $g>0$, every normalized actual full ground
$f_{\sigma,\kappa}$ satisfies

$$
\|J^*f_{\sigma,\kappa}\|_{\mathscr H_B}^2\longrightarrow0.
\tag{48.1}
$$

In particular the residue of the actual full ground spectral pole in
the boundary compression vanishes. This is compatible with all the
energies, collapsing gaps and ground probability laws of §§33,41--42.

Proof. For $0<\delta<\pi$ let
$E_\delta=\{D:\rho(D)<\delta\}$. Cauchy--Schwarz in the raw hidden
coordinate, whose measure on this set is $2\delta$, gives

$$
\begin{aligned}
\|J^*(1_{E_\delta}f_{\sigma,\kappa})\|_2
 &\le\sqrt{\delta/\pi}\,\|1_{E_\delta}f_{\sigma,\kappa}\|_2,\\
\|J^*f_{\sigma,\kappa}\|_2
 &\le\sqrt{\delta/\pi}
       +\|1_{E_\delta^c}f_{\sigma,\kappa}\|_2.
\end{aligned}
\tag{48.2}
$$

The second term tends to zero for each fixed $\delta$ by the
actual-ground concentration of Theorem 33.2. Letting
$\delta\downarrow0$ proves (48.1), including arbitrary ground phases.
This uses unscaled probability concentration and the $L^2$ norm;
it does not assume amplitude $L^1$ convergence on an expanding
rescaled chart, and claims no sharp residue rate.

For small parameters the actual ground is simple by (41.2).
Its rank-one spectral projection compresses to
$|J^*f_{\sigma,\kappa}\rangle\langle J^*f_{\sigma,\kappa}|$,
whose norm is exactly (48.1). Its fixed-time contribution is that
operator times $e^{-t\Lambda_{\sigma,1}}$. The ground energies have
finite limits (33.1), so this contribution also tends to zero in
norm. A normalized probability concentrated in a shrinking hidden
set can have unit mass while its amplitude integral tends to zero;
(48.2) proves precisely this distinction for the actual grounds.

The fixed-index eigenvalue laws specify pole locations and spacings,
whereas (48.1) specifies an overlap with the fixed boundary isometry.
Those are different data. Equations (46.4) and (47.2) determine the
fixed-time boundary limits without summing fixed-index eigenvalue
asymptotics. Hence neither the raw free leading response nor the
unit fibre average contradicts the published nonfree full spectral
bottom or its shrinking ground law. No interchange with an
uncontrolled spectral tail is required. $\square$

## 49. Complete restriction, actual zero leaf and the composition boundary

**Theorem 49.1 (same-source restrictions and distinct limiting responses).**
Let $R_{\sigma,\kappa}(t)$ be the semigroup of the complete
$D$-independent restriction, transported to $\mathscr H_B$ by $J$.
Let $Z_{\sigma,\kappa}(t)$ be the attractive semigroup of the actual
native $\kappa=0$ leaf with unit pole $q_0$, coupling $g$ and cutoff
$\tau_s$ or $\tau_b$ indexed by the same $a$. These are different
constructions. Their whole-base strong limits are

$$
\begin{array}{c|ccc}
 &\text{projected full evolution}&\text{complete restriction}
                       &\text{actual zero leaf}\\ \hline
\mathrm{raw}&S_t&S_t&S_t\\
\mathrm{unit}&B_b(t)&T_{gc_0/(2\pi)}(t)&T_{gc_0}(t).
\end{array}
\tag{49.1}
$$

For the raw family this comparison can also be made at its first
scale. Define the fixed operator

$$
\mathcal L_t=\int_0^t S_{t-u}M_\phi S_u\,du.
\tag{49.2}
$$

Then strongly on every fixed base input,

$$
\begin{aligned}
R_{{\rm raw},\kappa}(t)
 &=S_t+r_s\frac{gm_s}{2\pi}\mathcal L_t+o(r_s),\\
Z_{{\rm raw},\kappa}(t)
 &=S_t+r_s gm_s\mathcal L_t+o(r_s).
\end{aligned}
\tag{49.3}
$$

On $h_*$ the difference between the projected full raw coefficient
$A_s(t)$ and the restricted coefficient is strictly positive in
its pairing with $h_*$. Similarly

$$
\langle[B_b(t)-T_{gc_0/(2\pi)}(t)]h_*,h_*\rangle>0.
\tag{49.4}
$$

Thus restriction does not recover the full projected response, even
when their raw leading limits agree.

Proof. The exact complete-domain restriction is [G, (23.5)]:

$$
\overline T_\kappa[h]
 -\frac g{2\pi}\int_B\overline W_\kappa(q)|h(q)|^2d\nu_B,
\qquad h\in\overline{\mathcal F}_\kappa,
\tag{49.5}
$$

where $\overline W_\kappa=\int_{\mathbb T}W_\kappa\,dD$ is an
integral, not an average. Its normalization remains $g/(2\pi)$.
The actual leaf has the complete domain $\overline{\mathcal F}_0$
and its own field $V_{0,\tau}$, divided by $S(\tau)$ for unit
charge, with coupling $g$. Equations (34.3)--(34.5) give the
unit multiplier limits $c_0\phi$ in both constructions; bounded
perturbation and (46.1) prove their two unit limits in (49.1).
The raw integrated asymptotic (45.4) is
$\overline V_{\kappa,\tau_s}=r_s m_s\phi+o(r_s)$ uniformly.
The same scalar sine and nonzero visible-mode argument at the
actual leaf gives $V_{0,\tau_s}=r_s m_s\phi+o(r_s)$ uniformly.

The perturbing raw multipliers in these two comparison problems
are $O(r_s)$. Their second and higher bounded-potential Duhamel
terms are $O(r_s^2)$. The first terms, (46.1), and the uniform
field asymptotics therefore prove (49.3). In the first terms the
uniformly bounded free factors converge strongly at each integration
time, so dominated integration gives $\mathcal L_t$. The free
zeroth term differs from $S_t$ by $O_t(a)=o(r_s)$.
This also proves the raw comparison limits in (49.1).

For strictness in the raw coefficient, insert (46.10) into (44.3).
On surviving height paths $\int_0^t\phi(K_u)du>0$ and
$gc_sF(x)>0$. The strict inequality $e^z-1>z$ for $z>0$
shows that $A_s(t)h_*$ strictly exceeds its term linear in the
potential. The latter is
$gc_s(2\pi)^{-1}\int_{\mathbb R}F(x)dx\,\mathcal L_t h_*
 =gm_s(2\pi)^{-1}\mathcal L_t h_*$, proving the claimed pairing.
For the unit family, strict Jensen inequality in $D$, on the same
surviving paths, gives

$$
\frac1{2\pi}\int_{\mathbb T}
 e^{gc_0G_{\beta b}(D)\int_0^t\phi(K_u)du}\,dD
 >e^{(gc_0/(2\pi))\int_0^t\phi(K_u)du},
\tag{49.6}
$$

because $\int G_{\beta b}dD=1$ and $G_{\beta b}$ is nonconstant.
Multiplication by the positive terminal $\phi(K_t)/(2\pi)$ and
expectation prove (49.4).

The source distinctions are exactly Theorem 34.2. At the unit cutoff
the original full conditional source has density
$\phi(k)G_{\beta b}(D)/(J_\phi(2\pi)^2)$ relative to $d\mu$.
The actual leaf has raw measure $d\nu_B$ and its embedded source
is supported on $D=0$. The hidden-Haar-smeared source associated
with (49.5) has density
$\phi(k)/(J_\phi(2\pi)^3)$ relative to $d\mu$.
At every finite $b$ these differ. In the raw regime the original
conditional source has width $r_s$ and law (32.11); its field
mass tends to zero and its total source charge is (32.12).
The common weak unscaled source limit does not identify its
response coefficient with either comparison in (49.3).
All these statements retain the original time, raw measures,
both absorbing faces, controls, covariance and preparations.
$\square$

**Proposition 49.2 (analytic memory, supplier hypotheses and scope).**
The defects in (44.5) decide failure of composition through the
original analytic amplitude boundary. The strict unit limiting
defect rules out a time-homogeneous semigroup on this boundary
with the same responses. Concatenating the same full evolutions
without intermediate erasure requires information distinguishing
the hidden components lost by $J^*$.
In the raw family the leading limit composes, while reproduction
through its first nonzero correction has the nonzero defect
$r_sD_s(t)+o(r_s)$ on the test (44.6). These conclusions assert
neither a minimal finite hidden-state realization nor a physical
projection, reset, preparation or acquisition procedure.

Proof. Put $\Pi=JJ^*$. The exact bounded compression identity of
[Free quotient, (5.3)] applies at each actual cutoff because the
full attractive operator is selfadjoint and semibounded:

$$
\mathcal D_{\sigma,\kappa}(t)
 =[(1-\Pi)e^{-tH_{\sigma,\kappa}}J]^*
       [(1-\Pi)e^{-tH_{\sigma,\kappa}}J].
\tag{49.7}
$$

Composing the projected response twice inserts $\Pi$ at the
intermediate time, and (49.7) measures the lost returning
component. Equations (46.9) and (47.3)--(47.4) evaluate it at the
original fixed positive times, rather than only near $t=0$.
They give the stated obstruction and its raw order. An extra
intermediate projection is a mathematical operation in this test;
no native actuator implementing it is supplied.

The analytic tools used here have the following precise roles.
Teschl's [author text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
Theorems 5.11 and 6.24, supplies the semibounded Trotter formula
and closed bounded-multiplier perturbations (relative form bound
zero). The original complete forms and common lower bounds are
specified in Definition 44.1. Scalar common operator domains in
(46.2) are the explicit Dirichlet domains, not an assertion about
an interior operator core. Theorem 6.31 of that text requires
strong resolvent convergence for its functional-calculus conclusion;
no such conclusion is inferred merely from convergence of interior
forms here. The direct native path estimates (46.4)--(46.8) and
(47.2) supply the required fixed-time convergence instead.

Arendt--Dier--Ouhabaz,
[arXiv:1303.1167v1, Theorem 2.2](https://arxiv.org/pdf/1303.1167v1),
requires projection to preserve the form domain and the stated
cross-form inequality for invariance of a closed convex set.
The free averaging in [G, §23] preserves the complete free form
domain, but that fact is no invariance assertion for the attractive
form. Its bounded hidden-dependent multiplier and the strict
native defects above preclude transferring free invariance to the
responses under study. The older [Observation quotient,
Theorem 6.1](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md)
has full dimension three, base dimension two and a strict
semiboundedness hypothesis. The nearby singular restricted result
in its Theorem 11.1 has its own small-coupling hypothesis.
Neither supplies the present four-coordinate full evolution or
its critical asymptotics. The fixed-pole strict-gap comparison
retains its separate stable singular-form contract as well.

Gouasmi--Parish--Duraisamy,
[arXiv:1611.06277v2, §2.1, (2.1)--(2.3)](https://arxiv.org/pdf/1611.06277v2),
distinguishes an instantaneous projected term, hidden initial data
and subsequent feedback. That finite-dimensional elimination
example explains the interpretation of an obstruction to
composition; it supplies no native coefficient, field error,
semigroup domain or complexity theorem. The concrete native
content here is (45.2)--(46.9), the all-base unit correspondence
(47.2), the strict tests and the actual-ground residue (48.1).
These are repository-derived applications of classical analytic
tools, with the published spectra and ground laws reused exactly;
no exhaustive novelty assertion is made.

Finally $J^*$ takes the normalized amplitude integral in (44.1);
it is not marginalization of $|f|^2$. The latter retains unit ground probability and has the
shrinking laws of §42, while the former has (48.1). Neither
operation specifies a physical interface. Three retained state
coordinates, hidden state capacity and physical spatial axes are
different assertions. The mathematical composition obstruction
gives no physical spatial selection, independent driver, reset,
finite-memory dimension, growing-time estimate, acquisition cost
or computational speedup. The statements are for the two original
critical families and fixed original parameters only; they include
no further parameter uniformity, sharp residue rate or general
norm-resolvent claim. $\square$

## 追加锚（本行以下为增补区）

## 50. Native coupling measures and the equivalence of hidden labels

**Definition 50.1 (the supplied limiting realization and its two measures).**
Retain all fixed data of Definitions 31.1, 36.1 and 44.1. In particular,
$s\in\mathbb R$, $b>0$ and $g>0$ are fixed, the clock is unchanged,
and $\mathscr H_B$ includes both visible circles and both absorbing
height faces. Write

$$
\begin{aligned}
K&=\mathcal K_0,& M&=M_\phi,& P&=\|\phi\|_\infty,\\
c_b(D)&=gc_0G_{\beta b}(D),& C_s&=gc_s,&
c_s^{\rm line}(x)&=C_s e^{-x^2/(4\beta)},\\
\alpha_b&=gc_0G_{\beta b}(\pi),&
C_b&=gc_0G_{\beta b}(0).
\end{aligned}
\tag{50.1}
$$

The new symbol $C_s$ is a coupling, not the small parameter
$a=|\kappa|$. The complete native fibre generator remains
$\mathcal K_c=K-cM$, with operator domain $D(K)$ and form domain
$\overline{\mathcal F}_0$. On the original raw-circle space
$\mathscr H=L^2(\mathbb T,dD;\mathscr H_B)$ define

$$
\begin{aligned}
H_\infty&=\int_{\mathbb T}^{\oplus}(K-c_b(D)M)\,dD,\\
D(H_\infty)&=\left\{f:f(D)\in D(K)\text{ a.e.},\quad
                    \int_{\mathbb T}\|Kf(D)\|^2dD<\infty\right\},\\
(Q_tf)&=J^*e^{-tH_\infty}f
       =\frac1{\sqrt{2\pi}}\int_{\mathbb T}
                         T_{c_b(D)}(t)f(D)\,dD.
\end{aligned}
\tag{50.2}
$$

Here $J$ is exactly (44.1), and $Q_t:\mathscr H\to\mathscr H_B$.
The bounded multiplier in (50.2) leaves the displayed completed
operator domain unchanged; $H_\infty\ge\lambda-C_bP$. Its form
domain is the corresponding square-integrable direct integral of
$\overline{\mathcal F}_0$, with the free form integrable. Thus
$e^{-tH_\infty}$ is the direct integral of the complete $T_c(t)$,
and $Q_tJ=B_b(t)$. This is the supplied limit in (47.2).

Let $\mu_b$ be the pushforward of $dD/(2\pi)$ by $c_b$, and let
$\nu_s$ be the pushforward of $dx/(2\pi)$ by $c_s^{\rm line}$.
The second measure is defined on $(0,C_s]$, has infinite total mass,
and is used only with compensation or an integrable positive power
of $c$. Define the finite measure $\eta_s$ by
$d\eta_s(c)=c\,d\nu_s(c)$. The original responses are exactly

$$
B_b(t)=\int T_c(t)\,d\mu_b(c),\qquad
A_s(t)=\int [T_c(t)-S_t]\,d\nu_s(c).
\tag{50.3}
$$

**Theorem 50.2 (native label equivalence and full support).**
For every finite $b>0$,
$0<\alpha_b<C_b$, and $c_b$ is strictly decreasing as a function
of $\rho(D)\in[0,\pi]$. Consequently the precise equivalence of
the native hidden labels, in terms of their complete fibre responses,
is

$$
\begin{aligned}
T_{c_b(D)}(t)h=T_{c_b(E)}(t)h
 \quad\text{for every }t\ge0,\ h\in\mathscr H_B
\quad\Longleftrightarrow\quad
c_b(D)=c_b(E)
\quad\Longleftrightarrow\quad E=D\text{ or }E=-D\pmod{2\pi}.
\end{aligned}
\tag{50.4}
$$

The probability measure $\mu_b$ is atomless and has full support
$[\alpha_b,C_b]$. The measures on the raw side have densities

$$
d\nu_s(c)=\frac{\sqrt\beta}{\pi c\sqrt{\log(C_s/c)}}\,dc,
\qquad
d\eta_s(c)=\frac{\sqrt\beta}{\pi\sqrt{\log(C_s/c)}}\,dc
\quad(0<c<C_s).
\tag{50.5}
$$

Both have full support up to the endpoint zero, with no atom there
when $\eta_s$ is regarded as a measure on $[0,C_s]$. Their relevant
moments, including the raw factors, are

$$
\begin{aligned}
m_j^b&=\int c^j\,d\mu_b(c)
 =\frac{(gc_0)^j}{2\pi}\int_{\mathbb T}G_{\beta b}(D)^j\,dD
 \quad(j\ge0),& m_0^b&=1,\\
m_j^s&=\int c^j\,d\nu_s(c)
 =\sqrt{\frac\beta\pi}\frac{C_s^j}{\sqrt j}
 \quad(j\ge1),&
\int c^r\,d\eta_s(c)&=m_{r+1}^s\quad(r\ge0).
\end{aligned}
\tag{50.6}
$$

Proof. The heat-kernel monotonicity is classical: see
Alonso-Orán--Chamizo--Martínez--Mas, *Pointwise monotonicity of
heat kernels*, [arXiv:1807.11072v2, Theorem 1.1 and §2,
pp.1,4--5](https://arxiv.org/pdf/1807.11072v2).
The native correspondence is the unit circle with arclength
$dD$, Laplacian $\partial_D^2$, circumference $2\pi$ and time
$\beta b$; no rescaling of its period or density is involved.
Here its strict form can also be checked directly. Put
$f_N(D)=e^{N\cos D}/\int_{\mathbb T}e^{N\cos E}\,dE$.
It is even and its derivative is negative on $(0,\pi)$.
The derivative of $G_t*f_N$ solves the Dirichlet heat equation
on $(0,\pi)$, with nonpositive initial data, because evenness and
periodicity give derivative zero at both endpoints. The parabolic
maximum principle makes this derivative nonpositive for $t>0$.
The measures $f_NdD$ tend to the unit point mass at zero; convolution
therefore converges with every derivative to $G_t$ for fixed $t>0$.
It follows that $w(t,D)=\partial_DG_t(D)\le0$ on $(0,\pi)$.
It is not identically zero at any positive time: the Fourier
coefficient of $\sin D$ in $w$ is $-e^{-t}/\pi$.
Applying the strict maximum principle to $w$ between times $t/2$
and $t$ gives $w(t,D)<0$ throughout the open interval. Positivity
of $G_t$ follows also from its positive periodized Gaussian (32.8).
These classical heat-equation steps establish precisely the
monotonicity needed here, including every finite $\beta b>0$.

If two fibre semigroups agree on every input for all nonnegative
times, their generators agree on $D(K)$. Their difference is
$(c_b(E)-c_b(D))M$. Since $\phi>0$ almost everywhere on $I$,
$M$ is injective, so the couplings agree. Conversely equal
couplings give the same operator and domain. Strict radial
monotonicity gives the last equivalence in (50.4). This is a
statement about fibre operators, not the assertion that a delta
amplitude at an individual hidden label belongs to $\mathscr H$.

Each nonempty open subinterval of $[\alpha_b,C_b]$ has a hidden
preimage of positive raw length, while a singleton has at most two
preimages. This proves full support and absence of atoms. More
explicitly, on the interior the density is
$1/(\pi|c_b'(\rho(c))|)$, where $\rho(c)$ is the inverse on
$(0,\pi)$; it is integrable at the endpoints because it is a
pushforward of $d\rho/\pi$.

On the raw line, use the two signs of
$x=2\sqrt\beta\sqrt{\log(C_s/c)}$ and the original factor
$1/(2\pi)$. This gives (50.5). The divergence of
$\int d\nu_s$ is also immediate from the infinite length of
$\mathbb R$; it is not a probability measure. Direct Gaussian
integration gives
$\int (C_s e^{-x^2/(4\beta)})^j dx/(2\pi)
=C_s^j\sqrt{\beta/\pi}/\sqrt j$ for $j\ge1$.
The circle formula is the definition of pushforward. This proves
all moment and support assertions. $\square$

## 51. All-amplitude invisibility and the minimal supplied boundary

**Theorem 51.1 (the exact invisible space).**
For arbitrary full amplitudes, define

$$
\begin{aligned}
\mathscr N&=\bigcap_{t\ge0}\ker Q_t,\\
\mathscr C&=\overline{\operatorname{span}}
       \{e^{-tH_\infty}Jh:t\ge0,\ h\in\mathscr H_B\}.
\end{aligned}
\tag{51.1}
$$

Then, with equalities of amplitudes understood almost everywhere,

$$
\begin{aligned}
\mathscr C&=\mathscr N^\perp
 =\{f\in\mathscr H:f(D)=f(-D)\},\\
\mathscr N&=\{f\in\mathscr H:f(D)=-f(-D)\}.
\end{aligned}
\tag{51.2}
$$

In particular, for any $f_1,f_2\in\mathscr H$,

$$
Q_tf_1=Q_tf_2\text{ for every }t\ge0
\quad\Longleftrightarrow\quad
f_1(D)+f_1(-D)=f_2(D)+f_2(-D)\text{ a.e.}
\tag{51.3}
$$

Proof. Selfadjointness gives
$\langle Q_tf,h\rangle=\langle f,e^{-tH_\infty}Jh\rangle$;
thus $\mathscr N=\mathscr C^\perp$. Reflection in $D$ commutes
with $H_\infty$, and $Jh$ is even, so $\mathscr C$ is contained
in the even subspace. It remains to prove the converse; mere
separation of the scalar labels would not suffice for arbitrary
$\mathscr H_B$-valued amplitudes.

Every bounded selfadjoint $e^{-uH_\infty}$ preserves $\mathscr C$
by its semigroup law, and therefore also preserves
$\mathscr C^\perp$. For $v\in\mathscr C\cap D(H_\infty)$,
the strong generator difference quotient shows
$H_\infty v\in\mathscr C$. In particular, for $h\in D(K)$,

$$
H_\infty Jh=JKh-c_bJMh.
\tag{51.4}
$$

Both $Jh$ and $JKh$ are in $\mathscr C$, hence so is $c_bJMh$.
The set $M D(K)$ is dense in $\mathscr H_B$: $D(K)$ is dense,
$M$ is bounded, and $\overline{\operatorname{Ran}M}=\mathscr H_B$
because $M=M^*$ and $\ker M=0$. Boundedness of $c_b$ now implies
$c_bJh\in\mathscr C$ for every $h\in\mathscr H_B$.

Inductively, suppose $c_b^rJh\in\mathscr C$ for every base $h$.
For $h\in D(K)$ this vector belongs to the exact domain (50.2),
and

$$
H_\infty(c_b^rJh)=c_b^rJKh-c_b^{r+1}JMh.
\tag{51.5}
$$

The same density argument gives $c_b^{r+1}J\mathscr H_B
\subset\mathscr C$. Thus all vector-valued coupling polynomials
belong to $\mathscr C$. By Theorem 50.2, every measurable even
function of $D$ is a measurable function of $c_b(D)$, up to null
sets. Polynomials are dense in $L^2(\mu_b)$: continuous functions
are dense for this finite compactly supported measure, and the
Weierstrass theorem approximates continuous functions uniformly.
Finite sums of scalar functions times base vectors are dense in
the vector-valued $L^2$ space. Hence the coupling polynomials
are dense in the entire even subspace. This proves (51.2), and
applying it to $f_1-f_2$ proves (51.3).

No bounded inverse of $M$ was used; $\phi$ vanishes at the height
faces. Nor was an interior test space asserted to be an operator
core. Equations (51.4)--(51.5) use the full operator domain.
The spectral and reducing-subspace principles used here are the
classical ones in Teschl's
[author text, §3.1, (3.30)--(3.37) and Theorem 3.7,
printed pp.93--96](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
The identification of their generated subspace with the native
even amplitudes is the additional correspondence proved above.
$\square$

**Theorem 51.2 (minimal realization and boundary-fixing uniqueness).**
On $\widehat{\mathscr H}_b=L^2(\mu_b;\mathscr H_B)$ put

$$
\begin{aligned}
(\widehat H_bv)(c)&=(K-cM)v(c),& (\widehat Jh)(c)&=h,\\
D(\widehat H_b)&=\left\{v:v(c)\in D(K)\text{ a.e.},\quad
                    \int\|Kv(c)\|^2d\mu_b(c)<\infty\right\},\\
(Uv)(D)&=(2\pi)^{-1/2}v(c_b(D)).
\end{aligned}
\tag{51.6}
$$

Then $U$ is unitary from $\widehat{\mathscr H}_b$ onto
$\mathscr C$, $U\widehat J=J$, and it intertwines the generators
with their domains. The semibounded selfadjoint realization
$(\widehat{\mathscr H}_b,\widehat H_b,\widehat J)$ is minimal:
the closed span of $e^{-t\widehat H_b}\widehat J\mathscr H_B$
is its whole Hilbert space. Its compressed response is $B_b(t)$.
For every $v\in\widehat{\mathscr H}_b$ its actual full-input
readout is

$$
Q_tUv=\widehat J^*e^{-t\widehat H_b}v
     =\int T_c(t)v(c)\,d\mu_b(c).
$$

Within the category of semibounded selfadjoint generators with a
specified isometric boundary copy of $\mathscr H_B$, any two
minimal realizations of this same response are related by a
unique unitary that fixes that boundary and intertwines the
generators. Every such realization has a reducing boundary-cyclic
part with this minimal realization; an orthogonal invisible
summand is not determined by the compressed response.

Proof. The pushforward definition proves
$\|Uv\|_{\mathscr H}^2=\int\|v(c)\|^2d\mu_b(c)$, with precisely
the raw factor in (51.6). Theorem 50.2 and (51.2) prove that its
range is $\mathscr C$. The displayed domains and pointwise action
give the intertwining, including domain equality. Minimality and
the response formula follow from Theorem 51.1 and (50.3).
Substitution of $Uv$ in (50.2), with both factors
$(2\pi)^{-1/2}$, gives the stated full-input readout.

For completeness, let $(\mathscr L_i,A_i,I_i)$, $i=1,2$, be two
minimal triples in the declared category, with
$I_i^*e^{-tA_i}I_i=B_b(t)$. On their algebraic cyclic spans send

$$
\sum_j e^{-t_jA_1}I_1h_j
 \longmapsto\sum_j e^{-t_jA_2}I_2h_j.
\tag{51.7}
$$

The squared norm of either side is the same sum of inner products
with $B_b(t_j+t_k)$, since each $A_i$ is selfadjoint. Thus the map
is well defined and isometric. Minimality makes its extension
unitary and makes that extension unique. Increasing every $t_j$
by $u\ge0$ shows that it intertwines the semigroups; strong
generator difference quotients then give intertwining of the
generators and their domains. Taking $t_j=0$ gives boundary fixing.
For a nonminimal triple its closed cyclic span reduces the
semigroup, as in the proof of Theorem 51.1, and the same argument
applies there. An orthogonal reducing summand with zero boundary
overlap makes no contribution to $B_b$.

This uniqueness is a selfadjoint supplied-boundary assertion.
It does not minimize branches over arbitrary latent generators,
identify raw compensated $A_s$ with a normalized realization, or
give a physical hidden-state dimension. $\square$

## 52. All-order differentiation with the native noncommuting factors

**Theorem 52.1 (a common domain and the exact moment criterion).**
Let $\mathscr D$ consist of finite sums

$$
h(k,\theta,v)=\frac1{2\pi}\sum_{(n,m)\in E}
                     h_{nm}(k)e^{i(n\theta+mv)},
\qquad E\subset\mathbb Z^2\text{ finite},\quad
h_{nm}\in C_c^\infty(I).
\tag{52.1}
$$

This is dense in the whole base Hilbert space and is contained in
$D(\mathcal K_c^r)$ for every finite $c\ge0$ and every integer
$r\ge0$. For every such $h$, the functions $T_c(t)h$, $B_b(t)h$
and $A_s(t)h$ have strong right derivatives of every order at
$t=0$, as well as continuous strong derivatives on $[0,\infty)$.

For a finite positive UNIT list and a finite positive RAW list write

$$
\begin{aligned}
B^{[n]}(t)&=\sum_{i=1}^nw_iT_{c_i}(t),&
w_i&\ge0,\quad\sum_iw_i=1,\quad c_i\ge0,\\
A^{[n]}(t)&=\sum_{i=1}^na_i[T_{d_i}(t)-S_t],&
a_i&\ge0,\quad d_i\ge0,
\end{aligned}
\tag{52.2}
$$

where every coefficient and coupling is finite. For every integer
$q\ge0$, agreement of derivatives of orders $0,\ldots,q$ at
zero on every input in $\mathscr D$ is equivalent respectively to

$$
\sum_iw_ic_i^j=m_j^b\quad(0\le j\le q),
\qquad
\sum_i a_i d_i^j=m_j^s\quad(1\le j\le q).
\tag{52.3}
$$

The RAW condition for $q=0$ is empty. No normalization of
$\sum_i a_i$ occurs.

Proof. In each fixed angular mode the action of $K$ is exactly
(36.1) at $c=0$, a second-order height differential expression
with smooth polynomial potential. It maps $C_c^\infty(I)$ to
itself. Multiplication by the smooth $\phi$ has the same property,
without changing angular modes or enlarging the height support.
The explicit Dirichlet operator domain in (36.1) contains these
functions. Consequently $\mathcal K_c\mathscr D\subset\mathscr D$,
and induction proves membership in every generator-power domain.
Density follows from finite Fourier truncation and the density of
$C_c^\infty(I)$ in height $L^2$. This is a dense invariant test
domain for powers, not a claim that density makes it an operator
core for the Dirichlet generator. In particular no all-order
domain claim about the distinct vector $h_*$ of (44.6) is needed.

Put $L=-K$. On $\mathscr D$, for $r\ge0$,

$$
(L+cM)^r h=\sum_{j=0}^r c^j W_{r,j}h,
\qquad W_{r,0}=L^r,\quad W_{r,r}=M^r.
\tag{52.4}
$$

Here $W_{r,j}$ is the sum of all ordered words of length $r$
with $j$ factors $M$ and $r-j$ factors $L$, each word in its
actual order of action. This follows by ordinary multiplication
and induction on $r$ on the invariant domain; it is not a
commutative binomial formula. The spectral theorem gives
$\partial_t^rT_c(t)h=T_c(t)(L+cM)^rh$ continuously down to zero.
For $c$ in a compact interval these derivatives are bounded
uniformly on any fixed time interval, because (52.4) is a finite
vector-valued polynomial and $\|T_c(t)\|\le e^{cPt}$.
Thus differentiation under the finite measure $\mu_b$ is justified.

For the infinite raw measure one needs the compensation also
after differentiation. For fixed $r,h,T$, (52.4) shows
$\|[(L+cM)^r-L^r]h\|\le C_{r,h}c$ for $0\le c\le C_s$.
The exact identity

$$
\begin{aligned}
\partial_t^r[T_c(t)-S_t]h
 &=[T_c(t)-S_t]L^rh
   +T_c(t)[(L+cM)^r-L^r]h
\end{aligned}
\tag{52.5}
$$

and (44.4) therefore bound this derivative by $C_{r,h,T}c$
uniformly on $[0,T]$. This is integrable against $\nu_s$ by
(50.6). Dominated strong integration, applied successively to
these continuous derivatives (or to their integral fundamental
theorem), proves every asserted derivative of $A_s(t)h$.
At zero their values are consequently

$$
\begin{aligned}
\partial_t^rB_b(0)h&=\sum_{j=0}^r m_j^bW_{r,j}h,\\
\partial_t^rA_s(0)h&=\sum_{j=1}^r m_j^sW_{r,j}h.
\end{aligned}
\tag{52.6}
$$

The empty second sum is zero. Formula (52.6) for the finite
lists holds with their finite moments, also when a coupling or
coefficient is zero. It proves sufficiency in (52.3).
For necessity, argue successively in $r$. Once the lower moments
agree, the difference of the derivatives of order $r$ is exactly
the difference of the $r$th moments times $M^rh$. For every
$r\ge1$, $M^r$ is injective, hence is nonzero on any nonzero
$h\in\mathscr D$. Equality for all such $h$ forces that moment
to agree. In UNIT the zeroth moments already agree by the required
normalization; in RAW both zeroth responses vanish. This proves
necessity for every $q$, without a visible-mode restriction and
without commuting any factors. $\square$

## 53. Sharp native branch budgets and impossibility of exact finite lists

**Theorem 53.1 (the sharp orders for every branch budget).**
For each positive integer $n$, among all lists (52.2), the greatest
integer $q$ for matching initial derivatives through order $q$ on
every input in $\mathscr D$ is

$$
q_{\rm UNIT}(n)=2n-1,\qquad q_{\rm RAW}(n)=2n.
\tag{53.1}
$$

Both are attained with $n$ strictly positive weights and $n$
distinct couplings in the interior of their original compact
native ranges. The same attaining lists will be used in §54.
Neither $B_b(t)$ nor $A_s(t)$ equals a finite positive list in
its respective class for all $t\ge0$ as operators on the entire
$\mathscr H_B$.

Proof. Apply positive Gaussian quadrature to $\mu_b$ on
$[\alpha_b,C_b]$ and to $\eta_s$ on $[0,C_s]$.
Its classical content is the quadrature theorem stated in
Golub--Welsch, *Calculation of Gauss Quadrature Rules*,
*Math. Comp.* **23** (1969), §1, pp.221--222, with the
Jacobi-matrix correspondence in §2, (2.1)--(2.6), pp.222--223
([primary article](https://www.ams.org/journals/mcom/1969-23-106/S0025-5718-69-99647-1/S0025-5718-69-99647-1.pdf),
[public copy](https://web.stanford.edu/class/cme335/S0025-5718-69-99647-1.pdf)).
The positive compact moment setting is also the one in
Schmüdgen, *Ten Lectures on the Moment Problem*,
[arXiv:2008.12698v1, Theorem 1.16 and the opening of Lecture 2,
pp.16--17](https://arxiv.org/pdf/2008.12698v1).
Neither supplier identifies our native measure or our operator
derivatives; those are (50.5)--(50.6) and Theorem 52.1.

Here is the quadrature step explicitly for these measures. For
either finite measure $\sigma$, every nonzero polynomial has
strictly positive squared integral, by full interval support.
Thus its monic orthogonal polynomial $p_n$ of degree $n$ exists
by the positive-definite polynomial Gram matrix. It has $n$
simple roots in the interior of the interval. To verify this last
fact, let $q$ be the product of its distinct interior roots where
its sign changes. If there were fewer than $n$, then $\deg q<n$
and $p_nq$ would have a constant nonzero sign except at finitely
many points on the interval: every remaining interior root has
even multiplicity, and exterior or nonreal factors cannot change
the sign there. Its integral would be nonzero, contradicting
orthogonality to $q$. There must therefore be $n$ interior
sign-changing roots, all simple, exhausting the degree.

Write the roots as $z_1,\ldots,z_n$, let $\ell_i$ be their
degree-$(n-1)$ Lagrange polynomials, and put
$v_i=\int\ell_i\,d\sigma$. Polynomial division by $p_n$ gives

$$
\int f\,d\sigma=\sum_{i=1}^nv_if(z_i)
\qquad(\deg f\le2n-1).
\tag{53.2}
$$

Indeed the quotient has degree at most $n-1$, so its product
with $p_n$ integrates to zero, while the remainder is interpolated
by the $\ell_i$. Applying (53.2) to $\ell_i^2$ gives
$v_i=\int\ell_i^2d\sigma>0$, and applying it to $1$ gives the
total mass. This proves the required existence, location,
positivity and exactness as intermediate classical facts.

For $\sigma=\mu_b$, denote the nodes and weights by
$c_{b,i}^{(n)},w_{b,i}^{(n)}$. They are a valid UNIT list,
including $\sum_iw_{b,i}^{(n)}=1$, and match $m_j^b$ through
$j=2n-1$. For $\sigma=\eta_s$, denote them by
$d_{s,i}^{(n)},v_{s,i}^{(n)}$. All these nodes are strictly
between $0$ and $C_s$. Set

$$
a_{s,i}^{(n)}=\frac{v_{s,i}^{(n)}}{d_{s,i}^{(n)}}>0.
\tag{53.3}
$$

These are finite for each fixed $n$, with no requirement on
their sum. For $1\le j\le2n$,

$$
\sum_i a_{s,i}^{(n)}(d_{s,i}^{(n)})^j
 =\sum_i v_{s,i}^{(n)}(d_{s,i}^{(n)})^{j-1}
 =\int c^{j-1}d\eta_s(c)=m_j^s.
\tag{53.4}
$$

Theorem 52.1 proves attainment of both orders on every input
in the common all-power domain, not just in a scalar sector.
Every constructed node is an actual native fibre: the UNIT node
is $c_b(\rho_i)$ for its unique $\rho_i\in(0,\pi)$, and the RAW
node is $c_s^{\rm line}(x_i)$ with
$x_i=2\sqrt\beta\sqrt{\log(C_s/d_{s,i}^{(n)})}$.
For example, at budget one the two lists are explicitly

$$
B_1(t)=T_{gc_0/(2\pi)}(t),\qquad
A_1(t)=\sqrt{\frac{2\beta}{\pi}}
                   [T_{C_s/\sqrt2}(t)-S_t].
\tag{53.5}
$$

Indeed a one-node quadrature node is the first moment divided
by the total mass of its finite measure; (50.6) gives both
nodes and weights displayed here.

For the upper bounds retain the entire declared competitor class.
Given a UNIT list, let $z_1,\ldots,z_r$ be the distinct couplings
with positive total weight, where $1\le r\le n$. They may lie
anywhere in $[0,\infty)$. The polynomial
$p(c)=\prod_{i=1}^r(c-z_i)$ satisfies

$$
\sum_i w_i p(c_i)^2=0,
\qquad \int p(c)^2d\mu_b(c)>0.
\tag{53.6}
$$

The second inequality follows from full interval support,
regardless of the locations of the finitely many zeros.
Matching through derivative $2n$ would match every moment of
the polynomial $p^2$, whose degree is $2r\le2n$, contrary to
(53.6).

For a RAW list, discard only for this argument the terms with
$a_i=0$ or $d_i=0$, and merge the remaining repeated positive
couplings to $z_1,\ldots,z_r$, where $0\le r\le n$.
This does not restrict the competitors or change their response.
Put $p(c)=\prod_{i=1}^r(c-z_i)$, with $p=1$ when $r=0$.
Then

$$
\sum_i a_i d_i p(d_i)^2=0,
\qquad
\int c p(c)^2d\nu_s(c)=\int p(c)^2d\eta_s(c)>0.
\tag{53.7}
$$

The polynomial $cp^2$ has zero constant term and degree
$2r+1\le2n+1$, so all its integrals are finite even though
$\nu_s$ has infinite mass. Matching derivatives through
$2n+1$ would contradict (53.7) by Theorem 52.1. This covers
zero, repeated and redundant branches, including a list whose
response is identically zero. In particular redundancy cannot
improve the maximum in either family. It also shows that at an
attaining order all $n$ branches must be effective and distinct.

Finally equality for all times on the whole base implies equality
of every derivative on $\mathscr D$, by Theorem 52.1. For any
fixed finite list this contradicts (53.6) or (53.7). Thus the
finite-list exact-realization decisions are negative for both
original families, for every fixed original $s,b,g$.
The obstruction concerns complete native semigroups and uses
their noncommuting derivatives; it does not substitute scalar
exponentials for them. $\square$

## 54. The attaining lists also approximate in operator norm

**Theorem 54.1 (explicit finite-horizon bounds with raw compensation).**
Use exactly the quadrature lists of Theorem 53.1 and write

$$
\begin{aligned}
B_n(t)&=\sum_{i=1}^nw_{b,i}^{(n)}T_{c_{b,i}^{(n)}}(t),\\
A_n(t)&=\sum_{i=1}^na_{s,i}^{(n)}
                           [T_{d_{s,i}^{(n)}}(t)-S_t],\\
R_N(z)&=\sum_{j=N}^\infty\frac{z^j}{j!}\quad(z\ge0),&
M_s&=m_1^s=C_s\sqrt{\beta/\pi}.
\end{aligned}
\tag{54.1}
$$

For every fixed $0\le T<\infty$ the following computable errors are
valid in operator norm on the entire base, uniformly for
$0\le t\le T$:

$$
\begin{aligned}
\|B_b(t)-B_n(t)\|&\le E_{b,n}(T)
 :=2R_{2n}(C_bPT)
 \le2e^{C_bPT}\frac{(C_bPT)^{2n}}{(2n)!},\\
\|A_s(t)-A_n(t)\|&\le E_{s,n}(T)
 :=\frac{2M_s}{C_s}R_{2n+1}(C_sPT)
 \le\frac{2M_s}{C_s}e^{C_sPT}
                    \frac{(C_sPT)^{2n+1}}{(2n+1)!}.
\end{aligned}
\tag{54.2}
$$

Both tend to zero as $n\to\infty$. The coefficients and nodes
are determined by the finite positive moment matrices (50.6)
and the orthogonal polynomials in the proof of Theorem 53.1;
the bounds require no estimate on their smallest node or on
$\sum_i a_{s,i}^{(n)}$.

Proof. Since $K\ge\lambda>0$, $\|S_t\|\le1$.
Define ordered operator integrals on base inputs by

$$
U_0(t)=S_t,\qquad
U_j(t)=\int_0^tS_{t-u}M U_{j-1}(u)\,du\quad(j\ge1).
\tag{54.3}
$$

These are strong operator integrals and
$\|U_j(t)\|\le (Pt)^j/j!$ by induction. Bounded-perturbation
Duhamel expansion gives the norm-convergent series

$$
T_c(t)=\sum_{j=0}^\infty c^jU_j(t),\qquad
T_c(t)-S_t=\sum_{j=1}^\infty c^jU_j(t).
\tag{54.4}
$$

To justify the formula without any commutativity assumption,
differentiate $S_{t-u}T_c(u)h$ for $h\in D(K)$.
The common operator domain $D(K-cM)=D(K)$ gives derivative
$cS_{t-u}MT_c(u)h$; the factors have their displayed order.
Integration and density give the Duhamel identity on the whole
base. Iteration gives (54.4), because its $N$th remainder is
bounded by $e^{cPt}(cPt)^{N+1}/(N+1)!$ on bounded time and
coupling intervals. Equivalently the absolutely norm-convergent
series solves that Volterra equation uniquely by iteration.
This is the classical ordered bounded-perturbation expansion.
The selfadjoint common-domain input is Teschl's
[Theorem 6.4, printed p.135](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf):
the real bounded $-cM$ has relative operator bound zero.
The native series (54.3) retains the full $K$ of (36.1).

Integrating (54.4) against $\mu_b$ and subtracting the UNIT
list cancels all terms through $j=2n-1$. Every later moment
of either positive measure is at most $C_b^j$, since both are
probabilities supported in $[\alpha_b,C_b]$. The norm of the
remaining difference is at most
$2\sum_{j\ge2n}(C_bPt)^j/j!$, proving the first bound.

On the raw side compensation removes the $j=0$ term before
integration. For $j\ge1$,

$$
m_j^s\le M_s C_s^{j-1},\qquad
\sum_i a_{s,i}^{(n)}(d_{s,i}^{(n)})^j
 =\sum_i v_{s,i}^{(n)}(d_{s,i}^{(n)})^{j-1}
 \le M_s C_s^{j-1}.
\tag{54.5}
$$

The first estimate integrates $c^{j-1}$ against the finite
$\eta_s$; the second uses its same total mass and its same
compact range. Thus the sum of integrated norms in (54.4),
starting at $j=1$, is finite. This proves termwise integration
against the original infinite $\nu_s$ and controls its entire
tail towards $c=0$, rather than deleting a segment of the
hidden line. The moments through $2n$ cancel by (53.4), leaving
at most
$2M_s C_s^{-1}\sum_{j\ge2n+1}(C_sPt)^j/j!$.
This proves the second bound with the original raw normalization.

Finally $R_N(z)\le e^z z^N/N!$, as is seen by comparing
$(N+k)!$ with $N!k!$ in the series. For fixed $z$ this tends
to zero, proving all convergence assertions. All bounds are
operator bounds, so no restriction on the input or on visible
Fourier modes is present. Strong derivatives on $\mathscr D$
in §52 are not being replaced by operator-norm differentiability
of the unbounded-generator semigroups at zero. $\square$

**Theorem 54.2 (both composition corrections from the same lists).**
With precisely the lists in (54.1), define

$$
\begin{aligned}
V_n(t)&=B_n(2t)-B_n(t)^2\\
 &=\sum_iw_{b,i}^{(n)}
          [T_{c_{b,i}^{(n)}}(t)-B_n(t)]^2\ge0,\\
D_n(t)&=A_n(2t)-S_tA_n(t)-A_n(t)S_t\\
 &=\sum_i a_{s,i}^{(n)}
          [T_{d_{s,i}^{(n)}}(t)-S_t]^2\ge0.
\end{aligned}
\tag{54.6}
$$

For every fixed $0\le T<\infty$, uniformly for $0\le t\le T$,

$$
\begin{aligned}
\|V_b(t)-V_n(t)\|
 &\le E_{b,n}(2T)+2e^{C_bPT}E_{b,n}(T),\\
\|D_s(t)-D_n(t)\|
 &\le E_{s,n}(2T)+2E_{s,n}(T).
\end{aligned}
\tag{54.7}
$$

In particular both errors tend to zero in operator norm. The
RAW expression approximates the original first-order $D_s$
of (46.9), not $A_s(2t)-A_s(t)^2$.

Proof. Each individual $T_c(t)$ is selfadjoint and obeys its
own semigroup law. Expanding the UNIT square sum and using
$\sum_iw_iT_{c_i}(t)=B_n(t)$ and $\sum_iw_i=1$ gives
$\sum_iw_iT_{c_i}(t)^2-B_n(t)^2$; no two distinct fibres have
been commuted. This proves the first identity and positivity.
For the second identity put $T=T_{d_i}(t)$ and $S=S_t$.
The contribution of a single branch to its first line is

$$
(T^2-S^2)-S(T-S)-(T-S)S
 =T^2-ST-TS+S^2=(T-S)^2.
\tag{54.8}
$$

This uses both cross orders, and proves positivity after the
positive weighted sum. The same calculation under the
compensated integral is exactly (46.9).

Both $B_n(t)$ and $B_b(t)$ have norm at most $e^{C_bPt}$.
The identity $X^2-Y^2=X(X-Y)+(X-Y)Y$ therefore bounds the
difference of their squares by
$2e^{C_bPT}E_{b,n}(T)$, and their responses at $2t$ differ by
at most $E_{b,n}(2T)$. This proves the first inequality in
(54.7). Subtract the two cross expressions for $D_s$ and
$D_n$, and use $\|S_t\|\le1$, to obtain the second.

One may also see the first-order meaning directly: if a
bookkeeping scalar $r$ is used in $S_t+rA_n(t)$, its equal-step
composition difference is $rD_n(t)-r^2A_n(t)^2$.
Only its coefficient of $r$ is the raw correction. The
compensated bound
$\|A_n(t)\|\le M_sPt\,e^{C_sPt}$ follows from (54.4)--(54.5),
so this expansion introduces no divergent total-weight term.
The scalar $r$ here does not assert any new finite-$\kappa$
error estimate or replace the inherited scale $r_s$. $\square$

## 55. Predictive distinctions and the scope of the branch count

**Proposition 55.1 (what the native finite inquiry determines).**
The all-time equivalence of arbitrary UNIT full amplitudes is
(51.3); its minimal selfadjoint supplied-boundary representative
is (51.6). Boundary-prepared responses on all base inputs have
the finite-list obstructions, sharp derivative orders and
attaining approximations of §§52--54. These are different input
quantifiers. The necessary native label distinctions are coupling
distinctions, with exactly the reflection equivalence (50.4).
The budget $n$ counts complete $\mathscr H_B$-amplitude branches
in (52.2), and gives neither a physical spatial dimension nor
a memory-bit or scalar-state count.

Proof. A general $f\in\mathscr H$ is read by $Q_t$ in (50.2),
whereas a boundary-prepared input has the special form $Jh$
and response $Q_tJh=B_b(t)h$. The former allows arbitrary even
and odd amplitudes; the latter fixes the hidden profile before
evolution. Theorem 51.1 determines the former equivalence and
Theorem 51.2 removes exactly its invisible reducing summand.
Theorem 53.1 excludes exact finite positive native lists for
the latter response, while Theorems 54.1--54.2 approximate it
and the original compensated raw coefficients by the same
attaining lists. Every branch still contains all base modes,
and its base generator has both original absorbing faces.
In particular none of these theorems replaces a branch by a
number, a bit, an axis, or a commuting height-only model.

The raw response has no zeroth moment and no normalized hidden
probability in (50.3); its extra matching order comes from the
finite weighted measure $c\,d\nu_s$, not from an additional
spatial direction. The standard spectral, moment and quadrature
facts credited above are intermediate suppliers. The native
content is their verified correspondence with $K-cM$, the
actual $J^*e^{-tH_\infty}$, the two different raw measures and
their ordered response coefficients. No worldwide novelty
claim follows from that correspondence.

All statements are pointwise in the original fixed $s\in\mathbb R$,
$b>0$, $g>0$ and model data. The two signs of $\kappa$ retain
their already proved limits in §§44--49; nothing here asserts
new finite-$\kappa$ observability or norm-error transfer.
The approximation bounds concern fixed finite horizons, not
optimal uniform rates or growing horizons. The supplied
analytic boundary entails no physical amplitude acquisition,
projection actuator, reset, new driver, $SO(3)$ law, actual-ground
residue rate, spatial selection or computational speedup.
$\square$

## 追加锚（本行以下为增补区）

## 56. Actual ground amplitudes on the independent harmonic length

**Definition 56.1 (the unchanged families and boundary directions).**
Keep Definitions 31.1, 38.1, 38.2 and 44.1, including the actual
completed domains, both signs, all fixed data, raw measures and original
periods. In this section abbreviate

$$
\begin{gathered}
\mathcal H=H_{\sigma,\kappa},\quad W=W_{\sigma,\kappa},\quad
\widehat{\mathcal H}=L_\kappa-gM_{U_\kappa},\quad
h=h_{\sigma,\kappa},\quad d=d_{\sigma,\kappa},\quad
\ell=d\sqrt h,\quad w=\alpha_\sigma\ell,\quad
\alpha_\sigma=(\mathcal B_\sigma/\mathcal C_\sigma)^{1/4},\\
\eta_\sigma(k,\theta,v)=\frac{u_{c_\sigma}(k)}{2\pi},\quad
\Pi_\sigma=|\eta_\sigma\rangle\langle\eta_\sigma|,\quad
\delta_\kappa=g\|W-U_\kappa\|_\infty=o(h),\\
K_\kappa=H_\kappa^{\rm ht}-\xi_\kappa\ge0,\qquad
m_h(y)=\min\{y^2,h^{-1}\},\quad |y|\le\pi/\ell.
\end{gathered}
\tag{56.1}
$$

Here $W_{{\rm raw},\kappa}=V_{\kappa,\tau_s}$ and
$W_{{\rm unit},\kappa}=V_{\kappa,\tau_b}/S(\tau_b)$ are the actual
fields. The vector $\eta_\sigma$ has norm one on the entire original base.
Constants in the proofs may depend on the fixed original data and the
family, but not on the sign or small magnitude of $\kappa$.

**Lemma 56.2 (a full-form barrier and amplitude tails).**
There are $c>0$, $\epsilon_0>0$ and $C<\infty$ such that the following
statements hold for all sufficiently small nonzero parameters.
For $f$ in the original completed form domain,

$$
\begin{aligned}
\mathfrak q_{\mathcal H}[f]-\xi_\kappa\|f\|^2+\delta_\kappa\|f\|^2
\ge{}&\frac12\int_{\mathbb T^3}
             \langle f,K_\kappa f\rangle_{L^2(I)}\,d\theta\,dv\,dD\\
 &+\|Q_\kappa f\|^2
 +ch\int_\Omega m_h(D/\ell)|f|^2\,d\mu .
\end{aligned}
\tag{56.2}
$$

For any normalized actual full eigenfunction with eigenvalue
$\xi_\kappa+hr$, where $-1\le r\le\epsilon_0/h$, one has

$$
\frac{\|J^*f\|^2}{w}\le C\sqrt{r+2}.
\tag{56.3}
$$

For every fixed upper bound on $r$, its rescaled amplitude
$F(q,y)=\sqrt\ell f(q,\ell y)$ satisfies the uniform tail statement

$$
\lim_{R\to\infty}\limsup_{\kappa\to0}
 \int_{R<|y|<\pi/\ell}\|F(\cdot,y)\|_{\mathscr H_B}\,dy=0.
\tag{56.4}
$$

These estimates concern the full eigenfunction, including its nonzero
visible Fourier components.

Proof. Fix a closed interval $J_0\Subset I$ of positive length.
The height gap in Lemma 40.2 is at least $\gamma_*>0$, and
$\int_{J_0}v_\kappa^2\ge\alpha_*>0$. Write a height vector as
$zv_\kappa+R_0$, with $R_0\perp v_\kappa$. By (39.4), putting
$p(D)=\min\{(D/d)^2,1\}$, the nonnegative height multiplier
$V_D=g[U_\kappa(k,0)-U_\kappa(k,D)]$ is at least
$g\eta_{J_0}p(D)1_{J_0}$. For $0<\theta\le1$ sufficiently small,

$$
\begin{aligned}
\tfrac12\langle f,K_\kappa f\rangle+\langle f,V_Df\rangle
&\ge\left(\frac{\gamma_*}{2}-\theta g\eta_{J_0}\right)\|R_0\|^2
  +\frac{\theta g\eta_{J_0}\alpha_*}{2}p(D)|z|^2\\
&\ge c\,p(D)\|f\|^2.
\end{aligned}
\tag{56.5}
$$

Here $|A+B|^2\ge|A|^2/2-|B|^2$ was integrated on $J_0$,
and $p\le1$ absorbs the $R_0$ term. Applying this on height slices,
retaining the other half of $K_\kappa$ and the entire $Q_\kappa$
square, proves (56.2), since $p(D)=hm_h(D/\ell)$. The replacement
of $gW$ by $gU_\kappa$ costs at most $\delta_\kappa\|f\|^2$.
The height-slice argument is valid on the horizontal completion by
its height derivative characterization [G, (26.13)]; it assumes no
isotropic Sobolev domain for the full operator.

Here is a weighted eigenfunction argument that supplies the missing
amplitude integrability on the whole growing chart. Set $E=r+2\ge1$,
choose $R_E=(8E/c)^{1/2}$ and decrease $\epsilon_0$ so that
$R_E^2<1/(2h)$ and $R_E<\pi/\ell$ throughout the stated energy range.
Let $M_b=\sup_{\kappa,k}b_\kappa(k)<\infty$ and choose $\eta>0$
with $M_b^2\eta^2\le c/4$. On the actual periodic chart define

$$
\Phi(y)=\eta\int_{R_E}^{|y|}\sqrt{m_h(s)}\,ds
 \quad(|y|>R_E),\qquad \Phi(y)=0\quad(|y|\le R_E).
\tag{56.6}
$$

Its values match at the seam. Use $\min\{\Phi,L\}$ first, so every
multiplier is bounded. The product rule and the eigenvalue equation give
exactly the usual weighted energy identity

$$
\mathfrak q_{\mathcal H}[e^\Phi f]-(\xi_\kappa+hr)\|e^\Phi f\|^2
 =h\int b_\kappa(k)^2|\Phi'(y)|^2e^{2\Phi(y)}|F(q,y)|^2\,d\nu_B\,dy.
\tag{56.7}
$$

Indeed $Q_\kappa\Phi=\kappa b_\kappa\ell^{-1}\Phi'$ and
$a^2/\ell^2=h$; the weight has no height derivative. This is the
Agmon energy-identity method, applied here directly to the native
horizontal form. Lipschitz periodic multiplication preserves its
completed domain: approximate the weight by smooth periodic weights,
use the horizontal product rule, and then close the form. The height
Dirichlet traces stay zero. Thus (56.7) does not introduce a new domain
or assume an exponential-decay theorem for a different operator.

Using (56.2) in (56.7), dividing by $h$, and dropping the nonnegative
height and horizontal terms yields

$$
\int\left[cm_h-r-\delta_\kappa/h-M_b^2|\Phi'|^2\right]
          e^{2\Phi}|F|^2\,d\nu_B\,dy\le0.
\tag{56.8}
$$

For small parameters $\delta_\kappa/h\le1$. Inside $R_E$ the bracket
is at least $-E$; outside it is at least $E$, since
$m_h\ge8E/c$ and $M_b^2|\Phi'|^2\le cm_h/4$. The same inequalities
hold for the truncated weight. Normalization followed by monotone
convergence as $L\to\infty$ therefore proves

$$
\int e^{2\Phi}\|F(\cdot,y)\|_{\mathscr H_B}^2dy\le2.
\tag{56.9}
$$

For $|y|>R_E$, $\sqrt{m_h(y)}\ge R_E$, so
$\Phi(y)\ge\eta R_E(|y|-R_E)$. Consequently

$$
\int e^{-2\Phi}dy\le2R_E+\frac1{\eta R_E}\le C\sqrt E,
\qquad
\left(\int\|F(\cdot,y)\|_{\mathscr H_B}dy\right)^2\le C\sqrt E.
\tag{56.10}
$$

Since $J^*f=\sqrt{\ell/(2\pi)}\int F(\cdot,y)dy$ and
$w=\alpha_\sigma\ell$, this proves (56.3). For bounded $E$, the
same Cauchy--Schwarz estimate on $|y|>R$, using (56.6) and then
$h\to0$, makes the right tail tend to zero. This proves (56.4).
In particular no global untruncated second moment has been inferred
from (40.7)--(40.9). $\square$

**Theorem 56.3 (sharp residues of actual full low eigenstates).**
Let $P_{\sigma,\kappa,N}$ be the actual full spectral projection of
the $N$th eigenvalue, numbered from $N=1$. For each fixed $N$, through
both signs, in operator norm on the entire base,

$$
\frac{J^*P_{\sigma,\kappa,N}J}{w_{\sigma,\kappa}}
 \longrightarrow b_{N-1}\Pi_\sigma,
\qquad
b_{2m}=\frac1{\sqrt\pi}\frac{(2m)!}{4^m(m!)^2},\quad b_{2m+1}=0.
\tag{56.11}
$$

In particular the actual full ground, with no phase convention imposed
on its projection, satisfies

$$
\frac{J^*P_{\sigma,\kappa,1}J}{w_{\sigma,\kappa}}
 \longrightarrow\frac{\Pi_\sigma}{\sqrt\pi},\qquad
\frac{\operatorname{tr}(J^*P_{\sigma,\kappa,1}J)}{w_{\sigma,\kappa}}
 \longrightarrow\frac1{\sqrt\pi},\qquad
\frac{\|J^*P_{\sigma,\kappa,1}J\|}{w_{\sigma,\kappa}}
 \longrightarrow\frac1{\sqrt\pi}.
\tag{56.12}
$$

Proof. The compactness and min-max proof of Theorem 40.3 gives the
rescaled eigenfunction limit at every fixed index, not just its ground.
For completeness, take the first $N$ orthonormal block eigenfunctions.
Lemma 40.2 gives simultaneous strong limits. Inductively the $N$th
limit is orthogonal to the first $N-1$ oscillator eigenfunctions, while
its limiting Rayleigh quotient is at most $(2N-1)\omega_\sigma$.
The simple oscillator spectrum forces it to be the $N$th normalized
Hermite function up to phase. This starts with (40.11).

This conclusion transfers to the actual full eigenfunction without a
boundary-normalized perturbation estimate. The first $N$ averaged
full eigenvalues are the zero-visible block eigenvalues by (41.6),
and their neighboring gaps are bounded below by a positive constant
times $h$. If $f_N$ is an actual eigenfunction, then
$\|(\widehat{\mathcal H}-\Lambda_{\sigma,N})f_N\|\le\delta_\kappa$ on the
common operator domain. Expansion in the averaged eigenbasis bounds
its component outside the corresponding rank-one eigenspace by
$C_N\delta_\kappa/h=o(1)$. Equation (41.1) also supplies simplicity
of the actual fixed-index eigenvalue. After constant phases and the
fixed change from $\ell$ to $w$, this gives

$$
\sqrt w f_N(q,wx)\longrightarrow\eta_\sigma(q)\psi_{N-1}(x)
 \quad\hbox{strongly in }L^2(d\nu_B\,dx),\qquad
\psi_n(x)=\frac{H_n(x)e^{-x^2/2}}{\pi^{1/4}\sqrt{2^n n!}}.
\tag{56.13}
$$

Zero extension is used only for this $L^2$ comparison. Lemma 56.2,
applied to the actual eigenfunction itself, gives uniform amplitude
tails for each fixed index. On bounded $x$ intervals, integration is
a bounded $L^2$ functional; outside them use (56.4). Therefore

$$
\frac{J^*f_N}{\sqrt w}
 \longrightarrow\frac{\eta_\sigma}{\sqrt{2\pi}}
                         \int_{\mathbb R}\psi_{N-1}(x)dx
 \quad\hbox{in }\mathscr H_B.
\tag{56.14}
$$

The classical oscillator normalization is that of Teschl, §8.3,
(8.35)--(8.41), already matched in Theorem 40.3. Its Gaussian
integration, or the generating function
$\sum H_n(x)t^n/n!=e^{2xt-t^2}$ integrated against $e^{-x^2/2}$,
gives

$$
\frac1{2\pi}\left|\int\psi_{2m}\right|^2=b_{2m},\qquad
\int\psi_{2m+1}=0.
\tag{56.15}
$$

Taking outer products in (56.14) proves (56.11). For the ground,
$w^{-1/2}J^*f_1\to\pi^{-1/4}\eta_\sigma$ after phase choice.
The trace and norm of its rank-one outer product both equal
$\|J^*f_1\|^2$, proving all of (56.12). $\square$

## 57. Complete slow-time responses with the exact free compensation

**Lemma 57.1 (uniform low-energy counting and boundary spectral tails).**
Decrease $\epsilon_0$ in Lemma 56.2 if necessary. With
$r_{\kappa,N}=(\Lambda_{\sigma,N}-\xi_\kappa)/h$, one has

$$
\#\{N:r_{\kappa,N}\le E\}\le C(E+2)
 \quad(-1\le E\le\epsilon_0/h).
\tag{57.1}
$$

If $0<z_0\le z\le z_1<\infty$, the part of the normalized compressed
spectral sum with $N\ge N_0$ and
$\Lambda_{\sigma,N}-\xi_\kappa\le\epsilon_0/2$ is bounded by

$$
\left\|\frac1w\sum_{\substack{N\ge N_0\\
                  \Lambda_{\sigma,N}-\xi_\kappa\le\epsilon_0/2}}
 a_{\kappa,N}e^{-zr_{\kappa,N}}J^*P_{\sigma,\kappa,N}J\right\|
 \le C_{z_0,z_1}e^{-c_{z_0}N_0},\qquad 0\le a_{\kappa,N}\le1.
\tag{57.2}
$$

In (57.2) and subsequent spectral sums, $P_{\sigma,\kappa,N}$
means the rank-one eigenvector projection in an orthonormal full
eigenbasis, with each basis vector counted once. At every fixed index
these are the full rank-one spectral projections of Theorem 56.3 for
small parameters; at a multiple eigenvalue their sum is its full
spectral projection.

Proof. First use the averaged operator on its exact Fourier sum.
By (41.6), every nonzero visible pair lies above
$\xi_\kappa+2\epsilon_0$ for small parameters. In its zero-visible
block, (56.5) and $b_\kappa\ge m_b>0$ give the comparison, in the
$y$ chart,

$$
\frac{\widehat{\mathcal H}-\xi_\kappa}{h}
 \ge\frac{K_\kappa}{2h}\otimes1
       +1\otimes\left(-m_b^2\partial_y^2+cm_h(y)\right).
\tag{57.3}
$$

The scalar hidden operator has the actual periodic ends. This
comparison retains the height gap; below $\epsilon_0/h+1$, only the
height ground can occur on its right side if
$\epsilon_0<\gamma_*/4$ and $h$ is small. To count the hidden
operator below $E\ge0$, split its circle at
$|y|=R=[2(E+1)/c]^{1/2}$ and impose Neumann conditions at the two
cuts. Decrease $\epsilon_0$ so that $R^2<1/h$ and $R<\pi/\ell$
for $E\le\epsilon_0/h+1$. On the outer interval
$cm_h\ge2(E+1)$, so it contributes no such eigenvalue. On the
inner interval, dropping the nonnegative potential gives the
Neumann Laplacian on length $2R$, with at most
$1+2R\sqrt E/(\pi m_b)\le C(E+1)$ eigenvalues below $E$.
Neumann bracketing and min-max prove the count for the entire
averaged operator in this range. All frequencies, including arbitrary
compensating hidden frequencies in nonzero visible pairs, were
excluded by (41.6), not by a finite Fourier truncation.

The bounded full-form comparison
$|\Lambda_{\sigma,N}-\widehat\Lambda_{\kappa,N}|\le\delta_\kappa$
holds at every ordered index. Since $\delta_\kappa/h=o(1)$, the
same count, with enlarged constants and the indicated small energy
margin, gives (57.1) for the actual operator. Thus in the range of
(57.2), $r_{\kappa,N}\ge N/C-2$. Lemma 56.2 bounds the norm of
each compressed eigenvector outer product divided by $w$ by
$C\sqrt{r_{\kappa,N}+2}$. Since $r_{\kappa,N}\ge-1$ and
$\sqrt{r+2}e^{-z r}\le C_{z_0}e^{-z_0r/2}$ for $r\ge0$,
summing the resulting geometric upper bound, with the finitely many
negative $r$ values bounded on $[z_0,z_1]$, proves (57.2).
This is a uniform count and amplitude estimate below a fixed physical
energy cutoff, not a growing-index conclusion drawn from (41.1).
$\square$

**Lemma 57.2 (the remaining spectrum after exact free subtraction).**
Put $M_\kappa=gM_W$, $\mathsf A=\mathcal H-\xi_\kappa$ and
$\mathsf B=L_\kappa-\xi_\kappa$. The native bounds imply

$$
\|M_\kappa\|\le C,\qquad
\sup_q\int_{\mathbb T}gW(q,D)dD\le Cd,
\qquad d=r_s\ \hbox{or}\ 1.
\tag{57.4}
$$

Let $0\le\chi\le1$ be smooth, zero on
$(-\infty,\epsilon_0/4]$ and one on $[\epsilon_0/2,\infty)$.
Choose $\epsilon_0$ also smaller than one quarter of
$\lambda-e(c_\sigma)>0$. For $t\ge1$,

$$
\left\|J^*\left[e^{-t\mathsf A}\chi(\mathsf A)-e^{-t\mathsf B}\right]J\right\|
 \le Cd(1+t)^4e^{-\epsilon_0t/4}.
\tag{57.5}
$$

The estimate uses the actual nonaveraged multiplier and entire native
free evolution.

Proof. The first bound in (57.4) is (32.9). The raw integral bound
is (45.2); for UNIT it follows from uniform boundedness and the
original circle length $2\pi$. The exact free marginal intertwining
is $e^{-i\varpi\mathsf B}J=Je^{-i\varpi(\overline L_\kappa-\xi_\kappa)}$
for the real Fourier variable $\varpi$, since the entire
$D$-independent free subspace reduces
$L_\kappa$ by [G, (23.3)--(23.5), (26.13)]. Hence, for every real Fourier variable $\varpi$,

$$
\|M_\kappa^{1/2}e^{-i\varpi\mathsf B}J\|^2
 \le\frac1{2\pi}\sup_q\int gW(q,D)dD\le Cd.
\tag{57.6}
$$

Twice applying bounded-perturbation Duhamel, with a free evolution
at both endpoints, gives for $\varpi\ge0$

$$
\begin{aligned}
e^{-i\varpi\mathsf A}-e^{-i\varpi\mathsf B}
={}&i\int_0^\varpi e^{-i(\varpi-u)\mathsf B}M_\kappa e^{-iu\mathsf B}du\\
 &-\int_{0\le v\le u\le\varpi}
 e^{-i(\varpi-u)\mathsf B}M_\kappa e^{-i(u-v)\mathsf A}M_\kappa e^{-iv\mathsf B}\,dv\,du.
\end{aligned}
\tag{57.7}
$$

Both middle evolutions are unitary. Using (57.6) at the two ends,
and $\|M_\kappa^{1/2}e^{-i(u-v)\mathsf A}M_\kappa^{1/2}\|\le C$,
therefore gives

$$
\|J^*(e^{-i\varpi\mathsf A}-e^{-i\varpi\mathsf B})J\|\le Cd(|\varpi|+\varpi^2).
\tag{57.8}
$$

Negative $\varpi$ follow by adjoints. The Duhamel integrals are
strong integrals; their norm bounds follow by testing between arbitrary
unit vectors. Bounded perturbation preserves the selfadjoint domain.
There is no heat-kernel or resolvent approximation in this step.

For $f_t(x)=e^{-tx}\chi(x)$, Fourier inversion and the spectral
theorem now bound the compressed difference $f_t(\mathsf A)-f_t(\mathsf B)$ by

$$
Cd\int (|\varpi|+\varpi^2)|\widehat f_t(\varpi)|d\varpi
 \le Cd\|f_t\|_{H^4(\mathbb R)}
 \le Cd(1+t)^4e^{-\epsilon_0t/4}.
\tag{57.9}
$$

Scalar Fourier inversion in each matrix element suffices; (57.8)
bounds its integral absolutely. The middle inequality is
Cauchy--Schwarz with $(1+\varpi^2)^{-2}$,
followed by Plancherel. The last follows by differentiating $f_t$
up to four times: every term is supported on $x\ge\epsilon_0/4$
and is an exponentially decreasing function there with bounded
cutoff derivatives. Fourier-normalization constants are included
in $C$. Finally $\inf\sigma(L_\kappa)=\lambda$ exactly, while
$\xi_\kappa\to e(c_\sigma)<\lambda$. Thus $\chi(\mathsf B)=1$ for small
parameters. This proves (57.5). It is the factor $d$ in (57.5),
rather than an unscaled whole-semigroup bound, that is essential
in RAW. $\square$

**Theorem 57.3 (the two complete native slow-time limits).**
For both signs and every fixed original parameter, uniformly on each
$0<z_0\le z\le z_1<\infty$, in operator norm on the entire original
base,

$$
\begin{aligned}
\frac{e^{z\xi_\kappa/h_{\rm unit,\kappa}}}{w_{\rm unit,\kappa}}
 C_{{\rm unit},\kappa}(z/h_{\rm unit,\kappa})
 &\longrightarrow q_{\rm unit}(z)\Pi_{\rm unit},\\
\frac{e^{z\xi_\kappa/h_{\rm raw,\kappa}}}{w_{\rm raw,\kappa}}
 [C_{{\rm raw},\kappa}(z/h_{\rm raw,\kappa})
                  -F_\kappa(z/h_{\rm raw,\kappa})]
 &\longrightarrow q_{\rm raw}(z)\Pi_{\rm raw},\\
q_\sigma(z)&=\frac1{\sqrt{2\pi\sinh(2\omega_\sigma z)}},\qquad
F_\kappa(t)=J^*e^{-tL_\kappa}J=e^{-t\overline L_\kappa}.
\end{aligned}
\tag{57.10}
$$

In the first line $\xi_\kappa$ is its UNIT height center; in the
second it is its RAW height center, always exactly Definition 38.2.

Proof. Use the same $\chi$ as in Lemma 57.2. The exact identity

$$
\begin{aligned}
e^{t\xi_\kappa}[C_{\sigma,\kappa}(t)-F_\kappa(t)]
={}&\sum_N e^{-t(\Lambda_{\sigma,N}-\xi_\kappa)}
 [1-\chi(\Lambda_{\sigma,N}-\xi_\kappa)]J^*P_{\sigma,\kappa,N}J\\
 &+J^*[f_t(\mathsf A)-f_t(\mathsf B)]J
\end{aligned}
\tag{57.11}
$$

follows by spectral calculus; its first sum is finite at each
nonzero parameter. This decomposition cancels the entire free
high-energy contribution before taking a boundary normalization.
With $t=z/h$, (57.5) divided by $w=\alpha_\sigma d\sqrt h$
is at most

$$
C h^{-1/2}(1+z_1/h)^4e^{-\epsilon_0z_0/(4h)}\longrightarrow0.
\tag{57.12}
$$

For any fixed initial number of terms in (57.11), (41.1) and
Theorem 56.3 give the correctly propagated limit

$$
\frac1w e^{-z(\Lambda_{\sigma,N}-\xi_\kappa)/h}
                 J^*P_{\sigma,\kappa,N}J
 \longrightarrow b_{N-1}e^{-(2N-1)\omega_\sigma z}\Pi_\sigma.
\tag{57.13}
$$

This convergence is uniform on the stated compact $z$ interval.
The cutoff equals one in the low factor $1-\chi$ at these fixed
indices for small parameters. Lemma 57.1 controls the entire
remaining low-energy sum uniformly, and (57.12) already controlled
all the other levels and modes of the actual full dynamics.
Taking the index cutoff to infinity gives

$$
\begin{aligned}
\sum_{m\ge0}b_{2m}e^{-(4m+1)\omega_\sigma z}
 &=\frac{e^{-\omega_\sigma z}}{\sqrt\pi}
          (1-e^{-4\omega_\sigma z})^{-1/2}\\
 &=q_\sigma(z).
\end{aligned}
\tag{57.14}
$$

This proves the compensated limit for both families. For UNIT,
$w=\alpha_{\rm unit}\sqrt h$ and $\|F_\kappa(t)\|=e^{-\lambda t}$,
so

$$
\sup_{z_0\le z\le z_1}
 \frac{e^{z\xi_\kappa/h}}w\|F_\kappa(z/h)\|
 \le\frac{1}{\alpha_{\rm unit}\sqrt h}
       e^{-(\lambda-\xi_\kappa)z_0/h}\longrightarrow0.
\tag{57.15}
$$

It can therefore be added back in UNIT, proving the first line of
(57.10). It cannot be added back in RAW, as the next result shows.
The averaging error $o(h)$ has only been used in a fixed-index
$L^2$ comparison and uniform min-max counting. No $o(h)$
whole-semigroup error has been divided by $w$. $\square$

## 58. The free background, the two centers and predictive distinctions

**Theorem 58.1 (uncompensated RAW and the original free comparison).**
Put $h=h_{\rm raw,\kappa}$, $w=w_{\rm raw,\kappa}$,
$t=z/h$, and use the RAW $\xi_\kappa$. Define only from independent
native data

$$
B_\kappa(z)=\frac1w e^{-(\lambda-\xi_\kappa)z/h},\qquad
h_*(k,\theta,v)=\frac{\phi(k)}{2\pi},\qquad
P_*=|h_*\rangle\langle h_*|.
\tag{58.1}
$$

Uniformly on every compact positive $z$ interval,

$$
\begin{gathered}
B_\kappa(z)\longrightarrow+\infty,\qquad
\frac{w^{-1}e^{z\xi_\kappa/h}C_{{\rm raw},\kappa}(z/h)}
                  {B_\kappa(z)}\longrightarrow P_*,\\
\left\|w^{-1}e^{z\xi_\kappa/h}C_{{\rm raw},\kappa}(z/h)\right\|
 \sim \frac1w e^{-(\lambda-\xi_\kappa)z/h},\\
\frac{e^{z\xi_\kappa/h}}w
       \|F_\kappa(z/h)-S_{z/h}\|\longrightarrow0.
\end{gathered}
\tag{58.2}
$$

The operator convergence is in norm on the entire base, and the norm
equivalent has relative error tending to zero uniformly. Consequently
$S_t$ is interchangeable with $F_\kappa(t)$ in the compensated RAW
limit, although the two free terms themselves diverge at that
normalization. The separately normalized UNIT free response tends
to zero by (57.15).

Proof. The original free $D$-independent subspace reduces $L_\kappa$,
so its exact compression is $e^{-t\overline L_\kappa}$. In the
zero visible block it is $-\varepsilon^2\partial_k^2$, with the
exact ground $(\lambda,h_*)$ for every $\kappa$. Every other
visible block adds the nonnegative square $(nA_\kappa+mB_\kappa)^2$.
Their bottoms have a uniform positive gap above $\lambda$: use
the large-frequency bound [G, (26.6)] outside a fixed lattice ball,
and inside that ball use coefficient continuity and the strictly
positive nonzero-visible gaps at $\kappa=0$ from Theorem 36.2.
The next zero-visible height eigenvalue is $4\lambda$. Thus for
some $\gamma_f>0$, all $t\ge0$ and small parameters,

$$
\|F_\kappa(t)\|=e^{-\lambda t},\qquad
\|e^{\lambda t}F_\kappa(t)-P_*\|\le e^{-\gamma_ft}.
\tag{58.3}
$$

There is no unknown free-bottom correction or boundary-overlap
coefficient in this formula: the isometry $J$ fixes both exactly.

In RAW, $w=\alpha_{\rm raw}a\tau_s^{1/4}$,
$h=\tau_s^{-1/2}$ and $L_a=\log(1/a)$. Hence exactly

$$
\log B_\kappa(z)=L_a-\tfrac14\log\tau_s-\log\alpha_{\rm raw}
                    -(\lambda-\xi_\kappa)z\sqrt{\tau_s}.
\tag{58.4}
$$

Since $\tau_s\sim L_a/\lambda$ and $\xi_\kappa$ is bounded,
$\log B_\kappa(z)/L_a\to1$ uniformly on compact positive $z$
intervals. The compensated remainder in (57.10) is bounded after
its stated normalization. Dividing it by $B_\kappa(z)$ makes it
vanish uniformly; (58.3) proves the first three assertions of
(58.2). This concerns exactly the object with $e^{z\xi_\kappa/h}/w$,
regardless of the sign or a zero value of $e(c_{\rm raw})$.

For the last assertion, the exact $(n,m)$ blocks of
$\overline L_\kappa$ and $\mathcal K_0$ have the same scalar
Dirichlet domain and potentials differing by at most
$Ca(n^2+m^2)$, as in (46.1)--(46.2). Both scalar bottoms are at
least $\lambda+c\Psi(\sqrt{n^2+m^2})$ uniformly, with $\Psi$
from [G, (26.6)]. Duhamel on these scalar blocks, followed by the
supremum over the entire integer lattice, therefore gives for $t\ge1$

$$
\|F_\kappa(t)-S_t\|
 \le Ca t e^{-\lambda t}
       \sup_{R\ge1}R^2e^{-ct\Psi(R)}
 \le Ca t e^{-\lambda t}.
\tag{58.5}
$$

The zero visible block agrees exactly and contributes zero.
The last supremum is bounded because $\Psi$ has the growth
specified in [G, (26.6)]. In the normalization at issue,
$a/w=\alpha_{\rm raw}^{-1}\sqrt h$, so (58.5) implies

$$
\sup_{z_0\le z\le z_1}
 \frac{e^{z\xi_\kappa/h}}w\|F_\kappa(z/h)-S_{z/h}\|
 \le C h^{-1/2}e^{-(\lambda-\xi_\kappa)z_0/h}\longrightarrow0.
\tag{58.6}
$$

Here $\lambda-\xi_\kappa\to\lambda-e(c_{\rm raw})>0$.
This is a comparison of the two exact free responses at the requested
scale, not an inference from their individual sizes. $\square$

**Corollary 58.2 (actual-ground recentering in both conventions).**
Let $\Lambda_{\sigma,1}$ be the actual full ground energy. Write
$R_{{\rm unit},\kappa}(t)=C_{{\rm unit},\kappa}(t)$ and
$R_{{\rm raw},\kappa}(t)=C_{{\rm raw},\kappa}(t)-F_\kappa(t)$.
On the same compact positive $z$ intervals and whole-base norm scope,

$$
\frac{e^{z\Lambda_{\sigma,1}/h_{\sigma,\kappa}}}
                    {w_{\sigma,\kappa}}
 R_{\sigma,\kappa}(z/h_{\sigma,\kappa})
 \longrightarrow e^{\omega_\sigma z}q_\sigma(z)\Pi_\sigma.
\tag{58.7}
$$

For RAW this also holds with $S_t$ replacing $F_\kappa(t)$.
The uncompensated RAW response under actual-ground centering still
diverges; its norm is equivalent to
$w^{-1}e^{-(\lambda-\Lambda_{{\rm raw},1})z/h}$.
After taking the parameter limit, the explicit scalar functions obey

$$
q_\sigma(z)\sim(4\pi\omega_\sigma z)^{-1/2}\quad(z\downarrow0),
\qquad
e^{\omega_\sigma z}q_\sigma(z)\longrightarrow\pi^{-1/2}
                                      \quad(z\to\infty).
\tag{58.8}
$$

Proof. Theorem 41.1 gives
$(\Lambda_{\sigma,1}-\xi_\kappa)/h\to\omega_\sigma$.
Its exponential converges uniformly on every such compact interval;
multiplication of (57.10) proves (58.7), and of (58.2), (58.6)
proves the RAW comparisons. The elementary asymptotics of $\sinh$
give (58.8). All primary limits retain the exact $\xi_\kappa$.
No rate for $\xi_\kappa-e(c_\sigma)$, replacement by its limit in
an exponential, joint $z$ endpoint uniformity, or extra parameter
uniformity is used or asserted. $\square$

**Proposition 58.3 (probability, amplitude, time and dimension).**
For both native critical families, actual ground probability has the
normalized fluctuation law (42.2), while its amplitude-boundary spectral
weight is $w/\sqrt\pi+o(w)$ in the direction $\Pi_\sigma$.
The slow compensated response resolves all limiting even oscillator
levels with the weights (56.11), rather than just this ground pole.
UNIT loses the free background on that clock; RAW retains a background
larger than the compensated response by the factor $B_\kappa(z)$.
These are distinct predictive requirements and do not select a physical
spatial dimension or supply a preparation or acquisition operation.

Proof. The probability assertion is Theorem 42.1 and the amplitude
assertion is (56.12). Integration of an amplitude is not integration
of its square; Lemma 56.2 is what permits that passage on the growing
chart. The complete spectral sum (57.14) has a strictly positive term
for every even level, with limiting odd-level weights zero. In fact
$h_{\rm raw}=\tau_s^{-1/2}$ and $h_{\rm unit}=a$ resolve the actual
spacings (41.2), whereas $w_{\rm raw}$ and $w_{\rm unit}$ govern
boundary visibility. The native RAW propagation time $z\sqrt{\tau_s}$
is shorter than its source cutoff $\tau_s$; (58.4) quantifies the
surviving free background. UNIT uses propagation time $z/a$ and source
cutoff $b/a^2$; its free-background comparison is (57.15).

The phase periods, the two height deaths, the source cutoff clock and
the later propagation clock have all remained those of Definition
31.1 and [G, Definition 25.1]. The limiting base direction has the
original two visible coordinates and height; neither its coordinate
count, a hidden oscillator index nor covariance rank identifies three
Euclidean spatial axes. The observation-quotient and free-diffusion
classification boundaries in §§43,49,55 remain unchanged. There is no
new physical preparation, reset, actuator, finite-shot acquisition,
bit count, CPU estimate or infinite-volume law in these conclusions.

The classical inputs are selfadjoint spectral calculus (Teschl,
Chapters 2--4), form min-max (Theorem 4.10), bounded-form perturbation
as a relative-bound-zero case of KLMN (Theorem 6.24), and normalized
Hermite functions (§8.3, (8.35)--(8.41)), in the cited
[author text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
The needed bounded-operator Duhamel identity is written explicitly in
(57.7), and the classical weighted eigenfunction identity in (56.7).
Simon's [1983 paper, §1, (A1)--(A4), and §§2--3](https://www.numdam.org/item/AIHPA_1983__38_3_295_0.pdf)
provides the mature harmonic-localization comparison discussed in
43.3: fixed smooth scalar potentials with nondegenerate minima do
not by themselves cover this moving RAW field or horizontal full
operator. Its fixed-index result is not used as an amplitude-tail
or entire-response supplier. The native additions proved here are
(56.2)--(56.4), the uniform count (57.1), and the exact compensated
high-energy bound (57.5), which together close precisely those
correspondence gaps. The other native suppliers cited in 43.3 retain
their stated source, quotient and fixed-pole qualifications; none
is silently substituted for a critical amplitude theorem. These are
ordinary mathematical proofs, with no Lean-verification, physical
realization or worldwide-priority claim. $\square$

## 追加锚（本行以下为增补区）
