# Same-source attractive boundary response: complete Green marginal error

## 20. Uniform small central noise and the original exterior tail

**Definition 20.1 (analytic assumptions and the complete-source notation).**
Let $n\ge2$ be an integer. Throughout this continuation assume precisely
Definition 18.1 of [Same-source native attractive boundary response](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
with that definition and its suppliers understood as stated at revision
[6d4c5224d23d842a8772cd21c3c69fe7a45c8fdd](https://github.com/the-omega-institute/trureturing/blob/6d4c5224d23d842a8772cd21c3c69fe7a45c8fdd/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md).
In particular the analytic assumptions are Theorem 10.2's original-field
formulas and locally uniform off-pole convergence, the full complex polar
identity (12.12)--(12.13), the closed natural angular form and compact
embedding of V, Theorem 10.2 at the revision fixed in Definition 1.1,
the natural-core approximation (13.6)--(13.8), the complete-field scaling
(14.9), and the original closed form, compact smooth core and local
estimates (15.9)--(15.12). Here C and V mean the central-noise and
variable-coefficient Green stability suppliers, respectively, at
5cec4fa83ae7bbb4e787c42606525db4cd11ed48, exactly as in Definition 1.1.
The assertions below are conditional on these analytic assumptions.

For the small-noise comparison use Definition 10.1's family, for every
$\epsilon\ge0$, on $H^n=\mathbb R^{2n}\times\mathbb R$ with its raw
Lebesgue measure, identity unit source and fields

$$
\begin{aligned}
U_j&=\partial_{x_j}-\tfrac12y_j\partial_z,&
V_j&=\partial_{y_j}+\tfrac12x_j\partial_z,& Z&=\partial_z,\\
L_{n,\epsilon}&=-\sum_{j=1}^n(U_j^2+V_j^2)-\epsilon^2Z^2,&
h_{n,\epsilon}(t)&=e^{-tL_{n,\epsilon}}\delta_0,&
G_{n,\epsilon}&=\int_0^\infty h_{n,\epsilon}(t)\,dt.
\end{aligned}
\tag{20.1}
$$

The heat clock has horizontal covariance $2$ and independent central
covariance $2\epsilon^2$. Write $X=(X_1,W)$, $X_1=(x,y)$,
$W\in\mathbb R^{2n-2}$, $\xi=(x,y,z)$ and $\rho=|X_1|$. Set

$$
\begin{aligned}
m_{n,\epsilon}(t,\xi)
 &=\int_{\mathbb R^{2n-2}}h_{n,\epsilon}(t,X_1,W,z)\,dW,\\
M_{n,\epsilon}(\xi)
 &=\int_{\mathbb R^{2n-2}}G_{n,\epsilon}(X_1,W,z)\,dW
 =\int_0^\infty m_{n,\epsilon}(t,\xi)\,dt,\\
R(\xi)&=(\rho^4+16z^2)^{1/4},&
\delta_r(x,y,z)&=(rx,ry,r^2z),&
\Sigma&=\{\xi:R(\xi)=1\}.
\end{aligned}
\tag{20.2}
$$

Every omitted coordinate is integrated without a weight, and the time
integral retains both endpoints. These are the parent-source marginals;
they are not defined by an autonomous retained heat semigroup.
The partial Fourier convention is
$\widehat f(k)=\int_{\mathbb R}e^{-ikz}f(z)\,dz$ and
$f(z)=(2\pi)^{-1}\int_{\mathbb R}e^{ikz}\widehat f(k)\,dk$.

Use $J=(-\pi/2,\pi/2)$, $c(a)=\cos a$ and the original angular weight

$$
I_n=\int_0^{\pi/2}\sin(t)^{n-2}\,dt,\qquad
q_n(a)=\frac1{I_n}\int_0^1
             \frac{s^{n-2}}{\sqrt{1-s^2\sin^2a}}\,ds.
\tag{20.3}
$$

It extends continuously to $\overline J$, with
$q_n(\pm\pi/2)=1$. The full gauge sphere is parametrized by

$$
\omega(a,\theta)
 =(\sqrt{\cos a}\cos\theta,\sqrt{\cos a}\sin\theta,\sin a/4),
\qquad a\in\overline J,\quad\theta\in\mathbb R/(2\pi\mathbb Z).
\tag{20.4}
$$

At either endpoint of $\overline J$ all values of $\theta$ denote the
same axis point. Equations (12.5) and (14.9) of the original source give

$$
M_{n,0}(\delta_r\omega)=r^{-2}\frac{q_n(a)}{2\pi},\qquad
M_{n,\epsilon}(\delta_r\xi)=r^{-2}M_{n,\epsilon/r}(\xi)
\quad(r>0,\ \xi\ne0).
\tag{20.5}
$$

**Theorem 20.2 (uniform complete Green marginal error).**
Under Definition 20.1's assumptions, for every integer $n\ge2$ there
exist $C_n<\infty$ and $\epsilon_n\in(0,1]$ such that, for every
$\epsilon\in[0,\epsilon_n]$,

$$
\sup_{\omega\in\Sigma}
 |M_{n,\epsilon}(\omega)-M_{n,0}(\omega)|\le C_n\epsilon^2.
\tag{20.6}
$$

The supremum includes both axis points $(0,0,\pm1/4)$ and the
$z=0$ circle. There is no restriction on an angular approach to them.
One permissible choice of constants is obtained by fixing any
$\alpha\in(0,\pi/2)$ and putting

$$
\begin{aligned}
F_n(u)&=\frac{u}{\sinh u\,\cosh(u)^{n-1}},\\
b_\alpha&=\inf_{v\in\mathbb R}
        \operatorname{Re}[(v+i\alpha)\coth(v+i\alpha)]>0,\\
K_{n,\alpha}&=\int_{\mathbb R}|F_n(v+i\alpha)|\,|v+i\alpha|^2\,dv<\infty,\\
D_\alpha&=\tfrac14\min\{b_\alpha,\alpha\},\qquad
\epsilon_n=\min\{1,\sqrt{D_\alpha/(2\alpha^2)}\},\qquad
C_n=\frac{K_{n,\alpha}}{2\pi^2D_\alpha^2}.
\end{aligned}
\tag{20.7}
$$

**Proof.** At each fixed $t>0$, the exact original heat formulas
(9.7) and (10.3) give, with $\kappa=|k|$,

$$
\widehat m_{n,\epsilon}(t,\rho,k)
 =e^{-\epsilon^2tk^2}
  \frac{\kappa}{4\pi\sinh(\kappa t)\cosh(\kappa t)^{n-1}}
  \exp\!\left(-\frac{\rho^2\kappa\coth(\kappa t)}4\right).
\tag{20.8}
$$

The continuous value at $k=0$ is
$(4\pi t)^{-1}\exp(-\rho^2/(4t))$. Thus the raw unit-source
normalization is retained. The oscillator factors are classical:
Krötz--Thangavelu--Xu, *The heat kernel transform for the Heisenberg
group*, [math/0401243v2](https://arxiv.org/abs/math/0401243v2),
§2.2, (2.2.1), and §4.1, (4.1.2), supply their literature counterpart.
Their coordinates $(x,u,\xi)$ correspond to the present horizontal
coordinates and central coordinate $z$, their raw Haar measure is
Lebesgue measure, and their negative heat generator is $-L_{n,1}$.
The central Fourier sign is reversed in their §4.1; the oscillator
column is even in the Fourier parameter. For general $\epsilon$ the
central factor is exactly $e^{-\epsilon^2tk^2}$. Integrating an omitted
horizontal pair in that column gives $\operatorname{sech}(|k|t)$.
The inverse-transform constant here is the stated $1/(2\pi)$,
fixed by the Gaussian zero mode, rather than a copied prefactor from
(2.2.1). These mature heat formulas are intermediate suppliers for the
following source-specific error deduction.

For fixed $t>0$, Fourier inversion is absolutely convergent even at
$\epsilon=0$, because the hyperbolic factors decay exponentially as
$|k|\to\infty$. Setting $u=tk$ and subtracting the two fixed-time
columns yields the exact identity

$$
\begin{aligned}
&m_{n,\epsilon}(t,\rho,z)-m_{n,0}(t,\rho,z)\\
&\quad=\frac1{8\pi^2t^2}\int_{\mathbb R}
 F_n(u)\exp\!\left(-\frac{\rho^2u\coth u}{4t}+\frac{izu}{t}\right)
 \left(e^{-\epsilon^2u^2/t}-1\right)\,du.
\end{aligned}
\tag{20.9}
$$

Indeed $u/\sinh u$, $\cosh(u)^{-(n-1)}$ and $u\coth u$ are even
on the real line, so they reproduce the absolute-value expressions
in (20.8). At $u=0$ their singularities are removable. No Fourier
transform of an infinite-time Green integral is used in (20.9).

Fix $0<\alpha<\pi/2$. The functions $F_n(u)$ and $u\coth u$
are analytic on $|\operatorname{Im}u|<\pi/2$, with their removable
values at zero. If $z\ne0$, shift the contour in (20.9) to
$u=v+i\alpha\operatorname{sgn}z$. If $z=0$, either sign can be
used. This contour stays strictly inside the pole-free strip.
For completeness, on each vertical end $u=\pm A+iy$ with $y$ between
zero and the chosen shift,

$$
|F_n(\pm A+iy)|\le C_{n,\alpha}(1+A)e^{-nA},\quad
\operatorname{Re}(u\coth u)=A+O_\alpha((1+A)e^{-2A}),\quad
|e^{izu/t}|=e^{-zy/t}\le1.
\tag{20.10}
$$

Moreover, for $\delta\ge0$,
$|e^{-\delta u^2}-1|\le e^{\delta\alpha^2}+1$ there, since
$\operatorname{Re}(u^2)=A^2-y^2\ge-\alpha^2$.
Consequently the vertical integrals vanish as $A\to\infty$ for
all fixed $t,\rho,z,\epsilon$, including $\rho=0$ and $\epsilon=0$.
The shifted horizontal integrals are absolutely convergent.
Cauchy's theorem on these finite rectangles therefore justifies the
shift, with no angular or axis exclusion.

On the upper shifted line direct calculation gives

$$
\operatorname{Re}[(v+i\alpha)\coth(v+i\alpha)]
 =\frac{v\sinh(2v)+\alpha\sin(2\alpha)}
        {\cosh(2v)-\cos(2\alpha)}.
\tag{20.11}
$$

The denominator is positive and the numerator is strictly positive
for every real $v$: $v\sinh(2v)\ge0$ and
$\alpha\sin(2\alpha)>0$. The quotient is continuous, tends to
$|v|$ at infinity, and hence has strictly positive infimum
$b_\alpha$. On the lower line its real part is the same.
Also $|F_n(v\pm i\alpha)|$ decays exponentially times a linear
factor as $|v|\to\infty$, proving finiteness of $K_{n,\alpha}$.
Complex conjugation gives the same integral for both signs.

For any $u=v\pm i\alpha$ and $\delta\ge0$, the identity

$$
e^{-\delta u^2}-1
 =-\delta u^2\int_0^1e^{-s\delta u^2}\,ds
\quad\Longrightarrow\quad
|e^{-\delta u^2}-1|
 \le\delta|u|^2e^{\delta\alpha^2}
\tag{20.12}
$$

follows from $\operatorname{Re}(u^2)=v^2-\alpha^2\ge-\alpha^2$.
This estimate is valid without assuming $\delta$ small. Taking
$\delta=\epsilon^2/t$ in the shifted (20.9) gives

$$
|m_{n,\epsilon}(t,\rho,z)-m_{n,0}(t,\rho,z)|
 \le\frac{K_{n,\alpha}}{8\pi^2}\epsilon^2t^{-3}
 \exp\!\left(-\frac{b_\alpha\rho^2/4+\alpha|z|-\alpha^2\epsilon^2}{t}\right).
\tag{20.13}
$$

Here the central phase contributes $e^{-\alpha|z|/t}$ on the
chosen line. In particular the same estimate holds for $z=0$.
For $\omega\in\Sigma$, write $a\in\overline J$ as in (20.4).
Since $\rho^2=\cos a$, $|z|=|\sin a|/4$, and
$\cos a+|\sin a|\ge1$ on that entire closed interval,

$$
\frac{b_\alpha\rho^2}{4}+\alpha|z|
 =\frac{b_\alpha\cos a+\alpha|\sin a|}4
 \ge D_\alpha.
\tag{20.14}
$$

This is positive at the two axis points as well as at $z=0$.
For $0\le\epsilon\le\epsilon_n$ of (20.7), (20.13) is therefore
bounded, uniformly on $\Sigma$, by

$$
\frac{K_{n,\alpha}}{8\pi^2}\epsilon^2t^{-3}
                         e^{-D_\alpha/(2t)}.
\tag{20.15}
$$

This function is integrable over the whole positive time axis:
by $s=D_\alpha/(2t)$,

$$
\int_0^\infty t^{-3}e^{-D_\alpha/(2t)}\,dt
 =\frac4{D_\alpha^2}\int_0^\infty se^{-s}\,ds
 =\frac4{D_\alpha^2}.
\tag{20.16}
$$

The small-time endpoint has the displayed exponential control;
the large-time endpoint has the integrable power $t^{-3}$.
The individual nonnegative whole-time integrals in (20.2) are finite
off the pole by the supplied Theorem 10.2. Subtract them first on a
finite time interval, then let its endpoints tend to zero and infinity.
Estimate (20.15)--(20.16) justifies convergence of the difference
absolutely, uniformly on $\Sigma$, and identifies it with
$M_{n,\epsilon}-M_{n,0}$. It follows that its absolute value is at
most $K_{n,\alpha}\epsilon^2/(2\pi^2D_\alpha^2)$, proving (20.6).
For $\epsilon=0$ the difference is identically zero. The proof has
retained the full time integral and the full unweighted marginal.

**Corollary 20.3 (the original exterior error and log-cylinder multiplier).**
For every fixed integer $n\ge2$, with the constants of Theorem 20.2,
put $R_n=\epsilon_n^{-1}$ and $\ell_n=\log R_n\ge0$. For every
$\xi$ with $R=R(\xi)\ge R_n$,

$$
|M_{n,1}(\xi)-M_{n,0}(\xi)|\le C_nR^{-4}.
\tag{20.17}
$$

Equivalently, define on $[\ell_n,\infty)\times\overline J\times\mathbb T$

$$
\begin{aligned}
B_n(\ell,a,\theta)
 &=e^{2\ell}M_{n,1}(\delta_{e^\ell}\omega(a,\theta))
                                      -\frac{q_n(a)}{2\pi}\\
 &=M_{n,e^{-\ell}}(\omega(a,\theta))-M_{n,0}(\omega(a,\theta)).
\end{aligned}
\tag{20.18}
$$

Then for every $\ell\ge\ell_n$,

$$
\sup_{(a,\theta)\in\overline J\times\mathbb T}|B_n(\ell,a,\theta)|
 =\sup_{\omega\in\Sigma}|M_{n,e^{-\ell}}(\omega)-M_{n,0}(\omega)|
 \le C_ne^{-2\ell}.
\tag{20.19}
$$

Both axis directions remain included in the supremum.

**Proof.** Given $\xi\ne0$, set $\omega=\delta_{1/R}\xi\in\Sigma$.
The exact complete-field scaling (20.5) gives

$$
M_{n,1}(\delta_R\omega)-M_{n,0}(\delta_R\omega)
 =R^{-2}\{M_{n,1/R}(\omega)-M_{n,0}(\omega)\}.
\tag{20.20}
$$

For $R\ge R_n$, $1/R\le\epsilon_n$, so (20.6) proves (20.17).
Taking $R=e^\ell$ and using the homogeneous angular identity in
(20.5) proves (20.18)--(20.19). The scaling is for complete fields:
the parent heat density scales with factor $R^{-(2n+2)}$, the
whole time change contributes $R^2$, and the full omitted fibre
contributes $R^{2n-2}$, giving exactly $R^{-2}$. Thus no time
cutoff or weighted fibre has entered the exterior conclusion.

**Corollary 20.4 (every nonnegative polynomial weight).**
For every integer $n\ge2$, every real $p\ge0$, and every
$\ell_0\ge\ell_n$,

$$
\begin{aligned}
&\int_{\ell_0}^\infty(1+\ell)^p
 \sup_{\omega\in\Sigma}|M_{n,e^{-\ell}}(\omega)-M_{n,0}(\omega)|\,d\ell\\
&\qquad\le C_n\int_{\ell_0}^\infty(1+\ell)^pe^{-2\ell}\,d\ell<\infty.
\end{aligned}
\tag{20.21}
$$

In particular the same assertion holds with $(1+\ell)^p$ replaced
by any polynomial with nonnegative coefficients. In exterior radial
coordinates this is precisely

$$
\int_{e^{\ell_0}}^\infty(1+\log r)^p
 \sup_{\omega\in\Sigma}
 |r^2M_{n,1}(\delta_r\omega)-M_{n,0}(\omega)|\,\frac{dr}{r}<\infty.
\tag{20.22}
$$

**Proof.** Apply (20.19). For fixed real $p\ge0$,
$A_p=\sup_{\ell\ge0}(1+\ell)^pe^{-\ell}<\infty$ by elementary
calculus, so the right side of (20.21) is at most
$C_nA_pe^{-\ell_0}$. A polynomial with nonnegative coefficients
is a finite nonnegative sum of these weights. Finally put
$r=e^\ell$, so $dr/r=d\ell$, and apply (20.18).

**Corollary 20.5 (the full complex exterior form consequence).**
Fix an integer $n\ge2$, a real $g>0$ and $\ell_0\ge\ell_n$.
Write $d\eta=d\ell\,da\,d\theta$ on
$\mathcal C_{\ell_0}=(\ell_0,\infty)\times J\times\mathbb T$.
For every complex measurable $v$ for which the right side is finite,

$$
\left|g\int_{\mathcal C_{\ell_0}}B_n|v|^2\,d\eta\right|
 \le gC_n\int_{\mathcal C_{\ell_0}}e^{-2\ell}|v|^2\,d\eta.
\tag{20.23}
$$

Consequently (20.23) holds for every $v$ in the original exterior
form domain after the substitution $f=R^{-1}v$. With
$W_{n,\epsilon}^{\rm ext}[f]
=\int_{\{R>e^{\ell_0}\}}M_{n,\epsilon}|f|^2\,d\xi$, it reads

$$
\begin{aligned}
4g|W_{n,1}^{\rm ext}[f]-W_{n,0}^{\rm ext}[f]|
 &\le gC_n\int_{\mathcal C_{\ell_0}}e^{-2\ell}|v|^2\,d\eta\\
 &\le4gC_ne^{-4\ell_0}\|f\|_{L^2(\{R>e^{\ell_0}\},d\xi)}^2.
\end{aligned}
\tag{20.24}
$$

There is no angular symmetry restriction; every integer Fourier mode
and every complex superposition is included, with the natural angular
domains of (18.1).

**Proof.** The pointwise estimate (20.19), multiplication by
$g|v|^2$ and integration prove absolute convergence and (20.23).
The raw polar Jacobian and substitution give

$$
d\xi=\tfrac14e^{4\ell}d\eta,\qquad
4\|f\|_2^2=\int_{\mathcal C_{\ell_0}}e^{2\ell}|v|^2\,d\eta,
\qquad
4(W_{n,1}^{\rm ext}-W_{n,0}^{\rm ext})[f]
 =\int_{\mathcal C_{\ell_0}}B_n|v|^2\,d\eta.
\tag{20.25}
$$

In particular $e^{-2\ell}\le e^{-4\ell_0}e^{2\ell}$ on this
cylinder, proving (20.24). The separate potential forms are finite
on the original domain by the supplied original-field form bounds.
Alternatively their exterior finiteness follows directly from (20.5)
and (20.19), which bound $M_{n,0}$ and $M_{n,1}$ there.
Thus (20.25) first holds for compact smooth functions and extends
to the original exterior form domain; no derivative is taken of
$B_n$. Unitary Fourier series in $\theta$ and the unit-modulus
angular gauge $v_m=e^{-ima/2}w_m$ preserve this multiplication
estimate. No restriction on the Fourier support was made.

## 21. The exact counting boundary after the source comparison

**Definition 21.1 (the original count and the unresolved comparisons).**
Retain Definition 20.1's analytic assumptions. On the original retained
$\mathbb R^3$ put
$U=\partial_x-(y/2)\partial_z$, $V=\partial_y+(x/2)\partial_z$,
$Z=\partial_z$ and

$$
T_1[f]=\|Uf\|_2^2+\|Vf\|_2^2+\|Zf\|_2^2,\qquad
\mathcal H_1=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^
                                      {(\|f\|_2^2+T_1[f])^{1/2}}.
\tag{21.1}
$$

For each fixed $g>\lambda_n=2\pi\mu_n$, let $A_{n,1,g}$ be the
original Friedrichs operator of $T_1-gW_{n,1}$ on exactly this domain,
and $N_{n,g}(E)=\operatorname{rank}_{\mathbb C}
\mathbf1_{(-\infty,-E)}(A_{n,1,g})$ for $E>0$. In the notation
(18.1)--(18.3), $\mu_n=\inf_{0\ne b\in\mathcal H_c}A[b]/Q_n[b]$,
$Q_n[b]=\int_Jq_n|b|^2da$, and the natural domains are

$$
\begin{aligned}
\mathcal H_c&=\{b\in L^2(J;\mathbb C):b\in AC_{\rm loc}(J),\
                                  \sqrt c\,b'\in L^2(J)\},\\
A[b]&=\int_J(4c|b'|^2+c|b|^2)\,da,\\
D_0&=\mathcal H_c,\qquad
D_m=\mathcal H_c\cap L^2(J,\sin^2a/c(a)\,da)\quad(m\ne0),\\
L_{n,g}&=\frac{d_{n,g}}2
 =\frac1{4\pi}\sum_{m\in\mathbb Z}\int_{\mathbb R}
                         \nu_{n,g}(\sigma,m)\,d\sigma.
\end{aligned}
\tag{21.2}
$$

Here $\nu$ is the strict negative complex rank of the angular form
$A[b]+\int_Jc(\sigma+m\tan a)^2|b|^2da-(g/(2\pi))Q_n[b]$
on $D_m$. No endpoint trace is prescribed. The supplied Theorem 18.2
states $0<L_{n,g}<\infty$ and
$N_{n,g}(E)=L_{n,g}\log(1/E)+o(\log(1/E))$.
The stronger assertion (18.22) remains the following open question:
for every such fixed $n,g$, do there exist $C_{n,g}<\infty$ and
$E_{n,g}\in(0,1)$ such that

$$
|N_{n,g}(E)-L_{n,g}\log(1/E)|\le C_{n,g}
\qquad(0<E<E_{n,g})?
\tag{21.3}
$$

The auxiliary periodic and Dirichlet longitudinal indices $P_g(T)$
and $D_g(T)$ retain exactly the form (18.8), its positive-form
closures and the natural angular domains $D_m$. The already supplied
periodic estimate (18.9) is $P_g(T)=d_{n,g}T+O_{n,g}(1)$;
(18.11)--(18.12) supply only $D_g(T)/T\to d_{n,g}$.
The periodic estimate is used here solely as that existing result.
Its analytic Fredholm intermediate is Dyatlov--Zworski,
*Mathematical Theory of Scattering Resonances*, version 1.0,
[Theorem C.8, p.522](https://math.mit.edu/~dyatlov/res/res_final.pdf),
applied in (18.7) to identity plus a compact holomorphic polynomial
perturbation, with an invertible real point supplied by (18.6).
It does not compare longitudinal realizations. The strict complex
form-index principle used for comparisons is the classical
form-domain min-max principle in Teschl,
*Mathematical Methods in Quantum Mechanics*, authorized first edition,
[Theorems 4.10 and 4.12(i), p.119](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
It does not bound an interface's dimension cost.

A bounded comparison between $P_g(T)$ and $D_g(T)$ is not supplied
by these results. The full angular interface trace space is
infinite-dimensional, and no finite-codimension reduction for it
has been established. In particular the cutoff estimate (18.11)
uses a fixed negative margin $\delta>0$, with its constants depending
on $\delta$, before taking $\delta\downarrow0$. A prospective
Dirichlet-cylinder assertion

$$
\begin{gathered}
\forall n\ge2\ (n\in\mathbb Z),\ \forall g>\lambda_n,\quad
\exists C_{n,g}<\infty,\ \exists T_{n,g}>0:\\
|D_g(T)-d_{n,g}T|\le C_{n,g}\qquad(T\ge T_{n,g})
\end{gathered}
\tag{21.4}
$$

is an unproved subsidiary question, including couplings with zero
angular channels. It is not by itself a transfer theorem for (21.3).

Indeed, before the angular gauge, the exact original central energy
and spectral wall in (18.13) remain

$$
\begin{aligned}
4\|Zf\|_2^2
 &=\int e^{-2\ell}
   |2\sin a(\partial_\ell v-v)+4c\partial_av|^2\,d\eta,\\
4E\|f\|_2^2&=\int Ee^{2\ell}|v|^2\,d\eta.
\end{aligned}
\tag{21.5}
$$

Together with the homogeneous horizontal form, the original exterior
shifted form therefore retains the positive derivative term in
(21.5), the potential correction $-g\int B_n|v|^2d\eta$, and the
soft spectral wall $Ee^{2\ell}$. Theorem 20.2 and Corollary 20.5
control the potential correction. They do not turn the derivative
term into bounded $L^2$ multiplication. Still missing is a uniform
bounded strict-index comparison, as $E\downarrow0$, between this
original realization and a cylinder count with coefficient $d_{n,g}$,
including the interfaces, the central derivatives and the soft wall,
with the natural endpoints, every integer mode and all zero-channel
couplings. Even (21.4), if proved, would require this further comparison.
The fixed coupling and interface tolerances in (18.18)--(18.21) cannot
be replaced by $E$-dependent tolerances without controlling all of
the constants that depend on them.

For comparison with mature inverse-square counting theory,
Hassell--Marshall, *Eigenvalues of Schrödinger operators with potential
asymptotically homogeneous of degree $-2$*,
[math/0510617v1, Theorem 1, pp.2--3](https://arxiv.org/abs/math/0510617v1),
treat the positive Euclidean Laplacian in dimension $d\ge3$ with
bounded measurable potential $r^{-2}(P(\omega)+t(r,\omega))$ outside
$r=1$. Their bounded counting remainder assumes either absence of
the critical spherical angular eigenvalue $-(d-2)^2/4$ together with
$t=O((\log r)^{-1-\varepsilon})$, or the stronger
$t=O((\log r)^{-2-\varepsilon})$, $\varepsilon>0$, allowing that
critical eigenvalue. This is an attributed comparison, not an
application to (21.1): the present kinetic operator is different,
its natural endpoints are degenerate, and its angular pencil contains
$c(a)(\sigma+m\tan a)^2$. No equivalence or bounded-index reduction
to their separated spherical realization is assumed or proved.
Their threshold allowance also means that a zero angular channel
alone is not a counterexample to (21.3). Neither a changed-potential
example nor failure of an interface argument refutes the fixed
original-source assertion.

The quantitative estimates (20.6), (20.17), and (20.19)--(20.24) are
deductions from the original source formulas and their exact scaling;
the cited mature intermediate theorems are used only in their stated
realizations. These deductions make no assertion of literature
originality, of optimality of the rates, of parameter uniformity in
$n$ or $g$, or of the truth or falsity of (21.3).

## 追加锚（本行以下为增补区）
