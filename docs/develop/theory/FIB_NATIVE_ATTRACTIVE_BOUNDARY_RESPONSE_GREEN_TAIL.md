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
by any real polynomial $P(\ell)$ nonnegative on $[\ell_0,\infty)$. In exterior radial
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
$C_nA_pe^{-\ell_0}$. For $P(\ell)=\sum_{j=0}^d a_j\ell^j$ and $\ell\ge0$,
$|P(\ell)|\le(\sum_{j=0}^d|a_j|)(1+\ell)^d$. This proves the
assertion for every stated nonnegative polynomial. Finally put
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
\mathcal H_c&=\{b\in L^2(J;\mathbb C):b\in AC_{\rm loc}(J),
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

## 22. Bounded Dirichlet loss from energy-weighted seam cancellation

**Definition 22.1 (unchanged fibres and their energy spaces).** Retain
exactly Definition 18.1's analytic hypotheses, the complex cylinder
form (18.8), its periodic and longitudinal Dirichlet positive-form
closures, and the normalizations in (21.2). Fix an integer $n\ge2$
and a real $g>\lambda_n$, and put $k=g/(2\pi)$. Write
$H_m(s)=H_{n,g}(s,m)$ and $h_m(s)=h_{n,g}(s,m)$. On the original
natural angular domain define the Hilbert norm

$$
\begin{aligned}
\mathcal V_m&=D_m,\\
\|b\|_{\mathcal V_m}^2
 &=A[b]+m^2\int_J\frac{\sin^2a}{c(a)}|b|^2\,da+\|b\|_2^2,
\end{aligned}
\tag{22.1}
$$

where the middle term is omitted for $m=0$. Thus
$\mathcal V_0=\mathcal H_c$, and for every nonzero integer $m$,
$\mathcal V_m=\mathcal H_c\cap L^2(J,\sin^2a/c(a)\,da)$.
There is no angular endpoint condition beyond this finite energy.
By (18.6)--(18.7), choose an integer $M\ge0$ and a real $S>0$ such
that all nonpositive fibres have $|m|\le M$, $|s|\le S$. These
constants restrict the support of the negative spectral spaces;
they do not replace any angular space by a finite-dimensional one.

**Theorem 22.2 (a finite common range relative to negative energy).**
For every $\varepsilon>0$ and every integer $m$ with $|m|\le M$,
there are a finite-dimensional complex subspace
$R_m\subset\mathcal V_m$ and complex-linear maps
$K_m(s):L^2(J;\mathbb C)\to R_m$, $|s|\le S$, such that

$$
\|(I-K_m(s))u\|_{\mathcal V_m}
 \le\varepsilon\sqrt{-h_m(s)[u]}
\quad
\left(u\in\operatorname{Ran}\mathbf1_{(-\infty,0)}(H_m(s))\right).
\tag{22.2}
$$

The range $R_m$ is independent of $s$. The estimate includes every
real singular frequency and every multiplicity of a zero channel.

**Proof.** Fix $m$. Since $0\le q_n\le1$, the form norm of
$H_m(0)+k+1$ is equivalent to (22.1). Its fixed operator graph
domain $\mathcal G_m=D(H_m(0))$ embeds continuously in
$\mathcal V_m$: for $u\in\mathcal G_m$ the shifted form value is
bounded by
$(\|H_m(0)u\|_2+(k+1)\|u\|_2)\|u\|_2$.
The bounded polynomial perturbation

$$
H_m(z)=H_m(0)+2mz\sin a+z^2c(a),\qquad z\in\mathbb C,
\tag{22.3}
$$

has exactly this operator domain. Around each real $s_0$ choose
a fixed resolvent contour enclosing all negative eigenvalues of
$H_m(s_0)$ and its kernel, with its left real crossing below
$-k-1$ and its right real crossing positive and outside the
spectrum. Compact resolvent makes this a finite cluster. A
Neumann series on the contour, and the eigenvalue bound for a
bounded self-adjoint perturbation, show that for nearby real $s$
the same contour still encloses every negative eigenvalue.
The associated Riesz projection $E(z)$ is holomorphic. It is
holomorphic also from $L^2$ to $\mathcal G_m$, because, with
$B_m(z)=2mz\sin a+z^2c(a)$,

$$
H_m(0)(\zeta-H_m(z))^{-1}
 =\zeta(\zeta-H_m(z))^{-1}-I
       -B_m(z)(\zeta-H_m(z))^{-1}.
\tag{22.4}
$$

Consequently it is holomorphic into $\mathcal V_m$. On the real
interval it is the identity on the full strict negative space.

Expand $E(z)=\sum_{p\ge0}E_p(z-s_0)^p$ in the operator norm from
$L^2$ into $\mathcal G_m$. Each coefficient has finite rank.
Indeed $E_0$ has finite rank, and comparison of coefficients in
$E(z)^2=E(z)$ gives, for $p\ge1$,

$$
E_p=E_0E_p+E_pE_0+\sum_{1\le i<p}E_iE_{p-i}.
\tag{22.5}
$$

Induction proves the assertion, with all ranges in
$\mathcal G_m\subset\mathcal V_m$.

There are only finitely many real singular frequencies in
$[-S,S]$. At any such $s_0$, analytic Fredholm meromorphy applied
to (18.7) gives a finite-order pole bound

$$
\|H_m(s)^{-1}\|_{L^2\to L^2}
 \le C|s-s_0|^{-r}
\quad(0<|s-s_0|<\rho),
\tag{22.6}
$$

for some integer $r\ge1$ and finite $C,\rho>0$. Here $\rho$ is
small enough to exclude every other singular point. This is the
classical meromorphic-inverse conclusion of Dyatlov--Zworski,
[Theorem C.8, pp.521--522](https://math.mit.edu/~dyatlov/res/res_final.pdf),
already applied to this exact compact analytic pencil in (18.7).
For example, projecting onto $\ker H_m(s_0)$ reduces its possible
pole to the inverse of a finite analytic Schur matrix; its
determinant is not identically zero because nearby invertible
points exist. Thus no simple-crossing or genericity assumption
is involved. The self-adjoint spectral expansion in (22.6) gives

$$
-h_m(s)[u]\ge C^{-1}|s-s_0|^r\|u\|_2^2
\quad
\left(u\in\operatorname{Ran}\mathbf1_{(-\infty,0)}(H_m(s))\right).
\tag{22.7}
$$

Choose an integer $p$ with $p+1>r/2$. On a sufficiently small
fixed neighborhood of $s_0$ put
$K_m(s)=\sum_{i=0}^p E_i(s-s_0)^i$. Since $E(s)u=u$, its Taylor
remainder into $\mathcal V_m$ and (22.7) give

$$
\begin{aligned}
\|(I-K_m(s))u\|_{\mathcal V_m}
 &\le C_1|s-s_0|^{p+1}\|u\|_2\\
 &\le C_2|s-s_0|^{p+1-r/2}\sqrt{-h_m(s)[u]}.
\end{aligned}
\tag{22.8}
$$

Shrinking that neighborhood makes the last coefficient at most
$\varepsilon$. At $s=s_0$ itself, $K_m(s_0)=E(s_0)$ is exactly
the identity on the strict negative space. The left side of
(22.2) is then zero; no inverse at a singular point is used.

Remove these neighborhoods from $[-S,S]$. On the compact
remainder the inverse is uniformly bounded, so for some
$\gamma>0$ every strict negative vector satisfies
$-h_m(s)[u]\ge\gamma\|u\|_2^2$. The local projections above are
continuous from $L^2$ into $\mathcal V_m$. A finite cover by
sufficiently small intervals permits a piecewise choice
$K_m(s)=E(s_i)$ with
$\|E(s)-E(s_i)\|_{L^2\to\mathcal V_m}
\le\varepsilon\sqrt\gamma$ on each assigned piece. This proves
(22.2) on the remainder. If that remainder is empty this step is
unnecessary. At overlaps choose one of the finitely many available
formulas. No continuity of $K_m$ between pieces is required.

Let $R_m$ be the sum of the ranges of all the finitely many Taylor
coefficients and constant projections so used. It is a fixed
finite-dimensional subspace of $\mathcal V_m$, and all the maps
have range in it. Every choice depends only on
$n,g,m,\varepsilon$ and the fixed frequency interval, not on a
cylinder length. This proves (22.2). $\square$

**Theorem 22.3 (uniform bounded interface loss).** Under precisely
Definition 22.1's premises, there is a finite integer
$r_{n,g}\ge0$ such that, for every real $T\ge3$,

$$
0\le P_g(T)-D_g(T)\le r_{n,g}.
\tag{22.9}
$$

Consequently the subsidiary assertion (21.4) holds:

$$
D_g(T)=d_{n,g}T+O_{n,g}(1)\qquad(T\to\infty).
\tag{22.10}
$$

These statements use the strict negative complex index, every
integer angular mode, both natural angular endpoints, and every
fixed supercritical coupling, including those with zero channels.

**Proof.** Let $\mathcal N_T$ be the negative spectral space of
the exact periodic realization. Its dimension is $P_g(T)$, and
its vectors have finite Fourier expansions

$$
w_m(\ell)=T^{-1/2}\sum_j e^{is_j\ell}u_{m,j},
\qquad s_j=\frac{2\pi j}{T},\qquad
u_{m,j}\in\operatorname{Ran}
                 \mathbf1_{(-\infty,0)}(H_m(s_j)).
\tag{22.11}
$$

Only pairs with $|m|\le M$, $|s_j|\le S$ occur. For fixed $T$
there are finitely many such pairs, each with finite angular
rank, and every $u_{m,j}$ belongs to $\mathcal G_m$. In
particular these vectors have an actual
$\mathcal V=\bigoplus_{|m|\le M}\mathcal V_m$ valued seam trace
$\tau_Tw=(w_m(0))_m=(w_m(T))_m$. This assertion concerns only
$\mathcal N_T$ and does not assume a trace theorem on the entire
cylinder form domain.

Define the positive definite energy on this finite-dimensional
negative space by

$$
a_T(w)=-\mathcal Q_g[w]
       =\sum_{m,j}-h_m(s_j)[u_{m,j}].
\tag{22.12}
$$

Apply Theorem 22.2 with an $\varepsilon>0$ to be fixed below, and
put

$$
\begin{aligned}
F_Tw&=\left(T^{-1/2}\sum_j K_m(s_j)u_{m,j}\right)_m,\\
R&=\bigoplus_{|m|\le M}R_m,\qquad r=\dim_{\mathbb C}R,\\
X_T&=\ker(F_T|_{\mathcal N_T}).
\end{aligned}
\tag{22.13}
$$

Thus $\dim_{\mathbb C}X_T\ge P_g(T)-r$. The number $J_T$ of
available pairs in (22.11) satisfies
$J_T/T\le C_0=(2M+1)(S/\pi+1)$ for $T\ge1$. Triangle and
Cauchy--Schwarz inequalities give, using (22.2),

$$
\begin{aligned}
\|\tau_Tw-F_Tw\|_{\mathcal V}
 &\le\frac{\varepsilon}{\sqrt T}
             \sum_{m,j}\sqrt{-h_m(s_j)[u_{m,j}]}\\
 &\le\varepsilon\sqrt{C_0a_T(w)}.
\end{aligned}
\tag{22.14}
$$

For $w\in X_T$ its actual seam value $b=\tau_Tw$ therefore has
$\|b\|_{\mathcal V}\le\varepsilon\sqrt{C_0a_T(w)}$. The finite
codimension belongs to $X_T$ inside the periodic negative space;
the full angular trace space remains infinite-dimensional.

Choose a real smooth function $\eta$ on $[0,\infty)$ equal to one
near zero and supported in $[0,1)$. For $T\ge3$ set

$$
\chi_T(\ell)=\eta(\ell)+\eta(T-\ell),\qquad
(L_Tb)_m(\ell,a)=\chi_T(\ell)b_m(a).
\tag{22.15}
$$

This lift has the same value $b$ at the two log interfaces. It is
in the exact periodic positive-form closure by natural angular
core density and smooth longitudinal approximation. Since
$\chi_T$ is real, the magnetic cross term in its positive form
vanishes. That positive form is precisely the sum over $m$ of

$$
\begin{aligned}
&\left(\int_0^T\chi_T^2\,d\ell\right)
  \left(A[b_m]+m^2\int_J\frac{\sin^2a}{c(a)}|b_m|^2\,da\right)\\
&\hspace{12mm}+
 \left(\int_0^T|\chi_T'|^2\,d\ell\right)
                  \int_Jc(a)|b_m|^2\,da.
\end{aligned}
\tag{22.16}
$$

The two supports in (22.15) are disjoint and the two displayed
longitudinal integrals are fixed, independent of $T\ge3$.
Since $c\le1$ and the attractive potential only lowers the form,
there are finite positive constants $\alpha,\beta$, independent
of $T$, such that

$$
\|L_Tb\|_2\le\alpha\|b\|_{\mathcal V},\qquad
\mathcal Q_g[L_Tb]\le\beta\|b\|_{\mathcal V}^2.
\tag{22.17}
$$

The periodic operator $H_g^{\rm per}(T)$ is bounded below by
$-k$. Its spectral expansion on $\mathcal N_T$ gives
$\|H_g^{\rm per}(T)w\|_2^2\le k a_T(w)$. For $w\in X_T$, put
$b=\tau_Tw$ and $z=w-L_Tb$. The form representation identity
applies because $w$ is in the operator domain and $L_Tb$ is in
the form domain. Equations (22.14) and (22.17) imply

$$
\begin{aligned}
\mathcal Q_g[z]
 &=-a_T(w)-2\operatorname{Re}
       \langle H_g^{\rm per}(T)w,L_Tb\rangle
                           +\mathcal Q_g[L_Tb]\\
 &\le\left(-1+2\alpha\sqrt{kC_0}\,\varepsilon
                         +\beta C_0\varepsilon^2\right)a_T(w).
\end{aligned}
\tag{22.18}
$$

Choose $\varepsilon>0$ once so that this bracket is at most
$-1/2$, and take the spaces in Theorem 22.2 for that choice.
Thus $w\mapsto z$ is complex-linear, strictly negative on every
nonzero $w\in X_T$, and injective. No negative spectral gap has
been assumed, and no margin depends on $T$.

It remains to check the exact Dirichlet closure. The transformed
vector has the finite expansion

$$
z_m(\ell)=T^{-1/2}\sum_j
                (e^{is_j\ell}-\chi_T(\ell))u_{m,j}.
\tag{22.19}
$$

Every scalar factor is smooth and vanishes at both endpoints,
since $e^{is_jT}=1$. It is therefore approximable in
$H^1(0,T)$ by $C_c^\infty(0,T)$. Each angular coefficient is
approximable in $\mathcal V_m$ by $C_c^\infty(J)$, by (18.5)
and its $m=0$ counterpart. The tensor map is continuous into the
positive cylinder form norm: for its magnetic term,

$$
\int_0^T\int_Jc|f'u+im\tan(a)fu|^2
 \le2\|f'\|_2^2\|u\|_2^2
       +2m^2\|f\|_2^2
                    \int_J\frac{\sin^2a}{c(a)}|u|^2\,da,
\tag{22.20}
$$

and its angular term is $\|f\|_2^2A[u]$. Thus finite tensor
approximation places every $z$ in precisely the original
longitudinal Dirichlet positive-form closure, without an added
condition at either angular endpoint.

The image of $X_T$ is consequently a complex strictly negative
Dirichlet subspace of dimension at least $P_g(T)-r$. The classical
strict form-index principle, Teschl,
[Theorems 4.10 and 4.12(i), p.119](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
gives $D_g(T)\ge P_g(T)-r$. Together with the supplied
$D_g(T)\le P_g(T)$, this proves (22.9) with $r_{n,g}=r$.
If the existing periodic estimate is
$|P_g(T)-d_{n,g}T|\le C_P$ for $T\ge T_P$, then

$$
|D_g(T)-d_{n,g}T|\le C_P+r_{n,g}
\qquad(T\ge\max\{3,T_P\}),
\tag{22.21}
$$

which proves (22.10) with all its stated quantifiers.

For a direct application let
$\tau_j=\inf\{T>0:D_g(T)\ge j\}$, for positive integers $j$.
Zero extension preserves the compact Dirichlet core, its
positive form and its $L^2$ norm, and hence extends to its
defining closure. It follows that $D_g(T)$ is nondecreasing.
Write $d=d_{n,g}>0$ and let $C,T_0$ be constants in (22.21).
For every $j$ with $(j-C-1)/d\ge T_0$, the lower bracket has
$D_g((j-C-1)/d)\le j-1$, and the upper bracket has
$D_g((j+C+1)/d)\ge j+1$. Monotonicity therefore gives

$$
\frac{j-C-1}{d}\le\tau_j\le\frac{j+C+1}{d},\qquad
\left|\tau_j-\frac jd\right|\le\frac{C+1}{d}.
\tag{22.22}
$$

This consequence assumes no attainment of the infimum. It uses
the new bounded remainder, rather than merely its existing
density limit. $\square$

**Definition 22.4 (the separate original-count comparison).**
The analytic Fredholm meromorphy, contour calculus and strict
form-index principle used above are classical intermediates in
the stated realizations. The energy-weighted common-range
construction and its seam cancellation are deductions for the
unchanged forms (18.8). Their constants need not be uniform in
$n$ or $g$, and no optimality or literature-priority assertion is
made.

For the original operator (21.1), the independent comparison
problem remains: for each integer $n\ge2$ and each fixed
$g>\lambda_n$, do there exist finite $B_{n,g}\ge0$ and
$E_{n,g}\in(0,1)$ such that

$$
\left|N_{n,g}(E)
       -D_g\left(\tfrac12\log(1/E)\right)\right|
 \le B_{n,g}
\qquad(0<E<E_{n,g})?
\tag{22.23}
$$

This comparison retains the full original Friedrichs domain,
central derivatives, complete-source potential, interfaces and
soft spectral wall in (21.5), every integer mode, both natural
angular endpoints and all zero-channel couplings. It is not a
consequence of (22.9). If (22.23) is established independently,
(22.21) and $L_{n,g}=d_{n,g}/2$ give (21.3) with error at most
$B_{n,g}+C$ for sufficiently small $E$. The potential-tail
estimates alone do not supply (22.23).

## 追加锚（本行以下为增补区）
## 23. Bounded original-count transfer by localized energy cancellation

**Definition 23.1 (the original realization and localized observations).**
All statements in this section are ordinary conditional analysis under
exactly Definition 18.1's analytic hypotheses. Retain the original
identity unit source, complete marginal, raw measures, heat clock,
horizontal and central fields, free/Friedrichs closure, and strict
complex count in (21.1). Retain the full cylinder form (18.8), its
positive-form closures, every integer angular mode, and both natural
angular endpoints. Fix an integer $n\ge2$ and a real $g>\lambda_n$;
write $k=g/(2\pi)$ and $d=d_{n,g}=2L_{n,g}>0$. No constant below
is asserted uniform in $n$ or $g$.

Use $H_m(s),h_m(s),\mathcal V_m,\mathcal G_m$ from (22.1)--(22.4).
Thus $\mathcal G_m=D(H_m(0))$, $\mathcal G_m\hookrightarrow\mathcal V_m$,
and on this fixed operator domain

$$
H_m(z)=H_m(0)+2mz\sin a+z^2c(a),\qquad z\in\mathbb C.
\tag{23.1}
$$

For a cylinder of length $L$, let $Q_L$ and $H_L$ denote its exact
periodic form and operator. Its longitudinal frequencies are
$s_j=2\pi j/L$; its strict negative dimension is $P_g(L)$.
The bounds $H_m(s)\ge-k$ and $H_L\ge-k$ follow from the nonnegative
homogeneous form and $0<q_n\le1$.

For every finite $\Lambda\ge0$, an angular eigenvector of energy
at most $\Lambda$ has homogeneous positive energy at most
$k+\Lambda$. Applying (18.6) with this bound shows that only
finitely many $m$ and a bounded interval of real $s$ can contribute.
Their spectral ranks are uniformly finite because
$h_m(s)\ge A-k$. For those $m$, analytic Fredholm meromorphy in
(18.7) and its supplied invertible real point give finitely many
real singular frequencies. At each such $s_0$ there are finite
$C,r,\rho>0$, with $r$ an integer, such that

$$
\begin{aligned}
\|H_m(s)^{-1}\|&\le C|s-s_0|^{-r},
 &&0<|s-s_0|<\rho,\\
|h_m(s)[u]|&\ge C^{-1}|s-s_0|^r\|u\|_2^2,
 &&u\text{ in either strict sign spectral space}.
\end{aligned}
\tag{23.2}
$$

The second line follows by the spectral theorem, separately on
each sign space. For the positive space we use it only below a
fixed finite energy cutoff. At $s=s_0$ no inverse is taken.
These are uses of the same classical analytic Fredholm theorem
as (18.7), not a longitudinal comparison theorem.

The exact gauge $v_m=e^{-ima/2}w_m$ changes the original central
expression into

$$
\begin{aligned}
\mathcal C_m(s)u
 &=4cu'+\{2\sin a(is-1)-2imc\}u,\\
\mathcal C_m(\partial_x)
 &=2\sin a(\partial_x-1)+4c\partial_a-2imc.
\end{aligned}
\tag{23.3}
$$

For a fixed finite set of $m$, these are bounded maps
$\mathcal V_m\to L^2(J)$, locally uniformly in $s$; the derivative
bound uses $c^2\le c$. Define

$$
\begin{aligned}
\mathcal Y_m
 &=\mathcal V_m\oplus
   L^2((0,\infty),e^{-2t}dt;L^2(J))^{\oplus3},\\
\mathcal O_m(z)u
 &=(u,e^{izt}u,e^{izt}\mathcal C_m(z)u,e^{-izt}u).
\end{aligned}
\tag{23.4}
$$

The map $\mathcal O_m(z):\mathcal V_m\to\mathcal Y_m$ is
holomorphic for $|\operatorname{Im}z|<1$. On a smaller closed strip,
every power of $t$ arising from differentiation is integrable
against the displayed exponential weight, uniformly on compact
$z$ sets. A mass observation below means just the second and
fourth components, with any fixed scalar factor allowed.

**Theorem 23.2 (localized observations relative to strict energy).**
For every $\delta>0$ there is a finite $r_-$ independent of $L\ge3$
and a complex subspace $X_L$ of the full strict negative space of
$H_L$, of codimension at most $r_-$ in that space, such that,
with $a_L(w)=-Q_L[w]$,

$$
\begin{aligned}
\|w(0)\|_{\oplus_m\mathcal V_m}^2
 &+\sum_m\int_0^L e^{-2x}
       \bigl(\|w_m(x)\|_2^2+
        \|\mathcal C_m(\partial_x)w_m(x)\|_2^2\bigr)\,dx\\
 &+\sum_m\int_0^L e^{-2(L-x)}\|w_m(x)\|_2^2\,dx
 \le\delta^2a_L(w),\qquad w\in X_L.
\end{aligned}
\tag{23.5}
$$

The seam is periodic: $w(0)=w(L)$. For each finite $\Lambda>0$,
the analogous mass-only assertion holds on
$\operatorname{Ran}\mathbf1_{(0,\Lambda)}(H_L)$, with $Q_L[w]$
as energy and a finite codimension independent of $L\ge1$.
Its constants may depend on $\Lambda$. Both assertions include
all zero-channel couplings and exactly singular grid frequencies.

**Proof.** For each contributing $m$ and each real $s_0$ in its
compact frequency interval, choose a fixed resolvent contour
enclosing every eigenvalue in $[-k,\Lambda]$, with its right
real crossing strictly above $\Lambda$ and outside the spectrum.
For the negative assertion use $\Lambda=0$. Nearby the associated
Riesz projection $E(z)$ is holomorphic and is the identity on
every spectral vector under consideration. It is holomorphic
from $L^2$ into $\mathcal G_m$: writing
$B(z)=H_m(z)-H_m(0)$, the identity

$$
H_m(0)(\zeta-H_m(z))^{-1}
 =\zeta(\zeta-H_m(z))^{-1}-I-B(z)(\zeta-H_m(z))^{-1}
\tag{23.6}
$$

gives this graph norm assertion by contour integration.
If $E(z)=\sum_{p\ge0}E_p(z-s_0)^p$, all $E_p$ have finite rank
into $\mathcal G_m$. Indeed $E(z)^2=E(z)$ gives

$$
E_p=E_0E_p+E_pE_0+\sum_{1\le i<p}E_iE_{p-i},
\tag{23.7}
$$

and induction proves the claim. Every Taylor coefficient of
$\mathcal O_m(z)E(z):L^2\to\mathcal Y_m$ consequently has finite
rank: each is a finite sum of bounded coefficients of
$\mathcal O_m(z)$ composed with finite-rank coefficients of $E$.

Near a singular $s_0$, truncate this series at $p$ with
$p+1>r/2$, using (23.2). On either relevant strict sign space
the remainder is at most

$$
C_1|s-s_0|^{p+1}\|u\|_2
 \le C_2|s-s_0|^{p+1-r/2}\sqrt{|h_m(s)[u]|}.
\tag{23.8}
$$

Shrink the fixed neighborhood to make this at most
$\varepsilon\sqrt{|h_m(s)[u]|}$. At $s=s_0$ the zeroth Taylor
value equals the exact observation on the chosen cluster,
so its error is zero. On the compact complement of these
neighborhoods the inverse is uniformly bounded; a finite cover
and constant approximations to the continuous finite-rank maps
$\mathcal O_m(s)E(s)$ give the same estimate. Choose one formula
on overlaps. There is thus a finite common range
$R_m\subset\mathcal Y_m$ and linear maps $K_m(s)$ into $R_m$ with

$$
\|\mathcal O_m(s)u-K_m(s)u\|_{\mathcal Y_m}
 \le\varepsilon\sqrt{|h_m(s)[u]|}.
\tag{23.9}
$$

The range is the sum of finitely many coefficient and projection
ranges. It is independent of $L$. The chosen $K_m(s)$ need not
be continuous. This also proves the mass-only version.

Write a periodic low-energy vector as

$$
w_m(x)=L^{-1/2}\sum_j e^{is_jx}u_{m,j},\qquad s_j=2\pi j/L.
\tag{23.10}
$$

Its sum is finite. The number of contributing pairs $(m,j)$ is
at most $C_*L$ for $L\ge1$, for a fixed $C_*$. Restrict (23.4)
to $0\le t\le L$ and use $t=L-x$ for the right-end mass.
The identity $e^{is_jL}=1$ gives exactly the observations in
(23.5). Restriction is a contraction in the weighted spaces.
Replace $\mathcal O_m(s_j)u_{m,j}$ by $K_m(s_j)u_{m,j}$ in the
same Fourier sum, followed by this restriction; call the resulting
map $F_L$. Its rank is at most $\sum_m\dim R_m$.
Triangle and Cauchy--Schwarz give

$$
\|\mathcal J_Lw-F_Lw\|
 \le\varepsilon\sqrt{C_*a_L(w)}.
\tag{23.11}
$$

Here $\mathcal J_L$ denotes the full observation, or the mass-only
one; on the positive low-energy space set $a_L(w)=Q_L[w]$.
Choosing $\varepsilon$ and imposing the finitely many linear
constraints $F_Lw=0$ proves both claims. The full angular trace
space has not been assigned finite dimension. Strict energy, rather than a uniform negative or positive gap, controls the
error, including every finite-order zero in (23.2). $\square$

**Theorem 23.3 (bounded extra index from two exponential ends).**
For every fixed $C\ge0$ there is a finite $R_C$ such that, for
every real $L\ge1$ and every measurable real multiplier with

$$
0\le V_L(x,a,\theta)
 \le C\{e^{-2x}+e^{-2(L-x)}\},
\tag{23.12}
$$

the periodic form satisfies

$$
\operatorname{ind}_-\left(Q_L-\int V_L|w|^2\right)
 \le P_g(L)+K_0+R_C,
\tag{23.13}
$$

where $K_0<\infty$ is independent of $L$. The same upper bound
holds on the original longitudinal Dirichlet cylinder domain.
The multiplier need not preserve angular modes.

**Proof.** The kernel rank of $H_L$ is uniformly bounded. All its
contributions occur at the finitely many real singular frequencies
and angular integers identified above. For a fixed root and $L$
there is at most one $j$ with $2\pi j/L$ equal to that root;
each root has finite kernel dimension. Take $K_0$ to be the sum
of these dimensions, including every exact resonance.

Remove the strict negative space and this kernel. On the remaining
positive spectral space decompose $w=w_{\rm lo}+w_{\rm hi}$ at
energy $\Lambda$, orthogonally for both $L^2$ and $Q_L$. Then

$$
\|w_{\rm hi}\|_2^2\le\Lambda^{-1}Q_L[w_{\rm hi}].
\tag{23.14}
$$

Choose $\Lambda$ so large that $2C/\Lambda<1/4$. The low part
has the finite mode/frequency support already proved. Apply the
mass-only part of Theorem 23.2, scaled by $\sqrt C$, to the
observation

$$
\mathcal J_L^0w
 =(\sqrt C e^{-x}w(x),\sqrt C e^{-t}w(L-t))
\tag{23.15}
$$

in ordinary $L^2$ on each component. Impose its finite-rank
constraints on $w_{\rm lo}$, hence on $w$, so that
$\|\mathcal J_L^0w_{\rm lo}\|\le\beta\sqrt{Q_L[w_{\rm lo}]}$
with $\beta^2<1/4$. The high part obeys
$\|\mathcal J_L^0w_{\rm hi}\|\le\sqrt{2C/\Lambda}
\sqrt{Q_L[w_{\rm hi}]}$. Triangle and Cauchy--Schwarz yield

$$
\int V_L|w|^2
 \le\|\mathcal J_L^0w\|^2
 \le(\beta^2+2C/\Lambda)Q_L[w]<\tfrac12Q_L[w].
\tag{23.16}
$$

Thus the perturbed form is nonnegative on a space of codimension
at most $P_g(L)+K_0+R_C$. A strict negative space intersects it
only at zero, proving (23.13). The Dirichlet domain embeds in
the periodic domain by its defining closure. Arbitrarily small
positive eigenvalues were controlled by (23.2)--(23.11); all
high energies, angular integers and frequencies were controlled
by (23.14). This is an explicit index argument for (23.12).
$\square$

**Theorem 23.4 (the original bounded count and cylinder transfer).**
For every integer $n\ge2$ and every fixed real $g>\lambda_n$,
there exist finite $B_{n,g}\ge0$ and $E_0\in(0,1)$ such that

$$
\left|N_{n,g}(E)-D_g\!\left(\tfrac12\log(1/E)\right)\right|
 \le B_{n,g},\qquad 0<E<E_0.
\tag{23.17}
$$

This establishes the original comparison (22.23). In particular
the original count satisfies (21.3), under the same unchanged
analytic hypotheses and original realization.

**Proof.** Choose once and for all
$a_0\ge\max(0,\ell_n)$ from (20.19), and put
$T=\tfrac12\log(1/E)$. Denote the original form by
$q_{\rm orig}=T_1-gW_{n,1}$. The raw polar substitution and gauge
give, for compact longitudinal support or the zero-extended
Dirichlet constructions below,

$$
\begin{aligned}
d\xi&=\tfrac14e^{4\ell}\,d\ell\,da\,d\theta,
&4\|f\|_2^2&=\sum_m\int e^{2\ell}|w_m|^2,\\
4\{q_{\rm orig}[f]+E\|f\|_2^2\}
 &=Q_g[w]+\sum_m\int e^{-2\ell}
                  |\mathcal C_m(\partial_\ell)w_m|^2\\
 &\quad-g\int B_n(\ell,a,\theta)|v|^2
       +\sum_m\int Ee^{2\ell}|w_m|^2.
\end{aligned}
\tag{23.18}
$$

Here $v_m=e^{-ima/2}w_m$. The central multiplier $-2imc$ in
(23.3) is retained. The horizontal cross term is integrated with
zero longitudinal trace, exactly as in (18.13). The full-field
estimate (20.19)--(20.23) supplies

$$
\left|g\int B_n|v|^2\right|
 \le gC_n\int e^{-2\ell}|v|^2.
\tag{23.19}
$$

This bound uses the full complex multiplication form, allowing
angular mixing; the gauge preserves the integrated angular norm.
The coordinate map is used with the weighted mass identity in
(23.18) and the following explicit form-domain correspondences.

An original free-domain vector localized into a compact exterior
log interval maps into the exact natural homogeneous Dirichlet
cylinder domain. On the original compact smooth core the polar
identity gives the nonnegative homogeneous norm as four times
the localized horizontal energy. On this exterior support the
cylinder $L^2$ norm is bounded by the original one. Original
core convergence therefore gives homogeneous form convergence;
Fourier truncation, the natural angular cutoffs of (18.5), and
longitudinal smoothing give precisely the defining cylinder
closure, as in the argument following (18.17). The same core
limit on a half-cylinder starting at $\ell\ge a_0$ permits the
exterior upper estimates below; the weighted mass identity and
nonnegative homogeneous identity pass to those limits.

For the converse needed in the lower estimate, consider finite
sums $z_m(x)=\sum_j\phi_{m,j}(x)u_{m,j}$ with finitely many $m$,
$u_{m,j}\in\mathcal V_m$, and smooth scalar factors vanishing
at $0,L$. Approximate the factors in $H^1_0(0,L)$ and the angular
coefficients in $\mathcal V_m$ by their supplied compact smooth
cores. For a tensor, the magnetic square is bounded by

$$
\begin{aligned}
\int c|\phi'u+im\tan a\,\phi u|^2
 &\le2\|\phi'\|_2^2\|u\|_2^2
   +2m^2\|\phi\|_2^2\int_J\frac{\sin^2a}{c}|u|^2,\\
\|\mathcal C_m(\partial_x)(\phi u)\|_2
 &\le C_m(\|\phi'\|_2+\|\phi\|_2)\|u\|_{\mathcal V_m}.
\end{aligned}
\tag{23.20}
$$

The angular term is $\|\phi\|_2^2A[u]$, and
$\|cu'\|_2^2\le\int c|u'|^2$. These estimates give convergence
in the homogeneous positive norm and, after translation into
the fixed finite interval $[a_0,a_0+L]$, in the full original
free norm: the weights $e^{2\ell}$ and $e^{-2\ell}$ are bounded
there. Undoing the gauge and coordinates for the compact smooth
approximants gives actual compact smooth Cartesian functions,
supported away from the pole and both axes. Zero extension across
the longitudinal endpoints therefore belongs to the original
$\mathcal H_1$. Equations (23.18)--(23.19) pass to these limits
by the same approximants and closedness. Constants for this
density step may depend on the fixed $L$; a uniform approximation
rate or additional angular trace is not required.

For the lower index bound, take $L_-=T-a_0\ge3$ and the entire
periodic strict negative space of that length. On the subspace
$X_{L_-}$ from Theorem 23.2, write $a(w)=-Q_{L_-}[w]$ and
$b=w(0)=w(L_-)$. Fix a real smooth $\eta$ equal to one near zero
and supported in $[0,1)$, and put

$$
\chi_L(x)=\eta(x)+\eta(L-x),\qquad l_b=\chi_Lb,\qquad z=w-l_b.
\tag{23.21}
$$

The fixed-width supports are disjoint for $L\ge3$. Natural angular
density makes $l_b$ a periodic form-domain vector. There are
constants $A_1,A_2,A_3$ independent of $L$ with

$$
\|l_b\|_2\le A_1\|b\|_{\oplus_m\mathcal V_m},\qquad
Q_L[l_b]\le A_2\|b\|_{\oplus_m\mathcal V_m}^2.
\tag{23.22}
$$

The joint norm of its three localized mass/central observations
in (23.5) is at most $A_3\|b\|_{\oplus_m\mathcal V_m}$.
These estimates follow from the fixed supports of $\chi_L,\chi_L'$
and (23.3), with $m$ in its fixed negative-energy set. The magnetic
cross term between real $\chi_L'$ and $im\tan a\,\chi_L$ has
zero real part. They are the same real seam lift bounds as
(22.16)--(22.17), with its additional localized observations.

The spectral bound $H_L\ge-k$ gives
$\|H_Lw\|_2^2\le k a(w)$. The form representation identity yields

$$
\begin{aligned}
Q_L[z]
 &=-a(w)-2\operatorname{Re}\langle H_Lw,l_b\rangle+Q_L[l_b]\\
 &\le\{-1+2A_1\sqrt{k}\delta+A_2\delta^2\}a(w).
\end{aligned}
\tag{23.23}
$$

Each scalar factor $e^{is_jx}-\chi_L(x)$ in $z$ vanishes at both
ends. The converse construction above makes its translated inverse
transform an original free-domain vector $f_z$, extended by zero.
For $\ell=a_0+x$ and $L=T-a_0$, the exact wall is
$Ee^{2\ell}=e^{-2(L-x)}$. By (23.5), (23.19), and the lift bounds,
the central norm, possible positive correction, and soft wall
in (23.18) for $z$ sum to at most
$C_1(1+A_3)^2\delta^2a(w)$, where

$$
C_1=\max\{e^{-2a_0},gC_ne^{-2a_0},1\}.
\tag{23.24}
$$

Choose $\delta>0$ once so that
$2A_1\sqrt{k}\delta+\{A_2+C_1(1+A_3)^2\}\delta^2<1/2$.
Then

$$
4\{q_{\rm orig}[f_z]+E\|f_z\|_2^2\}\le-\tfrac12a(w)<0.
\tag{23.25}
$$

The linear map $w\mapsto f_z$ is injective, since a nonzero
kernel vector would contradict this strict inequality. The
strict complex form-index principle gives

$$
N_{n,g}(E)\ge P_g(T-a_0)-r_-.
\tag{23.26}
$$

For the upper bound, let a smooth $\vartheta$ be zero on
$(-\infty,0]$, equal to $\pi/2$ on $[1,\infty)$, and have bounded
derivative. For a fixed $b_0\ge0$ to be chosen, use

$$
\begin{aligned}
\chi_{\rm in}&=\cos\vartheta(\ell-a_0),\\
\chi_{\rm out}&=\sin\vartheta(\ell-(T+b_0)),\\
\chi_{\rm mid}&=\sin\vartheta(\ell-a_0)
                  \cos\vartheta(\ell-(T+b_0)).
\end{aligned}
\tag{23.27}
$$

For large $T$ the two transition intervals are disjoint, and
$\sum\chi_j^2=1$ exactly. These are smooth original-free-domain
multipliers, constant near the pole. With $S_T=\sum|\partial_\ell\chi_j|^2$,

$$
S_T\le C_\chi\{
\mathbf1_{[a_0,a_0+1]}+\mathbf1_{[T+b_0,T+b_0+1]}\}.
\tag{23.28}
$$

The original IMS identity (18.16) has the exact multiplier

$$
I_T=S_T\left(\frac c{R^2}+\frac{4\sin^2a}{R^4}\right).
\tag{23.29}
$$

Allocate its error to the three components using $\sum\chi_j^2=1$.
After multiplication by four and the polar substitution the
cylinder multiplier is exactly $S_T\{c+4e^{-2\ell}\sin^2a\}$,
bounded by $5C_\chi$ on the exterior transitions.

The inner component has support in a fixed bounded gauge ball;
only the fixed left transition contributes to its allocated
error. On a fixed slightly larger bounded Dirichlet region its
modified form $q_{\rm orig}-\int I_T|f|^2$ has finite negative
index $K_{\rm in}$ independent of $E,T$. Indeed (15.11)--(15.12)
give an equivalent shifted original free norm, (15.9) gives local
Euclidean $H^1$ control, and Rellich compactness gives compact
form embedding on this bounded region. The modification is a
fixed bounded multiplier away from the pole. Adding
$E\|f\|_2^2$ cannot increase $K_{\rm in}$.

The middle component has Dirichlet log support
$(a_0,T+b_0+1)$, of length $L_+=T+b_0+1-a_0$.
Its original domain maps into the natural homogeneous Dirichlet
domain proved above. Drop the nonnegative central and wall terms
for a lower form bound. Equations (23.19), (23.28)--(23.29) give
the comparison $Q_g-\int V_{L_+}|w|^2$, where, with $x=\ell-a_0$,

$$
\begin{aligned}
V_L(x)&=gC_ne^{-2a_0}e^{-2x}
 +5C_\chi\{\mathbf1_{[0,1]}(x)+\mathbf1_{[L-1,L]}(x)\}\\
&\le C_2\{e^{-2x}+e^{-2(L-x)}\},\qquad
C_2=gC_ne^{-2a_0}+5e^2C_\chi.
\end{aligned}
\tag{23.30}
$$

Theorem 23.3 bounds its strict negative index by
$P_g(L_+)+K_0+R_{C_2}$. Every angular mode remains in this upper
comparison, including the high-energy part of (23.14).

On the outer support $\ell\ge T+b_0$ the wall is at least
$e^{2b_0}$. The homogeneous form is at least $-k$ times the
cylinder norm, the correction is at least
$-gC_ne^{-2a_0}$ times that norm, and the allocated IMS error
is at least $-5C_\chi$ times it. Choose $b_0$ once so that

$$
e^{2b_0}\ge k+gC_ne^{-2a_0}+5C_\chi+1.
\tag{23.31}
$$

After dropping the nonnegative central norm, the outer allocated
shifted form is nonnegative. The half-cylinder core limit already
proved gives this inequality on the original exterior closure.

The partition map is injective, and the sum of its allocated
shifted forms equals $q_{\rm orig}+E\|\cdot\|_2^2$. Project the
inner component onto the fixed modified operator's negative
space, and the transformed middle component onto the periodic
comparison form's negative space. This projection is injective
on any strictly negative original subspace: in its kernel the
inner form, middle lower comparison and outer form would all
be nonnegative. The middle Dirichlet-to-periodic domain inclusion
justifies its projection. This form-domain dimension argument gives

$$
N_{n,g}(E)\le K_{\rm in}+P_g(T+b_0+1-a_0)+K_0+R_{C_2}.
\tag{23.32}
$$

Finally choose $C_P,C_D$ for the supplied bounds
$|P_g(L)-dL|\le C_P$ and $|D_g(L)-dL|\le C_D$ for large lengths.
Increase a fixed $T_0>0$ so that all preceding constructions and
length thresholds apply for $T>T_0$. Equations (23.26), (23.32) give

$$
\begin{aligned}
dT-C_-&\le N_{n,g}(e^{-2T})\le dT+C_+,\\
C_-&=da_0+C_P+r_-,\\
C_+&=d|b_0+1-a_0|+C_P+K_{\rm in}+K_0+R_{C_2}.
\end{aligned}
\tag{23.33}
$$

Thus (23.17) holds with
$B_{n,g}=\max(C_-,C_+)+C_D$ and $E_0=e^{-2T_0}\in(0,1)$.
All lengths and energies are real; the argument proves the bound
for every $0<E<E_0$. Since $d=2L_{n,g}$, (23.33) also proves
the original remainder (21.3). $\square$

**Application 23.5 (original logarithmic threshold placement).**
Write the original negative eigenvalues as $-\varepsilon_j$,
with $\varepsilon_j>0$ nonincreasing to zero and repeated with
complex multiplicity, and put $t_j=\tfrac12\log(1/\varepsilon_j)$.
The strict convention is

$$
N_{n,g}(e^{-2T})=\#\{j:t_j<T\}.
\tag{23.34}
$$

If $|N_{n,g}(e^{-2T})-dT|\le C$ for large $T$, then for all
sufficiently large $j$,

$$
\frac{j-C-1}{d}\le t_j\le\frac{j+C+1}{d},\qquad
\log(1/\varepsilon_j)=\frac j{L_{n,g}}+O_{n,g}(1).
\tag{23.35}
$$

The lower bracket has count at most $j-1$ and the upper bracket
at least $j+1$, proving these inequalities with the strict
counting convention and every multiplicity retained. This is a
direct inversion application of (23.33).

The localized finite-rank estimates (23.9)--(23.16) supply the
joint original-domain comparison missing from potential decay
and the cylinder remainder alone. Their strict-energy control
is used for the full central/wall lower estimate, while their
positive-space version bounds the extra upper index. The joint original-domain comparison is repo-derived. Classical
analytic Fredholm meromorphy, Riesz calculus, the strict form-index
principle and local Rellich compactness are reused in their stated
realizations. The estimates require no equivalence to a separated
Euclidean kinetic operator or additional gap or endpoint premise.
Their constants depend on the fixed parameters; no parameter-uniform
bound or rate optimality follows.

## 追加锚（本行以下为增补区）

## 24. Natural channel isolation and the original-domain phase boundary

**Definition 24.1 (fixed realization and reused suppliers).**
For every integer $n\ge2$, use precisely Definition 18.1 of the
[original source](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md), with
its definitions and analytic suppliers as stated at revision
[d6d829c43b0ed4f127a09666bc40088b6f440b94](https://github.com/the-omega-institute/trureturing/blob/d6d829c43b0ed4f127a09666bc40088b6f440b94/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md).
Thus the source is the identity unit source, the time integral and
unweighted omitted-coordinate marginal are complete, measures are raw,
the heat clock has covariance $2$, and $\epsilon=1$. The horizontal
and central fields, units, free closure and Friedrichs realization
are unchanged. In particular, on complex $L^2(\mathbb R^3,d\xi)$,

$$
\begin{aligned}
\mathcal H_1&=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^{\,
 (\|f\|_2^2+\|Uf\|_2^2+\|Vf\|_2^2+\|Zf\|_2^2)^{1/2}},\\
q_{\rm orig}&=T_1-gW_{n,1},\qquad D(q_{\rm orig})=\mathcal H_1,
\qquad \mathscr A=A_{n,1,g}.
\end{aligned}
\tag{24.1}
$$

Here $\mathscr A$ is the operator associated with the original form;
its operator domain $D(\mathscr A)$ is distinct from $\mathcal H_1$.
The analytic assumptions are exactly those listed in Definition 18.1:
Theorem 10.2's original-field formulas and locally uniform off-pole
convergence, the full complex polar identity (12.12)--(12.13), the
closed natural angular form and compact embedding supplied by V,
Theorem 10.2 at the revision fixed in Definition 1.1, natural-core
approximation (13.6)--(13.8), complete-field scaling (14.9), and the
original closed form, compact smooth core and local estimates
(15.9)--(15.12). Suppliers C and V retain their statements at
5cec4fa83ae7bbb4e787c42606525db4cd11ed48, as fixed in Definition 1.1.
They are conditional analytic suppliers here.

Write $J=(-\pi/2,\pi/2)$, $c(a)=\cos a$, $q=q_n$ as in (20.3),
$\mu=\mu_n$, $\lambda_n=2\pi\mu$, and

$$
\begin{aligned}
\mathcal H_c&=\{b\in L^2(J;\mathbb C):b\in AC_{\rm loc}(J),
                                     \ \sqrt c\,b'\in L^2(J)\},\\
A[b]&=\int_J(4c|b'|^2+c|b|^2)\,da,\qquad
Q[b]=\int_Jq|b|^2\,da,\qquad C[b]=\int_Jc|b|^2\,da,\\
B[b]&=A[b]-\mu Q[b],\qquad k=\frac g{2\pi},\qquad h[b]=A[b]-kQ[b].
\end{aligned}
\tag{24.2}
$$

All unweighted angular norms below are complex $L^2(J,da)$ norms.
In particular $0<q_*\le q\le1$ and $A\ge\lambda_0\|\cdot\|_2^2$
with $\lambda_0>0$. The pencil is exactly (18.1), on
$D_0=\mathcal H_c$ and
$D_m=\mathcal H_c\cap L^2(J,\sin^2a/c\,da)$ for every nonzero
integer $m$. No endpoint value is prescribed. Every rank and
multiplicity in this section is complex.

Reuse Theorem 15.2's original discreteness and lower semiboundedness,
the bounded-frequency assertion (18.6), the complete-source estimate
(20.19), and the exact original identities and natural form-domain
correspondences (23.18)--(23.20). Also reuse (23.17), (23.33) and
(23.35); in particular, for fixed $n,g>\lambda_n$,

$$
N_{n,g}(E)=L_{n,g}\log(1/E)+O_{n,g}(1),\qquad
 t_j-\frac{j}{2L_{n,g}}=O_{n,g}(1),\quad
 t_j=\tfrac12\log(1/\varepsilon_j).
\tag{24.3}
$$

Here $-\varepsilon_j$ are all original negative eigenvalues in the
order and with the multiplicities of (23.34). These are reused
bounded count and placement results, without a phase-convergence
conclusion. All subsequent assertions remain conditional on the
unchanged analytic suppliers above.

**Lemma 24.2 (near-threshold isolation in every integer mode).**
For every integer $n\ge2$ there exists a finite
$g_n^{\rm iso}>\lambda_n$ such that for every fixed
$g\in(\lambda_n,g_n^{\rm iso})$ there is $s=s_{n,g}>0$ with

$$
\nu_{n,g}(\sigma,m)=
\begin{cases}
1,&m=0,\ |\sigma|<s,\\
0,&\text{otherwise},
\end{cases}
\qquad d_{n,g}=\frac s\pi,\qquad L_{n,g}=\frac{s}{2\pi}.
\tag{24.4}
$$

At each root $\sigma=\pm s$ the pencil kernel has complex dimension
one and the corresponding eigenvalue has nonzero derivative. For all
$m\ne0$ and all real $\sigma$ there is a common strictly positive
unweighted angular lower bound. The threshold $g_n^{\rm iso}$ asserts
channel isolation only; it is not a threshold for a full geometric
phase law.

Proof. Fix $n$. The definition of $\mu$ gives $B\ge0$, and attainment
supplies a nonzero kernel vector. Since $q$ is bounded, closedness and
compact embedding of $A$ imply compact resolvent for $B$. The modulus
chain rule preserves $Q$ and cannot increase $A$, so there is a
nonnegative real kernel vector $b_0$. Its interior equation is

$$
-4(cb_0')'+(c-\mu q)b_0=0.
\tag{24.5}
$$

On every compact subinterval $c$ is smooth and positive and $q$ is
smooth; interior regularity makes this a classical equation. An
interior zero of $b_0$ would also have derivative zero, by
nonnegativity. Uniqueness for the linear initial-value equation would
then give $b_0=0$, a contradiction. Thus $b_0>0$ in $J$.
The modulus of every nonzero real kernel vector is likewise a
minimizer and strictly positive in the interior. Two independent real
kernel vectors would admit a nonzero real linear combination vanishing
at a prescribed interior point, which is impossible. Real coefficients
therefore give complex kernel dimension one. Normalize $\|b_0\|_2=1$.
Reflection preserves $B$, so uniqueness of its positive normalized
kernel generator makes $b_0$ even. Compact resolvent now gives a
strictly positive second eigenvalue $\gamma$ of $B$.

At $k=\mu$, let $e_m(\sigma)$ be the lowest eigenvalue of the form

$$
B[b]+\int_Jc(\sigma+m\tan a)^2|b|^2\,da,\qquad b\in D_m.
\tag{24.6}
$$

For $m\ne0$ it is positive. Indeed compactness would supply a zero
eigenvector if the bottom were zero. Both nonnegative terms would
vanish, so that vector would be a multiple of $b_0$ and
$\sigma+m\tan a$ would vanish almost everywhere on $J$, a contradiction.
This positivity is uniform. If $e_m(\sigma)\le1$, its unit minimizing
eigenvector satisfies

$$
A[b]+\int_Jc(\sigma+m\tan a)^2|b|^2\,da
=e_m(\sigma)+\mu Q[b]\le1+\mu.
\tag{24.7}
$$

Assertion (18.6), applied with $K=\mu+1$, confines every such pair
to finitely many integers $m$ and a bounded real frequency interval.
For each fixed $m$ the expansion (18.4) is a bounded polynomial
perturbation on a common form domain, so the lowest eigenvalue is
continuous in $\sigma$. Its positive minimum on that compact interval,
for each of the finitely many nonzero modes, together with the exterior
bound $1$, gives $\eta>0$ such that $e_m(\sigma)\ge\eta$ for every
$m\ne0$ and every real $\sigma$. If there are no such modes in the
bounded set, take $\eta=1$.

Choose $0<\delta_0<\min(1,\eta/2,\gamma/2)$ and set
$g_n^{\rm iso}=2\pi(\mu+\delta_0)$. For fixed $g$ in the asserted
interval write $\delta=k-\mu\in(0,\delta_0)$. Since $Q\le\|\cdot\|_2^2$,
all nonzero modes have lower bound $\eta-\delta>0$. For $m=0$ the form
is $B-\delta Q+\sigma^2C$, whose second eigenvalue is at least
$\gamma-\delta>0$. Its first eigenvalue at $\sigma=0$ is negative
by the trial $b_0$.

Let $f_\delta(t)$ be the first eigenvalue of $B-\delta Q+tC$ for
$t\ge0$. It is continuous by bounded perturbation. For $t_2>t_1$,
a unit lowest eigenvector $u_2$ at $t_2$ gives, by min-max,

$$
f_\delta(t_2)\ge f_\delta(t_1)+(t_2-t_1)C[u_2]
>f_\delta(t_1).
\tag{24.8}
$$

The last inequality uses $c>0$ almost everywhere. The function is
positive for all sufficiently large $t$: otherwise a unit vector of
nonpositive energy would violate (18.6) with homogeneous bound $K=k$.
Thus exactly one $s>0$ satisfies $f_\delta(s^2)=0$. The second-eigenvalue
bound gives its simple kernel. Bounded analytic perturbation by
$\sigma^2c$ gives derivative $2\sigma C[u]$ at each root for a unit
eigenvector $u$, which is nonzero at $\pm s$. This proves all ranks
in (24.4), including strict negative rank zero at the roots. Integrating
that rank over all integers exactly as in (18.2)/(21.2) gives
$d=(2s)/(2\pi)=s/\pi$ and $L=d/2=s/(2\pi)$. $\square$

**Proposition 24.3 (weighted natural indicial realization and endpoints).**
For every fixed $n,g$ in Lemma 24.2's interval, the same form $h$ on
$\mathcal H_c$ defines a lower semibounded compact-resolvent
self-adjoint operator $K_g$ in the auxiliary space $L^2(J,c\,da)$.
It has exactly one simple negative eigenvalue $-s^2$, no zero eigenvalue,
and a positive gap to its remaining spectrum. The complex-frequency
roots of the $m=0$ pencil are precisely $\pm s$ and purely imaginary
roots separated from zero. Its real positive even negative eigenvector
$\psi$, normalized by $C[\psi]=1$, has finite strictly positive limits
at both endpoints, bounded derivative, and zero endpoint flux
$4c\psi'$. These endpoint conclusions are derived, not imposed.
The statement about complex roots concerns only $m=0$.

Proof. Compactness first gives, for each $\epsilon>0$, a finite
$D_\epsilon$ such that

$$
\|b\|_2^2\le\epsilon A[b]+D_\epsilon C[b],\qquad b\in\mathcal H_c.
\tag{24.9}
$$

Otherwise choose counterexamples normalized to norm one with
$\epsilon A[b_j]+jC[b_j]<1$. Their bounded $A$ energy gives a
strongly unweighted $L^2$ convergent subsequence, with norm-one limit
$b$. Bounded multiplication by $c$ gives $C[b]=0$, contradicting
$c>0$ almost everywhere. Since $Q\le\|\cdot\|_2^2$, choose
$\epsilon<1/k$ and then sufficiently large finite $\beta$.
The form $h+\beta C$ is coercive and has norm equivalent to $A+C$.
That norm is complete by closedness and
$A\ge\lambda_0\|\cdot\|_2^2$. The natural domain contains the compact
smooth angular core, is dense in $L^2(c\,da)$, and embeds compactly
there. The closed-form representation theorem therefore supplies
$K_g$ on precisely this form domain.

The negative form index depends on $h$ on $\mathcal H_c$, independently
of the chosen Hilbert inner product. Lemma 24.2 makes it exactly one,
so the negative weighted eigenvalue is simple. A zero weighted
eigenvector would satisfy $h[b,\phi]=0$ for every
$\phi\in\mathcal H_c$; as $b\in L^2(da)$, this is also the weak
equation putting it in the operator domain and kernel of
$H_{n,g}(0,0)$. That operator is invertible by Lemma 24.2.
Thus zero is absent and compact resolvent gives a positive gap above
the single negative eigenvalue.

More generally, for any complex frequency $z$, the equation
$K_g\psi=-z^2\psi$ is equivalent to
$H_{n,g}(z,0)\psi=0$. This equivalence includes associated operator
domains: the weighted weak equation has right side $-z^2c\psi$ in
unweighted $L^2$, while the unweighted pencil equation has right side
$-z^2\psi$ in weighted $L^2$. The common form domain is unchanged.
Self-adjointness of $K_g$ forces $-z^2$ to be a real eigenvalue.
The real root $s$ from Lemma 24.2 identifies its unique negative
eigenvalue as $-s^2$; the positive eigenvalues give purely imaginary
roots whose distances from zero have a strictly positive lower bound.

The modulus and interior ODE argument, applied to the nonnegative
form $h+s^2C$, gives a positive generator $\psi$. Simplicity and
reflection make its $C$-normalized positive generator even. Its equation
and flux are

$$
-4(c\psi')'+(c-kq)\psi=-s^2c\psi,\qquad
p_*=4c\psi',\qquad p_*'=((1+s^2)c-kq)\psi.
\tag{24.10}
$$

Since $c^2\le c$, both $p_*$ and $p_*'$ are in $L^2(J,da)$, so
$p_*\in H^1(J)$ has endpoint traces. The finite energy
$\int_J|p_*|^2/c<\infty$ and the simple endpoint zeros of $c$ force
both traces to vanish. At endpoint distance $d$, the $H^1$ estimate
gives $|p_*|=O(\sqrt d)$ and thus $|\psi'|=O(d^{-1/2})$.
This is integrable, so $\psi$ has finite endpoint limits and is bounded.
Now (24.10) makes $p_*'$ bounded, whence $p_*=O(d)$ and $\psi'$ is
bounded.

If one endpoint value of $\psi$ were zero, integrate the two equations
from that endpoint, using $c(d)\asymp d$. With
$M(d)=\sup_{0\le t\le d}|\psi(t)|$, boundedness of their coefficients
gives $|p_*(d)|\le C_1dM(d)$, and then
$|\psi(d)|\le C_2dM(d)$. Taking the supremum forces $M(d)=0$ for
sufficiently small $d$, and interior uniqueness gives $\psi=0$.
This contradicts its normalization; positivity in the interior then
makes both endpoint limits strictly positive. In particular
$\mathcal C_0(s)\psi$ from (23.3) is unweighted $L^2$, also directly
from $\mathcal H_c$ and $c^2\le c$. The auxiliary weighted realization
does not replace the original Hilbert space or diagonalize its mass
wall. $\square$

**Proposition 24.4 (finite negative rank outside the exact symmetry sector).**
For every fixed $n,g$ in Lemma 24.2's interval, let $\mathcal S$ consist
of original $L^2$ functions independent of the horizontal angle $\theta$
and even in $z$. It reduces $\mathscr A$, and the restriction of
$\mathscr A$ to $\mathcal S^\perp$ has finite total negative complex
spectral rank. Thus deleting finitely many original negative eigenvalue
occurrences leaves only $\mathcal S$. Higher even angular components
inside $\mathcal S$ remain.

Proof. The exact complete heat Fourier column (10.3)/(20.8) depends
horizontally only on $\rho$ and is even in the central Fourier variable:
its factors are $e^{-\epsilon^2tk^2}$,
$|k|/(4\pi\sinh(|k|t))$,
$\cosh(|k|t)^{-(n-1)}$, and
$\exp(-|k|\coth(|k|t)\rho^2/4)$. Hence inverse Fourier transform
and the complete time integral make the actual potential rotationally
invariant and even in $z$. Rotations preserve raw measure, the compact
smooth original core and $Z$, and transform the horizontal fields by
an orthogonal pair. Every integer Fourier sector therefore reduces
the original closed form and its Friedrichs operator.

In the $m=0$ sector, $z$ reflection preserves horizontal energy because
the angular-central cross term vanishes there, and it preserves
central energy and potential. Equivalently, in (23.3), reflection
$a\mapsto-a$ anticommutes with
$\mathcal C_0(\partial_\ell)=2\sin a(\partial_\ell-1)+4c\partial_a$,
so its squared norm is invariant. Reflection preserves the original
core closure. This proves the claimed reducing sector for the actual
complete source and operator.

For every $m\ne0$, Lemma 24.2 gives lower bound $\eta-\delta$.
For $m=0$ odd in $a$, orthogonality to even $b_0$ gives $B\ge\gamma$,
so $B-\delta Q+\sigma^2C\ge\gamma-\delta$ for all real $\sigma$.
Put $\zeta=\min(\eta-\delta,\gamma-\delta)>0$. Zero extension of a
compact exterior cylinder function and Plancherel therefore give

$$
Q_g[w]\ge\zeta\int|v|^2\,d\ell\,da\,d\theta
\quad\text{on }\mathcal S^\perp.
\tag{24.11}
$$

The original-to-cylinder correspondence after (23.18), followed by
original core approximation and longitudinal cutoffs, extends this
inequality to the exterior free domain. The gauge preserves the
integrated angular norm. No endpoint value has been added.

Choose $a_*\ge\max(0,\ell_n)$ so that
$gC_ne^{-2a_*}\le\zeta/4$. The exact original formula (23.18), its
nonnegative central term and (23.19) imply, on exterior vectors in
$\mathcal S^\perp$ supported in $\ell>a_*$,

$$
q_{\rm orig}[f]\ge\frac{3\zeta}{16}\int|v|^2
 =\frac{3\zeta}{4}\int R^{-2}|f|^2\,d\xi.
\tag{24.12}
$$

The equality retains the raw Jacobian
$\int|v|^2=4\int R^{-2}|f|^2\,d\xi$.
Take a smooth $\vartheta$ from $0$ to $\pi/2$, constant outside
$(0,1)$, and a finite width $H>0$, and set
$\chi_{\rm in}=\cos\vartheta((\ell-a_*)/H)$,
$\chi_{\rm out}=\sin\vartheta((\ell-a_*)/H)$.
They are smooth original multipliers, constant near the pole, preserve
$\mathcal S^\perp$, and have squared sum one. If
$|\chi_{\rm in}'|^2+|\chi_{\rm out}'|^2\le D/H^2$, the exact IMS
multiplier (18.16) satisfies on its transition annulus

$$
I=(|\chi_{\rm in}'|^2+|\chi_{\rm out}'|^2)
 \left(\frac c{R^2}+\frac{4\sin^2a}{R^4}\right)
\le\frac{D(1+4e^{-2a_*})}{H^2}R^{-2}.
\tag{24.13}
$$

Choose finite $H$ making its coefficient at most $\zeta/4$.
Then $q_{\rm orig}[\chi_{\rm out}f]-\int I|\chi_{\rm out}f|^2$
is nonnegative on $\mathcal S^\perp$.

The inner component is supported in a fixed compact set. Choose a
bounded smooth Euclidean domain $\Omega$ containing it in its interior.
On its original free Dirichlet closure, (15.11)--(15.12) and boundedness
of $I$ give
$q_{\rm orig}-I\ge\alpha T_1-\beta\|\cdot\|_2^2$ for some
$\alpha>0$, with equivalent shifted free form norm. Estimate (15.9)
gives local Euclidean $H^1$ control; Rellich compactness gives compact
embedding into $L^2(\Omega)$. This inner shifted form therefore has a
finite-dimensional negative spectral space, of complex rank $K_{\rm in}$.
Original core approximation shows that multiplication by $\chi_{\rm in}$
maps the original domain into this Dirichlet domain.

For any strictly negative original form subspace $X\subset\mathcal S^\perp$,
map $f$ to the projection of $\chi_{\rm in}f$ onto that inner negative
space. This map is injective: a kernel vector has nonnegative inner
shifted form and nonnegative outer shifted form, and the IMS identity,
allocating $I$ by $\chi_{\rm in}^2+\chi_{\rm out}^2=1$, would give
$q_{\rm orig}[f]\ge0$. Hence $\dim_{\mathbb C}X\le K_{\rm in}$.
The strict form-index principle proves finite total negative rank on
$\mathcal S^\perp$. Its contribution is a fixed finite deletion; it
proves neither simplicity nor a phase law inside $\mathcal S$.
$\square$

**Proposition 24.5 (exact original ground-channel form compression).**
Fix $n,g$ in Lemma 24.2's interval, and take $s$ and the real positive
even $C$-normalized $\psi$ of Proposition 24.3. For any
$a_0\ge\ell_n$ and $u\in C_c^\infty((a_0,\infty);\mathbb C)$,

$$
f(R,a,\theta)=\frac{R^{-1}}{\sqrt{2\pi}}u(\log R)\psi(a)
\quad\text{belongs to }\mathcal H_1.
\tag{24.14}
$$

Define the finite real coefficients and complete-source compression

$$
\begin{aligned}
M_0&=\int_J\psi^2\,da,\qquad p(a)=2\sin a\,\psi(a),
\qquad r(a)=4c\psi'-2\sin a\,\psi,\\
\alpha&=\int_Jp^2\,da,\qquad\beta=\int_Jpr\,da,
\qquad\tau=\int_Jr^2\,da,\\
V(\ell)&=-g\int_JB_n(\ell,a)\psi(a)^2\,da.
\end{aligned}
\tag{24.15}
$$

Here $B_n$ is exactly the complete-source error in (20.23)/(23.18),
independent of $\theta$ by the complete heat formula. With all
longitudinal integrals over $(a_0,\infty)$, the exact identities are

$$
\begin{aligned}
4q_{\rm orig}[f]
 &=\int\Big\{|u'|^2-s^2|u|^2
 +e^{-2\ell}\big(\alpha|u'|^2
       +2\beta\operatorname{Re}(u'\overline u)+\tau|u|^2\big)
 +V(\ell)|u|^2\Big\}\,d\ell,\\
4\|f\|_2^2&=M_0\int e^{2\ell}|u|^2\,d\ell,
\qquad |V(\ell)|\le gC_nM_0e^{-2\ell}.
\end{aligned}
\tag{24.16}
$$

These assertions concern the original free form domain only.

Proof. Approximate $\psi$ in its supplied natural angular form norm
by the compact smooth angular core. On the fixed compact longitudinal
support of $u$, (23.20) controls both the homogeneous form and the
original central derivative, using $c^2\le c$; both exponential weights
are bounded there. Undoing coordinates gives actual compact smooth
Cartesian approximants away from the axes and pole. They converge in
the full original free norm, proving (24.14), with no graph-domain
assertion.

For $m=0$, the homogeneous part of (23.18) on this tensor is
$\int(C[\psi]|u'|^2+h[\psi]|u|^2)\,d\ell$.
Since $C[\psi]=1$ and $h[\psi]=-s^2$, these are exactly the first
two terms in (24.16). The retained central derivative is exactly

$$
\mathcal C_0(\partial_\ell)(u\psi)=p\,u'+r\,u.
\tag{24.17}
$$

Its squared norm gives the three $e^{-2\ell}$ terms, with finite
coefficients by natural energy and $c^2\le c$. The factor
$1/\sqrt{2\pi}$ gives unit angular $\theta$ norm. The raw Jacobian
in (23.18) gives precisely the mass $M_0e^{2\ell}$, and (20.19)
integrated against $\psi^2$ gives the stated bound on $V$.
These substitutions and the form-domain limit prove (24.16).
Testing against angular vectors outside $\operatorname{span}\{\psi\}$
still produces central, complete-source and mass couplings. Thus this
compression identifies no reducing scalar operator and supplies no
original operator-domain quasimode or phase result. $\square$

**Application 24.6 (sufficient original quasimodes and multiplicity exhaustion).**
Fix $n,g$ in Lemma 24.2's interval, $L=L_{n,g}=s/(2\pi)$, and the
original $\mathscr A$ in (24.1). Suppose there exist $D\in(0,\infty)$
and nonzero $f_j\in D(\mathscr A)$ for every sufficiently large integer
$j$, such that

$$
a_j=De^{-j/L},\qquad
\frac{\|(\mathscr A+a_j)f_j\|_2}{\|f_j\|_2}=o(a_j).
\tag{24.18}
$$

Then the full ordered original negative spectrum, including every
complex multiplicity, satisfies
$\varepsilon_j e^{j/L}\longrightarrow C\in(0,\infty)$.
The antecedent (24.18) is not established here.

Proof. The original spectral theorem gives
$\operatorname{dist}(-a_j,\operatorname{spec}\mathscr A)
\le\|(\mathscr A+a_j)f_j\|_2/\|f_j\|_2$.
Choose positive $r_j\to0$ strictly exceeding the relative residual.
Each magnitude interval
$I_j=[a_j(1-r_j),a_j(1+r_j)]$ then contains an actual negative
eigenvalue occurrence: the corresponding spectral interval lies away
from zero, and the original negative spectrum there is discrete.
The ratio $a_{j+1}/a_j=e^{-1/L}<1$ makes these intervals pairwise
disjoint for all sufficiently large $j$. Select one occurrence $b_j$
from each. Then $b_j/a_j\to1$ and $b_j$ is eventually strictly decreasing.

The selected multiset count is
$N_{\rm sel}(E)=L\log(1/E)+O(1)$: eventually
$a_j/2\le b_j\le2a_j$, and solving the exact geometric inequalities
for $a_j$ gives these bounds, with finite beginnings absorbed in $O(1)$.
By the reused original bounded count (23.33),
$N_{n,g}(E)-N_{\rm sel}(E)$ is bounded for sufficiently small $E$.
It counts the unselected occurrences, is nonnegative, and is
nondecreasing as $E$ decreases. Only finitely many such occurrences
therefore exist. This includes all extra complex multiplicities,
extra occurrences in the intervals, and eigenvalues outside them.
It gives a fixed indexing shift, rather than a bounded varying error.

Consequently a fixed integer $\kappa$ satisfies
$\varepsilon_{j+\kappa}=b_j$ for every sufficiently large $j$, and

$$
\varepsilon_{j+\kappa}e^{(j+\kappa)/L}
 =\frac{b_j}{a_j}De^{\kappa/L}
 \longrightarrow De^{\kappa/L}\in(0,\infty).
\tag{24.19}
$$

This proves the application using the actual original spectral theorem,
discreteness and bounded count. Original form-domain tensors or a
residual merely $O(a_j)$ do not satisfy (24.18). $\square$

**Remark 24.7 (sources and the unresolved original-domain bridge).**
The isolation, weighted natural realization, endpoint estimates and
finite symmetry-complement rank above are repository deductions under
the stated suppliers. The compressed identity is an application of the
existing exact original form formulas. The residual-to-spectrum and
bounded-count exhaustion mechanism in Application 24.6 is mature; see
Andrew Hassell and Simon Marshall, *Eigenvalues of Schrödinger operators
with potential asymptotically homogeneous of degree $-2$*,
[arXiv:math/0510617v1, Lemma 3 and Section 7](https://arxiv.org/html/math/0510617v1).
The application has a self-contained proof here and uses the original
bounded count as its specific input.

Theorem 2 of that primary source has a distinct applicability boundary:
it concerns the Euclidean $\mathbb R^3$ Laplacian, a potential exactly
$P(\omega)/r^2$ outside a fixed radius, one strictly supercritical
spherical eigenvalue, and every other spherical eigenvalue strictly
above threshold. No bridge placing the original kinetic form, central
regularization, complete-source error, natural endpoints, mass wall
and Friedrichs closure under those hypotheses has been supplied.
That theorem is not applied to the original operator here.

No original $D(\mathscr A)$ quasimodes with the relative $o(a_j)$
residual in (24.18) have been produced. Still missing are a connection
from the original core to a nonzero oscillatory asymptotic coefficient,
a decaying low-energy solution and matching estimates for the coupled
wall $Ee^{2\ell}$ with the original mass, and graph control of the
full central expression
$2\sin a(\partial_\ell-1)+4c\partial_a-2imc$ and complete-source
correction. The auxiliary weighted angular basis does not diagonalize
the original unweighted mass. Any original zero-energy resonance
allowed by Definition 18.1 must be handled; none is excluded by an
additional premise.

For $s=2\pi L$, the missing phase limit is equivalently convergence of
$t_j-\pi j/s$ to a finite real value, in which case the phase factor
would be $\exp(-2\lim_j(t_j-\pi j/s))$. The accepted (23.35) only
bounds this expression. Neither phase convergence nor an original
spectral ratio is established. Simplicity of the natural channel does
not imply simplicity of original eigenvalues; summable coefficients,
a scalar form compression and finite index errors do not establish
general phase matching. Thus the existence, for every $n\ge2$, of a
full geometric-phase threshold above $\lambda_n$ remains unresolved.
The constants and isolation intervals here need not be uniform in
$n$ or $g$, and no explicit interval or phase constant is asserted.
These are ordinary conditional analytic results, without a claim of
kernel verification, physical realization or literature priority.

## 追加锚（本行以下为增补区）
