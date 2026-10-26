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


## 25. Complete-source differentiation and the normalized exterior outgoing solution

**Definition 25.1 (unchanged source and exterior coordinates).**
Retain exactly the analytic hypotheses and original realization of
Definition 18.1 of
[Same-source native attractive boundary response](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
as used in Definitions 20.1 and 24.1. In particular, retain the
original-field formulas and locally uniform off-pole convergence of
Theorem 10.2, the full complex polar identity (12.12)--(12.13), the
closed natural angular form and compact embedding supplied by V,
Theorem 10.2, the natural-core approximation (13.6)--(13.8), the
complete-field scaling (14.9), and the original closed form, compact
smooth core and local estimates (15.9)--(15.12), with precisely the
suppliers fixed in those definitions. All conclusions in this section
are conditional on these hypotheses.

Thus the source is the identity unit source for the original fields
$U_j=\partial_{x_j}-y_j\partial_z/2$,
$V_j=\partial_{y_j}+x_j\partial_z/2$ and $Z=\partial_z$ on $H^n$,
with generator $L_{n,\epsilon}$ and heat column in (20.1)--(20.2).
Its clock has horizontal covariance $2$ and central covariance
$2\epsilon^2$, its measure is raw Lebesgue measure, and
$M_{n,\epsilon}$ integrates the entire unweighted omitted fibre
$\mathbb R^{2n-2}$ and the full time interval $(0,\infty)$.
The retained equation has $\epsilon=1$ and the original form
$q_{\rm orig}=T_1-gW_{n,1}$, associated with $A_{n,1,g}$.
Here $\mathcal H_1$ denotes the complex compact-smooth closure in
$\|f\|_2^2+\|Uf\|_2^2+\|Vf\|_2^2+\|Zf\|_2^2$, with retained
fields $U=\partial_x-y\partial_z/2$,
$V=\partial_y+x\partial_z/2$.

To distinguish the two radii, write
$r_h=(x^2+y^2)^{1/2}$ and $R_g=(r_h^4+16z^2)^{1/4}$.
Thus $R_g$ is the gauge denoted by $R$ in (20.2), rather than the
horizontal radius $\rho$ there. Use $\ell=\log R_g$,
$r_h^2=R_g^2\cos a$, $4z=R_g^2\sin a$, and $\omega(a,\theta)$
of (20.4). The dilation is $\delta_r(x,y,z)=(rx,ry,r^2z)$ and
$d\xi=\tfrac14e^{4\ell}\,d\ell\,da\,d\theta$.
Use $J=(-\pi/2,\pi/2)$, $c=\cos a$, $q_n$ of (20.3), and the
natural angular space and forms of (24.2):

$$
\begin{aligned}
\mathcal H_c
 &=\{b\in L^2(J,da):b\in AC_{\rm loc}(J),\ \sqrt c\,b'\in L^2(J,da)\},\\
A[b]&=\int_J(4c|b'|^2+c|b|^2)\,da,
& C[b]&=\int_Jc|b|^2\,da,
& Q[b]&=\int_Jq_n|b|^2\,da,\\
\|b\|_{\mathcal H_c}^2&=A[b]+\|b\|_2^2,
& h&=A-\frac{g}{2\pi}Q.
\end{aligned}
\tag{25.1}
$$

Forms and inner products are linear in their first argument; their
polarizations have the same letters. The unweighted angular norm is
$L^2(J,da)$, while $\|\cdot\|_C$ means $L^2(J,c\,da)$.
There are no prescribed angular endpoint values. The complete-source
error is exactly

$$
B_n(\ell,a)=M_{n,e^{-\ell}}(\omega(a,\theta))
                     -\frac{q_n(a)}{2\pi}.
\tag{25.2}
$$

It is independent of $\theta$, real and even in $a$ by the original
complete heat formula. Equations (20.19) and (23.18) identify it as
the original exterior error, not a replacement potential.

**Proposition 25.2 (longitudinal derivative of the complete-source error).**
For each integer $n\ge2$, with exactly $C_n,\epsilon_n$ from (20.7)
and $\ell_n=\log(1/\epsilon_n)$, the map
$\ell\mapsto B_n(\ell,\cdot)$ is continuously differentiable into
$L^\infty(J,da)$ on $(\ell_n,\infty)$ and

$$
\|\partial_\ell B_n(\ell,\cdot)\|_\infty
                 \le 2C_ne^{-2\ell}.
\tag{25.3}
$$

The same bound holds uniformly on the entire gauge sphere, including
both axis points and the $z=0$ circle.

Proof. Denote heat time by $\tau$. In the exact fixed-time difference
(20.9), put $\epsilon=e^{-\ell}$. Differentiation of its only
$\ell$-dependent factor gives

$$
\partial_\ell e^{-\epsilon^2u^2/\tau}
       =\frac{2\epsilon^2u^2}{\tau}e^{-\epsilon^2u^2/\tau}.
\tag{25.4}
$$

Use exactly the pole-free contour
$u=v+i\alpha\operatorname{sgn}z$, $0<\alpha<\pi/2$, of
(20.10)--(20.15); either sign is allowed at $z=0$.
The modulus of (25.4) is at most
$2\epsilon^2|u|^2\tau^{-1}e^{\alpha^2\epsilon^2/\tau}$.
The additional polynomial factor does not change the vanishing of
the vertical-end integrals: $F_n$ has the exponential decay in
(20.10), and for fixed $\tau$ the central Gaussian has nonpositive
quadratic real exponent at sufficiently large $|\operatorname{Re}u|$.
The geometric exponential on the whole sphere is bounded by
$e^{-D_\alpha/\tau}$, exactly by (20.14). Therefore, for
$0<\epsilon\le\epsilon_n$,

$$
\sup_{\omega\in\Sigma}
\left|\partial_\ell
 \{m_{n,e^{-\ell}}(\tau,\omega)-m_{n,0}(\tau,\omega)\}\right|
\le\frac{K_{n,\alpha}}{4\pi^2}\epsilon^2\tau^{-3}
                  e^{-D_\alpha/(2\tau)}.
\tag{25.5}
$$

Here $F_n,K_{n,\alpha},D_\alpha$ are the unchanged quantities in
(20.7). In particular no omitted-fibre or heat-time truncation has
been made. Since
$\int_0^\infty\tau^{-3}e^{-D_\alpha/(2\tau)}\,d\tau
=4/D_\alpha^2$, integration gives
$K_{n,\alpha}\epsilon^2/(\pi^2D_\alpha^2)=2C_n\epsilon^2$.

Differentiation under both integrals is justified locally uniformly
in $\ell>\ell_n$: on a sufficiently small compact neighborhood use
the largest $\epsilon$ there in the integrable bound (25.5).
The shifted Fourier integrals have a common integrable exponential
majorant in $v$. Their differentiated integrands depend continuously
on $\ell$, uniformly over the compact gauge sphere after domination.
Dominated convergence first in $v$ and then in $\tau$ proves
continuity of the derivative in the supremum norm and identifies it
with the derivative of (25.2). Thus (25.3) is derived from the
complete heat source; it is not an additional tail hypothesis.
$\square$

**Theorem 25.3 (normalized outgoing solution in the original exterior).**
Under Definition 25.1's unchanged hypotheses, for every integer
$n\ge2$ one may take $g_n^{\rm ext}=g_n^{\rm iso}$ from Lemma 24.2.
For every fixed real $g\in(\lambda_n,g_n^{\rm ext})$ there exist a
finite $R>0$ and a complex axisymmetric, $z$-even function $f_+$ on
$\Omega_R=\{\xi:R_g(\xi)>R\}$ such that
$\chi f_+\in\mathcal H_1$ for every smooth compactly supported
multiplier $\chi$ in $\Omega_R$ and
$q_{\rm orig}(f_+,\phi)=0$ for every original compact smooth
exterior test $\phi$. Thus it solves the original equation
$A_{n,1,g}f_+=0$ in the local form sense.

Let $s=s_{n,g}=2\pi L_{n,g}>0$ and let $\psi=\psi_{n,g}$ be the
real positive even natural vector of Proposition 24.3, normalized by
$C[\psi]=1$. Set
$w_+(\ell,a)=\sqrt{2\pi}e^\ell
 f_+(\delta_{e^\ell}\omega(a,\theta))$. There are continuous slice
representatives for which

$$
\|w_+(\ell)-e^{is\ell}\psi\|_{\mathcal H_c}
 +\|\partial_\ell w_+(\ell)-is e^{is\ell}\psi\|_C
                  \longrightarrow0\qquad(\ell\to\infty).
\tag{25.6}
$$

The outgoing coefficient is exactly $1$, so $f_+$ is nonzero.
The radius and estimates may depend on $n,g$; no uniformity or
effective radius is asserted. This theorem concerns only the
exterior, with the original complete tails, natural endpoints,
physical mass and free closure.

Proof. Fix arbitrary $n\ge2$ and
$g\in(\lambda_n,g_n^{\rm iso})$ throughout the construction.
We use the isolation and natural realization already proved in
Lemma 24.2 and Proposition 24.3, and the symmetry correspondence of
Proposition 24.4; none of these results is reproved here.
In particular $A\ge\lambda_0\|\cdot\|_2^2$ with $\lambda_0>0$,
and $\|\cdot\|_{\mathcal H_c}$ is equivalent to $A^{1/2}$.

For an axisymmetric function $f=e^{-\ell}w/\sqrt{2\pi}$, the
polarization of (23.18) at energy zero is exactly

$$
\begin{aligned}
4q_{\rm orig}(f,f_z)=p(w,z)
 &=\int\{C(w_\ell,z_\ell)+h(w,z)
       +e^{-2\ell}\langle Dw,Dz\rangle
       -g\langle B_n(\ell)w,z\rangle\}\,d\ell,\\
D&=\nu(\partial_\ell-1)+4c\partial_a,
\qquad \nu(a)=2\sin a,\qquad f_z=e^{-\ell}z/\sqrt{2\pi},\\
4\|f\|_2^2&=\int e^{2\ell}\|w(\ell)\|_2^2\,d\ell.
\end{aligned}
\tag{25.7}
$$

Initially the longitudinal support is compact in the exterior;
the natural-domain extensions use the correspondences
(23.18)--(23.20). Both brackets in the central and source terms of
(25.7) are unweighted $L^2(J,da)$ brackets. In particular, the
auxiliary $C$ inner product does not replace the physical mass.

Consider the full even natural complement
$V=\{b\in\mathcal H_c:b(-a)=b(a),\ C(b,\psi)=0\}$.
Proposition 24.3 gives $h[b]\ge\gamma C[b]$ on $V$ for a
$\gamma>0$, and constants $\alpha>0$, $\beta\ge0$ with
$h[b]+\beta C[b]\ge\alpha A[b]$ on $\mathcal H_c$.
Consequently

$$
h[b]\ge\kappa A[b]\quad(b\in V),\qquad
\kappa=\frac{\alpha}{1+\beta/\gamma}>0.
\tag{25.8}
$$

Also $h(\psi,b)=-s^2C(\psi,b)=0$ on $V$.
Thus $w=a(\ell)\psi+v(\ell)$ has no homogeneous cross terms,
but all central and complete-source couplings remain.
No higher even angular component is removed.

Choose a smooth real function $\eta_L(\ell)=L+\chi(\ell-L)$,
where $\chi(x)=0$ for $x\le0$, $\chi(x)=x$ for $x\ge1$,
$\chi\ge0$, and $|\chi'|\le H$ for a fixed finite $H$.
Take $L>\ell_n+1$ and set

$$
t(\ell)=e^{-2\eta_L(\ell)},\qquad
\widetilde B(\ell,a)=B_n(\eta_L(\ell),a),\qquad S=e^{-2L}.
\tag{25.9}
$$

These are auxiliary coefficients on the whole line, equal to the
original ones for $\ell\ge L+1$. They satisfy
$0<t\le S$, $|t'|\le2Ht$,
$\|\widetilde B\|_\infty\le C_nt$ and
$\|\partial_\ell\widetilde B\|_\infty\le2HC_nt$ by
Proposition 25.2. Their continuation on the left is not a boundary
condition or an additional source assumption on the exterior.

Choose $0<\delta<1$ with $\delta^2/\lambda_0<\kappa/4$.
Let $X_V$ be the completion of finite sums
$\sum_j\varphi_j(\ell)b_j(a)$, with
$\varphi_j\in C_c^\infty(\mathbb R)$ and $b_j\in V$, for

$$
\|v\|_{X_V}^2
 =\int_{\mathbb R}\{C[v_\ell]+A[v]+t\|Dv\|_2^2\}\,d\ell.
\tag{25.10}
$$

This completion has an injective distributional realization:
a Cauchy sequence converges in $L^2(\mathbb R;\mathcal H_c)$,
its longitudinal derivative converges in $L^2(\mathbb R;L^2(c\,da))$,
and its $D$ derivative converges in $L^2(t\,d\ell\,da)$.
Testing on compact subsets of $\mathbb R\times J$ identifies these
limits as the corresponding distributional derivatives. The last
term is therefore the actual closed central graph norm.
Tensor density is part of this definition, with the full natural
angular domain. On each compact longitudinal interval $t$ has a
positive minimum. The norm also controls unweighted $v_\ell$
locally: away from the endpoints use $C[v_\ell]$, while near them
$\nu$ is bounded away from zero and
$\nu v_\ell=Dv-4cv_a+\nu v$, with
$\|cv_a\|_2^2\le\int c|v_a|^2$. These are the genuine local
original derivatives.

Use the Hilbert space
$X=H^1(\mathbb R;\mathbb C)\oplus X_V$, identified with
$W=a\psi+v$, with the direct-sum norm. For conjugate weights
$W=e^{\delta\ell}w$, $Z=e^{-\delta\ell}z$, define

$$
\begin{aligned}
b_\delta(W,Z)=\int_{\mathbb R}\{&
 C(W_\ell-\delta W,Z_\ell+\delta Z)+h(W,Z)\\
 &+t\langle DW-\delta\nu W,DZ+\delta\nu Z\rangle
       -g\langle\widetilde B W,Z\rangle\}\,d\ell.
\end{aligned}
\tag{25.11}
$$

This is the exponentially conjugated auxiliary form, bounded on
$X\times X$. Indeed, writing
$p=\nu\psi$ and $r_{\rm ang}=4c\psi'-\nu\psi$, we have
$D(a\psi)=pa'+r_{\rm ang}a$. Both angular coefficients are in
unweighted $L^2$ by $\psi\in\mathcal H_c$ and $c^2\le c$,
as in (24.15)--(24.17). The $X_V$ norm controls all other central
terms; $A$ controls the unweighted source pairings.

On $X_V$ the real diagonal of (25.11) is exactly

$$
\int\{C[v_\ell]+h[v]-\delta^2C[v]
 +t\|Dv\|_2^2-\delta^2t\|\nu v\|_2^2
 -g\langle\widetilde Bv,v\rangle\}\,d\ell.
\tag{25.12}
$$

The mixed $\delta$ terms have zero real part.
Using (25.8), $|\nu|\le2$ and (25.9), its lower bound is

$$
\int\left\{C[v_\ell]
 +\left(\kappa-\frac{\delta^2+4\delta^2S+gC_nS}{\lambda_0}\right)A[v]
 +t\|Dv\|_2^2\right\}\,d\ell.
\tag{25.13}
$$

For sufficiently large $L$ this is at least
$\int(C[v_\ell]+\tfrac\kappa2 A[v]+t\|Dv\|_2^2)$.
The resulting $V$ block is invertible $X_V\to X_V^*$, with a
bound independent of sufficiently large $L$. Here the coercive-form
argument is the usual Hilbert-space argument: Riesz representation
gives a bounded operator $T$, and
$\operatorname{Re}\langle Tv,v\rangle\ge m\|v\|^2$ implies
$\|Tv\|\ge m\|v\|$ and closed range. The adjoint has the same
coercive real diagonal, hence zero kernel, so that range is dense
and therefore the entire space; the inverse norm is at most $1/m$.
This is the classical Riesz/adjoint framework of G. B. Folland,
*Real Analysis*, second edition, Chapter 5, applied to the specified
completed space, not an endpoint elliptic assertion.

The scalar homogeneous block is
$\int((a'-\delta a)\overline{(b'+\delta b)}-s^2a\overline b)$.
On the whole line its Fourier multiplier is

$$
m(\xi)=\xi^2+2i\delta\xi-\delta^2-s^2,
\qquad \inf_{\xi\in\mathbb R}\frac{|m(\xi)|}{1+\xi^2}>0.
\tag{25.14}
$$

The imaginary part can vanish only at $\xi=0$, where the real
part is negative. The stated lower bound follows by continuity
and $m(\xi)/\xi^2\to1$. Plancherel, in the classical whole-line
Fourier setting of Folland, Chapter 8, now gives the inverse
$\widehat a=\widehat F/m$, bounded from $H^{-1}(\mathbb R)$ to
$H^1(\mathbb R)$; it gives both surjectivity and injectivity.

Take the block diagonal operator consisting of this scalar block
and the full coercive $V$ block, including its entire central
term. The remaining scalar central/source terms and cross blocks
form an operator $E:X\to X^*$ satisfying

$$
\|E\|\le K(\sqrt S+S),
\tag{25.15}
$$

where $K$ depends on the fixed $n,g,s,\delta,\psi$, not on large
$L$. For example, for $a\in H^1$, $z\in X_V$,

$$
\begin{aligned}
\left|\int t\langle D(a\psi)-\delta\nu a\psi,
                         Dz+\delta\nu z\rangle\right|
 &\le K\sqrt S\,\|a\|_{H^1}\|z\|_{X_V},\\
\left|g\int\langle\widetilde B a\psi,z\rangle\right|
 &\le KS\|a\|_{H^1}\|z\|_{X_V}.
\end{aligned}
\tag{25.16}
$$

The reversed cross block has the same bounds, and the scalar
diagonal perturbations are $O(S)$. Both diagonal inverse bounds
are independent of large $L$. Enlarge $L$ until their product
with the bound in (25.15) is below $1/2$. The operator-norm
Neumann series then inverts the full $b_\delta:X\to X^*$.
In particular no unbounded central derivative has been declared
a bounded perturbation of the limiting homogeneous energy:
its entire $V$ block was retained in (25.10)--(25.13).

Let $w_0=e^{is\ell}\psi$. Its homogeneous equation vanishes
distributionally, since $h(\psi,b)=-s^2C(\psi,b)$ for every
$b\in\mathcal H_c$. Although $e^{\delta\ell}w_0$ is not in
$X$ at positive infinity, its full perturbation residual is the
following bounded functional on $X$:

$$
\begin{aligned}
F_\delta(Z)
 &=\int t e^{(\delta+is)\ell}
       \langle is p+r_{\rm ang},DZ+\delta\nu Z\rangle\,d\ell\\
 &\quad-g\int e^{(\delta+is)\ell}
                   \langle\widetilde B\psi,Z\rangle\,d\ell.
\end{aligned}
\tag{25.17}
$$

This identity first follows on compact tests by exact polarization;
there is no integration of growing homogeneous terms. Its central
part is bounded by Cauchy--Schwarz in the central norm because
$\int_{\mathbb R}t e^{2\delta\ell}\,d\ell<\infty$.
Its source part uses $A$ control of unweighted $L^2$ and
$\int_{\mathbb R}t^2 e^{2\delta\ell}\,d\ell<\infty$.
Both integrals converge at the negative end, where $t$ is constant,
and at the positive end, where $t=e^{-2\ell}$ and $0<\delta<1$.
All angular components of these residuals are retained.

Solve $b_\delta(Y,Z)=-F_\delta(Z)$ for every $Z\in X$ by the
full inverse, and set
$r=e^{-\delta\ell}Y$, $w=w_0+r$ and $X_\delta=e^{-\delta\ell}X$.
For compact longitudinal tests, (25.11) and (25.17) give the exact
auxiliary weak equation $p_{\rm aux}(w,z)=0$. Thus $w$ is an
actual coupled form solution, rather than a scalar ansatz.
The coefficient of $w_0$ was prescribed to be $1$ before inversion.

We next prove the strong slice regularity; weighted integrated
energy alone would not suffice. Let $P$ be the distributional
operator of $p_{\rm aux}$, and $P_h$ the same operator with
coefficients $t(\ell+h)$, $\widetilde B(\ell+h,a)$.
The homogeneous part and $D$ commute with longitudinal translation
$T_hu(\ell)=u(\ell+h)$. From (25.9) and (25.3), for small $|h|$,

$$
\frac{|t(\ell+h)-t(\ell)|}{|h|}\le Kt(\ell),\qquad
\frac{\|\widetilde B(\ell+h)-\widetilde B(\ell)\|_\infty}{|h|}
                                                  \le Kt(\ell).
\tag{25.18}
$$

Translation is uniformly bounded and strongly continuous on
$X_\delta$. On tensors this follows by changing $\ell$,
$t(\ell-h)/t(\ell)\le e^{2H|h|}$, and
$e^{\delta\ell}T_h=e^{-\delta h}T_he^{\delta\ell}$;
tensor density extends it to the completions. It preserves $V$.
For each nonzero small $h$ set

$$
z_h=\frac{T_hw-e^{ish}w}{h}
    =\frac{T_hr-e^{ish}r}{h}\in X_\delta.
\tag{25.19}
$$

Since $P_hT_hw=0$ and $Pw=0$, the exact distributional equation is
$Pz_h=(P-P_h)T_hw/h$.
After exponential conjugation this right side is uniformly bounded
in $X^*$. For its central part use (25.18) and Cauchy--Schwarz
with $\sqrt t e^{\delta\ell}DT_hw$ and
$\sqrt t(DZ+\delta\nu Z)$. The $w_0$ contribution is integrable
by (25.17); that of $r$ is bounded by translation on $X_\delta$.
For the source part use $t e^{\delta\ell}T_hw$ in unweighted
$L^2$ and $A$ control of $Z$, with the second integral following
(25.17). These distributional equalities extend to $X$ tests by
the defining density and the displayed bounds.

The full inverse therefore bounds $z_h$ uniformly in $X_\delta$.
Weak compactness in that Hilbert space and the injective local
distributional realization identify a weak subsequential limit as
$\partial_\ell r-isr$. Hence both $r$ and $\partial_\ell r$
belong to $X_\delta$. This is a difference-quotient argument;
no energy differentiability of the solution was assumed.

It follows from (25.10), its scalar summand, and equivalence of
$A^{1/2}$ with the natural norm that

$$
\begin{aligned}
y=e^{\delta\ell}r&\in H^1(\mathbb R;\mathcal H_c),\\
z=e^{\delta\ell}\partial_\ell r
          &\in H^1(\mathbb R;L^2(J,c\,da)).
\end{aligned}
\tag{25.20}
$$

For the first assertion use $r,\partial_\ell r\in
L^2(e^{2\delta\ell}d\ell;\mathcal H_c)$; for the second use
$\partial_\ell r\in X_\delta$, which also controls its next
longitudinal derivative in the $C$ norm. A Hilbert-valued $H^1$
function has a continuous, locally absolutely continuous
representative tending to zero at positive infinity: its $L^2$
norm supplies a sequence $t_j\to\infty$ of vanishing slice norms,
and the norm-square identity gives

$$
\|u(t)\|^2\le
 2\int_t^\infty\|u(\tau)\|\,\|u'(\tau)\|\,d\tau\longrightarrow0
\tag{25.21}
$$

by Cauchy--Schwarz. Apply this to both functions in (25.20).
Consequently $\|r(\ell)\|_{\mathcal H_c}
+\|\partial_\ell r(\ell)\|_C\to0$, with continuous representatives.
This proves both strong limits, without promoting an averaged or
almost-everywhere estimate to a trace assertion. Only the derived
longitudinal derivative of $B_n$ was used; no angular derivative,
graph regularity or external scattering theorem enters.

Return to the original exterior by taking $R=e^{L+1}$ and
$f_+=e^{-\ell}w/\sqrt{2\pi}$ for $\ell>L+1$.
There the auxiliary coefficients are exactly the original ones
in (25.7). All spaces and coefficients preserve evenness in $a$;
$w$ is independent of $\theta$, so $f_+$ is axisymmetric and even
in $z$.

For the original free closure, take a compact smooth longitudinal
cutoff $\chi_0$ in $(L+1,\infty)$. Its multiplication is bounded
in the local $X$ norm: differentiating adds $\chi_0'r$ to the
homogeneous longitudinal term and $\nu\chi_0'r$ to $D$,
both controlled by $A$. By (25.10), $\chi_0r$ is a limit of
finite natural angular tensors; $\chi_0w_0$ is such a tensor as
well. On this fixed compact interval, both physical weights are
bounded above and below, and the original free norm is controlled by

$$
\int\{C[\partial_\ell(\chi_0w)]+A[\chi_0w]
  +e^{-2\ell}\|D(\chi_0w)\|_2^2
  +e^{2\ell}\|\chi_0w\|_2^2\}\,d\ell.
\tag{25.22}
$$

For each finite tensor use the natural angular core approximation
and (23.20), including $\|cb'\|_2^2\le\int c|b'|^2$.
Undoing coordinates gives compact smooth Cartesian approximants
away from the axes and pole, converging in the original free norm,
exactly the correspondence used in (24.14). Thus
$\chi_0 f_+\in\mathcal H_1$.
For an arbitrary compact smooth exterior multiplier $\chi$, choose
$\chi_0=1$ on its radial support. The original $U,V,Z$ product
rules, with bounded derivatives of $\chi$ on that compact support,
show that $\chi f_+=\chi(\chi_0 f_+)\in\mathcal H_1$.
No angular endpoint data have been imposed.

For axisymmetric even compact smooth Cartesian tests, the polarized
identity (25.7) now agrees with the original local form pairing.
Their cylinder images are in the local test completion: a smooth
axisymmetric Cartesian function is smooth in $(r_h^2,z)$ up to
the axis, hence smooth in $(\ell,a)$ up to the two angular
endpoints on compact longitudinal intervals. The supplied natural
angular cutoffs approximate these images in $A$; the extra central
cutoff derivative is $4c\chi_a'w$ and is controlled by the same
weighted cutoff energy using $c^2\le c$. On compact angular
subintervals ordinary smooth tensor approximation converges in the
central norm as well. Projection onto $\psi$ and its $C$-orthogonal
complement preserves this local completion: the scalar coefficient
and its derivative are controlled by the $C$ norm, while
$D(a\psi)=pa'+r_{\rm ang}a$ controls its central term. Thus these
tests are admissible in the auxiliary equation by density, and
free-norm continuity gives $q_{\rm orig}(f_+,\phi)=0$.

Finally take any original compact smooth exterior test. Average it
first over horizontal rotations, which preserve the full original
form and leave $f_+$ invariant. Within this axisymmetric sector
average over $z$ reflection, using precisely Proposition 24.4's
$m=0$ reflection invariance. Both averages preserve compact smooth
exterior support, because $R_g$ is invariant, and preserve its
pairing with $f_+$. The resulting test is even and axisymmetric,
so its pairing is zero by the preceding paragraph. This proves the
weak equation against all original tests; it does not use
$z$ reflection as a symmetry of the nonaxisymmetric form.

The construction yields exactly
$w_+=e^{is\ell}\psi+r$ and
$\partial_\ell w_+=is e^{is\ell}\psi+\partial_\ell r$.
Equations (25.20)--(25.21) give (25.6). Since $C[\psi]=1$,
$\|w_+(\ell)\|_C\to1$, proving nonzero amplitude with precisely
normalized outgoing coefficient. A nonzero constant incoming
coefficient cannot belong to the decaying correction. Reality of
the equation also gives the real and imaginary exterior standing
waves.

For every fixed pair $n,g$ in the stated interval, (25.8) first
permits a positive $\delta<1$, and then a finite $L$ satisfies
(25.13) and the Neumann bound. Lemma 24.2 supplies a finite
$g_n^{\rm iso}>\lambda_n$ for every integer $n\ge2$.
Thus $g_n^{\rm ext}=g_n^{\rm iso}$ works for every fixed coupling
in its entire open interval. No uniform gap, radius, closed-interval
endpoint, genericity condition or resonance exclusion is needed.

The source-specific derivative estimate and coupled exterior
construction are deductions under the inherited analytic premises;
the Hilbert, Fourier, Neumann-series and $H^1$ tools used inside
the proof are classical. The construction supplies freely determined
data at a finite inner radius. It gives no extension through the
original core, no global $L^2$ or operator-domain membership, no
low-energy decaying solution or coupled mass-wall matching, and no
graph-domain residual of the kind required by (24.18).
Those obligations, and the full eigenvalue phase limit discussed in
24.7, remain separate and unresolved. In particular the exterior
normalization does not identify a global-core coefficient or resolve
an allowed original zero-energy resonance. The physical mass remains
$e^{2\ell}da$, the full central derivative remains present, and the
original complete source and all natural endpoints are unchanged.
These are conditional analytic conclusions, without a claim of
kernel verification, physical realization or literature priority.
$\square$

## 追加锚（本行以下为增补区）

## 26. The original regular core and a nonzero standing channel

**Definition 26.1 (original equation, natural channel and local solutions).**
Retain exactly the analytic hypotheses of Definition 18.1 of
[Same-source native attractive boundary response](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
with the original suppliers fixed there and in Definitions 20.1,
24.1 and 25.1. In particular retain the original-field heat formulas
and locally uniform off-pole convergence, the full complex polar
identity (12.12)--(12.13), the closed natural angular form and its
compact embedding, the natural-core approximation (13.6)--(13.8),
the complete-field scaling (14.9), and the original closed form,
compact smooth core and local bounds (15.9)--(15.12).
All statements in this section are conditional on precisely these
analytic hypotheses.

For clarity, the source and equation in this convention are

$$
\begin{aligned}
U_j&=\partial_{x_j}-\tfrac12y_j\partial_z,
&V_j&=\partial_{y_j}+\tfrac12x_j\partial_z,
&Z&=\partial_z,\\
L_{n,\epsilon}&=-\sum_{j=1}^n(U_j^2+V_j^2)-\epsilon^2Z^2,
&h_{n,\epsilon}(t)&=e^{-tL_{n,\epsilon}}\delta_0,\\
M_{n,\epsilon}(x,y,z)
 &=\int_0^\infty\int_{\mathbb R^{2n-2}}
       h_{n,\epsilon}(t,x,y,W,z)\,dW\,dt.
\end{aligned}
\tag{26.1}
$$

The heat column is the compact-smooth Friedrichs heat column on
$H^n$ with raw $dX\,dz$, identity unit pole, horizontal covariance
$2$ and central covariance $2\epsilon^2$. Both integrals in (26.1)
are complete and unweighted. On retained $\mathbb R^3$ set
$U=\partial_x-y\partial_z/2$, $V=\partial_y+x\partial_z/2$ and
$\epsilon=1$. With raw $d\xi=dx\,dy\,dz$, write

$$
\begin{aligned}
\mathcal H_1
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^{{\|\cdot\|}_{\rm free}},
&\|f\|_{\rm free}^2
 &=\|f\|_2^2+\|Uf\|_2^2+\|Vf\|_2^2+\|Zf\|_2^2,\\
T_1(f,\zeta)
 &=\langle Uf,U\zeta\rangle+\langle Vf,V\zeta\rangle
                         +\langle Zf,Z\zeta\rangle,\\
q_{\rm orig}(f,\zeta)
 &=T_1(f,\zeta)-g\int_{\mathbb R^3}M_{n,1}f\overline\zeta\,d\xi.
\end{aligned}
\tag{26.2}
$$

The operator $A_{n,1,g}$ is the Friedrichs operator of this form.
A global local-form solution of $A_{n,1,g}f=0$ means a distribution
$f$ such that $\chi f\in\mathcal H_1$ for every
$\chi\in C_c^\infty(\mathbb R^3)$ and
$q_{\rm orig}(f,\phi)=0$ for every
$\phi\in C_c^\infty(\mathbb R^3;\mathbb C)$; the latter pairing
uses a compact cutoff equal to one on the support of $\phi$.
It includes tests through the pole. It requires neither global
$L^2$ membership nor membership in the operator domain.
Forms and inner products are linear in the first argument.

Use the actual polar coordinates of Definition 25.1:

$$
\begin{aligned}
R_g&=((x^2+y^2)^2+16z^2)^{1/4},
&\ell&=\log R_g,
&\delta_r(x,y,z)&=(rx,ry,r^2z),\\
\omega(a,\theta)
 &=(\sqrt{\cos a}\cos\theta,\sqrt{\cos a}\sin\theta,\sin a/4),
&d\xi&=\tfrac14e^{4\ell}\,d\ell\,da\,d\theta,\\
w_f(\ell,a)&=\sqrt{2\pi}\,e^\ell
                    f(\delta_{e^\ell}\omega(a,\theta))
                    \quad\text{for axisymmetric }f.
\end{aligned}
\tag{26.3}
$$

Thus $J=(-\pi/2,\pi/2)$, $c=\cos a$ and

$$
I_n=\int_0^{\pi/2}\sin^{n-2}t\,dt,\qquad
q_n(a)=\frac1{I_n}\int_0^1
          \frac{v^{n-2}}{\sqrt{1-v^2\sin^2a}}\,dv.
\tag{26.4}
$$

Reuse $\mathcal H_c,A,C,Q,h=A-gQ/(2\pi)$ from (25.1), with
$\|b\|_{\mathcal H_c}^2=A[b]+\|b\|_2^2$ and no imposed
angular endpoint values. Fix arbitrary $n\ge2$ and
$g\in(\lambda_n,g_n^{\rm iso})$. Lemma 24.2 and Proposition 24.3
supply $s=s_{n,g}=2\pi L_{n,g}>0$ and a real positive even
$\psi=\psi_{n,g}$ such that

$$
C[\psi]=1,\qquad
h(\psi,b)=-s^2C(\psi,b)\quad(b\in\mathcal H_c).
\tag{26.5}
$$

Let $V_{\rm ev}=\{b\in\mathcal H_c:b(-a)=b(a),\ C(b,\psi)=0\}$.
The existing estimates $A\ge\lambda_0\|\cdot\|_2^2$ and
$h[b]\ge\kappa A[b]$ on $V_{\rm ev}$, with
$\lambda_0,\kappa>0$, are exactly (25.8) and its angular suppliers.
This is the entire even complement.

For exterior pairings reuse (25.7), with
$t=e^{-2\ell}$, $\nu=2\sin a$,
$D=\nu(\partial_\ell-1)+4c\partial_a$, and the complete error
$B_n$ of (25.2). In particular

$$
\begin{aligned}
p(w,z)&=\int\{C(w_\ell,z_\ell)+h(w,z)
             +t\langle Dw,Dz\rangle-g\langle B_nw,z\rangle\}\,d\ell,\\
4q_{\rm orig}(f,f_z)&=p(w_f,z),
&f_z&=e^{-\ell}z/\sqrt{2\pi},\\
4\|f\|_2^2&=\int e^{2\ell}\|w_f(\ell)\|_2^2\,d\ell,
&\|B_n(\ell)\|_\infty+\|\partial_\ell B_n(\ell)\|_\infty
 &\le K e^{-2\ell}
\end{aligned}
\tag{26.6}
$$

on a sufficiently remote exterior. The last bound is the conclusion
of Proposition 25.2 and (20.19), including the whole angular interval,
not an additional tail premise. The brackets involving $D$ and $B_n$
are unweighted $L^2(J,da)$ brackets. The auxiliary $C$ norm leaves
the physical mass in (26.6) unchanged. Denote by $\mathcal S$ the
axisymmetric $z$-even reducing sector of Proposition 24.4, extended
to local-form functions.

**Theorem 26.2 (global original-core standing wave throughout the isolation interval).**
Under exactly Definition 26.1's inherited analytic hypotheses, for
every integer $n\ge2$ one can take the finite threshold
$g_n^0=g_n^{\rm iso}>\lambda_n$. For every fixed real
$g\in(\lambda_n,g_n^0)$ there is a nonzero real
$f_0\in\mathcal S$ which is a global local-form solution of the
original equation $A_{n,1,g}f_0=0$ on all of $\mathbb R^3$.
There is $b\in\mathbb C\setminus\{0\}$ such that, with continuous
slice representatives and the normalization (26.3)--(26.5),

$$
\begin{aligned}
\big\|w_{f_0}(\ell)-2\operatorname{Re}(be^{is\ell})\psi
          \big\|_{\mathcal H_c}&\longrightarrow0,\\
\big\|\partial_\ell w_{f_0}(\ell)
       -2\operatorname{Re}(isbe^{is\ell})\psi
          \big\|_{L^2(J,c\,da)}&\longrightarrow0
                    \qquad(\ell\longrightarrow\infty).
\end{aligned}
\tag{26.7}
$$

Membership $\chi f_0\in\mathcal H_1$ holds for every compact
smooth multiplier, and the weak equation holds against every original
compact smooth test, including through the pole. No exceptional
couplings, resonance exclusion or additional endpoint, tail, source,
clock or mass hypothesis is required. The choices in the proof may
depend on the fixed pair $n,g$; no uniform estimate in either
parameter, effective radius, global $L^2$ membership or original
operator-domain membership is asserted.

Proof. Fix arbitrary $n,g$ as stated. The exterior waves and inverse
used below are precisely Theorem 25.3 and (25.11)--(25.20); they are
not obtained by replacing the original core with a left continuation.
The new connection uses the original local form on that core.

(1) Original local-form spaces and opposite weights.
Choose a large finite $L$ and a compact smooth radial multiplier
$\chi_0$ equal to one for $\ell\le L+1$, supported in
$\ell<L+2$, and constant near the pole. Start with compact smooth
members of $\mathcal S$ and complete them in

$$
\begin{aligned}
\|f\|_{\mathcal H}^2
 &=\|\chi_0f\|_{\rm free}^2
       +\int_L^\infty\mathcal E[w_f](\ell)\,d\ell,\\
\mathcal E[w]&=C[w_\ell]+A[w]+e^{-2\ell}\|Dw\|_2^2.
\end{aligned}
\tag{26.8}
$$

Call the resulting Hilbert space $\mathcal H$. This completion has
an injective realization as local distributions. On each fixed
exterior annulus its norm controls local $L^2$, since $A$ controls
the unweighted angular $L^2$ norm and the physical weights there
are bounded. The positive polar free identity and the natural-core
approximation identify the derivative limits with the original
$U,V,Z$ derivatives. On the inner region, including the pole,
$\chi_0=1$ and the defining norm is the original free norm. A
Cauchy sequence therefore has compatible distributional limits on
all compact sets; a zero distribution has zero derivatives and zero
norm. This proves injectivity and retains the original pole closure.

It also proves $\chi f\in\mathcal H_1$ for every compact smooth
$\chi$. To pass from radial to arbitrary multipliers use the
original product rules
$U(\chi f)=\chi Uf+(U\chi)f$, and the analogous identities for
$V,Z$, with bounded coefficients on the fixed support. Every tensor
used below belongs to this same completion: approximate its angular
factor by the supplied natural angular core and its longitudinal
factor in $H^1$ on its support. The extra original central term is
controlled by $c^2\le c$. These are exactly the tensor-to-original
correspondences (24.14), (25.22), with the actual original fields.
No angular endpoint datum or punctured-core domain is substituted.

Put $\rho=\max(\ell-L,0)$ outside the inner region and extend it
by zero throughout that region. It is a locally Lipschitz original
multiplier, constant near the pole. Smooth approximation on its
finite transition annulus justifies multiplication in the completion.
For real $\sigma$ define

$$
\mathcal H_\sigma
 =\{f:e^{\sigma\rho}f\in\mathcal H\},\qquad
\|f\|_{\mathcal H_\sigma}=\|e^{\sigma\rho}f\|_{\mathcal H}.
\tag{26.9}
$$

For $\sigma>0$, $\mathcal H_\sigma$ embeds boundedly and injectively
in $\mathcal H_{-\sigma}$. Compactly supported original smooth
members of $\mathcal S$ are dense in each space, by its completion,
longitudinal cutoff approximation and local multiplier approximation.
On every compact set the original local identities (15.8)--(15.9)
give Euclidean $H^1$ control. The classical Rellich--Kondrachov
compactness theorem on a bounded containing domain consequently makes
restriction to any fixed compact set compact into $L^2$.
This is local compactness; it makes no global Euclidean Sobolev
domain identification.

The form $4q_{\rm orig}$ extends continuously to
$\mathcal H_\sigma\times\mathcal H_{-\sigma}$. In the tail use
(26.6), cancellation of opposite exponential weights and
$A\ge\lambda_0\|\cdot\|_2^2$. Differentiating the weights adds
only the bounded $\sigma C$ terms and the $\sigma\nu$ terms in
the retained central graph pairing. In the compact interior use the
original local form continuity: (15.5) gives
$M_{n,1}\le(4\pi r_h)^{-1}$ and hence
$M_{n,1}\in L^{7/4}_{\rm loc}$, while (15.8)--(15.11) give the
needed local Sobolev and potential estimates. Thus, with the star
denoting the continuous antidual, define the bounded linear map

$$
P_\sigma:\mathcal H_\sigma\longrightarrow
                         (\mathcal H_{-\sigma})^*,\qquad
(P_\sigma f)(\zeta)=4q_{\rm orig}(f,\zeta).
\tag{26.10}
$$

Its kernel consists of original global weak solutions in this
weighted space: density identifies the equation with all compact
smooth symmetric tests, including tests through the pole. Recovery
of arbitrary original tests is given in (9) below.

(2) A scalar half-line summand and the whole complementary core.
Write $x=\ell-L$ on the tail and, for $f\in\mathcal H$, set
$a(x)=C(w_f(L+x),\psi)$. The normalization $C[\psi]=1$ and
(26.8) imply $a\in H^1(0,\infty)$, with bounded projection norm.
Choose a fixed smooth $\eta$ on $(L-1,L)$, zero near $L-1$
and equal to one near $L$. Define a lift $Ea$ by its cylinder
function

$$
w_{Ea}(\ell)=
\begin{cases}
a(\ell-L)\psi,&\ell\ge L,\\
a(0)\eta(\ell)\psi,&L-1<\ell<L,\\
0,&\ell\le L-1.
\end{cases}
\tag{26.11}
$$

The half-line trace inequality bounds $a(0)$ by $\|a\|_{H^1}$.
The tensor approximation in (1) proves $Ea\in\mathcal H$.
The two values agree at $\ell=L$, so its distributional first
derivative has no interface delta. Let $Y$ be the closed subspace
whose tail has $C(w_y,\psi)=0$. Then

$$
\mathcal H=E H^1(0,\infty)\mathbin{\dotplus}Y
\tag{26.12}
$$

with bounded projections. Its weighted analogues follow by
conjugation: multiplication by $e^{\sigma\rho}$ sends the scalar
coefficient to $e^{\sigma x}a(x)$ and is the identity on the inner
lift. It preserves $Y$. The tail of every $y\in Y$ takes values
in the full $V_{\rm ev}$, with all of its central graph energy.

The homogeneous tail cross terms vanish exactly:
$C(\psi,w_y)=C(\psi,\partial_\ell w_y)=0$ and
$h(\psi,w_y)=-s^2C(\psi,w_y)=0$. The central and complete-source
cross terms do not vanish and will be kept. When the raw horizontal
free expression is integrated into the cylinder expression on this
half cylinder, its longitudinal total derivative can also produce a
$C$ trace at $L$. Its scalar/scalar part depends only on
$a(0)\overline{b(0)}$ and has rank one; its scalar/$Y$ part is
zero by $C(\psi,w_y(L))=0$. Its entire $Y/Y$ part remains in the
actual complementary form. This accounts for the seam without
imposing a boundary condition on the original core.

(3) A coercive complementary block with a removable compact shift.
For sufficiently large $L$, (25.8) and (26.6) give on tail-supported
$V_{\rm ev}$ vectors

$$
p(v,v)\ge c_1\int\mathcal E[v]\,d\ell,\qquad c_1>0,
\tag{26.13}
$$

with $c_1$ independent of further enlargement of $L$. Indeed the
central square is nonnegative and
$|g\langle B_nv,v\rangle|\le gK e^{-2L}\lambda_0^{-1}A[v]$;
choose $L$ to retain at least half of the bound $h\ge\kappa A$.
Closure extends the inequality to its tail energy completion.

Take smooth longitudinal IMS cutoffs $\chi_i^2+\chi_e^2=1$,
with $\chi_e=0$ for $\ell\le L+1$ and $\chi_e=1$ for
$\ell\ge L+2$. They are original smooth multipliers constant
near the pole, and $\chi_e y$ still has angular values in
$V_{\rm ev}$. The exact original IMS identity is

$$
q_{\rm orig}[y]
 =q_{\rm orig}[\chi_i y]+q_{\rm orig}[\chi_e y]
                       -\int I|y|^2\,d\xi,
\tag{26.14}
$$

where $I$ is a bounded compactly supported original multiplier.
The unchanged bound (15.11)--(15.12) gives
$q_{\rm orig}[\chi_i y]\ge\alpha T_1[\chi_i y]
-\beta\|\chi_i y\|_2^2$ for $\alpha>0$. Choose a nonnegative
compact smooth $m$ equal to one on the supports of $\chi_i$ and
$I$, and a finite $K_0$ large enough that

$$
\begin{aligned}
\|y\|_Y^2
 &:=4q_{\rm orig}[y]+K_0\int m|y|^2\,d\xi\\
 &\ge c_2\left(T_1[\chi_i y]+\|\chi_i y\|_2^2
                   +\int\mathcal E[\chi_e w_y]\,d\ell\right),
\qquad c_2>0.
\end{aligned}
\tag{26.15}
$$

This is an equivalent Hilbert norm on $Y$. In particular it controls
the entire tail integral in (26.8), with a lower constant independent
of further large $L$. To see the needed uniform tail control, product
rules bound $\mathcal E[w_y]$ by the sum of the two cutoff energies,
and the positive exact free polar identity bounds the inner cutoff's
cylinder energy by $4T_1[\chi_i y]$. The compact physical $L^2$
part of the defining norm is also controlled. Equivalence constants
for that interior part may depend on $L$; these constants will not
be used to make exterior cross blocks small.

After opposite exponential conjugation, the real diagonal of this
shifted $Y$ form is exactly

$$
\|y\|_Y^2-\sigma^2\int_L^\infty
           \{C[w_y]+t\|\nu w_y\|_2^2\}\,d\ell.
\tag{26.16}
$$

The mixed weight terms have zero real part. Since $|\nu|\le2$,
$A\ge\lambda_0\|\cdot\|_2^2$ and (26.15) controls the whole
tail uniformly, the loss is at most $C\sigma^2\|y\|_Y^2$,
with $C$ independent of sufficiently large $L$. Choose a positive
$\delta<1$, below the exterior supplier's allowed exponent, such
that $C\delta^2<1/2$. The shifted conjugated $Y$ block is bounded
and coercive, and has inverse norm at most $2$ in this norm.
This uses the classical Hilbert coercive-form argument: Riesz
representation gives a bounded operator bounded below, its range
is closed, and the same real-diagonal estimate for its adjoint
makes that range dense, hence surjective. This is the Riesz/adjoint
argument of Folland, *Real Analysis*, Chapter 5, already used in
(25.12)--(25.13). The unbounded central derivative has remained
inside the full complementary graph norm throughout.

(4) The scalar half-line defect.
Under the same conjugation the scalar reference form on
$H^1(0,\infty)$ is

$$
S_\delta(a,b)=\int_0^\infty
 \{(a'-\delta a)\overline{(b'+\delta b)}-s^2a\overline b\}\,dx.
\tag{26.17}
$$

As a map to the antidual it is injective, has closed range, and
has cokernel dimension one. Here is the half-line calculation,
including its natural boundary. The $H^1$ Riesz representation
writes every continuous antilinear functional as
$F(b)=\int(F_0\overline b+F_1\overline{b'})$ with
$F_0,F_1\in L^2$ and a norm-controlled choice. Setting
$y=a'-\delta a-F_1$, the equation $S_\delta a=F$ becomes

$$
\frac{d}{dx}\binom{a}{y}
 =\begin{pmatrix}\delta&1\\-s^2&\delta\end{pmatrix}\binom{a}{y}
       +\binom{F_1}{\delta F_1-F_0},
\qquad y(0)=0,
\tag{26.18}
$$

Write the matrix as $M_\delta$. Its eigenvalues are $\delta\pm is$.
Before enforcing $y(0)=0$, the unique square-integrable solution is

$$
\binom{a(x)}{y(x)}
 =-\int_x^\infty e^{M_\delta(x-t)}
                       \binom{F_1(t)}{\delta F_1(t)-F_0(t)}\,dt.
\tag{26.19}
$$

For $t\ge x$, the exponential is bounded by a fixed multiple of
$e^{-\delta(t-x)}$. Young's convolution inequality and (26.18)
give a norm-controlled solution $a,y\in H^1$. A homogeneous
square-integrable solution vanishes, since both characteristic
exponents have positive real part. The only obstruction is therefore
the single scalar $y(0)$.

The adjoint null vector is
$\phi_\delta(x)=e^{-\delta x}\cos(sx)$, with natural boundary
$\phi_\delta'(0)+\delta\phi_\delta(0)=0$. Integration by parts
in (26.18), using $\phi_\delta(0)=1$, gives
$y(0)=F(\phi_\delta)$. Thus the range is exactly
$\{F:F(\phi_\delta)=0\}$. It is a closed hyperplane, and the
inverse on that range is bounded by (26.19). Consequently
$S_\delta$ has a bounded left inverse and complex Fredholm index
$-1$. This scalar natural boundary is part of the reference
calculation; it is not a physical boundary imposed on the core.

(5) The index of the unchanged global weighted map.
First consider $P_\delta+K_0m$ from $\mathcal H_\delta$ to
$(\mathcal H_{-\delta})^*$, where $K_0m$ means the mass pairing
$K_0\int mf\overline\zeta\,d\xi$. Conjugate to $\mathcal H$
and use (26.12). Its block diagonal reference consists of
$S_\delta$ and the actual shifted coercive $Y$ block from (3).
All remaining noncompact blocks have norm at most

$$
C(\sqrt S+S),\qquad S=e^{-2L},
\tag{26.20}
$$

in the scalar $H^1\mathbin{\dotplus}Y$ norm, with $C$ independent
of further large $L$. In detail,

$$
D(a\psi)=p_\psi a'+r_\psi a,\qquad
p_\psi=\nu\psi,\qquad r_\psi=4c\psi'-\nu\psi.
\tag{26.21}
$$

Both angular coefficients are unweighted $L^2$ by
$\psi\in\mathcal H_c$ and $c^2\le c$. The tail central norm
of $a\psi$ is bounded by $C\sqrt S\|a\|_{H^1}$. Pairing it
with the entire central norm of $Y$ gives the two central cross
bounds $C\sqrt S\|a\|_{H^1}\|y\|_Y$. The complete-source
cross blocks are bounded by $CS\|a\|_{H^1}\|y\|_Y$, using
$\|B_n\|_\infty\le Kt$ and $A$ control of unweighted $L^2$.
The scalar central and source diagonal errors are $O(S)$.
Conjugation replaces $a'$ by $a'-\delta a$ and $Dv$ by
$Dv\pm\delta\nu v$, giving the same bounds. These are precisely
the full graph estimates (25.15)--(25.16), now with the actual
original core retained in $Y$.

The other blocks are compact. The inner scalar lift contributes
only $a(0)$ to scalar/$Y$ pairings, so those blocks are finite
rank; its scalar diagonal and the longitudinal seam trace are rank
one. Any compactly supported mass pairing, including a portion on
a finite exterior collar, is compact by (1)'s local $L^2$
compactness and bounded local restriction of test functions. The
principal $Y/Y$ form, including its core, seam and central terms,
has not been deleted or approximated.

Let $B_0$ be the block diagonal reference and choose its bounded
left inverse $R$. It has $\dim\ker R=1$, and its norm can be
bounded by the maximum of the scalar left-inverse bound and $2$.
These bounds, and the tail constants in (26.20), are independent
of further large $L$. Enlarge $L$ until
$\|R\|C(\sqrt S+S)<1/2$. For the small remainder $E$,

$$
R(B_0+E)=I+RE
\tag{26.22}
$$

is invertible by the operator-norm Neumann series. Hence $B_0+E$
is injective with closed range. Its codomain is the direct sum of
that range and $\ker R$: for any codomain vector $z$, subtract
$(B_0+E)(I+RE)^{-1}Rz$, leaving an element of $\ker R$; the
intersection is zero by (26.22). Its index is therefore still $-1$.

Adding the remaining compact blocks preserves Fredholmness and
index. This is the classical compact-perturbation theorem for
bounded Fredholm operators on Hilbert spaces, in the framework of
Kato, *Perturbation Theory for Linear Operators*, Chapter IV,
Section 5. In the present setting one can see its content directly:
a generalized inverse of a Fredholm map has both compositions equal
to the identity modulo finite-rank projections; after a compact
perturbation both remain identity modulo compact operators.
Compactness then gives finite-dimensional kernels, closed range and
finite-dimensional cokernels. Splitting off those finite-dimensional
spaces along the compact-perturbation path reduces constancy of the
index to finite-dimensional rank-nullity. This applies to the bounded
maps between the specified completed spaces; it is not an exterior
geometric Fredholm assertion.

Finally the entire auxiliary shift $K_0m$ is compact as a map
$\mathcal H_\delta\to(\mathcal H_{-\delta})^*$: on its fixed
support use bounded local $H^1$ restriction, compact $L^2$
restriction and bounded local test restriction. Removing it proves
that the actual unchanged map has

$$
P_\delta\text{ Fredholm},\qquad
\operatorname{ind}_{\mathbb C}P_\delta=-1.
\tag{26.23}
$$

If $K=\ker P_\delta$, $k_0=\dim_{\mathbb C}K$, and

$$
Z_0=\{z\in\mathcal H_{-\delta}:
                q_{\rm orig}(u,z)=0\text{ for every }u\in\mathcal H_\delta\},
\qquad \dim_{\mathbb C}Z_0=k_0+1,
\tag{26.24}
$$

then $Z_0$ is the range annihilator. No inverse of the unshifted
original core and no absence of zero modes has been assumed.

(6) The exterior residuals annihilate every decaying zero mode.
Apply Theorem 25.3 directly to obtain its full coupled $f_+$, and
put $f_-=\overline{f_+}$. Let $\chi$ be a real original smooth
radial cutoff, zero on and inside a ball larger than their exterior
radius and one farther out. Set $U_\pm=\chi f_\pm$. They have
the original local free closure everywhere and vanish near the pole.
Their residuals, defined by local form pairings, are

$$
F_\pm(\zeta)=4q_{\rm orig}(U_\pm,\zeta).
\tag{26.25}
$$

They are compactly supported continuous local-form functionals:
outside the cutoff collar the exact exterior weak equation holds.
Thus $F_\pm\in(\mathcal H_{-\delta})^*$. On a remote tail,
(25.20) gives

$$
w_{U_\pm}=e^{\pm is\ell}\psi+r_\pm,
\qquad r_\pm,\ \partial_\ell r_\pm\in X_\delta,
\tag{26.26}
$$

where $X_\delta$ is the decaying exterior graph-energy space of
Section 25. Decrease $\delta$ if necessary. The energy of these
waves on remote unit longitudinal collars is bounded, by the
continuous weighted representatives in (25.20) and their homogeneous
parts. These are the exterior supplier's conclusions.

Hermitian symmetry embeds all of $K$ into $Z_0$. For $v\in K$
and $u\in\mathcal H_\delta\subset\mathcal H_{-\delta}$,
$q_{\rm orig}(u,v)=\overline{q_{\rm orig}(v,u)}=0$.
Moreover

$$
F_+(v)=F_-(v)=0\qquad(v\in K).
\tag{26.27}
$$

To prove this, let $\eta_T$ equal one for $\ell\le T$ and zero
for $\ell\ge T+1$, with uniformly bounded derivative and $T$
beyond the residual collar. Compact support of $F_U$ gives
$F_U(v)=4q_{\rm orig}(U,\eta_Tv)$. The equation for $v$, extended
to compact local-free tests by original form continuity, gives
$4q_{\rm orig}(\eta_TU,v)=0$. Their difference is the exact
cutoff commutator in $[T,T+1]$. Potential and angular zeroth-order
terms cancel. The remaining $C$ and full $tD$ pairings are bounded
by a constant times the two strip energy norms. The norm for $U$
is bounded, whereas

$$
\int_T^{T+1}\mathcal E[w_v]\,d\ell
 \le C e^{-2\delta(T-L)}\|v\|_{\mathcal H_\delta}^2.
\tag{26.28}
$$

Here conjugating the derivative and $D$ terms only adds terms
controlled by $A$. The commutator tends to zero, proving (26.27).
This applies to every member of $K$, whether or not it belongs to
global physical $L^2$.

(7) Compatibility with the actual core and a nonzero channel pair.
The classes $[F_+],[F_-]$ in $\operatorname{coker}P_\delta$ are
functionals on $Z_0$. By (26.27) both annihilate its
$k_0$-dimensional subspace $K$. Since $\dim Z_0=k_0+1$, these
two classes span a space of dimension at most one. Therefore some
$a_+,a_-\in\mathbb C$, not both zero, satisfy
$a_+F_++a_-F_-\in\operatorname{Ran}P_\delta$. Choose
$v\in\mathcal H_\delta$ with

$$
P_\delta v=-a_+F_+-a_-F_-,\qquad
u=v+a_+U_++a_-U_-.
\tag{26.29}
$$

The function $u$ has the original local free closure and solves the
original weak equation on all of $\mathbb R^3$ in the symmetric
sector. The finite-dimensional kernel has been handled by compatibility,
without a core inverse or an exclusion of resonant cases.

The two exterior channels are independent modulo
$\mathcal H_\delta$. Indeed, if $a_+U_++a_-U_-\in\mathcal H_\delta$,
subtract the weighted remainders in (26.26) and project onto $\psi$
in the $C$ pairing. The function
$a_+e^{is\ell}+a_-e^{-is\ell}$ would belong to unweighted
$L^2$ on a half-line. But

$$
\int_L^T|a_+e^{is\ell}+a_-e^{-is\ell}|^2\,d\ell
 =(|a_+|^2+|a_-|^2)(T-L)+O(1),
\tag{26.30}
$$

which is impossible for a nonzero pair. Thus $u$ is nonzero and
its exterior channel pair is genuinely nonzero. This proves a
connection to the regular core; it does not infer a global amplitude
from exterior normalization alone.

(8) Both strong traces for the decaying global correction.
On a sufficiently remote exterior the correction $w=w_v$ solves
the exact homogeneous equation $p(w,z)=0$ and has positive-$\delta$
weighted energy. To obtain both strong traces it remains to control
its longitudinal derivative in the same graph space, separately
from the integrated decay of $w$.

First consider a compact longitudinal interval $I$ in that exterior.
Its energy controls the unweighted derivative $w_\ell$. In fact

$$
\nu w_\ell=Dw-4cw_a+\nu w,
\qquad \inf_J(c+\nu^2)>0,\qquad c^2\le c,
\tag{26.31}
$$

and $t$ has a positive minimum on $I$. Combining these facts with
$C[w_\ell]$ bounds $\|w_\ell\|_{L^2(I\times J)}$ by the local
energy norm.

For nested compact intervals $I_0\Subset I_1$, take a smooth
$\eta=1$ on $I_0$ supported in $I_1$, and define
$\Delta_h=(T_h-I)/h$, $T_hw(\ell)=w(\ell+h)$.
Use the exact weak difference-quotient test
$-\Delta_{-h}(\eta^2\Delta_hw)$. It belongs to the same local
graph completion: for each nonzero $h$, tensor density and translation
justify it, since $t$ is bounded above and below locally. The
operator $D$ commutes with longitudinal translation. Also
$|t'|=2t$, and Proposition 25.2 supplies longitudinal Lipschitz
control of $B_n$ in unweighted $L^\infty(J)$.

Expanding this test produces the positive principal terms
$C[(\Delta_hw)_\ell]$, $A[\Delta_hw]$ and
$t\|D\Delta_hw\|_2^2$ on $I_0$. Lower-order $h$ and source
terms are bounded by $C\|\Delta_hw\|_{L^2(I_1\times J)}^2$.
Terms with derivatives of $\eta$ have the same bound after
Cauchy--Schwarz and absorption; coefficient-difference terms are
bounded by half the principal energy plus
$C\int_{I_1}\mathcal E[w]$. Consequently

$$
\int_{I_0}\mathcal E[\Delta_hw]\,d\ell
 \le C_{I_0,I_1}\left(
       \int_{I_1}\mathcal E[w]\,d\ell
           +\|\Delta_hw\|_{L^2(I_1\times J)}^2\right).
\tag{26.32}
$$

The last norm is uniformly bounded by the unweighted $w_\ell$
control just proved on a slightly larger interval. Weak compactness
therefore gives $w_\ell$ in the full local energy, including
$Dw_\ell$. This is the classical weak difference-quotient method
applied to the displayed graph form. It uses no angular derivative
of the potential.

Choose a remote smooth cutoff $\eta$ zero before a collar and one
after it, and extend $r=\eta w$ by zero to the whole line. Use the
original coefficients on the right and exactly the constant-left
auxiliary coefficients of (25.9) on the left. Choose the cutoff
collar where those coefficients already agree with the original
ones. In the whole-line equation $P_{\rm aux}r=F$, the residual is
supported in that collar and is exactly

$$
F(z)=\int\eta'\{C(w,z_\ell)-C(w_\ell,z)
        +t(\langle\nu w,Dz\rangle-\langle Dw,\nu z\rangle)\}\,d\ell.
\tag{26.33}
$$

Subtracting $p(w,\eta z)=0$ from $p(\eta w,z)$ proves the formula;
all multiplication terms cancel. The preceding local derivative
result makes both $F$ and its longitudinal derivative bounded
functionals on the oppositely weighted energy space. Differentiating
the collar formula requires only $w_\ell$ in the local energy,
$t'$, $\eta''$ and the fixed angular coefficients.

For $\Delta_hr$ the exact translated equation is

$$
P_{\rm aux}\Delta_hr
 =\Delta_hF+(P_{\rm aux}-P_{{\rm aux},h})T_hr/h,
\tag{26.34}
$$

where $P_{{\rm aux},h}$ has translated $t,\widetilde B$.
The bounds (25.18),
$|\Delta_ht|\le Ct$ and $\|\Delta_h\widetilde B\|_\infty\le Ct$,
and weighted Cauchy--Schwarz bound the right side uniformly in
the weighted energy antidual. Translation is bounded in the graph
space by $t(\ell+h)/t(\ell)\le e^{C|h|}$ and the corresponding
exponential-weight identity. Projection onto $\psi$ and its full
$C$-orthogonal complement is bounded there by (26.21), so this is
precisely the $X_\delta$ realization of Section 25.

Apply the actual full-line inverse (25.11)--(25.16), with this same
positive $\delta$ and a sufficiently large auxiliary radius. It
bounds $\Delta_hr$ uniformly in $X_\delta$. The injective local
distributional realization identifies its weak limit as $r_\ell$.
Thus both $r$ and $r_\ell$ belong to $X_\delta$; the auxiliary
left continuation has served only as an inverse for this cutoff
exterior function.

In particular

$$
e^{\delta\ell}r\in H^1(\mathbb R;\mathcal H_c),\qquad
e^{\delta\ell}r_\ell\in H^1(\mathbb R;L^2(J,c\,da)).
\tag{26.35}
$$

The second assertion uses the longitudinal derivative energy of
$r_\ell$, not differentiation of an asymptotic ansatz. For a
Hilbert-valued $H^1$ function $U$ on a half-line, the classical
norm-square identity, an $L^2$-vanishing sequence at infinity and
Cauchy--Schwarz give

$$
\|U(t)\|^2\le2\int_t^\infty\|U(\tau)\|\,\|U'(\tau)\|\,d\tau
                    \longrightarrow0.
\tag{26.36}
$$

It also gives the continuous representatives. Applying it separately
to the two functions in (26.35), and using $r=w_v$ on a remote
tail, yields

$$
\|w_v(\ell)\|_{\mathcal H_c}
       +\|\partial_\ell w_v(\ell)\|_{L^2(J,c\,da)}\longrightarrow0.
\tag{26.37}
$$

(9) Reality, all original tests and the exact quantifiers.
The equation and the local free completions are invariant under
conjugation. Since $U_-=\overline{U_+}$, the outgoing coefficient
in $\operatorname{Re}u$ is
$b_1=(a_++\overline{a_-})/2$, and that in
$\operatorname{Im}u$ is $b_2=(a_+-\overline{a_-})/(2i)$.
They cannot both vanish unless $a_+=a_-=0$. Take $f_0$ to be the
corresponding real or imaginary part with nonzero coefficient $b$.
It is real, nonzero, axisymmetric and even in $z$. The two strong
exterior traces of Theorem 25.3, (26.26) and the separate correction
limits (26.37) give exactly both limits in (26.7), with the stated
continuous representatives and $b\ne0$.

The local free closure under every compact smooth multiplier follows
from (1) for $v$ and Theorem 25.3 for the cutoff waves; the latter
vanish near the pole. Equation (26.29) cancels their residuals
against every compact smooth symmetric original test, including
through the pole. There is therefore no pole-supported source or
interface defect.

For any original compact smooth test $\phi$, first average over
horizontal rotations. The full original form is rotation invariant,
and $f_0$ is axisymmetric, so this preserves its pairing with $f_0$.
Then average the axisymmetric image under $z$ reflection, using
exactly the $m=0$ reflection invariance in Proposition 24.4. Both
averages preserve compact smoothness, including at the pole. The
result lies in the symmetric test sector already treated; hence
$q_{\rm orig}(f_0,\phi)=0$ for every original test. This uses no
reflection symmetry assertion for nonaxisymmetric sectors and
makes no angular truncation of the original equation.

The pair $n\ge2$ and $g\in(\lambda_n,g_n^{\rm iso})$ was arbitrary.
The weight, radius, compact shift and auxiliary inverse bounds may
depend on this fixed pair. The entire compact shift has been removed;
the original core, complete source, all natural endpoints, raw mass,
original fields and clock have been retained. Lemma 24.2 supplies
a finite nonempty isolation interval for each $n$, so
$g_n^0=g_n^{\rm iso}$ covers every fixed coupling in that full
open interval. This proves the theorem. $\square$

**Definition 26.3 (scope of the core phase datum).**
The datum furnished by Theorem 26.2 is the zero-energy original
regular-core standing channel with nonzero coefficient and both
strong traces. Its source-specific content is the original-form
weighted Fredholm calculation, the compatibility with every allowed
decaying kernel and the return of both strong traces for the core
correction. The natural angular isolation and endpoint conclusions,
complete-source derivative estimate, exterior waves and whole-line
exterior inverse remain the conditional results of Sections 24--25.
The Rellich, Riesz/adjoint, compact Fredholm perturbation,
Neumann-series and Hilbert-valued $H^1$ arguments inside the proof
are classical functional analysis applied to the specified spaces.
No external scattering or geometric $b$-operator applicability
assertion is a premise of this connection.

Theorem 26.2 supplies neither the original low-energy decaying
solutions nor coupled physical mass-wall matching. The graph-domain
residual $o(E)$, an actual quasimode construction satisfying (24.18),
its multiplicity-exhaustion obligations and the full geometric
eigenvalue-phase limit remain separate unresolved obligations.
The conditional implication in Application 24.6 is unchanged.
The physical mass is still $e^{2\ell}da$ and is not diagonalized
by the auxiliary weighted angular basis. The theorem asserts no
parameter-uniform estimate, global $L^2$ or operator-domain status
for $f_0$, physical realization or literature priority.

## 追加锚（本行以下为增补区）


## 27. Exact positive-energy exterior solutions without a phase prescription

**Definition 27.1 (inherited data and the positive-energy exterior form).**
Assume precisely Definition 18.1 of the
[original source at revision d6d829c43b0ed4f127a09666bc40088b6f440b94](https://github.com/the-omega-institute/trureturing/blob/d6d829c43b0ed4f127a09666bc40088b6f440b94/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
with suppliers C and V at
5cec4fa83ae7bbb4e787c42606525db4cd11ed48 as fixed in its Definition 1.1.
These are exactly the analytic hypotheses of Definitions 24.1, 25.1
and 26.1. All assertions in Sections 27--29 are ordinary conditional
analysis under them. Fix any integer $n\ge2$ and any real
$g\in(\lambda_n,g_n^{\rm iso})$, where the finite
$g_n^{\rm iso}>\lambda_n$ is supplied by Lemma 24.2.
Constants may depend on this fixed pair; no uniformity in $n,g$ is
assumed or asserted.

Retain the identity unit source, raw measures, covariance-$2$ heat
clock, full time integral and whole unweighted omitted fibre in
(26.1), with $\epsilon=1$. Retain the original fields $U,V,Z$, free
closure $\mathcal H_1$, form $q_{\rm orig}=T_1-gW_{n,1}$ and
Friedrichs operator of (26.2). There is no new source, boundary
realization or tail hypothesis. The actual gauge $R_g$, dilation,
angular parametrization, raw Jacobian and normalized cylinder image
$w_f$ are exactly (26.3).

Use $J,c,q_n,\mathcal H_c,A,C,Q,h$ from (25.1), with all forms
linear in the first argument. Unless a $C$ subscript is displayed,
angular inner products and norms use unweighted $L^2(J,da)$.
In particular $\|b\|_{\mathcal H_c}^2=A[b]+\|b\|_2^2$ and
$\|b\|_C^2=C[b]$. Reuse, without reproving, the positive real even
$\psi$ and $s=2\pi L_{n,g}>0$ of Proposition 24.3, together with
(25.8) and (26.5):

$$
\begin{aligned}
C[\psi]&=1,& h(\psi,b)&=-s^2C(\psi,b)\quad(b\in\mathcal H_c),\\
V_{\rm ev}&=\{b\in\mathcal H_c:b(-a)=b(a),\ C(b,\psi)=0\},\\
A[b]&\ge\lambda_0\|b\|_2^2\quad(b\in\mathcal H_c),&
h[v]&\ge\kappa A[v]\quad(v\in V_{\rm ev}),\qquad\lambda_0,\kappa>0.
\end{aligned}
\tag{27.1}
$$

The space $V_{\rm ev}$ is the entire even natural complement.
No endpoint value is imposed on it or on $\mathcal H_c$.
All integer angular sectors of the original operator retain the
natural domains in (18.1); the symmetry used below is precisely
Proposition 24.4's reducing axisymmetric $z$-even sector $\mathcal S$.

For $f=e^{-\ell}w/\sqrt{2\pi}$ and
$f_z=e^{-\ell}z/\sqrt{2\pi}$ in this sector, adding the physical
mass pairing to (25.7) gives the exact identity

$$
\begin{aligned}
4\{q_{\rm orig}(f,f_z)+E\langle f,f_z\rangle_{L^2(d\xi)}\}
 &=P_E(w,z)\\
 &=\int\bigl\{C(w_\ell,z_\ell)+h(w,z)
       +e^{-2\ell}\langle Dw,Dz\rangle
       -g\langle B_n(\ell)w,z\rangle
       +Ee^{2\ell}\langle w,z\rangle\bigr\}\,d\ell,\\
D&=\nu(\partial_\ell-1)+4c\partial_a,\qquad\nu=2\sin a,\\
4\|f\|_{L^2(d\xi)}^2&=\int e^{2\ell}\|w(\ell)\|_2^2\,d\ell.
\end{aligned}
\tag{27.2}
$$

The identity is initially on compact longitudinal natural tensors;
its local free-form extensions are those of (25.22).
The central, source and mass brackets in (27.2) are unweighted.
Here $B_n$ is the complete-source error of (20.18) and (25.2).
Corollary 20.3 and Proposition 25.2 already give, on a sufficiently
remote exterior and uniformly through both angular endpoints,

$$
\|B_n(\ell)\|_\infty+
 \|\partial_\ell B_n(\ell)\|_\infty\le C_Be^{-2\ell}.
\tag{27.3}
$$

Thus (27.3) is a reused conclusion for the complete time and fibre
integrals, rather than an additional assumption.
For $0<E<1$, put $T_E=\tfrac12\log(1/E)$ and $x=\ell-T_E$.
In these actual coordinates the mass coefficient becomes $e^{2x}$,
the central coefficient becomes $Ee^{-2x}$, and
$B_n(T_E+x)=O(Ee^{-2x})$ on its original exterior range.
The resulting comparison wall form is

$$
p_*(u,z)=\int_{\mathbb R}
 \{C(u_x,z_x)+h(u,z)+e^{2x}\langle u,z\rangle\}\,dx.
\tag{27.4}
$$

Its mass is the identity in unweighted $da$; the $C$-orthogonal
channel decomposition does not diagonalize that mass.
Equation (27.4) defines a comparison equation and does not replace
(27.2).

**Theorem 27.2 (exact exterior physical-free-tail family).**
Under Definition 27.1, for every fixed $R_0>1$ and every $E>0$
there is a nonzero real $f_E\in\mathcal S$ on
$\Omega_{R_0}=\{\xi:R_g(\xi)>R_0\}$ such that
$\chi f_E\in\mathcal H_1$ for every
$\chi\in C_c^\infty(\Omega_{R_0})$, and

$$
q_{\rm orig}(f_E,\phi)+E\langle f_E,\phi\rangle_{L^2(d\xi)}=0
\quad\bigl(\phi\in C_c^\infty(\Omega_{R_0};\mathbb C)\bigr).
\tag{27.5}
$$

Tests include every nonaxisymmetric original compact smooth test.
For every finite $R_0<r_1<r_2$ and every smooth real radial
$\eta$ on $\mathbb R^3$ with $0\le\eta\le1$,
$\eta=0$ on $R_g\le r_1$ and $\eta=1$ on $R_g\ge r_2$,

$$
\eta f_E\in\mathcal H_1.
\tag{27.6}
$$

The same $R_0$ works for all $E>0$. No boundary value at $R_0$,
nonzero channel coefficient, common phase or strong overlap estimate
is part of this assertion.

Proof. Let $V_D$ be the original-free-norm closure of
$C_c^\infty(\Omega_{R_0};\mathbb C)$ in the sector $\mathcal S$.
Its zero extensions belong to $\mathcal H_1$. Rotation averaging,
then $z$ reflection averaging inside $m=0$, preserve this core,
its free norm and the original form by Proposition 24.4.
The auxiliary zero-extension space is used to construct exterior
solutions; it prescribes no boundary condition in the theorem.

For fixed $E>0$, the positive form
$T_1(u,v)+E\langle u,v\rangle$ is a Hilbert inner product on $V_D$,
equivalent to the original free norm with constants allowed to
depend on $E$. Riesz representation gives an isomorphism from
$V_D$ to its antidual. Multiplication by $\sqrt{M_{n,1}}$ is compact
from $V_D$ to $L^2(d\xi)$. Indeed, the zero extensions have the
original free norm, the potential is bounded off the omitted pole,
and original (15.8)--(15.9) give Euclidean $H^1$ control on bounded
annuli. Local Rellich compactness therefore gives compactness on
such annuli. Original (15.7) gives
$\sup_{R_g>r}M_{n,1}\le C r^{-2}$, so the remaining tail has
operator norm tending to zero. This is also the restriction of
original (15.13)'s compact multiplication map.
Consequently

$$
\mathcal B_E(u,v)=q_{\rm orig}(u,v)+E\langle u,v\rangle
\tag{27.7}
$$

is the Riesz isomorphism minus a compact Hermitian map, and is
Fredholm of index zero. The Riesz/adjoint framework is the classical
Hilbert-space framework of Folland, *Real Analysis*, second edition,
Chapter 5; the compact-perturbation and Fredholm-alternative step is
Kato, *Perturbation Theory for Linear Operators*, Chapter IV,
Section 5, applied to this bounded map $V_D\to V_D^*$.
The local trace and Rellich uses concern the Euclidean $H^1$
realization furnished by original (15.8)--(15.13), not a global
identification of $\mathcal H_1$ with isotropic $H^1$.

If $\ker\mathcal B_E\ne0$, choose a nonzero real kernel vector
$u$ and set $f_E=u$ on the exterior. Such a real vector exists
because coefficients, core and sector are conjugation invariant.
This branch has zero extension in $\mathcal H_1$.

If $\ker\mathcal B_E=0$, the index-zero Fredholm alternative gives
a bounded inverse $V_D^*\to V_D$. Choose a real smooth radial
collar lift $F$, equal to one near the smooth compact surface
$R_g=R_0$ and zero for sufficiently large $R_g$, restricted to
the exterior. Its ordinary boundary trace is one. Local original
free energy controls ordinary $H^1$ on this collar by (15.8),
and the continuous $H^1$ trace of every member of $V_D$ is zero.
Hence $F\notin V_D$. Its compact collar support, finite original
derivatives and the bounded collar potential make
$z\mapsto-\mathcal B_E(F,z)$ a bounded antidual functional.
Solve $\mathcal B_E(u,z)=-\mathcal B_E(F,z)$ in $V_D$ and put
$f_E=F+u$. It is real, solves the equation on sector tests and
is nonzero because its trace is one. There is no energy exception:
the first branch handles every nontrivial kernel.

For an arbitrary complex original compact exterior test, average
first over rotations and then over $z$ reflection within the
axisymmetric image. Both averages preserve compact exterior support
and the pairing with $f_E$, by Proposition 24.4. The averaged test
is a sector test, proving (27.5) for all original tests. No test
on the omitted boundary has been used.

The original product rules extend by compact-core closure to bounded
smooth multipliers whose $U,V,Z$ derivatives are bounded and supported
on a compact annulus. The zero-extension part $u$ already lies in
$\mathcal H_1$. The collar lift has a smooth compact extension,
and every stated $\eta$ vanishes in a neighborhood of the omitted
boundary. Multiplying either part by $\eta$ and extending across
that boundary therefore gives an element of $\mathcal H_1$.
The same argument applies to each compact exterior multiplier $\chi$.
This proves actual physical $L^2$ membership and all three original
$U,V,Z$ tail energies in (27.6). Choosing the indicated branch for
each $E>0$ gives a family on one exterior. The construction relates
neither the oscillatory amplitudes nor their phases at different
energies. $\square$

## 28. The full coupled comparison wall and both strong left traces

**Definition 28.1 (wall energy, mass homotopy and opposite weights).**
Continue with Definition 27.1's arbitrary fixed $n,g$.
For $u=\alpha(x)\psi+v(x)$, $v(x)\in V_{\rm ev}$, put
$m=\|\psi\|_2^2$ and $d=\|c\psi\|_2^2$.
Both are finite and positive, and $md\ge1$ by $C[\psi]=1$.
Let $M_\theta$ be the Hermitian polarization of

$$
M_\theta[u]=m|\alpha|^2+\|v\|_2^2
       +2\theta\operatorname{Re}\langle\alpha\psi,v\rangle,
\qquad 0\le\theta\le1.
\tag{28.1}
$$

Define $X$ as the completion of compact longitudinal finite natural
tensors in the even angular domain, with squared norm

$$
\|u\|_X^2=\int_{\mathbb R}
 \bigl\{|\alpha_x|^2+|\alpha|^2+C[v_x]+A[v]
              +e^{2x}(m|\alpha|^2+\|v\|_2^2)\bigr\}\,dx.
\tag{28.2}
$$

The completion has its distributional realization by the closed
angular and longitudinal derivatives. It retains every component
of $V_{\rm ev}$ and the original natural endpoints.
Let $p_\theta$ be (27.4) with $M_\theta(u,z)$ in place of
$\langle u,z\rangle$. Choose
$0<\delta<\min(1/2,\sqrt\kappa/2)$ and a smooth nonnegative $\varphi$
with $\varphi(x)=-\delta x$ for $x\le-2$, $\varphi(x)=0$ for
$x\ge2$, and $|\varphi_x|\le\delta$. Its transition can be chosen
with all derivatives used below bounded. Put $\rho=e^\varphi$.
Initially on compact tensors, the opposite-weight conjugation is

$$
\begin{aligned}
b_\theta(Y,Z)&=p_\theta(\rho^{-1}Y,\rho Z)\\
 &=\int_{\mathbb R}\bigl\{
 C(Y_x-\varphi_xY,Z_x+\varphi_xZ)+h(Y,Z)
                   +e^{2x}M_\theta(Y,Z)\bigr\}\,dx.
\end{aligned}
\tag{28.3}
$$

This formula defines its bounded extension $X\to X^*$.
The auxiliary homotopy is used only to calculate the index;
$p_1=p_*$ has exactly the physical unweighted angular mass.

**Theorem 28.2 (normalized standing solution of the coupled wall).**
There exist a nonzero real even solution $W$ of
$p_*(W,z)=0$ for every compact natural test, a complex number
$\beta$ with $|\beta|=1$, and $C<\infty$, $\delta>0$ as in
Definition 28.1 such that, for every $x\le-2$,

$$
\begin{aligned}
&\|W(x)-2\operatorname{Re}(\beta e^{isx})\psi\|_{\mathcal H_c}\\
&\qquad+
 \|W_x(x)-2\operatorname{Re}(is\beta e^{isx})\psi\|_C
                         \le Ce^{\delta x}.
\end{aligned}
\tag{28.4}
$$

Both slice representatives are continuous in their displayed spaces.
For every finite $x_0$,

$$
\begin{aligned}
\int_{x_0}^\infty
 \{C[W_x]+A[W]+e^{2x}\|W\|_2^2\}\,dx&<\infty,\\
W_x&\in L^2((x_0,\infty);\mathcal H_c).
\end{aligned}
\tag{28.5}
$$

The equation retains the full even natural angular space and
unweighted physical mass. It is a conclusion for the comparison
wall (27.4).

Proof. First establish positivity of the entire mass homotopy.
Since $C(v,\psi)=0$, the unweighted vector $v$ is orthogonal to
$c\psi$. Projecting $\psi$ onto that orthogonal complement gives

$$
|\langle\psi,v\rangle|
 \le\sqrt{m-1/d}\,\|v\|_2.
\tag{28.6}
$$

Thus $r=\sqrt{1-1/(md)}<1$ and

$$
(1-r)(m|\alpha|^2+\|v\|_2^2)
 \le M_\theta[u]\le
(1+r)(m|\alpha|^2+\|v\|_2^2).
\tag{28.7}
$$

Indeed the absolute cross term is at most
$2r\sqrt m|\alpha|\|v\|_2$ and
$2\sqrt m|\alpha|\|v\|_2\le m|\alpha|^2+\|v\|_2^2$.
At $\theta=1$, $M_1[u]=\|u\|_2^2$ exactly.
At $\theta=0$ only the cross mass is removed; every complementary
angular component remains.

The $C$ projection onto $\psi$ is bounded in $\mathcal H_c$,
and $C$ orthogonality diagonalizes the longitudinal derivative.
Together with $A\ge\lambda_0\|\cdot\|_2^2$ and (28.7), this
proves equivalence of (28.2) with
$\int(C[u_x]+A[u]+e^{2x}\|u\|_2^2)\,dx$ and boundedness of
(28.3). It also gives an injective distributional realization:
Cauchy sequences have compatible local distributional limits for
$u,u_x$ and the angular derivative, so a zero distribution has
zero norm.

The real diagonal of (28.3) loses only
$(\varphi_x)^2C[Y]$. On the complement, $C[v]\le A[v]$ gives

$$
h[v]-(\varphi_x)^2C[v]\ge(\kappa-\delta^2)A[v].
\tag{28.8}
$$

The scalar part is bounded below by
$-(s^2+\delta^2)|\alpha|^2$. The uniformly positive mass in
(28.7) absorbs this scalar loss on a sufficiently remote right
half-line. Hence, for fixed sufficiently large $R$,

$$
\|Y\|_X^2\le C\left(
 \operatorname{Re}b_\theta(Y,Y)+\int_{x<R}|\alpha(x)|^2\,dx\right),
\tag{28.9}
$$

uniformly for $\theta\in[0,1]$.

We next control the left half-line without losing high angular
modes. On $x<-R$ the weight derivative is $-\delta$.
After dropping the exponentially small mass, use the block diagonal
constant-coefficient form on

$$
H=H^1(\mathbb R)\psi\mathbin{\dotplus}
 \overline{\{\text{finite natural }V_{\rm ev}\text{ tensors}\}}
 ^{\left(\int(C[v_x]+A[v])\,dx\right)^{1/2}}.
\tag{28.10}
$$

Its complementary block has coercive real part at least
$\int(C[v_x]+(\kappa-\delta^2)A[v])\,dx$.
Riesz representation and the same estimate for its adjoint give
an inverse to the full complementary block. The scalar Fourier
multiplier is

$$
\xi^2-2i\delta\xi-\delta^2-s^2,
\qquad
\inf_{\xi\in\mathbb R}
 \frac{|\xi^2-2i\delta\xi-\delta^2-s^2|}{1+\xi^2}>0.
\tag{28.11}
$$

Its imaginary part vanishes only at zero, where its real part
is negative; the quotient tends to one at infinity.
Plancherel therefore gives a bounded scalar isomorphism
$H^1\to H^{-1}$. These are the classical Hilbert and whole-line
Fourier arguments of Folland, Chapters 5 and 8, applied to
(28.10); they assert no additional angular endpoint regularity.

Let $\chi_-$ be one on $x<-R-1$ and zero on $x>-R$.
Multiplying $b_\theta Y$ by this cutoff gives a bounded element
of $H^*$, since on this left support the $X$ norm of a cut-off
$H$ test is bounded by its $H$ norm. The omitted mass has norm
$O(e^{-2R})$ on $H$ and is absorbed after increasing $R$.
In the cutoff commutator, integrate the term involving $Y_x$
once onto the test. The resulting terms pair only $Y$ with a
test or its first longitudinal derivative on the fixed transition
interval, and are bounded by the local $L^2(C)$ norm of $Y$.
The inverse just constructed gives, for a fixed compact interval $I$,

$$
\|\chi_-Y\|_H\le C\bigl(
 \|b_\theta Y\|_{X^*}+\|Y\|_{L^2(I;C)}\bigr).
\tag{28.12}
$$

The scalar integral in (28.9) on the remaining bounded interval
is controlled by the same local $C$ norm, since
$|C(Y,\psi)|^2\le C[Y]$. Insert (28.12) into (28.9) and use
Young's inequality to obtain

$$
\|Y\|_X\le C\bigl(
 \|b_\theta Y\|_{X^*}+\|Y\|_{L^2(I;C)}\bigr).
\tag{28.13}
$$

The adjoint has the same real diagonal, the conjugate nonvanishing
scalar multiplier, and the same cutoff commutator estimate; it
satisfies (28.13) too.

The restriction $X\to L^2(I;C)$ is compact. To see this on the
entire angular space, use Proposition 24.3's compact-resolvent
weighted angular realization after a positive shift.
Its finite spectral projections approximate the $C$ norm uniformly
on bounded angular form-energy sets. Each projected longitudinal
coefficient is bounded in $H^1(I)$ because $C[Y_x]$ is controlled.
Finite-dimensional one-dimensional Rellich compactness applies to
these coefficients, and the high-mode tail tends uniformly to zero.
The projections prove compactness only; no projection replaces the
operator or the solution.

Estimate (28.13) and this compactness give finite kernel dimension
and closed range. In detail, on the orthogonal complement of the
kernel, failure of a lower bound would give normalized vectors
whose images tend to zero. Compact restriction followed by (28.13)
gives an $X$-convergent subsequence with a nonzero limit in the
kernel and its orthogonal complement, a contradiction.
The same reasoning for the adjoint gives a finite-dimensional
cokernel. Thus every $b_\theta$ is Fredholm. Its operator-norm
continuity in $\theta$ follows directly from the bounded mass
cross form, so the index is constant along $[0,1]$.
This uses the index-continuity theorem for bounded Fredholm maps
in Kato, Chapter IV, Section 5, in the displayed completed spaces.

The following regularity argument justifies exclusion of a kernel
for this comparison problem. Write $T_hY(x)=Y(x+h)$.
Translations are uniformly bounded on $X$ for bounded $h$; the
mass weight changes by a factor bounded by $e^{2|h|}$.
If $b_\theta Y=F$ and translation difference quotients of $F$
are bounded in $X^*$, the exact translated equation gives

$$
\left\|b_\theta\frac{T_hY-Y}{h}\right\|_{X^*}
 \le C\|Y\|_X+C_F\qquad(0<|h|\text{ sufficiently small}).
\tag{28.14}
$$

Indeed coefficient differences of $\varphi_x$ and its derivatives
are bounded by $C|h|$, and
$|e^{2h}-1|/|h|$ stays bounded. Every resulting term is controlled
by the norm (28.2). The compact term in (28.13) for these
difference quotients is at most
$\|Y_x\|_{L^2(I+[-1,1];C)}$, already controlled by $X$.
Thus the difference quotients are bounded in $X$; weak compactness
and their distributional limit imply $Y_x\in X$.
No derivative in the natural angular norm was presumed.

For a kernel vector set $u=\rho^{-1}Y$.
The bounded multipliers $\rho^{-1}$ and their derivatives give
$u,u_x\in X$. In particular
$u\in H^1(\mathbb R;\mathcal H_c)$,
$u_x\in H^1(\mathbb R;L^2(J,c\,da))$, and
$e^xu,e^xu_x\in L^2(dx\,da)$.
The weak equation $p_\theta(u,z)=0$ extends by density to the
test $z=u_x$. The real derivative and $h$ terms integrate to
zero: their energy densities are $W^{1,1}$ functions with zero
end limits. For the mass term, the displayed integrability
justifies integration by parts and gives

$$
\operatorname{Re}\int e^{2x}M_\theta(u,u_x)\,dx
              =-\int e^{2x}M_\theta[u]\,dx.
\tag{28.15}
$$

Therefore $p_\theta(u,u_x)=0$ forces the rightmost integral to
vanish. Positivity (28.7) gives $u=0$, hence
$\ker b_\theta=0$. This conclusion concerns only the limiting
comparison wall; it excludes no original decaying mode or resonance.

To calculate the index, take $\theta=0$.
The entire complementary block is coercive, including its full
$e^{2x}\|v\|_2^2$ mass, and is invertible. The scalar block is
the conjugation of

$$
-a_{xx}-s^2a+me^{2x}a=0.
\tag{28.16}
$$

Choose a remote right half-line on which $me^{2x}-s^2\ge1$.
Minimizing
$\int(|a_x|^2+(me^{2x}-s^2)|a|^2)\,dx$ there with boundary
value one gives a nonzero finite-energy solution, unique for that
boundary value by strict coercivity. The ordinary nonsingular ODE
extends it through every finite $x$. The right finite-energy
solution space is one-dimensional: the Wronskian of any two
solutions is constant and tends to zero along a sequence at
infinity, because their values and derivatives are square integrable.
A zero Wronskian gives linear dependence.

On the left, rotate the first-order vector $(a,a_x/s)$ by the free
sine/cosine fundamental matrix. The resulting coefficient matrix is
$O(e^{2x})$, integrable at negative infinity. Gronwall's inequality
and integration give a finite limiting vector. The transformed
fundamental matrix has constant nonzero determinant, since its
system has trace zero, so its limit is invertible. Thus every
nonzero scalar solution has a nonzero limiting sine/cosine pair,
and bounded value and derivative on the left.
A scalar kernel vector of $b_0$ would have $\rho a\in X$,
which is impossible for a nonzero oscillatory left pair.
For the adjoint the opposite conjugation gives $\rho^{-1}a$,
which is $e^{\delta x}$ times a bounded oscillatory function on
the left and belongs to $X$. On the right $\rho=1$, so the
right one-dimensionality supplies exactly one adjoint kernel vector.
The scalar index is $-1$. Consequently

$$
\operatorname{ind}b_0=\operatorname{ind}b_1=-1,\qquad
\ker b_1=0,\qquad\dim\operatorname{coker}b_1=1.
\tag{28.17}
$$

It remains to construct a standing profile of the full equation.
Take a real smooth $\chi$ equal to one on $x\le-2$ and zero
on $x\ge-1$, and let $p_0(x)=\cos(sx)$, $p_1(x)=\sin(sx)$,
$u_j=\chi p_j\psi$. Their weighted residuals $G_j=\rho L_*u_j$
are antidual functionals on $X$. Explicitly,

$$
G_j(Z)=\int\rho\left\{
 -(\chi_{xx}p_j+2\chi_x(p_j)_x)C(\psi,Z)
           +e^{2x}\chi p_j\langle\psi,Z\rangle\right\}\,dx.
\tag{28.18}
$$

Here $L_*$ denotes the distributional operator of $p_*$.
The homogeneous channel terms cancel by (27.1).
The first term has compact support; the second decays like
$e^{(2-\delta)x}$ at negative infinity. Since $\delta<2$ and
$A$ controls unweighted $L^2$, both $G_j$ and their translation
derivatives are bounded in $X^*$.

Conjugation invariance makes the one-dimensional cokernel a
one-dimensional real space on real data. Choose a nonzero real
adjoint generator. There is a real pair $(c_0,c_1)\ne(0,0)$ whose
combination $c_0G_0+c_1G_1$ annihilates that generator.
The closed-range characterization and (28.17) give a unique $Y\in X$
with

$$
b_1Y=-(c_0G_0+c_1G_1).
\tag{28.19}
$$

Reality and injectivity give real $Y$. The difference-quotient
argument (28.14) applies to this forcing, so $Y_x\in X$.
Thus $u=c_0u_0+c_1u_1+\rho^{-1}Y$ solves the full wall equation.
Put $R_c=\sqrt{c_0^2+c_1^2}$ and

$$
W=\frac{2u}{R_c},\qquad
\beta=\frac{c_0-ic_1}{R_c},\qquad |\beta|=1.
\tag{28.20}
$$

For $x\le-2$ the remainder after the leading term in (28.4)
is $2e^{\delta x}Y/R_c$.
From $Y,Y_x\in X$ one has
$Y\in H^1(\mathbb R;\mathcal H_c)$ and
$Y_x\in H^1(\mathbb R;L^2(J,c\,da))$.
Hilbert-valued $H^1$ functions have bounded continuous
representatives: integrate the derivative of their squared norm
and use Cauchy--Schwarz, as in (25.21).
Apply this separately to $Y$ in $\mathcal H_c$ and to
$Y_x+\delta Y$ in the $C$ space. It gives both errors in (28.4),
including the derivative error, with continuous representatives.
The nonzero leading oscillatory pair also proves $W\ne0$.

On $x\ge-1$ the cutoff waves vanish, and $\rho^{-1}$ and its
derivatives are bounded; on $x\ge2$ one has $\rho=1$ exactly.
Thus $W,W_x$ have the indicated $X$ energies on every finite
right tail, proving (28.5). The wall coefficients $c,q_n$ are even,
so taking the even part of any compact natural angular test preserves
its pairing with $W$; the equation holds for all such tests.
All complement estimates, the Fredholm
argument, correction and traces have retained $V_{\rm ev}$ in full.
The homotopy ends at $\theta=1$, so the resulting equation has the
unweighted mass in (27.4). $\square$

## 29. Shifted normalized original-form profiles with a retained residual

**Definition 29.1 (one exterior and the approximate family).**
Under Definition 27.1, take $W,\beta,\delta$ from Theorem 28.2.
Choose one sufficiently remote
$\ell_0>\max(0,\ell_n)$ on which (27.3) holds, and put
$R_0=e^{\ell_0}$. For $0<E<1$, in exactly the coordinates (26.3),
define on $\Omega_{R_0}$

$$
\begin{aligned}
w_E^{\rm app}(\ell,a)&=W(\ell-T_E,a),\qquad
T_E=\tfrac12\log(1/E),\\
\Phi_E(\delta_{e^\ell}\omega(a,\theta))
 &=\frac{e^{-\ell}}{\sqrt{2\pi}}W(\ell-T_E,a).
\end{aligned}
\tag{29.1}
$$

The angular mass, source, clock, fields and free closure are those
of Definition 27.1. The superscript denotes an approximate original
solution; the original equation retains the residual below.

**Theorem 29.2 (physical free tails, ordered strong overlap and residual bounds).**
There is $E_0\in(0,1)$ such that, for every $0<E<E_0$, $\Phi_E$
is nonzero, real, axisymmetric and even in $z$.
Every compact smooth exterior multiplier gives
$\chi\Phi_E\in\mathcal H_1$, and every tail cutoff with the exact
quantifiers in Theorem 27.2 gives $\eta\Phi_E\in\mathcal H_1$.
The slices of $w_E^{\rm app}$ in $\mathcal H_c$ and of its
distributional longitudinal derivative in $L^2(J,c\,da)$ have
continuous representatives. With the same unit $\beta$ for all $E$,
put

$$
\begin{aligned}
r_E^{\rm app}(\ell)
 &=\|w_E^{\rm app}(\ell)
       -2\operatorname{Re}(\beta e^{is(\ell-T_E)})\psi\|_{\mathcal H_c}\\
 &\quad+
 \|\partial_\ell w_E^{\rm app}(\ell)
       -2\operatorname{Re}(is\beta e^{is(\ell-T_E)})\psi\|_C.
\end{aligned}
\tag{29.2}
$$

For $K\ge\max(2,\ell_0)$ and $T_E>2K$,

$$
\sup_{K\le\ell\le T_E-K}r_E^{\rm app}(\ell)\le Ce^{-\delta K}.
\tag{29.3}
$$

In particular the exact ordered limit is

$$
\lim_{K\to\infty}\limsup_{E\downarrow0}
       \sup_{K\le\ell\le T_E-K}r_E^{\rm app}(\ell)=0.
\tag{29.4}
$$

Here $K>\ell_0$ and the inner limit uses sufficiently small $E$
with $T_E>2K$. Equivalently, for every $\varepsilon>0$ there is
$K_0>\ell_0$ such that for every $K\ge K_0$ there is
$E_K\in(0,\min(E_0,e^{-4K}))$ for which every $0<E<E_K$ and
every $\ell\in[K,T_E-K]$ have $r_E^{\rm app}(\ell)<\varepsilon$.
The radius $R_0$, energy bound $E_0$ and $\beta$ are independent
of $E$.

For compact natural even tests $z$ supported in $\ell>K$, use
$D$ from (27.2) and define

$$
\mathcal N_{E,K}(z)^2=\int_K^\infty
 \{C[z_\ell]+A[z]+e^{-2\ell}\|Dz\|_2^2
                         +Ee^{2\ell}\|z\|_2^2\}\,d\ell.
\tag{29.5}
$$

The tests include finite tensors in the entire even natural domain
and their compactly supported limits in this norm.
With $f_z=e^{-\ell}z/\sqrt{2\pi}$, the exact original residual is

$$
\begin{aligned}
\mathcal R_E(z)
 &:=4\{q_{\rm orig}(\Phi_E,f_z)
                     +E\langle\Phi_E,f_z\rangle_{L^2(d\xi)}\}\\
 &=\int_K^\infty\left\{
 e^{-2\ell}\langle Dw_E^{\rm app},Dz\rangle
               -g\langle B_n(\ell)w_E^{\rm app},z\rangle\right\}\,d\ell.
\end{aligned}
\tag{29.6}
$$

There are constants $C_1,C_2<\infty$, independent of $E,K$ for
$T_E\ge K\ge\max(2,\ell_0)$, such that

$$
\begin{aligned}
\int_K^\infty e^{-2\ell}
 \bigl(\|Dw_E^{\rm app}\|_2^2+\|w_E^{\rm app}\|_2^2\bigr)\,d\ell
 &\le C_1e^{-2K},\\
|\mathcal R_E(z)|
 &\le C_2(e^{-K}+e^{-2K})\mathcal N_{E,K}(z).
\end{aligned}
\tag{29.7}
$$

They may depend on the fixed $n,g,\delta$, normalized $W$,
$C_B$ and $\lambda_0$. Identity (29.6), with integration over
the support of the test, also describes every original compact
complex test after the form-preserving averages of Proposition 24.4.
Neither exact vanishing nor nonvanishing of the residual for every
$E$ is asserted.

Proof. Choose $A_0\ge2$ so that the left $C$ error in (28.4)
is less than one for $x\le-A_0$. Choose a common $E_0\in(0,1)$
so small that
$T_E>\ell_0+A_0+2\pi/s$ whenever $0<E<E_0$.
There is then a full oscillatory period above $\ell_0-T_E$ and
below $-A_0$. At a point of that period the leading channel has
$C$ norm two, since $C[\psi]=1$ and $|\beta|=1$.
The error is less than one, so the restricted profile cannot vanish.
This proves nonzero $\Phi_E$ for every such $E$.
Reality and the symmetries follow directly from $W$.

If $K\ge\max(2,\ell_0)$, $T_E>2K$ and
$K\le\ell\le T_E-K$, then $x=\ell-T_E\le-K$.
Apply (28.4) at each such $x$ to obtain (29.3), with constants
independent of $E,K$. It gives (29.4) and its stated eventual-all-$E$
quantifiers. Continuity of both slices follows from Theorem 28.2.
No subsequence or energy-dependent phase is used.

We next verify the actual original free closure, including its
central derivative. The identity $c^2\le c$ and the definition of
$D$ give

$$
\|DW\|_2^2\le C\bigl(\|W_x\|_2^2+A[W]\bigr),
\tag{29.8}
$$

where $\partial_\ell W(\ell-T_E)=W_x(\ell-T_E)$.
For fixed $E$ and every finite $L>\ell_0$, (28.5) therefore yields

$$
\int_L^\infty\bigl\{
 C[(w_E^{\rm app})_\ell]+A[w_E^{\rm app}]
 +e^{-2\ell}\|Dw_E^{\rm app}\|_2^2
 +e^{2\ell}\|w_E^{\rm app}\|_2^2\bigr\}\,d\ell<\infty.
\tag{29.9}
$$

For the mass use $e^{2\ell}=E^{-1}e^{2x}$; the finite factor
$E^{-1}$ is permitted for this fixed-$E$ membership assertion.
For the central term the unweighted derivative on the right is
controlled by $W_x\in L^2(\mathcal H_c)$ in (28.5).
All terms are finite on the remaining bounded longitudinal
segments because $W$ is locally $H^1$ with values in $\mathcal H_c$.

Approximate first in longitudinal $H^1(\mathcal H_c)$ on a fixed
compact interval by finite natural tensors, and then approximate
their angular coefficients by original (13.6)--(13.8)'s compact
angular core. Bound (29.8) gives convergence of the central term
as well as of the homogeneous and physical mass terms.
Undoing the actual coordinates gives compact smooth Cartesian
approximants away from the axes and pole, exactly the free-norm
correspondence in (24.14) and (25.22).
Longitudinal truncations at infinity converge by the positive
integrals (29.9); their derivative errors tend to zero by the same
integrable norms. Multiplication by a stated radial tail cutoff,
which vanishes near the omitted boundary, thus gives an element
of the original $\mathcal H_1$.
For any compact exterior multiplier, choose a compact radial
multiplier equal to one on its support and use the original
$U,V,Z$ product rules. The same product rules handle every
permitted tail cutoff, whose transition derivatives have compact
annular support. This proves all asserted free multipliers and
physical free tails without adding angular endpoint data.

By the exact wall equation, translating $x=\ell-T_E$ cancels
$C(w_\ell,z_\ell)+h(w,z)+Ee^{2\ell}\langle w,z\rangle$ in
(27.2). The terms left over are precisely (29.6).
To prove its uniform bound, first establish the first line of
(29.7). On $x\le-2$, write the normalized profile as its bounded
standing part plus $e^{\delta x}\widetilde Y$, where
$\widetilde Y,\widetilde Y_x\in L^2(\mathbb R;\mathcal H_c)$ by
(28.19)--(28.20). The standing part and its unweighted derivative
are uniformly bounded, so their $e^{-2\ell}$ integral is
$O(e^{-2K})$.
For the correction, use (29.8) and, when $T_E\ge K$,

$$
\begin{aligned}
&e^{-2T_E}\int_{K-T_E}^{0}
 e^{(2\delta-2)x}
 \bigl(\|\widetilde Y\|_{\mathcal H_c}^2
             +\|\widetilde Y_x\|_{\mathcal H_c}^2\bigr)\,dx\\
&\quad\le C e^{-2T_E}e^{(2\delta-2)(K-T_E)}
 =C e^{-2\delta T_E}e^{-2(1-\delta)K}
 \le C e^{-2K}.
\end{aligned}
\tag{29.10}
$$

Here $\delta<1$. Restricting this calculation to $x\le-2$
only decreases the positive integral. The fixed transition
interval $[-2,0]$ contributes $O(e^{-2T_E})$, and on $x>0$
(28.5) and (29.8) give the same bound. Since $T_E\ge K$,
these contributions are $O(e^{-2K})$.
This proves the first line of (29.7) for all higher components
as well as the channel.

Cauchy--Schwarz now bounds the central term of (29.6) by
$C e^{-K}\mathcal N_{E,K}(z)$.
For the source term, (27.3) and $A[z]\ge\lambda_0\|z\|_2^2$
give

$$
\begin{aligned}
\left|g\int_K^\infty\langle B_nw_E^{\rm app},z\rangle\,d\ell\right|
 &\le gC_B\left(\int_K^\infty e^{-2\ell}
                         \|w_E^{\rm app}\|_2^2\,d\ell\right)^{1/2}
             \left(\int_K^\infty e^{-2\ell}\|z\|_2^2\,d\ell\right)^{1/2}\\
 &\le C e^{-2K}\mathcal N_{E,K}(z).
\end{aligned}
\tag{29.11}
$$

Together these prove the second line of (29.7).
For an arbitrary original compact complex exterior test, rotate
and then reflect its axisymmetric image. Proposition 24.4 preserves
its pairing with $\Phi_E$, as well as its compact exterior support.
The cylinder image of the averaged test belongs to the natural
local completion by (25.22) and its angular-core argument.
Thus (29.6) applies to that image. This retains all original tests,
including nonaxisymmetric ones, rather than restricting the
original weak equation's test space. $\square$

**Definition 29.3 (the joint exact-family boundary).**
Theorem 27.2 supplies exact original positive-energy exterior
solutions with every physical free tail, without a channel-phase
prescription. Theorem 28.2 supplies the coupled comparison wall and
both strong left traces. Theorem 29.2 supplies a separately defined
normalized approximate original family with all the ordered overlap
and physical-free-tail properties and with residual (29.6).
These are distinct families and equations. Their separate existential
statements do not assert a single exact family having all properties.

The unresolved joint assertion retains every original quantifier:
for each $n\ge2$, a finite immediate interval
$\lambda_n<g_n^{\rm wall}\le g_n^{\rm iso}$, every fixed
$g\in(\lambda_n,g_n^{\rm wall})$, and one finite $R_0>1$,
$E_0\in(0,1)$ and unit $\beta$, all independent of $E$.
On that fixed exterior it requires a nonzero real
axisymmetric $z$-even exact original family at every $0<E<E_0$
with every original compact test, every compact free multiplier,
every physical tail in (27.6), both continuous slice representatives
and the ordered overlap limit (29.4) for that same exact family.
No such joint threshold or exact family is established by
Theorems 27.2--29.2.

For the shifted construction, the remaining mathematical obligation
is to solve the full original exterior inhomogeneous equation for a
correction to $\Phi_E$, preserving the physical free tail and making
the correction tend to zero in both strong slice norms on
$[K,T_E-K]$ in the ordered $\lim_K\limsup_E\sup$ limit, for
every sufficiently small $E$. The shifted left endpoint tends to
negative infinity. An inverse or compatible alternative construction
with this uniform control has not been obtained here; every allowed
original kernel or resonance must be handled without exclusion.
An alternative exact construction with the identical joint
quantifiers would also suffice.

The remote-exterior antidual estimate (29.7) supplies neither exact
cancellation nor such a correction estimate. It also supplies no
claim that the residual is nonzero for every $E$, and no graph-residual
$o(E)$ statement. The kernel exclusion in (28.15) applies only to
the comparison wall. No genericity, resonance exclusion, stronger
tail, finite angular substitution, endpoint value, source change or
clock change is added to Definition 18.1. The zero-energy original
core datum of Theorem 26.2 remains separate and unchanged.
Global operator-domain extensions, quasimodes, multiplicity exhaustion
and an eigenvalue-phase limit are not conclusions of these partial
results; Application 24.6 remains a conditional implication.

## 追加锚（本行以下为增补区）

## 30. Uniform opposite-weight correction of the original wall family

**Definition 30.1 (unchanged premises and the auxiliary graph forms).**
Assume exactly original Definition 18.1 at
[d6d829c43b0ed4f127a09666bc40088b6f440b94](https://github.com/the-omega-institute/trureturing/blob/d6d829c43b0ed4f127a09666bc40088b6f440b94/docs/develop/theory/FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
with C and V at 5cec4fa83ae7bbb4e787c42606525db4cd11ed48 as fixed
in its Definition 1.1. Thus the analytic premises are the original-field
formulas and locally uniform off-pole convergence of its Theorem 10.2,
its full complex polar identity (12.12)--(12.13), V's closed natural
angular form and compact embedding, natural-core approximation
(13.6)--(13.8), complete-field scaling (14.9), and original closed form,
compact smooth core and local estimates (15.9)--(15.12).
Retain the identity unit source, raw measures, covariance-$2$ clock,
complete time integral and whole unweighted omitted fibre in (26.1),
with $\epsilon=1$, and precisely the original $U,V,Z$, $M_{n,1}$,
$\mathcal H_1$, $q_{\rm orig}$ and Friedrichs realization in (26.2).
The full integer angular domains are still $D_m$ in original (18.1).
All conclusions of this section are ordinary conditional analysis
under these premises.

Fix any $n\ge2$ and $g\in(\lambda_n,g_n^{\rm iso})$.
Use $J,c,A,C,h,\lambda_0,\kappa,V_{\rm ev},s,\psi$ of (27.1),
with $C[\psi]=1$, and $W,\beta,\delta_W$ of Theorem 28.2.
In particular $\|b\|_{\mathcal H_c}^2=A[b]+\|b\|_2^2$;
unsubscripted angular pairings use unweighted $da$.
Choose $0<\delta\le\delta_W$ with $\delta<1/2$ and
$\delta^2<\kappa/4$. Choose the smooth weight of Definition 28.1
at this $\delta$, and write $\sigma=e^{-\varphi}$, $\lambda=\log\sigma$.
Thus $\sigma=e^{\delta x}$ on $x\le-2$, $\sigma=1$ on $x\ge2$,
$|\lambda'|\le\delta$, and its needed derivatives are bounded.
The injective comparison map in (28.3), (28.13)--(28.17) is exactly
$Y\mapsto p_*(\sigma Y,\sigma^{-1}\,\cdot)$ at this allowed weight.

Use the continuation (25.9): $\eta_L(\ell)=L+\chi(\ell-L)$,
where $\chi=0$ on $(-\infty,0]$, $\chi(x)=x$ on $[1,\infty)$,
$\chi\ge0$ and $|\chi'|\le H$. For sufficiently large fixed $L>0$, put

$$
\begin{aligned}
t(\ell)&=e^{-2\eta_L(\ell)},& \widetilde B(\ell)&=B_n(\eta_L(\ell)),
&S&=e^{-2L},\\
0<t&\le S,& |t'|&\le2Ht,&
\|\widetilde B\|_\infty+\|\widetilde B'\|_\infty&\le C_B't.
\end{aligned}
\tag{30.1}
$$

These are consequences of (27.3). Both coefficients agree with the
original ones for $\ell\ge L+1$; the continuation below that radius
is auxiliary. Set $t_T(x)=t(T+x)$, $B_T(x)=\widetilde B(T+x)$ and
$D=\nu(\partial_x-1)+4c\partial_a$, $\nu=2\sin a$.
Let $X_T$ be the completion of compact longitudinal finite natural
tensors in the entire even angular space for the norm

$$
\|Y\|_{X_T}^2=\int_{\mathbb R}
 \{C[Y_x]+A[Y]+t_T\|DY\|_2^2+e^{2x}\|Y\|_2^2\}\,dx.
\tag{30.2}
$$

Write $X_*$ for the same completion with the central term omitted;
its norm is equivalent to (28.2). On compact tensors define

$$
\begin{aligned}
p_T(u,z)&=p_*(u,z)+\int\{t_T\langle Du,Dz\rangle
                                  -g\langle B_Tu,z\rangle\}\,dx,\\
b_T^+(Y,Z)&=p_T(\sigma^{-1}Y,\sigma Z),&
b_T^-(Y,Z)&=p_T(\sigma Y,\sigma^{-1}Z).
\end{aligned}
\tag{30.3}
$$

The bounded polarized expansions define these maps on $X_T$:
for $b_T^+$ the derivative pair is
$(Y_x-\lambda'Y,Z_x+\lambda'Z)$ and the central pair is
$(DY-\lambda'\nu Y,DZ+\lambda'\nu Z)$; for $b_T^-$ both
signs reverse. The $h$, source and unweighted mass pairings are
unchanged. All constants below may depend on the fixed $n,g,L$.

**Proposition 30.2 (graph realization and the uniform compact remainder).**
For sufficiently large $L$, (30.2) has an injective distributional
realization, (30.3) is a uniformly bounded adjoint pair
$X_T\to X_T^*$, and for both signs there are one bounded interval
$I$ and $C_0$, independent of $T$, such that

$$
\|Y\|_{X_T}\le C_0\bigl(\|b_T^\pm Y\|_{X_T^*}
                              +\|Y\|_{L^2(I;C)}\bigr).
\tag{30.4}
$$

Restriction to $L^2(I;C)$ is compact on bounded sets of $X_*$.

Proof. Closed angular and longitudinal derivatives identify limits
in (30.2) distributionally. In particular $A$ controls unweighted
$Y$ and $cY_a$. On every compact $x$ interval $t_T>0$ for fixed $T$;
$\nu Y_x=DY-4cY_a+\nu Y$ then controls the unweighted longitudinal
derivative near the angular endpoints, while $C[Y_x]$ controls it
away from them. Thus a zero distribution has zero graph norm.
Multiplication by a smooth longitudinal cutoff is bounded.
For $Y=a\psi+v$, $a=C(Y,\psi)$, the $C$ projection is bounded:
$a,a_x$ are controlled by $C[Y],C[Y_x]$, and
$D(a\psi)=\nu\psi a_x+(4c\psi_a-\nu\psi)a$ has unweighted
$L^2$ norm bounded by $|a_x|+|a|$, by (24.10).
The central norm of this scalar part is $O(S)$ times its squared
$H^1$ norm. Together with (28.7) at $\theta=1$, this gives uniform
equivalence with scalar $H^1$ plus the full complementary graph
norm, retaining the split and unsplit unweighted wall mass.
Bounded $\lambda'$ gives uniform boundedness of the expansions.
Hermiticity of $p_T$ gives $b_T^-(Y,Z)=\overline{b_T^+(Z,Y)}$.

To prove (30.4), first omit the wall mass on the whole line and
replace $\lambda'$ by either constant $\pm\delta$. Use the full space
$H_T$ with squared norm $\int(C[Y_x]+A[Y]+t_T\|DY\|_2^2)$.
The scalar unperturbed multiplier is
$\xi^2\pm2i\delta\xi-\delta^2-s^2$. Its modulus divided by
$1+\xi^2$ has positive infimum: a real zero would have $\xi=0$,
where the real part is $-\delta^2-s^2$, and the quotient tends to
one at infinity. Plancherel gives an $H^1\to H^{-1}$ isomorphism.
The complementary block, including its entire central term, has
real diagonal at least

$$
\int\left\{C[v_x]+
 \left(\kappa-\delta^2-
       \frac{(4\delta^2+gC_B')S}{\lambda_0}\right)A[v]
                  +t_T\|Dv\|_2^2\right\}\,dx.
\tag{30.5}
$$

For small $S$ this dominates the same expression with coefficient
$\kappa/2$ before $A[v]$. The coercive Hilbert-space argument,
with the identical adjoint estimate, gives a uniform inverse on
the full complementary graph space. The scalar central/source
self block has norm $O(S)$, and both scalar/complement cross
blocks have norm $O(\sqrt S)$, using the displayed formula for
$D(a\psi)$ and Cauchy--Schwarz in the central norm. A Neumann
series therefore gives a uniform inverse of the whole no-mass left
model on $H_T$. The unbounded central form has remained in the
complementary diagonal throughout this argument.

For the global forms the real diagonal is exactly

$$
\operatorname{Re}b_T^\pm(Y,Y)=\int\{C[Y_x]+h[Y]+t_T\|DY\|_2^2
 +e^{2x}\|Y\|_2^2-(\lambda')^2(C[Y]+t_T\|\nu Y\|_2^2)
                          -g\langle B_TY,Y\rangle\}\,dx.
\tag{30.6}
$$

Coercivity on $V_{\rm ev}$ and small $S$ control all complementary
terms. The remaining negative scalar term is absorbed by the
positive unweighted mass on a fixed sufficiently remote right
half-line, using (28.7). Hence for fixed large $R$,

$$
\|Y\|_{X_T}^2\le C\left(\operatorname{Re}b_T^\pm(Y,Y)
                                      +\int_{x<R}|a|^2\,dx\right).
\tag{30.7}
$$

Take a cutoff $\zeta$ equal to one on $x<-R-1$ and zero on $x>-R$,
with $R>2$. Apply the left-model inverse to $\zeta Y$.
On its support the omitted mass has norm $O(e^{-2R})$ on $H_T$
and is absorbed. A cutoff $H_T$ test has uniformly bounded $X_T$
norm. In the $C$ commutator integrate the term containing $Y_x$
once onto the test; only $Y$ and the test's first derivative remain.
For the central commutator use $D^*=-D$ in $dx\,da$:
$(4c)_a=-2\nu$ gives this identity, and the endpoint term
$4cY\overline Z$ vanishes first on the natural core and then by
closure. Its derivative-on-test term and remainder have the form

$$
2\int t_T\zeta'\langle\nu Y,DZ\rangle\,dx
       +\int t_T\langle K_T^\pm(x,a)Y,Z\rangle\,dx,
\qquad \|K_T^\pm\|_\infty\le C,
\tag{30.8}
$$

supported on a fixed compact interval: the coefficients use
$t_T'/t_T$, $\zeta',\zeta''$, $\nu,\nu_a$ and $\lambda'$,
all bounded. Thus the entire commutator is bounded by
$C(\|Y\|_{L^2(I;C)}+\sqrt S\|Y\|_{L^2(I;da)})\|Z\|_{H_T}$,
without a derivative of $Y$. Crucially, interpolation (24.9) gives,
for any $\varepsilon>0$, a bound
$\varepsilon\|Y\|_{X_T}+C_\varepsilon\|Y\|_{L^2(I;C)}$
for its coefficient. The left inverse consequently bounds
$\|\zeta Y\|_{H_T}$ by this expression plus
$C\|b_T^\pm Y\|_{X_T^*}$. On the remaining bounded part of
$x<R$, $|a|^2\le C[Y]$. Insert this bound in (30.7), use Young's
inequality, and absorb the chosen $\varepsilon$ to obtain (30.4).
Both signs have the same real diagonal and conjugate scalar
multipliers, so the argument applies to each.

Finally the finite spectral projections of Proposition 24.3's
positively shifted weighted angular realization approximate the
$C$ norm uniformly on bounded $A$ sets. Their longitudinal
coefficients are bounded in $H^1(I)$ by $C[Y_x]$ and are compact
in $L^2(I)$. The uniformly small angular remainder proves the
claimed compact restriction. These projections serve only this
compactness argument; every complementary mode remains in the
forms. The intermediate Hilbert, Fourier and Neumann-series tools
are those used in Theorem 28.2 (Folland, Chapters 5 and 8); local
Rellich compactness is applied to the displayed finite coefficients.
$\square$

**Proposition 30.3 (the auxiliary adjoint lower bound and a real right inverse).**
There exist $T_0,c_0>0$ such that for every $T>T_0$,

$$
\|b_T^-Z\|_{X_T^*}\ge c_0\|Z\|_{X_T}.
\tag{30.9}
$$

Consequently $b_T^+$ has a real-preserving right inverse of norm
at most $c_0^{-1}$. Its kernel is allowed.

Proof. Failure of (30.9) gives $T_j\to\infty$ and
$\|Z_j\|_{X_{T_j}}=1$, $\|b_{T_j}^-Z_j\|\to0$.
By (30.4) their local $C$ norms are bounded below. They are bounded
in the fixed space $X_*$; pass to a weak subsequence there and,
by the compact restriction, a strong local $C$ subsequence.
Its limit $Z$ is nonzero. On each fixed compact interval,
$t_{T_j},B_{T_j}\to0$ uniformly. For any fixed compact natural
tensor test, the central pairing tends to zero: its factor
$\sqrt{t_{T_j}}DZ_j$ is bounded, while the weighted derivative
factor of the fixed test tends to zero. The conjugated central
lower-order terms satisfy the same estimate; the source term
vanishes by (30.1). The base terms pass weakly to the limit.
Thus $p_*(\sigma Z,\sigma^{-1}z)=0$ on the tensor core and,
by boundedness and density, on $X_*$. This is exactly the
injective map (28.3), (28.13)--(28.17), so $Z=0$, a contradiction.
This argument proves the bound for all sufficiently large $T$.

Identify the antidual with $X_T$ by its Riesz map, and call the
operator representing $b_T^-$ $\mathcal A_T$. Then
$\mathcal A_T^*\mathcal A_T\ge c_0^2I$, and

$$
\mathcal R_T=\mathcal A_T
       (\mathcal A_T^*\mathcal A_T)^{-1},\qquad
\mathcal A_T^*\mathcal R_T=I,\qquad
\|\mathcal R_T\|\le c_0^{-1}.
\tag{30.10}
$$

This is a right inverse for $b_T^+$ after the Riesz identification.
Real coefficients, the real core and the real Riesz structure make
it preserve real data. Only the auxiliary decaying-left map
$b_T^-$ is bounded below. No inverse of an original exterior or
Friedrichs operator is asserted; all its permitted kernels and
zero-energy resonances remain allowed. No inner boundary condition
is used in the artificial-left construction. $\square$

**Proposition 30.4 (the weighted full residual and differentiated control).**
The functional $F_T(Z)=-p_T(W,\sigma Z)$, initially on compact tests,
extends to $X_T^*$ and, for fixed small $h_0>0$, satisfies

$$
\|F_T\|_{X_T^*}+
 \sup_{0<|h|<h_0}\left\|\frac{\tau_hF_T-F_T}{h}\right\|_{X_T^*}
                  \le C_L e^{-\delta T}.
\tag{30.11}
$$

Here $\tau_hu(x)=u(x+h)$ and $(\tau_hF)(Z)=F(\tau_{-h}Z)$;
translated graph norms are uniformly equivalent for $|h|<h_0$.

Proof. First extract the needed regularity from the actual wall
construction (28.18)--(28.20). Write its weighted correction as
$Y_*$. Its explicit forcing $G$ has bounded translation derivatives
through order two in $X_*^*$, indeed through every fixed order:
the compact cutoff part is smooth, and its left mass part decays
like $e^{(2-\delta_W)x}$. The conjugated base form has bounded
first and second coefficient derivatives as $X_*\to X_*^*$;
this includes the exact derivatives of $e^{2x}$.
Theorem 28.2 gives $Y_*,Y_{*x}\in X_*$. Differentiating its
equation once gives forcing $G_x-b_*'Y_*$, whose first difference
quotients are bounded by $G_{xx}$, $b_*''Y_*$ and $b_*'Y_{*x}$.
Apply (28.13)--(28.14) to the quotients of $Y_{*x}$.
Their compact remainder is controlled by the local $C$ norm of
$Y_{*xx}$, already contained in $\|Y_{*x}\|_{X_*}$.
Weak compactness and distributional identification give
$Y_{*xx}\in X_*$. Thus on the left, $W,W_x$ are their bounded
standing parts plus $e^{\delta_Wx}$ remainders with values and
first derivatives in $L^2(\mathcal H_c)$. On every finite right
tail the corresponding quantities are in $L^2(\mathcal H_c)$.
In particular $DW,DW_x$ have the required unweighted integrability,
using (29.8). No angular derivative of the source was required.

The comparison equation cancels the base terms, giving precisely
the residual of (29.6) with the continuation coefficients:

$$
F_T(Z)=-\int\{t_T\langle DW,D(\sigma Z)\rangle
                              -g\langle B_TW,\sigma Z\rangle\}\,dx.
\tag{30.12}
$$

Since $D(\sigma Z)=\sigma(DZ+\lambda'\nu Z)$, Cauchy--Schwarz
reduces its norm, and its differentiated norm, to the square roots
of the following integrals, for $j=0,1$:

$$
\begin{aligned}
&\int\sigma^2t_T
 (\|D\partial_x^jW\|_2^2+\|\partial_x^jW\|_2^2)\,dx\\
&\quad\le C e^{-2\delta T}\int_{\mathbb R}q_L(\ell)
 (\|D\partial_x^jW(\ell-T)\|_2^2
                         +\|\partial_x^jW(\ell-T)\|_2^2)\,d\ell,
\qquad q_L(\ell)=t(\ell)e^{2\delta\ell}.
\end{aligned}
\tag{30.13}
$$

Here $\sigma(x)\le Ce^{\delta x}$. The function $q_L$ is bounded
and integrable: it is $Se^{2\delta\ell}$ far left and
$e^{-2(1-\delta)\ell}$ far right. The standing parts contribute
at most a constant times $\int q_L$; the extracted left remainders
contribute their $L^2$ norms times a bounded factor, and the
right-tail terms contribute their $L^2$ norms times $\|q_L\|_\infty$.
Thus the last integrals are uniformly bounded in $T$.
The source pairing has $t_T^2$ in place of $t_T$, and $t_T\le S$.
Differentiating (30.12) introduces only $W_x,DW_x$, bounded
weight derivatives, $t_T'$ and $B_T'$, controlled by (30.1) and
the same $j=1$ estimate. This proves the distributional derivative
bound. Finally $t_T(x+h)/t_T(x)\le e^{2H|h|}$ and the wall-mass
ratio is $e^{2h}$; translations are uniformly bounded in $X_T$.
Integrating the derivative estimate along these translations proves
(30.11), including its difference-quotient assertion. $\square$

**Proposition 30.5 (exact correction and both continuous strong traces).**
For every $T>T_0$ there is a real $Y_T$ such that, with
$r_T=\sigma^{-1}Y_T$,

$$
\begin{aligned}
b_T^+Y_T&=F_T,& p_T(W+r_T,z)&=0
                    \quad\hbox{for every compact even natural test }z,\\
\|Y_T\|_{X_T}+\|Y_{Tx}\|_{X_T}&\le C_L e^{-\delta T},\\
\|r_T(x)\|_{\mathcal H_c}+\|r_{Tx}(x)\|_C
 &\le C_L e^{-\delta(T+x)}\qquad(x\le-2).
\end{aligned}
\tag{30.14}
$$

Both correction traces have continuous representatives in the
displayed slice spaces.

Proof. Apply the real right inverse (30.10) to (30.11).
For a compact $z$ use $Z=\sigma^{-1}z$ in (30.3) and (30.12)
to obtain the exact equation. Translation of $b_T^+Y_T=F_T$ gives

$$
\left\|b_T^+\frac{\tau_hY_T-Y_T}{h}\right\|_{X_T^*}
 \le C\|Y_T\|_{X_T}+C_L e^{-\delta T}.
\tag{30.15}
$$

Indeed all coefficient errors are bounded on the actual graph
space by (30.1), bounded weight derivatives and the derivative of
$e^{2x}$. No central derivative is treated as a bounded base-space
perturbation. Apply (30.4) to these quotients. Their compact term
is at most $\|Y_{Tx}\|_{L^2(I+[-1,1];C)}$, already controlled
by $\|Y_T\|_{X_T}$. Hence the quotients are uniformly
$O(e^{-\delta T})$ in $X_T$. Their weak limits equal the
distributional $Y_{Tx}$, proving its graph bound without assuming
an inverse for $b_T^+$.

It follows that $Y_T\in H^1(\mathbb R;\mathcal H_c)$ and
$Y_{Tx}\in H^1(\mathbb R;L^2(J,c\,da))$, both with norm
$O(e^{-\delta T})$. The Hilbert-valued norm-square identity and
Cauchy--Schwarz, as in (25.21), give bounded continuous
representatives with this same bound. On $x\le-2$,
$r_T=e^{-\delta x}Y_T$ and
$r_{Tx}=e^{-\delta x}(Y_{Tx}-\delta Y_T)$, proving (30.14).
Smooth positive $\sigma$ gives local continuity on the remaining
line as well. Thus neither strong trace is inferred merely from
an averaged estimate. $\square$

**Theorem 30.6 (one exact original family with the physical wall phase).**
Under precisely Definition 30.1's original conditional premises,
the joint exterior assertion in Definition 29.3 holds with
$g_n^{\rm wall}=g_n^{\rm iso}$. More explicitly, for every integer
$n\ge2$ this is a finite real number greater than $\lambda_n$;
for every fixed real $g\in(\lambda_n,g_n^{\rm wall})$ there are
one finite $R_0>1$, $E_0\in(0,1)$, one complex $\beta$ with
$|\beta|=1$, and nonzero real axisymmetric $z$-even functions
$f_E$ on $\Omega_{R_0}$ for every $0<E<E_0$, with all the following
properties. The constants $R_0,E_0,\beta$ are independent of $E$.
For every such $E$, every $\chi\in C_c^\infty(\Omega_{R_0})$
satisfies $\chi f_E\in\mathcal H_1$, and

$$
q_{\rm orig}(f_E,\phi)+E\langle f_E,\phi\rangle_{L^2(d\xi)}=0
\quad\bigl(\phi\in C_c^\infty(\Omega_{R_0};\mathbb C)\bigr).
\tag{30.16}
$$

This includes all nonaxisymmetric original tests. For every finite
$R_0<r_1<r_2$ and every smooth real radial cutoff $\eta$ on
$\mathbb R^3$, $0\le\eta\le1$, equal to zero on $R_g\le r_1$
and one on $R_g\ge r_2$, one has $\eta f_E\in\mathcal H_1$,
including physical $L^2$ mass and all original $U,V,Z$ energies,
with zero extension across the omitted boundary.
No boundary value at $R_g=R_0$ is prescribed.

In the actual coordinates (26.3), namely
$R_g=((x^2+y^2)^2+16z^2)^{1/4}$,
$\delta_r(x,y,z)=(rx,ry,r^2z)$ and
$\omega(a,\theta)=(\sqrt{\cos a}\cos\theta,\sqrt{\cos a}\sin\theta,
\sin a/4)$, set
$w_E(\ell,a)=\sqrt{2\pi}e^\ell f_E(\delta_{e^\ell}\omega(a,\theta))$
and $T_E=\tfrac12\log(1/E)$. There are continuous slice
representatives of $w_E$ in $\mathcal H_c$ and its distributional
longitudinal derivative in $L^2(J,c\,da)$. With the same $\beta$
for every $E$, define

$$
\begin{aligned}
\mathfrak r_E(\ell)&=
 \|w_E(\ell)-2\operatorname{Re}(\beta e^{is(\ell-T_E)})\psi\|_{\mathcal H_c}\\
 &\quad+\|\partial_\ell w_E(\ell)
       -2\operatorname{Re}(is\beta e^{is(\ell-T_E)})\psi\|_C.
\end{aligned}
\tag{30.17}
$$

Then, with $K>\log R_0$ and the inner limit restricted to
sufficiently small $E$ with $T_E>2K$,

$$
\lim_{K\to\infty}\limsup_{E\downarrow0}
          \sup_{K\le\ell\le T_E-K}\mathfrak r_E(\ell)=0.
\tag{30.18}
$$

Equivalently, for every $\varepsilon>0$ there is $K_0>\log R_0$
such that for every $K\ge K_0$ there is
$E_K\in(0,\min(E_0,e^{-4K}))$ for which every $0<E<E_K$ and
every $\ell\in[K,T_E-K]$ satisfy $\mathfrak r_E(\ell)<\varepsilon$.
The full even natural angular space, every higher even component,
the complete source and the unweighted physical mass are retained.
There is no genericity, exceptional-energy or resonance restriction,
extra angular endpoint value or stronger original tail assumption.

Proof. Choose $L$ satisfying Propositions 30.2--30.3 and put
$R_0=e^{L+1}$. For $T_E>T_0$ define the same family throughout by

$$
w_E(\ell)=W(\ell-T_E)+r_{T_E}(\ell-T_E),\qquad
f_E(\delta_{e^\ell}\omega)=\frac{e^{-\ell}}{\sqrt{2\pi}}w_E(\ell),
\quad \ell>L+1.
\tag{30.19}
$$

On this exterior the continuation equals $t=e^{-2\ell}$,
$B=B_n(\ell)$, and $e^{2(\ell-T_E)}=Ee^{2\ell}$.
Thus (30.14) is exactly the full original equation (27.2), with
its central derivative, complete source and unweighted angular
mass. Reality and the reducing symmetry are preserved.

For each fixed $E$ and finite $b>L+1$, $\sigma^{-1}$ and its
derivatives are bounded on $x\ge b-T_E$ and eventually equal
one. The graph energies of $Y_{T_E}$ and (28.5), (29.8) give

$$
\int_b^\infty\{C[w_{E\ell}]+A[w_E]
       +e^{-2\ell}\|Dw_E\|_2^2+e^{2\ell}\|w_E\|_2^2\}\,d\ell<\infty.
\tag{30.20}
$$

For the last term use $e^{2\ell}=E^{-1}e^{2x}$: the finite
fixed-$E$ factor is sufficient for physical membership, and the
angular mass remains unweighted $da$. On compact intervals,
$W+r_T$ is $H^1$ with values in $\mathcal H_c$, by (28.5) and
(30.14). Approximate there by finite natural tensors and use
original (13.6)--(13.8)'s angular core. Inequality (29.8), also
applied to the approximating differences, controls the central
term. The original-domain correspondence (24.14), (25.22) then
gives compact smooth Cartesian free-norm approximants away from
the axes and pole. Longitudinal truncations converge by all four
positive integrals in (30.20). The original $U,V,Z$ product rules
therefore give every stated radial tail and every compact exterior
multiplier, with their full quantifiers.

The cylinder images of compact axisymmetric even Cartesian tests
belong to this local natural completion by the angular-core
argument following (25.22). Thus (30.14) gives (30.16) for them.
For an arbitrary complex compact exterior test, rotation averaging
and then reflection averaging within $m=0$ preserve its pairing
with $f_E$ and its support, by Proposition 24.4. This proves
(30.16) for the whole original test class. The all-mode polar
identities in V, (10.10)--(10.11), retain every original integer
mode and natural endpoint; the reducing averages do not replace
the full test class by a scalar operator.

For $K\ge\max(2,L+1)$, $T_E>\max(T_0,2K)$ and
$K\le\ell\le T_E-K$, (28.4) and (30.14) give

$$
\mathfrak r_E(\ell)\le Ce^{-\delta_WK}+C_Le^{-\delta\ell}
                         \le (C+C_L)e^{-\delta K}.
\tag{30.21}
$$

This proves exactly (30.18) and its eventual-all-small-$E$
formulation; the continuous representatives follow from the two
separate trace conclusions. To ensure nonzero for every small $E$,
choose one fixed large $K$ with the last bound less than $1/2$,
and shrink $E_0$ so every $0<E<E_0$ has
$T_E>\max(T_0,2K+2\pi/s+1)$. The overlap contains a full period
of the leading wave. At a point of leading amplitude two,
$C[\psi]=1$ and (30.21) give $\|w_E\|_C>3/2$.
Thus every member is nonzero, without passage to a subsequence.
The choices $L,R_0,\beta,E_0$ depend only on the fixed $n,g$.
They work for each pair throughout the entire open isolation
interval, so $g_n^{\rm wall}=g_n^{\rm iso}$ is admissible.

The source-specific correction (30.4)--(30.15) is a repository-derived
deduction from (24.9), (27.1)--(27.3) and the comparison construction
of Theorem 28.2. Its intermediate Riesz, adjoint, Fourier,
compactness and difference-quotient tools are classical, as in
Folland, *Real Analysis*, second edition, Chapters 5 and 8, and
Evans, *Partial Differential Equations*, second edition, Chapter 5.
Theorem 27.2's separate exact family is not identified with (30.19);
(29.6)'s approximate residual is cancelled by the new correction.
The functions in (30.19) are exterior functions: this theorem gives
no extension through the original core, global operator-domain
membership, graph-residual estimate, spectral exhaustion or
eigenvalue-phase limit, and no uniformity in $n,g$. $\square$

## 追加锚（本行以下为增补区）
