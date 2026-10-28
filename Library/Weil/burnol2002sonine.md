---
bibkey: burnol2002sonine
authors: Jean-François Burnol
year: 2002
title: Sur les « espaces de Sonine » associés par de Branges à la transformation de Fourier
doi: 10.1016/S1631-073X(02)02546-3
url: https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/S1631-073X(02)02546-3.pdf
claim: The physical even Sonin projection has an explicit truncated-Fourier resolvent formula, and its completed Mellin space has a genuine entire de Branges generator. The source does not estimate the projection after an Euler-factor change of metric. Its radial actual-source application exhibits the boundary-recovery obstruction on unrestricted reciprocal sources and restores the test-norm comparison under the selected source's fixed excess separation, with a supporting-multiplier-independent coefficient.
strata_touched: []
license: citation-only
triage: anchor
---

# Physical Sonin projection and its entire generator

The inspected primary source is the [published article](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/S1631-073X(02)02546-3.pdf), *C. R. Acad. Sci. Paris, Ser. I* 335 (2002), pp.689–692, DOI [10.1016/S1631-073X(02)02546-3](https://doi.org/10.1016/S1631-073X(02)02546-3). Its four-page PDF has SHA-256 `799586f60b1b591dabfd4eddf02d7270bbb186182551315954d99a462666f7a5`. The following are supplier results, reused without a new proof, numerical reproduction, or Lean declaration. Inspection of the statements and accompanying argument is not a complete proof audit.

## Carrier, Fourier normalization and projection

Sections 2–3 use even physical functions with norm

$$
\|\xi\|^2=\int_0^\infty|\xi(t)|^2\,dt,
\qquad
(\mathcal F_+\xi)(x)=2\int_0^\infty\cos(2\pi xy)\xi(y)\,dy.
$$

For each $\lambda>0$, let $Q_\lambda$ be the orthogonal cutoff to $(-\lambda,\lambda)$, $F_\lambda=Q_\lambda\mathcal F_+Q_\lambda$ and $D_\lambda=F_\lambda^2$, acting on the even cutoff space. The physical Sonin space $K_\lambda$ consists of functions whose values and Fourier transforms vanish on that interval. It is distinct from the compact support of a multiplicative test integrating dilations.

The discussion preceding Theorem 4, printed p.691, gives $\|F_\lambda\|<1$. Theorem 4 gives the **orthogonal** projection

$$
\begin{aligned}
\pi_\lambda\xi={}&\xi
-(I-D_\lambda)^{-1}
\bigl(Q_\lambda\xi-F_\lambda\mathcal F_+\xi\bigr)\\
&-\mathcal F_+(I-D_\lambda)^{-1}
\bigl(Q_\lambda\mathcal F_+\xi-F_\lambda\xi\bigr).
\end{aligned}
$$

The inverse acts on the cutoff space; its outputs are extended by zero when regarded as physical functions. The source also identifies $D_\lambda$ with the kernel $\sin(2\pi\lambda(x-y))/(\pi(x-y))$ restricted to even cutoff functions. Corollary 5 gives specialized formulas, including for inputs already vanishing on the physical interval. These formulas should be reused rather than reconstructed from finite Gram matrices.

At $\lambda=1$, the carrier, norm and Fourier convention agree with the physical even Sonin setup of the [archimedean trace source](connesconsani2021archimedean.md). This statement concerns the source conventions; no new compiled project application is claimed.

## The entire generator is additional source data

Theorem 8, printed p.692, constructs an **entire** function $E_\lambda$ satisfying the de Branges condition for $\operatorname{Re}w>1/2$. It identifies $B(E_\lambda)$ isometrically with the completed Mellin transforms of $K_\lambda$, using the critical-line measure $dt/(2\pi)$. Theorem 9 identifies $E_\lambda$ with $\sqrt\lambda$ times the jump of the completed Mellin evaluator at the physical cutoff. Section 1, equation (1), gives the reproducing kernel in terms of the genuine entire generator.

The $S$-dependent local-factor product in the [semilocal source](connesconsanimoscovici2024semilocal.md) specifies its weighted norm; it is not thereby this entire generator. Substitution into a de Branges kernel formula requires an actual generator and the corresponding isometry.

## Remaining arithmetic interface

The source supplies the unweighted physical projection and its kernel ingredients. It does not estimate their deformation under the finite Euler-factor metric supplied by $\theta_S$, or the correction to the orthogonal compressed dilation trace. A physical projection formula alone does not determine that correction's sign.

The integrating Weil test remains separate from the even physical vectors. An odd additive test can integrate this physical representation without becoming an odd physical vector. No estimate for the [full same-test arithmetic form](frankliebseiringer2006hardy.md), including all prime powers, follows here. The actual semilocal signed comparison remains unresolved.

## The direct theta-to-Sonine identification changes domain or norm

This is a conditional paper application of the original theta model,
not a new Mellin, uncertainty, interpolation or de Branges theorem.
The [theta tail](../Analytic/romik2021orthogonal.md),
[common-source correction (G1)–(G5)](lagarias2004li.md#a-common-source-inverse-for-both-critical-edge-projections),
[zero duals (FH1)](lagarias2004li.md#use-actual-form-inputs-and-a-fixed-head)
and [minimal form comparison (WF2)](fukushima2011dirichlet.md#transformed-form-and-a-global-derivative-comparison)
are reused without recomputation. The additional application concerns
these exact theta inputs, including after their common critical correction.

### Fix the right Mellin convention before applying a source theorem

Burnol's *On Fourier and Zeta(s)*, [arXiv math/0112254v6](https://arxiv.org/abs/math/0112254v6),
manuscript p.32, uses

$$
(\mathcal Mf)(w)=\int_0^\infty f(t)t^{-w}dt,\qquad
\|f\|_{L^2(dt)}^2=\int_{\mathbb R}
 |(\mathcal Mf)(1/2+i\tau)|^2\frac{d\tau}{2\pi}.
$$

The 50-page source PDF has SHA-256
`1b7163ddc57f2212b621eac68d551a0987e83267bda5dcda15ca126fe1e3660c`.
Write $g_\infty(w)=\pi^{-w/2}\Gamma(w/2)$. For a completed
Mellin boundary value $F=g_\infty\mathcal Mf$, the same norm is

$$
\|F\|_\Gamma^2:=
\int_{\mathbb R}\frac{|F(1/2+i\tau)|^2}
 {2\pi|g_\infty(1/2+i\tau)|^2}d\tau.
\tag{BM1}
$$

This is Mellin Plancherel with its displayed multiplier; it is not
an assertion that the genuine entire generator $E_a$ above equals
$g_\infty$. The two integral representations of the norm agree on
the completed Sonine image, without requiring equal pointwise weights.
The physical spaces $L_a$ used in *Two complete and minimal systems
associated with the zeros of the Riemann zeta function*,
[DOI 10.5802/jtnb.434](https://doi.org/10.5802/jtnb.434), section 2
and Theorem 3.1, printed pp.70–72, require the input and its cosine
transform to be constant on $(0,a)$. Note 6, printed p.73, explicitly
switches to the bare Mellin transform. A completeness statement there
does not identify another weighted source space with $L_a$.

### The direct physical input has trivial intersection with every fixed Sonine space

Retain $H=L^2_{\rm even}(\nu)$, $d\nu=2\Phi\cosh(x/2)dx$,
$\omega=\Phi/(2\cosh(x/2))$ and
$\mathcal Au(z)=\int_{\mathbb R}\Phi(x)u(x)\cos(zx)dx$.
The literal change of variables $t=e^x$ defines

$$
\begin{aligned}
 f_u(t)&=t^{-1/2}\Phi(\log t)u(\log t),\\
 (\mathcal Mf_u)(1/2+i\tau)&=\mathcal Au(\tau),\\
 \|u\|_\nu^2&=\int_0^\infty
       \frac{|f_u(t)|^2}{\omega(\log t)}dt,\qquad
 f_u(1/t)=t f_u(t).
\end{aligned}
\tag{BM2}
$$

These identities hold almost everywhere for $u\in H$; the transform
identity is an ordinary integral by the owned theta decay and
Cauchy–Schwarz. Since $\omega$ is bounded,
$f_u\in L^2(dt)$. If $f_u\in L_a$, its constant value on $(0,a)$
must vanish: the owned two-sided theta tail gives

$$
 \omega(\log t)^{-1}\asymp t^4e^{\pi/t^2}
 \qquad(t\downarrow0).
$$

The reciprocal identity in (BM2) then makes $f_u$ vanish also for
$t>1/a$. It therefore has compact support away from zero (or is
already zero if these gaps overlap). Its cosine transform is entire,
and being constant on $(0,a)$ it is constant everywhere. The
Riemann–Lebesgue lemma makes that constant zero, and Fourier
uniqueness gives $f_u=0$. Consequently, for every fixed $a>0$,

$$
 \{f_u:u\in H\}\cap L_a=\{0\},
 \qquad \{f_u:u\in H\}\cap K_a=\{0\}.
\tag{BM3}
$$

This concerns the displayed direct input only. It does not exclude
Sonine projection or a different transform with a separately proved
norm and arithmetic correspondence. The correctly completed boundary
value $g_\infty(1/2+i\tau)\mathcal Au(\tau)$ does satisfy

$$
 \|g_\infty\mathcal Au\|_\Gamma^2
   =\int\omega(x)|u(x)|^2d\nu(x)
   \le\|\omega\|_\infty\|u\|_\nu^2.
$$

This inequality supplies no missing Sonine membership or entire
completion: the Gamma-completed continuation can be meromorphic.

### Relabelling the raw Fourier value as completed Mellin is unbounded even in the form norm

Keep the actual $B=C_-^*C_-$, $G=P_NB|_N$ and
$L_Br=r-G^{-1}P_NBr$ from (G1)–(G5). They are bounded on the
centered ambient space; $L_B$ maps the actual form domain into itself,
since $N\subset D(T)$ and $T|_N=I/2$. For $r\in\mathcal R$,
the existing common correction gives

$$
 e_\pm r=C_\pm L_Br,\qquad
 c\|r\|_\nu^2\le\|e_-r\|^2\le\tfrac12\|r\|_\nu^2.
$$

The lower inequality follows by minimizing
$\langle B(r-n),r-n\rangle$ over $n\in N$ and using
$r\perp N$; no commutation of $B$ and $P_N$ is assumed.
Define the raw-value label, now as a function of the Mellin variable,

$$
 \mathcal J r(w)=
 \mathcal A(L_Br)\bigl(-i(w-1/2)\bigr).
$$

The following exclusion refers to this exact $\mathcal J$ with the
norm (BM1), allowing that norm to be infinite. It does not replace
$\mathcal J$ by its Gamma multiple.

Classical critical-line infinitude supplies distinct real zeros
$\tau_j\to\infty$ without computing a zero table. Reuse
$r_j=e_{\tau_j}\in\mathcal F\cap\mathcal R$ and put
$u_j=L_Br_j$. Let $\mu_k=\int x^k\omega(x)dx$ for $k=0,2$.
The zero duality, the critical annihilation and Riemann–Lebesgue give

$$
 \begin{aligned}
 \|r_j\|_\nu^2&=\int\omega(x)\cos^2(\tau_jx)dx
       \longrightarrow\mu_0/2>0,\\
 \mathcal Au_j(\tau_j)&=\|r_j\|_\nu^2,\qquad
 |(\mathcal Au_j)'(\tau)|\le\sqrt{\mu_2}\|u_j\|_\nu.
 \end{aligned}
\tag{BM4}
$$

Boundedness of $L_B$ makes the derivative bound uniform in $j$.
Thus $|\mathcal Au_j|$ has a fixed positive lower bound on a fixed-width
interval about $\tau_j$, for all large $j$. Stirling's fixed-real-part
[Gamma asymptotic](https://dlmf.nist.gov/5.11.E9) is

$$
 |g_\infty(1/2+i\tau)|^{-2}
       \asymp |\tau|^{1/2}e^{\pi|\tau|/2}.
$$

The interval in (BM4) therefore gives
$\|\mathcal J r_j\|_\Gamma^2\gtrsim
\tau_j^{1/2}e^{\pi\tau_j/2}$. On these same actual form inputs,
$Ur_j=s\cos(\tau_jx)$, with the owned $s,s'\in L^2$.
Applying (WF2), rather than assuming a bound for the positive channel,
gives

$$
 \|r_j\|_{\mathcal F}^2
 =\|r_j\|_\nu^2+D(r_j)\le C(1+\tau_j^2).
$$

Also $D(u_j)=D(r_j)+\|G^{-1}P_NBr_j\|_\nu^2/2$, since
$r_j\perp N$ and $T|_N=I/2$. The correction's ambient norm is
uniformly bounded. The owned edge inequality
$\|C_+u\|^2\le D(u)$ thus bounds $\|e_+r_j\|^2$ by the same
polynomial rate, while $\|e_-r_j\|^2\le\mu_0/2$.
It follows that there is no finite $C$ satisfying either bound

$$
 \begin{aligned}
 \|\mathcal J r\|_\Gamma&\le C\|r\|_{\mathcal F},\\
 \|\mathcal J r\|_\Gamma&\le
       C\bigl(\|e_+r\|^2+\|e_-r\|^2\bigr)^{1/2}
 \end{aligned}
 \qquad(r\in\mathcal F\cap\mathcal R).
\tag{BM5}
$$

The exponential lower rate against the polynomial upper rate proves
both exclusions, including when an individual left side is infinite.
This is stronger than failure of ambient-norm control for the same
raw-value label. It is not an obstruction to an operator-domain norm,
a restricted spectral class, or a transform with other boundary values.

The correct Gamma multiple has the bounded norm above and the direct
Sonine-domain obstruction (BM3); dropping that multiple has the
form-norm obstruction (BM5). Neither conclusion decides the signed
comparison between the two actual projected channels. No negative
Weil value, endpoint half-bound, full Robin inequality or RH proof
follows, and no new Lean certification or literature priority is claimed.


## Nonzero actual sources with the matched Laplace reciprocity

The required existence supplier is already in this published article:
section 2, printed p.690, before Theorem 1, gives an unnumbered
construction of a nonzero Schwartz function whose value and Fourier
transform both vanish on an arbitrarily large interval about zero.
The text attributes the construction to a private communication from
Kahane. The source cited here is Burnol's published account, not a
separate claimed Kahane paper or an invented theorem number.
This `literature-attested` existence statement is reused directly;
no new projection or common-gap existence theorem is constructed.

The following `repo-derived` application changes dimension through
[Grafakos--Teschl, Theorem 1.1](../Fourier/grafakosteschl2013radial.md),
then pays the original actual-source $M+\mathcal P$ norm. It does not
identify the old cosine Sonine Hilbert norm with that source norm.
It is paper mathematics without Lean certification or a priority claim.

### Transport the published common gap to the required radial order

Choose $R>1$ and a nonzero Schwartz function $g$ on $\mathbb R$
such that $g$ and $\widehat g$ vanish on $(-R,R)$.
It can be taken real and even while retaining the gap: take a nonzero
real or imaginary part, then its even part if nonzero; otherwise
differentiate its nonzero odd part. Differentiation preserves both gaps.

Set $G(z)=g(|z|)$ on $\mathbb R^9$. It is a nonzero radial Schwartz
function. Apply the published dimension recurrence four times, from
dimension one to nine. Because derivatives of the one-dimensional
Fourier profile vanish throughout $0<r<R$, its nine-dimensional
Fourier transform also vanishes on the ball $|\xi|<R$.

If $G-\mathcal F_9G\ne0$, take $\Psi=G-\mathcal F_9G$.
Otherwise $G=\mathcal F_9G$; take

$$
\Psi=\left(|z|^2+\frac{\Delta}{4\pi^2}\right)G.
$$

The displayed operator anticommutes with Fourier transformation.
It preserves the radial Schwartz class and its spatial gap, and it
cannot annihilate this nonzero $G$: its radial equation would be
$g''+8g'/r+4\pi^2r^2g=0$ on $r>0$, whose uniqueness and the open
zero interval would force $g=0$. In either case this gives

$$
\Psi\ne0,\qquad \mathcal F_9\Psi=-\Psi,\qquad
\Psi(z)=\psi(|z|)=0\quad(|z|<R).                 \tag{SG1}
$$

### Return to the same physical source and pay its full domain

Put $w(x)=(x/\pi)^6-1$ and, for $x>\pi$, define

$$
v(x)=x^{7/2}\psi(\sqrt{x/\pi}),\qquad
F(x)=v(x)/w(x).                                  \tag{SG2}
$$

The numerator vanishes for $x<\pi R^2$, so the simple zero of
$w$ at $\pi$ creates no singularity. The resulting nonzero real
source is smooth, zero near $\pi$, and rapidly decreasing with all
derivatives at infinity. Hence its original sixth moment is finite.
The [exact weighted radial correspondence RF2--RF3](../Fourier/grafakosteschl2013radial.md#the-actual-weighted-source-in-nine-dimensions)
gives, on this very source,

$$
L_F(s):=\int_\pi^\infty w(x)F(x)e^{-sx}dx
=-s^{-9/2}L_F(1/s)\quad(\Re s>0).                 \tag{SG3}
$$

It remains to pay the ACTUAL Gamma domain, not just an auxiliary
Hankel norm. In the [owned W317 notation](suzuki2026screw.md), set

$$
q(t)=(\pi e^t)^{9/4}\sum_{n\ge1}n^4F(n^2\pi e^t),
\quad t\ge0,\qquad q_+=q\,\mathbf1_{t\ge0}.
$$

For any sufficiently large integer $N$, rapid decrease gives
$|F(x)|+|xF'(x)|\le C_Nx^{-N}$. Consequently

$$
|q(t)|+|q'(t)|\le C_N'(\pi e^t)^{9/4-N}
 \sum_{n\ge1}n^{4-2N}.                            \tag{SG4}
$$

Taking $N=4$ proves $q,q'\in L^1\cap L^2(0,\infty)$.
The value $q(0)$ need not be zero: the terms $F(n^2\pi)$ for $n\ge2$
can contribute despite the source gap. Retain this jump in the zero
extension. Integration by parts gives

$$
|\widehat {q_+}(\xi)|\le C\min\left\{\|q\|_1,
 \frac{|q(0)|+\|q'\|_1}{|\xi|}\right\}.
$$

Since the full Gamma multiplier is comparable to
$1+\log(2+|\xi|)$, this proves $\mathcal P(F)<\infty$.
Thus SG2 is a NONZERO source in the SAME actual $\mathcal V$
which satisfies SG3. Rapid polynomial decrease is compatible with
the absence of square-root-exponential moments established through RF4.

By [LR2--LR3](hernandezsantamaria2025optimal.md#the-selected-null-obeys-a-weighted-laplace-reciprocity),
this example is $D$-orthogonal to every evenized physical Gaussian
$f_a+f_{-a}$ and every fixed even parameter derivative at zero.
Their span is therefore not dense in the $D$ Hilbert norm, even
when its orthogonal complement is tested inside the actual $\mathcal V$.
Density of ALL finite Gaussian features in W326 cannot be restricted
to that radical subfamily. This does not give the example a negative
Weil energy, a global supporting-null equation, or any favorable full
arithmetic sign. The relevant matched-branch sign estimate, RH and
strict all-integer Robin remain unresolved.

## The selected source pays its radial boundary recovery cost

The [ordinary radial-domain application](../Fourier/grafakosteschl2013radial.md#the-matched-actual-null-enters-the-ordinary-hankel-domain)
puts a selected matched null in radial $L^2(\mathbb R^9)$.
For that selected source, the already established small-excess
positivity restores a bounded transport from the radial logarithmic
form to the actual arithmetic test, with a constant independent of
the supporting multiplier. Reciprocity by itself is insufficient:
the explicit obstruction below lies in the ORIGINAL $\mathcal V$
but has positive complete energy. Keeping both statements identifies
which source-selection condition pays the boundary division.

The construction uses the truncated-Fourier resolvent method already
supplied by this article, Section 3, Lemma 2, Theorem 4 and
Corollary 5, printed p.691. Those statements concern the even
one-dimensional carrier. The radial version needed here is justified
below; it is not attributed to the article as an exact nine-dimensional
statement. No new common-gap existence theorem, projection algorithm
or logarithmic uncertainty principle is claimed. This is a
`repo-derived` actual-source application, without Lean/kernel
certification or a literature-priority claim.

### Keep the actual recovery map and its boundary division

Use $\mathcal F_9$ with kernel $e^{-2\pi iz\cdot\xi}$ and write
$T_F(z)=\tau_F(|z|)$ as in RF3. Set, for $y\ge0$,

$$
\begin{aligned}
 f(y)&=(\pi e^{2y})^{9/4}F(\pi e^{2y}),\\
 A(y)&=e^{9y/2}\tau_F(e^y),\\
 (\Theta f)(y)&=\sum_{n\ge1}n^{-1/2}f(y+\log n),\\
 (V_cf)(y)&=\int_0^\infty e^{-cs}f(y+s)\,ds.
\end{aligned}
$$

W338's ACTUAL test, with every theta dilation retained, is exactly

$$
 A(y)=\pi^{-23/4}e^{5y}(1-e^{-12y})f(y),\qquad
 g_F(y)=(I-3V_{5/2})\Theta f(y)\quad(y\ge0),
 \qquad g_F(-y)=g_F(y).                              \tag{BT1}
$$

The first equality transports the radial density, not its quantity
interpretation; the second is W338 after $t=2y$. In particular this
map divides by a factor with a simple zero at $y=0$ before applying
the actual theta and Volterra operators. It is not a unitary Mellin
change of variables on $A$.

For an anti-Fourier vector with the unit-ball gap define its
nonnegative radial logarithmic form by

$$
 \mathcal C_9(T)=
 \int_{\mathbb R^9}\log|z|\,|T(z)|^2dz+
 \int_{\mathbb R^9}\log|\xi|\,|\mathcal F_9T(\xi)|^2d\xi
 =2\int_{|z|\ge1}\log|z|\,|T(z)|^2dz.              \tag{BT2}
$$

Finiteness is required. This is the ordinary log-position plus
log-frequency expectation on the radial carrier; no arithmetic
prime or pole term is part of its definition. There is NO universal
constant $C$ such that

$$
 \|g_F\|_2^2\le C[\|T_F\|_2^2+\mathcal C_9(T_F)]     \tag{BT3}
$$

for all reciprocal actual sources for which its right side is finite.
Here reciprocal means RF3, not the stronger matched global-null
condition HI1.

### Make a common-gap shell without losing the boundary trace

Let $P$ be multiplication by the indicator of the unit ball and
$C_0=P\mathcal F_9P$ on radial $L^2$ functions supported there.
This is compact and self-adjoint. Its norm is strictly below one:
an extremizer at norm one would have both its value and Fourier
transform supported in the ball, which Fourier analytic uniqueness
excludes. Compactness then gives $\|C_0\|<1$.
Thus the same truncated-transform resolvent used in the supplier
is available here, with fixed finite inverse norm.

For $0<\epsilon<1/4$ take two real smooth radial bumps obtained by scaling fixed profiles
to disjoint subshells of widths proportional to $\epsilon$ inside $1+\epsilon<r<1+2\epsilon$. Normalize their span in
$L^2(\mathbb R^9)$ so every unit vector $a_\epsilon$ in this
two-dimensional space obeys

$$
 \|a_\epsilon\|_2=1,\qquad
 \|a_\epsilon\|_1\le C\sqrt\epsilon,\qquad
 \|\nabla a_\epsilon\|_2\le C\epsilon^{-1}.
$$

For such a vector form, on the closed ball,

$$
 h_\epsilon=(I-C_0)^{-1}P\mathcal F_9a_\epsilon.
$$

Its $L^2$ norm is $O(\sqrt\epsilon)$. The equation
$h_\epsilon=P\mathcal F_9a_\epsilon+C_0h_\epsilon$
then gives $\|h_\epsilon\|_{C^j(\overline B)}
\le C_j\sqrt\epsilon$ for every fixed $j$.
The real boundary value $h_\epsilon(1)$ is one linear functional
on the two-dimensional shell space. Choose a unit vector in its
kernel, and extend $h_\epsilon$ by zero outside the ball.
Its zero trace makes that extension $H^1$, with norm
$O(\sqrt\epsilon)$. Set

$$
 T_\epsilon=(I-\mathcal F_9)(a_\epsilon+h_\epsilon).
                                                               \tag{BT4}
$$

Radial Fourier inversion and the resolvent equation give
$\mathcal F_9T_\epsilon=-T_\epsilon$ and $PT_\epsilon=0$
exactly. Write outside the ball
$T_\epsilon(r)=a_\epsilon(r)+q_\epsilon(r)$, where
$q_\epsilon=-\mathcal F_9(a_\epsilon+h_\epsilon)$.
The boundary choice gives

$$
 q_\epsilon(1)=0,\qquad
 \|q_\epsilon\|_{C^1([1,2])}\le C\sqrt\epsilon,
 \qquad |q_\epsilon(r)|+|q_\epsilon'(r)|
          \le C\sqrt\epsilon\,r^{-4}\quad(r\ge2).       \tag{BT5}
$$

The last bound is the published radial Bessel formula with
$\nu=7/2$. On $r\rho\ge1$ its kernel and fixed radial derivatives
are $O(\rho^{-4})$ after the compact input-radius factors are
integrated; the $r\rho<1$ portion of the ball is
$O(\sqrt\epsilon\,\rho^{-9})$. The shell has $L^1$ norm
$O(\sqrt\epsilon)$ and the ball correction has uniformly bounded
derivatives of that size. All constants in BT5 are independent of
the chosen unit combination and $\epsilon$.

### Pay the original source domain and retain the actual theta tail

Return by the exact RF3 density map:

$$
 F_\epsilon(\pi r^2)=
 \frac{(\pi r^2)^{7/2}}{r^{12}-1}T_\epsilon(r),
 \qquad r>1.                                         \tag{BT6}
$$

BT5 cancels the denominator's simple zero for the correction.
This gives a smooth source on the closed physical half-line;
its value at $\pi$ need not be zero. Away from the shell the
correction is $O(\sqrt\epsilon)$ on bounded intervals and
$O(\sqrt\epsilon\,r^{-9})$ for $r\ge2$.
The same estimates on the differentiated Bessel kernel give
$xF_\epsilon'(x)=O(\sqrt\epsilon\,x^{-4})$ in the tail.
Consequently $M_6(F_\epsilon)<\infty$.

For each fixed $\epsilon$ the actual theta profile $u(t)$ of W338
and its derivative are in $L^1\cap L^2(0,\infty)$: the tail bounds
above make their differentiated dilation series absolutely convergent.
The zero extension retains its possible jump at zero. Integration
by parts bounds its Fourier transform by
$C_\epsilon\min(1,|\xi|^{-1})$, which pays the full logarithmic
Gamma norm. Thus $F_\epsilon\in\mathcal V$, not merely an auxiliary
Hankel space, and RF3 gives its exact weighted Laplace reciprocity.

In BT1 split $f=f_a+f_q$ according to BT5. The shell part has
width $O(\epsilon)$ near $y=0$, with

$$
 \|f_a\|_2\asymp\epsilon^{-1},\qquad
 \|f_a\|_1\le C\epsilon^{-1/2},\qquad
 \Theta f_a=f_a.
$$

The last equality uses $e^y\ge1$ and $n\ge2$ outside the shell.
BT5 gives
$|f_q(y)|\le C\sqrt\epsilon\,e^{-9y/2}$ after enlarging $C$
on a fixed compact interval. Thus the COMPLETE remaining theta
sum is $O(\sqrt\epsilon)$ in $L^2(0,\infty)$; its coefficients
are bounded by the convergent sum $\sum n^{-5}$.
The forward Volterra image of $f_a$ is supported in an interval
of length $O(\epsilon)$ and has supremum
$O(\epsilon^{-1/2})$, so its $L^2$ norm is $O(1)$.
The Volterra operator is bounded on the correction's $L^2$ space.
BT1 therefore yields

$$
 \|g_{F_\epsilon}\|_2\ge c\epsilon^{-1}.             \tag{BT7}
$$

This does not assume invertibility of the half-line Volterra
combination; it retains that operator on the actual shell and tail.

### The radial logarithmic payment grows only logarithmically

Put $v_\epsilon=a_\epsilon+h_\epsilon$. Its support is in the
ball of radius two, $\|v_\epsilon\|_2\asymp1$, and
$\|\nabla v_\epsilon\|_2\le C\epsilon^{-1}$.
Fourier Plancherel and Jensen's inequality for the concave logarithm
give

$$
 \int\log(2+|\xi|)\,|\mathcal F_9v_\epsilon(\xi)|^2d\xi
 \le C[1+\log(\epsilon^{-1})].
$$

Together with BT4 and compact support of $v_\epsilon$, this implies

$$
 \|T_\epsilon\|_2^2\le C,\qquad
 0\le\mathcal C_9(T_\epsilon)
       \le C[1+\log(\epsilon^{-1})].                 \tag{BT8}
$$

BT7--BT8 refute BT3, including its restriction to reciprocal actual
sources. No estimates of the complete arithmetic energy were used
to manufacture that norm mismatch.

Finally these sources satisfy, with the ORIGINAL moments,

$$
 H(F_\epsilon)\asymp\epsilon^{-2},\qquad
 D(F_\epsilon)=M_6(F_\epsilon)-H(F_\epsilon)
                 \asymp\epsilon^{-1},\qquad
 \frac{D(F_\epsilon)}{H(F_\epsilon)}=O(\epsilon).       \tag{BT9}
$$

The shell pays the leading terms; the correction has $M_6=O(\epsilon)$.
The [existing small-excess positivity MR4](hernandezsantamaria2025optimal.md#2-transfer-the-existing-small-excess-positivity-into-the-completed-domain)
therefore gives $\mathfrak E(F_\epsilon)>0$ for small $\epsilon$.
They cannot be nonzero matched global nulls with $\lambda>0$.

An estimate of the BT3 type must therefore retain an additional
boundary recovery cost or restrict its source class by further
conditions. The selected branch's global null equation and excess
separation remain available for a restricted comparison. Failure of
BT3 does not rule out such a comparison or another signed argument;
it gives no negative Weil example or RH/Robin conclusion.


### Restore the comparison with the selected source's excess gap

The obstruction BT9 has $D/H\to0$. For a fixed $0<\delta\le1$,
restrict instead to actual sources with $D(F)\ge\delta H(F)$ and
ordinary radial $L^2$ density. Define the exact radial payment

$$
 R_0(F)=\int_\pi^\infty (x/\pi)^{-7/2}w(x)^2|F(x)|^2dx
       =\pi^{7/2}\Gamma(9/2)\|T_F\|_2^2.
$$

For $t=x/\pi\ge1$, $w=t^6-1$ and $0<\eta\le1$,

$$
 w\le\eta+2\eta^{-1}t^{-7/2}w^2.
$$

Indeed when $w\ge\eta$, the increasing function
$w/(1+w)^{7/12}$ is at least $\eta/2$; when $w<\eta$ the
first term suffices. Integrating and taking $\eta=\delta/2$ gives

$$
 H(F)\le8\delta^{-2}R_0(F),\qquad
 D(F)\le8\delta^{-1}R_0(F),\qquad
 M_6(F)\le16\delta^{-2}R_0(F).                       \tag{BT10}
$$

W338's existing actual-profile bound $\|g_F\|_2^2\le CM_6(F)$
retains all theta terms and the actual Volterra operator. Thus
BT10 already controls the actual test by the ordinary radial norm
on this restricted class. No new theta-bound theorem or inverse of
its half-line Volterra combination is needed.

For reciprocal sources the radial logarithmic form also pays that
ordinary norm by a fixed uncertainty cost. Choose $R>1$ such that
$|\{z\in\mathbb R^9:1\le|z|\le R\}|=1/4$, and let $Q$ be
cutoff to this annulus. The ordinary Fourier kernel has modulus one,
so the classical Hilbert--Schmidt estimate gives
$\|Q\mathcal F_9Q\|\le1/4$. For
$v=QT_F$ and $z=(I-Q)T_F$, the unit-ball gap places $z$ outside
radius $R$. Anti-reciprocity gives
$\|v\|_2\le\tfrac14\|v\|_2+\|z\|_2$.
Orthogonality of the cutoffs therefore gives

$$
 \|z\|_2^2\ge\frac9{25}\|T_F\|_2^2,\qquad
 \mathcal C_9(T_F)\ge\frac{18}{25}\log R\,\|T_F\|_2^2.
                                                               \tag{BT11}
$$

This only consumes the elementary finite-volume Fourier cutoff
bound on the actual anti-eigenvector; it is not a new uncertainty
principle. BT10--BT11 supply, for reciprocal actual sources with finite radial
logarithmic form,

$$
 \boxed{\quad
 \|g_F\|_2^2\le C\delta^{-2}\mathcal C_9(T_F)
 \quad\text{if }D(F)\ge\delta H(F).
 \quad}                                                       \tag{BT12}
$$

The existing bounds even give an explicit coefficient: W338 has
$\|g_F\|_2^2\le S(F)$, and W324 gives
$S(F)\le\pi^{7/2}\zeta(3)^2M_6(F)$. Hence $C$ in BT12 can be
chosen as

$$
 C=\frac{200\pi^7\Gamma(9/2)\zeta(3)^2}{9\log R},\qquad
 R=\left(1+\frac1{4|B_9|}\right)^{1/9}.
$$

No numerical optimization or smallness of this coefficient is claimed.

For the SAME selected matched global null, MR5 gives the fixed
separation $\delta_*:=\min(1,\epsilon_*)>0$, while HI2 gives a
moment strictly above $17/2$. That moment pays both ordinary radial
$L^2$ and its logarithmic position integral; reciprocity pays the
Fourier integral. Thus BT12 applies with $\delta=\delta_*$.
The comparison constant has no dependence on the positive supporting
multiplier $\lambda$; the size of $\mathcal C_9(T_F)$ itself is
not claimed uniform in $\lambda$.

This restores precisely a norm comparison that fails on the full
reciprocal class. It does not insert $\mathcal C_9$ as an additional
positive term in the actual Weil form. A signed comparison with
W362's positive energies and the complete prime discrepancy still
has to be proved on the SAME selected source. No exclusion of the
matched negative branch, RH or all-integer Robin inequality follows
from BT12 alone.
