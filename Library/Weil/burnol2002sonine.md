---
bibkey: burnol2002sonine
authors: Jean-François Burnol
year: 2002
title: Sur les « espaces de Sonine » associés par de Branges à la transformation de Fourier
doi: 10.1016/S1631-073X(02)02546-3
url: https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/S1631-073X(02)02546-3.pdf
claim: The physical even Sonin projection has an explicit truncated-Fourier resolvent formula, and its completed Mellin space has a genuine entire de Branges generator. The source does not estimate the projection after an Euler-factor change of metric.
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
