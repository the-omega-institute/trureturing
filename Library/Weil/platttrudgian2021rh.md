---
bibkey: platttrudgian2021rh
authors: Dave Platt and Tim Trudgian
year: 2021
title: The Riemann hypothesis is true up to 3·10^12
doi: 10.1112/blms.12460
url: https://arxiv.org/abs/2004.09765v1
claim: Published verification supplies the finite-height RH premise. Retaining the positive Gamma filtering loss strengthens the existing whole-source negative allowance to every fixed logarithmic exponent below two-thirds; finite height still leaves a negative allowance.
strata_touched: []
license: citation-only
triage: anchor
---

# Verified zero height and the retained Gamma reserve

## Published input and the additional application

Platt--Trudgian, *The Riemann hypothesis is true up to
$3\cdot10^{12}$*, Bulletin of the London Mathematical Society **53**
(2021), no. 3, 792--797, DOI
[10.1112/blms.12460](https://doi.org/10.1112/blms.12460).
Theorem 1 of the [arXiv v1 primary](https://arxiv.org/pdf/2004.09765v1),
printed p.2, states verification through height $3000175332800$.
This published computation is reused, without repeating or independently
certifying it.

For $T\ge3$, write $\mathsf{RH}(T)$ for the assertion that every
nontrivial zeta zero with $|\Im\rho|\le T$, including the height
boundary, lies on $\Re\rho=1/2$. The source supplies this premise at
$T_0=3\cdot10^{12}$; it does not supply unbounded verified heights.

The [existing actual-source account](suzuki2026screw.md#a-finite-verified-zero-height-controls-the-entire-actual-negative-allowance),
W359 and W365--W371, already transports this premise to the COMPLETE
physical form and its original sixth moment. Its lower allowance decays
as $(\log T)^{-1/3}$. The application below reuses the actual-domain
identification, the weighted profile bounds and the entire signed zero
tail. The additional step retains the positive Gamma filtering loss
while paying the complete prime-and-pole mixed error. The analytic
ingredients are classical weighted interpolation, the heat filter and
Young's inequality; no new general interpolation theorem, zero
verification or literature-priority claim is made. This is a paper
application, without Lean/kernel certification.

## The same full-source lower allowance with a stronger decay rate

Retain W317's actual domain $\mathcal V$, COMPLETE energy
$\mathfrak E(F)$ and original sixth moment $M(F)$, and W338's even
profile $g_F$. For every fixed $0<\kappa<2/3$, there is a finite
$C_\kappa$, independent of $T$, source, scalar field, coefficients,
count, width and support, such that

$$
\mathsf{RH}(T)\quad\Longrightarrow\quad
\mathfrak E(F)\ge
-\frac{C_\kappa M(F)}{(\log T)^\kappa}
\qquad(T\ge3,\ F\in\mathcal V).
\tag{VHR1}
$$

Constants may depend on the FIXED $\kappa$. The endpoint $2/3$ is not
asserted. For example, $\kappa=1/2$ improves the earlier asymptotic
exponent $1/3$ with the same interpolation weight $a=5/6$.

It suffices to consider $\mathfrak E(F)\le0$: positive-energy sources
already satisfy VHR1. If $M(F)=0$, the source is zero. Otherwise put
$M=M(F)>0$, $g=g_F$, $b=5/2$ and

$$
\|v\|_a^2=\int_{\mathbb R}e^{2a|r|}|v(r)|^2dr.
$$

W366, used ONLY on this nonpositive-energy class, gives
$\|g\|_b^2\le CM$. The profile also has the full logarithmic Fourier
form norm required in W359. In its exact normalization,
$\mathfrak E(F)=\alpha\mathcal Q_W(g)$ with
$\alpha=2/\sqrt\pi>0$. The form $\mathcal Q_W$ includes the signed
Gamma integral, every prime power and both poles.

### Keep the positive filtering loss before estimating the arithmetic error

For $0<\epsilon<1$, let $h=K_\epsilon*g$ be the existing normalized
heat filter, so $\widehat h(\tau)=e^{-\epsilon\tau^2}\widehat g(\tau)$
with unitary Fourier normalization. Put

$$
w=g-h,\quad H=\log(1/\epsilon),\quad
q(\tau)=\Re\operatorname{digamma}(1/4+i\tau/2)-\log\pi,
\quad q_0=q(0),\quad p=q-q_0.
$$

The owned digamma estimate gives $p\ge0$ and
$p(\tau)\ge cH$ on $|\tau|\ge\epsilon^{-1/4}$ once $H$ is sufficiently
large. Since $1-e^{-2x}\ge(1-e^{-x})^2$ for $x\ge0$, the shifted
nonnegative Gamma form satisfies

$$
\begin{aligned}
\Gamma_+(g)-\Gamma_+(h)
&:=\int_{\mathbb R}p(\tau)(1-e^{-2\epsilon\tau^2})
                  |\widehat g(\tau)|^2d\tau\\
&\ge cH\|w\|_0^2-CH\epsilon M.
\end{aligned}
\tag{VHR2}
$$

Indeed, below the frequency cut,
$|1-e^{-\epsilon\tau^2}|^2\le\epsilon$, so the omitted low-frequency
part of $\|w\|_0^2$ is at most $\epsilon\|g\|_0^2$.
The signed constant part of Gamma costs at most
$2|q_0|\|g\|_0\|w\|_0$, because the filter contracts the unweighted
norm. Thus it is bounded by $C\sqrt M\|w\|_0$, without discarding VHR2.

For every fixed $1/2<a<b$, weighted heat convolution gives
$\|h\|_b+\|w\|_b\le C\sqrt M$. Weighted interpolation, with
$\theta=a/b\in(0,1)$, gives

$$
\|w\|_a\le\|w\|_0^{1-\theta}\|w\|_b^\theta
\le C M^{\theta/2}\|w\|_0^{1-\theta}.
\tag{VHR3}
$$

Write $\mathcal B$ for the ENTIRE prime-and-pole part of
$\mathcal Q_W$. The same weighted correlation bound used in W368 yields

$$
|\mathcal B(g,g)-\mathcal B(h,h)|
\le C_a(\|g\|_a+\|h\|_a)\|w\|_a
\le C_a\sqrt M\|w\|_a.
\tag{VHR4}
$$

For precision, its prime bound uses
$|\int v(r)\overline{u(r-s)}dr|
\le e^{-a|s|}\|v\|_a\|u\|_a$ and the convergent COMPLETE series
$\sum_{n\ge2}\Lambda(n)n^{-a-1/2}$. The two exponential pole
functionals are continuous in the same norm since $a>1/2$.
Polarization therefore proves VHR4 for complex, signed profiles too.
No prime-power truncation or favorable correlation sign enters.

### Pay the mixed error against this same reserve

Set $r=\|w\|_0/\sqrt M$. Combining VHR2--VHR4 on the SAME actual
profile and its ONE filtered difference gives

$$
\mathcal Q_W(g)\ge\mathcal Q_W(h)
+M\bigl[cHr^2-Cr-C_ar^{1-\theta}-CH\epsilon\bigr].
\tag{VHR5}
$$

Split the positive quadratic term into two equal payments. Young's
inequality, or direct minimization in the single real variable $r\ge0$,
gives

$$
\begin{aligned}
Cr&\le\tfrac c2Hr^2+C'/H,\\
C_ar^{1-\theta}&\le\tfrac c2Hr^2+
 C'_a H^{-(1-\theta)/(1+\theta)}.
\end{aligned}
$$

Since $0<(1-\theta)/(1+\theta)<1$, the $H^{-1}$ and
$H\epsilon=He^{-H}$ costs can be included in the latter bound. Hence,
for sufficiently large $H$,

$$
\mathcal Q_W(g)\ge\mathcal Q_W(h)
-C_a M H^{-(b-a)/(b+a)}.
\tag{VHR6}
$$

For any FIXED $0<\kappa<2/3$, choose
$a=(5/2)(1-\kappa)/(1+\kappa)>1/2$; then
$(b-a)/(b+a)=\kappa$. This consumes the positive Gamma difference
once. It does not assume the desired sign of the complete energy.

### Reuse the complete signed zero tail and return to original sources

Under $\mathsf{RH}(T)$, W369--W370 already give, for
$\epsilon=1/T$,

$$
\mathcal Q_W(h)\ge
-CM\sqrt T\log(2+T)e^{-T}.
\tag{VHR7}
$$

That argument keeps nonreal zeros in their signed conjugate pairing;
only the inclusively verified head becomes a sum of nonnegative
squares. Its entire unverified tail, multiplicities and domain passage
are reused unchanged. It does not require $h$ to be another actual
source profile. VHR6--VHR7 and W359 prove VHR1 for large $T$.
W317's uniform $\mathfrak E(F)\ge-CM(F)$ absorbs the remaining bounded
range $3\le T\le T_*$ by increasing $C_\kappa$.

The original-source normalization W257 and the already defined
completed minima in W371 consequently give, under the SAME premise,

$$
\begin{gathered}
e_K\ge-\frac{C_\kappa K}{(\log T)^\kappa}
\qquad(K>1),\\
4\pi^3 A Q_{\mathcal K_A^g}(\sigma)
\ge-\frac{C_\kappa}{(\log T)^\kappa}Q_{6,A}(\sigma).
\end{gathered}
\tag{VHR8}
$$

These are the original moment, source and full form, with arbitrary
admitted count, width and real or complex coefficients. No auxiliary
source is renormalized and no positive subclass replaces the full class.

The improvement is an asymptotic decay rate. The constants have not
been numerically evaluated, so no numerical improvement at $T_0$ is
asserted. Taking $a\downarrow1/2$ makes the prime-and-pole constants
singular; the proof supplies neither the endpoint $\kappa=2/3$ nor a
constant uniform up to it. A fixed verified height leaves a negative
allowance. Its removal still requires unbounded heights or an
independent signed estimate. Thus VHR1--VHR8 prove neither
$e_4=0$, all-source positivity, RH, the same-integer signed Robin tail
bound nor strict Robin for every integer $n>5040$.
