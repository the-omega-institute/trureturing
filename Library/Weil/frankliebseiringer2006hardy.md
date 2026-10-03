---
bibkey: frankliebseiringer2006hardy
authors: Rupert L. Frank, Elliott H. Lieb, and Robert Seiringer
year: 2006
title: Hardy-Lieb-Thirring inequalities for fractional Schrodinger operators
doi: null
url: https://arxiv.org/abs/math/0610593v2
claim: Nonlocal IMS retains a joint pole-prime correction. Below the first prime shift, refinement leaves the prime atoms unchanged; actual local contributions minus the actual Gamma defect approach the negative shifted-digamma baseline on slow dilations. Positivity requires a positive arithmetic reserve, which is not supplied by the mesh or the known optimal local floor.
strata_touched: []
license: citation-only
triage: anchor
---

# Nonlocal localization and the actual Weil correction

The primary source is [Frank–Lieb–Seiringer, arXiv:math/0610593v2](https://arxiv.org/pdf/math/0610593v2), 27 October 2006, §3.3, Lemma 3.5 and equation (3.13), printed p.12. For $u\in C_c^\infty(\mathbb R^d)$, $0<s<\min(1,d/2)$ and a finite real Lipschitz square partition $\sum_j\chi_j(x)^2=1$ for all $x\in\mathbb R^d$, it writes the fractional Hardy form as the sum of the localized forms minus an integral-operator correction. That correction has kernel

$$
a_{s,d}|x-y|^{-d-2s}\sum_j(\chi_j(x)-\chi_j(y))^2.
$$

The paper's fractional kernel is not the Weil Gamma kernel and has no prime atoms or zeta pole term. The transferable ingredient is the localization calculation; its arithmetic application below is a separate paper derivation, not an additional theorem attributed to that source or a newly compiled general Weil theorem. A nonnegative pointwise correction kernel need not define a positive semidefinite operator.

## Common test and normalization

Use the project's [actual energy decomposition](../../D5/S3/Weil/Separator/UnconditionalExplicitFormula.lean). Let $f\in C_c^\infty(\mathbb R;\mathbb C)$ be even, with support in $[-L,L]$, $L>0$. Let $\chi_1,\ldots,\chi_m$ be real, even, smooth functions satisfying $\sum_i\chi_i(x)^2=1$ on $[-L,L]$, and put $f_i=\chi_i f$. Each $f_i$ is an admissible even test. Use the same global $L$ for every term. Write

$$
E_t(f)=\int_{\mathbb R}|f(x)-f(x-t)|^2\,dx,
\qquad k_\Gamma(t)=\frac{e^{-t/2}}{1-e^{-2t}},
\qquad P(f)=2\left|\int_{\mathbb R}e^{x/2}f(x)\,dx\right|^2.
$$

With $w_n=\Lambda(n)/\sqrt n$, the source form is

$$
Q(f)=P(f)+\int_0^\infty k_\Gamma(t)E_t(f)\,dt
+\sum_{2\le n\le e^{2L}}w_nE_{\log n}(f)-c_L\|f\|_2^2,
\qquad c_L=2\sum_{2\le n\le e^{2L}}w_n-c_\Gamma.
$$

Here $c_\Gamma=\Re\operatorname{digamma}(1/4)-\log\pi$, and $\Lambda$ includes prime powers. A linear partition $\sum\rho_i=1$ is not automatically a square partition. Taking $\sqrt{\rho_i}$ also needs a smoothness argument at its zeros. The ordinary smooth partition construction in [ExternalSupportInvisibility](../../D5/S3/Weil/TestFunctions/ExternalSupportInvisibility.lean) does not by itself settle these obligations.

Define the real defect correlation

$$
D_\chi(x,t)=\sum_i(\chi_i(x)-\chi_i(x-t))^2,
\qquad K_f(t)=\int_{\mathbb R}D_\chi(x,t)\Re\bigl(f(x)\overline{f(x-t)}\bigr)\,dx.
$$

Square expansion gives the one-shift IMS identity

$$
\sum_i E_t(f_i)-E_t(f)=K_f(t).
$$

There is no extra $1/2$ in this one-shift convention. The mass term cancels because $\sum_i\|f_i\|_2^2=\|f\|_2^2$. The function $K_f$ is real, even, smooth, supported in $[-2L,2L]$, and $K_f(0)=K_f'(0)=0$. It need not be nonnegative for complex or sign-changing $f$.

## Keep the pole and primes together

The global pole does not split into independent local squares. Expanding it gives

$$
P(f)-\sum_iP(f_i)
=\iint e^{(x+y)/2}\sum_i(\chi_i(x)-\chi_i(y))^2
\Re\bigl(f(x)\overline{f(y)}\bigr)\,dx\,dy.
$$

Evenness of both $f$ and the multipliers permits $y\mapsto-y$, changing the exponential to $e^{(x-y)/2}$ without changing the remaining factor. Setting $t=x-y$ and pairing positive and negative $t$ yields

$$
P(f)-\sum_iP(f_i)=2\int_0^\infty\cosh(t/2)K_f(t)\,dt.
$$

Consequently the complete localization correction is

$$
Q(f)-\sum_iQ(f_i)
=\int_0^\infty e^{t/2}K_f(t)\,dt
-\sum_{2\le n\le e^{2L}}\frac{\Lambda(n)}{\sqrt n}K_f(\log n)
-\int_0^\infty\frac{e^{-5t/2}}{1-e^{-2t}}K_f(t)\,dt. \tag{1}
$$

This uses the exact cancellation
$2\cosh(t/2)-k_\Gamma(t)=e^{t/2}-e^{-5t/2}/(1-e^{-2t})$.
Estimating the pole and prime terms separately would discard this common-source cancellation.

Let $\Psi(u)=\sum_{n\le u}\Lambda(n)$ be the right-continuous Chebyshev function, distinct from the golden conjugate, and define $W_f(u)=u^{-1/2}K_f(\log u)$ for $u\ge1$. Equation (1) becomes

$$
Q(f)-\sum_iQ(f_i)
=\int_1^{e^{2L}}(\Psi(u)-u)W_f'(u)\,du
-\int_1^{e^{2L}}\frac{W_f(u)}{u(u^2-1)}\,du. \tag{2}
$$

Indeed the first two terms of (1) equal $-\int W_f\,d(\Psi-u)$. Integration by parts has no boundary charge: $W_f(1)=W_f(e^{2L})=0$. At $u=1$, $W_f(u)=O((u-1)^2)$, so the second integrand is integrable. Compact support makes this a finite-scale identity without any PNT or RH hypothesis. This calculation preserves signs; it is not a bound on the Chebyshev error.

For a joint Lipschitz bound $\|\chi(x)-\chi(y)\|_{\ell^2}\le B|x-y|$ on $[-L,L]$, Cauchy–Schwarz gives $|K_f(t)|\le B^2t^2\|f\|_2^2$. Thus the last term of (1) has absolute value at most $C_*B^2\|f\|_2^2$, where

$$
C_*:=\int_0^\infty\frac{t^2e^{-5t/2}}{1-e^{-2t}}\,dt
=2\sum_{m\ge0}(2m+5/2)^{-3}<\infty.
$$

A cutoff family with $B\le C/L$ would give an $O(L^{-2})$ bound for this Gamma remainder. The existence of such a family subordinate to increasingly fine FIB windows is an additional condition, not a consequence of the window count. The signed first integral in (2) remains the arithmetic obligation for the same actual $f$ and cutoffs. A large absolute-value envelope neither supplies that lower bound nor proves no better estimate is possible.

## Ordinary windows require both poles

The preceding even-test calculation has a general paper-level extension. For an arbitrary complex smooth compactly supported $g$, use

$$
A_\pm(g)=\int e^{\pm x/2}g(x)\,dx,
\qquad P_{\rm full}(g)=2\Re\bigl(A_+(g)\overline{A_-(g)}\bigr).
$$

This is the two-pole term from the [general explicit formula](../../D5/S3/Weil/ZetaCore/ExplicitFormulaBridge.lean), rather than an application of the even-only rank-one energy bundle to a non-even function. With this pole term, write $Q_{\rm full}$ for the same energy expression with the same ambient $L$ and $c_L$. It agrees with $Q$ on even tests. Its pole kernel is $2\cosh((x-y)/2)$, so for arbitrary smooth $f$ and real smooth square multipliers on its ambient interval,

$$
P_{\rm full}(f)-\sum_iP_{\rm full}(\chi_i f)
=2\int_0^\infty\cosh(t/2)K_f(t)\,dt.
$$

Thus (1) and (2) apply to $Q_{\rm full}$ without requiring the individual pieces to be even. On odd pieces the pole term is negative, not a positive square. Translation of $g$ multiplies $A_+$ and $A_-$ by opposite real factors, which cancel in their product; the full form is translation invariant. The actual general explicit-form interface is reusable, but the complete non-even jump-energy and localization bridge displayed here has not been compiled as a new Lean theorem.

## Reuse the stronger small-window spectral floor

For an interval of length $d<\log2$, prime autocorrelations vanish. This does not make the whole-line Gamma energy vanish: its interaction with the exterior supplies an endpoint potential. The relevant existing result is [Suzuki v3](suzuki2026screw.md), Corollary 1.2 and Theorem 1.4, not a new small-window positivity claim. With $\lambda^W_a$ the source's lowest Weil eigenvalue on $(-a,a)$, it gives

$$
\lambda^W_{d/2}=\log(1/d)-\gamma-\log\pi+\mu_1+O(d),
\qquad \mu_1>0. \tag{3}
$$

Here $\mu_1$ is the lowest Rayleigh value of the closure of the form in its equation (4.4),

$$
\mathcal L(v)=\frac14\iint_{(-1,1)^2}\frac{|v(x)-v(y)|^2}{|x-y|}\,dx\,dy
-\frac12\int_{-1}^1\log(1-x^2)|v(x)|^2\,dx.
$$

The initial domain is $H^1_0(-1,1)$; a constant is not in that initial domain. The smooth approximation in the source's §3.2 and the logarithmic Fourier form norm in (4.6) put the constant in the closed form domain. Its Rayleigh quotient is $1-\log2$, hence

$$
0<\mu_1\le1-\log2. \tag{4}
$$

This upper comparison uses the source's domain argument, rather than assuming that an arbitrary boundary value is admissible. A direct exterior-potential lower bound with asymptotic $\log(1/d)-\gamma-\log\pi+O(d)$ discards $\mu_1$ and is weaker than (3). Reproving that weaker local positivity would not close the present gap. The source theorem and this application have not been independently formalized here.

## The cost of a fine square partition

Suppose now that the smooth cutoffs are nonnegative and their vector has Lipschitz constant $B>0$ on the common ambient interval. The two unit cutoff vectors give

$$
0\le D_\chi(x,t)\le\min(B^2t^2,2),
\qquad |K_f(t)|\le\min(B^2t^2,2)\|f\|_2^2
$$

on pairs relevant to the correlation. Let $k_*(t)=e^{-5t/2}/(1-e^{-2t})$. A sharper scalar Gamma envelope than the earlier $C_*B^2$ is

$$
I_2(B)=\int_0^\infty k_*(t)\min(B^2t^2,2)\,dt
=\log B+c_{\rm IMS}+R(B),
\quad c_{\rm IMS}=\tfrac32\log2+\tfrac\pi2-\tfrac72, \tag{5}
$$

where, writing $a=\sqrt2/B$,

$$
R(B)=\int_0^a(2-B^2t^2)\left(\frac1{2t}-k_*(t)\right)dt>0,
\qquad R(B)=O(B^{-1}).
$$

To obtain (5), split at $a$ and use
$\int_s^\infty k_*(t)dt=\operatorname{atanh}(e^{-s/2})+\arctan(e^{-s/2})-2e^{-s/2}$.
The subtracted kernel tends to $3/4$ at zero and is positive for $t>0$; this also proves the stated remainder properties. For the actual finite support cutoff, when $2L>a$,

$$
I_2(B,2L)=I_2(B)-2\int_{2L}^\infty k_*(t)\,dt. \tag{6}
$$

The discarded tail tends to zero as $L\to\infty$. These formulas concern a uniform upper envelope, not the value or a lower bound of the signed Gamma correction for a particular $f$.

There is also a geometric cost. If every cutoff support has diameter at most $d$ and the ambient interval contains a segment longer than $d$, cutoff vectors at distance greater than $d$ are orthogonal. The square partition traces the unit sphere, so that segment's image has length at least $\pi/2$. Its length is at most $B$ times the segment length. Taking distances down to $d$ gives

$$
Bd\ge\pi/2. \tag{7}
$$

Consider cofinal supports $L_j\to\infty$ and fine partitions with $d_j\downarrow0$, whose **actual smooth cutoff support intervals** have lengths $d_{j,i}\in[d_j/r,d_j]$ for a fixed $r\ge1$. For nonzero tests $f_j$ supported in the corresponding ambient intervals, set

$$
\mathcal B_j=
\frac{\sum_i\lambda^W_{d_{j,i}/2}\|\chi_{j,i}f_j\|_2^2}{\|f_j\|_2^2}
-I_2(B_j,2L_j).
$$

Equations (3)–(7) give the uniform paper-level comparison

$$
\limsup_j\mathcal B_j
\le\log r+\frac92-\gamma-2\log\pi-\frac32\log2-\frac\pi2. \tag{8}
$$

The right side is approximately $-0.977193$ for $r=1$ and $-0.495981$ for $r=\varphi$. The latter is a conditional width-ratio example: the ratio of bare FIB cylinder lengths does not construct a smooth square partition or prove this ratio for its support intervals. Smooth cutoffs must overlap at the seams, and their actual widths and Lipschitz constants must be checked.

For $1\le r\le\varphi$, this rejects a particular sufficient budget even when the **optimal** local spectral constants are used: subtracting this independent Gamma envelope and merely using a zero lower bound for the signed arithmetic term in (2) cannot give positive fine-scale margins under these conditions. Equation (8) does not give this rejection for every fixed width ratio. It does not give a negative value of the actual Weil form, a lower bound on its actual Gamma cost, or an obstruction to stronger joint estimates. The local surpluses, localization defect and arithmetic term depend on the same $f$ and cutoffs; retaining those relations is the remaining route. The analytic asymptotics and comparison (8) are not a new compiled general theorem.

## A smooth realization of the physical windows

The width-ratio hypothesis can be realized by standard mollification and normalization. This constructs windows in the chosen physical interval chart; it does not intertwine FIB ATOM operations with prime translation.

Take adjacent tiles $I_i=[b_i,b_{i+1})$ of lengths in $[a,\varphi a]$, $a>0$, and a nonnegative smooth mollifier $\eta$ of integral one, positive on $(-1,1)$ with topological support $[-1,1]$. Put $\eta_\varepsilon(x)=\varepsilon^{-1}\eta(x/\varepsilon)$, $0<\varepsilon<a/2$, and

$$
\rho_i=\eta_\varepsilon*\mathbf1_{I_i},\qquad
s=(\sum_i\rho_i^2)^{1/2}.
$$

Index the tiles by $0\le i<N$, include tiles $0,N-1$ as padding in this sum, and keep the source support compactly inside $(b_1+\varepsilon,b_{N-1}-\varepsilon)$. On $U=(b_0+\varepsilon,b_N-\varepsilon)$, the $\rho_i$ sum to one and at most two are nonzero, so $s\ge1/\sqrt2$. For interior tiles define $\chi_i=\rho_i/s$ on $U$ and zero outside. Each retained numerator's support is compactly contained in $U$, making this extension smooth. The retained family has square unity near the source support and global squared norm at most one.

The complete cutoff support widths and a joint Lipschitz bound are

$$
d_i=b_{i+1}-b_i+2\varepsilon,\qquad
\frac{\max d_i}{\min d_i}\le\frac{\varphi a+2\varepsilon}{a+2\varepsilon}<\varphi,
\qquad B\le\frac{2\|\eta\|_\infty}{\varepsilon}.
$$

Indeed $\rho_i'=\eta_\varepsilon(x-b_i)-\eta_\varepsilon(x-b_{i+1})$. At most one seam contributes at a point, so $\|\rho'\|_{\ell^2}\le\sqrt2\|\eta\|_\infty/\varepsilon$. Differentiating $\rho/\|\rho\|$ is orthogonal projection followed by division by $s$, giving the bound. No additional endpoint cutoff is inserted. These widths belong to the complete $\chi_i$, not the possibly smaller supports of a particular $\chi_i f$. This uses standard smooth partition ingredients and supplies no new arithmetic positivity.

## The actual residual requires a positive arithmetic contribution

The same-function comparison avoids replacing the Gamma defect by a scalar envelope. Let $f\in C_c^\infty(\mathbb R;\mathbb C)$ have support in $[-L,L]$, and let a finite real smooth square partition hold there. Suppose each $g_i=\chi_i f$ has support in an interval of length at most $d<\log2$. Keep the full two-pole form and the same ambient prime cutoff for all terms. Define

$$
R_f(t)=\Re\int f(x)\overline{f(x-t)}\,dx,\qquad
\mathcal C(g)=\iint e^{|x-y|/2}\Re\bigl(g(x)\overline{g(y)}\bigr)\,dx\,dy.
$$

Every local prime correlation vanishes. Since $K_f(t)=2(R_f(t)-\sum_iR_{g_i}(t))$, at every prime-power atom $K_f(\log n)=2R_f(\log n)$, independently of the partition. The signed arithmetic integral in (2), denoted $J_\chi(f)$, decomposes exactly as

$$
J_\chi(f)=J_{0,L}(f)-A_\chi(f),\qquad
A_\chi(f)=\sum_i\mathcal C(g_i),
$$

$$
J_{0,L}(f)=2\int_0^{2L}e^{t/2}R_f(t)\,dt
-2\sum_{2\le n\le e^{2L}}\frac{\Lambda(n)}{\sqrt n}R_f(\log n).
$$

The interval kernel gives a uniform bound without cutoff derivatives:

$$
|A_\chi(f)|\le2(e^{d/2}-1)\|f\|_2^2. \tag{9}
$$

For $x\in[a,b]$, $b-a\le d$, its row integral is
$2(e^{(x-a)/2}+e^{(b-x)/2}-2)\le2(e^{d/2}-1)$.
Apply $2|uv|\le|u|^2+|v|^2$ and sum the local masses to obtain (9). Thus $J_\chi$ converges to $J_{0,L}$ as the maximum width tends to zero, uniformly on unit tests with an error bound independent of $L$. Refinement below the first prime shift changes only this controlled local continuum term.

Write $E_*(f)=\int_0^\infty k_*(t)E_t(f)dt$ and $a_0=c_\Gamma+4$. The complete accounting is

$$
Q_{\rm full}(f)=a_0\|f\|_2^2+E_*(f)+J_{0,L}(f), \tag{10}
$$

$$
S_\chi(f):=\sum_iQ_{\rm full}(g_i)-\int_0^\infty k_*(t)K_f(t)dt
=a_0\|f\|_2^2+E_*(f)+A_\chi(f). \tag{11}
$$

To check the cancellation, the full pole has kernel $e^{|x-y|/2}+e^{-|x-y|/2}$, while

$$
\int_0^\infty e^{-t/2}E_t(g)dt
=4\|g\|_2^2-\iint e^{-|x-y|/2}\Re(g(x)\overline{g(y)})dxdy.
$$

Using $k_\Gamma-k_*=e^{-t/2}$ cancels the decaying kernel and leaves $\mathcal C(g)$. The whole-line energy is essential: for shifts larger than the support width it is $2\|g\|_2^2$, not zero. The project's [pole-continuum and shifted-digamma identities](../../D5/S3/Weil/ZetaGamma/PoleContinuumCompletion.lean) and [renormalized Weil multiplier](../../D5/S3/Weil/ZetaGamma/RenormalizedWeilMultiplier.lean) already supply the completion for their even bundled tests. Equation (11) remains a paper application of the general explicit formula to the possibly non-even local pieces.

The baseline is strictly negative. Its series, supplied by [GammaMu](../../D5/S3/Weil/ZetaGamma/GammaMu.lean), gives

$$
a_0=\operatorname{digamma}(5/4)-\log\pi
=-\gamma-\log\pi+\sum_{m\ge1}\left(\frac1m-\frac1{m+1/4}\right)<-1.
$$

Indeed each summand is at most $\tfrac12(1/m-1/(m+1))$, whose sum is $1/2$, while $\gamma>1/2$ and $\log\pi>1$. Numerically $a_0\approx-1.372183419$; the strict sign uses the series bound rather than this decimal.

For a fixed even $h\in C_c^\infty(\mathbb R;\mathbb C)$ with $\|h\|_2=1$, put $f_R(x)=R^{-1/2}h(x/R)$, $R>0$. The standard translation estimate $E_t(f_R)\le t^2\|h'\|_2^2/R^2$ gives

$$
|S_\chi(f_R)-a_0|
\le2(e^{d/2}-1)+\frac{C_*\|h'\|_2^2}{R^2},\qquad
0<C_*\le\frac{26}{125}. \tag{12}
$$

For completeness, the translation estimate follows by integrating $f_R'$ along a segment, applying Cauchy–Schwarz and then Fubini. The moment bound follows from
$1/(1-e^{-2t})=1+1/(e^{2t}-1)\le1+1/(2t)$ for $t>0$ and
$\int_0^\infty(t^2+t/2)e^{-5t/2}dt=26/125$.
If $h$ and the cutoffs are nonnegative, then also $S_\chi(f_R)\ge a_0$.

As $R\to\infty$ and $d\to0$, the **actual** residual therefore tends to $a_0$, uniformly over these partitions, without any width-ratio, window-count or cutoff-derivative bound. Even if the widths merely remain below $\log2$, (12) gives

$$
\limsup_{R\to\infty} S_\chi(f_R)
\le a_0+2(\sqrt2-1)<2\sqrt2-3<0. \tag{13}
$$

The first bound is approximately $-0.543756294$. This uses actual local forms and the actual signed Gamma defect of the same test. It is not a negative-full-Weil example. Since $Q_{\rm full}(f_R)=S_\chi(f_R)+J_\chi(f_R)$, positivity for these tests requires

$$
J_\chi(f_R)\ge-a_0-2(e^{d/2}-1)-\frac{C_*\|h'\|_2^2}{R^2}. \tag{14}
$$

Equation (14) is a necessary condition under positivity, not a supplied prime-discrepancy estimate. In particular a zero lower bound for $J_\chi$ cannot alone certify these directions. The needed arithmetic estimate must provide this positive contribution and also control the other, oscillatory test directions. The identities and uniform estimates (9)–(14) are paper-level deductions; they do not settle RH or establish a new compiled localization theorem.

## Separating higher prime powers with the same test

The [weighted Mertens application](broadbent2026mertens.md) controls the higher-prime-power contribution for every compact smooth complex test, including the non-even local pieces. In the notation of (10), define the primary-prime discrepancy

$$
C_L(f)=2\int_0^{2L}e^{t/2}R_f(t)dt
-2\sum_{p\le e^{2L}}\frac{\log p}{\sqrt p}R_f(\log p).
$$

Keep the actual same $f$ throughout. Then $J_{0,L}(f)=C_L(f)-T(f)$, where $T$ is the higher-power sum in that note; compact support makes its infinite-index notation identical to the common finite cutoff. Writing

$$
T(f)=\tfrac12|\int f|^2+2\kappa\|f\|_2^2+\epsilon(f),\qquad
|\epsilon(f)|\le(8M_1+D_3)\|f'\|_2^2,
$$

the remaining comparison is exactly

$$
Q_{\rm full}(f)=C_L(f)-\tfrac12|\int f|^2
+(a_0-2\kappa)\|f\|_2^2+E_*(f)-\epsilon(f).
$$

The combined remainder has absolute value at most $(26/125+8M_1+D_3)\|f'\|_2^2$. Its higher-power energy has a favorable sign: that note also gives $-\epsilon(f)=4\int E(v)R_f'(2v)dv+\mathcal D_{\ge3}(f)$ with $\mathcal D_{\ge3}(f)\ge0$. Together with $E_*(f)\ge0$, this yields the paper-level sufficient condition

$$
C_L(f)\ge\tfrac12|\int f|^2+(2\kappa-a_0)\|f\|_2^2+8M_1\|f'\|_2^2
\quad\Longrightarrow\quad Q_{\rm full}(f)\ge0.
$$

No such lower bound for $C_L(f)$ has been supplied. The derivative budget is useful on fixed smooth slow dilations, where it decreases quadratically, and need not be affordable on oscillatory tests. The Mertens supplier closes one paper-level debit estimate while leaving the signed primary-prime comparison unresolved. It provides no FIB-to-prime-translation intertwiner, all-support positivity, or RH conclusion.

## A prime edge crossing an intermediate FIB window

The five first-level internal-coordinate intervals have geometric order $[3],[null],[5],[2],[2\ 5]$. Put $\varphi=(1+\sqrt5)/2$. In particular

$$
I_3=[-1,\varphi-2],\qquad I_{null}=[\varphi-2,2\varphi-3],\qquad I_5=[2\varphi-3,\varphi-1].
$$

For this test construction, choose these numerical intervals as windows in the Weil physical $x$ coordinate. This choice does not identify prime translation with an operation on the original golden-coordinate source or prove an intertwining theorem. Translation by $\log2$ sends the entire interval $[-41/100,-39/100]\subset\operatorname{int}I_3$ into $\operatorname{int}I_5$, across $I_{null}$. This is an edge of the actual prime translation, not a legal-digit seam transition.

For a smooth example take a nonzero even real $\eta\in C_c^\infty(-1/100,1/100)$, $a=2/5$, $b=\log2-2/5$, and

$$
f(x)=\eta(x-a)+\eta(x+a)+\eta(x-b)+\eta(x+b).
$$

It is even with support in $[-41/100,41/100]$. At this radius $2<e^{2L}<3$, so the only active prime power is $2$. The four bump supports are disjoint. Exactly the ordered centre pairs $(a,-b)$ and $(b,-a)$ have separation $\log2$, giving

$$
\int f(x)f(x-\log2)\,dx=2\|\eta\|_2^2>0.
$$

The original prime contribution to $Q$ is therefore $-2\sqrt2\log2\,\|\eta\|_2^2$. The pair $(b,-a)$ crosses $I_{null}$, whereas $(a,-b)$ connects $I_{null}$ to $I_5$. Dropping the nonadjacent pair alone loses $-\sqrt2\log2\,\|\eta\|_2^2$, half of the displayed prime contribution, even for a legitimate even smooth test. This is not a negative-full-form example and does not refute RH. Pairing mirrored windows to keep evenness changes their support geometry and must retain the corresponding cross terms.

## Reuse and remaining research target

The standard IMS identity is reusable mathematics, not a new FIB positivity theorem. The project's [smooth rational approximation](../../D5/S3/Weil/TestFunctions/RationalCutoffApproximation.lean) controls the complete paired zero sum; its [golden cofinal interface](../../D5/S3/Weil/CofinalSupport/GoldenCofinalPositivity.lean) still requires positivity for every admitted test at every chosen scale. Neither supplies a lower bound for the signed integral in (2).

A sufficient next input would combine genuine lower margins for the localized tests with a lower bound for the **same** $W_f$ against $\Psi-u$, paying the displayed Gamma remainder uniformly over all allowed coefficients and growing supports. Equation (14) is a necessary benchmark on the slow dilations, not this all-test sufficient bound. The family $W_f$ is constrained by a common $f$ and square partition; it cannot be replaced by arbitrary independently optimized weights. The corresponding Robin research also retains a joint signed prime fluctuation, but identifying those two test families requires another explicit map.

The analytic localization, Stieltjes calculations and uniform comparisons above are paper-level applications with their hypotheses displayed, not a new Lean closure. Transient exact Lean checks cover only the stated rational interval placement, first-prime support threshold, pointwise four-bump pairing, scalar Gamma cancellation, negativity of the scalar expression in (8) at $r=\varphi$, and the actual scalar inequalities $c_\Gamma+4<-1$ and $c_\Gamma+4+2(\sqrt2-1)<0$; no named wrapper is retained. The scalar checks do not prove the spectral-domain, asymptotic, integral or cutoff premises. The nonlocal source, these checks, and the missing all-scale arithmetic estimate have different evidentiary roles.
