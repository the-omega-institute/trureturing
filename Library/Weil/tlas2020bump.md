---
bibkey: tlas2020bump
authors: T. Tlas
year: 2020
title: Bump Functions With Monotone Fourier Transforms Satisfying Decay Bounds
doi: null
url: https://arxiv.org/abs/2003.12364v2
claim: The initial saddle lemma matches the prescribed bump; retaining its complex coefficient before taking real parts supplies an absolute-envelope asymptotic with a fixed phase, rather than a relative estimate through Fourier zeros.
strata_touched: []
license: citation-only
triage: anchor
---

# The original bump and its real-frequency supplier

The source is [arXiv:2003.12364v2](https://arxiv.org/pdf/2003.12364v2), initial lemma and proof on PDF pp.2–3. The original PDF and TeX were inspected. The displayed real cosine formula suppresses a constant phase; the complex saddle expression immediately before taking real parts retains the needed coefficient. The statements and applications here are paper-level, without a Lean implementation.

## Match the function and Fourier convention

Keep exactly the original test of [the research volume, §§19.3 and 30](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md):

$$
\phi(x)=e^{-1/(1-4x^2)}\mathbf1_{\{|x|<1/2\}},
\qquad \Phi(t)=\int_{\mathbb R}\phi(x)e^{-itx}\,dx.
$$

Tlas's initial lemma concerns

$$
\phi_{A,B}(v)=
e^{-B/(1-v)^A}e^{-B/(1+v)^A}\mathbf1_{\{|v|<1\}},
\qquad
\widehat{\phi_{A,B}}(k)=\int\phi_{A,B}(v)e^{-2\pi ikv}\,dv.
$$

At $A=1$, $B=1/2$ there is an exact identity, including the support:

$$
\phi_{1,1/2}(2x)=\phi(x),
\qquad
\Phi(t)=\tfrac12\widehat{\phi_{1,1/2}}\!\left(\frac{t}{4\pi}\right).
\tag{1}
$$

Thus the source variable $\widetilde k=2\pi k$ is $t/2$, and its two exponential coefficients are $\alpha=\beta=1$. This uses the initial lemma, rather than the final theorem's different function with a monotone Fourier transform.

## Retain the saddle coefficient before taking real parts

On p.3 the contour integral is written as twice the real part of a single complex integral. For these parameters the latter has, up to its nonzero complex leading coefficient, the form

$$
\widetilde k^{-3/4}
\exp\!\left(-i\widetilde k+(-1+i)\sqrt{\widetilde k}\right)
(o(1))\widetilde k^{-3/4}e^{-\sqrt{\widetilde k}}.
$$

The prefactor $\widetilde k^{-1/2}$ outside the source's saddle integral combines with its $\widetilde k^{-1/4}$ saddle prefactor. Consequently (1) gives constants $a>0$, $\eta\in\mathbb R$ and a real remainder $\varepsilon(t)\to0$ such that

$$
\Phi(t)=a\,t^{-3/4}e^{-\sqrt{t/2}}
\left[\cos\!\left(t/2-\sqrt{t/2}+\eta\right)+\varepsilon(t)\right],
\qquad t\to+\infty.
\tag{2}
$$

The error in (2) is in units of the positive envelope $t^{-3/4}e^{-\sqrt{t/2}}$. No division by the cosine is made. The fixed phase is retained, and no numerical threshold or explicit bound for $\varepsilon$ is supplied by this application.

[Johnson, arXiv:1508.04376v1, §2](https://arxiv.org/pdf/1508.04376v1) analyzes the same bump, with $\Phi(t)=F(t/2)/2$, and displays the complex coefficient explicitly. It is a technical note using approximate expressions and numerical comparisons; those comparisons alone do not establish a uniform error at cosine zeros. The input used here is Tlas's complex saddle asymptotic in the proof, not an extrapolation of Johnson's finite numerical check. Saddle analysis and the original bump's decay belong to these sources, rather than to a new project criterion.

## Apply the supplier to the unchanged dilation average

Retain the volume's original nonnegative normalized weight $w$, supported on $[1,b]$, where $b=2+\sqrt5$, and its fixed verified height $H=3000175332800$. Its head is

$$
P_H(R)=2\sum_{0<\gamma\le H}m_\rho p(\gamma)
\int_1^b w(u)\Phi(uR\gamma)^2\,du,
\qquad p(z)=z^2(1+4z^2)^2.
$$

The fixed verified zeros in this head lie on the critical line. Reuse the actual critical zero $\gamma_0\in[14,15]$ and the volume's already established bound $w\ge w_0>0$ on $I=[5/4,5/2]$. These are fixed published inputs; no verified height is enlarged.

Put $r=R\gamma_0$ and $\Theta_r(u)=ur/2-\sqrt{ur/2}+\eta$. On $I$,

$$
\Theta_r'(u)=\frac r2-\frac{\sqrt r}{2\sqrt{2u}},
\qquad
\int_I\cos^2\Theta_r(u)\,du=\frac{|I|}{2}+O(r^{-1}).
$$

The latter is ordinary integration by parts in the oscillatory cosine term: $\Theta_r'$ is bounded below by a positive multiple of $r$, and $\Theta_r''=O(\sqrt r)$ on this fixed interval. Equation (2) also gives $\sup_{u\in I}|\varepsilon(ur)|\to0$, so the integral of the squared bracket in (2) is at least $|I|/8$ for all sufficiently large real $R$. No pointwise positive lower bound for $\Phi$ is asserted.

Throughout the core, $uR\gamma_0\le(75/2)R$. Its squared positive envelope therefore satisfies

$$
(uR\gamma_0)^{-3/2}e^{-\sqrt{2uR\gamma_0}}
\ge (75/2)^{-3/2}R^{-3/2}e^{-\sqrt{75R}}.
$$

Keeping just this actual nonnegative head term proves the paper-level application

$$
P_H(R)\ge cR^{-3/2}e^{-\sqrt{75R}}
\ge cR^{-3/2}e^{-10\sqrt R}
\qquad(R\ge R_0),
\tag{3}
$$

for some $c>0$ and finite $R_0$. Neither constant is numerically certified here. This applies the existing saddle supplier and a standard positive average; it is not a new saddle theorem, zero computation or RH criterion.

## What the strengthened reserve pays

For actual zeros $\rho=\beta+i\gamma$, put $z_\rho=\gamma-i(\beta-1/2)$ and keep the analytic square. Consider precisely the infinite subset

$$
\mathcal C_H(R)=
\{\rho:\gamma>H,\ |\beta-1/2|\le R^{-1/2}\},
\qquad
E_{\mathrm{near}}(R)=
2\sum_{\rho\in\mathcal C_H(R)}m_\rho p(z_\rho)
\int_1^b w(u)\Phi(uRz_\rho)^2\,du.
$$

The subset retains reflected positive-ordinate pairs and their actual multiplicities. Its dependence on $R$ does not change the pointwise-in-$R$ use of the existing common zero-count bound. Reuse the volume's complete-tail proof in §31.2: it needs only the actual critical strip, $N_+(t)\le t\log t$, and the complex Fourier estimate. Its use of $|\beta-1/2|<1/2$ in the polynomial majorant remains valid. The refined restriction gives, in the Fourier factor alone,

$$
|\Phi(uRz_\rho)|^2
\le16e^{b\sqrt R-\sqrt{R\gamma}/3}.
$$

The same nonnegative summable majorant, with cutoff $H$ and $\sqrt{RH}/3\ge28$, consequently gives

$$
|E_{\mathrm{near}}(R)|
\le6000H^7\log H\,
e^{b\sqrt R-\sqrt{RH}/3},
\qquad R\ge1.
\tag{4}
$$

The absolute square appears only in this legitimate upper majorant; the original expression defining $E_{\mathrm{near}}$ retains its analytic square. All zeros at height $H$ remain in the inclusive head. The existing tail proof, not a new criticality assumption above $H$, supplies the count and summation in (4).

Combining (3)–(4) yields

$$
\frac{|E_{\mathrm{near}}(R)|}{P_H(R)}
\le\frac{6000H^7\log H}{c}\,R^{3/2}
\exp\!\left[-\left(\frac{\sqrt H}{3}-b-10\right)\sqrt R\right]
\longrightarrow0.
\tag{5}
$$

In particular this subset can use less than half the fixed head for all sufficiently large real $R$, without a numerical threshold claim. This is a restricted application of existing bounds. The complementary actual zeros with $\gamma>H$ and $|\beta-1/2|>R^{-1/2}$ still have an uncontrolled signed contribution. Every hypothetical fixed nonzero horizontal displacement eventually belongs to that complement. Thus (5) neither excludes off-line zeros nor establishes positivity of the complete average, RH, Robin, or the FIB-to-prime intertwining.
