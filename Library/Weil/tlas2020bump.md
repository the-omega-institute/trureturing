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

The prefactor $\widetilde k^{-1/2}$ outside the source's saddle integral combines with its $\widetilde k^{-1/4}$ saddle prefactor. Consequently (1) gives constants $a>0$, $\eta\in\mathbb R$ and a real remainder $r(t)\to0$ such that

$$
\Phi(t)=a\,t^{-3/4}e^{-\sqrt{t/2}}
\left[\cos\!\left(t/2-\sqrt{t/2}+\eta\right)+r(t)\right],
\qquad t\to+\infty.
\tag{2}
$$

The error in (2) is in units of the positive envelope $t^{-3/4}e^{-\sqrt{t/2}}$. No division by the cosine is made. The fixed phase is retained, and no numerical threshold or explicit bound for $r$ is supplied by this application.

[Johnson, arXiv:1508.04376v1, §2](https://arxiv.org/pdf/1508.04376v1) analyzes the same bump, with $\Phi(t)=F(t/2)/2$, and displays the complex coefficient explicitly. It is a technical note using approximate expressions and numerical comparisons; those comparisons alone do not establish a uniform error at cosine zeros. The input used here is Tlas's complex saddle asymptotic in the proof, not an extrapolation of Johnson's finite numerical check. Saddle analysis and the original bump's decay belong to these sources, rather than to a new project criterion.
