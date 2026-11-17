---
bibkey: hiai2024affinerenyi
authors: Fumio Hiai
year: 2024
title: Log-majorization and matrix norm inequalities with application to quantum information
doi: 10.1007/s44146-024-00142-w
url: https://arxiv.org/abs/2402.16067
claim: Section 3 defines the alpha-z Renyi divergences; Remark 3.2 asks monotonicity along nonnegative affine parameter lines.
strata_touched:
  - D5/S3/Quantum/Divergence/AlphaZAffine
license: citation-only
triage: anchor
---

# Affine-parameter alpha-z Renyi monotonicity

For finite-dimensional positive semidefinite complex matrices
$\rho\ne0$ and $\sigma$, write $s(\rho)$ and $s(\sigma)$ for the
orthogonal projections onto their ranges. Section 3 uses

$$
Q_{\alpha,z}(\rho\Vert\sigma)
=\operatorname{Tr}\left|
\rho^{\alpha/(2z)}\sigma^{(1-\alpha)/(2z)}
\right|^{2z},\qquad z>0,
$$

when $\alpha\in[0,1]$ or $s(\rho)\le s(\sigma)$, and the value
$+\infty$ otherwise. Negative powers invert on the support and vanish
on the kernel. For $\alpha\ne1$,

$$
D_{\alpha,z}(\rho\Vert\sigma)
=\frac{\log\bigl(Q_{\alpha,z}(\rho\Vert\sigma)
 /\operatorname{Tr}\rho\bigr)}{\alpha-1}.
$$

At $\alpha=1$, the value, independent of $z$, is

$$
D_{1,z}(\rho\Vert\sigma)
=\frac{\operatorname{Tr}\rho(\log\rho-\log\sigma)}
 {\operatorname{Tr}\rho}
$$

under $s(\rho)\le s(\sigma)$, and $+\infty$ otherwise. In the
supported case the logarithms are evaluated on their supports; multiplication
by $\rho$ gives the convention $0\log0=0$.

Theorem 3.1(ii), as identified in the supplied source statement, gives the
fixed-$z$ monotonicity: for every fixed $z>0$, the function
$\alpha\mapsto D_{\alpha,z}(\rho\Vert\sigma)$ is nondecreasing
on $(0,\infty)$ with these endpoint and support conventions. Only this
part of Theorem 3.1 is used as a literature boundary here; no transcription
of its other parts is asserted.

Remark 3.2 asks whether, for $\kappa,z_0\ge0$ and
$\kappa+z_0>0$, the function

$$
\alpha\longmapsto
D_{\alpha,\kappa\alpha+z_0}(\rho\Vert\sigma)
$$

is nondecreasing on $(0,\infty)$. The case $\kappa=0$ is the fixed
positive-$z$ result above. The target is arbitrary finite dimension and
semidefinite inputs, including the normalized Umegaki value at one.

For positive definite inputs the repository proves joint convexity of
$\log Q_{\alpha,z}$ on $\mathbb R\times(0,\infty)$ by complex
three-lines interpolation of compound matrices, weak log-majorization,
and scalar Holder interpolation with perspective weights. Restriction to
an affine line and $Q_{1,z}=\operatorname{Tr}\rho$ give monotonicity of
the normalized secant slopes away from one, including comparisons across
one. The fixed-$z=1$ trace derivative is computed using
$A^a=\exp(a\log A)$ and the product rule. Joint convexity and the
constant value on the vertical line $\alpha=1$ transfer this derivative
to every affine line through a positive scale. Its value is the
normalized Umegaki trace, so convex secant inequalities insert one.

The theorem `D5.S3.Quantum.Divergence.AlphaZAffine.result` covers every
finite-dimensional supported semidefinite pair with $\rho\ne0$,
$\kappa>0$ and $z_0\ge0$, on the entire positive alpha axis. Its
support hypothesis is $\ker\sigma\subseteq\ker\rho$, equivalent
to $s(\rho)\le s(\sigma)$ for these Hermitian matrices. Common
positive regularization gives the semidefinite conclusion. In the power
product its kernel correction has the positive net exponent $1/(2z)$;
in the entropy product it is $\varepsilon\log\varepsilon$. Both
vanish at zero. The theorem has no convexity, derivative, regularization
limit, dimension bound or commutativity assumption.

The Lean conclusion quantifies only $\alpha>0$. At $\alpha=1$, the
sigma factor has exponent zero and CFC returns the identity; support
inclusion makes its extra kernel component vanish after multiplication
by the positive power of rho. This explanation concerns the sigma factor
at one only. At $\alpha=0$, CFC instead gives $\rho^0=I$, whereas the
source uses $s(\rho)$. For example, $\rho=\operatorname{diag}(1,0)$,
$\sigma=I_2$ gives the totalized Lean $Q_{0,z}=2$ and the source $Q_{0,z}=1$.

If $z_0=0$, the point $\alpha=0$ gives $z=0$ and lies outside the source
definition's domain. If $z_0>0$, the source endpoint is defined but is not
quantified by `result`. On each positive eigenspace,
$\rho^{\alpha/(2z(\alpha))}$ tends to the identity as
$\alpha\downarrow0$, and it vanishes on the kernel for every positive
alpha. Hence it tends to $s(\rho)$, and finite spectral continuity gives
the source endpoint trace and divergence. Theorem 3.1 and this continuity
bridge give the endpoint comparison: source literature proved or paper
derived, not formalized. The fixed-$z$ case $\kappa=0$ and unsupported
extended-value cases likewise use source results, not additional Lean
conclusions.

## Verified locator

Source page: https://arxiv.org/abs/2402.16067.
Publication DOI: 10.1007/s44146-024-00142-w.
The supplied locator is arXiv:2402.16067v3, Section 3, Theorem 3.1 and
Remark 3.2. These identifiers have not been independently compared with
the manuscript body. Literal wording, exhaustive later literature status and worldwide priority
remain unverified. The note
paraphrases the supplied mathematical statement and reproduces no proof
text from the article.
