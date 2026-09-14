---
bibkey: salem1953integralequation
authors: Raphaël Salem
year: 1953
title: Sur une proposition équivalente à l’hypothèse de Riemann
doi: null
url: https://gallica.bnf.fr/ark:/12148/bpt6k3188h
claim: Bounded integral-equation uniqueness, the positive logarithmic kernel, and its Mellin–Fourier connection to zeta zeros.
strata_touched:
  - D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Weil/salem1953integralequation -->
# Salem's integral equation

## Verified locator

Raphaël Salem, *Sur une proposition équivalente à l’hypothèse de Riemann*,
Comptes rendus hebdomadaires des séances de l'Académie des sciences,
volume 236 (1953), printed pages 1127–1128. The digitized volume is at
https://gallica.bnf.fr/ark:/12148/bpt6k3188h.
The supplied original-page source packet identifies both printed pages and
contains selected visual transcriptions. These transcriptions, rather than a
new inspection of the images or a complete prose transcription, were read here.

The first paragraph on page 1127 gives a necessary and sufficient condition
for no zeta zero of abscissa sigma, with 0 < sigma < 1. Its displayed equation
(1) is

\[
 \int_{-\infty}^{\infty}
 \frac{e^{-\sigma v}\varphi(v)}{e^{e^{y-v}}+1}\,dv=0.
\]

The ensuing text explicitly assumes sigma > 0. Page 1128 displays

\[
 \Gamma(s)(1-2^{1-s})\zeta(s)
 =\int_0^\infty\frac{t^{s-1}}{e^t+1}\,dt
 =\int_{\mathbb R}\frac{e^{\sigma u}}{e^{e^u}+1}e^{i\gamma u}\,du,
 \qquad s=\sigma+i\gamma.
\]

It names the kernel K_sigma(u) = exp(sigma u)/(exp(exp u)+1), calls it
summable on the real line, and invokes Wiener's theorem in the following
convolution paragraph. The source's selected bounded-solution clauses do not
explicitly name a real or complex codomain, a measure, measurability, or
almost-everywhere equality. Those modern conventions must be made explicit
when stating the formal theorem; they are not quoted as printed words of Salem.

## The positive-half-line formulation

The original A069 atlas clause, at
https://github.com/the-omega-institute/trureturing/blob/915a86bf19ec91fdbd690a70e75c84014d237b7d/docs/develop/theory/RH_RESEARCH_LANE_THEORY.md#L8094,
uses every delta in (1/2,1), every bounded measurable complex function on the
positive half-line, and the equation

\[
 I_{\delta,f}(x)=\int_0^\infty
       \frac{t^{\delta-1}f(t)}{e^{xt}+1}\,dt=0\qquad(x>0).
\]

Here powers of positive real t are real powers, then included in the complex
numbers. Uniqueness means f = 0 almost everywhere for Lebesgue measure.
The conjunction over all these delta is equivalent to the standard Riemann
hypothesis. Values of f outside the positive half-line are immaterial.

Set mu = volume restricted to (0,infinity). The formal hypothesis
NullMeasurable f mu is exactly measurability on the completed sigma algebra
NullMeasurableSpace. Its completed measure has the same value on every set
and exactly the same almost-everywhere filter as mu. Since the complex
numbers are separable, this hypothesis is equivalent to
AEStronglyMeasurable f mu. Trimming the completed measure back to the Borel
sigma algebra gives mu; the Bochner integral trim theorem then identifies
the two integrals for each such integrand. Thus arbitrary completed-measurable
representatives are allowed without a Borel measurability hypothesis.

The maps v -> exp(-v) and t -> -log(t) preserve null sets in the respective
directions. This follows from differentiability of the inverse maps on their
domains and the theorem that a differentiable map sends a Lebesgue-null set
to a null set. Positivity supplies the exp/log inverse identities. It follows
that g(v) = f(exp(-v)) is almost-everywhere strongly measurable and that
AE vanishing of g is equivalent to AE vanishing of f on (0,infinity).

## Declaration correspondence and proof

The definition **salemKernel** is Salem's page-1128 kernel included in the
complex numbers. The theorem **salem_integral_eq_convolution** gives

\[
 I_{\delta,f}(e^y)=e^{-\delta y}
       \int_{\mathbb R}K_\delta(u)f(e^{u-y})\,du.
\]

This change-of-variables identity holds even for totalized integrals and is
not, by itself, a convergence assertion. Its proof applies the existing
MellinDilationFlow positive-logarithmic identity and translation invariance.
For delta > 0 and bounded completed-measurable f, both sides are genuinely
integrable: FermiMellin supplies positive-scale Mellin integrability;
bounded multiplication controls the original integrand; the exponential
Jacobian integrability equivalence and bounded multiplication control the
convolution. A private convergent transport also identifies the original
integral on the completed measure.

For **salem_bounded_measurable_uniqueness_iff_rh**, the forward implication
uses the Fourier convention exp(-2 pi i u xi), so

\[
 \widehat K_\delta(\xi)=M(\delta,-2\pi\xi),\qquad
 M(\delta,\gamma)=\int_0^\infty
       \frac{t^{\delta-1+i\gamma}}{e^t+1}\,dt.
\]

The existing FermiMellin criterion makes this transform nowhere zero under
RH. Its product formula Gamma(s)(1-2^(1-s))zeta(s) is holomorphic in
0 < Re(s) < 1. Restricting scalars to the reals and composing with
s = delta - 2 pi i xi gives the smoothness needed by the existing
SmoothConvolutionUniqueness theorem. Applying it to g and transporting the
AE conclusion proves original-domain uniqueness.

Conversely, a Mellin zero at delta + i gamma gives the actual function
f_gamma(t) = exp(i gamma log t). It is measurable and has norm one; the
interval (1,2] has positive measure, so this function cannot vanish almost
everywhere. Its integrals are genuinely integrable. Positive Mellin scaling
multiplies the zero at scale one by x^(-delta-i gamma), hence its original
integral is zero for every x > 0. Uniqueness rules out every such zero, and
the existing FermiMellin equivalence gives RH.

## Implementation sources

These are applications of existing repository declarations, not transplants
of the original article's proof. FermiMellin's convergence/product proof and
its source adaptations are attributed separately in
[the Fermi Mellin note](sanftenberg2026fermi.md).
The generic convolution cancellation theorem and its classical
Wiener-density interpretation are documented in
[the Wiener note](../Fourier/fulsche2025wiener.md).
That note uses Fulsche–Luef–Werner, arXiv:2405.08678v2, Theorem 2.1,
printed page 3, with the group/Fourier/duality conventions on pages 2–4.
The source's angular frequency is 2 pi xi; its density theorem does not
require the extra smoothness used by the repository's cancellation proof.
The original Wiener 1932 body and the published JFA version were not read.
Salem attribution, this modern statement interpretation, and these Lean
implementation sources therefore have distinct scopes.
