---
bibkey: fulsche2025wiener
authors: Robert Fulsche, Franz Luef, Reinhard F. Werner
year: 2025
title: "Wiener's Tauberian theorem in classical and quantum harmonic analysis"
doi: null
url: https://arxiv.org/abs/2405.08678v2
claim: "Wiener's approximation theorem: translates of S in L1(G) span a dense subspace exactly when the Fourier zero sets have empty intersection; bounded convolution cancellation on the real line is a duality corollary."
strata_touched:
  - D5/S3/Fourier/SmoothConvolutionUniqueness
license: citation-only
triage: anchor
---

# Wiener's approximation theorem and bounded convolution cancellation

## Verified locator

- Versioned source: https://arxiv.org/abs/2405.08678v2
- Research-author preprint, arXiv:2405.08678v2, Theorem 2.1
  (Wiener's approximation theorem), printed page 3, Section 2:
  https://arxiv.org/html/2405.08678v2#S2.Thmthm1a
- PDF: https://arxiv.org/pdf/2405.08678v2
- Group, Haar measure, Euclidean example and Fourier convention: Section 2,
  printed pages 2-3, HTML S2.p1, S2.Thmthm1 and S2.p2. Translation and
  reflection: page 3, S2.p5. Complex dual pairing and L-infinity conventions:
  Section 2.1, page 4, S2.SS1.p1 and S2.SS1.p2.
- Verification used the captured versioned HTML clauses and PDF page extracts
  in the supplied source packet; no fresh source retrieval was performed.
  The arXiv revision timestamp is September 14, 2025, 16:15:37 UTC;
  the PDF title-page date is September 16, 2025. These are distinct facts.

## Source theorem

Theorem 2.1 states that, for a subset S of L1(G), translates of functions in S
span a dense subspace of L1(G) if and only if the intersection of their Fourier
zero sets in the dual group is empty. The standing group is locally compact,
abelian and Hausdorff, with a choice of Haar measure. The Euclidean example
uses Lebesgue measure and characters x -> exp(i x eta), with Fourier transform
given by integration against the conjugate character. A singleton is regular
exactly when its Fourier transform vanishes nowhere (page 3, S2.p3).

Theorems 2.2 and 2.3 on page 3 give Tauberian consequences concerning limits
and closed translation-invariant subspaces, respectively. No separate numbered
zero-convolution cancellation theorem is attributed to this source here.

## Specialized corollary and correspondence

The real additive group is second-countable and locally compact abelian;
Lebesgue volume is its Haar measure. Let k and g be complex-valued functions
on the real line, with k integrable. Assume g is almost-everywhere strongly
measurable and there exists a real M >= 0 bounding |g(y)| for every real y.
Assume the Fourier transform of k is nowhere zero and
integral k(u) g(y-u) du = 0 for every real y.

An almost-everywhere strongly measurable complex function has a Borel
measurable representative equal to it almost everywhere. The pointwise bound
implies an essential bound, so this representative defines an L-infinity
class. The second-countable duality convention on page 4 identifies that space
with the complex-linear dual of L1 by the bilinear pairing integral h(u) f(u)
du, without conjugation of either function.

Use the reflected representative to define Lambda(h) = integral h(u) g(-u)
du. This is a continuous complex-linear functional with
|Lambda(h)| <= M ||h||_1. With the source translation alpha_x k(u) = k(u-x),
the change of variable v = u-x gives
Lambda(alpha_x k) = integral k(v) g(-x-v) dv = 0.
Theorem 2.1 applied to S = {k} makes the translate span dense, hence Lambda
vanishes on L1. Injectivity of the stated dual identification implies that
g(-u) is zero almost everywhere. Reflection preserves Lebesgue measure, so
g itself is zero almost everywhere.

Replacing a representative on a null set leaves each convolution integral
unchanged: for each fixed y, the map u -> y-u preserves null sets. This
argument does not require a common exceptional set for all real y.
All the integrals above exist by the L1 bound times M.

The pinned Fourier convention is FT(k)(xi) = integral exp(-2 pi i u xi) k(u)
du. The source's angular frequency eta equals 2 pi xi. This bijection of real
frequencies preserves nowhere-vanishing, so the normalization changes no
hypothesis of the density argument.

The public declaration
D5/S3/Fourier/SmoothConvolutionUniqueness.ae_eq_zero_of_smooth_fourier_convolution_eq_zero
also assumes the Fourier transform of k is infinitely differentiable over
the reals. This is an additional restriction of the specialized corollary;
Theorem 2.1 does not need it. The paper does not print this exact Lean
signature or its proof. No integrability, continuity, Fourier transform,
support restriction or reciprocal-growth condition on g is added.

## Proof exposition and attribution limits

The specialized proof divides compact smooth frequency tests by the smooth
nowhere-zero Fourier transform of k, takes inverse Fourier transforms, and
uses an L1/L1/bounded Fubini estimate. Compact frequency tests approximate
compact smooth spatial tests in L1; the bounded reflected pairing passes to
the limit, and test-function separation yields the almost-everywhere result.
This proof description is separate from the source's density/duality
formulation. Classical theorem priority remains Wiener's.

The preprint's reference [27], printed page 29, cites N. Wiener, Tauberian
theorems, Annals of Mathematics (2) 33 (1932), pages 1-100. The original 1932
body was not captured, so no original theorem number or statement page is
asserted. The matching journal metadata lists DOI 10.1016/j.jfa.2025.111265,
Journal of Functional Analysis 290(4), article 111265, cover date February 15,
2026. Its body was not read; the preprint's theorem and page locators are not
transferred to that edition. This note contains citation and paraphrase only.

Salem's 1953 pages 1127-1128 historically invoke Wiener in a particular
kernel problem. They are not the attribution for this generic theorem.
The positive-halfline kernel, logarithmic transport and both implications
of the Riemann-hypothesis equivalence are separate mathematical obligations.
