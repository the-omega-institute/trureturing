---
bibkey: flajolet2009analytic
authors: Philippe Flajolet and Robert Sedgewick
year: 2009
title: Analytic Combinatorics
doi: null
url: https://algo.inria.fr/flajolet/Publications/book.pdf
claim: Pringsheim positive-boundary obstruction for nonnegative power-series coefficients, and Cauchy cycle-count weights for permutations.
strata_touched:
  - D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit
  - D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse
license: citation-only
triage: anchor
---

<!-- GID: D5/L/flajolet2009analytic -->
# flajolet2009analytic

Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge
University Press, 2009, ISBN 978-0-521-89806-5. The retained PDF body separately
dates its electronic version June 26, 2009. This citation-only note uses the
public author PDF; PDF generation metadata is not the bibliographic basis.

Theorem IV.6 (Pringsheim's Theorem), printed p.240 / PDF p.256, states that
if a function is representable at the origin by a power series with nonnegative
coefficients and radius R, then the positive real point R is a singularity.
The immediately preceding Theorem IV.5 explicitly discusses finite radius.
Item IV.13, printed pp.240--242, supplies the continuation argument.

The formal private obstruction has a real sequence a with a(n)>=0 for every
natural n, a finite NNReal radius R>0 equal to the radius of
FormalMultilinearSeries.ofScalars Complex (fun n => (a n : Complex)), and an
analytic function g at the complex embedding of R. It assumes an epsilon>0
such that g(x) equals the original scalar sum for every real x with
R-epsilon<x<R and 0<=x, and concludes False. These are the precise local
continuation hypotheses used in the formal specialization.

Analytic continuation supplies an expansion at R-h reaching R+h. Uniqueness
identifies it with the original recentered series. Nonnegative double summation
and the multilinear finite-subset expansion imply convergence of the original
series at R+h, contradicting its radius. The original print on p.242 uses n-m
in the definition of g_m but m-n in two later displays. The formal proof derives
the finite-subset identity with Mathlib's map_add_univ and changeOriginIndexEquiv;
it does not copy either inconsistent later display as a proven identity.

The consuming public theorem is only the A006 reverse implication at the
repository's derivative-defined canonicalLiCoefficient: nonnegativity for every
n>=1 implies Mathlib RiemannHypothesis. The Li specialization and its frozen
summability-to-RH consumer are repository assembly, not a Li theorem attributed
to this textbook. The implication does not close a full equivalence atom, prove
RH-forward positivity, or prove the fixed-lambda1 A013 bound.

The source intake retained the complete author PDF (SHA256
f7bc98dfbfbc99716e19a0a0aa6f1750fb62acbf50b58d65731aabf161dccace), cover and
printed pp.239--242. This inherited source evidence is not independent proof
review. The theorem paragraph is on printed p.240 / PDF p.256; the exponent
discrepancy was separately observed in the original page image.

## Permutation cycle weights

Printed p.188 gives Cauchy's formula: a permutation with cycle multiplicities
m_k satisfying sum_k k*m_k=n has n!/product_k(k^(m_k)*m_k!) realizations.
Fixed points are included with k=1. Example III.9, printed pp.175-176,
discusses cycle expectations; Note III.15, p.180, gives related moments.
These classical formulas are background for the A398726 weighted-size limit.
The local theorem's full-partition class-size proof uses the attributed
TauCeti formulation in D5/L/tauceti2026classsizes.

Additional inspected original passages are Note II.26 (p.137), Theorem VI.13
and the distinct-cycle permutation example (p.435), the fixed-size cycle
discussion and Example IX.23 (pp.674-675), and the multivariate discussion
(pp.715-716). The number of distinct sizes, the probability of no repeated
sizes, and a fixed-size cycle law are different claims from the sum of
distinct sizes weighted by length. No complete application proving that exact
weighted limit was located in these passages. This does not assert that it
is absent from the complete book or the broader literature.

## Verified locator

- https://algo.inria.fr/flajolet/Publications/book.pdf
- Theorem IV.6, printed p.240 / PDF p.256; preceding finite-radius Theorem IV.5
  on the same page; complete proof discussion IV.13, printed pp.240--242 /
  PDF pp.256--258. Bibliographic identity is supported by the PDF cover and
  body, with the print year and electronic-version date distinguished above.
- Repository original A006 row:
  https://github.com/the-omega-institute/trureturing/blob/915a86bf19ec91fdbd690a70e75c84014d237b7d/docs/develop/theory/RH_RESEARCH_LANE_THEORY.md#L7514

- Permutation locators: Cauchy cycle-count formula, printed p.188;
  Example III.9, pp.175-176; Note III.15, p.180, in the same author PDF.
