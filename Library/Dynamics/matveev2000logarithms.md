---
bibkey: "matveev2000logarithms"
authors: "E. M. Matveev"
year: 2000
title: "An explicit lower bound for a homogeneous rational linear form in the logarithms of algebraic numbers. II"
doi: "10.1070/IM2000v064n06ABEH000314"
url: "https://www.mathnet.ru/eng/im314"
claim: "Corollary 2.3 gives an explicit lower bound for a nonzero integer linear form in fixed logarithms of algebraic numbers, with logarithmic dependence on the coefficient height."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Arithmetic isolation of a posterior score atom

The English primary paper is *Izvestiya: Mathematics* 64(6), 1217–1269.
Section 2 on printed page 1219 defines the algebraic number field degree,
absolute logarithmic heights, logarithm choices and coefficient parameter.
Corollary 2.3, equation (2.6), permits the coefficient parameter to be
replaced by the maximum absolute integer coefficient. Its nonvanishing
hypothesis is essential. The mathematical article and the metadata at the
linked Math-Net record agree on author, title and DOI.

For the positive rational algebraic numbers 2 and 3, use their real
logarithms, the field Q of degree one, and height parameters log(2) and
log(3). These exceed the corollary's 0.16 lower threshold. Prime
factorization ensures that a nontrivial integer combination of the two
logarithms is nonzero. With both coefficients bounded by H, the
corollary gives a lower bound of the form H raised to a fixed negative
power after absorbing fixed constants. Neither the theorem nor this
specialization is new; both are `literature-attested`.

[The posterior threshold volume, Chapter 38](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
uses the bound inside the proof of a model-specific result. On the
actual all-row count cutoff, the uncompensated score difference from
the central count pair is an integer combination of log(2) and log(3)
with coefficients of logarithmic size. The compensated-score
perturbation, threshold-rounding error and shrinking window are all
smaller than any fixed negative power of log(M). Thus the window
contains only the central count pair with probability tending to one.
This uses a uniform cutoff and the actual row-tail estimates in both
experiments; it is not a claim that irrationality alone controls gaps.

The mixed central-group occupancy and the calibrated posterior variance
then identify the scale sqrt(q/lambda). Classical bounded-array Gaussian
limits and the existing variance-weighted exact-center comparison give
a Gaussian amplitude. The score-window path has one whole-group jump;
a deterministic Skorokhod time change aligns its moving jump with zero.
The continuous-limit martingale theorem is not applied directly to this
jump path. Joint array convergence and overlap-covariance estimates,
followed by one full-vector posterior comparison, establish independence
from the existing coarse, threshold-field and fine-boundary limits.

The arithmetic isolation, its exact posterior transfer, and this joint
actual pair/path conclusion are `repo-derived` ordinary mathematics.
The logarithmic-form estimate, conditional Bernoulli methods, Gaussian
limit tools and Skorokhod time changes remain classical inputs. The
statement is restricted to the specified r=1/2 subsequence. It supplies
no general nonlattice tangent theorem, optimal Diophantine exponent,
useful numerical onset bound, actual moment convergence or global
originality certificate.
