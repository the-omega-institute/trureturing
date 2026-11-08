---
bibkey: blackwelldubins1962merging
authors: David Blackwell and Lester Dubins
year: 1962
title: Merging of Opinions with Increasing Information
doi: 10.1214/aoms/1177704456
url: https://doi.org/10.1214/aoms/1177704456
claim: The Main Theorem gives infinite-future predictive merging under absolute continuity; Theorem 2 gives joint almost-everywhere and L1 conditional dominated convergence along monotone sigma-algebras.
strata_touched:
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/JointConditionalDominatedConvergence
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/JointDominatedConvergence
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PredictiveMerging/BlackwellDubins
license: reference-only
triage: anchor
---

# Predictive merging and joint conditional dominated convergence

David Blackwell and Lester Dubins, *Merging of Opinions with Increasing
Information*, The Annals of Mathematical Statistics 33(3), 882–886.
The principal locators are the Main Theorem and Theorem 2 on page 883.

The Main Theorem concerns a product of arbitrary measurable coordinate spaces.
A predictive probability P supplies a conditional law of the entire future
given each finite past. If Q is absolutely continuous with respect to P, then
for every chosen sequence of these conditional P laws there exists a sequence
of conditional Q laws on the same past and future spaces for which the
measurable-event total-variation distance tends to zero along Q-almost every
full history. The predictive definition is on page 882; the Main Theorem is on
page 883; the normalized-density argument and uniform event estimate are on
pages 884–885, including equations (13)–(14). The event distance on page 883 is
the supremum over measurable events, or one half of the full variation norm.

The corresponding product-coordinate construction totalizes the finite real
Radon–Nikodym representative and normalizes each chosen predictive row.
Rows of zero or infinite mass retain the original probability row. Fubini
and the genuine composition-product law identify the new predictive law;
only almost-everywhere statements discard exceptional rows. The bounded
minimum of the density and its prefix conditional mean is dominated by the
single integrable density. Theorem 2 and its diagonal give convergence of
the conditional overlap numerator. The individual-law common-part identity
then gives convergence of the supremum over the entire future event field.
Only countably many time-indexed exceptional sets are combined. No standard
Borel or countable-generation hypothesis, supplied normalization, supplied
likelihood convergence or supplied merging estimate is used.

For real random variables yₙ converging almost everywhere to y, Theorem 2
assumes that the countable supremum of |yₙ| has finite expectation. For a
monotone increasing or monotone decreasing sequence of sigma-algebras
converging to a sigma-algebra M, it concludes that the actual conditional
expectations of yₙ given the jth field converge to the conditional expectation
of y given M, jointly in n and j, almost everywhere and in L1. The text
explicitly distinguishes this joint conclusion from the weaker diagonal.

The corresponding formal results cover both monotone directions on arbitrary
probability spaces. Their hypotheses give an integrable real envelope g with
|yₙ| ≤ g almost everywhere for each n. Countability puts all these inequalities
on one full-measure set. There the nonnegative supremum of |yₙ| is finite and
at most |g|; its expectation is therefore finite. This direction connects the
formal hypotheses to the paper. A reverse equivalence is not used.

Both proofs use decreasing measurable tail suprema of the absolute input
error, conditional order and positivity, preservation of integrals, upward
or downward conditional-expectation convergence, and a rectangular epsilon
argument on one common full-measure set. The L1 conclusion follows from the
uniform conditional-expectation contraction estimate and fixed-integrand
L1 convergence along the corresponding monotone family. The conditional-expectation, upward-convergence
and dominated-convergence ingredients come from the pinned mathematical
library. The fixed-input downward construction is an attributed source port
described in [the downward source note](tauceti2026levydownward.md). The
decreasing result uses the raw infimum of the ambient sub-sigma-algebras;
the increasing result uses their supremum. Each joint composition is proved
in its corresponding source, sharing the original scalar tail-control lemma.

Neither adapted inputs nor measurability of the limit with respect to M is
required for the two conditional dominated-convergence results. The
predictive-merging result separately supplies the conditional-law and
normalized-overlap bridges described above.
No literature novelty is claimed. The note cites mathematics only and
reproduces no external implementation or paper text.

## Verified locator

DOI: 10.1214/aoms/1177704456

DOI URL: https://doi.org/10.1214/aoms/1177704456

Verified original full text: http://www.dklevine.com/archive/refs4565.pdf.
The predictive definition is on page 882; the Main Theorem and Theorem 2,
equation (2), are on page 883; the predictive density argument and equations
(13)–(14) are on pages 884–885. Theorem 2 includes the joint almost-everywhere
and L1 conclusions. These locators are verified against this original-paper
copy; the DOI and its URL identify the publication.
