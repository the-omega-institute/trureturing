---
bibkey: blackwelldubins1962merging
authors: David Blackwell and Lester Dubins
year: 1962
title: Merging of Opinions with Increasing Information
doi: 10.1214/aoms/1177704456
url: https://doi.org/10.1214/aoms/1177704456
claim: Theorem 2 gives joint almost-everywhere and L1 conditional dominated convergence along monotone sigma-algebras.
strata_touched:
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/JointConditionalDominatedConvergence
license: reference-only
triage: anchor
---

# Joint conditional dominated convergence

David Blackwell and Lester Dubins, *Merging of Opinions with Increasing
Information*, The Annals of Mathematical Statistics 33(3), 882–886.
The primary locator is Theorem 2, page 883, equation (2).

For real random variables yₙ converging almost everywhere to y, the theorem
assumes that the countable supremum of |yₙ| has finite expectation. For a
monotone increasing or monotone decreasing sequence of sigma-algebras
converging to a sigma-algebra M, it concludes that the actual conditional
expectations of yₙ given the jth field converge to the conditional expectation
of y given M, jointly in n and j, almost everywhere and in L1. The text
explicitly distinguishes this joint conclusion from the weaker diagonal.

The corresponding formal result covers the increasing case on arbitrary
probability spaces. Its hypotheses give an integrable real envelope g with
|yₙ| ≤ g almost everywhere for each n. Countability puts all these inequalities
on one full-measure set. There the nonnegative supremum of |yₙ| is finite and
at most |g|; its expectation is therefore finite. This direction connects the
formal hypotheses to the paper. A reverse equivalence is not used.

The proof uses decreasing measurable tail suprema of the absolute input
error, conditional order and positivity, preservation of integrals, upward
conditional-expectation convergence, and a rectangular epsilon argument on
one common full-measure set. The L1 conclusion follows from the uniform
conditional-expectation contraction estimate and fixed-integrand upward L1
convergence. The conditional-expectation, upward-convergence and dominated-
convergence ingredients come from the pinned mathematical library; the
joint composition is proved in the corresponding source.

Neither adapted inputs nor measurability of the limit with respect to M is
required. Decreasing fields and the further conditional-law bridges needed
for the paper's predictive-merging theorem are outside this formal result.
No literature novelty is claimed. The note cites mathematics only and
reproduces no external implementation or paper text.

## Verified locator

DOI: 10.1214/aoms/1177704456

DOI URL: https://doi.org/10.1214/aoms/1177704456

Verified original full text: http://www.dklevine.com/archive/refs4565.pdf,
Theorem 2, page 883, equation (2), including the joint almost-everywhere and
L1 conclusions. The theorem locator is verified against this original-paper
copy; the DOI and its URL identify the publication.
