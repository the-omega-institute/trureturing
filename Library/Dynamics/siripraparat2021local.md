---
bibkey: "siripraparat2021local"
authors: "Tatpon Siripraparat; Kritsana Neammanee"
year: 2021
title: "A local limit theorem for Poisson binomial random variables"
doi: "10.2306/scienceasia1513-1874.2021.006"
url: "https://www.scienceasia.org/2021.47.n1/scias47_111.pdf"
claim: "Theorem 2 bounds the uniform point-probability error for a heterogeneous independent Bernoulli sum by an explicit quantity of order inverse total variance."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Local Bernoulli probabilities and a growing posterior interval

Published in *ScienceAsia* 47 (2021), 111–116. The checked primary publisher
PDF has six pages. The introduction on printed page 111 defines the uniform
point-probability error against the normal density divided by its standard
deviation. Theorem 2 on printed page 112 applies to independent Bernoulli
variables with heterogeneous parameters and total variance greater than one.
Its explicit bound is of order inverse total variance as that variance grows.
It requires neither identical parameters nor uniform separation from zero
and one. This local bound is `literature-attested`; an ordinary distribution-
function Berry–Esseen bound alone does not supply the needed relative central
point probabilities.

[The parity fluctuation volume, Chapter 32](../../docs/develop/theory/PARITY_HIDDEN_ARROW_FLUCTUATIONS.md)
uses this result for a calibrated independent Bernoulli representation of the
fixed-size posterior, whose total mean equals the support size exactly.
It applies the theorem to both the full auxiliary array and the complement
of the data-selected rank interval. The resulting ratio is integrated under
the interval's product law. This controls its full posterior label vector in
total variation, then its exact conditional mean at the smaller fluctuation
scale. The source's independent Bernoulli variables are auxiliary posterior
variables; they are not the actual dependent observations.

The local theorem does not itself establish the actual rank interval's size,
its confinement to adjacent lattice layers, the calibrated posterior variance,
or its coupling to the coarse loss coordinate. Those steps and their joint
mixed-normal conclusion in the stationary pair/path experiment are
`repo-derived` ordinary mathematics. Generic conditioning approximations and
Gaussian variance mixtures are classical mechanisms, not new general theories.
The posterior conditional statement is under the uniform support prior;
permutation equivariance transfers the unconditional joint law to every fixed
support. No conditional random-label claim is made with the true support fixed.

The total-variation estimate uses an interval carrying a vanishing fraction of
total auxiliary variance. A fixed positive fraction retains a finite-population
variance correction. The result therefore does not claim that conditioning can
be removed from arbitrary large subsets, nor that all posterior coordinates
are jointly independent. It also does not assert convergence of actual fourth
moments or make a global originality claim.
