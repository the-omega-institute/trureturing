---
bibkey: "ferger2015empirical"
authors: "Dietmar Ferger; Daniel Vogel"
year: 2015
title: "Weak convergence of the empirical process and the rescaled empirical distribution function in the Skorokhod product space"
doi: null
url: "https://arxiv.org/abs/1506.04324v1"
claim: "Theorem 2.1 gives independent limits for the global empirical process and a locally rescaled empirical distribution: a time-transformed Brownian bridge and a two-sided Poisson process."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Global and local empirical limits

The checked primary version is arXiv:1506.04324v1, submitted 2015-06-13;
its title page is dated 2015-06-16 and the PDF has 22 pages.

For iid observations with a fixed distribution function F, the paper considers
the global empirical process scaled by the square root of sample size and the
empirical mass in neighborhoods of width inverse sample size around a fixed
point. The local process uses the left limit of F on the negative half-axis.
Condition C.1, printed page 5, assumes the corresponding finite one-sided
derivatives at that point; it permits a jump at the point.

Theorem 2.1, printed page 6, proves joint convergence in the product of two
Skorokhod spaces. The limits are a Brownian bridge composed with F and a
two-sided Poisson process whose rates are the one-sided derivatives. These
limits are independent even though both statistics are computed from the same
empirical distribution. This is `literature-attested` precedent for global/local
asymptotic independence, not a new general principle of the parity model.

The theorem's local scale has a finite limiting expected count. The parity
output-budget calculation instead has a growing expected count of order
q/sqrt(lambda), a changing signal distribution, possibly moving lattice phases,
and actual dependent observations before a marked-count comparison. The source
does not provide the calibrated compensated-score clock, the fixed-size
posterior comparison, or exact minimax centering. Those hypotheses and transfers
must be established within that model; a common “local process” description
does not make the theorem directly applicable.

## A uniform empirical bridge as an auxiliary marginal

The global marginal of Theorem 2.1, with a fixed uniform distribution, supplies
the classical uniform empirical-process Brownian bridge. This marginal is enough
for a direct rare-count decomposition: conditional on the total number of rare
entries, their entry parameters are iid with a normalized distribution function.
A uniform inverse-distribution representation expresses their process as the
uniform empirical bridge composed with that distribution function. An independent
binomial total-count fluctuation supplies the remaining normal component.

The present functional budget proof separately establishes uniform convergence
of the changing normalized distribution functions to a continuous clock, a
random-sample-size conditioning argument, and the actual-experiment transfer.
It does not apply the source's local Poisson limit to a regime with diverging
local expected count. The arithmetic clock may have corners; continuity is the
property needed for the composition step.
