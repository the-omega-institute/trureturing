---
bibkey: "ottolini2020oscillations"
authors: "Andrea Ottolini"
year: 2020
title: "Oscillations for order statistics of some discrete processes"
doi: "10.1017/jpr.2020.25"
url: "https://arxiv.org/abs/2010.09071v1"
claim: "Discrete maxima can have oscillating asymptotic distributions, and ties affect their upper order statistics; the paper studies independent variables and specified allocation models."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Oscillations for order statistics of some discrete processes

The inspected primary text is arXiv:2010.09071v1, dated 18 October 2020,
16 pages. The journal article appears in *Journal of Applied Probability*
57(3), 703–719 (2020), with the DOI above. Manuscript page numbers below
refer to that pinned version.

Theorem 1.1, p. 2, studies the maximum of independent identically distributed
discrete variables with an unbounded upper support. Its hypothesis is the
existence of a limiting successive upper-tail ratio in the closed unit
interval. The three displayed cases distinguish zero, strictly intermediate,
and unit limiting ratios. Remark 1.2 interprets the first case through
oscillating probabilities and subsequences. Theorem 1.3, pp. 2–3, addresses
ties under the zero-tail-ratio hypothesis; it is not a general theorem for
all discrete laws or all triangular arrays.

The allocation results in Theorems 1.5–1.7, p. 4, concern uniform multinomial
allocations and symmetric Dirichlet mixtures under their stated fixed-ratio
conditions. Equations (1.4)–(1.5), pp. 3–4, explain the conditional
representation and probability ratio used to transfer extreme events from
independent variables. This is a specific conditioning argument, not an
assertion that dependence can always be removed by Poissonization.

Discrete extreme oscillations and the need to account for ties are
`literature-attested`. In the arithmetic extension of
[PARITY_HIDDEN_ARROW](../../docs/develop/theory/PARITY_HIDDEN_ARROW.md),
there are two row classes with different compound-Poisson laws, the Poisson
time increases logarithmically, and the observed rows come from compensated
stationary pairs or paths. The proof uses that model's exact likelihood and
fixed-number row comparison, followed by a posterior average over the
observed boundary bin. No theorem from this paper is used to replace those
steps. In particular, its zero-tail-ratio tie theorem does not give the
reciprocal-binomial boundary factor or the two-class critical series.

The parity model's analytic phase-dependent exponential rate, and its
resulting nonconvergence of exact minimax risk along integer dimensions,
are repository-derived consequences of that critical series. The bounded
source search found no theorem here stating those conclusions. This is a
source-scope comparison, not a global originality claim.

The manuscript cites C. W. Anderson's 1970 paper, *Extreme value theory for
a class of discrete distributions with applications to some stochastic
processes*, DOI `10.2307/3212152`, as prior work on discrete extremes. Its
original full text was not inspected for this note; the primary source
actually read is Ottolini's pinned manuscript.
