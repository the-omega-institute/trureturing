---
bibkey: beiglbocknutz2014martingale
authors: Mathias Beiglböck and Marcel Nutz
year: 2014
title: Martingale inequalities and deterministic counterparts
doi: 10.1214/EJP.v19-3270
url: https://arxiv.org/abs/1401.4698v2
claim: Finite-support martingale values are iterated concave envelopes, and their increasing limit is the least fixed point majorizing the terminal payoff for an update preserving zero increments.
strata_touched:
  - D5/S3/Quantum/Recovery/FiniteLocalBellmanEnvelope
  - D5/S3/Quantum/Recovery/FiniteLocalFrontierMoment
license: citation-only
triage: anchor
---

# Finite-support Bellman envelopes

Lemma 2.2 identifies the concave envelope with the supremum of expectations
under finitely supported laws having a specified barycenter. Proposition 2.1
and Lemma 2.3 connect envelope iteration with finite-horizon martingale values.
Theorem 3.3 treats a state update preserving zero increments: the increasing
iteration limit is the least fixed point majorizing the payoff. The framework
allows extended real payoffs and does not require continuity of the limit.

The Bloch-ball construction restricts each node to one coordinate. Its
five-point representation uses Carathéodory in the three active coordinates
and one reward coordinate. Joint upper semicontinuity at finite stages follows
from compact truncated hypographs. The retained Lean proof directly constructs
finite trees and grafts finitely many continuations with a common error; it does
not use the cited paper as a kernel premise. The source-specific frontier gap
and the physical recovery interface are additional mathematical obligations.

## Verified locator

The declared DOI is https://doi.org/10.1214/EJP.v19-3270. Crossref's record for
that DOI identifies Beiglböck and Nutz, the title above, Electronic Journal of
Probability and publication year 2014. The version URL
https://arxiv.org/abs/1401.4698v2 locates the cited Lemma 2.2, Proposition 2.1,
Lemma 2.3 and Theorem 3.3; the full text is
https://arxiv.org/html/1401.4698v2. These locators support the general envelope
attribution and do not identify a theorem for the five-ray quantitative gap.

## Finite local threshold splitting

Matthias Kleinmann, Hermann Kampermann and Dagmar Bruß,
*Asymptotically perfect discrimination in the LOCC paradigm* (2011),
DOI: [10.48550/arXiv.1105.5132](https://doi.org/10.48550/arXiv.1105.5132),
provide the interpolation and recovery construction used for the complete
common-threshold cut.

Section III.1, equations (5a), (5b) and (6), constructs an interpolating local
measurement followed by recovery copies of the original branches. Section
III.2, Protocol splitting, applies this construction at the first crossing of
a prescribed regular-deviation threshold. The primary version is
[arXiv:1105.5132v2](https://arxiv.org/abs/1105.5132v2); the corresponding
[full text](https://arxiv.org/html/1105.5132v2) supplies these locators.

For a normalized product prefix effect $Q$ with defect $d>\varepsilon$, let
$E_i=w_iQ_i$ be an original local split, with $\sum_iE_i=Q$ and unchanged
inactive factor. Write $d_i=\operatorname{Tr}(P_-Q_i)$ and set

$$
\alpha_i=\frac{w_i(\varepsilon-d_i)_+}{d-\varepsilon},
\qquad
\beta=\frac1{1+\sum_i\alpha_i}.
$$

The interpolation rows are $\beta(E_i+\alpha_iQ)$. Their masses are
$\beta(w_i+\alpha_i)$ and, on positive rows, their normalized defects are
$\max(\varepsilon,d_i)$. Recovery copies have joint effects
$E_{ij}=\beta(\delta_{ij}+\alpha_i)E_j$. Each column sums to $E_j$.
Copying every complete original continuation therefore preserves each
terminal effect, endpoint and label, hence every real function of the
original terminal leaf under one common leaf map. A zero row has an identity
continuation and requires no conditional division.

At an exact-threshold row the recovery copies remain below the cut. Above
threshold, $\alpha_i=0$ and only the original child $i$ has positive mass;
recursion enters that strictly shorter original child. The complete
prefix-free cut consists of exact-threshold nodes and terminal nodes above
threshold. Each original level introduces at most two refined levels, so a
tree of depth $D$ becomes a tree of depth at most $2D$.

The source defect is a regular deviation for the two-state ensemble
$\gamma_-=P_-/4$, $\gamma_+=P_W/4$, with average state
$\gamma_-+\gamma_+=I/4$. The minus marginal depends continuously on joint
classical probabilities, is preserved by postprocessing, and is a weighted
average of its conditional marginals under staged postselection. At a
normalized product effect $Q$, its conditional value is
$\operatorname{Tr}(P_-Q)=d$. A non-identity or singular root is a product
prefix filter; child effects lie on its support, and the local
square-root/pseudoinverse realization acts there with identity completion on
the unused kernel. Zero branches carry no conditional value requirement.

The finite frontier proof uses this known construction inside its
source-specific moment and failure-defect estimate. The cited discrimination
conclusions are not recovery premises. The quantitative five-ray gap and the
forward map from actual CP protocols to the source Bellman value are separate
conclusions.
