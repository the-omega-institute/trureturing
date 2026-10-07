---
bibkey: houghnielsen2017restricted
authors: "Robert D. Hough; Pace P. Nielsen"
year: 2017
title: "Covering systems with restricted divisibility"
doi: 10.48550/arXiv.1703.02133
url: https://arxiv.org/html/1703.02133v2
claim: "The clique Shearer theorem bounds conditional avoidance probabilities by ratios of the clique partition function when all coordinate-subset values are strictly positive."
strata_touched:
  - D5/S3/Combinatorics/Probability/FiniteCliqueAvoidance
license: citation-only
triage: anchor
---

# Finite clique avoidance and conditional queries

Appendix C, Theorem 16 of version 2, dated 8 August 2018, is the
Clique Shearer Theorem. Event vertices have nonempty clique footprints;
intersecting footprints give the dependency edges. For a coordinate
subset S, let Z(S) be the probability of avoiding every event whose
footprint is contained in S. The theorem assumes that the corresponding
clique partition function rho(S) is strictly positive for every S.
It then gives, for S contained in T,

    Z(T) / Z(S) >= rho(T) / rho(S).

The deletion induction uses independence of an event from the joint
avoidance of events with disjoint footprints. Pairwise independence is
insufficient. Positivity of only the full-set partition function is
also insufficient.

## Finite rational formulation

The finite formulation uses one rational probability law and actual
events indexed by nonempty coordinate subsets. The polynomial is
specified by its empty-set value and its coordinate-deletion identity:

    rho(empty) = 1,
    rho(insert p R) = rho(R)
      - sum_(U subset R) t(insert p U) rho(R minus U), p notin R.

Nonnegative activities t bound the actual event probabilities. The
same induction in the cited proof permits these upper activities:
each activity multiplies a nonnegative avoidance ratio in a subtracted
term. No artificial event realization of the upper bounds is needed.
Absent events can be represented by the empty event with activity zero.

For a query E supported on coordinates Q, its independence from the
joint avoidance on the complement of Q gives, under the single law
conditioned on full avoidance,

    P(E | full avoidance) <= P(E) rho(P minus Q) / rho(P).

The query conclusion follows by dropping bad events that touch Q and
using the relative-avoidance inequality. It concerns the actual
conditional law, not an independently selected query law or a
resampling output distribution.

The finite theorem does not establish a particular congruence family's
activity bounds, polynomial positivity, CRT realization, or infinite
sum over query heights. Those are separate application obligations.
This is a formalization of the cited argument, not an originality claim.
No source text or implementation is vendored.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1703.02133
- Version inspected: https://arxiv.org/html/1703.02133v2
- Location: Appendix C, Theorem 16 (Clique Shearer Theorem), its proof,
  and the following Shearer-type theorem.
