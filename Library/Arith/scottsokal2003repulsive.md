---
bibkey: scottsokal2003repulsive
authors: "Alexander D. Scott; Alan D. Sokal"
year: 2003
title: "The repulsive lattice gas, the independent-set polynomial, and the Lovász local lemma"
doi: 10.48550/arXiv.cond-mat/0309352
url: https://arxiv.org/abs/cond-mat/0309352
claim: "For the hard-core independence polynomial, the positive component in the negative orthant characterizes simultaneous positivity on all induced vertex subsets."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# A positive ray certifies all induced subgraphs

The inspected version is [v2](https://arxiv.org/html/cond-mat/0309352v2),
dated 16 September 2004; first version 2003. Checked 16 September 2026.
Theorem 2.10(a) and (b′), with hard-core self-repulsion, identifies a
positive path from zero to a negative weight vector with positivity of
every induced-subset polynomial.

Consequently, if `Z_V(t)` is positive for all `0 <= t <= 1`, then every
`Z_U(1)` is positive. The [Erdős #7 dossier](../../Problems/erdos-7-odd-covering-systems.md)
also gives a finite deletion-recurrence argument for this specialization.
Positivity only at the endpoint is insufficient. This criterion alone does
not establish the required ray positivity for arbitrary congruence families.

## Conditional avoidance under the same source

Theorem 4.1(a), equation (4.3), of the same v2 was checked against the
original PDF on 20 September 2026. If the event-probability bounds satisfy
the theorem's conditional non-neighbor hypothesis (4.1) and lie in its
strict region R(G), then, for any event-index sets Y and Z,

    P(avoid Y | avoid Z) >= Z_G(-p 1_(Y union Z)) / Z_G(-p 1_Z) > 0.

Product-coordinate independence supplies (4.1) for events whose dependency
graph joins overlapping coordinate supports. The strict-region condition
must still be proved for the particular bounds; a positive value of the
full polynomial alone is insufficient. This ratio concerns conditional
avoidance in the same original probability space, not a resampling output
law. The [coupled first-root result](../../docs/reports/erdos7-odd-covering/problem-details/21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md)
uses it after checking the complete support-polynomial region for one
specified block and its descendant-domain bounds.

Citation and source-boundary note only; no source text or code is vendored.

## Literal laminar conflicts under actual conditioning

The same Theorem 4.1 permits any graph satisfying its lopsided hypothesis
(4.1), as its Remark 1 explicitly states. For product laws on complete
prime-power coordinates, a coordinatewise conditioning coupling preserves
all compatible literal prefix events: compatible prefixes are nested.
Thus the residue-conflict graph satisfies (4.1), even when the digits
inside a coordinate are dependent. An independent rare query coordinate
and (4.3) then give a query ratio for the actual law conditioned on
avoiding the original events. The complete argument and its strict-region
premise appear in [the laminar-prefix application](../../docs/reports/erdos7-odd-covering/problem-details/24-laminar-prefix-conflicts-under-actual-conditioning.md).
This is an application of the cited theorem; it neither identifies the
conditional law with a resampling terminal law nor supplies universal
strict feasibility for AP families. The v2 primary theorem and Remark 1
were checked on 20 September 2026.
