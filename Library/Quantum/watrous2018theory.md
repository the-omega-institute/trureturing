---
bibkey: watrous2018theory
authors: John Watrous
year: 2018
title: The Theory of Quantum Information
doi: 10.1017/9781316848142
claim: Positive trace-preserving maps on finite-dimensional complex matrix spaces admit invariant density operators.
strata_touched:
  - D5/S3/Quantum/ChannelFixedState
license: citation-only
triage: anchor
---

# The Theory of Quantum Information

John Watrous's book supplies the literature anchor for fixed points of
finite-dimensional quantum channels in Section 4.4. The result represented by
`D5/S3/Quantum/ChannelFixedState.channel_fixed_state_exists` is the standard
invariant-density-operator existence statement for a positive trace-preserving
complex-linear map on a nonempty finite-dimensional matrix algebra.

The repository proof uses Cesaro averages and finite-dimensional compactness.
This note does not attribute that proof method, the pure-fixed-point premise of
Theorem 4.5, complete positivity, the tangent factor, or equivalence with an
interior faithful invariant state to the cited section.

## Search log

- 2026-08-07: The review correction identified John Watrous, *The Theory of
  Quantum Information*, Cambridge University Press (2018), DOI
  `10.1017/9781316848142`, Section 4.4, as the literature source for the
  finite-dimensional channel fixed-point setting and invariant states.
- 2026-08-07: The scope was cross-checked against the Lean declaration: the
  repository theorem assumes a complex-linear map, positivity, and trace
  preservation on matrices indexed by a finite nonempty type. It does not
  assume complete positivity.
- 2026-08-07: No specific theorem number is attributed because none was
  verified in this worktree.

## Verified locator

- DOI: https://doi.org/10.1017/9781316848142
- Cambridge University Press, Section 4.4
