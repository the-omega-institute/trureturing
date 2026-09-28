---
bibkey: watrous2018theory
authors: John Watrous
year: 2018
title: The Theory of Quantum Information
doi: 10.1017/9781316848142
claim: Finite-dimensional quantum channels admit complete Kraus and isometric Stinespring representations; positive trace-preserving maps admit invariant density operators.
strata_touched:
  - D5/S3/Quantum/ChannelFixedState
  - D5/S3/Quantum/Entanglement/FiniteSectorChannelOptimality
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

## Complete channel representations

The author-hosted pre-publication copy at
https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf gives the following precise
locators. Page numbers are printed pages, followed by one-based PDF pages.

- Theorem 2.22, pp. 82-83 (PDF 90-91): complete positivity is equivalent
  to positive Choi representation, a Kraus representation with identical
  left and right operators, and a Stinespring representation with identical
  left and right dilation operators. The proof applies complete positivity
  to the unnormalized maximally entangled operator and factors the resulting
  positive Choi operator spectrally.
- Theorem 2.26, pp. 87-89 (PDF 95-97): trace preservation is equivalent
  to completeness of every Kraus representation and to the identity
  A* B = I for every Stinespring representation.
- Corollary 2.27, p. 89 (PDF 97), equations (2.129)-(2.130): a quantum
  channel admits a complete Kraus family and an isometric Stinespring
  dilation, each representing its action on every input operator.

The proof of `FiniteSectorChannelOptimality.result` applies this
finite-dimensional representation theorem internally in the canonical
matrix channel interface. Its Kraus/environment index has cardinality
equal to the product of input and output dimensions; zero Kraus operators
pad the spectral representation. They do not assert that this is the
minimal Choi-rank environment. The internal representation also includes empty
coordinate types; those cases follow from the empty matrix identities,
and are not attributed to the book's nonzero-map statement in Theorem 2.22.

The finite representation theorem alone does not establish the optimum over
local channels in the spectral coarse-graining problem, or its stabilized
trace-norm error formula.
