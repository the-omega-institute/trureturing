---
bibkey: chung2026thermodynamicobjectivity
authors: Wonyong Chung
year: 2026
title: The thermodynamic budget of objectivity
doi: null
url: https://arxiv.org/abs/2611.34909v1
claim: "Section VIII derives the independent-register writing speed limit and asks for its analogue under collective register permutations."
strata_touched:
  - D5/S3/Quantum/Information/RecordWriting/TwoRegister
  - D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation
license: citation-only
triage: anchor
---

# The thermodynamic budget of objectivity

At the zero-gap benchmark the registers start uniform and independent in
both event branches. Chung states the entropy-production–activity bound
$\Sigma A \ge R^2(1-2e_*)^2/2$ in Eq. (7) for scheduled local baths and
single-register permutations. Its parameter
$e_*=H_2^{-1}(\delta)$ is the Bayes error for a symmetric binary readout at
deficit $\delta$. The proof uses the classical bath
current bound cited there as references [57] and [58]. The closing paragraph
poses a collective extension and describes how a
three-register permutation can improve on the independent-register bound.

The repository's two-register argument uses the range of the four joint
probability masses. This range is preserved by every joint permutation.
Independent local relaxation constrains its growth through the two
single-register biases and the signed parity moment. The finite-protocol
inequality bounds the sum of marginal Bayes contrasts by the sum of the
two branch bath variations.

For a uniform event, Section II specifies objectivity through the mutual
information of each record. At fixed mean absolute bias a symmetric
readout can have less information than an asymmetric one. For two
registers, the sharp threshold for each output at mean bath variation
$t\in[0,1]$ is the binary
Jensen–Shannon information of conditional probabilities
$\min(1,1/2+t)$ and $\min(1,1/2+t)-t$. The optimizing protocol can use
the event as control for a joint swap and complement. This extends the
gate class of Eq. (7). The repository theorem concerns the finite
classical protocol. The cost in each branch is the sum of joint endpoint
total variations across local bath steps. Reversible gates carry zero charge.

## Verified locator

Source: https://arxiv.org/abs/2611.34909v1

[arXiv:2611.34909v1, Section VIII and Eq. (7)](https://arxiv.org/html/2611.34909v1#S8).
[Section II gives the mutual-information criterion](https://arxiv.org/html/2611.34909v1#S2).
