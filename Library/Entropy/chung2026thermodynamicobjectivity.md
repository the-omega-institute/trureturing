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
  - D5/S3/Quantum/Information/RecordWriting/LocalBathWeakRecording
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

The finite local-bath bound for an arbitrary binary cube allows joint
permutations chosen by the event. Each bath step uses common two-state
rates over the spectator configurations. For $R$ designated bits, each
with decoding error at most $(1-m)/2$, let $C$ be the product of the
branch-averaged transition activity and certified edge charge. Define
$q=2^N\sqrt{2C}$ for $N$ total registers. The finite protocol satisfies
$C\ge (Rm^2/2)(1-q)/(1+q)$. The local current bound and orthogonality
of the coordinate signs yield a lower coefficient of $R/2$ as
$m\to0$ at fixed $N$. The general sharp collective cost remains open.

The finite theorem assumes $2j_e^2\le a_e\sigma_e$ with nonnegative
edge charge $\sigma_e$. For matched flux support, the source proves
this using the logarithmic charge $j_e\log(f_e/g_e)$, evaluated at the
input law of the step. This is the discrete time-reversed entropy
production of Lee, Lee and Park. It equals time-backward entropy
production plus $D(p_{\mathrm{out}}\Vert p_{\mathrm{in}})$ for a
finite step. Activity in the finite model is the expected number of
transitions in that step. Chung's continuous-time accounting integrates
the entropy-production rate and counts microscopic bath jumps.
[Lee, Lee and Park, Sec. II](https://arxiv.org/html/2406.17966v2#S2).

## Verified locator

Source: https://arxiv.org/abs/2611.34909v1

[arXiv:2611.34909v1, Section VIII and Eq. (7)](https://arxiv.org/html/2611.34909v1#S8).
[Section II gives the mutual-information criterion](https://arxiv.org/html/2611.34909v1#S2).
