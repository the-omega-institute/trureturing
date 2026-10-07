---
slug: zhang-zhao-2026-domirank-entropy-monotonicity
bibkey: zhangzhao2026domirank
doi: 10.48550/arXiv.2610.00107
url: https://arxiv.org/abs/2610.00107v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.result
---

# DomiRank entropy need not decrease with competition

## Problem

Yingying Zhang and Chengye Zhao, *Theoretical Analysis of DomiRank
Centrality: Automorphism, Entropy, and Graph Transformations*,
arXiv:2610.00107v1, Section 4.1, Remark 4.6, identify the unconditional
assertion

> the DomiRank entropy of a connected non-regular graph decreases
> monotonically with σ

as an open problem. The claim quantifies over every finite connected
nonregular unweighted undirected simple graph and every pair
$0<\sigma<\tau<-1/\lambda_{\min}(A)$. It asserts
$H_G(\tau)\le H_G(\sigma)$, with the actual inverse equilibrium
$\Gamma(s)=s(I+sA)^{-1}A\mathbf1$, positive clipping, normalization,
and Shannon entropy in bits. There is no raw-positivity or extra
nonzero-normalizer premise. Conjecture 4.7 is excluded.

## Motivation

Preregistration [#13267](https://github.com/the-omega-institute/trureturing/issues/13267)
classifies this explicit single-paper question as Tier 1. The
conditional Theorem 4.5 and four numerical networks motivate the
question of removing sufficient conditions. The sole public theorem
negates the full source-faithful universal assertion.

## Gap

The qualification in #13267 found no settlement in the inspected
primary v1, target-bounded arXiv material, original DomiRank v2 paper,
companion v1/v3, OpenAlex exact record and cited-by query, or fourteen
target-specific GitHub issue/PR searches. This is bounded reported
evidence. Scholar was blocked, Semantic Scholar returned 429,
MathDB was unavailable, and only the formal-conjectures path index
was searched. Exhaustive novelty and priority are
`ASSUMED-UNVERIFIED`. The identifier/display-date mismatch is retained
without inferring chronology.

## Route

The connected graph on $\{0,1,2,3,4,5\}$ has edges
$\{0,4\},\{0,5\},\{1,2\},\{1,3\},\{1,4\},\{2,3\},\{2,4\}$
and degree vector $(2,3,3,2,3,1)$. Its spectral minimum lies in
$[-3,-1]$. The inverse equilibrium gives

$$
\Gamma(1/20)=\frac{(397,577,577,378,576,198)}{4357},
\qquad
\Gamma(1/6)=\frac{(33,45,45,28,44,16)}{129}.
$$

All coordinates are strictly between zero and one. Rational
logarithm bounds with integral remainders prove
$H_G(1/6)-H_G(1/20)>1/(500\log2)$.

Let $d=A\mathbf1$, $D=\sum_i d_i$, $w_i=d_i/D$ and
$q_i=(Ad)_i/d_i$. For every finite nonempty graph with positive
degrees, the normalized inverse extension at zero has derivative

$$
H'(0)=\frac{\sum_iw_iq_i\log d_i
 -(\sum_iw_iq_i)(\sum_iw_i\log d_i)}{\log2}.
$$

For the six-vertex graph this is $\log(27/2)/(49\log2)>0$.
Explicit derivative estimates prove strict increase for **every**
$0<a<b<\delta$, where $\delta=1/5000000$; all such points are
spectrally admissible with scores strictly between zero and one.
Zero is used only in this normalized inverse extension and is not
a source-domain point or a counterexample parameter.

For **every** natural $m>0$, form the actual connected nonregular
independent-clone graph $G_m$ on
$\operatorname{Fin}(6)\times\operatorname{Fin}(m)$. It has $6m$
vertices and spectral minimum in $[-3m,-m]$. The proof establishes
the inverse equilibrium replication and identities

$$
\Gamma_{G_m}(s)_{(i,j)}=\Gamma_G(ms)_i,
\quad P_{G_m}(s)_{(i,j)}=P_G(ms)_i/m,
\quad H_{G_m}(s)=H_G(ms)+\log(m)/\log2
$$

for $0<s<1/(3m)$. Consequently every $m>0$ has the exact pair
$1/(20m),1/(6m)$ with the same strict entropy gap, and the whole
increasing interval $0<a<b<\delta/m$, with admissible parameters
and scores strictly between zero and one.

## Falsifier

The certificate must concern the source adjacency and inverse,
the full stable spectral domain, and clipped normalized entropy.
A scalar proxy, a floating-point comparison, a witness at zero,
or a statement with an added positivity premise would fail this
target. The cubic reduced coordinate denominator in the proof is
not identified with the adjacency determinant.

## Evidence

[`DomiRankEntropyRefutation.lean`](../D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.lean)
exports the source-facing definitions `Nonregular`, `clipped`,
`normalized`, `entropyBits`, `spectralMinimum`, `graphAdj`,
`graphDegrees`, `graphGamma`, `graphEntropyBits`, `claim`, and the
sole closed theorem `result : ¬ claim`. The covariance, exact pair,
whole intervals and every-$m$ family are proof-local certificates.
The theorem consumes the family at $m=1$, transfers both exact-pair
and interval increments through its entropy identity, and contradicts
the claimed nonincrease using their sum. Its axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`.

## Triage

Tier 1; resolution **Refuted**. Admission basis is
`open-problem-resolution`, preregistration #13267. The judgement
form is `proof_shape: result: bind-only`, `escape_witness: none`:
the proof composes existing finite-graph, inverse, spectral,
calculus and logarithm results with explicit calculations and
estimates. The external open-problem resolution supplies the
admission basis. Utility is `certified-instance; basis=refutes`,
with the closed `claim` and `result`. Information-escape registration
and enrollment remain paused and unfinished.

### What the settlement shows

The failure mechanism is a positive degree-weighted covariance of
neighbor-degree ratio with log degree. Competition initially moves
normalized mass toward a more even distribution in this connected
nonregular graph. This produces a whole positive interval of entropy
increase, and independent cloning preserves that failure at every
order $6m$ after rescaling the parameter. These are one problem
settlement, not separate open-problem resolutions.

The source's conditional Theorem 4.5 is not contradicted by negating
its proposed unconditional extension; its sufficient conditions
are not proved here. The four sampled numerical networks do not
establish a universal law. The separate star-minimum Conjecture 4.7
remains outside this result. A classification of graphs or additional
conditions ensuring entropy nonincrease throughout the stable domain
is unresolved here.

## ASSUMED-UNVERIFIED

The bounded literature qualification is source-reported; exhaustive
novelty and priority are not established. The identifier/display-date
discrepancy remains unresolved. The source's conditional Theorem 4.5
and separate Conjecture 4.7 are not verified by this module.
