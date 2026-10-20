---
bibkey: aaronson2005postselection
authors: Scott Aaronson
year: 2005
title: Quantum Computing, Postselection, and Probabilistic Polynomial-Time
doi: null
url: https://arxiv.org/abs/quant-ph/0412187
claim: Uniform polynomial quantum computation with postselection on a nonzero-probability measurement event has complexity class PostBQP equal to PP.
strata_touched: []
license: citation-only
triage: anchor
---

# Conditional successful states carry a computational permission

Primary source: https://arxiv.org/pdf/quant-ph/0412187. Definition 1
specifies PostBQP and Theorem 4 proves PostBQP = PP. The postselection
event must have positive probability on every input; the acceptance
conditions concern the second output conditional on that event.

A formula $\varphi$ with $m$ variables defines the diagonal projector

$$
\Pi_\varphi=\sum_{\varphi(w)=1}|w\rangle\langle w|.
$$

Applying it to the uniform superposition has success probability
$M/2^m$, where $M$ is the number of satisfying assignments. When $M>0$,
the normalized successful state is the uniform superposition over those
assignments. Direct repeated preparation needs expected $2^m/M$
attempts. The normalization is a conditional state description, not a
deterministic trace-preserving operation available at unit cost.

When $M=0$ this success event has probability zero, so conditioning on
this event alone does not even define a legal all-input PostBQP algorithm.
The equality with PP concerns algorithms satisfying the complete
postselection definition, rather than this unmodified filtering proposal.

The SAT clause projectors commute because they share the computational
basis. For arbitrary quantum projections, sequential success need not
mean simultaneous constraint satisfaction. For instance, the ranges of
$|0\rangle\langle0|$ and $|+\rangle\langle+|$ have zero intersection,
but applying these projections in that order to $|0\rangle$ succeeds
with probability $1/2$. Any completion interpretation must preserve
the actual order and the appropriate common constraint semantics.

This note concerns postselection as a computational resource. It does
not turn static existence of a successful history, environmental
purification, or ordinary bounded-error quantum computation into that
resource.
