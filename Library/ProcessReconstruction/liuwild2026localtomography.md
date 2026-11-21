---
bibkey: liuwild2026localtomography
authors: Zidu Liu and Dominik S. Wild
year: 2026
title: "Efficiently Learning Global Quantum Channels with Local Tomography"
doi: 10.1103/51mt-ghpn
url: https://arxiv.org/abs/2603.07037v1
claim: "Exponential decay of Choi conditional mutual information gives a local-to-global guarantee in Choi trace norm. The conclusion asks for tight diamond norm bounds using a similar approach."
strata_touched:
  - D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction
license: citation-only
triage: anchor
---

# Choi conditional mutual information and diamond reconstruction

Equation (3) and Definition 1 group each input reference with the corresponding output.
The exponential upper bound is uniform in the regions, with a decay
length determined by the number of middle sites. Theorem 1 controls
trace norm error for the normalized Choi state.

For every register of at least two qubits, the formal obstruction gives
two unital channels of Kraus rank two with identical data on all proper
paired windows. The trace norm of the difference of their normalized Choi states is
4/2ⁿ and their unhalved diamond distance is 2. For either channel,
the Choi conditional mutual information is bounded by
24 exp(−(log 2)|M|/2), where M is the middle region. The bound holds
in nats with the same constants at every register size. Thus any
estimate determined by those marginals has diamond error at least 1
for at least one of the two channels.

Section V already notes that system-spanning GHZ-type coherences
can escape every proper local marginal. This construction realizes the
obstruction for unital rank-two channels with a uniform CMI bound and
maximal diamond separation. The estimator result concerns exact proper
paired-window data. A guarantee on a smaller channel class or a reconstruction
using additional probes requires its own hypotheses. Appendix D treats
a bound with a dimension factor and the separate Pauli-channel case.

## Verified locator

PRX Quantum 7, 043015, PDF p. 4, Eq. (3) and Definition 1,
p. 5, Theorem 1, and p. 9,
§V, the paragraph asking for tight diamond norm bounds. PDF p. 10
discusses invisible GHZ-type coherences. Appendix D
relates the two norms. The open-question paragraph is also in arXiv v1,
p. 7, §V. [DOI](https://doi.org/10.1103/51mt-ghpn) · [Source](https://arxiv.org/abs/2603.07037v1) · [Journal PDF](https://harvest.aps.org/v2/journals/articles/10.1103/51mt-ghpn/fulltext)
