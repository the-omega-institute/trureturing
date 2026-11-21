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

## Fresh product-input discrimination

Liu–Wild §V motivates the construction through the diamond-norm question
and its discussion of GHZ-type coherence. The repository proves the
exact testing curve for this pair on n ≥ 1 qubits. Each channel has Kraus
rank two for n ≥ 2.

Each of the fixed M calls uses a fresh tensor product of single-qubit
density states and a finite POVM on that call’s full output. The policy
chooses both from the classical outcome history and a finite random seed
with the same law under both hypotheses. The optimal equal-prior and
worst-case success probabilities both equal 1 − (1 − 2/2ⁿ)^M/2. The
upper bound follows by multiplying lower bounds on conditional overlap.
Repeated all-plus inputs and a three-outcome GHZ measurement attain it
with a fair guess if every call is inconclusive. Success of at least two
thirds requires at least 2ⁿ/6 calls.

On arbitrary full-register inputs the two channels induce identical
reduced maps on every proper output subset, even with a retained
reference. In particular, their proper paired Choi marginals agree.
A GHZ input with access to the full output distinguishes them with
certainty in one call.

## Nearest-neighbor realization with environment records

On an open path of N qubits, write d = 2ᴺ and pair each input
reference with its corresponding output. For either of two explicit
channels, every proper paired marginal on s sites is the identity
divided by 4ˢ. The full normalized Choi entropy is 2 log d − (log 2)/d.
For pairwise disjoint L, M, R the paired conditional mutual information
is (log 2)/d when their union is the full path and both outer regions
are nonempty, and zero otherwise. In nats, (log 2) exp(−(log 2)|M|)
bounds it uniformly in the path length and in the regions, as
required in Definition 1.

The full normalized Choi states have unhalved trace norm difference
2/d, while the channels have unhalved diamond distance 2. Every
channel-valued estimator from all exact proper paired marginals has
worst-case diamond error at least 1 on this pair. One call on the
all-ones product input followed by a global parity measurement
identifies the channel when this probe is available.

The adjacent XOR sampler for a uniform parity class appears in Horacsek, Lee, Shinkar, Viola and Zhou, *Local Samplers for Product Distributions*, §1, p. 109:2, with attribution to Babai and Boppana–Lagarias. The channel here makes the parity constraint conditional on a designated input and proves the induced marginal and CMI formulas. [DOI](https://doi.org/10.4230/LIPIcs.ICALP.2026.109)

Lean verifies the finite record isometry and that its environment
partial trace gives the channel action on every input matrix. The
trace specializes to the repository's EnvironmentRecords qubit
trace. The accompanying paper proof establishes a ten-layer
nearest-neighbor realization with at most six ancillas per site,
including the output, from a pure product initialization. The
construction gives the same exact-data obstruction when the channels
are promised this local Stinespring realization.

## Coherent query lower bound for hidden activation on a path

Put d = 2ᴺ on the N-qubit path. For each mark a, translate each input bit
xᵢ by 1 − aᵢ before the edge-record channel. Only the input word a becomes
all ones. The original independent fair edge and site bits then yield
uniform outputs off a and the uniform parity-b law on a. In Lean the marked
CPTP oracle equals this translated path channel. Precomposing the original
record isometry by the same basis permutation and tracing the original
environment gives its action on every input matrix.

On the normalized Choi state, the translation permutes the input reference
basis and factors over any kept and discarded site sets. Every proper paired
marginal remains maximally mixed for every (a,b). The paired entropies and
conditional mutual information in Liu–Wild Definition 1 retain the
values of the original path channels. In particular the uniform bound in
nats is (log 2) exp(−(log 2)|M|), with |M| the number of middle sites.
For a fixed mark the two parities have unhalved diamond distance 2.

Any T-call protocol that reports the parity with probability at least
2/3 on every (a,b) needs T ≥ d/3. The protocol may start with an
arbitrary entangled probe and use arbitrary adaptive CPTP operations on
the query register and finite quantum memory. The decision may receive
a after the last call. The same lower bound applies to a finite POVM
whose outcomes give channel estimates with unhalved diamond error
strictly below 1 with probability at least 2/3 on every (a,b).

Ghosh, Jackson and Datta, arXiv:2611.20366v1, §3.1, Eqs. (8)–(10), give the rank-one perturbation family containing these channels as a deterministic specialization. Rosenthal, Aaronson, Subramanian, Datta and Gur, arXiv:2409.12566v4, Theorem 1.2 and §3, use rare input weights to prove a coherent query lower bound for replacement-channel certification. The path construction supplies the one-dimensional realization, proper-window equality and uniform Choi CMI for the specific family used here. [Ghosh–Jackson–Datta](https://arxiv.org/abs/2611.20366v1) · [Rosenthal et al.](https://arxiv.org/abs/2409.12566v4)

The channel model exposes the system output after the environment trace.
A known mark can be queried directly with one computational product probe
and a parity measurement. The accompanying paper proof supplies the
original ten-layer nearest-neighbor schedule from a pure product
environment. Prepending one parallel layer of local input flips realizes
the translated path family with the same ancilla count. The paper also
gives an O(d)-call product-probe algorithm under the marked family promise.

## Verified locator

PRX Quantum 7, 043015, PDF p. 4, Eq. (3) and Definition 1,
p. 5, Theorem 1, and p. 9,
§V, the paragraph asking for tight diamond norm bounds. PDF p. 10
discusses invisible GHZ-type coherences. Appendix D
relates the two norms. The open-question paragraph is also in arXiv v1,
p. 7, §V. [DOI](https://doi.org/10.1103/51mt-ghpn) · [Source](https://arxiv.org/abs/2603.07037v1) · [Journal PDF](https://harvest.aps.org/v2/journals/articles/10.1103/51mt-ghpn/fulltext)
