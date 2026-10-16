---
bibkey: campbell2010optimalentangling
authors: Earl T. Campbell
year: 2010
title: Optimal entangling capacity of dynamical processes
doi: 10.1103/PhysRevA.82.042314
url: https://arxiv.org/abs/1007.1445
claim: Section VII asks whether log-negativity entangling capacity is resource independent for all unitaries or all CPTP maps.
strata_touched:
  - D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.82.042314

Source: https://arxiv.org/abs/1007.1445

Phys. Rev. A **82**, 042314. Page references are to arXiv:1007.1445v2.

## Resource independence

Section VII, p. 7, states:

> What do the results so far tell us about the existence of resource independent EC monotones? To recap, we know that log-robustness EC is always resource independent, and that log-negativity EC is resource independent for basic unitaries, such as two-qubit gates. The most obvious open question is whether log-negativity EC is resource independent for all unitaries, or indeed all CPTP maps, or whether this is a singular feature of 2-qubit gates.

Section I, Eqs. (1)–(2), defines the unassisted capacity as the supremum of output entanglement over separable inputs, and the assisted capacity as the supremum of output entanglement minus input entanglement over all density matrices. Local ancillary systems are free. Eqs. (4)–(5) and the logarithmic rescaling give log-negativity as the base-two logarithm of the partial-transpose trace norm.

The finite Kraus interpretation quantifies all finite local dimensions and all finite local ancilla dimensions. The all-CPTP clause is the statement compared by the two capacities. Its refutation makes no assertion about the unitary clause or the two-qutrit unitary conjecture.

Section I, p. 2, states:

> Throughout, we assume that local ancilla (typically labelled as Hilbert space Ha′ ⊗ Hb′ ), local unitaries and classical communication are freely available as is appropriate in many communication and distributed computation scenarios.

> The maximum achievable entanglement for a dynamical map, Λ, when the initial state is separable, is given by:

$$E(\Lambda)=\sup\{E(\Lambda(\sigma))\mid\sigma\in S\}.$$

> However, when prior entanglement is available, the maximum increase of entanglement is:

$$E^D(\Lambda)=\sup\{E(\Lambda(\sigma))-E(\sigma)\mid\sigma\in D\}.$$
