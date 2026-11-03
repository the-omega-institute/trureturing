---
bibkey: narasimhachargour2015cooling
authors: Varun Narasimhachar, Gilad Gour
year: 2015
title: "Low-temperature thermodynamics with quantum coherence"
doi: 10.1038/ncomms8689
url: https://arxiv.org/abs/1409.7740v3
claim: "In the low-temperature limit, thermal operations act with an ancilla in its ground space; the paper introduces cooling maps, channels whose Kraus operators are diagonal or lower a single energy level, characterizes their state transitions, and conjectures (Conjecture 1) that cooling maps are equivalent to low-temperature thermal operations with regard to the feasibility of state transitions."
strata_touched:
  - D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation
license: citation-only
triage: anchor
---

# Narasimhachar–Gour, low-temperature thermodynamics with quantum coherence

## Verified locator

DOI: 10.1038/ncomms8689

Source: https://arxiv.org/abs/1409.7740v3

Nature Communications 6, 7689 (2015).

V. Narasimhachar and G. Gour, arXiv:1409.7740v3 [quant-ph] (9 August 2015, the latest version); Nature Communications 6, 7689 (2015).

Low-temperature thermal operations (main text): the ancilla state is replaced by the normalized projector onto the ground space of its Hamiltonian, $\gamma_A\approx P_{\mathrm{ground}}/g$, and

> In the remainder, we will use the term "thermal operation" to mean "thermal operation under the low-temperature assumption".

Cooling maps (Supplementary Note):

> A quantum channel (CPTP map) with a Kraus decomposition consisting of Kraus operators of the following two classes: Diagonal matrices $\{K_1\dots K_n\}$. Without loss of generality, we can assume $n\le d$. Matrices of the form $J_{jk}\propto|E_j\rangle\langle E_k|$, $j<k$. All matrix representations are in the standard basis $\{|E_j\rangle\}$. Note that the elements of the matrices can be complex.

Conjecture 1 (Supplemental Material, `LTT_arXiv.tex` lines 924–927):

> Cooling maps are equivalent to low-temperature thermal operations, with regard to the feasibility of state transitions.

followed by: "Note that this could be true even if the set of cooling maps is strictly larger than that of thermal operations—there could still be a thermal operation achieving every state transition that is possible through cooling maps."

## Encoding and boundary

A low-temperature thermal operation is encoded with a finite ancilla `Fin m` with diagonal energies (a basis change of the ancilla is absorbed into the unitary), a unitary commuting with $H_S\otimes I+I\otimes H_A$, and the output $\operatorname{Tr}_A[U(\rho\otimes P_{\min}/g)U^\dagger]$ with the full ground eigenspace. A cooling map is a finite Kraus family whose members are diagonal or multiples of $|E_j\rangle\langle E_k|$ with $j<k$, with $\sum_iK_i^\dagger K_i=I$. The repository refutes Conjecture 1 for a four-level system with energies $0,1,3,7$ and the uniform pure input: a cooling map with two diagonal Kraus operators reaches a state with uniform populations that no ground-space thermal operation reaches. Positive-temperature thermal operations, approximate transitions, catalytic variants and the qubit equivalence shown in the source are outside this conclusion.
