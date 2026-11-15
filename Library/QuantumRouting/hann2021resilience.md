---
bibkey: hann2021resilience
authors: Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang
year: 2021
title: "Resilience of quantum random access memory to generic noise"
doi: null
url: https://arxiv.org/pdf/2012.05340v2
claim: "Section II.B specifies three-state router and incident/output systems, sequential address absorption by SWAP and conditional routing; Appendix A separates sequential and pipelined timing; Appendix B equation B1 defines vacuum-preserving classical-bit readout."
strata_touched:
  - D5/S3/Quantum/Routing/HannSpatialQram
license: citation-only
triage: anchor
---

# Sequential three-state spatial lookup

## Verified locator

- URL: https://arxiv.org/pdf/2012.05340v2
- Section II.B and Figure 1(b), printed pages 4–5.
- Appendix A and Figure 10, printed pages 19–20.
- Appendix B, equation (B1) and Figure 11(b), printed pages 19–21.

The router and each incident/output mode have basis labels W, 0 and 1.
The occupied logical subspace is spanned by 0 and 1. W means wait for a
router and vacuum for a spatial mode. Address signals are physical
three-level systems encoded in the occupied subspace. Section II.B states
that an address encountering a waiting router swaps its incident state
with the router state. A router in 0 or 1 sends subsequent signals to its
left or right output. Figure 1(b) implements routing with two controlled
SWAP gates. Figure 10 also contains ordinary full SWAP transfers.

Appendix A explicitly describes the sequential schedule in which address
k+1 is injected only after address k has reached its router. It then gives
a different pipelined ordering. `HannSpatialQram` uses the former schedule.
It does not assert equality of the two permutations on arbitrary dirty
configurations. A parent's output and its child's incident mode are one
physical rail in the formal state coordinates.

Equation (B1) gives X-tilde = |1><0| + |0><1| + |W><W|. Classically
controlled X-tilde operations act at every leaf: they exchange occupied
labels for datum 1 and preserve vacuum. This establishes the no-extra-copying
property on initialized modes. The formal circuit allows either occupied
input bus label, so the result is bus XOR selected classical bit.

The ideal clean lookup and its operational induction are the formalization
of this published construction. No noise theorem, resource bound, physical
Hamiltonian or copying of unknown quantum states is claimed. The earlier
proposal https://arxiv.org/pdf/0708.1879 uses a distinct fiducial-qubit
notation f; this correspondence makes no assertion f = W. The Boolean
network of https://arxiv.org/pdf/1502.03450v4, Section IV, Figure 9 and
equation (11), is a separate implementation.
