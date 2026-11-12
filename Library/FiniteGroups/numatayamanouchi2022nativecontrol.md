---
bibkey: numatayamanouchi2022nativecontrol
authors: Yasuhide Numata; Yuiko Yamanouchi
year: 2022
title: "On the action of the toggle group of the Dynkin diagram of type A"
doi: 10.5802/alco.204
url: https://arxiv.org/abs/2103.16217
claim: "The toggles of independent sets of an open path generate its entire symmetric group; consumed as a combinatorial input to native no11 quantum control."
strata_touched: []
license: citation-only
triage: anchor
---

## Source and exact correspondence

Published in Algebraic Combinatorics 5 (2022), 149-161. [Publisher page](https://alco.centre-mersenne.org/articles/10.5802/alco.204/). Theorem 3.7, printed page 155, identifies the generated toggle group with the full symmetric group for every path length n>=1. The relevant theorem and proof text were inspected. The theorem is already stated in the publisher abstract at the level used here.

The source's independent subsets of the path vertices 1,...,n are precisely the legal no-consecutive-one indicator strings B_n. Its toggle at i adds or removes i when independence is preserved and otherwise fixes the set. This is exactly the underlying permutation of a full-flip native pulse R_i(0,pi/2) in the project's existing legal-interference Chapter 8. The physical pulse also has amplitude phases. Those phases disappear when it conjugates a diagonal matrix, which is the precise use of the permutation theorem in [the gate-state-machine continuation](../../docs/develop/theory/FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md), Theorem 11.2.

The published theorem concerns a finite permutation group. It does not prove the native pulse Lie algebra, guarantee physical access, bound pulse length for arbitrary permutations, or compile Shor's algorithm. The added Lie argument obtains a nonconstant diagonal commutator from one site's two quadratures, spans all diagonal differences by toggle conjugations, isolates one matching edge and transports its two quadratures to every pair. That additional derivation and its ideal control assumptions are written explicitly in the theory; their historical novelty has not been audited.

## Other primary inputs and excluded claims

F. Albertini and D. D'Alessandro, *Notions of controllability for quantum mechanical systems*, [arXiv:quant-ph/0106128](https://arxiv.org/abs/quant-ph/0106128), supplies the standard finite-dimensional Lie-group control framework. D. D'Alessandro, *On Quantum State Observability and Measurement*, [arXiv:quant-ph/0307127](https://arxiv.org/abs/quant-ph/0307127), DOI 10.1088/0305-4470/36/37/310, distinguishes controlled state evolution, observational equivalence and measurement families. Neither general controllability nor informational completeness implies a short circuit or single-copy state tomography.

A. Barenco et al., *Elementary gates for quantum computation*, [arXiv:quant-ph/9503016](https://arxiv.org/abs/quant-ph/9503016), DOI 10.1103/PhysRevA.52.3457, supplies established one-qubit and CNOT universality. D. Jaksch et al., *Fast Quantum Gates for Neutral Atoms*, [arXiv:quant-ph/0004038](https://arxiv.org/abs/quant-ph/0004038), DOI 10.1103/PhysRevLett.85.2208, supplies historical blockade-mediated conditional-phase context. The specific zero-separator encoding, exact five-pulse CZ/nine-pulse CNOT identities and explicit routing bound in the continuation are derived in its declared ideal occupancy model. They do not reproduce a material level scheme, finite-blockade correction, apparatus or error budget from Jaksch et al.

The weak control theorem allows a second quadrature at any one site. The short encoded compiler uses phase-addressable data sites throughout, as permitted by the original larger menu. These two results have different resource assumptions and cannot be conflated. The current finite verification is ordinary symbolic algebra, exact modular Lie-word rank lower bounds and classical simulation of one compiled order-probe. No Lean verification, physical universality demonstration, optimized synthesis, many-body phase, arithmetic speedup or historical-first claim is asserted.

## Verified locator

- DOI: https://doi.org/10.5802/alco.204
- URL: https://arxiv.org/abs/2103.16217
