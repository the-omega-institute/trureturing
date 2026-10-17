---
bibkey: shor1997gateorbits
authors: Peter W. Shor
year: 1997
title: "Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer"
doi: 10.1137/S0097539795293172
url: https://arxiv.org/abs/quant-ph/9508027
claim: "Established reversible arithmetic and Fourier order finding, applied with explicit phase, work-register and power-access contracts."
strata_touched: []
license: citation-only
triage: anchor
---

## Primary source and actual use

Shor's paper provides quantum polynomial-time algorithms for factoring and discrete logarithms. The independent [gate/state-machine continuation](../../docs/develop/theory/FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md) uses the order-finding architecture and explicitly separates it from a factoring reduction. A Fibonacci matrix period is an order-finding target; finding it is not by itself the classical reduction that factors an arbitrary integer.

Kitaev, *Quantum measurements and the Abelian Stabilizer Problem*, [arXiv:quant-ph/9511026](https://arxiv.org/abs/quant-ph/9511026), provides the unitary-eigenvalue and Abelian-action formulation. IBM's official [order-finding explanation](https://quantum.cloud.ibm.com/learning/en/courses/fundamentals-of-quantum-algorithms/phase-estimation-and-factoring/shor-algorithm) and [tutorial](https://quantum.cloud.ibm.com/docs/en/tutorials/shors-algorithm) expose controlled high powers, finite phase precision and classical denominator recovery. These sources were consulted on 14 October 2026. No hardware results from the tutorial were reproduced.

## Control is an access assumption

Araujo, Feix, Costa and Brukner, *Quantum circuits cannot control unknown operations*, [arXiv:1309.7976](https://arxiv.org/abs/1309.7976), DOI 10.1088/1367-2630/16/9/093026, establishes a no-go statement in a specified black-box circuit model. Its global-phase argument explains why a channel specification does not uniquely supply a phase-referenced controlled gate. The paper itself distinguishes physical extensions with additional information.

Tang and Wright, *Are controlled unitaries helpful?*, [arXiv:2508.00055v2](https://arxiv.org/abs/2508.00055v2), revised 23 April 2026, gives phase-averaged decontrolling for a broad task/access class using forward/inverse queries. The abstract and version record were checked; the detailed construction was not implemented or reproved. This is a boundary on sweeping no-go interpretations, not a delivered control compiler.

## Project-specific derivations and scope

The continuation derives the monomial phase accumulated by the actual no11 full-flip pulses, its effect on cycle eigenphases, the concrete three-word return-sign example, tensor-conjugate cancellation on the diagonal code, the exact reduced-clock dependence on residual work, and the faithful companion-matrix probe over composite moduli. Generic monomial/Fourier algebra and reversible computation retain their established ownership. No exhaustive priority search or novel-algorithm claim is asserted.

The existing LucasCompanion Lean file supplies algebraic definitions and period identities only. It has not been recompiled in this delivery, and the new quantum integration is ordinary written mathematics. The Fibonacci occupancy space, a Fibonacci fusion-chain algebra and the modular Fibonacci recurrence are distinct objects; no gate compilation between them follows from their names. The new line has no dependency on the HS4 or many-body PR.

## Verified locator

- DOI: https://doi.org/10.1137/S0097539795293172
- URL: https://arxiv.org/abs/quant-ph/9508027
