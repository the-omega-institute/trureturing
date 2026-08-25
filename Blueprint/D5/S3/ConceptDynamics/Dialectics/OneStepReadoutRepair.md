# One-Step Readout Repair

## Abstract

The current and next readouts form their canonical least joint interface.

**Theorem 1.1 (The current and next readouts form the least repair).**

$$\begin{gathered}\forall X, B: \operatorname{Type}, q: X \to B, F: X \to X,\\{}\operatorname{Refines}\left(q, \operatorname{conceptJoin}\left(q, {q \circ F}\right)\right) \land\\{}\operatorname{Refines}\left({q \circ F}, \operatorname{conceptJoin}\left(q, {q \circ F}\right)\right) \land\\{}(\forall C: \operatorname{Type}, r: X \to C, a, b: C \to B,\\{}q = a \circ r \Rightarrow q \circ F = b \circ r \Rightarrow \operatorname{conceptJoin}\left(q, {q \circ F}\right) = \langle a, b \rangle \circ r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/OneStepReadoutRepair.one_step_readout_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source state, readout, and update are independent primitives. Their repaired interface is the canonical concept join of the current readout and its value after one update.

The first two public conjuncts retain the current readout and determine the next readout. The final clause quantifies over another interface and its two supplied factor maps.

Pairing those supplied maps gives the displayed factorization of the canonical joint readout, which is the coarseness assertion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/OneStepReadoutRepair.one_step_readout_repair`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
