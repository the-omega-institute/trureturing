# Deterministic Readout PVM

## Abstract

Deterministic readout fibers form a complete family of diagonal projections.

**Theorem 1.1 (Fiber projections are orthogonal and complete).**

$$\forall X: \operatorname{Type}, O: \operatorname{Type}, [\operatorname{Fintype}(X)], [\operatorname{Fintype}(O)], [\operatorname{DecidableEq}(X)], [\operatorname{DecidableEq}(O)], q: X \to O \Rightarrow \forall o: O, op: O, \operatorname{deterministicProjection}(q, o) \circ \operatorname{deterministicProjection}(q, op) = if o = op then \operatorname{deterministicProjection}(q, o) else 0 \land sum_{o} \operatorname{deterministicProjection}(q, o) = I.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/DeterministicReadoutPvm.deterministic_readout_pvm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier and deterministic readout, each outcome projection is the diagonal indicator of its readout fiber.

Distinct fibers are disjoint, giving the product law; the fibers cover the state carrier, giving the identity sum.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/DeterministicReadoutPvm.deterministic_readout_pvm`
