# Minimal Naturality

## Abstract

Diagonal naturality forces the unique surjective predictive-completion factor.

**Theorem 1.1 (Naturality forces commutation and the unique surjective completion factor).**

$$\forall Y, O, W, [\operatorname{Finite} Y], [\operatorname{Finite} W], [\operatorname{Nonempty} Y],\ tau: Y \to Y, q: Y \to O, r: Y \to W, o: W \to O, sigma: W \to W,\ Surjective(r) \land q = o \circ r \land \forall A \in \operatorname{Type},\; \operatorname{Nonempty}(A) \Rightarrow \left(\forall E \in A \to \left(A \to Y\right),\; Q_{r}(\Delta_{tau}(E)) = \Delta_{sigma}(P_{r}(E))\right) \Rightarrow (r \circ tau = sigma \circ r) \land \exists h \in W \to CompletedState(tau, q),\; \left(Surjective(h) \land completionProjection(tau, q) = h \circ r\right) \land \left(\forall hPrime \in W \to CompletedState(tau, q),\; \left(Surjective(hPrime) \land completionProjection(tau, q) = hPrime \circ r\right) \Rightarrow hPrime = h\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/MinimalNaturality.minimal_naturality_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau update a finite state carrier Y, q be its readout, and let a finite realization r map Y surjectively to W while preserving q through o. The source diagonal is evaluated by applying tau to each table diagonal; P_r and Q_r push tables and vectors through r.

If Q_r Delta_tau equals Delta_sigma P_r for every nonempty address type and every evaluation table, the singleton address instance forces r tau = sigma r. The canonical predictive-completion universal property then supplies a surjective factor h to the completed-state carrier, and surjectivity of r makes h unique even after retaining only the two displayed factor clauses.

Repository search found and directly applied the canonical declarations DeterministicCompletionMinimality.minimal_deterministic_completion and the CompletedState, completionProjection definitions. Pinned Mathlib search found Function.semiconj_iff_comp_eq and quotient-surjectivity ingredients; no single library theorem packaged this naturality converse. The loogle and leansearch executables were unavailable on PATH.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/MinimalNaturality.minimal_naturality_factor`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/DeterministicCompletionMinimality](DeterministicCompletionMinimality.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](../Refinement/PredictionCompletion.md)
