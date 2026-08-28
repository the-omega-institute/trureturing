# Finite Expectation Table Separation

## Abstract

An unrealizable complete affine expectation table has a finite linear certificate.

**Theorem 1.1 (A finite linear inequality detects nonrealizability).**

$$\begin{aligned}\forall State: \operatorname{Type}, Protocol: \operatorname{Type},\\\operatorname{NormedAddCommGroup}(State) \land \operatorname{NormedSpace}(\mathbb{R}, State),\\D: \operatorname{Set}(State), e: Protocol \to \operatorname{ContinuousAffineMap}(\mathbb{R}, State, \mathbb{R}),\\y: Protocol \to \mathbb{R}, \operatorname{IsCompact}(D) \land \operatorname{Convex}(\mathbb{R}, D),\\\neg\exists \rho: State, \rho\in D \land \forall p: Protocol, e(p, \rho) = y(p)\\\Rightarrow \exists S: \operatorname{Finset}(Protocol), L: \operatorname{ContinuousLinearMap}(\mathbb{R}, S \to \mathbb{R}, \mathbb{R}), a: \mathbb{R},\\(\forall \rho: State, \rho\in D \Rightarrow L((p: S \mapsto e(p, \rho))) < a) \land\\a < L((p: S \mapsto y(p))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/FiniteExpectationTableSeparation.finite_expectation_table_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density-matrix carrier is exposed as a compact convex subset of a real normed state space. Every effect expectation is a continuous affine real-valued map, and the complete formal table is assumed not to agree with any state on every effect.

The open sets on which one effect disagrees with the table cover the density matrices. Compactness extracts a finite effect set. Its finite readout image is compact and convex.

Finite-dimensional Hahn-Banach separation supplies a continuous linear functional and threshold. Every realizable selected readout lies strictly below the threshold, while the selected entries of the formal table lie strictly above it.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/FiniteExpectationTableSeparation.finite_expectation_table_separation`
