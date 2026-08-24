# Control Quotient Universal Minimality

## Abstract

The quotient by all monoid-indexed public outcomes is the universal coarsest action-complete concept.

**Theorem 1.1 (The control quotient is the universal action completion).**

$$\begin{gathered}\forall M, X, O: \operatorname{Type}, \operatorname{MonoidAction}(M, X), q: X \to O,\\{}Kctl(x, m) := q(m \cdot x), Zctl := \operatorname{Quotient}(\operatorname{ker}(Kctl)),\\{}pi := \operatorname{controlProjection}(q),\\{}q = \operatorname{controlReadout}(q) \circ pi \land\\{}(\forall m, pi \circ \operatorname{act}(m) = \operatorname{controlAction}(q, m) \circ pi) \land\\{}(\forall m, \operatorname{outcome}(q, m) = \operatorname{controlOutcome}(q, m) \circ pi) \land\\{}(\forall C, (\operatorname{Recoverable}(q, C) \land \operatorname{ActionClosed}(C) \land \operatorname{OutcomeDetermined}(q, C)) \Rightarrow (\exists! h: \operatorname{range}(C) \to \operatorname{range}(pi), \operatorname{rangeFactorization}(pi) = h \circ \operatorname{rangeFactorization}(C))) \land\\{}\operatorname{ker}(Kctl) = \operatorname{ker}(\operatorname{DynClosure}(q, \operatorname{act}(M))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality.control_quotient_universal_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The control profile is constructed directly from the source monoid action: at a state it records the public readout after every action. The named control carrier is the quotient by equality of these complete profiles, and the canonical projection is retained in every public equation.

The empty action recovers the present readout. Multiplication in the monoid makes every action preserve profile equality, producing an induced action on the quotient; evaluating a profile at a chosen action gives the corresponding public consequence from the current quotient value.

For any competing concept, the theorem requires recovery, action closure, and consequence determination as separate public premises. Consequence determination forces its equality kernel into the control kernel, and the imported realized-image criterion supplies the unique factor onto the canonical quotient image.

Finally, finite intervention words and single monoid actions induce the same state equivalence. Word composition gives one direction, while the one-action word gives the reverse, identifying this quotient with the family's dynamic completion at the kernel level.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality.control_quotient_universal_minimality`
- Dependency: [D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality](../Interventions/DynamicClosureMinimality.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization](../RefinementFactorization/RealizedImageKernelFactorization.md)
