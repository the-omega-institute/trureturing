# Experiment Value Is Kernel Reduction

## Abstract

An experiment is valuable when it removes target residual pairs, independently of the nominal size of its response space.

**Lemma 1.1 (No target residual pair is equivalent to factorization).**

$$\begin{aligned}\forall E, X, R, Y: \operatorname{Type},\\A: \operatorname{Set}\left(E\right), r: E \to \left(X \to R\right), t: X \to Y,\\\operatorname{Nonempty}\left(X\right) \Rightarrow \operatorname{TargetIdentifiable}\left(A, r, t\right) \iff \exists f: (\forall a: A, R) \to Y, t = f \circ \operatorname{jointReadout}\left(\operatorname{restrict}\left(r, A\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction.targetIdentifiable_iff_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target residual pair consists of two states that every allowed experiment treats alike even though the target separates them. Target identifiability is exactly the absence of such a pair.

For a nonempty state space, absence of residual pairs says that the target is constant on every fiber of the joint allowed-experiment readout. The existing identifiability criterion then supplies a single map that recovers the target from the complete response tuple, and any such factorization rules out a residual pair.

Indexing the joint response tuple by the subtype of allowed experiments ensures that the factorization uses precisely the admitted family, not experiments outside it.

**Theorem 1.2 (Experiment value is reduction of the target residual kernel).**

$$\begin{aligned}(\operatorname{card}\left(\operatorname{Fin}\left(1000\right)\right) > \operatorname{card}\left(Bool\right) \land \\\operatorname{residualPairs}\left(\emptyset, large, target\right) = \operatorname{residualPairs}\left(univ, large, target\right) \land \\(\operatorname{TargetIdentifiable}\left(\emptyset, large, target\right) \iff \operatorname{TargetIdentifiable}\left(univ, large, target\right))) \land \\(\operatorname{card}\left(Bool\right) = 2 \land \\\operatorname{residualPairs}\left(\emptyset, bit, target\right) = \{(false, true), (true, false)\} \land \\\operatorname{residualPairs}\left(univ, bit, target\right) = \emptyset \land \\\neg \operatorname{TargetIdentifiable}\left(\emptyset, bit, target\right) \land \operatorname{TargetIdentifiable}\left(univ, bit, target\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction.experiment_value_is_kernel_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the Boolean state space, the large-output experiment is constant: both states receive the same element of a response type with one thousand symbols. Allowing that experiment therefore leaves the residual-pair set unchanged and does not improve target identifiability.

With no allowed bit experiment, the identity target has exactly the two ordered off-diagonal Boolean residual pairs. Once the identity bit experiment is allowed, equal responses force equal states, so the residual-pair set becomes empty and the target is identifiable.

Thus a two-symbol response can be decisive while a strictly larger response space is inert. The mathematical value of the experiment is the target-relevant kernel it removes, rather than the cardinality of its nominal output alphabet.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction.experiment_value_is_kernel_reduction`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction.targetIdentifiable_iff_factorization`
- Dependency: [D5/S3/ConceptDynamics/Experiment/ExperimentIdentifiability](ExperimentIdentifiability.md)
