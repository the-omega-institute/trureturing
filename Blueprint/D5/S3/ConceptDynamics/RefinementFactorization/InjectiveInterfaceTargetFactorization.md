# Injective Interface Target Factorization

## Abstract

An injective interface uniquely factors every target on its realized image.

**Theorem 1.1 (An injective interface factors every target).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}q: X \to B, T: X \to Y,\\{}\operatorname{Injective}(q) \Rightarrow\\{}\exists! h: \operatorname{range}(q) \to \operatorname{range}(T),\\{}\operatorname{rangeFactorization}(T) = h \circ \operatorname{rangeFactorization}(q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization.injective_interface_factors_every_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the interface and target are restricted canonically to their realized images. Thus the factor is total without choosing arbitrary values outside the interface image, and the statement remains valid for an empty state type.

Injectivity makes equality of interface values imply equality of states and hence equality of every target value. The imported realized-image kernel criterion turns this kernel inclusion directly into the displayed unique commuting factor.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization.injective_interface_factors_every_target`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization](RealizedImageKernelFactorization.md)
