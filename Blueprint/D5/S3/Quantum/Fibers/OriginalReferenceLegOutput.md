# Tensor action and measurable quantum outputs

## Abstract

Original affine-leg outputs in the trace-norm space of an arbitrary reference.

**Theorem 1.1 (The original row acts only on the live system).**

$$\forall H \in CompleteComplexHilbertSpace, c \in Real, a \in Real, k \in Real, S \in Real, g \in \operatorname{Functions}\left(\operatorname{Fin}\left(5\right), Real\right), i \in \operatorname{Fin}\left(5\right), z \in \operatorname{Tensor}\left(\operatorname{EuclideanSpace}\left(\operatorname{Fin}\left(5\right)\right), H\right),\; \operatorname{referenceJumpAfterCoordinates}\left(c, a, k, S, g, i, z\right) = \operatorname{scalarTensorIdentification}\left(\operatorname{tensorMap}\left(\operatorname{originalAbsorbingRow}\left(c, a, k, S, g, i\right), \operatorname{identity}\left(H\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceLegOutput.tensor_jump_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The system is the five-dimensional Euclidean space and H is any complete complex Hilbert space. The finite tensor isometry sends u tensor x to the vector with coordinates u_i x. The amplified row is obtained from the literal original jumpKraus coefficients. On a simple tensor, distributing the finite row sum gives the original scalar row action on u multiplied by x. Tensor induction extends this identity to every joint vector. The algebraic tensor is already complete because its finite-system coordinate realization is a complete finite Hilbert sum. Thus the equation is the action tensored with the unchanged reference on the entire joint space, including entangled vectors.

**Theorem 1.2 (Actual affine-leg Bochner outputs on every Borel event).**

$$\forall H \in CompleteComplexHilbertSpace, L \in OriginalAffineLeg, i \in \operatorname{Fin}\left(5\right), rho \in \operatorname{TraceClass}\left(\operatorname{Blocks}\left(\operatorname{Fin}\left(5\right), H\right)\right),\; \operatorname{Positive}\left(rho\right) \Rightarrow \left(\operatorname{IntegrableOnTraceNorm}\left(\operatorname{actualFailureOutput}\left(L, i, rho\right), \operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right)\right) \land \left(\forall E \in \operatorname{Set}\left(Real\right),\; \operatorname{MeasurableSet}\left(E\right) \Rightarrow \operatorname{integralOnEvent}\left(\operatorname{actualFailureOutput}\left(L, i, rho\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right), E\right)\right) = \operatorname{smul}\left(\operatorname{integralOnEvent}\left(\operatorname{actualCoefficient}\left(L, i\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right), E\right)\right), \operatorname{referenceCompression}\left(rho, i\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceLegOutput.affine_failure_bochner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L has c<1/2, positive duration, and endpoints strictly between zero and c. Its height is the literal affine path, its hazard is the original positive-part logarithmic hazard, its survival is exp of minus its hazard integral, and its rate subtracts the actual logarithmic probability derivative. The coefficient is g_i(t) S(t) p_i(k(t))/p_i(x). It equals the supplied affine-leg density divided by the positive initial probability p_i(x). The original affine-leg density is continuous on the closed time interval by Leg.density_cont in OriginalControlMarkedJump. ContinuousOn.intervalIntegrable_of_Icc gives interval integrability, and intervalIntegrable_iff_integrableOn_Ioc_of_le transfers it to (0,L.duration]. Division by the fixed positive initial probability gives scalar coefficient integrability. For fixed rho and i the output lies in the one-dimensional span of the same reference compression pi_i rho iota_i, even when the reference and trace-class space are nonseparable. Scalar multiplication proves Bochner integrability in the genuine trace norm. On the intersection of every Borel event E with (0,L.duration] the integral is the scalar coefficient integral times that fixed compression. The pointwise Kraus identity identifies this density with the actual output; it does not prescribe an output law. No normalization, product-state or finite-rank restriction is imposed. This theorem concerns one actual affine leg. Repeated-prefix coefficient masses, the early/late trace-distance equality, the operational supremum, the general six-dimensional input extension and the inverse application require further conclusions.

**Theorem 1.3 (Positive actual outputs on every Borel event).**

$$\forall H \in CompleteComplexHilbertSpace, L \in OriginalAffineLeg, i \in \operatorname{Fin}\left(5\right), rho \in \operatorname{TraceClass}\left(\operatorname{Blocks}\left(\operatorname{Fin}\left(5\right), H\right)\right), E \in \operatorname{Set}\left(Real\right),\; \left(\operatorname{Positive}\left(rho\right) \land \operatorname{MeasurableSet}\left(E\right)\right) \Rightarrow \left(\operatorname{IntegrableOnTraceNorm}\left(\operatorname{actualFailureOutput}\left(L, i, rho\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right), E\right)\right) \land \left(\operatorname{pointwiseActualKrausConjugation}\left(\operatorname{actualFailureOutput}\left(L, i, rho\right), L, i, rho, \operatorname{intersection}\left(\operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right), E\right)\right) \land \left(\operatorname{Positive}\left(\operatorname{integralOnEvent}\left(\operatorname{actualFailureOutput}\left(L, i, rho\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right), E\right)\right)\right) \land \operatorname{norm}\left(\operatorname{integralOnEvent}\left(\operatorname{actualFailureOutput}\left(L, i, rho\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right), E\right)\right)\right) = \operatorname{integralOnEvent}\left(\operatorname{normFunction}\left(\operatorname{actualFailureOutput}\left(L, i, rho\right)\right), \operatorname{intersection}\left(\operatorname{Ioc}\left(0, \operatorname{duration}\left(L\right)\right), E\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalReferenceLegOutput.affine_failure_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original affine leg, every mode, every complete complex Hilbert reference, every positive trace-class joint input and every Borel time event E, the density is integrable on D=(0,L.duration] intersect E. At every time in D its underlying operator is the literal amplified Kraus conjugation of that same input. The coefficient is nonnegative on this interval, so the Bochner event integral is positive. Scalar factorization in TraceClass H proves the exact identity norm(integral_D F)=integral_D norm(F), using the genuine trace norm. No separability, product-state, finite-reference or input normalization condition is imposed.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceLegOutput.affine_failure_bochner`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceLegOutput.affine_failure_event`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalReferenceLegOutput.tensor_jump_intertwining`
- Dependency: [D5/S3/Quantum/Fibers/OriginalReferenceKraus](OriginalReferenceKraus.md)
