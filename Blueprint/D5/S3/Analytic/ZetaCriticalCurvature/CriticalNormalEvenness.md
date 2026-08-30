# Critical Normal Evenness

## Abstract

Reflection-even scalar potentials have zero first normal derivative at the fixed axis.

**Theorem 1.1 (Even Has Deriv At Zero).**

$$\forall V: \mathbb{R} \to \mathbb{R}, d: \mathbb{R},\\{}(HasDerivAt V d 0) \land (\forall u : \mathbb{R}, V (-u) = V u) \Rightarrow\\{}(d = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.even_hasDerivAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A differentiable even real function has zero derivative at the reflection fixed point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Deriv Even Zero).**

$$\forall V: \mathbb{R} \to \mathbb{R},\\{}(DifferentiableAt \mathbb{R} V 0) \land (\forall u : \mathbb{R}, V (-u) = V u) \Rightarrow\\{}(deriv V 0 = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.deriv_even_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

deriv formulation of the same reflection obstruction.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Critical Normal Derivative Zero).**

$$\forall V: \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right), t: \mathbb{R}, d: \mathbb{R},\\{}(HasDerivAt (\lambda u : \mathbb{R} \mapsto V u t) d 0) \land (\forall u : \mathbb{R}, V (-u) t = V u t) \Rightarrow\\{}(d = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.critical_normal_derivative_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Parameterized potential version. For every fixed tangential coordinate t, normal reflection symmetry removes the first normal derivative.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Critical Normal Deriv Zero).**

$$\forall V: \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\\{}(\forall t : \mathbb{R}, DifferentiableAt \mathbb{R} (\lambda u : \mathbb{R} \mapsto V u t) 0) \land (\forall u t : \mathbb{R}, V (-u) t = V u t) \Rightarrow\\{}(\forall t : \mathbb{R}, deriv (\lambda u : \mathbb{R} \mapsto V u t) 0 = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.critical_normal_deriv_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise family formulation.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.critical_normal_deriv_zero`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.critical_normal_derivative_zero`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.deriv_even_zero`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.even_hasDerivAt_zero`
