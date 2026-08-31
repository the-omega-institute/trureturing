# Finite Atomic Budgeted Completion

## Abstract

An active complementary gap forces an even optimizer to be finite atomic.

**Theorem 1.1 (Active budget gives a finite symmetric atomic completion).**

$$\forall a \in \operatorname{Real}\left(\right), theta \in \operatorname{Real}\left(\right), lambda \in \operatorname{NNReal}\left(\right), phi \in \operatorname{WeilTestFunction}\left(\right), residual \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), completion \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right),\; \left(0 < a \land \left(0 < theta \land \left(\left(\forall x \in \operatorname{Real}\left(\right),\; \operatorname{conj}\left(phi\left(x\right)\right) = phi\left(x\right)\right) \land \left(\left(\forall xi \in \operatorname{Real}\left(\right),\; 0 \le \operatorname{realPart}\left(\operatorname{fourierLaplace}\left(phi, xi\right)\right) + \frac{theta}{(xi)^{2} + (a)^{2}}\right) \land \left(\operatorname{Integrable}\left((xi: \operatorname{Real}\left(\right) \mapsto \operatorname{realPart}\left(\operatorname{fourierLaplace}\left(phi, xi\right)\right) + \frac{theta}{(xi)^{2} + (a)^{2}}), residual\right) \land \left(\operatorname{Integrable}\left((xi: \operatorname{Real}\left(\right) \mapsto \frac{1}{(xi)^{2} + (a)^{2}}), residual\right) \land \left(\operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \operatorname{realPart}\left(\operatorname{fourierLaplace}\left(phi, xi\right)\right) + \frac{theta}{(xi)^{2} + (a)^{2}}, residual\right) = 0 \land \left(\operatorname{map}\left((xi: \operatorname{Real}\left(\right) \mapsto -xi), residual\right) = residual \land completion = \operatorname{smul}\left(\operatorname{ofReal}\left(\frac{\operatorname{toReal}\left(lambda\right)}{2 \cdot \operatorname{pi}\left(\right)}\right), \operatorname{volume}\left(\operatorname{Real}\left(\right)\right)\right) + residual\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists I \in Type, finiteI \in \operatorname{Fintype}\left(I\right), point \in I \to \operatorname{Real}\left(\right), weight \in I \to \operatorname{ENNReal}\left(\right), weightZero \in \operatorname{ENNReal}\left(\right),\; \left(\forall r \in I,\; weight\left(r\right) \ne \operatorname{infinity}\left(\right)\right) \land \left(weightZero \ne \operatorname{infinity}\left(\right) \land \left(\left(\forall r \in I,\; \left((point\left(r\right))^{2} + (a)^{2}\right) \cdot \operatorname{fourierLaplace}\left(phi, point\left(r\right)\right) + theta = 0 \land \left((-point\left(r\right))^{2} + (a)^{2}\right) \cdot \operatorname{fourierLaplace}\left(phi, -point\left(r\right)\right) + theta = 0\right) \land completion = \operatorname{smul}\left(\operatorname{ofReal}\left(\frac{\operatorname{toReal}\left(lambda\right)}{2 \cdot \operatorname{pi}\left(\right)}\right), \operatorname{volume}\left(\operatorname{Real}\left(\right)\right)\right) + \operatorname{sum}\left(r, I, \operatorname{smul}\left(weight\left(r\right), \operatorname{dirac}\left(point\left(r\right)\right) + \operatorname{dirac}\left(-point\left(r\right)\right)\right)\right) + \operatorname{smul}\left(weightZero, \operatorname{dirac}\left(0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/FiniteAtomicBudgetedCompletion.finite_atomic_budgeted_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complementary contact support places the residual measure on the real zeros of the canonical entire contact function. Positive pressure and Schwartz decay confine those zeros to a compact interval.

Analytic isolation makes the real contact set finite. Evenness then splits every singleton mass equally between its positive and negative Dirac representatives, including the possible zero atom.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/FiniteAtomicBudgetedCompletion.finite_atomic_budgeted_completion`
- Dependency: [D5/S3/Weil/TestFunctions/ActiveFiniteContactCompletion](ActiveFiniteContactCompletion.md)
- Dependency: [D5/S3/Weil/TestFunctions/ComplementaryContactSupport](ComplementaryContactSupport.md)
