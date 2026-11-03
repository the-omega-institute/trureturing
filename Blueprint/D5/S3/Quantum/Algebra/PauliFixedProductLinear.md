# A strict certificate for the same fixed-product Pauli realization

## Abstract

The full actual Pauli residual gives a strictly improved linear certificate on the literal nonempty small-parameter interval.

Use the fixed local spin products, fixed cross channel, tensor product and positive inner products of PauliFixedProductFamily. Only the actual local and joint actions vary with real t. Epsilon is defined as the square root of the complete actual reportSquared(t), including all 4096 ordered product-basis triples and every output coordinate. The full residual identity gives epsilon=12sqrt(2) absolute t. The exact local action constant is d=sqrt(1+t squared), and the original constants u=1, ell=sqrt(2), k=1 give C=1+2sqrt(2), with uniform action gap sqrt(2). No change of product, inner product, report normalization or time scale occurs.

Define L=2 C d epsilon/(sqrt(2)-2 C epsilon). The old bound is the minimum of d and (C epsilon+sqrt(C squared epsilon squared+4 C d epsilon))/2, retaining its independent cap. The endpoint is exactly 1/(192sqrt(2)C). The strict comparison uses the actual epsilon computed from the original maps; neither domination nor improvement is assumed.

**Theorem 1.1 (The literal interval contains a nonzero parameter).**

$$\exists t, 0<\Vert t\Vert<\frac{1}{192\sqrt{2}C}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductLinear.small_interval_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C and the endpoint are strictly positive. Half of the endpoint is an explicit positive member. The zero endpoint remains in the ambient family but is excluded from this strict inequality interval.

**Theorem 1.2 (The actual defect is dominated and the old root and cap are both strictly larger).**

$$\forall t, 0<\Vert t\Vert<\frac{1}{192\sqrt{2}C} \Rightarrow \frac{\Vert t\Vert}{2}\le\operatorname{L}(t)<\operatorname{old}(t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductLinear.actual_strict_improvement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t in the stated interval, the original denominator is strictly positive, the actual diagonal map is nonzero and the unit generator is nonzero. Every local unit vector has actual diagonal defect at most L(t), and the attained maximum absolute t divided by two is at most L(t). The same L(t) is strictly smaller than the original old(t), including its cap.

The exact report implies zero less than epsilon less than 1/(16C), and the interval also gives absolute t less than one. Thus 1 at most d at most sqrt(2). With x=C epsilon, the linear certificate is at most 4x, strictly less than sqrt(x), at most the old quadratic root, and strictly below one at most d. Domination of the actual defect follows directly from its exact norm formula and the explicit positive-denominator expression. This proves the family-specific comparison without assuming or establishing a general stability theorem for arbitrary M and Gamma.

At t=0 the same products and actions still satisfy the realization contract, epsilon is zero, every local diagonal defect vanishes and the unit generator is zero. The action remains nonzero on spatial labels, and the positive action gap stays sqrt(2). These are algebraic assertions about this finite-dimensional realization, without a conclusion about physical acquisition, general noisy reconstruction or a common quantum representation for other systems.

**Theorem 1.3 (An actual member has activity and strict improvement together).**

$$\exists t, 0<\Vert t\Vert<\frac{1}{192\sqrt{2}C}, \frac{\Vert t\Vert}{2}\le\operatorname{L}(t)<\operatorname{old}(t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductLinear.nonempty_improvement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Half of the positive endpoint gives an actual parameter with a nonzero diagonal defect and a nonzero unit generator. Its attained defect maximum is dominated by the linear certificate, which is strictly smaller than the original capped root. The same existential member includes the entire all-input realization contract, exact defect and local constants, actual action and label Grams, their spectra and the support gap. All these properties hold simultaneously for the same fixed-product realization.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductLinear.actual_strict_improvement`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductLinear.nonempty_improvement`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductLinear.small_interval_nonempty`
- Dependency: [D5/S3/Quantum/Algebra/PauliLocalBounds](PauliLocalBounds.md)
