# Binary XOR Transformation Tightness

## Abstract

Incompressible masks make binary XOR transformation prices tight within a logarithmic gap.

**Theorem 1.1 (An incompressible XOR mask attains the description bound).**

$$\begin{gathered}\forall c: \mathbb{N}, M: \operatorname{BinaryDescriptionMachine}\left(c\right), l: \mathbb{N},\\{}\exists r: \operatorname{Fin}\left(l\right) \to \operatorname{Fin}\left(2\right),\\{}l \leq K_{M,l}(r) \land\\{}\operatorname{Involutive}\left(\operatorname{pointwiseXor}\left(r\right)\right) \land\\{}\operatorname{pointwiseXor}\left(r, 0\right) = r \land\\{}l - {2 log_2(l + 1) + c} \leq K_{M,l}(r) - K_{M,l}(0) \land\\{}Ktransform_{M,l}(\operatorname{pointwiseXor}\left(r\right)) \leq l + c \land\\{}l - {2 log_2(l + 1) + c + c} \leq Ktransform_{M,l}(\operatorname{pointwiseXor}\left(r\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/XorTransformationTightness.xor_transformation_description_tight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binder M : BinaryDescriptionMachine(c) is the exact Lean interface for one fixed binary description machine. Its object and transformation systems use binary-list code length, object realization is functional, and it supplies concrete XOR, zero-string, and application compilers with the displayed fixed and logarithmic overheads.

There are 2^l length-l binary strings but only 2^l - 1 binary programs shorter than l. Functionality therefore leaves a mask r with object description complexity at least l. This is a counting construction, not an incompressibility premise.

Pointwise addition in Fin 2 is the canonical bitwise XOR. It is involutive and sends the zero string to r. The concrete zero compiler bounds K(0^l) by 2 log_2(l+1)+c, giving the public information-difference lower bound.

The concrete XOR compiler gives K_transform(xor_r) <= l+c. Applying the existing transformation-description compiler to xor_r(0)=r yields the opposite lower bound l-[2 log_2(l+1)+2c]. Thus the witness name price is squeezed to within the source's logarithmic gap.

Pinned Mathlib supplies finite binary carriers and arithmetic but no Kolmogorov-complexity or incompressible-XOR theorem. The repository search found only the imported general transformation bound, whose own projection marks this tightness construction as residual.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/XorTransformationTightness.xor_transformation_description_tight`
- Dependency: [D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound](TransformationDescriptionBound.md)
