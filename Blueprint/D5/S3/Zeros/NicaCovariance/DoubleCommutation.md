# Coprime Double Commutation

## Abstract

Coprime address translations doubly commute and their divisible subspaces meet at the product address.

**Theorem 1.1 (Coprime backward and forward shifts commute).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{Coprime}(\operatorname{primeAxisEncoding}(u), \operatorname{primeAxisEncoding}(v)) \Rightarrow \operatorname{backwardShiftCLM}(u) \circ \operatorname{forwardTranslationCLM}(v) = \operatorname{forwardTranslationCLM}(v) \circ \operatorname{backwardShiftCLM}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/DoubleCommutation.backward_shift_comp_forward_translation_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a coordinate divisible by v, both compositions recover the same coefficient after swapping the normalized additions of u and v. At every other coordinate, coprimality cancels the u factor from the divisibility test, so both zero-extended translations vanish.

**Theorem 1.2 (Coprime forward translations doubly commute).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{Coprime}(\operatorname{primeAxisEncoding}(u), \operatorname{primeAxisEncoding}(v)) \Rightarrow \operatorname{adjoint}(\operatorname{forwardTranslationCLM}(u)) \circ \operatorname{forwardTranslationCLM}(v) = \operatorname{forwardTranslationCLM}(v) \circ \operatorname{adjoint}(\operatorname{forwardTranslationCLM}(u))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/DoubleCommutation.adjoint_forward_translation_comp_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjoint of forward translation by u is the backward shift by u. The double-commutation identity is therefore the preceding coprime commutation theorem after rewriting that adjoint, with no additional coordinate argument.

**Theorem 1.3 (Coprime divisible subspaces meet at the product address).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{Coprime}(\operatorname{primeAxisEncoding}(u), \operatorname{primeAxisEncoding}(v)) \Rightarrow \operatorname{divisibleSubspace}(u) \operatorname{inf} \operatorname{divisibleSubspace}(v) = \operatorname{divisibleSubspace}(\operatorname{normalizedTableAdd}(u, v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/DoubleCommutation.divisibleSubspace_inf_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the meet means that a coefficient family vanishes away from both divisibility supports. For coprime encoded addresses, divisibility by their product is equivalent to simultaneous divisibility by u and v, so the meet is exactly the subspace at their normalized table sum.

## References

- Truth anchor: `D5/S3/Zeros/NicaCovariance/DoubleCommutation.adjoint_forward_translation_comp_of_coprime`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/DoubleCommutation.backward_shift_comp_forward_translation_of_coprime`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/DoubleCommutation.divisibleSubspace_inf_of_coprime`
- Dependency: [D5/S3/Zeros/NicaCovariance/SemigroupRelations](SemigroupRelations.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint](../ShiftOperators/BackwardShiftAdjoint.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry](../ShiftOperators/BackwardShiftCoisometry.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/BackwardShiftOperator](../ShiftOperators/BackwardShiftOperator.md)
- Dependency: [D5/S3/Zeros/ShiftOperators/ShiftRangeProjection](../ShiftOperators/ShiftRangeProjection.md)
