# Primitive Step-Two Magnus Logarithm

## Abstract

The step-two tensor logarithm is an antisymmetric primitive coordinate.

**Definition 1.1 (Universal tensor commutator).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensorCommutator`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensorCommutator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-two bracket is the difference of the two ordered pure tensors before any operator representation is selected.

**Definition 1.2 (Doubled primitive Magnus coordinate).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubledPrimitiveMagnus`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubledPrimitiveMagnus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the tensor square of degree one from doubled degree two extracts the step-two logarithmic component.

**Definition 1.3 (Degree-two primitive antisymmetry).**

Lean statement: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.IsPrimitiveDegreeTwo`

*Formalization.* `D5/S3/Observer/Chronology/PrimitiveMagnusLog.IsPrimitiveDegreeTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A degree-two tensor is primitive in the truncated sense when the canonical factor flip negates it.

**Theorem 1.4 (Finite chronological logarithms are primitive).**

$$\forall f, L, \operatorname{IsPrimitiveDegreeTwo}(\operatorname{doubledPrimitiveMagnus}(\operatorname{chronologicalTensorSignature}(f, L))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimitiveMagnusLog.chronological_primitive_magnus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tensor commutators are primitive, and a single-event logarithm has no degree-two part; the tensor BCH law adds the commutator of the degree-one coordinates under Chen multiplication, and concatenation therefore obeys the Chen-to-BCH append law, with two events giving exactly the tensor bracket and the swap negating it.

For any step-two group-like signature the doubled Magnus coordinate is antisymmetric (primitive), so by the frozen Hopf balance every finite chronological logarithm is a primitive degree-two coordinate.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.IsPrimitiveDegreeTwo`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.chronological_primitive_magnus`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.doubledPrimitiveMagnus`
- Truth anchor: `D5/S3/Observer/Chronology/PrimitiveMagnusLog.tensorCommutator`
- Dependency: [D5/S3/Observer/Chronology/TruncatedTensorHopf](TruncatedTensorHopf.md)
