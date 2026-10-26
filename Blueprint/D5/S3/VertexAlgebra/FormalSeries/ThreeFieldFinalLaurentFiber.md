# Finite inverse-binomial coefficient fibers

## Abstract

Finite inverse-binomial coefficient fibers

**Definition 1.1 (LaurentIndex).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.LaurentIndex`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.LaurentIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Four nonnegative indices j,q,h,l, grouped as ((j,q),(h,l)).

**Definition 1.2 (laurentInput).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentInput`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed input exponents are e0+k-j-h, e1+2k+j-q+h-l, and e2+a0+a1+a2+q+l.

**Definition 1.3 (LaurentAdmissible).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.LaurentAdmissible`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.LaurentAdmissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The split satisfies h<=q and all three signed input exponents are nonnegative.

**Theorem 1.4 (laurent_bounds).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurent_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurent_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Admissibility bounds j+h by e0+k and q+l by e0+e1+3k. Summing the first two input coordinates gives the exact second balance; the third input has the resulting finite upper bound.

**Definition 1.5 (laurentFiber).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentFiber`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite product of ranges filtered by exactly the signed admissibility predicate.

**Theorem 1.6 (mem_laurentFiber_iff).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.mem_laurentFiber_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.mem_laurentFiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible quadruple lies in the containing box, so membership in the finite fiber is equivalent to admissibility.

**Definition 1.7 (laurentWeight).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentWeight`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar is binom(-k,j) binom(-a0,q) choose(q,h) binom(-a1,l). The middle splitting introduces no additional sign.

**Definition 1.8 (laurentTerm).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentTerm`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the signed numerator coefficient at laurentInput by laurentWeight when h<=q; otherwise return zero.

**Definition 1.9 (laurentCoefficient).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finitary sum of the inverse-factor terms defines the Laurent coefficient for an arbitrary, possibly infinite, three-variable formal power series over any commutative complex algebra.

**Theorem 1.10 (laurentCoefficient_eq_sum).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support of the term function lies in laurentFiber, yielding the displayed literal finite sum with the same weights and signed inputs.

**Theorem 1.11 (laurentCoefficient_zero).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient vanishes if any cumulative cone coordinate is negative: e0+k, e0+e1+3k, or e0+e1+e2+3k+a0+a1+a2. Individual raw exponents may be negative.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.LaurentAdmissible`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.LaurentIndex`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient_eq_sum`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentCoefficient_zero`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentFiber`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentInput`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentTerm`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurentWeight`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.laurent_bounds`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber.mem_laurentFiber_iff`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision](SupportedThreeFieldCollision.md)
- Dependency: [D5/S3/VertexAlgebra/StateFieldResidueReconstruction](../StateFieldResidueReconstruction.md)
