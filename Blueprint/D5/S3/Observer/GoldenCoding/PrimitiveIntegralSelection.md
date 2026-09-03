# Primitive Integral Selection

## Abstract

Trace and signed determinant classify a nonnegative integral binary matrix up to simultaneous coordinate swap.

**Theorem 1.1 (Trace one and determinant minus one select the Fibonacci matrix).**

$$\begin{aligned}\forall M: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{N}),\\{}(\operatorname{trace}(M) = 1 \land \operatorname{det}(\operatorname{cast}(\mathbb{Z}, M)) = -1) \Rightarrow\\{}(M = \operatorname{matrix2}(1, 1, 1, 0) \lor M = \operatorname{matrix2}(0, 1, 1, 1)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/PrimitiveIntegralSelection.primitive_integral_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace condition leaves the two possible diagonal orders. In either order, the signed determinant condition forces the product of the off-diagonal natural entries to equal one.

Both off-diagonal entries are therefore one. The two displayed matrices differ by simultaneously swapping the coordinates.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/PrimitiveIntegralSelection.primitive_integral_selection`
