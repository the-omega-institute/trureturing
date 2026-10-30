# Pisano period and Fibonacci matrix order

## Abstract

The scalar Fibonacci period is the order of the Fibonacci companion matrix.

**Theorem 1.1 (Scalar periods and returns of consecutive values).**

Lean statement: `D5/S3/Arith/PisanoMatrixBridge.period_iff_return`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PisanoMatrixBridge.period_iff_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural modulus n and shift k, equality of all Fibonacci residues at indices m+k and m is equivalent to the k-th iterate of the step (x,y) mapped to (y,x+y) returning (0,1). The statement includes m=0 and m=1 and imposes no positivity on k.

**Theorem 1.2 (Exact scalar-to-matrix period bridge).**

Lean statement: `D5/S3/Arith/PisanoMatrixBridge.pisanoPeriod_eq_matrix_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PisanoMatrixBridge.pisanoPeriod_eq_matrix_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural modulus n greater than one, the least positive period of the Fibonacci residues equals the multiplicative order of the matrix [[1,1],[1,0]] over ZMod n. The proof identifies the returning pair (F_k,F_(k+1)) with the power of the reduced golden unit and uses the injective golden multiplication matrix homomorphism to transfer return exponents exactly.

## References

- Truth anchor: `D5/S3/Arith/PisanoMatrixBridge.period_iff_return`
- Truth anchor: `D5/S3/Arith/PisanoMatrixBridge.pisanoPeriod_eq_matrix_order`
- Dependency: [D5/S3/Arith/GoelPisanoRatioRefutation](GoelPisanoRatioRefutation.md)
- Dependency: [D5/S3/Arith/GoldenFibonacciModulusPeriod](GoldenFibonacciModulusPeriod.md)
