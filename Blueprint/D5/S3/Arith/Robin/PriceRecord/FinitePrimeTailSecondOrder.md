# Native scoped implementation

## Abstract

Finite prime-square Abel tail through three logarithmic coefficients.

Native compiled scope only. The estimate is finite in both endpoints and uses the exact strict/inclusive prime interval. It does not claim an infinite tail, final16, or RH.

**Definition 1.1 (Retained endpoint polynomial).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder.tailPolynomial`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder.tailPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tailPolynomial x is 1/(x log x)-1/(x log(x)^2)+2/(x log(x)^3), with both endpoint values retained.

**Theorem 1.2 (Uniform finite two-endpoint estimate).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder.finite_square_three_terms`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder.finite_square_three_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists X>1 such that every X<=y<=z satisfies abs(squareSum y z-(tailPolynomial y-tailPolynomial z)) <= 130/(y*log(y)^4). The proof combines the coefficient-25 four-term envelope, both endpoint errors, the finite integral error, and the exact K4/K5 model corrections.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder.finite_square_three_terms`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FinitePrimeTailSecondOrder.tailPolynomial`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
