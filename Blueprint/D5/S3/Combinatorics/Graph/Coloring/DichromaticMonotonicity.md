# Crew's dichromatic monotonicity conjecture

## Abstract

Positive transfers along singleton splits give real dichromatic monotonicity.

Crew, Keller, Kuehr, Lin, Monroy Rodríguez and Williams pose Conjecture 2 in Section 8.1 of Properties of the Dichromatic Polynomial. https://arxiv.org/html/2611.13273v1#Thmconj2

**Definition 1.1 (The normalized dichromatic polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity.normalizedDichromaticPolynomial`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity.normalizedDichromaticPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide the polynomial by the nth power of the real palette parameter, where n is the vertex count. At order one and palette parameter zero, evaluate the derivative of the polynomial at zero. The order-one polynomial is either the variable or the zero polynomial, so this fills the removable endpoint with the corresponding constant value. The order-zero quotient is constant one.

**Theorem 1.2 (Weak monotonicity on the closed ray).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity.normalizedDichromaticPolynomial_monotoneOn`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity.normalizedDichromaticPolynomial_monotoneOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite digraph of order n and real palette parameters a and b with n − 1 ≤ a ≤ b, the normalized value at a is at most the normalized value at b. The derivative of each partition weight is its incoming transfer sum minus its outgoing transfer sum. For a target singleton and any distinct recipient block, merging the two reconstructs the unique source of that marked split. The finite incoming sum over recipients cancels the formal outgoing term at the singleton. Grouping the remaining signed coefficients by block subsets gives the falling factorial derivative. The beta-moment bound makes each genuine transfer positive. Acyclicity is preserved by splitting, so summation over acyclic partitions gives a nonnegative derivative. Continuity gives the closed endpoint at orders at least two, and the extended quotient is constant at smaller orders.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity.normalizedDichromaticPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticMonotonicity.normalizedDichromaticPolynomial_monotoneOn`
- Dependency: [D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion](DichromaticPartitionExpansion.md)
