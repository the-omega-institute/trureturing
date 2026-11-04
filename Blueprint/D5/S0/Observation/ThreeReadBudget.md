# Three-Read Budget Nullspace

## Abstract

The unbounded three-read budget kills the visible three-time aggregate.

**Theorem 1.1 (Unbounded rewrites force the three-read image into the bilinear nullspace).**

Lean statement: `D5/S0/Observation/ThreeReadBudget.three_read_budget_nullspace`

*Proof.* Machine-checked in Lean as `D5/S0/Observation/ThreeReadBudget.three_read_budget_nullspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an arbitrary real module, R an arbitrary real bilinear reading, and U an arbitrary real linear map. Assume that for every f, g, and natural rewrite multiplier n, 2 R(f, U g + n (I + U + U²) g) is at most R(f,f) + R(g,g).

The n = 0, g = 0 instance gives nonnegativity of every quadratic self-reading. For a fixed f and g, linearity expands the budget as an affine function of n. If R(f,(I + U + U²)g) were positive, the Archimedean property supplies a natural n whose positive slope exceeds the fixed budget, contradicting the inequality. Applying the same upper bound to -f gives the opposite sign, so the coefficient is zero.

Thus range(I + U + U²) is contained in the vectors h with R(f,h) = 0 for every f. This is the initial necessity subclaim of C133 Theorem 2.2. The opposite-slot identity R(h,f) = 0, symmetry, U-invariance, the quotient construction, the converse, and the later complex classification are outside this result. No invertibility, symmetry, positivity, or finite dimension is assumed.

## References

- Truth anchor: `D5/S0/Observation/ThreeReadBudget.three_read_budget_nullspace`
