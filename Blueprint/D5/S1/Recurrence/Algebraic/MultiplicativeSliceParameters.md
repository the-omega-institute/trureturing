# Multiplicative Slice Parameters

## Abstract

Multiplicative Slice Parameters.

**Definition 1.1 (The coefficient equations).**

Lean statement: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.ForcedEquations`

*Formalization.* `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.ForcedEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all positive integers m and n, the coefficients satisfy (1 - p(m))(1 - p(n))c(m,n) = 1 - p(m+n) and p(m)p(n)c(m,n) = -p(m+n).

**Definition 1.2 (The geometric family).**

Lean statement: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.GeometricFamily`

*Formalization.* `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.GeometricFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real parameter t different from 1 and -1 gives p(m) = t^m/(t^m - 1) and c(m,n) = -((t^m - 1)(t^n - 1))/(t^(m+n) - 1) at positive indices. The parameter zero gives p(m) = 0 and c(m,n) = 1.

**Definition 1.3 (The unit family).**

Lean statement: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.UnitFamily`

*Formalization.* `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.UnitFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every positive index p(m) = 1, and at every pair of positive indices c(m,n) = -1.

**Theorem 1.4 (Exhaustive classification).**

Lean statement: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two coefficient equations hold if and only if the coefficients belong to the geometric family or the unit family. Any zero entry at a positive index forces all positive entries of p to be zero; any unit entry forces them all to be one. In every other case all positive entries avoid both zero and one. Values at index zero are unrestricted.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.ForcedEquations`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.GeometricFamily`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.UnitFamily`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.result`
