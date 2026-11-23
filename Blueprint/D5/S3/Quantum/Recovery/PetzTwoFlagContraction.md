# Sharp complex two-flag contraction bound

## Abstract

The complex two-flag objective attains its maximum at the two opposite real corners.

**Theorem 1.1 (Exact radial and phase deficiency).**

Lean statement: `D5/S3/Quantum/Recovery/PetzTwoFlagContraction.twoFlag_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzTwoFlagContraction.twoFlag_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m ≥ 0, C > 0, f > 0 and g > 0. For real w and v, write A = 8m + f(f + g)/C − w and B = 8m + g(f + g)/C − v. Assume A ≥ 0, B ≥ 0 and A + B > 0. Take complex y and z with |y|² ≤ 1 and |z|² ≤ 1.

The objective is w(1 − |y|²) + v(1 − |z|²) + 4m|y − z|² + (f Re y − g Re z)²/C. It is at most 16m + (f + g)²/C, with equality exactly at (y,z) = (1,−1) or (−1,1).

The upper bound minus the objective equals A(1 − |y|²) + B(1 − |z|²) + 4m|y + z|² + f(f + g)(Im y)²/C + g(f + g)(Im z)²/C + fg(Re y + Re z)²/C. All six terms are nonnegative.

At equality, the three phase squares force Im y = Im z = 0 and Re y + Re z = 0. The moduli are then equal, so the radial terms sum to (A + B)(1 − |y|²). Since A + B > 0, equality requires |y|² = |z|² = 1.

**Theorem 1.2 (The four-slot Hermitian contraction).**

Lean statement: `D5/S3/Quantum/Recovery/PetzTwoFlagContraction.matrix_twoFlag_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzTwoFlagContraction.matrix_twoFlag_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Index a Hermitian matrix Y by pairs (b,s) with b and s in {0,1}. Assume I − Y² is positive semidefinite and assign nonnegative row weights a(b,s). In each row the partner column is (1 − b,s). Take y = Y((0,0),(1,0)) and z = Y((0,1),(1,1)).

Use the same conditions on m, C, f and g, with w = a(0,0) + a(1,0) and v = a(0,1) + a(1,1) in the margins A ≥ 0, B ≥ 0 and A + B > 0. Replace the two weighted slack terms in the scalar objective by the sum of a(b,s) times the squared moduli of all nonpartner entries of row (b,s). This matrix objective is at most 16m + (f + g)²/C. Equality holds exactly when the two selected entries are (1,−1) or (−1,1).

The diagonal of I − Y² bounds the full sum of squared moduli in each row by one. Hermiticity identifies the moduli of each pair of partner entries. At a corner the two partner pairs exhaust all four row bounds, so all nonpartner entries vanish.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzTwoFlagContraction.matrix_twoFlag_maximum`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzTwoFlagContraction.twoFlag_maximum`
