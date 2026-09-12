# Finite Attainment for Extended Linear Programs

## Abstract

Both feasible valid extended linear programs attain finite opposite values.

**Theorem 1.1 (Finite opposite attained values).**

Lean statement: `D5/S3/Analytic/Convexity/FiniteStrongDuality.strong_duality_of_both_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/FiniteStrongDuality.strong_duality_of_both_feasible` (`✓ std3`). ∎

*Citation.* Martin Dvorak and Vladimir Kolmogorov (2026). *Duality theory in linear optimization and its extensions -- formally verified*. DOI: [10.46298/afm.14253](https://doi.org/10.46298/afm.14253).

*Commentary.*

Let F be a linearly ordered field and I and J arbitrary finite row and column types with decidable equality. An ExtendedLP contains a matrix A, bound vector b and objective vector c with coefficients in Extend F; its variables are nonnegative elements of F. It minimizes the sum c ᵥ⬝ x subject to A ₘ* x ≤ b.

ValidELP requires all six restrictions: no row or column of A mixes the two infinities; a negative-infinite bound cannot share a row with a negative-infinite matrix entry; a negative-infinite objective coefficient cannot share a column with a positive-infinite matrix entry; a positive-infinite bound cannot share a row with a positive-infinite matrix entry; and a positive-infinite objective coefficient cannot share a column with a negative-infinite matrix entry.

Dualization sends (A,b,c) to (−Aᵀ,c,b). A program is feasible when it reaches some extended objective value other than positive infinity. If a valid program P and its dual are both feasible, there exists r : F such that P reaches the finite value toE(−r) and its dual reaches the finite value toE(r). Reaches includes an actual feasible vector realizing the indicated objective value.

The augmented system constructs primal and dual witnesses whose finite objectives sum to at most zero. Weak duality supplies the opposite inequality, giving equality and the stated opposite values. The proof retains the recession argument needed to exclude a zero scaling coefficient in the augmented alternative.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/FiniteStrongDuality.strong_duality_of_both_feasible`
- Dependency: [D5/S3/Analytic/Convexity/ExtendedFarkas](ExtendedFarkas.md)
