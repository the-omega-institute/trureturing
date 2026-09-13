# Extended Farkas Alternative

## Abstract

The Farkas alternative holds for extended coefficients under four infinity restrictions.

**Theorem 1.1 (Alternative for extended coefficients).**

Lean statement: `D5/S3/Analytic/Convexity/ExtendedFarkas.extended_farkas`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/ExtendedFarkas.extended_farkas` (`✓ std3`). ∎

*Citation.* Martin Dvorak and Vladimir Kolmogorov (2026). *Duality theory in linear optimization and its extensions -- formally verified*. DOI: [10.46298/afm.14253](https://doi.org/10.46298/afm.14253).

*Commentary.*

Let F be a linearly ordered field and I and J arbitrary finite types, with decidable equality on I. Extend F is WithBot (WithTop F). Negative infinity absorbs every sum. The action of every nonnegative scalar on negative infinity is negative infinity; zero acting on positive infinity is zero, and a positive scalar acting on positive infinity is positive infinity. Finite coefficients use ordinary field multiplication.

For A : Matrix I J (Extend F) and b : I → Extend F, assume that no row of A contains both infinities, no column contains both infinities, no row containing positive infinity has a positive-infinite bound, and no row containing negative infinity has a negative-infinite bound.

Exactly one alternative holds: there exists x : J → NNeg F with A ₘ* x ≤ b; or there exists y : I → NNeg F with −Aᵀ ₘ* y ≤ 0 and b ᵥ⬝ y < 0. Each heterogeneous product is the finite sum of the nonnegative weights acting on the extended coefficients.

The construction removes tautological rows and columns forced to zero, applies the finite inequality alternative to the remaining field coefficients, and restores witnesses in both directions. The infinity restrictions justify the zero weights and the restored inequalities.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/ExtendedFarkas.extended_farkas`
- Dependency: [D5/S3/Analytic/Convexity/FarkasAlternative](FarkasAlternative.md)
