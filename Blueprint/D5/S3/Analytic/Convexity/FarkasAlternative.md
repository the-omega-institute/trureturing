# Finite Farkas Alternatives

## Abstract

The finite Bartl recursion supplies Farkas alternatives over ordered scalars.

**Theorem 1.1 (Finite Bartl alternative).**

Lean statement: `D5/S3/Analytic/Convexity/FarkasAlternative.fin_farkas_bartl`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/FarkasAlternative.fin_farkas_bartl` (`✓ std3`). ∎

*Citation.* Martin Dvorak and Vladimir Kolmogorov (2026). *Duality theory in linear optimization and its extensions -- formally verified*. DOI: [10.46298/afm.14253](https://doi.org/10.46298/afm.14253).

*Commentary.*

Let R be a linearly ordered division ring, V a linearly ordered additive commutative group with an R-module structure whose scalar action is monotone for nonnegative scalars, and W an additive commutative group with an R-module structure. For every natural number n, linear map A from W to Fin n → R, and linear map b from W to V, exactly one of the following alternatives holds.

There exists a componentwise nonnegative vector x : Fin n → V such that, for every w : W, the sum of A(w,j) acting on x(j) equals b(w); or there exists y : W such that A(y) is componentwise nonnegative and b(y) is strictly negative. The Lean statement expresses exclusivity and exhaustiveness by inequality of the two propositions.

The recursion either appends a zero coefficient to the shorter representation, or rescales a separating direction and restores the last coefficient after eliminating its coordinate. No commutativity of multiplication in R is assumed.

**Theorem 1.2 (Inequality alternative).**

Lean statement: `D5/S3/Analytic/Convexity/FarkasAlternative.inequality_farkas_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/FarkasAlternative.inequality_farkas_neg` (`✓ std3`). ∎

*Citation.* Martin Dvorak and Vladimir Kolmogorov (2026). *Duality theory in linear optimization and its extensions -- formally verified*. DOI: [10.46298/afm.14253](https://doi.org/10.46298/afm.14253).

*Commentary.*

For arbitrary finite row and column types I and J over a linearly ordered field F, with decidable equality on I, exactly one alternative holds: a nonnegative x satisfies A x ≤ b; or a nonnegative y satisfies −Aᵀ y ≤ 0 and b · y < 0. The coordinate interpretation of the Bartl theorem and the addition of nonnegative slack variables give this interface.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/FarkasAlternative.fin_farkas_bartl`
- Truth anchor: `D5/S3/Analytic/Convexity/FarkasAlternative.inequality_farkas_neg`
