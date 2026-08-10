# Almost Additivity of the Contraction Reading

## Abstract

The contraction reading is almost additive over prime exponents.

**Theorem 1.1 (The contraction reading is almost additive).**

$$\forall m,n\ge1,\quad\lvert\operatorname{lambdaMinus}(mn)-\operatorname{lambdaMinus}(m)-\operatorname{lambdaMinus}(n)\rvert\leq\log(\operatorname{rad}(\gcd(m,n)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/AlmostAdditivity.lambdaMinus_almost_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural numbers m and n, the contraction reading of their product differs from the sum of their separate readings by at most the natural logarithm of the product of the distinct primes common to m and n. The module defines that distinct-prime product explicitly and defines the reading as a finite sum over prime exponents, so the displayed bound formalizes the source atom without hiding either arithmetic object behind an assumption.

The proof expands the factorization of mn and isolates the intersection of the two prime supports. Outside that intersection one exponent is zero, so the local defect vanishes. On a common prime axis the existing three-valued deficit theorem says that the defect has absolute value at most one. The triangle inequality then bounds the weighted sum by the sum of logarithms of the common primes, and the logarithm-of-a-finite-product identity turns that sum into the stated radical bound.

This is not a thin wrapper around an exact library theorem. Mathlib supplies the prime-factorization multiplication law, the GCD support identity, the finite-sum triangle inequality, and the logarithm-of-product lemma; the repository's contraction-face deficit result provides the decisive local bound. Searches found no library declaration for the assembled almost-additivity statement.

## References

- Truth anchor: `D5/S1/Deficit/AlmostAdditivity.lambdaMinus_almost_additive`
- Dependency: [D5/S1/Deficit/DeficitThreeValued](DeficitThreeValued.md)
