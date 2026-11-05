# Bala's Complex-Shift Determinant Conjecture

## Abstract

A one-by-one determinant refutes the arbitrary complex shift in OEIS A086205.

**Definition 1.1 (The generalized-binomial determinant).**

$$\forall n \in \mathbb{N},\; \forall z \in \mathbb{C},\; \operatorname{shiftedDet}\left(n, z\right) = \operatorname{det}\left([\operatorname{choose}\left(\left(i + 1\right)^{2} + z, j + 1\right)]_{i, j \in \operatorname{Fin}\left(n\right)}\right)$$

*Formalization.* `D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.shiftedDet` (`✓ std3`).

*Citation.* Peter Bala; OEIS Foundation (2023). *OEIS A086205: arbitrary complex shift of a binomial determinant*. URL: <https://oeis.org/A086205>.

*Commentary.*

Rows and columns run from one through n. For complex w and natural k, choose(w,k) is the falling factorial w(w-1)...(w-k+1) divided by k!, as given by Ring.choose and Ring.choose_eq_smul. The product for k = 0 is one. At n = 0 the matrix is empty and its determinant is one.

**Definition 1.2 (The arbitrary-complex-shift assertion).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; \forall z \in \mathbb{C},\; \operatorname{shiftedDet}\left(n, z\right) = \operatorname{shiftedDet}\left(n, 0\right)\right)$$

*Formalization.* `D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.claim` (`✓ std3`).

*Citation.* Peter Bala; OEIS Foundation (2023). *OEIS A086205: arbitrary complex shift of a binomial determinant*. URL: <https://oeis.org/A086205>.

*Commentary.*

The unshifted determinant defines A086205(n). The conjecture asserts equality for every natural n, including zero, and every complex shift z.

**Theorem 1.3 (The assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; OEIS Foundation (2023). *OEIS A086205: arbitrary complex shift of a binomial determinant*. URL: <https://oeis.org/A086205>.

*Commentary.*

For n = 1 and z = 1 the only entry is choose(2,1) = 2, whereas the unshifted entry is choose(1,1) = 1. A one-by-one determinant equals its entry. The asserted equality would imply 2 = 1 in the complex numbers, refuting the printed universal assertion.

## References

- Truth anchor: `D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.claim`
- Truth anchor: `D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.result`
- Truth anchor: `D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.shiftedDet`
