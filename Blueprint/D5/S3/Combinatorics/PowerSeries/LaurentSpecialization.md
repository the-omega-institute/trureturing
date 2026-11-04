# LaurentSpecialization

## Abstract

Support-controlled specialization of Laurent coefficient series.

For a source monomial q^n T^k, shift the Laurent row by T^n. On the cone k >= -n the row becomes an ordinary polynomial, so evaluation at q^r followed by outer evaluation at q^(a+1) is legitimate. The final degree is (a+1+r)n+rk. Truncation is used only to define a continuous additive map on the ambient space; multiplicativity is proved on admissible inputs by the injective polynomial-to-Laurent map. The weighted Jacobi module is the live consumer. This construction reuses Mathlib LaurentPolynomial.trunc and PowerSeries.eval₂Hom, with their complete discrete-coefficient topology. It does not assert an unrestricted Laurent substitution.

**Definition 1.1 (lift).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Shift row n by T^n and take its nonnegative polynomial part.

**Definition 1.2 (Admissible).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.Admissible`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The shifted series lies in the image of genuine polynomial coefficients; this records the support cone.

**Theorem 1.3 (lift_of_map).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_of_map`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_of_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

A polynomial preimage is reconstructed exactly by truncation.

**Theorem 1.4 (map_lift).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.map_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.map_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

For admissible input, lifting loses no Laurent coefficient.

**Theorem 1.5 (admissible_one).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The identity series belongs to the support cone.

**Theorem 1.6 (admissible_mul).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The support condition is closed under multiplication.

**Theorem 1.7 (lift_mul).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The polynomial lift is multiplicative on admissible inputs.

**Theorem 1.8 (lift_one).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The lift preserves the identity, used by finite products.

**Definition 1.9 (liftAdd).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.liftAdd`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.liftAdd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The lift is additive on the full ambient coefficient space.

**Theorem 1.10 (continuous_lift).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.continuous_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.continuous_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Each lifted row depends continuously on just its original row.

**Definition 1.11 (diagonal).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.diagonal`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.diagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Evaluate the polynomial variable at q^r and the outer variable at q^(a+1).

**Definition 1.12 (specialize).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The composite row shift and positive evaluation map.

**Definition 1.13 (specializeAdd).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specializeAdd`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specializeAdd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The continuous additive specialization used to transfer complete integer sums.

**Theorem 1.14 (specialize_mul).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Admissible products specialize multiplicatively.

**Theorem 1.15 (specialize_one).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The specialization preserves one, including empty finite products.

**Theorem 1.16 (continuous_specialize).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.continuous_specialize`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.continuous_specialize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The positive weighted evaluation preserves genuine limits.

**Theorem 1.17 (lift_monomial).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

A supported monomial becomes the exact ordinary polynomial monomial of degree n+k.

**Theorem 1.18 (admissible_monomial).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The explicit inequality n+k >= 0 supplies the required polynomial preimage.

**Theorem 1.19 (specialize_monomial).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The exact weighted degree and the original rational coefficient are preserved.

**Theorem 1.20 (admissible_sub).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The support condition is closed under subtraction.

**Theorem 1.21 (admissible_prod).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Every finite product of supported factors remains supported.

**Theorem 1.22 (specialize_prod).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The supported specialization commutes with arbitrary finite products.

**Theorem 1.23 (specialize_factor).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

A supported Laurent Euler factor becomes its exact weighted Euler factor.

**Theorem 1.24 (admissible_factor).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The positivity condition on a Laurent factor is checked before specializing.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.Admissible`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_factor`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_monomial`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_mul`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_one`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_prod`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.admissible_sub`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.continuous_lift`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.continuous_specialize`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.diagonal`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.liftAdd`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_monomial`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_mul`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_of_map`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.lift_one`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.map_lift`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specializeAdd`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_factor`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_monomial`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_mul`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_one`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.specialize_prod`
