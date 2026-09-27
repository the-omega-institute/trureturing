# The conjecture of OEIS A362534 is false at n = 19

## Abstract

At n = 19 the adiabatic polarization-transfer bound g(19) = 215955/131072 has numerator 215955, while the ratio f(19)/g(19) = 92378/43191 has denominator 43191, so the conjecture of OEIS A362534 fails.

**Definition 1.1 (The symmetry-constrained bound).**

$$\forall n \in \mathbb{N},\; \operatorname{f}\left(n\right) = \operatorname{ite}\left(\operatorname{NatMod}\left(n, 2\right) = 0, 2^{1 - n} \cdot n \cdot \operatorname{choose}\left(n - 1, \operatorname{NatDiv}\left(n, 2\right)\right), 2^{1 - n} \cdot n \cdot \operatorname{choose}\left(n - 1, \operatorname{NatDiv}\left(n - 1, 2\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/SabbaPolarizationTransferRefutation.f` (`✓ std3`).

*Citation.* Mohamed Sabba (2023). *OEIS A362534, Numerators of the ratio of the symmetry-constrained bound to the adiabatic bound on polarization transfer in AXn spin-1/2 systems*. URL: <https://oeis.org/A362534>.

*Commentary.*

For even n the bound is 2^(1-n) n binomial(n-1, n/2), for odd n it is 2^(1-n) n binomial(n-1, (n-1)/2), as rational numbers; NatDiv and NatMod are the natural quotient and remainder.

**Definition 1.2 (The adiabatic bound).**

$$\forall n \in \mathbb{N},\; \operatorname{g}\left(n\right) = \operatorname{ite}\left(\operatorname{NatMod}\left(n, 2\right) = 0, 2 \cdot (1 - 2^{-n} \cdot \operatorname{choose}\left(n, \operatorname{NatDiv}\left(n, 2\right)\right)), 2 \cdot (1 - 2^{-n} \cdot \operatorname{choose}\left(n, \operatorname{NatDiv}\left(n - 1, 2\right)\right))\right)$$

*Formalization.* `D5/S0/Certificates/SabbaPolarizationTransferRefutation.g` (`✓ std3`).

*Citation.* Mohamed Sabba (2023). *OEIS A362534, Numerators of the ratio of the symmetry-constrained bound to the adiabatic bound on polarization transfer in AXn spin-1/2 systems*. URL: <https://oeis.org/A362534>.

*Commentary.*

For even n the bound is 2 (1 - 2^(-n) binomial(n, n/2)), for odd n it is 2 (1 - 2^(-n) binomial(n, (n-1)/2)).

**Definition 1.3 (The conjecture of OEIS A362534).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{num}\left(\operatorname{g}\left(n\right)\right) = \operatorname{den}\left(\frac{\operatorname{f}\left(n\right)}{\operatorname{g}\left(n\right)}\right)))$$

*Formalization.* `D5/S0/Certificates/SabbaPolarizationTransferRefutation.claim` (`✓ std3`).

*Citation.* Mohamed Sabba (2023). *OEIS A362534, Numerators of the ratio of the symmetry-constrained bound to the adiabatic bound on polarization transfer in AXn spin-1/2 systems*. URL: <https://oeis.org/A362534>.

*Commentary.*

For every n at least one, the numerator of g(n) equals the denominator of f(n)/g(n), both in lowest terms (num and den of a rational number).

**Theorem 1.4 (A counterexample at n = 19).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SabbaPolarizationTransferRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sabba-2023-a362534-polarization-transfer-refutation` (refuted) by `D5/S0/Certificates/SabbaPolarizationTransferRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sabba-2023-a362534-polarization-transfer-refutation","declaration_gid":"D5/S0/Certificates/SabbaPolarizationTransferRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohamed Sabba (2023). *OEIS A362534, Numerators of the ratio of the symmetry-constrained bound to the adiabatic bound on polarization transfer in AXn spin-1/2 systems*. URL: <https://oeis.org/A362534>.

*Commentary.*

Since 19 is odd, f(19) = 2^(-18) 19 binomial(18, 9) = 230945/65536 and g(19) = 2 (1 - 2^(-19) binomial(19, 9)) = 215955/131072. Their ratio is 92378/43191 in lowest terms, whose denominator 43191 differs from the numerator 215955 = 5 times 43191 of g(19).

## References

- Truth anchor: `D5/S0/Certificates/SabbaPolarizationTransferRefutation.claim`
- Truth anchor: `D5/S0/Certificates/SabbaPolarizationTransferRefutation.f`
- Truth anchor: `D5/S0/Certificates/SabbaPolarizationTransferRefutation.g`
- Truth anchor: `D5/S0/Certificates/SabbaPolarizationTransferRefutation.result`
