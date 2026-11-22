# Fermat products and power-of-two totients

## Abstract

Fermat products and power-of-two totients

**Theorem 1.1 (An arbitrary finite set of Fermat indices).**

$$\forall I \in \operatorname{Finset}\left(\mathbb{N}\right),\; \prod_{a \in I} (\operatorname{fermatNumber}\left(a\right)) + 1 \le 2^{\sum_{a \in I} (2^{a}) + 1} \land \left(\prod_{a \in I} (\operatorname{fermatNumber}\left(a\right)) + 1 = 2^{\sum_{a \in I} (2^{a}) + 1} \Leftrightarrow I = \operatorname{range}\left(\operatorname{card}\left(I\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat.fermat_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For every finite set I of nonnegative indices, the product of the Fermat numbers plus 1 is at most 2 raised to one plus the sum of their powers of 2. Equality holds exactly for I=range(card(I)). No primality or upper bound on the indices is assumed.

**Theorem 1.2 (The power-of-two totient case).**

$$\forall n \in \mathbb{N},\; \forall E \in \mathbb{N},\; \operatorname{Odd}\left(n\right) \Rightarrow \left(\operatorname{totient}\left(n\right) = 2^{E} \Rightarrow n \le \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat.odd_le_sigma_totient_of_two_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

An odd integer with power-of-two totient is squarefree and is a product of distinct Fermat primes. The product estimate proves n<=sigma(phi(n)). The case n=1 is included. Oddness is necessary for this stronger inequality: n=2 has totient 1 and sigma(1)=1. No assertion that all Fermat primes are known is needed.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat.fermat_product_bound`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat.odd_le_sigma_totient_of_two_pow`
