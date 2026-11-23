# Prime sources in a minimal counterexample

## Abstract

Prime sources in a minimal counterexample

**Theorem 1.1 (Abundancy of distinct prime powers).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall e \in \mathbb{N} \to \mathbb{N},\; \left(\forall p \in \mathbb{N},\; p \in S \Rightarrow \left(\operatorname{e}\left(p\right) \ne 0 \Rightarrow \operatorname{Prime}\left(p\right)\right)\right) \Rightarrow \operatorname{abundancyIndex}\left(\prod_{p \in S} (p^{\operatorname{e}\left(p\right)})\right) = \prod_{p \in S} (\operatorname{geom}\left(p, \operatorname{e}\left(p\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.abundancy_prime_power_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For a finite set of bases and arbitrary nonnegative exponents, the abundancy of their product equals the product of the finite reciprocal geometric factors, provided every base with nonzero exponent is prime. Zero exponents impose no primality condition and contribute one. Primality cannot be omitted: the singleton base 1 at exponent 1 has abundancy 1 but geometric factor 2. The identity includes the empty set.

**Definition 1.2 (Sources of a totient prime).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall q \in \mathbb{N},\; q \in \operatorname{primeSources}\left(n, r\right) \Leftrightarrow \left(q \in \operatorname{primeFactors}\left(n\right) \land r \mid q - 1\right)$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.primeSources` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The sources are the prime divisors q of n for which r divides q-1.

**Theorem 1.3 (The prime-source deletion obstruction).**

$$\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; m \ne 0 \Rightarrow \left(\operatorname{Prime}\left(r\right) \Rightarrow \left(r \mid \operatorname{totient}\left(m\right) \Rightarrow \left(\operatorname{alpha}\left(m\right) < 1 \Rightarrow \left(\left(\forall d \in \mathbb{N},\; d \mid m \Rightarrow \left(d < m \Rightarrow 1 \le \operatorname{alpha}\left(d\right)\right)\right) \Rightarrow \operatorname{geom}\left(r, \operatorname{card}\left(\operatorname{primeSources}\left(m, r\right)\right)\right) < \prod_{q \in \operatorname{primeSources}\left(m, r\right)} (\frac{q}{q - 1})\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.prime_deletion_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Assume a nonzero m has ratio below 1, while every strictly smaller divisor has ratio at least 1. For each prime r dividing its totient, the product of q/(q-1) over all sources strictly exceeds the geometric sum through their number. Minimality forces m to be squarefree. Deleting all sources leaves a proper divisor whose totient is coprime to r, and each deleted source contributes a factor of r to phi(m).

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.abundancy_prime_power_product`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.primeSources`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.prime_deletion_necessary`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction](Reduction.md)
- Dependency: [D5/S3/Factorization/LehmerTotientDichotomy](../../../Factorization/LehmerTotientDichotomy.md)
