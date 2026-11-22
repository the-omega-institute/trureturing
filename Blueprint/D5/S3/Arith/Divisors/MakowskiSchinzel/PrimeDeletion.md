# Prime sources in a minimal counterexample

## Abstract

Prime sources in a minimal counterexample

**Definition 1.1 (Sources of a totient prime).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall q \in \mathbb{N},\; q \in \operatorname{primeSources}\left(n, r\right) \Leftrightarrow \left(q \in \operatorname{primeFactors}\left(n\right) \land r \mid q - 1\right)$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.primeSources` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The sources are the prime divisors q of n for which r divides q-1.

**Theorem 1.2 (The prime-source deletion obstruction).**

$$\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; m \ne 0 \Rightarrow \left(\operatorname{Prime}\left(r\right) \Rightarrow \left(r \mid \operatorname{totient}\left(m\right) \Rightarrow \left(\operatorname{alpha}\left(m\right) < 1 \Rightarrow \left(\left(\forall d \in \mathbb{N},\; d \mid m \Rightarrow \left(d < m \Rightarrow 1 \le \operatorname{alpha}\left(d\right)\right)\right) \Rightarrow \operatorname{geom}\left(r, \operatorname{card}\left(\operatorname{primeSources}\left(m, r\right)\right)\right) < \prod_{q \in \operatorname{primeSources}\left(m, r\right)} (\frac{q}{q - 1})\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.prime_deletion_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Assume a nonzero m has ratio below 1, while every strictly smaller divisor has ratio at least 1. For each prime r dividing its totient, the product of q/(q-1) over all sources strictly exceeds the geometric sum through their number. Minimality forces m to be squarefree. Deleting all sources leaves a proper divisor whose totient is coprime to r, and each deleted source contributes a factor of r to phi(m).

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.primeSources`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.prime_deletion_necessary`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction](Reduction.md)
- Dependency: [D5/S3/Factorization/LehmerTotientDichotomy](../../../Factorization/LehmerTotientDichotomy.md)
