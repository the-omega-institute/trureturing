# Prime Precision Entropy Contraction

## Abstract

Each added prime-exponent digit contracts unresolved entropy exactly.

**Theorem 1.1 (One precision step has the exact prime contraction factor).**

$$\forall s \in \mathbb{R}, p \in \operatorname{Primes}, k \in \mathbb{N},\; 1 < s \Rightarrow \left(Pr\left(primeExponentPMF\left(s, p\right), \left\{v \ge k \mid v \in \mathbb{N}\right\}\right) \cdot H\left(map\left(v \mapsto v - (k), filter\left(primeExponentPMF\left(s, p\right), \left\{v \ge k \mid v \in \mathbb{N}\right\}\right)\right)\right) = (p^{-s})^{k} \cdot H\left(primeExponentPMF\left(s, p\right)\right) \land \left(Pr\left(primeExponentPMF\left(s, p\right), \left\{v \ge k + 1 \mid v \in \mathbb{N}\right\}\right) \cdot H\left(map\left(v \mapsto v - (k + 1), filter\left(primeExponentPMF\left(s, p\right), \left\{v \ge k + 1 \mid v \in \mathbb{N}\right\}\right)\right)\right) = (p^{-s})^{k + 1} \cdot H\left(primeExponentPMF\left(s, p\right)\right) \land Pr\left(primeExponentPMF\left(s, p\right), \left\{v \ge k + 1 \mid v \in \mathbb{N}\right\}\right) \cdot H\left(map\left(v \mapsto v - (k + 1), filter\left(primeExponentPMF\left(s, p\right), \left\{v \ge k + 1 \mid v \in \mathbb{N}\right\}\right)\right)\right) = p^{-s} \cdot Pr\left(primeExponentPMF\left(s, p\right), \left\{v \ge k \mid v \in \mathbb{N}\right\}\right) \cdot H\left(map\left(v \mapsto v - (k), filter\left(primeExponentPMF\left(s, p\right), \left\{v \ge k \mid v \in \mathbb{N}\right\}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction.prime_precision_entropy_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a zeta parameter above one and a prime. The channel law is the canonical geometric prime-exponent probability mass function.

At each precision, filter the channel on the unresolved tail, translate the conditional law back to zero, and weight its entropy by the tail probability.

Geometric memorylessness identifies the translated conditional law with the original channel. The tail mass is the corresponding prime ratio raised to the precision, giving both displayed levels and their exact one-step contraction.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction.prime_precision_entropy_contraction`
- Dependency: [D5/S3/Analytic/PrimeProducts/GeometricResidualMemorylessness](GeometricResidualMemorylessness.md)
