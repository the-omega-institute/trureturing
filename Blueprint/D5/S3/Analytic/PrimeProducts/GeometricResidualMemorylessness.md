# Geometric Residual Memorylessness

## Abstract

Conditioning a geometric law on a tail preserves its translated residual law.

**Theorem 1.1 (A geometric tail has the original residual law).**

$$\forall success \in unitInterval, k \in \mathbb{N},\; \left(success \ne 0 \land success \ne 1\right) \Rightarrow map\left(v \mapsto v - k, cond\left(geometricMeasure\left(success\right), \{v \in \mathbb{N} \mid v \geq k\}\right)\right) = geometricMeasure\left(success\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GeometricResidualMemorylessness.geometric_residual_memoryless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let success be a nondegenerate parameter in the unit interval. Mathlib's canonical zero-start geometric measure assigns mass proportional to one minus success raised to the sampled natural value.

For every natural threshold k, condition this measure on the tail event that the sampled value is at least k, then push the conditional law forward by natural subtraction of k.

Singleton extensionality reduces equality of the complete laws to the geometric mass factorization. The positive tail mass cancels, leaving the original geometric singleton mass at every residual value.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/GeometricResidualMemorylessness.geometric_residual_memoryless`
