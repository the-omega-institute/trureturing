# Strict Finite Prefix Dominance

## Abstract

A finite geometric-prefix logarithm is strictly below its harmonic prefix.

**Theorem 1.1 (Strict finite prefix comparison).**

$$\begin{aligned}\forall z \in \mathbb{R}, a \in \mathbb{N},\\1 \le a \land 0 < z \land z < 1 \Rightarrow\\log\left(\sum_{k=0}^{a} z^{k}\right) < \sum_{k=1}^{a} \frac{z^{k}}{k}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent a is any natural number at least one, and z is any real number strictly between zero and one. Both sums are finite. The proof differentiates their difference and uses the strict bound on the geometric sum to obtain a positive derivative; its value at zero is zero.

For z = 1/p this gives the strict prime-axis prefix clause of the Robin reference comparison. The theorem does not include reference maximization, a uniform signed-tail estimate, the Robin inequality or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix`
