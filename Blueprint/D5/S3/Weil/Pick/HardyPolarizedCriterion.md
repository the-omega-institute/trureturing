# Hardy Polarized Criterion

## Abstract

A finite Hardy Hankel block vanishes exactly when its negative-frequency coefficients vanish.

**Theorem 1.1 (Finite Hardy Hankel block vanishing criterion).**

$$\forall n \in \mathbb{N}, c \in \mathbb{N}to\mathbb{C}, \operatorname{H}(c) = 0 \iff {\forall i, j \in \operatorname{Fin}(n), c_{i+j+1} = 0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/HardyPolarizedCriterion.hardy_polarized_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite truncation, the Hankel block samples the coefficient sequence at i + j + 1, the negative-frequency tail of a Laurent symbol. Its vanishing is therefore equivalent to the vanishing of every sampled tail coefficient.

This is the finite algebraic Hardy statement. The source-level identification of the symbol with a completed-zeta RH family is not assumed here, because that analytic bridge has no owner in the pinned library.

**Theorem 1.2 (A negative coefficient witnesses a nonzero Hankel block).**

$$\forall n \in \mathbb{N}, c \in \mathbb{N}to\mathbb{C}, \forall i, j \in \operatorname{Fin}(n), c_{i+j+1} \neq 0 \Rightarrow \operatorname{H}(c) \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/HardyPolarizedCriterion.hardy_nonzero_of_negative_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any explicitly nonzero sampled negative-frequency coefficient gives a matrix entry that is nonzero, hence constructs a concrete witness against Hankel-block vanishing.

## References

- Truth anchor: `D5/S3/Weil/Pick/HardyPolarizedCriterion.hardy_nonzero_of_negative_coefficient`
- Truth anchor: `D5/S3/Weil/Pick/HardyPolarizedCriterion.hardy_polarized_criterion`
