# Intertwining Defect Propagation

## Abstract

An operator intertwining defect telescopes and propagates with exact norm bounds.

**Theorem 1.1 (Intertwining defects telescope exactly).**

$$\forall k, X, Y: \operatorname{Type}, [\operatorname{NontriviallyNormedField}\left(k\right)], [\operatorname{SeminormedAddCommGroup}\left(X\right)], [\operatorname{NormedSpace}\left(k, X\right)], [\operatorname{SeminormedAddCommGroup}\left(Y\right)], [\operatorname{NormedSpace}\left(k, Y\right)],\\{}A: \operatorname{ContinuousLinearMap}\left(k, Y, Y\right), C: \operatorname{ContinuousLinearMap}\left(k, X, Y\right), T: \operatorname{ContinuousLinearMap}\left(k, X, X\right), n: Nat,\\{}C \cdot T^{n} - A^{n} \cdot C = \sum_{j=0}^{n-1} A^{n-1-j} \cdot \left(C \cdot T - A \cdot C\right) \cdot T^{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.intertwining_defect_telescope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T and A be continuous linear endomorphisms of possibly distinct spaces, and let C map the source space to the target. The time-n defect is the sum of the one-step defect transported by the remaining powers of A and the elapsed powers of T.

A noncommutative-ring induction proves exact cancellation. At time zero the finite sum is empty and both sides are zero.

**Theorem 1.2 (The propagated defect has a weighted norm bound).**

$$\Vert C \cdot T^{n} - A^{n} \cdot C \Vert \leq \sum_{j=0}^{n-1} \Vert A \Vert^{n-1-j} \cdot \Vert C \cdot T - A \cdot C \Vert \cdot \Vert T \Vert^{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.norm_intertwining_defect_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triangle inequality, the operator-norm composition bound, and the norm bound for powers turn the exact telescope into the finite weighted sum stated in the source corollary.

No finite-dimensional, completeness, inner-product, or nontrivial carrier assumption is used.

**Theorem 1.3 (Uniform norm bounds give linear propagation).**

$$\Vert A \Vert \leq L \land \Vert T \Vert \leq L \Rightarrow \Vert C \cdot T^{n} - A^{n} \cdot C \Vert \leq n \cdot L^{n-1} \cdot \Vert C \cdot T - A \cdot C \Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.uniform_norm_intertwining_defect_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both operator norms are at most L, every summand is at most L to the power n minus one times the one-step defect norm. There are exactly n summands.

The proof does not need L less than one. Natural subtraction is truncated, so at n equal to zero its exponent is zero while the leading factor n makes the right side zero.

**Theorem 1.4 (The bound on A is necessary).**

$$\Vert 0 \Vert \leq 1 \land \neg\Vert 1 \cdot 0^{3} - 2^{3} \cdot 1 \Vert \leq 3 \cdot 1^{3-1} \cdot \Vert 1 \cdot 0 - 2 \cdot 1 \Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.left_norm_bound_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the one-dimensional real space take A as multiplication by two, C as the identity, T as zero, L as one, and n as three. The bound on T holds, but the claimed conclusion without the bound on A is false.

**Theorem 1.5 (The bound on T is necessary).**

$$\Vert 0 \Vert \leq 1 \land \neg\Vert 1 \cdot 2^{3} - 0^{3} \cdot 1 \Vert \leq 3 \cdot 1^{3-1} \cdot \Vert 1 \cdot 2 - 0 \cdot 1 \Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.right_norm_bound_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symmetric one-dimensional counterexample takes A as zero, C as the identity, T as multiplication by two, L as one, and n as three. The bound on A holds, but the conclusion without the bound on T is false.

## References

- Truth anchor: `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.intertwining_defect_telescope`
- Truth anchor: `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.left_norm_bound_is_necessary`
- Truth anchor: `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.norm_intertwining_defect_le`
- Truth anchor: `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.right_norm_bound_is_necessary`
- Truth anchor: `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.uniform_norm_intertwining_defect_le`
