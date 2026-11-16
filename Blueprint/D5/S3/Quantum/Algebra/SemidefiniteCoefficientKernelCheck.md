# Positive semidefinite coefficient-kernel exclusion

## Abstract

A positive semidefinite coefficient matrix is detected by its matrix-valued Gram compression on a complex-linearly independent family.

**Theorem 1.1 (The coefficient map has trivial positive-semidefinite kernel).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall k \in Nat,\; \forall X \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \operatorname{Complex}\left(\right)\right),\; \forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \operatorname{Complex}\left(\right)\right),\; ((\operatorname{LinearIndependent}\left(Complex, X\right)) \land (\operatorname{PosSemidef}\left(T\right))) \Rightarrow ((\sum_{r : \operatorname{Fin}\left(k\right)} (\sum_{s : \operatorname{Fin}\left(k\right)} ((\operatorname{entry}\left(T, r, s\right)) \cdot (\operatorname{conjTranspose}\left(\operatorname{entry}\left(X, r\right)\right) \cdot \operatorname{entry}\left(X, s\right)))) = 0) \Rightarrow (T = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/SemidefiniteCoefficientKernelCheck.exact_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural a, b and k, X is a family of a by b complex matrices indexed by Fin k and is complex-linearly independent. For a positive semidefinite k by k complex matrix T, form Phi(T) as the finite double sum of T r s times the conjugate-transpose Gram block X r star times X s. If Phi(T) is zero, then T is zero. The statement includes k = 0, a = 0 and b = 0.

The proof evaluates each diagonal entry of Phi(T), reindexes the finite sums, and applies Matrix.PosSemidef.dotProduct_mulVec_zero_iff after the nonnegative summands are shown to sum to zero. The resulting coefficient relation is exactly the finite-type characterization of complex linear independence. No scalar-Gram premise and no positivity assumption on a, b or k is used.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/SemidefiniteCoefficientKernelCheck.exact_check`
