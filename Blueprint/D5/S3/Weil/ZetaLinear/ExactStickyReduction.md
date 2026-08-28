# Exact Sticky Reduction

## Abstract

Completing a positive complementary block preserves positivity and negative inertia.

**Theorem 1.1 (Exact sticky reduction).**

$$\forall HP \in \operatorname{Type}\left(\right), HQ \in \operatorname{Type}\left(\right), APP \in \operatorname{LinearMap}\left(\mathbb{R}, HP, HP\right), AQP \in \operatorname{LinearMap}\left(\mathbb{R}, HP, HQ\right), AQQ \in \operatorname{LinearMap}\left(\mathbb{R}, HQ, HQ\right), AQQInv \in \operatorname{LinearMap}\left(\mathbb{R}, HQ, HQ\right),\; \left(\operatorname{NormedAddCommGroup}\left(HP\right) \land \left(\operatorname{InnerProductSpace}\left(\mathbb{R}, HP\right) \land \left(\operatorname{NormedAddCommGroup}\left(HQ\right) \land \left(\operatorname{InnerProductSpace}\left(\mathbb{R}, HQ\right) \land \left(\left(\forall q \in HQ,\; 0 \le \operatorname{inner}\left(\operatorname{apply}\left(AQQ, q\right), q\right)\right) \land \left(\left(\forall x \in HQ, y \in HQ,\; \operatorname{inner}\left(\operatorname{apply}\left(AQQ, x\right), y\right) = \operatorname{inner}\left(x, \operatorname{apply}\left(AQQ, y\right)\right)\right) \land \operatorname{comp}\left(AQQ, AQQInv\right) = \operatorname{id}\left(\mathbb{R}, HQ\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\left(\forall z \in \operatorname{Prod}\left(HP, HQ\right),\; 0 \le \operatorname{apply}\left(\operatorname{blockEnergy}\left(APP, AQP, AQQ\right), z\right)\right) \Leftrightarrow \left(\forall p \in HP,\; 0 \le \operatorname{apply}\left(\operatorname{schurEnergy}\left(APP, AQP, AQQ, AQQInv\right), p\right)\right)\right) \land \operatorname{negativeIndex}\left(\operatorname{blockEnergy}\left(APP, AQP, AQQ\right)\right) = \operatorname{negativeIndex}\left(\operatorname{schurEnergy}\left(APP, AQP, AQQ, AQQInv\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ExactStickyReduction.exact_sticky_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let HP and HQ be real inner-product spaces representing the retained and complementary summands. The full block energy and its Schur energy are constructed from APP, AQP, AQQ, and a right inverse of AQQ.

Assume the complementary block is nonnegative and symmetric. Then the full energy is nonnegative exactly when the Schur energy is, and their negative inertia indices agree.

The negative index is the supremum of dimensions of finite negative-definite subspaces, so the statement remains meaningful when HQ is infinite-dimensional. The proof completes the square and transports every finite negative subspace in both directions.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/ExactStickyReduction.exact_sticky_reduction`
