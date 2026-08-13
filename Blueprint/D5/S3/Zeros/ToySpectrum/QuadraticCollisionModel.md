# Quadratic Collision Model

## Abstract

The quadratic collision model has explicit real, double, and conjugate roots, and always has two roots with multiplicity.

**Theorem 1.1 (The z squared plus t model has the three root regimes).**

$$(\forall t \in \mathbb{R},\ (((t < 0) \Rightarrow (\operatorname{roots}(\operatorname{quadraticCollisionPolynomial}(t)) = \{\sqrt{(- t)}, - \sqrt{(- t)}\} \land \sqrt{(- t)} \neq - \sqrt{(- t)}))) \land ((t = 0) \Rightarrow \operatorname{roots}(\operatorname{quadraticCollisionPolynomial}(t)) = \{0,0\}) \land ((0 < t) \Rightarrow (\operatorname{roots}(\operatorname{quadraticCollisionPolynomial}(t)) = \{i \sqrt{t},- i \sqrt{t}\} \land \operatorname{conj}(i \sqrt{t}) = - i \sqrt{t}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel.quadratic_collision_model_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t < 0 the roots are the distinct real numbers plus or minus square root of minus t. At t = 0 the root multiset is the doubled zero. For t > 0 the roots are the conjugate pair plus or minus i square root t. The certificate is for this explicit polynomial model only; it does not assert a zeta zero theorem.

**Theorem 1.2 (The quadratic model always has two roots with multiplicity).**

$$(\forall t \in \mathbb{R},\ \operatorname{card}(\operatorname{roots}(\operatorname{quadraticCollisionPolynomial}(t))) = 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel.off_line_zeros_born_in_pairs_not_created` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiset cardinality is two for every real t, including the collision point where the two entries coincide. Thus the off-line conjugate pair in this toy model is a redistribution of two roots through a double root, not creation of additional roots.

## References

- Truth anchor: `D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel.off_line_zeros_born_in_pairs_not_created`
- Truth anchor: `D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel.quadratic_collision_model_certificate`
