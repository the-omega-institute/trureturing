# A Norm-Two Ideal in the Minus-Five Quadratic Order

## Abstract

The standard two-generator ideal in the minus-five quadratic order has quotient norm two.

**Theorem 1.1 (The standard ideal has quotient norm two).**

$$\operatorname{IdealQuotientMk}\left(normTwoIdeal, 2\right) = 0 \land\\{}\operatorname{IdealQuotientMk}\left(normTwoIdeal, 1 + \sqrt{-5}\right) = 0 \land\\{}(\forall x: \operatorname{QuadraticOrder}, \operatorname{quotientEquivZModTwo}\left(\operatorname{IdealQuotientMk}\left(normTwoIdeal, x\right)\right) = \operatorname{residueHom}\left(x\right)) \land\\{}\operatorname{NatCard}\left(\operatorname{IdealQuotient}\left(\operatorname{QuadraticOrder}, normTwoIdeal\right)\right) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/NormTwoIdeal.ideal_norm_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is exactly the quadratic order Z[sqrt(-5)]. The named ideal is constructed as the ideal span of 2 and 1 + sqrt(-5), matching the two source generators.

Evaluation at sqrt(-5) = 1 modulo two is a surjective ring homomorphism. Its kernel is the named ideal, so the first isomorphism theorem gives the displayed canonical quotient equivalence and computation rule.

Both generators therefore vanish in the quotient. Transporting cardinality through the equivalence to ZMod 2 proves that the quotient-cardinality definition of the ideal norm is two.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/NormTwoIdeal.ideal_norm_two`
