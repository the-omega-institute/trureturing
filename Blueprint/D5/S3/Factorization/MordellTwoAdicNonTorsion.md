# Binary Valuation Descent on Mordell Curves

## Abstract

Negative binary X-valuation forces infinite order on the smooth locus of an integral Mordell model.

**Definition 1.1 (The integral Mordell model).**

$$E_{b} : Y^{2} = X^{3} + b$$

*Formalization.* `D5/S3/Factorization/MordellTwoAdicNonTorsion.mordellCurve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Weierstrass coefficients are zero except for a6=b, with b an integer. At b=0 the model is singular; the theorem below concerns only its nonsingular affine points.

**Theorem 1.2 (Negative binary X-valuation forces infinite order).**

$$\forall b \in \mathbb{Z}, P \in \left(E_{b}\right)^{{sm,aff}}(\mathbb{Q}), v_{2}(X(P)) < 0 \Rightarrow \neg FiniteAddOrder(P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonsingular affine rational point with v2(X)<0, the duplication formula and the integrality of b give v2(X(2P))=v2(X(P))-2. The same calculation applies to every subsequent double, yielding pairwise distinct points and therefore infinite additive order.

An integral point with odd X and nonzero even Y has a double with negative binary X-valuation. The next theorem proves this first doubling step. Point construction and distinct twist classes are separate claims.

**Theorem 1.3 (Unit X and positive binary Y-valuation force infinite order).**

$$\forall b \in \mathbb{Z}, P \in \left(E_{b}\right)^{{sm,aff}}(\mathbb{Q}), X(P) \neq 0 \land v_{2}(X(P)) = 0 \land 0 < v_{2}(Y(P)) \Rightarrow \neg FiniteAddOrder(P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero X condition excludes the zero abscissa, whose binary valuation is also zero by convention. The tangent calculation gives v2(X(2P))=-2-2v2(Y(P))<0. The preceding theorem then proves that the double, and therefore the original point, has infinite order.

## References

- Truth anchor: `D5/S3/Factorization/MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x`
- Truth anchor: `D5/S3/Factorization/MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y`
- Truth anchor: `D5/S3/Factorization/MordellTwoAdicNonTorsion.mordellCurve`
