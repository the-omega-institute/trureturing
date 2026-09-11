# Maximum modulus and square-shadow growth order

## Abstract

Circular maximum modulus is attained for continuous complex functions. A square shadow rescales the radius and halves extended-real growth order.

**Definition 1.1 (Circular maximum modulus).**

$$\operatorname{M}\left(f, r\right) = \operatorname{sSup}\left(\operatorname{normImageOfSphere}\left(f, r\right)\right)$$

*Formalization.* `D5/S3/Analytic/Entire/SquareShadowOrderHalving.maxModulus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition is the real supremum of the image of the radius-r sphere under the norm of f. Continuity supplies boundedness; nonnegative radius supplies nonemptiness. Negative radii are irrelevant to growth order.

**Theorem 1.2 (Radius zero).**

$$\operatorname{M}\left(f, 0\right) = \operatorname{norm}\left(\operatorname{f}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/SquareShadowOrderHalving.max_modulus_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex-valued function, the radius-zero sphere is the singleton origin, so its maximum modulus is the norm of the value there.

**Theorem 1.3 (The maximum is attained).**

$$\exists z \in \operatorname{sphere}\left(0, r\right), \operatorname{M}\left(f, r\right) = \operatorname{norm}\left(\operatorname{f}\left(z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/SquareShadowOrderHalving.max_modulus_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For continuous f and nonnegative r, there exists a complex z on the radius-r sphere whose value has norm maxModulus(f,r). This applies the compact extreme value theorem and identifies the attained value with the supremum.

**Theorem 1.4 (Square-shadow maximum modulus).**

$$\operatorname{M}\left(G, r\right) = \operatorname{M}\left(F, \sqrt{r}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/SquareShadowOrderHalving.max_modulus_square_shadow` (`✓ std3`). ∎

*Citation.* trureturing contributors (2026). *Square descent of entire-function growth order*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/ad7ed967c5cf013e1c08f2b598928ba81d2f4a5d/Meta/Digestion/atoms/sha256/02442d2ab1d0fe1f273e0f69b93b84d85cdc6876f384b45bee09778d12f1882c>.

*Commentary.*

Assume F and G are continuous complex functions and F(z)=G(z squared) for every z. For every nonnegative r, their circular maxima satisfy the displayed equality. One inequality squares a maximizing point; the other chooses a complex square root of a maximizing point. Radius zero is included.

**Definition 1.5 (Extended-real growth order).**

$$\operatorname{order}\left(f\right) = \operatorname{limsupAtTop}\left(\frac{\operatorname{log}\left(\operatorname{log}\left(\operatorname{M}\left(f, r\right)\right)\right)}{\operatorname{log}\left(r\right)}\right)$$

*Formalization.* `D5/S3/Analytic/Entire/SquareShadowOrderHalving.order` (`✓ std3`).

*Citation.* trureturing contributors (2026). *Square descent of entire-function growth order*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/ad7ed967c5cf013e1c08f2b598928ba81d2f4a5d/Meta/Digestion/atoms/sha256/02442d2ab1d0fe1f273e0f69b93b84d85cdc6876f384b45bee09778d12f1882c>.

*Commentary.*

The real quotient is coerced to EReal before taking the limsup at positive infinity. Thus positive infinity remains a possible order. Lean's total real logarithm and division define the expression at all small radii, including one; only the tail affects the limsup. Under these conventions the zero function has order zero.

**Theorem 1.6 (Growth order is halved).**

$$\operatorname{order}\left(G\right) = \frac{\operatorname{order}\left(F\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/SquareShadowOrderHalving.order_square_shadow` (`✓ std3`). ∎

*Citation.* trureturing contributors (2026). *Square descent of entire-function growth order*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/ad7ed967c5cf013e1c08f2b598928ba81d2f4a5d/Meta/Digestion/atoms/sha256/02442d2ab1d0fe1f273e0f69b93b84d85cdc6876f384b45bee09778d12f1882c>.

*Commentary.*

For the same continuous F and G satisfying F(z)=G(z squared), the extended-real orders obey this equality, including infinite order. The maximum-modulus equality, the logarithm of a square root, the image of atTop under square root, and positive scalar multiplication of limsup form one proof chain.

**Theorem 1.7 (Order one descends to one half).**

$$\operatorname{order}\left(G\right) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/SquareShadowOrderHalving.order_half_of_order_one` (`✓ std3`). ∎

*Citation.* trureturing contributors (2026). *Square descent of entire-function growth order*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/ad7ed967c5cf013e1c08f2b598928ba81d2f4a5d/Meta/Digestion/atoms/sha256/02442d2ab1d0fe1f273e0f69b93b84d85cdc6876f384b45bee09778d12f1882c>.

*Commentary.*

If F has order one, its square shadow G has order one half. In the entire-function setting, the source constructs G from the even Taylor coefficients of F. This module takes the resulting identity F(z)=G(z squared) as a hypothesis; it does not reconstruct the Taylor series or prove a canonical-product theorem.

## References

- Truth anchor: `D5/S3/Analytic/Entire/SquareShadowOrderHalving.maxModulus`
- Truth anchor: `D5/S3/Analytic/Entire/SquareShadowOrderHalving.max_modulus_attained`
- Truth anchor: `D5/S3/Analytic/Entire/SquareShadowOrderHalving.max_modulus_square_shadow`
- Truth anchor: `D5/S3/Analytic/Entire/SquareShadowOrderHalving.max_modulus_zero`
- Truth anchor: `D5/S3/Analytic/Entire/SquareShadowOrderHalving.order`
- Truth anchor: `D5/S3/Analytic/Entire/SquareShadowOrderHalving.order_half_of_order_one`
- Truth anchor: `D5/S3/Analytic/Entire/SquareShadowOrderHalving.order_square_shadow`
