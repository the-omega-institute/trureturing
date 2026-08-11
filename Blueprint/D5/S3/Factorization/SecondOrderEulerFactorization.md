# Second-Order Euler Factorization

## Abstract

Convergent local second-order factors assemble into the corresponding Euler product.

**Theorem 1.1 (Local second-order factors assemble globally).**

$$\prod_i L_i = (\prod_i A_i)(\prod_i B_i)(\prod_i C_i) \operatorname{exp}(\sum_i H_i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/SecondOrderEulerFactorization.second_order_euler_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every local Euler factor is the product of two leading factors, a reciprocal factor, and the exponential of a remainder. If the three factor products converge and the remainders have a sum, then the product of the local factors equals the product of the three global factors times the exponential of the remainder sum. The reciprocal product is supplied with its own convergence witness, so the statement does not silently divide by a possibly zero limit.

This is the convergence-witness transport behind the source atom's second-order factorization. The pinned library has the required pieces but no exact assembled declaration: HasProd.mul composes the leading products, HasSum.cexp turns the remainder sum into an exponential product, HasProd.congr_fun applies the local identity, and HasProd.unique identifies the global limit. The declaration is therefore a thin honest wrapper over those general results.

## References

- Truth anchor: `D5/S3/Factorization/SecondOrderEulerFactorization.second_order_euler_factorization`
