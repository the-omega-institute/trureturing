# Square Order Descent

## Abstract

Square-root rescaling of a radial maximum-modulus function halves its logarithmic order.

**Theorem 1.1 (Square-root rescaling halves logarithmic order).**

$$\begin{gathered}\forall M_{F}, M_{G}: \mathbb{R} \to \mathbb{R},\\{}Eventually\left(1 < \left(M_{F}\right)\left(r\right)\right) \land (\forall r \geq 0, \left(M_{G}\right)\left(r\right) = \left(M_{F}\right)\left(\sqrt{r}\right)) \Rightarrow\\{}\rho\left(M\right) := \operatorname{limsup}_{r\to \infty} \frac{{\log(\log(M\left(r\right)))}}{{\log(r)}}, Eventually\left(1 < \left(M_{G}\right)\left(r\right)\right) \land\\{}\rho\left(M_{G}\right) = \frac{1}{2} \rho\left(M_{F}\right) \land (\rho\left(M_{F}\right) = 1 \Rightarrow \rho\left(M_{G}\right) = \frac{1}{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SquareOrderDescent.square_order_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M_F and M_G be real radial maximum-modulus functions. Assume M_F is eventually greater than one, so its nested logarithm uses the standard positive branch, and assume M_G(r) equals M_F(sqrt(r)) at every nonnegative radius. Then M_G is also eventually greater than one.

Define rho(M) as the extended-real upper limit of log(log(M(r))) divided by log(r) as r tends to infinity. The identity log(sqrt(r)) = log(r)/2 away from the degenerate radii gives rho(M_G) = rho(M_F)/2. In particular, order one descends to order one half.

The source statement did not specify a relationship between F and G; the displayed maximum-modulus rescaling is therefore an explicit hypothesis. The proof uses Mathlib's square-root filter map and nonnegative-constant limsup scaling theorem after restricting to radii greater than one.

## References

- Truth anchor: `D5/S3/Analytic/SquareOrderDescent.square_order_descent`
