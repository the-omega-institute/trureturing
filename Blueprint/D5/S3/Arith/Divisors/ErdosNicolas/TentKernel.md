# A rational positive semidefinite reciprocal tangent kernel

## Abstract

A rational positive semidefinite reciprocal tangent kernel

**Definition 1.1 (The tangent kernel).**

$$\forall L \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{K}\left(L, r\right) = \operatorname{ite}\left(r \le L, \frac{2}{L} - \frac{r}{L^{2}}, \frac{1}{r}\right)$$

*Formalization.* `D5/S3/Arith/Divisors/ErdosNicolas/TentKernel.K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

For a positive natural cutoff L, the linear part meets the reciprocal tail at L. Lean defines the field operations at L=0 as well; positive semidefiniteness and Cauchy–Schwarz require a positive cutoff, while pointwise kernel and energy nonnegativity also hold at zero.

**Theorem 1.2 (Positive semidefiniteness).**

$$\forall I \in Type,\; \forall S \in \operatorname{Finset}\left(I\right),\; \forall x \in I \to \mathbb{Z},\; \forall c \in I \to \mathbb{Q},\; \forall L \in \mathbb{N},\; 0 < L \Rightarrow 0 \le \sum_{i \in S} (\sum_{j \in S} (\operatorname{c}\left(i\right) \cdot \operatorname{c}\left(j\right) \cdot \operatorname{K}\left(L, \operatorname{natAbs}\left(\operatorname{x}\left(i\right) - \operatorname{x}\left(j\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/TentKernel.kernel_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

A finite discrete Green identity writes the kernel as a nonnegative combination of the constant kernel and tents. Each tent is the Gram kernel of finite integer intervals. The statement allows repeated integer points and arbitrary signed rational coefficients. No integral or limiting argument is assumed.

**Theorem 1.3 (Rational kernel Cauchy–Schwarz).**

$$\forall L \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall B \in \operatorname{Finset}\left(\mathbb{N}\right),\; 0 < L \Rightarrow \operatorname{energy}\left(L, A, B\right)^{2} \le \operatorname{energy}\left(L, A, A\right) \cdot \operatorname{energy}\left(L, B, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/TentKernel.energy_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

The bilinear energy is the double sum of K(L,dist(a,b)). Positive semidefiniteness applied to a rational quadratic polynomial yields the square inequality. The two finite sets need not be disjoint.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/TentKernel.K`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/TentKernel.energy_sq_le`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/TentKernel.kernel_psd`
