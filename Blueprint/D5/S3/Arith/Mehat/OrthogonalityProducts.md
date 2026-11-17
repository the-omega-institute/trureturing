# Integer orthogonality factors and square-product separation

## Abstract

Arbitrarily many integer orthogonality factors can have pairwise distinct products of entry squares.

Fin(n) is the finite type of integers from zero through n minus one. Matrix(m,n,R) is the type of R-valued matrices with row type m and column type n; matrix multiplication and transpose have their usual meanings. The symbol smul denotes integer scalar multiplication, and the typed matrix 1 is the identity. Function.Injective means that equality of outputs implies equality of the complete input functions. Every product below ranges over all indices in Fin(k), and its value is an integer. The implicit parameter R ranges over arbitrary universe levels; [CommRing(R)] is an anonymous commutative-ring instance.

**Definition 1.1 (Problem 9.2).**

$$\operatorname{Problem92} : \operatorname{Prop} := \forall k \in \mathbb{N},\; 1 \le k \Rightarrow \exists (A : \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{Z}\right)) (\gamma : \operatorname{Fin}\left(k\right) \to \mathbb{Z}), (\forall i \in \operatorname{Fin}\left(k\right),\; \gamma\left(i\right) \ne 0 \land A\left(i\right) \cdot (A\left(i\right))^{T} = \operatorname{smul}\left(\gamma\left(i\right), (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{Z}\right))\right)) \land \operatorname{Function}.\operatorname{Injective}\left((p : \operatorname{Fin}\left(k\right) \to (\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right))) \mapsto \prod_{i \in \operatorname{Fin}\left(k\right)} (A\left(i\right)\left((p\left(i\right))_{1}, (p\left(i\right))_{2}\right))^{2}\right)$$

*Formalization.* `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem92` (`✓ std3`).

*Citation.* Sanjit Singh Mehat (2026). *Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243*. URL: <https://arxiv.org/html/2609.05530v1>.

*Commentary.*

For every positive natural k there are k integer matrices of order three, each with a nonzero integer constant gamma and A times its transpose equal to gamma times the identity. The map from all functions choosing one of the nine entry positions in each factor to the product of those entry squares is injective. The matrices and constants may depend on k.

**Definition 1.2 (Quaternion factors).**

$$\forall \{R : \operatorname{Type}^{*}\} [\operatorname{CommRing}\left(R\right)] (a : \operatorname{Fin}\left(4\right) \to R), (\operatorname{quaternionMatrix}\left(a\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), R\right)) = \begin{pmatrix}a\left(0\right)^{2} + a\left(1\right)^{2} - a\left(2\right)^{2} - a\left(3\right)^{2}&2 \cdot (a\left(1\right) \cdot a\left(2\right) - a\left(0\right) \cdot a\left(3\right))&2 \cdot (a\left(1\right) \cdot a\left(3\right) + a\left(0\right) \cdot a\left(2\right))\\2 \cdot (a\left(1\right) \cdot a\left(2\right) + a\left(0\right) \cdot a\left(3\right))&a\left(0\right)^{2} - a\left(1\right)^{2} + a\left(2\right)^{2} - a\left(3\right)^{2}&2 \cdot (a\left(2\right) \cdot a\left(3\right) - a\left(0\right) \cdot a\left(1\right))\\2 \cdot (a\left(1\right) \cdot a\left(3\right) - a\left(0\right) \cdot a\left(2\right))&2 \cdot (a\left(2\right) \cdot a\left(3\right) + a\left(0\right) \cdot a\left(1\right))&a\left(0\right)^{2} - a\left(1\right)^{2} - a\left(2\right)^{2} + a\left(3\right)^{2}\end{pmatrix}$$

*Formalization.* `D5/S3/Arith/Mehat/OrthogonalityProducts.quaternionMatrix` (`✓ std3`).

*Citation.* Sanjit Singh Mehat (2026). *Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243*. URL: <https://arxiv.org/html/2609.05530v1>.

*Commentary.*

The classical quaternion rotation formula gives a polynomial matrix with orthogonality constant equal to the square of the sum of the four coordinate squares. Individual factors need not satisfy either Euler diagonal equation.

**Theorem 1.3 (Factors for every positive length).**

$$\operatorname{problem92} : \operatorname{Problem92}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Mehat/OrthogonalityProducts.problem92` (`✓ std3`). ∎

*Resolves.* `Problems/mehat-2026-problem-92-orthogonality-products` (proved) by `D5/S3/Arith/Mehat/OrthogonalityProducts.problem92`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mehat-2026-problem-92-orthogonality-products","declaration_gid":"D5/S3/Arith/Mehat/OrthogonalityProducts.problem92","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sanjit Singh Mehat (2026). *Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243*. URL: <https://arxiv.org/html/2609.05530v1>.

*Commentary.*

For any two different coordinate polynomials, an integer quaternion makes the first zero and the second nonzero. Thus no nonzero weighted difference of their squares vanishes identically. For equal coordinates, different nonzero old products also give a nonzero difference. The product of all collision polynomials and all entry polynomials is nonzero in the integer polynomial ring. MvPolynomial.funext implies that it is nonzero at some integer tuple. Appending this quaternion factor preserves nonzero entries and injectivity, so induction gives every finite length. The induction includes the empty tuple only as an auxiliary extension; Problem 9.2 asserts positive lengths. No coefficient-size bound, efficient construction, order-seven result, or full Euler-matrix theorem is asserted here.

## References

- Truth anchor: `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem92`
- Truth anchor: `D5/S3/Arith/Mehat/OrthogonalityProducts.problem92`
- Truth anchor: `D5/S3/Arith/Mehat/OrthogonalityProducts.quaternionMatrix`
