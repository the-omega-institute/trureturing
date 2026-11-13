# Integer orthogonality factors and square-product separation

## Abstract

Arbitrarily many integer orthogonality factors can have pairwise distinct products of entry squares.

**Definition 1.1 (Problem 9.2).**

Lean statement: `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem92`

*Formalization.* `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem92` (`✓ std3`).

*Citation.* Sanjit Singh Mehat (2026). *Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243*. URL: <https://arxiv.org/html/2609.05530v1>.

*Commentary.*

For every positive natural k there are k integer matrices of order three, each with a nonzero integer constant gamma and A times its transpose equal to gamma times the identity. The map from all functions choosing one of the nine entry positions in each factor to the product of those entry squares is injective. The matrices and constants may depend on k.

**Definition 1.2 (Problem 9.1).**

Lean statement: `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem91`

*Formalization.* `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem91` (`✓ std3`).

*Citation.* Sanjit Singh Mehat (2026). *Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243*. URL: <https://arxiv.org/html/2609.05530v1>.

*Commentary.*

For every natural k at least two there is an integer matrix M of order three to the power k, with nonzero integer constant gamma, satisfying orthogonality, both squared diagonal sums equal to gamma, and injectivity of entry squares over all positions. The second diagonal uses the usual reversed finite index. This statement is separate from the factor theorem.

**Definition 1.3 (Quaternion factors).**

Lean statement: `D5/S3/Arith/Mehat/OrthogonalityProducts.quaternionMatrix`

*Formalization.* `D5/S3/Arith/Mehat/OrthogonalityProducts.quaternionMatrix` (`✓ std3`).

*Citation.* Sanjit Singh Mehat (2026). *Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243*. URL: <https://arxiv.org/html/2609.05530v1>.

*Commentary.*

The classical quaternion rotation formula gives a polynomial matrix with orthogonality constant equal to the square of the sum of the four coordinate squares. Individual factors need not satisfy either Euler diagonal equation.

**Theorem 1.4 (Factors for every positive length).**

Lean statement: `D5/S3/Arith/Mehat/OrthogonalityProducts.problem92`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Mehat/OrthogonalityProducts.problem92` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sanjit Singh Mehat (2026). *Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243*. URL: <https://arxiv.org/html/2609.05530v1>.

*Commentary.*

For any two different coordinate polynomials, an integer quaternion makes the first zero and the second nonzero. Thus no nonzero weighted difference of their squares vanishes identically. For equal coordinates, different nonzero old products also give a nonzero difference. The product of all collision polynomials and all entry polynomials is nonzero in the integer polynomial ring. MvPolynomial.funext implies that it is nonzero at some integer tuple. Appending this quaternion factor preserves nonzero entries and injectivity, so induction gives every finite length. The induction includes the empty tuple only as an auxiliary extension; Problem 9.2 asserts positive lengths. No coefficient-size bound, efficient construction, order-seven result, or full Euler-matrix theorem is asserted here.

## References

- Truth anchor: `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem91`
- Truth anchor: `D5/S3/Arith/Mehat/OrthogonalityProducts.Problem92`
- Truth anchor: `D5/S3/Arith/Mehat/OrthogonalityProducts.problem92`
- Truth anchor: `D5/S3/Arith/Mehat/OrthogonalityProducts.quaternionMatrix`
