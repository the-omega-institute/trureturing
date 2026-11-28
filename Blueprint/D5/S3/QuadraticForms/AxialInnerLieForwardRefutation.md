# Simplicity of the axial algebra does not imply simplicity of the inner Lie algebra

## Abstract

The simple rational spin factor with four vector coordinates has a selected-axis inner Lie algebra with a proper nonzero ideal.

**Definition 1.1 (The rational primitive Jordan-half forward implication).**

$$\operatorname{claim} \Leftrightarrow (\forall A \in \operatorname{Type},\; ([\operatorname{AddCommGroup}\left(A\right)] [\operatorname{Module}\left(\mathbb{Q}, A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{Q}, A\right)] \forall L \in \operatorname{LinearMap}\left(\mathbb{Q}, A, \operatorname{End}\left(\mathbb{Q}, A\right)\right),\; (\forall X \in \operatorname{Set}\left(A\right),\; ((\forall a \in A,\; (\forall b \in A,\; (L\left(a\right)\left(b\right) = L\left(b\right)\left(a\right)))) \Rightarrow ((\forall a \in A,\; ((a \in X) \Rightarrow (\operatorname{IsAxis}\left(L, a\right)))) \Rightarrow ((\operatorname{Generates}\left(L, X\right)) \Rightarrow ((\operatorname{AlgebraSimple}\left(L\right)) \Rightarrow (\operatorname{IsSimple}\left(\mathbb{Q}, (\operatorname{selectedLie}\left(L, X\right))\right)))))))))$$

*Formalization.* `D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.claim` (`✓ std3`).

*Citation.* Ilya Gorshkov, Sergey Shpectorov (2026). *Axial Algebras: Questions and Conjectures*. DOI: [10.46298/cm.19581](https://doi.org/10.46298/cm.19581). URL: <https://arxiv.org/abs/2606.30048v1>.

*Commentary.*

The endomorphisms in End(ℚ,A) are ℚ-linear. The linear map L defines multiplication by L(a)(b). Its symmetry gives commutativity. IsAxis uses the actual eigenspaces of L(a) at 1, 0 and 1/2. It requires a nonzero idempotent, its line as the 1-eigenspace, spanning by the three eigenspaces and the six products of the Jordan-half fusion table. Distinct eigenspaces are independent. Generates requires every multiplication-closed linear subspace containing X to be the whole space. The selectedLie subalgebra is the Lie span of [L(a), L(b)] for a and b in X. AlgebraSimple means that every subspace stable under all left multiplications is zero or the whole space.

**Theorem 1.2 (The rational spin factor gives a counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ilya Gorshkov, Sergey Shpectorov (2026). *Axial Algebras: Questions and Conjectures*. DOI: [10.46298/cm.19581](https://doi.org/10.46298/cm.19581). URL: <https://arxiv.org/abs/2606.30048v1>.

*Commentary.*

The carrier is ℚ × ℚ⁴, with multiplication (a,u)(b,v) = (ab + u·v, av + bu). The chosen axes are (1/2, ±eᵢ/2) for the four standard basis vectors. Their actual 1-eigenspaces are their own lines, their 0-eigenspaces are the opposite spin lines, and their half-eigenspaces are the vectors perpendicular to the corresponding basis vectors. The two signed axes for each coordinate linearly generate the unit and all basis vectors. If an algebra ideal contains an element with a nonzero vector component, a commutator of two coordinate left multiplications gives a nonzero pure vector in the ideal. Its square is a nonzero rational multiple of the unit. An ideal containing a nonzero scalar also contains the unit and hence is the whole space. The unit (1,0) is nonzero and squares to itself. Together with the ideal calculation, this makes the witness simple under the usual nonzero simplicity convention. The published forward implication would therefore force its selected-axis inner Lie algebra to be simple. The selected-axis Lie span is isomorphic to the standard so₄(ℚ) acting on the vector coordinates. Under the resulting isomorphism with so₃(ℚ) × so₃(ℚ), the preimage of the kernel of the second projection contains the preimage of (r,0) and excludes the preimage of (0,r), where r is the elementary skew matrix with entry 1 in row 0, column 1. This gives a nonzero proper Lie ideal.

## References

- Truth anchor: `D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.result`
- Dependency: [D5/S3/QuadraticForms/OrthogonalLieStructure](OrthogonalLieStructure.md)
