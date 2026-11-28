# Simplicity of the inner Lie algebra does not imply simplicity of the axial algebra

## Abstract

A rational primitive Jordan-half axial algebra with a proper scalar ideal has simple selected-axis inner Lie algebra.

**Definition 1.1 (The rational primitive Jordan-half converse).**

$$\operatorname{claim} \Leftrightarrow (\forall A \in \operatorname{Type},\; (\forall L \in A \to \operatorname{End}\left(\mathbb{Q}, A\right),\; (\forall X \in \operatorname{Set}\left(A\right),\; ((\forall a \in A,\; (\forall b \in A,\; (L\left(a\right)\left(b\right) = L\left(b\right)\left(a\right)))) \Rightarrow ((\forall a \in A,\; ((a \in X) \Rightarrow (\operatorname{IsAxis}\left(L, a\right)))) \Rightarrow ((\operatorname{Generates}\left(L, X\right)) \Rightarrow ((\operatorname{IsSimple}\left(\mathbb{Q}, (\operatorname{selectedLie}\left(L, X\right))\right)) \Rightarrow (\operatorname{AlgebraSimple}\left(L\right)))))))))$$

*Formalization.* `D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.claim` (`✓ std3`).

*Citation.* Ilya Gorshkov, Sergey Shpectorov (2026). *Axial Algebras: Questions and Conjectures*. DOI: [10.46298/cm.19581](https://doi.org/10.46298/cm.19581). URL: <https://arxiv.org/abs/2606.30048v1>.

*Commentary.*

The type binder for A has the Lean typeclass assumptions AddCommGroup A, Module ℚ A and FiniteDimensional ℚ A. The bilinear map L defines multiplication by L(a)(b). Its symmetry gives commutativity. IsAxis uses the actual eigenspaces of L(a) at 1, 0 and 1/2. It requires a nonzero idempotent, its line as the 1-eigenspace, spanning by the three eigenspaces and the six products of the Jordan-half fusion table. Distinct eigenspaces are independent. Generates requires every multiplication-closed linear subspace containing X to be the whole space. The selectedLie subalgebra is the Lie span of [L(a), L(b)] for a and b in X. AlgebraSimple means that every subspace stable under all left multiplications is zero or the whole space. In the published converse, choose the field ℚ and the Jordan-half fusion law, then restrict to finite dimension and primitive axes. Every such instance of the printed implication yields the displayed claim.

**Theorem 1.2 (The scalar summand gives a counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ilya Gorshkov, Sergey Shpectorov (2026). *Axial Algebras: Questions and Conjectures*. DOI: [10.46298/cm.19581](https://doi.org/10.46298/cm.19581). URL: <https://arxiv.org/abs/2606.30048v1>.

*Commentary.*

The algebra is (ℚ × ℚ³) × ℚ with the spin product on the first factor and the ordinary scalar product on the last factor. The chosen generators are the two spin axes for each coordinate and the last-factor unit z. The spin axes have 1-eigenline equal to their own line, 0-eigenspace given by the opposite spin line and ℚz, and half-eigenspace given by the perpendicular vectors. For z the corresponding spaces are ℚz, the spin factor and zero. The chosen axes already span linearly and ℚz is a nonzero proper ideal. Every chosen commutator acts by a skew matrix on the three vector coordinates and by zero on both scalar coordinates. The positive-coordinate axes yield the elementary skew matrices up to a factor of 1/4. The frozen orthogonal simplicity theorem applies to the resulting Lie equivalence.

## References

- Truth anchor: `D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/AxialInnerLieConverseRefutation.result`
- Dependency: [D5/S3/QuadraticForms/OrthogonalLieStructure](OrthogonalLieStructure.md)
