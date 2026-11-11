# Serre G2 and its seven-dimensional representation

## Abstract

An actual matrix image of the standard Serre G2 algebra.

**Definition 1.1 (Fourteen explicit matrices).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (i : \operatorname{Fin}\left(14\right)), (\operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), k\right)))$$

*Formalization.* `D5/S3/QuadraticForms/SerreG2MatrixImage.basisMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrices are two coroots, six positive and six negative root vectors in dimension seven. This is concrete matrix data; it does not define a dimension-tagged replacement for G2.

**Definition 1.2 (An actual matrix Lie subalgebra).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \operatorname{LieSubalgebra}\left(k, \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), k\right)\right))$$

*Formalization.* `D5/S3/QuadraticForms/SerreG2MatrixImage.matrixImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear span of the fourteen matrices is proved closed under the actual matrix commutator. Every entry of its complete bracket table is a universal identity over the stated field. The kernel checks the matrix identities; an external finite checker is not a proof premise.

**Theorem 1.3 (Dimension of the actual matrix image).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \operatorname{Module}.\operatorname{finrank}\left(k, \operatorname{matrixImage}\left(k\right)\right) = 14)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SerreG2MatrixImage.matrixImage_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Explicit coordinate extraction is a left inverse to assembly. It gives a linear equivalence from k to the power fourteen onto the matrix image and proves its dimension fourteen.

**Definition 1.4 (Map from mathlib's actual Serre G2).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \operatorname{LieHom}\left(k, \operatorname{LieAlgebra}.\operatorname{g}_{2}\left(k\right), \operatorname{matrixImage}\left(k\right)\right))$$

*Formalization.* `D5/S3/QuadraticForms/SerreG2MatrixImage.serreMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six Chevalley generators satisfy the actual CartanMatrix.G₂ Serre relations in the matrix image. The universal free Lie map therefore descends through exactly mathlib's Serre quotient, producing a genuine Lie homomorphism from LieAlgebra.g₂ k.

**Theorem 1.5 (Surjectivity from actual Serre words).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \operatorname{Function}.\operatorname{Surjective}\left(\operatorname{serreMap}\left(k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SerreG2MatrixImage.serreMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fourteen explicit Lie words in the actual Serre generators map to the fourteen spanning matrices. Their linear combinations prove surjectivity onto the whole matrix image.

**Definition 1.6 (Proved correspondence under simplicity).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] [\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, \operatorname{LieAlgebra}.\operatorname{g}_{2}\left(k\right)\right)] \operatorname{LieEquiv}\left(k, \operatorname{LieAlgebra}.\operatorname{g}_{2}\left(k\right), \operatorname{matrixImage}\left(k\right)\right))$$

*Formalization.* `D5/S3/QuadraticForms/SerreG2MatrixImage.correspondence_of_isSimple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If the actual Serre G2 algebra is simple, the nonzero surjection has zero kernel and is an actual Lie equivalence to the fourteen-dimensional matrix image. A hypothetical isomorphism from a nonabelian simple ideal supplies this hypothesis in the KMV exclusion. No unconditional normal-form theorem or unconditional dimension computation for the Serre presentation is assumed. This correspondence suffices for that exclusion. Classical Serre and G2 matrix facts receive prior credit; the evolution-algebra application retains Haobo Ma then Wenlin Zhang attribution.

## References

- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixImage.basisMatrix`
- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixImage.correspondence_of_isSimple`
- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixImage.matrixImage`
- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixImage.matrixImage_finrank`
- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixImage.serreMap`
- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixImage.serreMap_surjective`
- Dependency: [D5/S3/QuadraticForms/SerreG2MatrixTable](SerreG2MatrixTable.md)
