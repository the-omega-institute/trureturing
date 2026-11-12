# Standard orthogonal Lie algebras

## Abstract

Classical structure of actual standard orthogonal Lie algebras.

**Theorem 1.1 (Actual simplicity outside dimension four).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (n : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] 3 \le \operatorname{Fintype}.\operatorname{card}\left(n\right) \Rightarrow \left(\operatorname{Fintype}.\operatorname{card}\left(n\right) \ne 4 \Rightarrow \operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(n, k\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalLieStructure.isSimple_of_card_ne_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every characteristic-zero field, actual so_n is nonabelian simple when the finite index type has cardinality three or at least five. Double rotation brackets give coordinate projectors. Two projectors isolate a nonzero rotation in size three; four projectors isolate it when five distinct indices are available. Brackets of that rotation generate all rotations and hence the whole algebra. This proves the ideal dichotomy for actual matrix ideals. Size four is treated by the separate actual split equivalence.

**Theorem 1.2 (Trivial radical outside dimension four).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (n : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] 3 \le \operatorname{Fintype}.\operatorname{card}\left(n\right) \Rightarrow \left(\operatorname{Fintype}.\operatorname{card}\left(n\right) \ne 4 \Rightarrow \operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(n, k\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalLieStructure.hasTrivialRadical_of_card_ne_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field and every finite decidable index type of cardinality at least three and different from four, the actual standard orthogonal matrix Lie algebra has zero solvable radical. The proved actual simplicity supplies trivial solvable radical through mathlib’s standard instance. This is classical structure, not a novelty claim.

**Definition 1.3 (The actual dimension-four split).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] soFourEquiv : \operatorname{LieEquiv}\left(k, \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(4\right), k\right), \operatorname{Prod}\left(\operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(3\right), k\right), \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(3\right), k\right)\right)\right))$$

*Formalization.* `D5/S3/QuadraticForms/OrthogonalLieStructure.soFourEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field, this explicit Lie equivalence maps a skew four-by-four matrix with upper entries (a,b,c,d,e,f) to skew three-by-three matrices with upper triples (a+f,b-e,c+d) and (a-f,b+e,d-c). The inverse recovers a=(pL+pR)/2, b=(qL+qR)/2, c=(rL-rR)/2, d=(rL+rR)/2, e=(qR-qL)/2 and f=(pL-pR)/2. The linear inverse and bracket identities are proved for the actual matrices. No algebraic-closedness hypothesis is used.

**Theorem 1.4 (Trivial radical in dimension four).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(4\right), k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalLieStructure.so_four_hasTrivialRadical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit split and the radical-free dimension-three factors imply zero actual solvable radical in dimension four.

**Theorem 1.5 (All dimensions at least three).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (m : \operatorname{Nat}\left(\right)), (3 \le m \Rightarrow \operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(m\right), k\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalLieStructure.hasTrivialRadical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field and every integer m at least three, so_m has zero actual solvable radical, including m=4. This theorem alone does not prove simplicity, classify evolution derivations, identify their radical quotient, or exclude the genuine Serre G2 algebra. Those remain separate obligations of the Ma-then-Zhang credited KMV application.

## References

- Truth anchor: `D5/S3/QuadraticForms/OrthogonalLieStructure.hasTrivialRadical`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalLieStructure.hasTrivialRadical_of_card_ne_four`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalLieStructure.isSimple_of_card_ne_four`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalLieStructure.soFourEquiv`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalLieStructure.so_four_hasTrivialRadical`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification](EvolutionAlgebras/SemisimpleDerivationClassification.md)
- Dependency: [D5/S3/QuadraticForms/LieRadicalTransfer](LieRadicalTransfer.md)
