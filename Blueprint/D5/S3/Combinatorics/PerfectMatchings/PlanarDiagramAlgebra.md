# The literal planar diagram algebra

## Abstract

The literal planar diagram algebra

The coefficient ring R is commutative. Diagram n contains the literal boundary matchings with a noncrossing representative; there is no quotient on pairings. TL(R,n) is the free coefficient module on this set. Its multiplication is the bilinear extension of path concatenation, with every internal loop assigned zero.

**Definition 1.1 (Diagram).**

$$\forall (n: \operatorname{Nat}), (\operatorname{Diagram}\left(n\right) = \operatorname{Subtype}\left(((d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)) \mapsto \exists (M: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((2) \cdot (n)\right)), (\operatorname{toMatching}\left(M\right) = d))\right))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.Diagram` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

This is the full zero-fugacity Temperley-Lieb diagram basis.

**Definition 1.2 (TL).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\operatorname{TL}\left(R, n\right) = \operatorname{MonoidAlgebra}\left(R, \operatorname{Diagram}\left(n\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.TL` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

MonoidAlgebra supplies the finite-support coefficient carrier. No multiplication is assumed on Diagram n.

**Definition 1.3 (additiveWithOne).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\operatorname{additiveWithOne}\left(R, n\right) = \{ \operatorname{toAddCommGroup} := (\operatorname{inferInstance}: \operatorname{AddCommGroup}\left(\operatorname{TL}\left(R, n\right)\right)), \operatorname{one} := \operatorname{MonoidAlgebra}.\operatorname{single}\left(\operatorname{identity}\left(n\right), 1\right) \}))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.additiveWithOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing additive commutative group is extended by the single identity diagram with coefficient one. Here identity n is Subtype.mk (identityMatching n) (identity_planar n).

**Definition 1.4 (ring).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\operatorname{ring}\left(R, n\right) = \{ \operatorname{toAddCommGroup} := \operatorname{AddCommGroupWithOne}.\operatorname{toAddCommGroup}\left(\operatorname{additiveWithOne}\right), \operatorname{toAddGroupWithOne} := \operatorname{AddCommGroupWithOne}.\operatorname{toAddGroupWithOne}\left(\operatorname{additiveWithOne}\right), \operatorname{mul_{assoc}} := \operatorname{mul_{assoc}}', \operatorname{one_{mul}} := \operatorname{one_{mul}}', \operatorname{mul_{one}} := \operatorname{mul_{one}}', \operatorname{left_{distrib}} := \operatorname{mul_{add}}', \operatorname{right_{distrib}} := \operatorname{add_{mul}}', \operatorname{zero_{mul}} := \operatorname{zero_{mul}}', \operatorname{mul_{zero}} := \operatorname{mul_{zero}}' \}))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.ring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive projections expand the inherited additiveWithOne entry. The remaining entries are the literal Ring record fields. The existing multiplication is instMulTL; the loop cocycle gives basis associativity and linear extension gives the ring laws.

**Definition 1.5 (algebra).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\operatorname{algebra}\left(R, n\right) = \operatorname{Algebra}.\operatorname{ofModule}\left(\operatorname{smul_{mul}}', \operatorname{mul_{smul}}'\right)))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.algebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two named scalar compatibility proofs define the algebra structure from the existing R-module.

**Theorem 1.6 (single_mul_single).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\forall (a: \operatorname{Diagram}\left(n\right)), (\forall (b: \operatorname{Diagram}\left(n\right)), (\forall (r: R), (\forall (s: R), (((\operatorname{MonoidAlgebra}.\operatorname{single}\left(a, r\right): \operatorname{TL}\left(R, n\right))) \cdot (\operatorname{MonoidAlgebra}.\operatorname{single}\left(b, s\right)) = \operatorname{ite}\left(\operatorname{internalLoopCount}\left(\operatorname{Subtype}.\operatorname{val}\left(a\right), \operatorname{Subtype}.\operatorname{val}\left(b\right)\right) = 0, \operatorname{MonoidAlgebra}.\operatorname{single}\left(\operatorname{concat}\left(a, b\right), (r) \cdot (s)\right), 0\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.single_mul_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual private concat has underlying matching composite (Subtype.val a) (Subtype.val b); composite_planar supplies the subtype proof. No extra operation on diagrams is introduced.

**Definition 1.7 (generator).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right)), ((\operatorname{generator}\left(i\right): \operatorname{TL}\left(R, n\right)) = \operatorname{MonoidAlgebra}.\operatorname{single}\left(\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{cupcapMatching}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), \operatorname{by} \operatorname{omega}\right), \operatorname{cupcap_{planar}}\left(n, \operatorname{Fin}.\operatorname{val}\left(i\right), \operatorname{by} \operatorname{omega}\right)\right), 1\right))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.generator` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

The paper labels this cup-cap by Fin.val i+1; Lean uses the zero-based finite index i.

**Definition 1.8 (h).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\operatorname{h}\left(R, n\right) = -(\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}\left(\right), ((i: \operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right)) \mapsto (\operatorname{generator}\left(i\right): \operatorname{TL}\left(R, n\right)))\right))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.h` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Equation (4.69) is the negative sum of the n-1 open-boundary generators. Fin(n-1) is empty for n=0 and n=1.

**Definition 1.9 (instMulTL).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\operatorname{instMulTL}\left(R, n\right) = \operatorname{Mul}.\operatorname{mk}\left(((a: \operatorname{TL}\left(R, n\right)) \mapsto ((b: \operatorname{TL}\left(R, n\right)) \mapsto \operatorname{bilinear}\left(a, b\right)))\right)))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instMulTL` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

The literal private bilinear is the composition of two Finsupp.lift maps with MonoidAlgebra.coeffLinearEquiv.toLinearMap. Its basisProduct is MonoidAlgebra.single (concat a b) 1 when internalLoopCount a.val b.val=0, and zero otherwise.

**Definition 1.10 (instOneTL).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (n: \operatorname{Nat}), (\operatorname{instOneTL}\left(R, n\right) = \operatorname{One}.\operatorname{mk}\left(\operatorname{MonoidAlgebra}.\operatorname{single}\left(\operatorname{identity}\left(n\right), 1\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instOneTL` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

The literal private identity is Subtype.mk (identityMatching n) (identity_planar n).

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.Diagram`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.TL`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.additiveWithOne`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.algebra`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.generator`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.h`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instMulTL`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instOneTL`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.ring`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.single_mul_single`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarSewing](PlanarSewing.md)
- Dependency: [D5/S3/Topology/BrauerZeroMonoid](../../Topology/BrauerZeroMonoid.md)
- Dependency: [D5/S3/Topology/FiniteMatchingAssociativity](../../Topology/FiniteMatchingAssociativity.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](../../Topology/FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](../../Topology/FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](../../Topology/FiniteMatchingSewing.md)
