# The literal planar diagram algebra

## Abstract

The literal planar diagram algebra

A commutative coefficient ring R is arbitrary. Diagram(n) contains all boundary matchings admitting an NCMatching representative, without identifying distinct pairings. TL(R,n) is the free R-module on that set. The MonoidAlgebra wrapper supplies only coefficients and additive structure: no multiplication is installed on Diagram(n). The multiplication here is the bilinear extension of the loop-zero product. It is associative by the actual matching loop cocycle. The coefficient rings Z and C use the same construction. Fin(n-1) is empty at n=0 and n=1.

**Definition 1.1 (Diagram).**

$$\forall n \in Nat,\; \operatorname{Diagram}\left(n\right) = \operatorname{Subtype}\left(\operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right), \operatorname{HasNoncrossingRepresentative}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.Diagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HasNoncrossingRepresentative(d) means that there exists M:NCMatching(2*n) with toMatching(M)=d.

**Definition 1.2 (TL).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \operatorname{TL}\left(R, n\right) = \operatorname{MonoidAlgebra}\left(R, \operatorname{Diagram}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.TL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is exactly the finite-support coefficient functions on all diagrams, in a one-field wrapper.

**Definition 1.3 (additiveWithOne).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \operatorname{additiveWithOne}\left(R, n\right) = \operatorname{AdditiveGroupWithUnit}\left(\operatorname{FiniteSupportAddition}\left(\operatorname{Diagram}\left(n\right), R\right), \operatorname{single}\left(\operatorname{IdentityDiagram}\left(n\right), 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.additiveWithOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Addition and negation are coefficientwise, and the unit is the single identity diagram with coefficient one. Natural and integer casts are the canonical additive casts.

**Definition 1.4 (ring).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \operatorname{ring}\left(R, n\right) = \operatorname{RingStructure}\left(\operatorname{TL}\left(R, n\right), \operatorname{BilinearExtension}\left(\operatorname{LoopZeroProduct}\left(n\right)\right), \operatorname{single}\left(\operatorname{IdentityDiagram}\left(n\right), 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.ring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive structure is unchanged. Basis products use composite(d,e) with coefficient zero for any internal loop; the loop cocycle proves their associativity. Linear extension proves the full ring laws.

**Definition 1.5 (algebra).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \operatorname{algebra}\left(R, n\right) = \operatorname{AlgebraFromModule}\left(\operatorname{TL}\left(R, n\right), \operatorname{CoefficientwiseScalarAction}\left(R\right), \operatorname{algebraMap}\left(R, \operatorname{TL}\left(R, n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.algebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The algebra map sends r to r times the unit; the existing coefficientwise R-module structure is compatible with multiplication on both sides.

**Theorem 1.6 (single_mul_single).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \forall a \in \operatorname{Diagram}\left(n\right),\; \forall b \in \operatorname{Diagram}\left(n\right),\; \forall r \in R,\; \forall s \in R,\; \operatorname{Multiply}\left(\operatorname{single}\left(a, r\right), \operatorname{single}\left(b, s\right)\right) = \operatorname{If}\left(\operatorname{internalLoopCount}\left(\operatorname{val}\left(a\right), \operatorname{val}\left(b\right)\right) = 0, \operatorname{single}\left(\operatorname{PlanarComposite}\left(a, b\right), \operatorname{Multiply}\left(r, s\right)\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.single_mul_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PlanarComposite carries exactly composite(val(a),val(b)), with planarity supplied by composite_planar. This is the defining vertical concatenation rule for arbitrary coefficients.

**Definition 1.7 (generator).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \forall i \in \operatorname{Fin}\left(\operatorname{Subtract}\left(n, 1\right)\right),\; \operatorname{generator}\left(R, n, i\right) = \operatorname{single}\left(\operatorname{PlanarCupcap}\left(n, i\right), 1\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.generator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PlanarCupcap is cupcapMatching at the zero-based index; cupcap_planar provides its noncrossing witness. The printed generator label is i+1.

**Definition 1.8 (h).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \operatorname{h}\left(R, n\right) = \operatorname{Negate}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(\operatorname{Subtract}\left(n, 1\right)\right), \operatorname{generator}\left(R, n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the negative sum of the n-1 standard open-boundary generators.

**Definition 1.9 (instMulTL).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \forall a \in \operatorname{TL}\left(R, n\right),\; \forall b \in \operatorname{TL}\left(R, n\right),\; \operatorname{Multiply}\left(a, b\right) = \operatorname{bilinear}\left(a, b\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instMulTL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplication field sends (a,b) to bilinear(a)(b). Bilinear is the two successive Finsupp lifts of basisProduct(d,e): one composite basis vector when the internal loop count is zero, and zero otherwise.

**Definition 1.10 (instOneTL).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in Nat,\; \operatorname{One}\left(\operatorname{TL}\left(R, n\right)\right) = \operatorname{single}\left(\operatorname{identity}\left(n\right), 1\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instOneTL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Identity(n) is identityMatching(n) equipped with the noncrossing witness identity_planar(n).

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
