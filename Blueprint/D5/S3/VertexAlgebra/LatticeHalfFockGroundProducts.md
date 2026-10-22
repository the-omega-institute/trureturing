# Native Ground Products

## Abstract

Cocycle products in the actual chosen quotient ground module

D is an arbitrary finite integral symmetric even-diagonal lattice datum and hu:IsUnit D.G.det. groundRank and groundRepresentation are exactly the choices from actual_twisted_ground_representation D hu. No alternative finite sign representation or charge table is substituted. The actual central element acts by minus the identity; natural powers and native complexSign supply its general action.

**Theorem 1.1 (Native cocycle product).**

$$\operatorname{GroundProduct}\left(D, hu, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Exactly U_a U_b=epsilon(D,a,b) U_(a+b), from multiplication in the actual extension and quotient representation. The companion actual interchange is U_a U_b=paritySign(B(a,b)) U_b U_a. The half-norm square sign is retained. Quotient equality U_(-a)=U_a is a separate mod-two fact, not inversion. These ground relations do not themselves construct a twisted module or orbifold VOA. Classical provenance, zero novelty claim; full moonshine, string and AdS/CFT realization remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_product`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
