# The Original Native Orbit Intertwiner

## Abstract

An actual projector image and a spanning E-orbit intertwine the original quotient action.

**Theorem 1.1 (The Original Native Orbit Intertwiner).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeOrbit.quotient_intertwiner`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeOrbit.quotient_intertwiner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pplus acts on the literal chosen NativeGround and equals the product over i of (I+F_i)/2, where F_i is the original normalized right action of the i-th binary unit. The nonzero-charge trace theorem from TwistedGround.OperatorAlgebra applies to these genuine original quotient elements. The projector has trace one, hence a nonzero actual image; its image seed then generates the character orbit.

The basis indexed by all 4096 binary halves consists of E_x(Pplus(seed)). Both independence and spanning are established. Its coordinate isomorphism defines intertwiner from Ground(12) into the exact original chosen carrier.

Translation acts by shifting the orbit labels, while the commuting F-subgroup acts diagonally by the distinct binary characters. These two identities give the full standard Weyl action. Restoring the original actionScalar gives an intertwiner of the actual quotient E/K representations, not an assumed equivalence or an identification of existential choices.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeOrbit.quotient_intertwiner`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/BinaryOrbit](BinaryOrbit.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/BinaryProjectorProduct](BinaryProjectorProduct.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/NativeHyperbolicActions](NativeHyperbolicActions.md)
