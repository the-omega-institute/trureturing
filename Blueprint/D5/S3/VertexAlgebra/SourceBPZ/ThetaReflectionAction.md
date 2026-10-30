# Theta Reflection Action

## Abstract

The order-two lattice reflection action and its fixed-grade coevaluation invariants.

D is the existing arbitrary integral even lattice datum. Carrier D is the original finite-charge oscillator carrier, theta D is the literal charge-and-oscillator reflection, sourcePairing D is the original complex bilinear form, and grade D h intersect fixedSpace D is the existing finite-energy theta-fixed submodule. ReflectionGroup is the additive group ZMod 2. thetaRepHom packages the reflection as an additive homomorphism into the permutation group of Carrier D, so its nonzero element is the reflection.

**Theorem 1.1 (Identity element acts trivially).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, thetaRep D 0 is the identity linear equivalence of Carrier D.

**Theorem 1.2 (Generator is the lattice theta involution).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, thetaRep D 1 is exactly the existing theta D linear equivalence.

**Theorem 1.3 (The reflection is the nontrivial order-two element).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_neg_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, thetaRep D (-1) equals theta D, using the equality -1 = 1 in ZMod 2.

**Theorem 1.4 (Reflection preserves the source pairing).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, g:ZMod 2 and u,v:Carrier D, sourcePairing D (thetaRep D g u) (thetaRep D g v) = sourcePairing D u v.

**Theorem 1.5 (The restricted action on fixed vectors is trivial).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, g:ZMod 2 and v in fixedSpace D, thetaRep D g v.val = v.val.

**Theorem 1.6 (Fixed-grade coevaluation is reflection invariant).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.coevaluation_fixed_under_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.coevaluation_fixed_under_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, signed grade h and functional on grade D h intersect fixedSpace D, thetaRep D (-1) applied to the coevaluation value equals that value.

The representation packages the already proved theta involution and source-pairing isometry; it adds no positivity, nondegeneracy or orbit-representative choice. The coevaluation statement is an algebraic consequence of its fixedSpace codomain. It does not claim a complete lattice vertex algebra, modularity, fusion, or analytic completion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.coevaluation_fixed_under_reflection`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_fixed`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_neg_one`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_one`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.thetaRep_zero`
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation](OriginalSourceCoevaluation.md)
