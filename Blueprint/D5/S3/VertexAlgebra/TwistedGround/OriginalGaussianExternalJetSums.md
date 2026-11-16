# Signed Diagonal Jet Generators

## Abstract

Signed Diagonal Jet Generators

**Theorem 1.1 (sourceJetMoment_generators).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<r<1 and norm(u)+r<1, set x=r and lambdaRatio=the original shifted central derivative at shift zero divided by the period. The positive Vjet sum equals 2x partial_x Mplus minus its explicit U amplitude plus Aminus(0)/2 minus 2x lambdaRatio Mplus. The negative sum multiplied by u equals 2xu partial_x Mminus minus its scaled U amplitude minus Aminus(0)/2 minus 2xu lambdaRatio Mminus. The derivatives are of the actual amplitude series on the diagonal.

**Theorem 1.2 (sourceJetMoment_generators_explicit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those same conditions the positive Vjet amplitude is Mplus times [-xu/(1-(1-x)u) -(1-2u+(1-x)u squared)/(2(1-(1-x)u)) -2x lambdaRatio] plus Aminus(0)/2. The negative Vjet sum multiplied by u is Mminus times [xu/(1-x-u) -(u(1-u)/(2(1-x-u))-1/2) -2xu lambdaRatio] minus Aminus(0)/2. Its diagonal derivative has the positive xi-minus sign. These are source-jet identifications, not the terminal J/T kernel identification.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums.sourceJetMoment_generators_explicit`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums](OriginalGaussianExternalModeSums.md)
