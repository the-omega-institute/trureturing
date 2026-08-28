# Weight-One Character Residual for Niemeier VOAs

## Abstract

Subtracting the weight-one character makes every Niemeier scalar character equal to J, while the untwined scalar remains blind to finer structure.

**Theorem 1.1 (Weight-one subtraction gives the universal character J).**

$$\left(\left(\forall N \in NiemeierVOA\left(\right),\; apply\left(scalarCharacter, N\right) = jPlusTwentyFourTimesCoxeterPlusOne\left(J, apply\left(coxeterNumber, N\right)\right)\right) \land \left(\left(\forall N \in NiemeierVOA\left(\right),\; apply\left(weightOneDimension, N\right) = twentyFourTimesCoxeterPlusOne\left(apply\left(coxeterNumber, N\right)\right)\right) \land \left(\left(apply\left(coxeterNumber, A5FourD4\left(\right)\right) = 6 \land apply\left(coxeterNumber, D4Six\left(\right)\right) = 6\right) \land \left(apply\left(theta, A5FourD4\left(\right)\right) = apply\left(theta, D4Six\left(\right)\right) \land \left(\left(\forall V \in VOAData\left(\right),\; \left(centralCharge\left(V\right) = 24 \land holomorphic\left(V\right)\right) \Rightarrow scalarCharacter\left(V\right) = addDimension\left(J, weightOneDimension\left(V\right)\right)\right) \land \left(apply\left(structureData, A5FourD4\left(\right)\right) \ne apply\left(structureData, D4Six\left(\right)\right) \land apply\left(classificationData, A5FourD4\left(\right)\right) \ne apply\left(classificationData, D4Six\left(\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall N \in NiemeierVOA\left(\right),\; weightOneResidual\left(apply\left(scalarCharacter, N\right), apply\left(weightOneDimension, N\right)\right) = J\right) \land \left(sameThetaDifferentRoot\left(theta\right) \land \left(\left(\forall V \in VOAData\left(\right),\; \left(centralCharge\left(V\right) = 24 \land holomorphic\left(V\right)\right) \Rightarrow scalarCharacter\left(V\right) = addDimension\left(J, weightOneDimension\left(V\right)\right)\right) \land \left(scalarBlindToStructure\left(scalarCharacter, structureData\right) \land classificationNeedsRefinement\left(scalarCharacter, classificationData\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/VOACompletion/WeightOneCharacterResidual.weight_one_character_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Niemeier carrier keeps the two source-named root systems A5^4 D4 and D4^6 as distinct constructors, alongside the complete list of twenty-four named Niemeier root-system constructors.

The supplied character and weight-one formulas are the preceding source identities Z = J + 24(h + 1) and dim(V1) = 24(h + 1). Pointwise subtraction proves the first conclusion. The equal Coxeter values and equal Theta witness give the concrete scalar collision.

The central-charge and holomorphicity guards remain visible in the general VOA clause. Separate structural and classification witnesses record why an untwined scalar character cannot recover multiplication, OPE, group-action, Lie, orbifold, or other fine data.

## References

- Truth anchor: `D5/S3/Analytic/VOACompletion/WeightOneCharacterResidual.weight_one_character_residual`
