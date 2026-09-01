# The Fourth-Stage Unified Theorem Map

## Abstract

The fourth stage links observable algebras, finite quotients, coding, class groups, and spectral limits.

**Theorem 1.1 (Static, finite-quotient, coding, valuation, and spectral chains).**

$$ObservableAlgebraRepresentation \land {Refinement \iff PullbackInclusion} \land {PrimePowerResidualTrivial \iff Nilpotent} \land ConjugacyClassSuccessRate \land ExactResidueDistance \land ErrorErasureDecoding \land ClassGroupQuotient \land TraceSaturation \land NonSimilarityWitness.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/FourthStageUnifiedTheoremMap.fourth_stage_unified_theorem_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Observable events are the powerset of the realized image, while refinement is equivalent to inclusion of pullback algebras.

For finite groups, prime-power residual triviality is nilpotence; conjugacy-invariant separation has an exact finite success rate.

The bounded CRT code has exact distance n minus its largest blind coordinate count and uniquely decodes within the joint error-erasure budget.

Principal-trivial ideal homomorphisms descend uniquely to the class group under the Dedekind hypotheses.

Cayley-Hamilton controls higher traces once the characteristic polynomial is fixed, but a concrete Jordan witness shows that all power traces still do not determine similarity.

## References

- Truth anchor: `D5/S3/PrimeObserver/FourthStageUnifiedTheoremMap.fourth_stage_unified_theorem_map`
- Dependency: [D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation](../../S0/Observation/PowerTraceCharacteristicPolynomialSaturation.md)
- Dependency: [D5/S0/Observation/PowerTraceSimilarityCountermodel](../../S0/Observation/PowerTraceSimilarityCountermodel.md)
- Dependency: [D5/S3/Arith/Coding/ErrorErasureUniqueDecoding](../Arith/Coding/ErrorErasureUniqueDecoding.md)
- Dependency: [D5/S3/Arith/Coding/ExactResidueCodeMinimumDistance](../Arith/Coding/ExactResidueCodeMinimumDistance.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraRepresentation](../ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraRepresentation.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraRefinementDuality](../ConceptDynamics/RefinementAlgebra/PullbackAlgebraRefinementDuality.md)
- Dependency: [D5/S3/Factorization/Galois/ClassFunctionSeparationRate](../Factorization/Galois/ClassFunctionSeparationRate.md)
- Dependency: [D5/S3/Factorization/IdealClassGroups/ClassGroupQuotientUniversality](../Factorization/IdealClassGroups/ClassGroupQuotientUniversality.md)
- Dependency: [D5/S3/Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness](../Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness.md)
