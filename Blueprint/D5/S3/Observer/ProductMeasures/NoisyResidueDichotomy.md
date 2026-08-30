# Noisy Residue Kakutani Dichotomy

## Abstract

Noisy residue transcripts split into singular and equivalent regimes by energy.

**Definition 1.1 (Noisy residue coordinate law).**

$$\operatorname{noisyResidueLaw}\left(r, K, x, i\right) = \operatorname{K}\left(i, \operatorname{r}\left(i, x\right)\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.noisyResidueLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state residue is passed through its coordinate channel.

**Definition 1.2 (Pairwise local Hellinger energy).**

$$\operatorname{pairLocalHellingerEnergy}\left(L, x, y, i\right) = \operatorname{energy}\left(\operatorname{L}\left(x, i\right), \operatorname{L}\left(y, i\right)\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.pairLocalHellingerEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The energy compares the two state-dependent coordinate laws.

**Definition 1.3 (Blind coordinate set).**

$$\operatorname{blindCoordinates}\left(L, x, y\right) = \operatorname{zeroSet}\left(\operatorname{pairLocalHellingerEnergy}\left(L, x, y\right)\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.blindCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coordinate is blind when its local Hellinger energy is zero.

**Definition 1.4 (Infinite observation transcript).**

$$\operatorname{infiniteTranscript}\left(X, omega, i\right) = \operatorname{X}\left(i, omega\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.infiniteTranscript` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transcript evaluates the coordinate observation at one sample.

**Definition 1.5 (State transcript product law).**

$$\operatorname{transcriptLaw}\left(L, x\right) = \operatorname{productLaw}\left(\operatorname{L}\left(x\right)\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.transcriptLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law is the countable product of a state's coordinate PMFs.

**Theorem 1.6 (Noisy residue product completion criterion).**

$$\operatorname{MutuallySingular}\left(\operatorname{transcriptLaw}\left(L, x\right), \operatorname{transcriptLaw}\left(L, y\right)\right) \Leftrightarrow \neg \operatorname{Summable}\left(\operatorname{pairEnergy}\left(L, x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.noisy_residue_product_completion_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under local equivalence, singularity is exactly nonsummable energy.

**Theorem 1.7 (Independent transcript completion criterion).**

$$\operatorname{MutuallySingular}\left(\operatorname{mappedTranscriptLaw}\left(P, X\right), \operatorname{mappedTranscriptLaw}\left(Q, Y\right)\right) \Leftrightarrow \neg \operatorname{Summable}\left(\operatorname{pairEnergy}\left(L, x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.noisy_residue_independent_completion_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent observations have the coordinate product law, so the criterion applies to their mapped transcript laws.

**Theorem 1.8 (Equal local laws have zero total energy).**

$$\operatorname{pairEnergy}\left(L, x, y\right) = 0 \land \left(\operatorname{totalEnergy}\left(L, x, y\right) = 0 \land \operatorname{transcriptLaw}\left(L, x\right) = \operatorname{transcriptLaw}\left(L, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.equal_local_laws_zero_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality coordinate by coordinate gives zero energy and equal products.

**Theorem 1.9 (Singleton outputs have zero energy).**

$$\operatorname{singletonOutputEnergy}\left(i\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.singleton_output_energy_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique PMF on a singleton agrees with itself at every coordinate.

**Theorem 1.10 (Empty outputs carry no PMF).**

$$\operatorname{IsEmpty}\left(\operatorname{PMF}\left(\emptyset\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.empty_output_has_no_pmf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization rules out a probability mass function on the empty type.

**Theorem 1.11 (Local equivalence is necessary).**

$$\operatorname{ExistsFiniteEnergySingularProductsWithoutLocalEquivalence}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.local_mutual_absolute_continuity_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single disjoint coordinate gives finite energy but singular products.

**Theorem 1.12 (Coordinate independence is necessary).**

$$\operatorname{ExistsDependentEqualMarginalZeroEnergySingularTranscripts}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.coordinate_independence_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two dependent Boolean transcripts share every marginal and zero energy, yet their full laws are singular.

## References

- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.blindCoordinates`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.coordinate_independence_is_necessary`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.empty_output_has_no_pmf`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.equal_local_laws_zero_energy`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.infiniteTranscript`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.local_mutual_absolute_continuity_is_necessary`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.noisyResidueLaw`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.noisy_residue_independent_completion_criterion`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.noisy_residue_product_completion_criterion`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.pairLocalHellingerEnergy`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.singleton_output_energy_zero`
- Truth anchor: `D5/S3/Observer/ProductMeasures/NoisyResidueDichotomy.transcriptLaw`
- Dependency: [D5/S3/Observer/ProductMeasures/FinitePmfDichotomy](FinitePmfDichotomy.md)
