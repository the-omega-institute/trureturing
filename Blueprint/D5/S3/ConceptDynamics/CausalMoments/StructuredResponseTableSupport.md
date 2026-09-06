# Exact support cost and structured table families

## Abstract

The quaternary coding gives an exact capacity count. A smaller structured generator is a genuine model restriction unless the omitted tables already have zero mass or are excluded by justified cross-stratum structure.

**Definition 1.1 (Cover every positive-mass table).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.SupportsLaw`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.SupportsLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A deterministic latent-state generator is exact for a law only when every positive-mass atom is produced by some latent state.

**Theorem 1.2 (Universal table generation needs 4^k states).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.surjective_response_table_generator_requires_four_pow`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.surjective_response_table_generator_requires_four_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Surjectivity onto all k-row Boolean response tables forces at least 4^k deterministic latent states by finite cardinality.

**Theorem 1.3 (Every smaller family omits a table).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.small_generator_not_universal`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.small_generator_not_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any latent family below the radix capacity fails to cover the unrestricted table carrier. This is a support statement, not a DFAO-state lower bound.

**Theorem 1.4 (Twenty-one latent atoms cannot cover three unrestricted rows).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.twenty_one_latent_states_not_universal_three_rows`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.twenty_one_latent_states_not_universal_three_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three quaternary rows already give 64 possible tables, so a 21-element latent carrier is not universal. The number 21 mirrors the current golden powers-only draft scale solely to make the complexity distinction explicit; no automaton-minimality conclusion follows.

**Theorem 1.5 (Positive row kernels fill the full table space).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.independentResponseTable_full_support`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.independentResponseTable_full_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity of all four row-response masses makes every complete table have positive product mass.

**Theorem 1.6 (Full-support probability laws inherit the capacity lower bound).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.positive_independent_table_law_generator_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.positive_independent_table_law_generator_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact deterministic latent generator of the positive independent-row law must cover every table and therefore needs at least 4^k states.

**Theorem 1.7 (Compression requires a restricted model family).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.positive_independent_table_law_not_supported_by_small_generator`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.positive_independent_table_law_not_supported_by_small_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A smaller latent carrier cannot reproduce a full-support independent-row law exactly. Automata can still give short algorithmic descriptions of structured tables because that is a different complexity notion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.SupportsLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.independentResponseTable_full_support`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.positive_independent_table_law_generator_lower_bound`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.positive_independent_table_law_not_supported_by_small_generator`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.small_generator_not_universal`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.surjective_response_table_generator_requires_four_pow`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/StructuredResponseTableSupport.twenty_one_latent_states_not_universal_three_rows`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding](QuaternaryResponseTableCoding.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping](../PartialIdentification/FiniteIndependentSourceGrouping.md)
