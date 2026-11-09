# Foundations of the Original Stochastic Triangle Law

## Abstract

Finite entropy, crossing supports and original common-record laws supply the binary triangle structure.

The source and output alphabets are arbitrary finite types. The source law is nonnegative and normalized, and each incident kernel is a nonnegative normalized row. Agreement annuls every off-diagonal response cell. The joint record retains all original source symbols, structural zeros and unused output symbols. Only positive incident-pair rows are forced to be point masses; zero-marginal rows remain unrestricted.

**Theorem 1.1 (Agreement forces the active original rows).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.original_law_recoverability`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.original_law_recoverability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume agreement. At each positive source cell, the product response law and agreement force all three response vectors to be point masses at one common symbol. Every positive incident-pair marginal has a positive extension. Thus its fixed kernel row is a point mass. The incident readouts agree on every positive source cell, and the record-cell identity also covers zero source cells.

**Theorem 1.2 (The common record belongs to the same law).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.original_law_common_record`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.original_law_common_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume agreement. Summing the six-variable law over the other two outputs gives recordLaw. The output weights are a probability vector. Replacing the first response by either other incident response gives the same record/source joint law.

**Theorem 1.3 (Dual total correlation is nonnegative).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.dual_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.dual_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a normalized nonnegative finite three-variable law, strong subadditivity and entropy subadditivity make its dual total correlation nonnegative.

**Theorem 1.4 (Zero dual total correlation gives a threefold product).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.dual_zero_product`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.dual_zero_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a normalized nonnegative finite three-variable law, zero dual total correlation forces the full table to equal the product of its three marginals, including zero cells.

**Theorem 1.5 (Total correlation balances pair and dual information).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.totalCorrelation_dual_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.totalCorrelation_dual_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative finite three-variable table, twice its KL total correlation equals the three pair mutual informations plus dual total correlation.

**Theorem 1.6 (Crossing support families need four coordinates).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.cardinal_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.cardinal_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If three finite support families cover the coordinates and every cross-family pair has exactly one common coordinate, at least two coordinates imply at least four.

**Theorem 1.7 (Four crossing coordinates carry parity labels).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.three_codes`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.three_codes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the crossing support families cover between two and four coordinates, each family admits a surjective Boolean label and the coordinates admit a bijection from Boolean pairs. Membership in the three families selects the first bit, second bit and their exclusive-or.

**Theorem 1.8 (Both labelled blocks have positive mass).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.mass_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.mass_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A surjective Boolean label on the positive-mass subtype gives each extended block a strictly positive mass in the original nonnegative law.

**Theorem 1.9 (The two block masses sum to one).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.mass_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.mass_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partitioning a normalized finite law by any Boolean label preserves total mass.

**Theorem 1.10 (Support codes identify every pair cell).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.cell_from_support`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.cell_from_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative product cell selected from zero or the product of the original marginals is exactly the product of the two coded marginal blocks. Positive factors imply active marginals; the identity also treats zero marginals.

**Theorem 1.11 (Parity forces fair block weights).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.fair_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.fair_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three normalized Boolean weight vectors with positive first and second weights, whose pair products agree along parity, all have weight one half in each block.

**Theorem 1.12 (Pair tables determine the original posterior).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.posterior_from_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.posterior_from_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an output has mass one quarter and its pair table is a product with second block mass one half, summing the normalized second posterior identifies the first posterior as twice the first block mass.

**Theorem 1.13 (Positive total mass has a positive entry).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.positive_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.positive_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite real table with positive sum contains a positive entry.

**Theorem 1.14 (Original record cells are nonnegative).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.record_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.record_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original record cell is the product of a nonnegative source cell and a nonnegative incident response probability.

**Theorem 1.15 (The original output law is normalized).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.output_is_probability`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.output_is_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the original record law gives a nonnegative output law of total mass one.

**Theorem 1.16 (Agreement identifies the three record tables).**

Lean statement: `D5/S3/Entropy/TriangleFourSymbolFoundation.record_eq_other_responses`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TriangleFourSymbolFoundation.record_eq_other_responses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under agreement, either other incident response gives the same record/source cell as the first response. Zero source cells are included.

## References

- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.cardinal_lower_bound`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.cell_from_support`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.dual_nonneg`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.dual_zero_product`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.fair_weights`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.mass_pos`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.mass_sum`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.original_law_common_record`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.original_law_recoverability`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.output_is_probability`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.positive_entry`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.posterior_from_pair`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.record_eq_other_responses`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.record_nonneg`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.three_codes`
- Truth anchor: `D5/S3/Entropy/TriangleFourSymbolFoundation.totalCorrelation_dual_balance`
- Dependency: [D5/S3/Divergence/ClassicalDPI](../Divergence/ClassicalDPI.md)
- Dependency: [D5/S3/Entropy/ConditionalEntropy](ConditionalEntropy.md)
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformationIndependence](MutualInformationIndependence.md)
- Dependency: [D5/S3/Entropy/Relabeling/InjectiveInvariance](Relabeling/InjectiveInvariance.md)
- Dependency: [D5/S3/Entropy/Submodularity/StrongSubadditivity](Submodularity/StrongSubadditivity.md)
