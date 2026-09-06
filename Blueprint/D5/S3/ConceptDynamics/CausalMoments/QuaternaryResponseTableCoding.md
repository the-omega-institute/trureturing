# Quaternary response-table coding and the golden power input

## Abstract

A Boolean complete response pair is one quaternary symbol. A k-row table is therefore a k-digit radix-four word, while the golden DFAO at index k receives the Zeckendorf representation of the corresponding capacity boundary 4^k.

**Definition 1.1 (Encode one response pair as a base-four digit).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responsePairDigitEquiv`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responsePairDigitEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The control bit is the high binary bit and the treatment bit is the low bit. This is a coding equivalence and imposes no response-coordinate independence.

**Definition 1.2 (Encode a full table coordinatewise).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableDigitEquiv`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableDigitEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib piCongrRight transports the one-row equivalence across all strata.

**Definition 1.3 (Radix-four integer code).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableCodeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableCodeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib finFunctionFinEquiv identifies k quaternary digits with an integer code below four to the k.

**Theorem 1.4 (Exact table-space cardinality).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTable_card_eq_four_pow`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTable_card_eq_four_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unrestricted k-stratum carrier of Boolean complete response pairs has cardinality exactly 4^k.

**Theorem 1.5 (Codes lie below the capacity boundary).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableCode_lt_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableCode_lt_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual k-digit table code lies strictly below 4^k. The number 4^k is the one-past-the-last radix capacity, rather than the code of a table.

**Theorem 1.6 (The golden DFAO reads the table-space capacity).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.golden_base4_power_word_is_response_table_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.golden_base4_power_word_is_response_table_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing golden input base4PowerWord k is the Zeckendorf encoding of 4^k, which is also the exact cardinality of the k-row response-table carrier. This does not identify DFAO state count with causal support size.

**Definition 1.7 (Embed a golden digit prefix as one response table).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first k base-four digits of the golden ratio select one distinguished quaternary response table through the standard pair decoder.

**Definition 1.8 (Choose one node at each table-tree level).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefixCode`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefixCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinguished k-row prefix is encoded as one concrete element of Fin(4^k). The coordinate orientation is inherited from Mathlib's explicit radix equivalence.

**Theorem 1.9 (Recover each golden digit).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix_digit`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix_digit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Re-encoding a row of the distinguished table returns the corresponding existing golden base-four digit.

**Theorem 1.10 (Successive prefixes form one nested path).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix_castSucc`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix_castSucc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Passing from k to k+1 preserves every old row. The golden digit sequence therefore selects one path through the rooted four-ary tree whose level k contains all 4^k response tables.

**Theorem 1.11 (The selected node remains inside the full capacity).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefixCode_lt_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefixCode_lt_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected level-k node is one of the 4^k possible tables, so its code lies below the same boundary whose Zeckendorf representation is fed to the golden DFAO.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefixCode`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefixCode_lt_capacity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix_castSucc`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.goldenResponsePrefix_digit`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.golden_base4_power_word_is_response_table_capacity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responsePairDigitEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableCodeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableCode_lt_capacity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTableDigitEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/QuaternaryResponseTableCoding.responseTable_card_eq_four_pow`
- Dependency: [D5/S1/Digit/GoldenBase4AutomataOracle](../../../S1/Digit/GoldenBase4AutomataOracle.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable](FiniteConditionalResponseTable.md)
