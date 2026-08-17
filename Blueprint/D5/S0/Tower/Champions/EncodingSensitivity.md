# Encoding-Sensitive and Encoding-Blind Quantities

## Abstract

Coding fingerprints distinguish binary, Zeckendorf, and Tribonacci coding, while their occupied first places all decode to the same unit value.

**Definition 1.1 (Fingerprint indexed by coding system).**

$$\operatorname{codingFingerprintFor}\left(\mathit{binary}\right) = \mathit{binaryCodingFingerprint} \land \left(\operatorname{codingFingerprintFor}\left(\mathit{zeckendorf}\right) = \mathit{zeckendorfCodingFingerprint} \land \operatorname{codingFingerprintFor}\left(\mathit{tribonacci}\right) = \mathit{tribonacciCodingFingerprint}\right)$$

*Formalization.* `D5/S0/Tower/Champions/EncodingSensitivity.codingFingerprintFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indexed function selects the already frozen binary, Zeckendorf, or Tribonacci coding fingerprint without changing its value.

**Definition 1.2 (First-place decoded value).**

$$\operatorname{firstPlaceDecodedValue}\left(\mathit{binary}\right) = 2^{0} \land \left(\operatorname{firstPlaceDecodedValue}\left(\mathit{zeckendorf}\right) = \operatorname{wValue}\left(0\right) \land \operatorname{firstPlaceDecodedValue}\left(\mathit{tribonacci}\right) = \operatorname{decode}\left(\mathit{tribonacciFirstDigitName}\right)\right)$$

*Formalization.* `D5/S0/Tower/Champions/EncodingSensitivity.firstPlaceDecodedValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is not a constant function by definition: its three branches use the binary positional weight, the Zeckendorf weight carrier, and the Tribonacci representation decoder, respectively.

**Theorem 1.3 (The fingerprint distinguishes coding systems).**

$$\operatorname{Injective}\left(\mathit{codingFingerprintFor}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/EncodingSensitivity.coding_fingerprint_is_encoding_sensitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity packages the frozen pairwise inequalities as sensitivity: equal fingerprint values force equal coding-system indices.

**Theorem 1.4 (First-place decoding is encoding-blind).**

$$\forall coding \in \mathit{CodingSystem},\; \operatorname{firstPlaceDecodedValue}\left(\mathit{coding}\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/EncodingSensitivity.first_place_decoded_value_is_encoding_blind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every member of the three-coding index, the independently computed occupied first place decodes to one.

This is an S0 parsing-layer comparison. It does not identify any zeta-layer object: zeta declarations live at S3 and the S0 coding interfaces provide no permitted bridge to them.

## References

- Truth anchor: `D5/S0/Tower/Champions/EncodingSensitivity.codingFingerprintFor`
- Truth anchor: `D5/S0/Tower/Champions/EncodingSensitivity.coding_fingerprint_is_encoding_sensitive`
- Truth anchor: `D5/S0/Tower/Champions/EncodingSensitivity.firstPlaceDecodedValue`
- Truth anchor: `D5/S0/Tower/Champions/EncodingSensitivity.first_place_decoded_value_is_encoding_blind`
- Dependency: [D5/S0/Tower/Champions/CodingFingerprint](CodingFingerprint.md)
