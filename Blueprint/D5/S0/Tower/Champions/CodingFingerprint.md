# Coding Spectrum Fingerprint

## Abstract

The first-place Binet main term divided by its decoded value distinguishes three coding systems.

**Definition 1.1 (Scale-independent coding fingerprint).**

$$\mathit{codingFingerprint} = \frac{\mathit{leadingMainTerm}}{\mathit{decodedValue}}$$

*Formalization.* `D5/S0/Tower/Champions/CodingFingerprint.codingFingerprint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fingerprint is the leading first-place expansion main term divided by the value decoded from that first place.

**Theorem 1.2 (Common rescaling does not change the fingerprint).**

$$\forall leadingMainTerm \in R, decodedValue \in R, scale \in R,\; \mathit{scale} \ne 0 \Rightarrow \frac{\mathit{scale} \cdot \mathit{leadingMainTerm}}{\mathit{scale} \cdot \mathit{decodedValue}} = \frac{\mathit{leadingMainTerm}}{\mathit{decodedValue}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/CodingFingerprint.coding_fingerprint_scale_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying both the Binet main term and the decoded value by one nonzero scale cancels exactly in the quotient.

**Theorem 1.3 (The shifted Tribonacci coefficient is the frozen coefficient times t).**

$$\frac{t^{2}}{3 \cdot t^{2} - 2 \cdot t - 1} = a \cdot t$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/CodingFingerprint.tribonacci_binet_normalization_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative-form coefficient for powers t to n minus one equals the frozen coefficient for powers t to n multiplied by t. The proof uses the frozen Tribonacci cubic equation.

**Theorem 1.4 (Binary fingerprint).**

$$\mathit{rBinary} = 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/CodingFingerprint.binary_coding_fingerprint_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first binary main term and its decoded positional weight are both one.

**Theorem 1.5 (Zeckendorf fingerprint).**

$$\mathit{rZeckendorf} = \frac{\mathit{phi}^{2}}{\operatorname{sqrt}\left(5\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/CodingFingerprint.zeckendorf_coding_fingerprint_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first Zeckendorf position decodes to Fib two, hence to one, while its exact Perron main term is phi squared over square root five.

**Theorem 1.6 (Tribonacci fingerprint).**

$$\mathit{rTribonacci} = \frac{t^{2}}{3 \cdot t^{2} - 2 \cdot t - 1} \cdot t^{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/CodingFingerprint.tribonacci_coding_fingerprint_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied first Tribonacci digit decodes to one through the frozen representation carrier, leaving the shifted Binet coefficient times t squared.

**Theorem 1.7 (The three coding fingerprints are pairwise distinct).**

$$\mathit{rBinary} \ne \mathit{rZeckendorf} \land \left(\mathit{rBinary} \ne \mathit{rTribonacci} \land \mathit{rZeckendorf} \ne \mathit{rTribonacci}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/CodingFingerprint.coding_fingerprint_values_pairwise_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact ordered-field estimates give one below the Zeckendorf value, the Zeckendorf value below two, and two below the Tribonacci value.

## References

- Truth anchor: `D5/S0/Tower/Champions/CodingFingerprint.binary_coding_fingerprint_value`
- Truth anchor: `D5/S0/Tower/Champions/CodingFingerprint.codingFingerprint`
- Truth anchor: `D5/S0/Tower/Champions/CodingFingerprint.coding_fingerprint_scale_invariant`
- Truth anchor: `D5/S0/Tower/Champions/CodingFingerprint.coding_fingerprint_values_pairwise_distinct`
- Truth anchor: `D5/S0/Tower/Champions/CodingFingerprint.tribonacci_binet_normalization_bridge`
- Truth anchor: `D5/S0/Tower/Champions/CodingFingerprint.tribonacci_coding_fingerprint_value`
- Truth anchor: `D5/S0/Tower/Champions/CodingFingerprint.zeckendorf_coding_fingerprint_value`
- Dependency: [D5/S0/Tower/GoldenNames](../GoldenNames.md)
- Dependency: [D5/S0/Tower/Tribonacci/Binet](../Tribonacci/Binet.md)
- Dependency: [D5/S0/Tower/Tribonacci/Representation](../Tribonacci/Representation.md)
