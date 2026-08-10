# Diagonal Capture Count

## Abstract

Finite diagonal capture intersections have exact counts and factor independently.

**Lemma 1.1 (Simultaneous captures have an exact cardinality).**

$$\operatorname{card}\left(\operatorname{capturedListings}\left(f, S\right)\right) = \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)^{\operatorname{card}\left(S\right)} \cdot \operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right) \cdot \left(\operatorname{card}\left(A\right) - \operatorname{card}\left(S\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/CaptureCount.capture_inter_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set of selected rows, each selected diagonal entry is chosen from the fixed points of the twist. All rows outside the selection remain free, and the selected rows are then determined.

**Theorem 1.2 (Capture intersections factor in integer form).**

$$\operatorname{card}\left(\operatorname{capturedListings}\left(f, S\right)\right) \cdot \left(\operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right)^{2}}\right)^{\operatorname{card}\left(S\right)} = \left(\operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) \cdot \operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right) \cdot \left(\operatorname{card}\left(A\right) - 1\right)}\right)^{\operatorname{card}\left(S\right)} \cdot \operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/CaptureCount.capture_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After clearing every denominator, the count of a simultaneous capture times the corresponding power of the full listing count equals the product of the single-row capture counts.

**Theorem 1.3 (Fixed-point-free twists have the full escape count).**

$$\operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) = 0 \Rightarrow \operatorname{card}\left(\operatorname{escapedListings}\left(f\right)\right) = \operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/CaptureCount.escaped_card_of_fixfree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the twist has no fixed point, the previously established exact escape count reduces to the cardinality of the full finite listing space.

**Theorem 1.4 (Fixed-point-free twists escape every listing).**

$$\operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) = 0 \Rightarrow \operatorname{allListingsEscaped}\left(f\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/CaptureCount.escape_all_of_fixfree` (`✓ std3`). ∎

*Citation.* F. William Lawvere (1969). *Diagonal arguments and cartesian closed categories*. DOI: [10.1007/BFb0080769](https://doi.org/10.1007/BFb0080769).

*Commentary.*

The full escape count equals the size of the ambient listing type, so any unescaped listing would force a strict cardinality deficit. Thus every listing is escaped.

## References

- Truth anchor: `D5/S0/Diagonal/CaptureCount.capture_independent`
- Truth anchor: `D5/S0/Diagonal/CaptureCount.capture_inter_card`
- Truth anchor: `D5/S0/Diagonal/CaptureCount.escape_all_of_fixfree`
- Truth anchor: `D5/S0/Diagonal/CaptureCount.escaped_card_of_fixfree`
