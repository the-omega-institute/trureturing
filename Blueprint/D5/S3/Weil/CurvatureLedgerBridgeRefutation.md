# Curvature-Ledger Bridge Refutation

## Abstract

Two frozen-definition toy readouts refute a globally normalized curvature-ledger measure bridge.

**Definition 1.1 (Literal unit-multiplicity curvature atom).**

Lean statement: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.unitCurvatureAtom`

*Formalization.* `D5/S3/Weil/CurvatureLedgerBridgeRefutation.unitCurvatureAtom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a spectral point rho, this specialization retains exactly the frozen curvature location -Im(rho) + i(Re(rho) - 1/2) and the unit-multiplicity mass 2 pi. It introduces no calibration or alternate support map.

**Definition 1.2 (Frozen mirror-pair deficit readout).**

Lean statement: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.zeroDeficitPair`

*Formalization.* `D5/S3/Weil/CurvatureLedgerBridgeRefutation.zeroDeficitPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The paired deficit measure is the sum of the already frozen zeroDeficitMeasure at rho and at mirror(rho). Each atom remains supported at its original zero address.

**Theorem 1.3 (First curvature readout).**

$$\operatorname{unitCurvatureAtom}(\frac{3}{4})=\operatorname{ofReal}(2\pi)\operatorname{dirac}(\frac{i}{4})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CurvatureLedgerBridgeRefutation.first_curvature_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the W-B1 zero pair {3/4, 1/4}, only the right zero enters the frozen curvature sum. Its upperPoint is i/4 and its unit-multiplicity mass is 2 pi.

**Theorem 1.4 (First deficit readout).**

$$\operatorname{zeroDeficitPair}(\frac{3}{4})=\frac{1}{32}\operatorname{dirac}(\frac{3}{4})+\frac{1}{32}\operatorname{dirac}(\frac{1}{4})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CurvatureLedgerBridgeRefutation.first_deficit_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen address gives zeroAddressedScaling = 1/8 at both zeros, so the selected second variation is 1/32 at each. The measure is supported at 3/4 and 1/4, not at i/4, and its total mass is 1/16.

**Theorem 1.5 (Second curvature readout).**

$$\operatorname{unitCurvatureAtom}(1)=\operatorname{ofReal}(2\pi)\operatorname{dirac}(\frac{i}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CurvatureLedgerBridgeRefutation.second_curvature_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the distinct displacement pair {1, 0}, the right-zero curvature atom moves to i/2 while retaining the same unit-multiplicity mass 2 pi.

**Theorem 1.6 (Second deficit readout).**

$$\operatorname{zeroDeficitPair}(1)=\frac{1}{2}\operatorname{dirac}(1)+\frac{1}{2}\operatorname{dirac}(0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CurvatureLedgerBridgeRefutation.second_deficit_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At displacement one half, zeroAddressedScaling = 1/2 and the selected second variation is 1/2. The two deficit atoms therefore remain at 1 and 0 with total mass 1.

**Theorem 1.7 (No global mass normalization).**

$$\neg\exists c\in\mathbb{R}_{ge0}, c16^{-1}=2\operatorname{ofReal}(\pi) \land c=2\operatorname{ofReal}(\pi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CurvatureLedgerBridgeRefutation.no_global_mass_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A global scalar would have to send total deficit mass 1/16 to 2 pi in the first example and total deficit mass 1 to 2 pi in the second. Positivity of pi makes those equations incompatible.

**Theorem 1.8 (W-B3 bridge verdict).**

$$\neg\exists c\in\mathbb{R}_{ge0}, c\operatorname{zeroDeficitPair}(\frac{3}{4})=\operatorname{unitCurvatureAtom}(\frac{3}{4}) \land c\operatorname{zeroDeficitPair}(1)=\operatorname{unitCurvatureAtom}(1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CurvatureLedgerBridgeRefutation.curvature_ledger_bridge_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Verdict: bridge-refuted. Applying a hypothetical common measure scalar to the universal set would imply the two incompatible total-mass equations. Independently, the exact readouts expose a support mismatch in both examples: curvature lives at i/4 or i/2, whereas deficit remains at the original real zero pair.

## References

- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.curvature_ledger_bridge_refuted`
- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.first_curvature_readout`
- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.first_deficit_readout`
- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.no_global_mass_normalization`
- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.second_curvature_readout`
- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.second_deficit_readout`
- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.unitCurvatureAtom`
- Truth anchor: `D5/S3/Weil/CurvatureLedgerBridgeRefutation.zeroDeficitPair`
- Dependency: [D5/S3/Analytic/Boundary/InteriorCurvatureCriterion](../Analytic/Boundary/InteriorCurvatureCriterion.md)
- Dependency: [D5/S3/Weil/LedgerDeficitSecondVariation](LedgerDeficitSecondVariation.md)
