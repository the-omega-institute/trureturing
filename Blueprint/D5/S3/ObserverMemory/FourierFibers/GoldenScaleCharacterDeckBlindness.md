# Golden Scale Character Deck Blindness

## Abstract

Integer golden Fourier characters are blind to one full scale deck step even though the golden helix level changes.

**Theorem 1.1 (Quotient Fourier readout forgets the helix sheet).**

$$\forall m: \mathbb{Z}, \neg \operatorname{Injective}(\operatorname{goldenHelixFourierReadout}(m)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/GoldenScaleCharacterDeckBlindness.golden_helix_fourier_readout_not_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One full golden scale period leaves every integer Fourier character unchanged, although the universal-cover helix level increases.

The theorem reuses GoldenScaleHelix to separate quotient phase from completion-depth memory. Adding the level coordinate detects the deck step.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/GoldenScaleCharacterDeckBlindness.golden_helix_fourier_readout_not_injective`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix](../../CompletionDynamics/GoldenMobius/GoldenScaleHelix.md)
