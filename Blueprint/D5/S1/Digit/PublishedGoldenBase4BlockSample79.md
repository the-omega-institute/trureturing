# Published Golden Base-Four Block Sample 79

## Abstract

The first 79 exact golden-ratio base-four power records are transported losslessly into binary Zeckendorf first-return coordinates.

**Theorem 1.1 (Every block record expands to its canonical power word).**

Lean statement: `D5/S1/Digit/PublishedGoldenBase4BlockSample79.publishedBlockSample79_expand`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PublishedGoldenBase4BlockSample79.publishedBlockSample79_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite decoder is checked on all indices zero through seventy-eight. The totalized fallback is therefore unreachable on the declared sample.

Expansion recovers the unique arithmetic word supplied by the existing golden base-four oracle, so no second dictionary or Zeckendorf implementation is introduced.

**Theorem 1.2 (Machine fitting is equivalent to recurrent-skeleton fitting).**

Lean statement: `D5/S1/Digit/PublishedGoldenBase4BlockSample79.machineFitsPowerSample79_iff_extractSkeletonFits`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PublishedGoldenBase4BlockSample79.machineFitsPowerSample79_iff_extractSkeletonFits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M17 extraction commutes pointwise with the first-return coordinate change. Hence a typed partial DFAO fits the original 79 power words exactly when its extracted recurrent skeleton fits the transported block sample.

The distinguished zero-input anchor remains separate and is carried by the anchored machine semantics used by the published experiment.

## References

- Truth anchor: `D5/S1/Digit/PublishedGoldenBase4BlockSample79.machineFitsPowerSample79_iff_extractSkeletonFits`
- Truth anchor: `D5/S1/Digit/PublishedGoldenBase4BlockSample79.publishedBlockSample79_expand`
- Dependency: [D5/S0/Automata/BinaryZeckendorfBlockSkeleton](../../S0/Automata/BinaryZeckendorfBlockSkeleton.md)
- Dependency: [D5/S1/Digit/GoldenBase4AutomataOracle](GoldenBase4AutomataOracle.md)
