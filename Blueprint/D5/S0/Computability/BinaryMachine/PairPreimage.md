# Preserving witnesses under polynomial instance maps

## Abstract

Preserving witnesses under polynomial instance maps.

Every raw outer word is decoded by the supplied finite pair parser. On success the concrete transducer transforms only the instance, keeping the entire certificate in a disjoint register; the pair constructor re-encodes the result. On outer failure it returns the empty raw word. A uniform all-word polynomial tape bound follows from executed decoder, transducer and constructor runs.

**Theorem 1.1 (polyTime_map).**

Lean statement: `D5/S0/Computability/BinaryMachine/PairPreimage.polyTime_map`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/PairPreimage.polyTime_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

Every raw outer word is decoded by the supplied finite pair parser. On success the concrete transducer transforms only the instance, keeping the entire certificate in a disjoint register; the pair constructor re-encodes the result. On outer failure it returns the empty raw word. A uniform all-word polynomial tape bound follows from executed decoder, transducer and constructor runs.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/PairPreimage.polyTime_map`
- Dependency: [D5/S0/Computability/BinaryMachine/TransducerPair](TransducerPair.md)
