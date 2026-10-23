# Total exact binary pair projections

## Abstract

Total exact binary pair projections.

The supplied decoder detects missing unary delimiters, oversized length claims and short payloads. For a valid pair the selected component is returned unchanged; for an invalid outer word the literal fixed fallback is written. Both left and right projections are total polynomial transducers in the same tape model, and arbitrary payload bytes and empty components are preserved.

**Theorem 1.1 (polyTime_project).**

Lean statement: `D5/S0/Computability/BinaryMachine/PairProjection.polyTime_project`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/PairProjection.polyTime_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The supplied decoder detects missing unary delimiters, oversized length claims and short payloads. For a valid pair the selected component is returned unchanged; for an invalid outer word the literal fixed fallback is written. Both left and right projections are total polynomial transducers in the same tape model, and arbitrary payload bytes and empty components are preserved.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/PairProjection.polyTime_project`
- Dependency: [D5/S0/Computability/BinaryMachine/PairPreimage](PairPreimage.md)
