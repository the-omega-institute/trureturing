# Four-Exit Scan Extension

## Abstract

Ordinary actual slot scans extend retained response recipes with exact excess.

**Theorem 1.1 (Extension from an arbitrary retained slot set).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FourExitScanExtension.ordinary_scan_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitScanExtension.ordinary_scan_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least one, fix any coordinate equivalence for the baseline and the four exceptional rows at each slot. A recipe on the baseline and any retained set of slots extends to a recipe on the complete family. Its gain is unchanged on every retained coordinate and equals one on all four rows of every added slot. The assertion includes empty and full retained sets.

The three response vectors at an added slot are realized by LLLR, LRR, and RLR below that slot. The first separates A and Y; the second separates H; the third separates Z. Each exceptional row exits after one nonleaf reply, while every other row continues through labelled leaves. Induction over the added slots composes these splits with the original retained recipe.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitScanExtension.ordinary_scan_completion`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](FourExitRawEndpointSpectrum.md)
