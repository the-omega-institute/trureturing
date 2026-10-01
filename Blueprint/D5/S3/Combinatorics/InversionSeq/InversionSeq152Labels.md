# A Bijection with Bounded Sorted Labels

## Abstract

Subtracting positional ranks converts bounded rotated blocks into weakly increasing label blocks.

**Theorem 1.1 (Sorted labels for rotated blocks).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Labels.sorted_label_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Labels.sorted_label_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Fix nonnegative integers n, l and u. Lists of nonempty blocks with total length n, strictly increasing concatenation, entries greater than l and rotated-concatenation entries at most u + 1 plus their positions are in bijection with lists of nonempty label blocks of total length n whose concatenation is weakly increasing, whose labels lie between l and u inclusive and whose block-tail labels are strictly less than u. Rotation moves each block's first entry to its end, and positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Labels.sorted_label_bijection`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Bounds](InversionSeq152Bounds.md)
