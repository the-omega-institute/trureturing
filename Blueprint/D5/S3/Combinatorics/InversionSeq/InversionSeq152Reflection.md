# Run Lengths under Dyck Path Reflection

## Abstract

Reflection exchanges ascent lengths and descent lengths while reversing their order.

**Theorem 1.1 (Reflected ascent lengths).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Reflection.reflection_runs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Reflection.reflection_runs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Reflect a Dyck path by reversing its step word and exchanging up steps with down steps. The list of lengths of its nonempty ascents is the reverse of the list of lengths of the original path's nonempty descents.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Reflection.reflection_runs`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalReverse](../Nonnesting/NonnestingBasicRoyalReverse.md)
