# Weakly Increasing Inversion Sequences and Dyck Paths

## Abstract

Weakly increasing inversion sequences correspond to Dyck paths, with increases recorded by descent lengths.

**Definition 1.1 (Counts of preceding down steps).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.eastCounts`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.eastCounts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Starting with a nonnegative count e, traverse a word of up and down steps. Record the current count at each up step and increase it by one at each down step. The resulting list has one entry per up step.

**Definition 1.2 (Steps from a sequence of counts).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.dyckSteps`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.dyckSteps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Given a size n, a current count e and a word of nonnegative integers, replace each successive value v by v minus e down steps followed by one up step, and continue with current count v. After the last value, append n minus the current count down steps. Subtractions are truncated at zero.

**Theorem 1.3 (A bijection preserving descent statistics).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.monoDyckEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.monoDyckEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every nonnegative n, weakly increasing inversion sequences of length n are in bijection with Dyck paths of semilength n. The forward map inserts down steps according to successive entry counts, and the inverse records the number of down steps before each up step. The final descent has length n minus the maximum sequence entry, taking the maximum of the empty sequence to be zero. The lengths of all other nonempty descents are the positive successive differences of the sequence after adjoining an initial zero.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.dyckSteps`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.eastCounts`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.monoDyckEquiv`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqDefs](InversionSeqDefs.md)
