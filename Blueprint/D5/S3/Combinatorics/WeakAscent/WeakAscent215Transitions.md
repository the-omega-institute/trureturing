# Transitions of Active Marks

## Abstract

Appending a letter induces record, fresh-site or old-site transitions on the active marks.

**Theorem 1.1 (The active-mark transition correspondence).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Transitions.left_transitions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215Transitions.left_transitions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a nonempty word w in the class avoiding 100, 101, 110 and 201, put M equal to its maximum, b equal to one plus its weak ascent count minus M, and e true exactly when its last entry is M. Appendable letters are in bijection with either a gap g below b or a position s in the increasing active-value list. The gap choice appends M + g + 1, appends g false marks and a true mark, changes the budget to b minus g and sets true mode. A site choice appends its active value. At a false mark it truncates the mark list before s, retains budget b and sets false mode. At a true mark with e true and s last, it leaves the singleton true list, changes the budget to b + 1 and sets true mode. At any other true mark it leaves the empty list, retains budget b and sets false mode.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Transitions.left_transitions`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory](WeakAscent215WordHistory.md)
