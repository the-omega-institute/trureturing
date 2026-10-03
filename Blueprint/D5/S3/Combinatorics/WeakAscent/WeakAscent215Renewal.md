# Renewal at the First Old Site

## Abstract

Full histories extend pure histories by visits to old sites and split at the first such visit.

**Definition 1.1 (Full steps).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.FullStep`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.FullStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

A full step is either a pure record or descent step, or an old-site step with a nonnegative site.

**Definition 1.2 (The mode after a pure prefix).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.finishMode`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.finishMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The mode of an empty pure step list is its initial Boolean mode. A record changes the mode to true and a descent changes it to false; subsequent steps determine the final mode in the same way.

**Definition 1.3 (Full stack runs).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.FullRun`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.FullRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

A full run starts from a Boolean stack, a nonnegative budget and a Boolean mode. A record appends false marks and one true mark, subtracts its gap from the budget and sets the mode to true; its gap must be less than the budget. A descent at a false-marked site truncates the stack before that site, preserves the budget and sets the mode to false. An old-site step requires a positive budget and a true-marked site. When the mode is true and the site is last, it leaves the singleton true stack, increases the budget by one and retains true mode; otherwise it leaves the empty stack, preserves the budget and sets false mode. The empty list is permitted exactly when the budget is positive.

**Theorem 1.4 (Decomposition at the first old-site step).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.first_old_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.first_old_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For every initial stack, budget and mode, full histories are in bijection with either a budgeted pure prefix or a budgeted pure prefix followed by an old-site choice in its terminal stack and a full suffix. Reconstruction concatenates the pure prefix, the chosen old-site step and the suffix. The suffix starts with a singleton true stack, one extra unit of remaining budget and true mode exactly when the pure prefix finishes in true mode and the chosen site is last; otherwise it starts with an empty stack and false mode. Moreover, for a positive budget and a stack of length c, histories of length n + 1 are in bijection with a choice among the record gaps below the budget or the c stack sites, followed by a history of length n from the state prescribed by that first transition.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.FullRun`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.FullStep`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.finishMode`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Renewal.first_old_decomposition`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure](WeakAscent215Pure.md)
