# Pure Stack Histories

## Abstract

Record and descent steps act on Boolean stacks, with record gaps recording expenditure.

**Definition 1.1 (Record and descent steps).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.PureStep`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.PureStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

A pure step is either a record with a nonnegative gap or a descent to a nonnegative site.

**Definition 1.2 (Shifting descent sites).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.shift`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.shift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

Shifting a pure step by a nonnegative offset leaves a record gap unchanged and adds the offset to a descent site.

**Definition 1.3 (Expenditure of a pure step list).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.spend`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.spend` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The expenditure of a list of pure steps is the sum of its record gaps; descents contribute zero.

**Definition 1.4 (Pure runs on Boolean stacks).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.PureRun`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.PureRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The empty step list leaves the stack unchanged. A record of gap g appends g false marks and then a true mark. A descent to site s is permitted precisely when s is below the stack length and its mark is false, and replaces the stack by its prefix of length s. A pure run applies these transitions successively and records the terminal stack.

**Definition 1.5 (Pure runs with a positive remaining budget).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.BudgetRun`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.BudgetRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

A budgeted pure run uses the same stack transitions as a pure run. A record of gap g requires g to be strictly less than the current budget and subtracts g from it. Descents leave the budget unchanged, and an empty terminal list requires a positive budget.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.BudgetRun`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.PureRun`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.PureStep`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.shift`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215Pure.spend`
