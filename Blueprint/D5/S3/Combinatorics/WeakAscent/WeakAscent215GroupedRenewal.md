# Grouped Renewal Series

## Abstract

Grouping histories by expenditure and remaining budget gives bivariate renewal identities.

**Definition 1.1 (The record-ending series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.recordSeries`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.recordSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The coefficient of z to the power s and x to the power l in the record-ending series counts pure histories of expenditure s and length l whose last step is a record.

**Definition 1.2 (The marked-survivor series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.survivorSeries`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.survivorSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The coefficient of z to the power s and x to the power l in the survivor series counts pairs consisting of a pure history of expenditure s and length l and a choice of one of its terminal old entries.

**Definition 1.3 (Full histories with fixed initial budget).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.fullSeries`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.fullSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

For a Boolean e and a nonnegative budget b, the coefficient of x to the power l in F_e(b;x) counts full histories of length l with initial mode e and budget b. The initial stack consists of a single true mark when e is true and is empty otherwise.

**Definition 1.4 (The positive-budget series).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.budgetSeries`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.budgetSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

The positive-budget series B_e(z,x) is the sum, over nonnegative b, of z to the power b times F_e(b + 1;x). Thus the exponent of z records the initial budget minus one.

**Theorem 1.5 (Grouped renewal equations).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.grouped_renewal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.grouped_renewal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

Write P, R and S for the pure, record-ending and marked-survivor series, with z recording expenditure and x recording length. Then R = xP + zR. For each Boolean e, put U = S + P when e is true and U = S otherwise, and put M = R + 1 when e is true and M = R otherwise. Let T be the sum of z to the power b times F_true(b + 2;x), let O = x(U B_false + M T), and let A = B_e + x M B_false. The renewal equation is A + zO = P + O + zA.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.budgetSeries`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.fullSeries`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.grouped_renewal`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.recordSeries`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215GroupedRenewal.survivorSeries`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition](WeakAscent215Decomposition.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints](WeakAscent215Endpoints.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215WeightedRenewal](WeakAscent215WeightedRenewal.md)
