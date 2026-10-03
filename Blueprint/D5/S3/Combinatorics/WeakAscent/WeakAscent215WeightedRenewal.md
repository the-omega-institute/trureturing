# Weighted Renewal Counts

## Abstract

Pure prefixes and their terminal old sites give a weighted recurrence for full histories.

**Theorem 1.1 (The finite weighted renewal recurrence).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscent215WeightedRenewal.weighted_renewal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscent215WeightedRenewal.weighted_renewal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2025). *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*. DOI: [10.5281/zenodo.17144266](https://doi.org/10.5281/zenodo.17144266). URL: <https://math.colgate.edu/~integers/z80/z80.pdf>.

*Commentary.*

Fix a Boolean e and nonnegative integers b and d. The initial stack is a singleton true mark when e is true and is empty otherwise, with initial budget b and mode e. The pure histories h of length at most d and expenditure less than b form a finite collection. The number of full histories of length d + 1 from this initial state equals the number of pure histories of that length and expenditure less than b, plus a sum over this collection. For a prefix h, put r = b minus its expenditure and t = d minus its length, let a be its terminal old-entry count plus one when e is true and unchanged otherwise, and let m be one when its final mode is true and zero otherwise. Its contribution is (a minus m) times the number of full histories of length t from the empty stack with budget r and false mode, plus m times the number from the singleton true stack with budget r + 1 and true mode.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscent215WeightedRenewal.weighted_renewal`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints](WeakAscent215Endpoints.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215Finite](WeakAscent215Finite.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscent215HistoryFinite](WeakAscent215HistoryFinite.md)
