# Binary Run Intervals for Cyclotomic Zeros

## Abstract

Binary Run Intervals for Cyclotomic Zeros

**Definition 1.1 (Binary run value).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.runValue`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.runValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a Boolean starting bit and a list of positive run lengths, runValue recursively encodes the alternating binary runs as a natural number; the true and false branches occupy complementary blocks.

**Definition 1.2 (Admissible run language).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.RunAdmissible`

*Formalization.* `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.RunAdmissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

RunAdmissible d describes the surviving run lists: a one-run list has length at most d, a two-run list has both lengths at most d with one strictly shorter, and every longer list has each internal leading run strictly shorter than d.

**Theorem 1.3 (Forbidden runs lie in zero intervals).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.forbidden_runs_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.forbidden_runs_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For d at least two and m positive, if every nonempty positive run expansion with value m is inadmissible, then m plus one belongs to the cyclotomic zero set for d.

**Theorem 1.4 (Run survival induction).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.run_survival`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.run_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

Suppose a predicate on a starting phase and a positive run list satisfies the terminal, deletion, reflection, and singular transition rules. Then its value at phase one is equivalent to RunAdmissible d for every nonempty positive run list.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.RunAdmissible`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.forbidden_runs_mem`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.runValue`
- Truth anchor: `D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals.run_survival`
- Dependency: [D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs](CyclotomicDigitHankelDefs.md)
