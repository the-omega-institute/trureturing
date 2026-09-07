# ExecutableHoKalman

## Abstract

Finite noisy Ho-Kalman reconstruction with explicit arithmetic certificates.

**Definition 1.1 (tuples).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.tuples`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.tuples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite Cartesian powers are enumerated as lists, with no noncomputable conversion from a finite set.

**Theorem 1.2 (mem tuples).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.mem_tuples`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.mem_tuples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction proves that every coordinatewise-valid tuple occurs in the enumeration.

**Definition 1.3 (allPivots).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.allPivots`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.allPivots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every selection of observation rows and reachability columns is listed in a fixed order. This transparent exhaustive algorithm is not claimed to be efficient for large dimensions.

**Theorem 1.4 (mem allPivots).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.mem_allPivots`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.mem_allPivots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No finite candidate pivot is omitted from the search space.

**Definition 1.5 (absSum).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.absSum`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.absSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational sum of absolute entries gives a conservative and executable upper bound for the induced infinity norm.

**Definition 1.6 (acceptable).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.acceptable`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.acceptable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data-only Boolean test checks a nonzero determinant, nonnegative entrywise uncertainty, and a strict inverse-noise margin.

**Definition 1.7 (scan).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.scan`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.scan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A structural recursion returns the first accepted pivot or rejects after exhausting the supplied finite list.

**Theorem 1.8 (scan sound).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.scan_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.scan_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every successful scan result passes the actual Boolean acceptance test.

**Theorem 1.9 (scan none iff).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.scan_none_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.scan_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rejected scan is equivalent to failure of every acceptance test in its input list.

**Definition 1.10 (choosePivot).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exhaustive list is passed to the verified scan; the caller provides samples, model order and uncertainty, never an inverse or a success proof.

**Theorem 1.11 (choosePivot none iff).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_none_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global rejection has the precise meaning that every candidate fails the stated conservative test.

**Theorem 1.12 (choosePivot success).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_success`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If some candidate passes the executable test, the search returns a candidate. This is completeness relative to the test, not automatic model-order identification.

**Theorem 1.13 (choosePivot certificate).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Success exposes the determinant and strict rational margin that will be consumed by the real perturbation theorem.

**Definition 1.14 (Result).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.Result`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.Result` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output contains a selected pivot and three rational matrices. No correctness or error assertion is hidden in a structure field.

**Definition 1.15 (run).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.run`

*Formalization.* `D5/S3/Observer/Hankel/ExecutableHoKalman.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An accepted pivot is converted into actual transition, input and output matrices. Singular or insufficiently conditioned data return none.

**Theorem 1.16 (run fields).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.run_fields`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.run_fields` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output fields are proved to coincide with the finite-data construction at the returned pivot.

**Theorem 1.17 (run exact recovery).**

Lean statement: `D5/S3/Observer/Hankel/ExecutableHoKalman.run_exact_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ExecutableHoKalman.run_exact_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual output reproduces every Markov parameter of any order-matching reference system consistent with the noiseless input samples. The source also includes scalar reduction examples; their execution status is separate from their presence.

## References

- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.Result`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.absSum`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.acceptable`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.allPivots`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_certificate`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_none_iff`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.choosePivot_success`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.mem_allPivots`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.mem_tuples`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.run`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.run_exact_recovery`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.run_fields`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.scan`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.scan_none_iff`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.scan_sound`
- Truth anchor: `D5/S3/Observer/Hankel/ExecutableHoKalman.tuples`
- Dependency: [D5/S3/Observer/Hankel/FiniteHoKalmanBlocks](FiniteHoKalmanBlocks.md)
