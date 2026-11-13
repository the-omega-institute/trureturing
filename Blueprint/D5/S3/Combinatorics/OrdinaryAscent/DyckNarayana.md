# Dyck peaks and Narayana numbers

## Abstract

Licensed suffix-ballot enumeration of actual Mathlib Dyck-word peak fibers, used by the ordinary-avoider statistic equivalence.

Adapted from Per Alexandersson's Apache-2.0 RealRooted source at commit 27276f93bbaf6b46bce689bca110bbacab1bba6b, with proof credit to Aristotle (Harmonic). The Lean module preserves the copyright notice, complete license and modification notice. No broad dependency or pin upgrade is introduced.

**Definition 1.1 (Narayana numbers).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.narayana`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.narayana` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

The natural-number quotient choose(n,k) choose(n,k-1) divided by n, with N(0,0)=1 and N(0,k)=0 for positive k. Truncated subtraction requires the explicit positive-peak hypotheses in the quotient theorem.

**Definition 1.2 (Adjacent UD count).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.peakCountList`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.peakCountList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

Count adjacent up-down factors in a list of Dyck steps.

**Definition 1.3 (Peaks of an actual Dyck word).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.peakCount`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.peakCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

Apply the adjacent UD count to the underlying list of a Mathlib DyckWord.

**Theorem 1.4 (Prepending an upstep).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.pc_U`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.pc_U` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

Prepending an upstep creates exactly one new peak when the previous list starts with a downstep.

**Theorem 1.5 (Prepending a downstep).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.pc_D`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.pc_D` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

Prepending a downstep preserves the adjacent UD count.

**Theorem 1.6 (Positive-size positive-peak quotient identity).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.narayana_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.narayana_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

For nonzero n and nonzero k, n times the Narayana number equals choose(n,k) choose(n,k-1). The zero-peak case is excluded because natural subtraction makes the unrestricted formula false.

**Theorem 1.7 (Actual Dyck peak fibers).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.card_semilength_peakCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.card_semilength_peakCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

The cardinality of actual Dyck words with semilength n and k adjacent UD peaks is N(n,k), provided the pair is not (1,0). This is a statement about actual finite fibers, not a formal generating series.

**Theorem 1.8 (The excluded fiber is empty).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.card_semilength_one_peakCount_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.card_semilength_one_peakCount_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *The Narayana distribution of Dyck-word peaks (RealRooted DyckStatistics)*. URL: <https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean>.

*Commentary.*

No actual Dyck word has semilength one and zero peaks. This separately handles the exceptional natural-quotient boundary.

## References

- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.card_semilength_one_peakCount_zero`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.card_semilength_peakCount`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.narayana`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.narayana_mul`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.pc_D`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.pc_U`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.peakCount`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.peakCountList`
