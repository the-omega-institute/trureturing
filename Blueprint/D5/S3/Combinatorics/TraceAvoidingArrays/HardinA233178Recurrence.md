# From exact source cardinalities to the full recurrence

## Abstract

The all-width recurrence for the literal normalized six-colour five-row array count.

The source count and FullE are those of HardinA233178Literal. The transfer uses the original five rows as five independent base-three digits. Its three-label columns are an auxiliary representation of the source graph. No continuation or source-correspondence hypothesis is assumed.

**Theorem 1.1 (Exact column cardinality bridge).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.count_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, chromaticCount(n+1) is the sum of the continuation vector v(n). The explicit base-three equivalence is a bijection between all 243 columns and all functions from the five rows into three labels. Applying it columnwise is a bijection with the actual array function domain. Literal edges become exactly Bond. The original generic cont_matrix theorem counts all continuations; its pair condition is True, its triple condition tests the last two columns, and its class is the last column. No initial-column multiplicity is lost.

**Theorem 1.2 (All subsequent chromatic widths).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.chromatic_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.chromatic_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, write C(k)=chromaticCount(k). Then C(n+12)=6*C(n+11)+31*C(n+10)-97*C(n+9)-163*C(n+8) +417*C(n+7)+93*C(n+6)-514*C(n+5)+192*C(n+4)+72*C(n+3)-36*C(n+2). The exact source cardinality bridge and the certified vector identity give this relation. The finite vector certificate propagates by arbitrary further matrix powers.

**Theorem 1.3 (The literal FullE theorem).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233178` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233178","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The theorem proves FullE itself. The chromatic coefficients sum to one, so adding six preserves the unscaled recurrence. Substitution of 48*a(n)=32^n*(chromaticCount(n)+6) multiplies the coefficient at lag i by 32^i. All lag widths are at least two when the source width exceeds eleven. Integer cancellation then gives exactly the ten coefficients in FullE. The theorem has no source-bridge assumption, finite upper cutoff, changed onset, generating-function condition, minimal-order assertion or colour-surjectivity hypothesis.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.chromatic_recurrence`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.count_transfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic](HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Literal](HardinA233178Literal.md)
