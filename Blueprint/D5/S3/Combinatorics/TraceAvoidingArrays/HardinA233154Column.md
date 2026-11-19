# OEIS A233154

## Abstract

The literal 7-column count obeys a recurrence determined by its finite row quotient.

**Theorem 1.1 (finite_certificate).**

$$(\forall r \in Row\left(7\right),\; (rowLegal\left(r\right)) \Rightarrow (\forall s \in Fin\left(16\right),\; \sum_{(c: Row\left(7\right))} \operatorname{if} (rowLegal\left(c\right)) \land ((compatible\left(r, c\right)) \land (classify\left(c\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = quotient\left(classify\left(r\right), s\right))) \land ((\forall s \in Fin\left(16\right),\; \sum_{(c: Row\left(7\right))} \operatorname{if} (rowLegal\left(c\right)) \land (classify\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = weights\left(s\right)) \land (Matrix.mulVec\left((quotient)^{1 + 4}, (1: Fin\left(16\right) \to \operatorname{Int})\right) = \sum_{(j: Fin\left(4\right))} HSMul.hSMul\left(![-810, 972, -351, 42]\left(j\right), Matrix.mulVec\left((quotient)^{1 + Fin.val\left(j\right)}, (1: Fin\left(16\right) \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The three finite identities give the successor counts, initial class multiplicities and a polynomial relation among quotient powers.

**Theorem 1.2 (result).**

$$\forall n \in \operatorname{Nat},\; (T7\left(n + 5\right): \operatorname{Int}) = 42 \cdot (T7\left(n + 4\right): \operatorname{Int}) - 351 \cdot (T7\left(n + 3\right): \operatorname{Int}) + 972 \cdot (T7\left(n + 2\right): \operatorname{Int}) - 810 \cdot (T7\left(n + 1\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233154` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233154","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

The finite relation extends through all further matrix powers. The initial instance supplies the exact starting index.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateOne](HardinA233154CertificateOne.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateTwo](HardinA233154CertificateTwo.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateZero](HardinA233154CertificateZero.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows](HardinA233154Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
