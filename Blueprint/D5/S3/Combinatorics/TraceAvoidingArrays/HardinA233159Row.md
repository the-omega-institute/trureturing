# OEIS A233159

## Abstract

Equality patterns and their quotient determine labelled six-row strip counts.

**Theorem 1.1 (finite_certificate).**

$$(\forall r \in Row\left(6\right),\; \forall s \in Fin\left(122\right),\; \sum_{(c: Row\left(6\right))} \operatorname{if} (columnCompatible\left(r, c\right)) \land (classify\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = quotient\left(classify\left(r\right), s\right)) \land ((\forall s \in Fin\left(122\right),\; \sum_{(c: Row\left(6\right))} \operatorname{if} classify\left(c\right) = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = weights\left(s\right)) \land (Matrix.mulVec\left((quotient)^{6 + 9}, (1: Fin\left(122\right) \to \operatorname{Int})\right) = \sum_{(j: Fin\left(9\right))} HSMul.hSMul\left(![-4128, 17216, -27636, 21056, -6705, -573, 1038, -283, 30]\left(j\right), Matrix.mulVec\left((quotient)^{6 + Fin.val\left(j\right)}, (1: Fin\left(122\right) \to \operatorname{Int})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

The three identities specify the quotient, the initial class counts and the finite relation among matrix powers.

**Theorem 1.2 (result).**

$$\forall n \in \operatorname{Nat},\; (U_{6}\left(n + 16\right): \operatorname{Int}) = 30 \cdot (U_{6}\left(n + 15\right): \operatorname{Int}) - 283 \cdot (U_{6}\left(n + 14\right): \operatorname{Int}) + 1038 \cdot (U_{6}\left(n + 13\right): \operatorname{Int}) - 573 \cdot (U_{6}\left(n + 12\right): \operatorname{Int}) - 6705 \cdot (U_{6}\left(n + 11\right): \operatorname{Int}) + 21056 \cdot (U_{6}\left(n + 10\right): \operatorname{Int}) - 27636 \cdot (U_{6}\left(n + 9\right): \operatorname{Int}) + 17216 \cdot (U_{6}\left(n + 8\right): \operatorname{Int}) - 4128 \cdot (U_{6}\left(n + 7\right): \operatorname{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233159` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233159","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

Multiplication by every further matrix power extends the finite relation to all strip lengths in the displayed range.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate](HardinA233159RowCertificate.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows](HardinA233159Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
