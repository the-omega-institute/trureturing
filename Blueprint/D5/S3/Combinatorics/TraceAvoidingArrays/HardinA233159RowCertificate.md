# OEIS A233159

## Abstract

Equality patterns and their quotient determine labelled six-row strip counts.

**Theorem 1.1 (quotient_certificate).**

$$(\forall r \in Row\left(6\right),\; \forall s \in Fin\left(122\right),\; \sum_{(c: Row\left(6\right))} \operatorname{if} (columnCompatible\left(r, c\right)) \land (classify\left(c\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = quotient\left(classify\left(r\right), s\right)) \land ((\forall s \in Fin\left(122\right),\; \sum_{(c: Row\left(6\right))} \operatorname{if} classify\left(c\right) = s \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0 = weights\left(s\right)) \land (\forall v \in Fin\left(122\right) \to \operatorname{Int},\; \forall i \in Fin\left(122\right),\; Matrix.mulVec\left(quotient, v\right)\left(i\right) = List.sum\left(List.map\left(v, successors\left(i\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate.quotient_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233159: 6-row three-state sum exclusion*. URL: <https://oeis.org/A233159>.

*Commentary.*

Successor counts, initial multiplicities and sparse matrix action agree with the finite column tables.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate.quotient_certificate`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows](HardinA233159Rows.md)
