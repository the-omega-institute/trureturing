# Quotient row block 2

## Abstract

Successor counts in one block of seven-column row codes.

**Theorem 1.1 (row_counts).**

$$\forall a \in Fin\left(729\right),\; (rowLegal\left(decode\left(7, (\langle 3 \cdot Fin.val\left(a\right) + 2, \operatorname{by} \operatorname{omega}\rangle: Fin\left(2187\right))\right)\right)) \Rightarrow (\forall s \in Fin\left(16\right),\; classCount\left(decode\left(7, (\langle 3 \cdot Fin.val\left(a\right) + 2, \operatorname{by} \operatorname{omega}\rangle: Fin\left(2187\right))\right), s\right) = quotient\left(classify\left(decode\left(7, (\langle 3 \cdot Fin.val\left(a\right) + 2, \operatorname{by} \operatorname{omega}\rangle: Fin\left(2187\right))\right)\right), s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateTwo.row_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233154: three-state horizontal and antidiagonal sum exclusion*. URL: <https://oeis.org/A233154>.

*Commentary.*

Every legal source code in the block has the stated number of successors in each quotient class.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateTwo.row_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows](HardinA233154Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](HardinA233155RowTransfer.md)
