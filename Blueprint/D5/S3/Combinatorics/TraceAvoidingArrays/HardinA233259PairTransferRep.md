# Representative rows

## Abstract

The finite representative-row quotient certificate.

**Theorem 1.1 (Representative rows).**

$$\forall i \in \operatorname{Fin}\left(14\right),\; \forall s \in \operatorname{Fin}\left(14\right),\; \sum_{c \in \operatorname{Col}} ((if (\operatorname{compatible}\left(\operatorname{representatives}\left(i\right), c\right)) \land (\operatorname{cls}\left(c\right) = s) then 1 else 0)) = \operatorname{Q}\left(i, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep.representative_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Representative rows.

**Theorem 1.2 (Quotient rows).**

$$\forall b \in \operatorname{Col},\; \forall s \in \operatorname{Fin}\left(14\right),\; \sum_{c \in \operatorname{Col}} ((if (\operatorname{compatible}\left(b, c\right)) \land (\operatorname{cls}\left(c\right) = s) then 1 else 0)) = \operatorname{Q}\left(\operatorname{cls}\left(b\right), s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep.quotient_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Quotient rows.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep.quotient_rows`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep.representative_rows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](HardinA233259PairTransferCore.md)
