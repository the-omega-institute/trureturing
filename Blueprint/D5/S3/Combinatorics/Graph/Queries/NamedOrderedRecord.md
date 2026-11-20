# Likelihood of an ordered name-query record

## Abstract

Independent persistent local orders give an exact likelihood for a realized adaptive name-query record.

**Theorem 1.1 (A factorial factor for each distinct successful query).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/NamedOrderedRecord.orderedRecord_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/NamedOrderedRecord.orderedRecord_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A reply table on a finite set of names gives either a miss or a set of returned names at each query name. Independently choose a uniform enumeration of each successful reply set and keep it fixed for every visit to that name. A miss uses a separate response, including when a successful reply set is empty.

Fix an adaptive protocol and an ordered transcript realized by one reference reply table and one reference enumeration table. Another reply table gives the transcript positive probability precisely when it agrees with the reference on the unordered replies at every name queried in the transcript. In that case the ordered transcript has probability equal to the reciprocal of the product of the factorials of the successful reply sizes, counting each queried name once.

Agreement on the unordered replies transfers the reference order to the other table at each queried name. Replaying the protocol then reduces to fixing those coordinates of the independent table. Any ordered replay also gives equality after erasing the orders, which excludes every incompatible table.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/NamedOrderedRecord.orderedRecord_mass`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/FixedNeighborOrder](FixedNeighborOrder.md)
- Dependency: [D5/S3/Combinatorics/Probability/NamingRestrictionLaw](../../Probability/NamingRestrictionLaw.md)
