# Simultaneous Steiner Switch Supports

## Abstract

Subspace criteria for common Steiner return patterns and simultaneous switch counts.

**Theorem 1.1 (The codimension criterion for return supports).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.realizesReturnSupport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.realizesReturnSupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Take the binary span of the requested circuit rows in a finite Steiner loop with trivial centre. Quotient that span by the span of the rows required to have zero return. One labelling has the specified zero pattern on the full requested components exactly when a subspace of the quotient avoids every projected row required to have nonzero return and has codimension at most the binary dimension of the fibre.

The kernel of the realized return map contains the span of the zero rows and descends to such a subspace. Conversely, embed the quotient by the avoiding subspace in the fibre. Extend the resulting map on the row span to the space of triples and take its values on the triple basis.

**Theorem 1.2 (The range of simultaneous counts).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.commonSwitchCounts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.commonSwitchCounts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

A family of counts of noncommuting starts in one normalized extension with the identity fibre as its centre is realizable exactly when one subspace of the triple-coordinate space gives all the counts. Its codimension is at most the fibre dimension. For each pivot pair, count every quotient vertex that fails to return within two rounds and every other vertex whose circuit row lies outside the subspace. Multiply this number by the size of the fibre.

**Theorem 1.3 (Realizing the profile in one labelled triple system).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.labelledCommonSwitchCounts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.labelledCommonSwitchCounts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

For a nontrivial base loop and distinct nonidentity members of every pivot pair, the same normalized extension and the same labelled complete triple system realize the counts supplied by the chosen subspace. The extension has exactly the identity fibre as its centre. Its triple labelling has exactly the chosen subspace as its kernel, so the same system realizes the support and the count profile. The matching of uncovered pairs after each deletion is the actual matching of that labelled system. The fibre count therefore applies to the successful switch starts for all the specified deletions and pivots.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.commonSwitchCounts`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.labelledCommonSwitchCounts`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchSupport.realizesReturnSupport`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerReturnDependencies](SteinerReturnDependencies.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount](SteinerSchreierSwitchCount.md)
