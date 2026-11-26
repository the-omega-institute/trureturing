# Purity and shelling of the fair-bias link

## Abstract

The signed fair-bias facets have uniform size and satisfy the lexicographic shelling criterion.

**Theorem 1.1 (Each facet has size equal to the column nullity).**

Lean statement: `D5/S3/TotalVariation/FairBiasShelling.facet_card_eq_nullity`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasShelling.facet_card_eq_nullity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite labelled family of columns in a finite vector space over the binary field. Each maximal nonempty face of the signed complement-spanning complex has one vertex per label outside a column basis. Its cardinality equals the number of labels minus the rank of the full family. The signed complex is the nonempty part of the independence complex of the dual column matroid pulled back along the sign-forgetting map.

**Theorem 1.2 (Lexicographic precedence satisfies the shelling criterion).**

Lean statement: `D5/S3/TotalVariation/FairBiasShelling.lexicographic_facet_shelling`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasShelling.lexicographic_facet_shelling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the same finite binary column family and any linear order on its signed labels. Order facets by the first differing label. For an earlier facet S and a later facet T, there is a facet U earlier than T that contains the intersection of S and T and omits exactly one vertex of T. Extend the common vertices and an earlier differing vertex to a basis inside T together with that vertex.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasShelling.facet_card_eq_nullity`
- Truth anchor: `D5/S3/TotalVariation/FairBiasShelling.lexicographic_facet_shelling`
- Dependency: [D5/S3/TotalVariation/FairBiasFaceCount](FairBiasFaceCount.md)
