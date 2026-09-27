# First-Orientation Deletion Equivalence

## Abstract

Excursion deletion equates the actual first-orientation singleton-word fibers.

Fix exactSourceHypotheses(n,m,M,i,j,sigma). Let gamma be wordProduct(n,deletedExcursion(m,M,i)) and pi=sigma*gamma inverse. The quantification is over every n,m,M,i,j and sigma satisfying the exact source condition, including i=j and empty outer words. Fiber(n,tau) is the subtype of lists a with singletonWord(n,tau,a); Equiv(A,B) is the type of equivalences between A and B, and val forgets the subtype proof. ExactSource, SourceShape, Image and Deleted denote exactSourceHypotheses, sourceShape, imageWord and deletedExcursion respectively.

**Theorem 1.1 (Deletion equates source and target singleton fibers).**

$$\operatorname {ExactSource}\left(n, m, M, i, j, sigma\right) \implies \exists e \in \operatorname {Equiv}\left(\operatorname {Fiber}\left(n, sigma\right), \operatorname {Fiber}\left(n, pi\right)\right),\; \forall a \in \operatorname {Fiber}\left(n, sigma\right),\; \forall p \in \operatorname {List}\left(Nat\right),\; \forall q \in \operatorname {List}\left(Nat\right),\; \operatorname {SourceShape}\left(m, M, i, j, \operatorname {val}\left(a\right), p, q\right) \implies \operatorname {val}\left(\operatorname {e}\left(a\right)\right) = \operatorname {Image}\left(i, j, p, q\right) \land \operatorname {length}\left(\operatorname {val}\left(a\right)\right) = \operatorname {length}\left(\operatorname {val}\left(\operatorname {e}\left(a\right)\right)\right) + \operatorname {length}\left(\operatorname {Deleted}\left(m, M, i\right)\right) \land 0 < \operatorname {length}\left(\operatorname {Deleted}\left(m, M, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeDeletionEquiv.source_deletion_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

There exists an equivalence between actual singletonWord fibers of sigma and pi. For every source word a and every sourceShape(m,M,i,j,a,p,q), its forward value is imageWord(i,j,p,q), and length(a) equals length(imageWord) plus the strictly positive length of deletedExcursion. Forward consecutive validity and reducedness are proved; injectivity recovers the first j marker without restricting the suffix. Surjectivity uses the existing conditional lift after extracting an actual shaped source. The paper's Proposition 3.8 supplies the injection context, but does not claim this equivalence. Reflected and oscillating cases and Conjecture 5.1 remain open.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeDeletionEquiv.source_deletion_equiv`
- Dependency: [D5/S1/Words/Permutations/MamedeConditionalConverse](MamedeConditionalConverse.md)
- Dependency: [D5/S1/Words/Permutations/MamedeShapeExtraction](MamedeShapeExtraction.md)
