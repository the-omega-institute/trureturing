# Historical Congruence of Native Operations

## Abstract

Historical isomorphisms preserve native compositions, complement, and the exact temporal domain.

**Theorem 1.1 (Equivalence and strong temporal-domain congruence).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalCongruence.historical_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HistoricalCongruence.historical_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any natural dimension d, including zero. Write H(X,Xprime) for historical isomorphism of rich histories: a bijection of complete archives preserves and reflects causality, preserves time, position, sign and the literal ordered source tree at every event, and maps both the current region and the selection onto their counterparts. The relation H is reflexive, symmetric and transitive.

For all rich histories X, Xprime, Y and Yprime of dimension d, H(X,Xprime) and H(Y,Yprime) imply both H(parallel(X,Y),parallel(Xprime,Yprime)) and H(product(X,Y),product(Xprime,Yprime)). For every X and Xprime, H(X,Xprime) also implies H(complement(X),complement(Xprime)), where complement means the current region minus the selection. No balance condition is needed for this historical assertion.

Under the same two input isomorphisms, Guard(archive(X),archive(Y)) holds if and only if Guard(archive(Xprime),archive(Yprime)) holds. Each guard compares the absolute times of every pair of archived events, including inactive and unselected events. For every legal proof g of the first guard and every legal proof gprime of the second, H(temporal(X,Y,g),temporal(Xprime,Yprime,gprime)) holds. Thus legality is transported in both directions, and the output statement does not depend on a chosen guard proof.

The event maps keep each old archive tag and apply its input bijection. A generated product event with actual current parents a and b maps to the event with parents hX(a) and hY(b). Its time is the maximum parent time plus one, its position is the sum of parent positions, its sign compares the parent signs, and its source is the ordered pair of parent sources. Each of the two old internal generators and the two parent generators is preserved and reflected. Transporting paths in both directions gives the entire causal relation. Empty current regions erase generated pairs but do not remove either old archive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalCongruence.historical_congruence`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/GeneratedProduct](GeneratedProduct.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence](HistoricalEquivalence.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TemporalComposition](TemporalComposition.md)
