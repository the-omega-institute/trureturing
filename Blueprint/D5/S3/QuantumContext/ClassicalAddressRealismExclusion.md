# Classical Address Realism Excluded by Finite Projection Contexts

## Abstract

The finite projection contexts exclude deterministic classical hidden-address realism.

**Theorem 1.1 (One hidden address induces a global projection valuation).**

$$ClassicalAddressRealism \Rightarrow \operatorname{addressInducesValuation}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.address_induces_global_projection_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The realism premise is independent of the obstruction: it consists of a nonempty hidden-address type, a deterministic binary outcome table on the eighteen ray labels at each address, and one-per-context completeness for all nine tetrads.

For a fixed address, choose the ray label representing each actual projection and read the address's outcome table there. The labeled-projection injectivity theorem proves that this choice agrees with every displayed label, so the context-completeness equations become the global projection-valuation equations.

**Theorem 1.2 (No deterministic classical hidden-address model exists).**

$$\neg \operatorname{Nonempty}(\operatorname{ClassicalAddressRealism}).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.classical_address_realism_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A classical address-realistic model assigns every one of the eighteen ray labels a definite binary value at each member of a nonempty hidden-address space. Context completeness requires exactly one selected ray in each of the nine displayed tetrads at every address.

The bridge theorem first turns any single address into a valuation on the actual ConfigurationProjection subtype. Only then does the proof invoke the frozen projection_valuation_obstruction; the realism premise is not a renamed copy of its conclusion.

The conclusion concerns only this explicit finite projection configuration and this context-independent binary assignment law. It makes no claim about arbitrary dimensions, arbitrary operator algebras, locality, or every possible meaning of classical realism.

**Theorem 1.3 (The eight-context assignment is a genuine near miss).**

$$\exists v: Fin(18) \to Fin(2),\ v \operatorname{satisfiesFirstEight}, \land \neg v \operatorname{satisfiesAllNine}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.eight_context_near_miss_cannot_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen eightContextValuation supplies one explicit binary assignment whose totals are one in contexts zero through seven.

The same assignment cannot satisfy the ninth context: the frozen parity contradiction rules out all nine equations. This keeps the anti-vacuity witness while making clear that the local witness does not extend to a global valuation.

**Theorem 1.4 (The finite projection configuration is nonvacuous).**

$$\operatorname{Nonempty}(\operatorname{Fin}(9)) \land (\forall c \in \operatorname{Fin}(9),\ \operatorname{card}(\operatorname{projectionContext}(c)) = 4) \land (\exists v: \operatorname{ConfigurationProjection} \to \operatorname{Fin}(2),\ \sum_{k \in \operatorname{Fin}(4)} v(\operatorname{labeledProjection}(\operatorname{contextRay}(0,k))) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.projection_configuration_is_nonvacuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct exhibits a member of the nine-context index type. The second proves that every context contains exactly four distinct actual projections, using injectivity of both the context ray map and the labeled-projection embedding.

For the third conjunct, an explicit binary function assigns one to the first projection of context zero and zero to every other projection. Its sum on that context is one. Thus the contradiction comes from global incompatibility among the nine contexts, not from an empty context family, malformed contexts, or a locally unsatisfiable constraint.

## References

- Truth anchor: `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.address_induces_global_projection_valuation`
- Truth anchor: `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.classical_address_realism_exclusion`
- Truth anchor: `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.eight_context_near_miss_cannot_extend`
- Truth anchor: `D5/S3/QuantumContext/ClassicalAddressRealismExclusion.projection_configuration_is_nonvacuous`
- Dependency: [D5/S3/QuantumContext/ProjectionValuationObstruction](ProjectionValuationObstruction.md)
