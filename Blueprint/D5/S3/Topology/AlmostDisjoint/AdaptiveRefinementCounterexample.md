# An adaptive finite-refinement counterexample over the convergent sequence

## Abstract

A literal compact open surjection defeats all finite closed open-restriction refinements.

The total space is the literal tagged subset of OnePoint Nat times unitInterval times Bool^(A + Nat) supplied by TaggedCompactSpace. Write g for its real value coordinate. U(false) is the literal set g < 2/3, and U(true) is the literal set g > 1/3. These two open sets cover the total space. A finite refinement may have any number of closed pieces, including zero when the total space is empty; its assignments into the original cover may repeat, pieces may be empty, and no individual restriction must be onto. Every restriction is required to be open into the entire base OnePoint Nat.

The information audit remains unfinished. The source-owner mirror checks the whole existential source statement, but whole-source variation and raw occurrence reconstruction/sourceSelection remain absent under https://github.com/the-omega-institute/trureturing/issues/16293. No validated four-slot registration is asserted.

**Theorem 1.1 (Closed open-restriction pieces would create a forbidden threshold partitioner).**

$$\exists A: \operatorname{Set}\left(\operatorname{Set}\left(Nat\right)\right), \exists ell: A \to unitInterval, \operatorname{ADFamily}\left(A\right) \land {\forall a: A, \operatorname{ConvergesOn}\left(natValue, \operatorname{val}\left(a\right), \operatorname{ell}\left(a\right)\right)} \land \operatorname{IsClosed}\left(\operatorname{literalSpace}\left(A, natValue, ell\right)\right) \land \operatorname{IsCompact}\left(\operatorname{literalSpace}\left(A, natValue, ell\right)\right) \land \operatorname{Continuous}\left(\operatorname{projection}\left(A, natValue, ell\right)\right) \land \operatorname{IsOpenMap}\left(\operatorname{projection}\left(A, natValue, ell\right)\right) \land \operatorname{Surjective}\left(\operatorname{projection}\left(A, natValue, ell\right)\right) \land {\forall b: Bool, \operatorname{IsOpen}\left(\operatorname{U}\left(b\right)\right)} \land {\forall x: \operatorname{Space}\left(A, natValue, ell\right), \exists b: Bool, x \in \operatorname{U}\left(b\right)} \land \neg\operatorname{HasFiniteClosedRefinement}\left(\operatorname{projection}\left(A, natValue, ell\right), U\right) \land \neg\operatorname{HasOpenZeroDimensionalResolution}\left(\operatorname{projection}\left(A, natValue, ell\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample.exists_compact_open_map_no_finite_closed_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the actual convergent maximal almost-disjoint family from ThresholdPartitionerElimination, index it by its set of distinct members, and choose an existing branch representative for each member to define its limit. The no-threshold-partitioner theorem is unconditional: neither CH nor regularity of continuum is assumed. The compact construction gives the actual continuous open onto projection and continuous compact sections with clopen ranges.

For a closed piece K whose projection is open into the entire base, intersect K with each clopen section range. The projection of this intersection is both compact and open in OnePoint Nat. If it contains infinity it contains cofinitely many natural numbers; otherwise compactness makes its natural-number part finite. On each actual family member, the section over n equals the actual natural point d_n. Hence the set of n with d_n in K partitions every family member.

A finite union of partitioners is again a partitioner. Group all refinement pieces assigned to U(false). The union of their natural-point sets contains every n with natValue(n) <= 1/3: a piece assigned to U(true) cannot cover such a point. The union is contained in natValue(n) < 2/3 by subordination. This produces the exact threshold partitioner that the supplier excludes, contradicting every finite closed refinement.

If a compact Hausdorff zero-dimensional space Z mapped continuously onto the total space with open composite projection, pull the two open sets back to Z. Mathlib supplies a finite subordinate disjoint clopen cover. Its images are closed and cover the total space. For each image, IsOpenMap.of_comp transfers openness of the composite restriction along the continuous surjection from the clopen cell onto that image. These images would be a forbidden refinement. No metrizability of Z is required.

The result establishes the actual compact-open-map obstruction over OnePoint Nat and excludes an open zero-dimensional resolution for that map. The extension to every infinite compact zero-dimensional metrizable base, the full base classification, and the original Peng dynamical question require their separate proofs. Worldwide novelty is not established by this formalization.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/AdaptiveRefinementCounterexample.exists_compact_open_map_no_finite_closed_refinement`
- Dependency: [D5/S3/Topology/AlmostDisjoint/TaggedCompactSpace](TaggedCompactSpace.md)
- Dependency: [D5/S3/Topology/AlmostDisjoint/ThresholdPartitionerElimination](ThresholdPartitionerElimination.md)
