# Complete Root Supergraph Exclusion

## Abstract

An exhaustive common-unbiased projector catalogue with a single canonical six-block and a disjoint bipartite remainder excludes two mutually unbiased completions.

**Theorem 1.1 (Exhaustive coverage and a one-sided graph certificate exclude a quartet).**

$$CompleteRootCover \land CanonicalSixBlockAndBipartiteRemainder \Rightarrow NoMutuallyUnbiasedCompletionPair.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion.no_mutually_unbiased_completions_of_complete_root_supergraph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean statement is on the existing RankOneContext and overlap API. An arbitrary label type indexes candidate projectors. Every projector of each actual completion must equal a labelled candidate. Any distinct labels with zero trace overlap either both lie in a six-element canonical set, or both lie outside it and have opposite Boolean colors. The contexts are complete orthogonal six-element rank-one measurements.

Three distinct vertices cannot form a clique in a bipartite component. Therefore every six-element context uses exactly the canonical set. Two such contexts share a normalized rank-one projector, giving overlap one, which contradicts mutual unbiasedness at overlap one-sixth.

Only a supergraph is required; allowed edges may disappear under parameter variation. The theorem does not read or trust an external interval report. A separate analytic, kernel-checked adapter must discharge exhaustive root coverage and the certified nonedge implications. No intrinsic information score or maximal-catalog admission is asserted here.

**Theorem 1.2 (Two covered six-frames have a quantitatively large cross overlap).**

$$TubeCoverWithLargeSameTubeOverlap \land CanonicalSixBlockAndBipartiteSmallOverlapSupergraph \land TwoSixFramesWithSmallInternalOverlaps \Rightarrow SomeCrossOverlapAtLeastMu.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion.six_frames_have_large_cross_overlap_of_root_tube_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tubes are sets of matrices on the existing Fin 6 carrier. For eta <= mu, any two matrices in one tube have real trace overlap at least mu. Matrices in distinct tubes with overlap below eta must have labels in the canonical six-block, or labels of opposite colors in the disjoint bipartite remainder. Every member of both six-frames lies in a tube, and all within-frame overlaps are below eta.

Each frame has distinct labels by the same-tube lower bound. The existing private clique argument confines both label sets to the six canonical labels. The frames therefore share a label, and the same-tube bound supplies a cross overlap at least mu. Tubes may be empty, contain several roots, or overlap. Root existence, uniqueness, and exact root count are not needed.

For normalized outer products, this is a squared-inner-product bound. The interval instance uses mu=99/100 and eta=1/100000000; the theorem itself does not read that instance or its PASS report. The previous exact root-catalogue theorem is retained. No new semantic Arena or intrinsic-information gain is asserted.

**Theorem 1.3 (Five-color partner certificates exclude a second six-frame).**

$$WholeTubeOrthogonalityAndUnbiasednessEnclosures \land EveryFirstSixCliqueHasFiveColorableCommonPartnerGraph \land TwoCoveredSixFramesWithSmallInternalOverlaps \Rightarrow SomeCrossUnbiasednessErrorAtLeastTau.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion.two_relation_tube_certificate_forces_cross_unbiasedness_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem is stated for actual matrices in sets of tube matrices, using real trace overlap. Same-tube overlap at least mu and internal overlap below eta <= mu make each six-frame use six distinct labels. An orthogonality candidate relation contains every pair with overlap below eta. A separate unbiased candidate relation contains every pair whose overlap differs from one-sixth by less than tau.

For every injectively labelled first six-clique, the induced graph on labels unbiased-compatible with all six first labels has a proper coloring into Fin 5. A hypothetical second compatible six-frame would inject Fin 6 into Fin 5, a contradiction. No uniqueness of the first completion, global bipartition, or canonical-only classification is used.

The computational instance enumerates all 2414 first cliques, each with at most fourteen common candidate labels. The compact certificate covers their 23 distinct partner sets by nine five-colored supersets. The Lean theorem retains exhaustive coverage, overlap enclosures, and the coloring certificate as mathematical hypotheses. An external PASS or saved list does not discharge them. No kernel admission is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion.no_mutually_unbiased_completions_of_complete_root_supergraph`
- Truth anchor: `D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion.six_frames_have_large_cross_overlap_of_root_tube_cover`
- Truth anchor: `D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion.two_relation_tube_certificate_forces_cross_unbiasedness_error`
- Dependency: [D5/S3/Quantum/Tomography/RankOneContextCommutator](RankOneContextCommutator.md)
