# Signed birth enumeration

## Abstract

Actual legal signed births and exhaustive proper-stage enumerations under the continuum hypothesis.

The variables top and m range over the indicated topological and measurable structures on X. SupportFamily(X) consists of a Nat-indexed sequence of clopen sets, nonempty at every index, with pairwise disjoint underlying sets. BornData(V) is the exact subtype of sequences of actual RegularSigned(X) measures whose total variation on the whole space is one, whose total variation on the complement of V(n) is zero, and whose positive Jordan mass on the whole space is at least one half, at every n. Both Jordan parts are regular. These are independent certificates; normalization alone does not imply support nullity or positive mass. Label is exactly SignedProperLimit.Label. Every enumerated value is a legal signed sequence, including labels not yet eligible for bookkeeping.

**Theorem 1.1 (Countable-generator signed coding).**

$$\forall X \in TypeU,\; \forall m \in \operatorname{MeasurableSpace}\left(X\right),\; \operatorname{CountablyGenerated}\left(X, m\right) \Rightarrow \operatorname{Le}\left(\operatorname{CardinalMk}\left(Nat \to \operatorname{SignedMeasure}\left(X, m\right)\right), \operatorname{continuum}\left(UniverseU\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.signed_sequences_card_le_continuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any countably generated measurable space, signedCode evaluates a real signed measure on finite intersections of natGeneratingSequence. The empty intersection is the whole space. VectorMeasure.ext_of_generateFrom on the existing finite-intersection pi-system proves injectivity. A sequence of measures is then coded by reals indexed by Nat times Finset(Nat). This countable index has real-function cardinal continuum. No regularity, normalization, positivity, compactness or signed representation theorem is required for this bound.

**Theorem 1.2 (Total exhaustive signed enumeration).**

$$\forall X \in TypeOne,\; \forall top \in \operatorname{TopologicalSpace}\left(X\right),\; \operatorname{PseudoMetrizableSpace}\left(X, top\right) \Rightarrow \left(\operatorname{CompactSpace}\left(X, top\right) \Rightarrow \left(\forall m \in \operatorname{MeasurableSpace}\left(X\right),\; \operatorname{BorelSpace}\left(X, top, m\right) \Rightarrow \left(\operatorname{SecondCountableTopology}\left(X, top\right) \Rightarrow \left(\forall V \in \operatorname{SupportFamily}\left(X, top\right),\; \operatorname{continuum}\left(UniverseZero\right) = alephOne \Rightarrow \left(\exists nu \in Label \to \operatorname{BornData}\left(X, top, m, V\right),\; \operatorname{Surjective}\left(nu\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.exists_signed_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X live in Type1 with a compact pseudometrizable second-countable topology and its Borel measurable space. For every SupportFamily V, CH in Universe0 gives a surjection Label to BornData(V). Nonemptiness is proved by choosing a point in each support and taking the Jordan pair (dirac,zero). The Jordan conversion theorem identifies the actual positive and negative parts; their sum is dirac. Regularity follows on the proper compact pseudometrizable Borel carrier. The countable-generator code bounds the entire legal subtype, and explicit cardinal lifts align CH with Label. The embedding-to-surjection theorem uses this actual nonempty codomain. No optional value fills a measure entry.

**Theorem 1.3 (Legal supports from an onto base projection).**

$$\forall X \in TypeU,\; \forall top \in \operatorname{TopologicalSpace}\left(X\right),\; \forall p \in \operatorname{ContinuousMap}\left(X, top, \operatorname{Cube}\left(omega\right)\right),\; \operatorname{Surjective}\left(p\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{SupportFamily}\left(X, top\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.exists_supportFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any topological space with an actual continuous surjection to the literal Cube(omega) has a SupportFamily. The nth base cylinder has coordinate n true and every preceding natural coordinate false. Finite intersections make it clopen; the single-true-coordinate point proves nonemptiness; the earlier true coordinate contradicts membership in a later cylinder. SupportFamily.pullback uses the given continuous map literally, preserving each index, clopenness and disjointness; surjectivity preserves nonemptiness. The same operation transports an already enumerated family to its actual launch carrier.

**Theorem 1.4 (Exhaustive support families and clopens).**

$$\forall X \in TypeOne,\; \forall top \in \operatorname{TopologicalSpace}\left(X\right),\; \operatorname{CompactSpace}\left(X, top\right) \Rightarrow \left(\operatorname{T2Space}\left(X, top\right) \Rightarrow \left(\operatorname{TotallyDisconnectedSpace}\left(X, top\right) \Rightarrow \left(\operatorname{SecondCountableTopology}\left(X, top\right) \Rightarrow \left(\forall p \in \operatorname{ContinuousMap}\left(X, top, \operatorname{Cube}\left(omega\right)\right),\; \operatorname{Surjective}\left(p\right) \Rightarrow \left(\operatorname{continuum}\left(UniverseZero\right) = alephOne \Rightarrow \left(\left(\exists U \in Label \to \operatorname{SupportFamily}\left(X, top\right),\; \operatorname{Surjective}\left(U\right)\right) \land \left(\exists P \in Nat \to \operatorname{Clopens}\left(X, top\right),\; \operatorname{Surjective}\left(P\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.exists_clopen_enumerations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a compact Hausdorff totally disconnected second-countable Type1 carrier with an onto base projection, CH gives a surjection Label to all SupportFamily values and a surjection Nat to all clopens. The existing Clopens.countable_iff_secondCountable theorem supplies countability. Countable sequences of clopens have cardinal at most continuum, and the actual base pullback supplies a legal value. These are proper-stage birth constructions. They neither construct the global history nor impose metrizability or subsequence bookkeeping on the final omegaOne space.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.exists_clopen_enumerations`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.exists_signed_enumeration`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.exists_supportFamily`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBirthEnumeration.signed_sequences_card_le_continuum`
- Dependency: [D5/S3/Topology/InverseLimit/SignedProperLimit](SignedProperLimit.md)
