# Golden Branch Observer Decomposition

## Abstract

Golden branch conjugation splits the two-dimensional observation space into trivial and sign channels.

**Theorem 1.1 (The two golden branches are the trivial and sign representations).**

$$\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\operatorname{J}\left(e_{+}\right) = e_{-} \land \operatorname{J}\left(e_{-}\right) = e_{+}\right) \land P_{ev} = \frac{1}{2} \cdot \left(I + J\right)\right) \land P_{odd} = \frac{1}{2} \cdot \left(I - J\right)\right) \land \left(\forall v \in V_{br},\; \left(v = P_{ev}(v) + P_{odd}(v) \land \operatorname{J}\left(P_{ev}(v)\right) = P_{ev}(v)\right) \land \operatorname{J}\left(P_{odd}(v)\right) = -P_{odd}(v)\right)\right) \land \operatorname{range}\left(P_{ev}\right) = V_{ev}\right) \land V_{ev} = \operatorname{span}\left(\mathbb{C}, e_{+} + e_{-}\right)\right) \land \operatorname{range}\left(P_{odd}\right) = V_{odd}\right) \land V_{odd} = \operatorname{span}\left(\mathbb{C}, e_{+} - e_{-}\right)\right) \land \operatorname{IsCompl}\left(V_{ev}, V_{odd}\right)\right) \land \left(\forall v \in V_{ev},\; \operatorname{J}\left(v\right) = v\right)\right) \land \left(\forall v \in V_{odd},\; \operatorname{J}\left(v\right) = -v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenBranchObserverDecomposition.golden_branch_observer_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the complex coordinate space on the two real golden embeddings. Galois conjugation is the canonical bit flip, and the even and odd maps are the half-sum and half-difference projectors.

The proof applies the repository's general involution decomposition, then computes the two projector ranges as the spans of (1,1) and (1,-1). These spans are complementary; conjugation acts on them with eigenvalues one and minus one.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenBranchObserverDecomposition.golden_branch_observer_decomposition`
- Dependency: [D5/S0/Conventions/InvolutionDecomposition](../../../S0/Conventions/InvolutionDecomposition.md)
- Dependency: [D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification](../../PrimeForms/Splitting/GoldenLocalBranchClassification.md)
