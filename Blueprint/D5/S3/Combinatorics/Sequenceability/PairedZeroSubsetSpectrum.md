# Coefficient-one zero subsets of signed C3 coordinate bases

## Abstract

Coefficient-one zero subsets of signed C3 coordinate bases

V(r) is the original coordinate group Fin r to ZMod 3. The existential includes uniqueness: every other pair-index set J giving the same original subset equals I.

For a natural rank r, work in the original additive group Fin r to ZMod 3. Write e_i for Pi.single i 1. The alphabet is the image of (i,b) mapped to e_i or minus e_i. Injectivity distinguishes coordinates and signs, so there are exactly 2r distinct nonzero labels.

**Theorem 1.1 (Zero subsets are exactly unions of original opposite pairs).**

$$\forall r \in \mathrm{Nat},\; \forall S \in \mathrm{Finset}\left(\mathrm{V}\left(r\right)\right),\; (S \subseteq \mathrm{alphabet}\left(r\right)) \Rightarrow ((\mathrm{sum}\left(S\right) = 0) \Leftrightarrow (\exists I \in \mathrm{Finset}\left(\mathrm{Fin}\left(r\right)\right),\; (S = \mathrm{pairs}\left(I\right)) \land (\forall J \in \mathrm{Finset}\left(\mathrm{Fin}\left(r\right)\right),\; (S = \mathrm{pairs}\left(J\right)) \Rightarrow (J = I))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum.zero_subset_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the sum of an actual subset S at coordinate i gives the indicator of e_i in S minus the indicator of minus e_i in S. Modulo three this vanishes exactly when the two membership bits agree. Thus S has coefficient-one sum zero if and only if there is a unique coordinate subset I for which S is the union of the original opposite pairs indexed by I.

Good(w) requires nonzero sum on every nonempty proper contiguous interval. Only the full word is exempt, even when its sum is zero. The equivalent decomposition predicate quantifies over actual decompositions w = l ++ u ++ v, with u nonempty and at least one of l or v nonempty. This spectrum supplies no count of Good orders by itself. The paired Good-order enumeration corresponds to known connected chord diagrams; no literature-priority claim or solution of the arbitrary-subset sequenceability problem follows.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum.zero_subset_spectrum`
