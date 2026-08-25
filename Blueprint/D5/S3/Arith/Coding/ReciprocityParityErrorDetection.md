# Reciprocity Parity Error Detection

## Abstract

A valid finite sign report detects one flipped symbol but can accept two flips.

**Theorem 1.1 (A parity report detects one flip but not every pair of flips).**

$$\forall I: \operatorname{Type},\ [\operatorname{DecidableEq}\left(I\right)], S: \operatorname{Finset}\left(I\right),\ profile: I \to \operatorname{ZUnits}, a, b: I,\ a \in S \land b \in S \land a \neq b \land \prod_{v \in S} profile(v) = 1 \Rightarrow (\prod_{v \in S} \operatorname{flipLocalSign}\left(profile, a, v\right) = -1 \land \prod_{v \in S} \operatorname{flipLocalSign}\left(profile, a, v\right) = \prod_{v \in S} \operatorname{flipLocalSign}\left(profile, b, v\right) \land \prod_{v \in S} \operatorname{update}\left(\operatorname{flipLocalSign}\left(profile, a\right), b, -profile(b), v\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ReciprocityParityErrorDetection.reciprocity_parity_error_detection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite report of integer signs whose product is one, flipping either of two selected coordinates changes the product to minus one. The two single-error syndromes are equal, so this one check does not identify which selected coordinate was flipped.

If the two selected coordinates are distinct, flipping both restores the product to one. This supplies an explicit even-error pattern that the parity check accepts.

## References

- Truth anchor: `D5/S3/Arith/Coding/ReciprocityParityErrorDetection.reciprocity_parity_error_detection`
