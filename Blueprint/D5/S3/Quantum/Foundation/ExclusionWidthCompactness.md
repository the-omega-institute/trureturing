# Full-effect widths and compact original-label layers

## Abstract

Entire original-effect widths have compact saturation, compact positive layers under faithful labels, and a positive attained global maximum.

The carrier is any finite dimensional real normed vector space with a closed pointed generating convex cone C and a real-linear unit u strictly positive on every nonzero cone vector. K is the entire normalized base, P contains all its extreme points, and effects are the entire interval from zero to u on C. The ball condition assigns to each actual original pure label an injective affine chart of its entire exclusion by a closed Euclidean unit ball of some positive finite dimension. The dimension may vary and may equal one. Only the global maximum uses a nonzero carrier explicitly.

The original exclusion uses the minimum of every proper effect confirming the label. The existing exclusion predicate instead asks for such an effect vanishing at a specified original state. Compactness of the entire confirming-effect set proves the minimum is attained for every state, including mixed states, and makes the two definitions equal. The existing whole-ball face theorem supplies a single original confirmer vanishing on the entire exclusion. No finite effect menu, selected label set, pure closedness, Pair premise, common metric, spectral representation, fibration or whole-ball continuity is assumed.

**Definition 1.1 (confirmingEffects).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.confirmingEffects`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.confirmingEffects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete compact slice of all original continuous proper effects evaluating to one at a specified label. In finite dimension every original linear effect has this continuous representation.

**Definition 1.2 (oscillation).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.oscillation`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.oscillation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum minus infimum of one effect on the whole specified set. Compact nonempty sets attain both extrema.

**Definition 1.3 (width).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum of whole-set oscillations over the entire original proper effect interval. On each entire original exclusion ball this supremum is attained by an effect and two endpoints.

**Definition 1.4 (EndpointData).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.EndpointData`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.EndpointData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One original label, two original states and two full original effects, stored in one finite product. No purity or finite selection of the original domains is part of this type.

**Definition 1.5 (endpointCertificates).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.endpointCertificates`

*Formalization.* `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.endpointCertificates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Joint data in K cubed times the full effect interval squared. The last effect confirms the label and vanishes at both endpoints; the other effect separates their readings by at least a specified real threshold. Purity is a consequence for positive thresholds with faithful labels, and for threshold one without faithful labels.

**Theorem 1.6 (Relative upper semicontinuity).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_upperSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_upperSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the relative topology of all original pure states, whole-ball width is upper semicontinuous. Only the positive-dimensional entire-ball condition is required; faithful labels and closedness of the pure carrier are not premises. A superlevel is the inverse image of the compact projection of joint endpoint certificates.

**Theorem 1.7 (Ambient compact positive layers).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.positive_width_layer_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.positive_width_layer_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strictly positive real threshold, all original pure labels whose entire exclusions have width at least that threshold form a compact subset of the original ambient vector space. The empty layer is included. Faithfulness means injectivity of the map from every original pure label to its entire exclusion set. Two distinct common zero endpoints force the compact exposed one-face to have one extreme point; Krein-Milman then makes that entire face a singleton.

**Theorem 1.8 (Attained positive width on the minimum-defined exclusion).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.original_exclusion_width`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.original_exclusion_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure label, take every original state at which the infimum over all original confirming effects is zero. Its entire effect width is strictly positive and at most one, and one original effect and two states in this entire set attain it. Compactness of the full confirming interval proves attainment of the infimum at every mixed input, identifying this set with the existing existential exclusion. A separating continuous functional is normalized using its actual extrema on the entire original base and the original unit, producing a proper effect on the whole cone.

**Theorem 1.9 (Compact saturation without faithful labels).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.saturated_labels_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.saturated_labels_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The labels of width-one entire exclusions form a compact subset of the original ambient space, possibly empty. Global label injectivity is not assumed. A proper effect reaching one and zero on an entire ball has pure endpoints: its maximum face intersects the ball in a singleton by strict convexity of the entire chart. If that ball had two labels, zero symmetry and the two-common-points rigidity would identify the two endpoint exclusions, forcing a pure point to exclude itself.

**Theorem 1.10 (Width collapse at mixed limits).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_tendsto_zero_of_mixed_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_tendsto_zero_of_mixed_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sequence of original pure labels converging in the ambient vector space to a nonpure point, the widths of their entire exclusion balls tend to zero under faithful labels. Each positive layer is ambient compact and therefore excludes a neighborhood of the nonpure limit. No compactness of the entire pure carrier is assumed.

**Theorem 1.11 (Independent whole-ball diameter collapse).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.diameter_tendsto_zero_of_mixed_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.diameter_tendsto_zero_of_mixed_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary convergent sequence and nonpure ambient limit, the diameters of the entire exclusion balls tend to zero under faithful labels. This proof uses compact joint endpoint certificates with a positive endpoint-distance threshold. Such a certificate forces its label to be pure by the common-zero argument. A neighborhood excluding the compact certificate projection bounds every endpoint distance and hence the whole diameter. It uses no comparison between effect width and metric diameter.

**Theorem 1.12 (Countable exhaustion of the whole pure carrier).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.pure_eq_countable_width_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.pure_eq_countable_width_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All original pure states are exactly the union of the layers with thresholds one over n plus one, indexed by natural n starting at zero. This is the positive-integer reciprocal exhaustion, with dimension-one ball charts retained. Positivity of each whole-ball width supplies a reciprocal threshold. Under faithful labels the preceding compact-layer theorem makes each member ambient compact.

**Theorem 1.13 (Positive global maximum at an original pure label).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_global_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_global_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonzero finite dimensional original space with faithful labels, some actual original pure label attains the supremum of all whole-ball widths. Its width is strictly positive and at most one. Pure spanning supplies a pure label. Its positive width defines a nonempty compact layer, and relative upper semicontinuity gives a maximum on that layer; all labels outside the layer have smaller width. The conclusion gives no equality of the maximum with one.

**Theorem 1.14 (Every near-saturated sequence has a saturated limit).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.near_saturation_subsequence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.near_saturation_subsequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sequence of original pure labels whose entire-ball widths tend to one admits a strictly increasing map of natural indices and a corresponding ambient-convergent subsequence with a saturated original pure limit. Global injectivity is not used. Each label is paired with an attaining full effect, both endpoints and a common-zero confirmer. A single subsequence in their compact joint product preserves all five objects and reaches a width-one certificate; local saturated-label uniqueness makes its label pure.

**Theorem 1.15 (Uniform upper gap in the absence of saturation).**

Lean statement: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.no_saturation_uniform_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.no_saturation_uniform_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If no original pure label has whole-ball width one, the supremum over all original pure labels is strictly less than one under the positive-dimensional entire-ball condition alone. Maximize endpoint oscillation on the entire compact joint-certificate set. Equality with one would produce a saturated pure label. No uniform gap is assumed, and this result implies neither automatic injectivity nor a saturated ball.

The conclusions are conditional mathematics on the same original full-effect model. They give no automatic injectivity, edge openness, stable-zero-witness principle, saturation propagation, physical realization or quantum representation. A positive attained maximum need not equal one. No literature priority is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.EndpointData`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.confirmingEffects`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.diameter_tendsto_zero_of_mixed_limit`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.endpointCertificates`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.near_saturation_subsequence`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.no_saturation_uniform_gap`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.original_exclusion_width`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.oscillation`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.positive_width_layer_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.pure_eq_countable_width_layers`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.saturated_labels_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_global_maximum`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_tendsto_zero_of_mixed_limit`
- Truth anchor: `D5/S3/Quantum/Foundation/ExclusionWidthCompactness.width_upperSemicontinuous`
- Dependency: [D5/S3/Quantum/Foundation/ContinuousFrameSum](ContinuousFrameSum.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalFacePolarity](OriginalFacePolarity.md)
