# Native Time Profiles

## Abstract

Native time profiles, copy polynomials, and exact copy expressibility of tail regions.

**Definition 1.1 (Reflexive current successors).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.successors`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.successors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set retains complete timed attributes of the current event itself and all its current causal successors, including unselected targets.

**Definition 1.2 (Native event cell).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.cell`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A current event determines its timed attribute, selected Boolean bit, and finite successor attribute set.

**Definition 1.3 (Signed finite time profile).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum signed singleton cell measures over every current event. Noncurrent archive events contribute no cells. Events in the same cell add their integer coefficients.

**Definition 1.4 (Linear cell transport).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.push`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.push` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport a finitely supported integer profile along a cell map, adding coefficients when cells merge.

**Definition 1.5 (Terminal selected charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This integer linear functional weights selected cells by one and unselected cells by zero.

**Theorem 1.6 (Terminal readout equals native charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout_gamma`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout_gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rich native history, applying the selected-cell functional to its complete time profile gives precisely its native q readout.

**Definition 1.7 (Integer attribute shift).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.shiftAttribute`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.shiftAttribute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add an arbitrary integer to time while preserving position, sign and source.

**Definition 1.8 (All five unary updates).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.unaryCell`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.unaryCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complement flips selection. Spatial and source filters conjoin their predicate with selection. Causal filtering tests whether the successor set hits the fixed timed-attribute predicate. Shifting changes both the own attribute and every successor attribute.

**Theorem 1.9 (Native unary operations are linear pushes).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_unary`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_unary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every balanced history and every native unary primitive, the actual output time profile equals the corresponding linear push of the input profile.

**Theorem 1.10 (Parallel profiles add).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_parallel`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_parallel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of balanced histories, the complete profile of their tagged parallel composite is the sum of the two profiles. Actual current events are reindexed; each component retains its successor set.

**Definition 1.11 (Generated product attribute).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productAttribute`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productAttribute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Generated time is the maximum parent time plus one. Positions add, signs multiply via Boolean equality, and sources form the ordered tree product.

**Definition 1.12 (Generated product cell).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productCell`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parent selection bits conjoin. The successor set of a newly generated current event is the singleton containing its own generated attribute.

**Definition 1.13 (Bilinear cell push).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productPush`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productPush` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extend the generated cell operation by integer bilinearity in the two finitely supported profiles.

**Theorem 1.14 (Native product equals the bilinear push).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_product`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of balanced histories, the actual generated-product profile equals the bilinear push of the two parent profiles. The proof uses the exact parent-pair current equivalence and absence of paths out of generated nodes.

**Definition 1.15 (Homogenized native profile).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.pack`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.pack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A balanced native history is embedded as the pair consisting of the integer one and its complete time profile. The extra coordinate represents constants in the multilinear syntax interpretation.

**Definition 1.16 (Multilinear interpretation of the copy syntax).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each input occurrence occupies a distinct multilinear coordinate. Constants use the empty coordinate family. Unary nodes use linear profile pushes. Binary nodes combine disjoint leaf families using bilinear homogenized parallel or product maps. Temporal nodes are assigned parallel semantics here; the correctness theorem explicitly requires temporal freedom.

**Theorem 1.17 (The multilinear model computes native evaluation).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model_eval`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arity, temporal-free copy term, independent balanced leaf assignment and successful native result, applying the multilinear model to the packed leaves gives exactly the packed result. Structural induction consumes the native unary, parallel and product profile updates. This connects the formal multilinear interpretation to the actual finite native histories.

**Definition 1.18 (Tagged parallel copies).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copies`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

copies 0 is the empty balanced history and copies (n+1) appends one tagged parallel copy of the input.

**Definition 1.19 (Independent copy evaluation).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.value`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

value is the total native value of a copy term under an independent leaf assignment, with the empty history as the failure default.

**Definition 1.20 (The 5B/5C polynomial bridge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopyPolynomialLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopyPolynomialLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive temporal-free copy term and balanced input, diagonal evaluation on independently replicated leaves is an integer polynomial in the replication count. Its degree is bounded by the number of input occurrences, its constant coefficient is q(N(0)), and its linear coefficient is the sum of one-hole slice values minus the full constant correction r·q(N(0)). The theorem copy_polynomial_law proves this statement from the actual native time profile.

**Definition 1.21 (Squarefree profile coefficients).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.profileCoefficients`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.profileCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coefficient is the multilinear profile model evaluated with the input profile on the indicated set of leaf occurrences and the empty profile elsewhere.

**Theorem 1.22 (Native independent-copy expansion).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.profile_multiaffine`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.profile_multiaffine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every temporal-free copy term, balanced input and independently chosen natural replication counts, the actual native profile is the sum over sets of distinct leaf occurrences, weighted by the product of their counts. The proof consumes model_eval and the primitive profile updates.

**Theorem 1.23 (Lemma 5B and the full 5C coefficient).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_polynomial_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_polynomial_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual charge of a temporal-free term on m copies at every leaf is an integer polynomial of degree at most the arity. The constant coefficient is q(N(0)); the linear coefficient is the sum of the one-leaf slice charges minus r times q(N(0)). No vanishing constant is assumed.

**Definition 1.24 (Region readout under copies).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopiesRegionLinear`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopiesRegionLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate specifies integer linearity of every region readout under tagged parallel copies; copies_region_linear proves it.

**Definition 1.25 (Scalar readout of a native word).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.wordReadout`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.wordReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wordReadout extracts q from a successful native one-hole word and returns the neutral integer on failure.

**Definition 1.26 (Finite one-hole slice family).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopySliceReadoutLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopySliceReadoutLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CopySliceReadoutLaw is the exact finite normalization consequence needed after the polynomial bridge: every total copy expression representing the fixed region supplies a finite family of total one-hole words whose readouts sum to that region.

**Definition 1.27 (Joint saturation for finite word families).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopySaturationLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopySaturationLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CopySaturationLaw records the common indistinguishability construction below a nonpositive time threshold for any finite family of total one-hole words.

**Definition 1.28 (Positive finite diagonal copy expression).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopyQExpressible`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopyQExpressible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A region is copy-expressible when some positive finite copy term is total on every balanced input and its diagonal q readout equals the region readout.

**Theorem 1.29 (Identification from natural evaluations).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.polynomial_identification`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.polynomial_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integer polynomial whose values at all natural numbers are n times a fixed integer is X multiplied by the constant polynomial a.

**Theorem 1.30 (Exact regional replication law).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copies_region_linear`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copies_region_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every fixed region readout on n tagged parallel copies equals n times its value on the original balanced input.

**Theorem 1.31 (Common finite-family saturation).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_saturation_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_saturation_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any finite family of total one-hole words admits a common nonpositive threshold and, at every position and every pair of times below it, a pair of inputs with equal readouts for every word. The proof reuses the existing finite predicate construction and its saturation theorem. The selected positive event has a common source in the pair; this statement does not require that source to be leaf(0).

**Theorem 1.32 (Polynomial identification recovers the slices).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_slice_readout_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_slice_readout_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalize the total copy term before choosing the input. Identify its polynomial from all natural replication counts using regional linearity, obtain zero constant coefficient, and use the full linear coefficient to recover the exact sum of the fixed one-hole slices.

**Theorem 1.33 (Finite word sums force a uniform tail).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.sum_word_readouts_implies_tail`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.sum_word_readouts_implies_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved joint saturation shows that a finite sum of total one-hole word readouts cannot distinguish sufficiently early times at one position; equality of the sum and the selected-region calculation therefore forces Tail.

**Theorem 1.34 (Copy necessity).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_q_expressible_implies_tail`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_q_expressible_implies_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Copy expressibility implies Tail by the proved polynomial, slice-readout and finite joint-saturation results, without additional law assumptions.

**Theorem 1.35 (Tail supplies a one-copy expression).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.tail_implies_copy_q_expressible`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.tail_implies_copy_q_expressible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing one-hole tail construction embeds as a positive one-occurrence copy term.

**Theorem 1.36 (Proposition 64).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.proposition64`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.proposition64` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every region, the exact positive-arity all-input copy criterion is equivalent to Tail. Necessity uses the native profile polynomial, its full linear coefficient, and finite joint saturation; sufficiency reuses the frozen one-hole construction. No profile or saturation assumptions remain.

**Theorem 1.37 (Three-way equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.proposition64_three_way`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.proposition64_three_way` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every region, copy expressibility is equivalent to the conjunction of the existing one-hole QExpressible criterion and Tail. The copy necessity retains the native polynomial proof on its live dependency path.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopiesRegionLinear`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopyPolynomialLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopyQExpressible`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopySaturationLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.CopySliceReadoutLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.cell`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copies`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copies_region_linear`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_polynomial_law`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_q_expressible_implies_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_saturation_law`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.copy_slice_readout_law`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_parallel`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_product`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.gamma_unary`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.model_eval`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.pack`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.polynomial_identification`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productAttribute`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productCell`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.productPush`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.profileCoefficients`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.profile_multiaffine`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.proposition64`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.proposition64_three_way`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.push`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.readout_gamma`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.shiftAttribute`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.successors`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.sum_word_readouts_implies_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.tail_implies_copy_q_expressible`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.unaryCell`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.value`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.wordReadout`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/CoarseObservation](CoarseObservation.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility](RegionFilterQExpressibility.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization](TotalCopyNormalization.md)
