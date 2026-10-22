# Copy Profiles and Polynomial Readouts

## Abstract

Native multilinear time profiles yield the complete copy polynomial and the finite slice argument for tail regions.

**Definition 1.1 (Tagged parallel copies).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copies`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

copies 0 is the empty balanced history and copies (n+1) appends one tagged parallel copy of the input.

**Definition 1.2 (Independent copy evaluation).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.value`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

value is the total native value of a copy term under an independent leaf assignment, with the empty history as the failure default.

**Definition 1.3 (The 5B/5C polynomial bridge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyPolynomialLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyPolynomialLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive temporal-free copy term and balanced input, diagonal evaluation on independently replicated leaves is an integer polynomial in the replication count. Its degree is bounded by the number of input occurrences, its constant coefficient is q(N(0)), and its linear coefficient is the sum of one-hole slice values minus the full constant correction r·q(N(0)). The theorem copy_polynomial_law proves this statement from the actual native time profile.

**Definition 1.4 (Squarefree profile coefficients).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.profileCoefficients`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.profileCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coefficient is the multilinear profile model evaluated with the input profile on the indicated set of leaf occurrences and the empty profile elsewhere.

**Theorem 1.5 (Native independent-copy expansion).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.profile_multiaffine`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.profile_multiaffine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every temporal-free copy term, balanced input and independently chosen natural replication counts, the actual native profile is the sum over sets of distinct leaf occurrences, weighted by the product of their counts. The proof consumes model_eval and the primitive profile updates.

**Theorem 1.6 (Lemma 5B and the full 5C coefficient).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_polynomial_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_polynomial_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual charge of a temporal-free term on m copies at every leaf is an integer polynomial of degree at most the arity. The constant coefficient is q(N(0)); the linear coefficient is the sum of the one-leaf slice charges minus r times q(N(0)). No vanishing constant is assumed.

**Definition 1.7 (Region readout under copies).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopiesRegionLinear`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopiesRegionLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate specifies integer linearity of every region readout under tagged parallel copies; copies_region_linear proves it.

**Definition 1.8 (Scalar readout of a native word).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.wordReadout`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.wordReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wordReadout extracts q from a successful native one-hole word and returns the neutral integer on failure.

**Definition 1.9 (Finite one-hole slice family).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySliceReadoutLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySliceReadoutLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CopySliceReadoutLaw is the exact finite normalization consequence needed after the polynomial bridge: every total copy expression representing the fixed region supplies a finite family of total one-hole words whose readouts sum to that region.

**Definition 1.10 (Joint saturation for finite word families).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySaturationLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySaturationLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CopySaturationLaw records the common indistinguishability construction below a nonpositive time threshold for any finite family of total one-hole words.

**Definition 1.11 (Positive finite diagonal copy expression).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyQExpressible`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyQExpressible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A region is copy-expressible when some positive finite copy term is total on every balanced input and its diagonal q readout equals the region readout.

**Theorem 1.12 (Identification from natural evaluations).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.polynomial_identification`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.polynomial_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integer polynomial whose values at all natural numbers are n times a fixed integer is X multiplied by the constant polynomial a.

**Theorem 1.13 (Exact regional replication law).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copies_region_linear`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copies_region_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every fixed region readout on n tagged parallel copies equals n times its value on the original balanced input.

**Theorem 1.14 (Lemma 6 for a common finite family).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_saturation_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_saturation_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any finite family of total one-hole words admits a common nonpositive threshold and, at every position and every pair of times below it, a pair of inputs with equal readouts for every word. The proof reuses the existing finite predicate construction and its saturation theorem.

**Theorem 1.15 (Polynomial identification recovers the slices).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_slice_readout_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_slice_readout_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalize the total copy term before choosing the input. Identify its polynomial from all natural replication counts using regional linearity, obtain zero constant coefficient, and use the full linear coefficient to recover the exact sum of the fixed one-hole slices.

**Theorem 1.16 (Finite word sums force a uniform tail).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.sum_word_readouts_implies_tail`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.sum_word_readouts_implies_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved joint saturation shows that a finite sum of total one-hole word readouts cannot distinguish sufficiently early times at one position; equality of the sum and the selected-region calculation therefore forces Tail.

**Theorem 1.17 (Copy necessity).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_q_expressible_implies_tail`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_q_expressible_implies_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Copy expressibility implies Tail by the proved polynomial, slice-readout and finite joint-saturation results, without additional law assumptions.

**Theorem 1.18 (Tail supplies a one-copy expression).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.tail_implies_copy_q_expressible`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.tail_implies_copy_q_expressible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing one-hole tail construction embeds as a positive one-occurrence copy term.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopiesRegionLinear`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyPolynomialLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyQExpressible`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySaturationLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySliceReadoutLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copies`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copies_region_linear`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_polynomial_law`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_q_expressible_implies_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_saturation_law`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_slice_readout_law`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.polynomial_identification`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.profileCoefficients`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.profile_multiaffine`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.sum_word_readouts_implies_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.tail_implies_copy_q_expressible`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.value`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.wordReadout`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile](NativeTimeProfile.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility](RegionFilterQExpressibility.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization](TotalCopyNormalization.md)
