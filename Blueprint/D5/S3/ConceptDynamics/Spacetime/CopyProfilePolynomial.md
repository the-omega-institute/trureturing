# Copy Profiles and Polynomial Readouts

## Abstract

The copy profile bridge is stated explicitly and its tail consequence is compiled conditionally.

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

For every positive temporal-free copy term and balanced input, diagonal evaluation on independently replicated leaves is an integer polynomial in the replication count. Its degree is bounded by the number of input occurrences, its constant coefficient is q(N(0)), and its linear coefficient is the sum of one-hole slice values minus the full constant correction r·q(N(0)). This is the explicit open bridge; the module does not assert it as proved.

**Definition 1.4 (Region readout under copies).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopiesRegionLinear`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopiesRegionLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second explicit open law records the expected integer linearity of every region readout under tagged parallel copies.

**Definition 1.5 (Scalar readout of a native word).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.wordReadout`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.wordReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wordReadout extracts q from a successful native one-hole word and returns the neutral integer on failure.

**Definition 1.6 (Finite one-hole slice family).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySliceReadoutLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySliceReadoutLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CopySliceReadoutLaw is the exact finite normalization consequence needed after the polynomial bridge: every total copy expression supplies a finite family of total one-hole words whose readouts sum to the target region.

**Definition 1.7 (Joint saturation for finite word families).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySaturationLaw`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopySaturationLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CopySaturationLaw records the common low-time indistinguishability construction for any finite family of total one-hole words.

**Definition 1.8 (Positive finite diagonal copy expression).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyQExpressible`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.CopyQExpressible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A region is copy-expressible when some positive finite copy term is total on every balanced input and its diagonal q readout equals the region readout.

**Theorem 1.9 (Identification from natural evaluations).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.polynomial_identification`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.polynomial_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integer polynomial whose values at all natural numbers are n times a fixed integer is X multiplied by the constant polynomial a.

**Theorem 1.10 (Finite word sums force a uniform tail).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.sum_word_readouts_implies_tail`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.sum_word_readouts_implies_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under joint saturation, a finite sum of total one-hole word readouts cannot distinguish sufficiently early times at one position; equality of the sum and the selected-region calculation therefore forces Tail.

**Theorem 1.11 (Conditional copy necessity).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_q_expressible_implies_tail`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_q_expressible_implies_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Copy expressibility implies Tail once the finite slice-readout and joint-saturation laws are supplied.

**Theorem 1.12 (Tail supplies a one-copy expression).**

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
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.copy_q_expressible_implies_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.polynomial_identification`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.sum_word_readouts_implies_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.tail_implies_copy_q_expressible`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.value`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.wordReadout`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility](RegionFilterQExpressibility.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization](TotalCopyNormalization.md)
