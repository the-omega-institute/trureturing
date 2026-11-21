# The smallest affine independent-bit representation

## Abstract

The fair subgroup and the active quotient biases give the exact minimum number of input bits.

**Theorem 1.1 (The nonzero moments determine the fair subgroup).**

Lean statement: `D5/S3/TotalVariation/MinimumParityInputs.fairSpan_eq_spectralAnnihilator`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/MinimumParityInputs.fairSpan_eq_spectralAnnihilator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite additive commutative group in which every element added to itself is zero, take any finite family of input columns, an affine offset, and real bias factors. The subgroup spanned by the columns with zero bias equals the subgroup of elements on which every character with a nonzero output moment takes value one. The characters trivial on the fair subgroup descend to the quotient. For each nonzero quotient element, some quotient character distinguishes that element from zero.

**Theorem 1.2 (The signs determine the adjusted offset on the quotient).**

Lean statement: `D5/S3/TotalVariation/MinimumParityInputs.adjusted_offset_coset_exact`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/MinimumParityInputs.adjusted_offset_coset_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite additive commutative group in which every element added to itself is zero, let a real mass function satisfy the quotient criterion for subgroup H and offset s. An offset t makes every nonzero moment positive after multiplication by the corresponding character value at t exactly when t minus s belongs to H. Every surviving character descends to the quotient, where the criterion makes its adjusted moment positive. Its sign is constant on the offset coset.

**Theorem 1.3 (The quotient moments recover every absolute grouped bias).**

Lean statement: `D5/S3/TotalVariation/MinimumParityInputs.visibleBias_recovered`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/MinimumParityInputs.visibleBias_recovered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take an affine output on a finite additive commutative group in which every element added to itself is zero. For any nonzero column of the quotient by the fair subgroup, invert the logarithms of the absolute moments of the pullback characters. The resulting bias equals the absolute product of the input bias factors whose columns project to that quotient column. Every fair input projects to zero, so the quotient moments used here are nonzero.

**Theorem 1.4 (The fair dimension and the active quotient columns give the minimum).**

Lean statement: `D5/S3/TotalVariation/MinimumParityInputs.minimum_input_count_exact`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/MinimumParityInputs.minimum_input_count_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the output space be a finite module over the binary field. Let the real mass function have total mass one and satisfy the quotient criterion for some subgroup and offset. Write H for its spectral annihilator. The number of inputs in every finite affine representation is at least the dimension of H plus the number of nonzero quotient columns whose recovered bias is strictly less than one.

There exists a representation with all input biases in the closed interval from -1 to 1, the same mass at every output point, and exactly this many inputs. Fair columns must span H. Distinct active quotient columns require distinct additional inputs. Choose a basis for the fair columns and lift each active quotient column once using its recovered bias to obtain equality.

## References

- Truth anchor: `D5/S3/TotalVariation/MinimumParityInputs.adjusted_offset_coset_exact`
- Truth anchor: `D5/S3/TotalVariation/MinimumParityInputs.fairSpan_eq_spectralAnnihilator`
- Truth anchor: `D5/S3/TotalVariation/MinimumParityInputs.minimum_input_count_exact`
- Truth anchor: `D5/S3/TotalVariation/MinimumParityInputs.visibleBias_recovered`
- Dependency: [D5/S3/TotalVariation/QuotientParitySpectrum](QuotientParitySpectrum.md)
