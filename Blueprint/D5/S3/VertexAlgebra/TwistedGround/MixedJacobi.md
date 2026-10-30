# Finite actual mixed coefficient transport and the Leech vacuum channel

## Abstract

Finite actual mixed coefficient transport and the Leech vacuum channel

The original Carrier, ActualTensor, correctedField, tensor stress L1, rank/16 intercept and selected actualForm are retained. The finite transport statements do not identify the fixed restricted dual with the original fixed source. All bilinear pairings retain their original ordered slots.

For finite Mobius transport, the input cutoff exceeds its maximum supported odd weight. The common rectangle cutoff also exceeds the maximum supported odd weight of each corrected-field output on those finitely many lowered inputs. Input nilpotence kills the omitted columns; actual output nilpotence kills the remaining omitted rows. The map (i,j) to (n=i+j,i), with inverse (n,i) to (i,n-i), is used only on that bounded rectangle.

The diagonal sum uses ActualMobiusAllOrder.corrected_field_mobius_coefficient. The one-sided lowering formula follows by splitting left multiplication by target L1 into its adjoint action and commuting right multiplication, then applying the existing homogeneous divided-adjoint formula. Its indices satisfy i <= q and ell <= q-i. Original corrected-field inversion extends linearly over an entire source grade, using actual original-source nilpotence. Applying this inversion after one-sided lowering gives the stated lowering-transpose formula without assuming symmetry of the selected form.

For signed ordered-product transport, let o be the Hahn order of the rightmost actual field on its actual input. The cutoff R=(e-o).toNat+1 ensures that its exponent e-2k is below o for every k >= R. Hence the ordered product is zero beyond R before reindexing. The literal triangular map is (j,h) to (k=j+h,j), with inverse (k,j) to (j,k-j). Binomial reflection and Vandermonde then give the signed diagonal weight. Negative binomial parameters do not provide the finiteness argument; actual field support does.

The vacuum-channel construction uses RealLeech.exists_positive_even_unimodular_gram, retaining the integral charge equivalence with the actual Golay real lattice and its original pairing. A single lowest half-oscillator on an actual ground basis vector has negative parity and conformal weight two. Nondegeneracy of the unchanged form supplies a detecting vector, and odd-grade orthogonality supplies a detecting basis vector of the same weight. Evaluating the normalized coefficient on the actual vacuum gives B(v,u) at standard mode I_3, and this value is nonzero. Neither a positive form nor a symmetry premise is used.

These are repository Lean finite coefficient derivations using the existing covariance, inversion, nondegeneracy and actual Golay lattice suppliers. FLM's PNAS announcement supplies the carrier conventions recorded with MixedIntertwiner; it is not attributed a detailed proof of these formulas. The full signed all-source mixed Jacobi identity still requires the finite source-law substitution and the uniform transformed-input support bounds and both signed triangular branch identifications. The first dual-action branch is evaluated explicitly on its actual target grade by mixed_first_branch_pairing. Three-twisted crossing and identification of the restricted dual with the original fixed source are separate obligations.

**Theorem 1.1 (Finite evaluation of original all-order Mobius covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.finite_mobius_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.finite_mobius_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two independently finite target-power sums equal a finite sum of the original all-order source-coordinate readouts on every original source and actual tensor input.

**Theorem 1.2 (Actual one-sided lowering followed by homogeneous source inversion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.lowered_field_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.lowered_field_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pairing of a divided target L1 power applied after an original field coefficient becomes a finite triangle of lowered inputs and a finite original-source inversion sum. Every signed raw exponent and every homogeneous source grade is included.

**Theorem 1.3 (Signed triangular transport with actual ordered-product support).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.ordered_signed_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.ordered_signed_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual Hahn-order cutoff makes the rectangular signed binomial convolution finite before its diagonal reindexing. The rightmost field action supplies the zero terms required by Vandermonde.

**Theorem 1.4 (Finite original-source iterate expansion of the dual-action branch).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_first_branch_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_first_branch_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary signed m, n and r, the complete first dual-action sum paired with an actual fixed target-grade vector equals a finite sum of normalized kernels on original opposite-source iterates. Sharp homogeneous truncation bounds the outer index, and the original source monomial bound limits source L1. The two target lowering sums remain finite at their actual homogeneous energy bounds.

**Theorem 1.5 (Actual second-input action expanded by lowering and transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_second_input_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_second_input_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A signed fixed-source mode acts on the actual second twisted input, with its signed output energy represented by the stated nonnegative integer W. This energy follows from original zero-mode covariance. Evaluating the resulting normalized coefficient on every fixed-grade test vector gives finite target lowering triangles and the finite original-source inversion sum, with the original ordered bilinear form.

**Theorem 1.6 (Actual first-input action expanded by one-sided lowering).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_first_input_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_first_input_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A signed fixed-source mode acts on the actual first twisted input, with its signed output energy represented by the stated nonnegative integer W. The normalized coefficient on every fixed-grade test vector expands over the complete finite triangle of source L1 powers and lowered actual inputs. Actual covariance supplies the transformed energy; no mixed iterate identity is a hypothesis.

**Theorem 1.7 (Nonzero actual Leech weight-two vacuum channel at I_3).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.actual_leech_vacuum_channel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.actual_leech_vacuum_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Golay Leech lattice has two actual negative-parity weight-two twisted vectors whose normalized I_3 coefficient evaluates on the original vacuum as the nonzero original ordered pairing B(v,u).

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.actual_leech_vacuum_channel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.finite_mobius_transport`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.lowered_field_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_first_branch_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_first_input_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.mixed_second_input_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.ordered_signed_transport`
- Dependency: [D5/S3/Arith/Lattices/Golay/RealLeech](../../Arith/Lattices/Golay/RealLeech.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder](../HalfFock/ActualMobiusAllOrder.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedOpposite](MixedOpposite.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedTranslation](MixedTranslation.md)
