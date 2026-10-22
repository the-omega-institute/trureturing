# Native Fock Normal Fields

## Abstract

Statewise finite physical current-jet insertion on the actual native tensor module.

The carrier is the existing ActualTensor D hu with hu : IsUnit D.G.det. A source oscillator (i,k) inserts the physical divided jet with coefficient binomial(-j-3/2,k) and cover exponent -2j-2k-3. Negative j acts on the left and nonnegative j on the right, independently of jet order. In particular j=-1 remains a creation mode. Ordinary cover normalMinusOne is not used.

**Theorem 1.1 (The left creation convolution is finite on each vector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.negativeTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.negativeTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

For a fixed exponent, increasing the negative-mode creation index decreases the tail-field coefficient exponent. Its actual Hahn order gives a finite index bound before any finsum distribution is used.

**Theorem 1.2 (The right annihilation convolution is finite on each vector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.positiveTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.positiveTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The released tensor_current_truncation supplies a finite cutoff for the original vector. No support condition on an End-valued infinite family is assumed. The actual tensor current and the actual existing tail field are used.

**Theorem 1.3 (Finite intermediate orders give lower truncation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalCoefficient_lower_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalCoefficient_lower_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The creation part uses the tail field order minus the source jet shift. The annihilation part uses the minimum of finitely many actual tail-field orders after the right current acts. This lower bound proves each convolution term vanishes below it and is consumed directly by HVertexOperator.of_coeff. Additivity and scalar linearity use the preceding finite-support proofs.

**Theorem 1.4 (The existing zero-charge tensor field is the identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.charged_zero_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.charged_zero_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

At zero charge the creation series is zero, the existing translated polynomial is constant, and the genuine ground representation acts by its unit. The actual charged coefficient is the identity at exponent zero and zero elsewhere, first on pure tensors and then by tensor induction. No alternate charged map is defined.

**Theorem 1.5 (The unit polynomial selects the existing charged field).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

This consumed monomial-basis evaluation is used by charged-state recovery and carries no new mathematical-content credit.

**Theorem 1.6 (A source variable selects its actual physical current insertion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The single-occurrence basis evaluation is consumed by current recovery, with insertion order k and exponent -2j-2k-3. It is a proof-organization lemma, not new mathematical content.

**Theorem 1.7 (Zero physical shift preserves a native field).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.shiftLinear_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.shiftLinear_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The coefficient equality is consumed by generator recovery and has no new-content credit.

**Theorem 1.8 (Insertion into the identity recovers the native tensor current).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalInsertion_identity_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalInsertion_identity_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The order-zero physical jet has scalar coefficient one. Each odd cover exponent selects exactly one negative or nonnegative underlying current mode in the already finite convolution; even cover exponents select none. The recovered field is the existing tensorCurrentField, including the creation mode j=-1.

**Theorem 1.9 (The original target cutoff bounds every unfiltered tuple).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

ModeTuple labels occurrences by their positions, retaining repeated variables. flatCoefficient uses every integer tuple, without filtering: all negative jet currents act left of the one existing charged coefficient and all nonnegative currents act right. Same-sign native current commutation preserves the ORIGINAL target annihilation cutoff R after every right derivative. A nonzero term therefore has every j<R. Replacing negative indices by -1 leaves the right action unchanged, so its states come from the finite box [-1,R]. Let L be the minimum of zero and the actual base-field orders on these right-derivative states, n the word length and W=sum(2k+3). A nonzero term has e+2sum(j)+W>=L; with M=min(L-e-W,0), every mode lies in [M-nR,R]. The bound is on individual full products, not a cancellation-raised intermediate tail-field order.

**Theorem 1.10 (Every native state has finite unfiltered tuple support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

On a pure polynomial tensor ground state the cutoff is exactly the original polynomial vars.sup(k+1), using current_vanish. Tensor induction extends finite support to every algebraic tensor; sums use coefficient linearity and finite support of the two original families. No signature, norm sign, occupation or source-word restriction is imposed.

**Theorem 1.11 (The term is the exact full Fock-normal product).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The recursive tuple operator equals leftAction times the original field coefficient at e+2sum(j)+sum(2k+3) times rightAction. Each actual jet factor is jetScalar(k,j) times the existing native tensorCurrent(i,j). This consumed normalization identifies the native charged middle without defining a second charged map.

**Theorem 1.12 (Pointwise finite sums equal the existing nested insertions).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalSequence_flattened`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalSequence_flattened` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

After full tuple support is proved, finsum_curry and finite-support map_finsum identify the unfiltered sum with normalInsertion recursion. Integer modes split bijectively into -(r+1) and r, exactly the two existing single-insertion sums. No End-valued infinite sum is used.

**Theorem 1.13 (Actual same-sign jet currents commute).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.jetCurrent_same_sign`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.jetCurrent_same_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The native Heisenberg commutator has no contraction when both modes are negative or both nonnegative. Pure-tensor lifting and scalar linearity prove the exact jet identity; no oscillator law is assumed.

**Theorem 1.14 (Fock-normal insertions commute on every native field).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalInsertion_commute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalInsertion_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The finite flattened two-occurrence sum is reindexed by exchanging its two labelled mode coordinates. Two negative factors commute on the left, two nonnegative factors commute on the right, and opposite signs act on different sides of the middle coefficient. This is not an asserted field locality or Jacobi law.

**Theorem 1.15 (Repeated-occurrence enumeration is immaterial).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalWord_perm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalWord_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

List.Perm induction uses the actual commuting insertion theorem, including arbitrary repeated labels and the empty word. The result is consumed by normalPolynomial_monomial_enumeration and the polynomial expansion of the actual corrected Ytw.

**Theorem 1.16 (The existing charged word has its full native expansion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalWord_flattened`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalWord_flattened` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

The general sequence theorem is applied to the existing chargedField and consumed by Ytw_fock_normal_coefficients. This is an organizational application, not separately claimed new mathematics.

**Theorem 1.17 (Arbitrary polynomial coefficients consume enumeration independence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_enumerated_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_enumerated_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

Each supported monomial may use any permutation of its occurrence list. Monomial-basis linear extension gives the exact finite expansion with the original complex coefficients, consumed directly inside correctedPolynomial/Ytw rather than defining an alternate assignment.

The construction adapts the finite-support normal-product architecture attributed to Scott Carnahan and the classical twisted lattice construction. Full twisted Jacobi, physical translation, sectorTranslation recurrences, ground monodromy and inverse-Gram stress equality remain separate obligations. Compilation and source-admission registrations are distinct; Reg obligation aliases do not constitute completed four-slot registrations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.charged_zero_identity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatCoefficient_factorization`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.flatTerm_support_bound`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.jetCurrent_same_sign`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.negativeTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalCoefficient_lower_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalInsertion_commute`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalInsertion_identity_current`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_X`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_enumerated_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalPolynomial_one`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalSequence_flattened`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalWord_flattened`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.normalWord_perm`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.positiveTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.shiftLinear_zero`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
