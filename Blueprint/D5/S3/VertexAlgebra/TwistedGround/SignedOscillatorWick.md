# Signed Bilinear Oscillator Wick Form

## Abstract

Signed Bilinear Oscillator Wick Form

For every original integral symmetric even lattice D, define a complex bilinear factorial form F on the original MvPolynomial oscillator, using the existing occupation factorial weight. Its creation/derivative identity reuses FactorialFockMetric.mul_X_pderiv_pairing by conjugating polynomial coefficients once. No Hermitian metric or positive-definiteness premise is substituted.

At natural half-mode k use the signed matrix A_k=-(k+1/2)G. The existing OriginalCurrentMetric substitution and its inverse act on the same variables, at the same mode. W(p,q)=F(Phi(p),q). A polynomial generator chain rule and Leibniz extend the signed creation/lowering identities to arbitrary polynomials. Integer IsUnit D.G.det supplies the inverse matrix and both-sided nondegeneracy; no determinant or form symmetry is assumed as a new premise.

The actual half_annihilation_creation theorem gives the signed creation/translation transpose for every integer coefficient n, with negative indices literally zero. Expanding both input translation polynomials gives a finite double-support rectangle. Exchanging this rectangle sends c-d=e+N to d-c=-e-N, giving the same-charge coefficient reflection e to -e-2N. No infinite Hahn support is reversed and no vector-valued charged support is assumed finite.

Rank zero, empty supports, zero charges, zero vectors and indefinite lattices remain in the full quantified scope. This is classical algebraic Wick/Fock normalization with no literature novelty claim. The ground pairing and tensor charged adjoint are separate consumers. Ground symmetry, PCT, analytic completion, intertwining fields, Jacobi, fusion, Monster, string theory and AdS/CFT do not follow from this oscillator module.

Information-escape registration remains unfinished: the faithful compiled Reg mirrors currently report declared_unresolved. The source-reconstruction diagnostics and missing binding certificates are recorded at https://github.com/the-omega-institute/trureturing/issues/21134 under the repository linked-issue exception. Compilation does not assert a validated registration.

FactorialBilinear.P, FactorialBilinear.form and FactorialBilinear.monomial_left, together with modeMatrix and complex_det_unit, are available at this original owner for direct reuse by OriginalSourceCoevaluation. Their definitions and proof bodies are unchanged. The monomial formula is F(monomial alpha c,p)=weight(alpha)*c*p.coeff alpha; modeMatrix remains the negative half-frequency Gram matrix. The integer source consumer derives its retuning and actual inverse from these owners, without copying private proofs or adding a new inverse axiom.

**Definition 1.1 (wick).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complex bilinear form W on the original Oscillator D, formed from the existing factorial weight and signed same-mode Gram substitution.

**Theorem 1.2 (wick creation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by X_(i,k) transposes to -(k+1/2) times the actual Gram-weighted annihilation map. This helper is consumed by the creation/translation proof.

**Theorem 1.3 (wick lowering).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_lowering`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The converse transpose direction follows from the polynomial substitution chain rule. It is consumed by oscillator symmetry and the charged transpose induction.

**Theorem 1.4 (wick nondegenerate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both separating directions are obtained from nonzero occupation factorials and the existing invertible substitution. Integer unimodularity is the only additional hypothesis; the tensor consumer uses both directions.

**Definition 1.5 (translatedCoeff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.translatedCoeff`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.translatedCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Signed coefficients of the actual finite translation polynomial, equal to zero for negative indices.

**Theorem 1.6 (creation translation adjoint).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.creation_translation_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.creation_translation_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native half-creation coefficient transposes to the same-charge actual translation coefficient. The proof derives the lowering recurrence from the existing actual annihilation calculation and preserves all signed indices.

**Theorem 1.7 (oscillator coefficient adjoint).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.oscillator_coefficient_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.oscillator_coefficient_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer exponent e and norm N=bilinear D a a, the native oscillator coefficient at e transposes to the same charge at -e-2N. A finite rectangle of the two translation supports supplies the index exchange. This is consumed by the actual tensor adjoint.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.creation_translation_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.oscillator_coefficient_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.translatedCoeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_creation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_lowering`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick.wick_nondegenerate`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](../LatticeHalfFockChargedTensorCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/OriginalCurrentMetric](../OriginalCurrentMetric.md)
