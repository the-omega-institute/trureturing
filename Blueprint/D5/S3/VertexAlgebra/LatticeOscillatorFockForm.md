# LatticeOscillatorFockForm

## Abstract

Actual oscillator contravariant Hermitian form

The carrier is exactly LatticeGeneratingFieldLocality.Oscillator D: complex multivariate polynomials on Fin D.rank times all natural frequency indices. D.G is the original integral symmetric Gram matrix. No inverse, positive signature, finite occupation cutoff, or invariant-form structure is introduced. The weight of index (i,r) is r+1. The constructions apply to arbitrary finite polynomial superpositions at every frequency.

For coordinate x=(i,r), A_x is (r+1) times the actual Gram-weighted partial derivative. The existing public neutralPolynomialMode_positive and neutralPolynomialMode_negative identify A_x and multiplication by X_x with the original modes in every charge sector. The contraction is zero at unequal frequencies and is (r+1) times D.G i j at equal frequencies. Positive-positive commutation and the mixed creation/annihilation law are obtained from neutralPolynomialMode_heisenberg, without repeating its private derivative suppliers.

For finite occupation d, annihilatorProduct is the noncommutative product of its occurrence multiset mapped to the actual commuting annihilators. It is not a polynomial evaluation into a falsely commutative endomorphism ring. gramBilinear extends the functional q maps to constantCoeff(annihilatorProduct d q) from the actual monomial basis. fockForm p q equals gramBilinear(conjugatePolynomial p,q), so the left slot is conjugate-linear and the right slot is complex-linear.

The substantive finite-word proof is annihilatorEvaluation_reverse_creator: applying an arbitrary polynomial annihilator word to X_y q gives X_y times its application to q, plus the word obtained by applying the actual A_y to the first polynomial. Polynomial induction includes every repeated occupation; constants, sums and multiplication by a generator use the actual CCR. Its constant term derives the reverse-creator adjoint rather than assuming it. Integral-Gram conjugation commutes with the actual annihilators. Both creator recursions give bilinear symmetry and hence Hermitian symmetry.

Energy orthogonality uses the native weight r+1, not total polynomial degree. Substitution X_(i,r) maps to 2^(r+1) X_(i,r) intertwines each actual annihilator with the same frequency factor. The contraction vanishes when frequencies differ, which makes this substitution self-adjoint for gramBilinear. A polynomial homogeneous at native energy m is multiplied by 2^m. Distinct natural energies have distinct powers of two, forcing zero pairing. This is form orthogonality, not a reproof of conformal grading or an assumption of finite all-charge energy fibers.

Vacuum pairing equals the actual constant coefficient, so its vacuum-vacuum value is one. Extensional uniqueness holds on the original full polynomial carrier: any conjugate-left/right-linear candidate with that vacuum functional and the same actual creator-adjoint law equals the explicitly constructed form. These are comparison hypotheses in a uniqueness theorem, not fields defining the constructed form.

This is standard algebraic Heisenberg contravariance and a Lean construction on the existing carrier, with zero literature novelty claimed. The supplied Kac, Frenkel-Lepowsky-Meurman and Borcherds bibliography notes provide classical context, not an inspected locator for this exact Lean theorem. Utility is none: no bounded enumerator, numerical oracle, or certified finite example carries the result.

The form need not be nondegenerate or positive for arbitrary D.G. Inverse-Gram nondegeneracy and positivity for actual real transverse directions are separate extensions. Complex frame conjugation gives conjugate(F) G F.transpose, not F G F.transpose. Charged vertex-field/BPZ invariance, the full signed bc ghost pairing, adjointness of the actual Q, boundary-cycle orthogonality, descent to the literal original cohomology quotient, and equality with the surviving transverse form remain separate obligations. No no-ghost theorem, physical quotient isometry, full string construction, or AdS/CFT realization follows from this oscillator form alone.

**Definition 1.1 (Actual finite annihilator word).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.annihilatorProduct`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.annihilatorProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entire finite occurrence multiset is used; repeated occupations are not truncated.

**Definition 1.2 (Constructed Hermitian Fock form).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm`

*Formalization.* `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only already proved scalar linearity is packaged in its type; no symmetry, adjoint, positivity or nondegeneracy field is assumed.

**Theorem 1.3 (Vacuum functional).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_vacuum_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_vacuum_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed bind-only construction consequence used by uniqueness and the faithful Reg readout dependence proof. Normalization is its direct application, not a separately retained theorem.

**Theorem 1.4 (Original negative-mode adjoint).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_creation_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_creation_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed bind-only insertion consequence in the actual uniqueness proof; the exact original positive and negative modes occur in its statement.

**Theorem 1.5 (Hermitian symmetry).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_isSymm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_isSymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumes the full finite-word reverse creator identity and integral-Gram conjugation, not an assumed Hermitian structure.

**Theorem 1.6 (Original positive-mode adjoint).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_annihilation_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_annihilation_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The opposite adjoint is derived from the same actual finite-word CCR and real conjugation on the original polynomial carrier.

**Theorem 1.7 (Native weighted-energy orthogonality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_energy_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_energy_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Arbitrary finite polynomials homogeneous at unequal native weighted energies pair to zero; all frequencies are included.

**Theorem 1.8 (Extensional uniqueness).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_unique`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial induction determines the entire form from the original vacuum functional and actual creator adjoint on arbitrary states.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.annihilatorProduct`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_annihilation_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_creation_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_energy_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_isSymm`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_unique`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOscillatorFockForm.fockForm_vacuum_left`
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](LatticeSugawaraCurrents.md)
