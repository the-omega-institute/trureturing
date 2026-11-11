# Rational energy of the actual signed compressed modes

## Abstract

Actual compressed signed modes preserve the intrinsic rational energy with the Schur shift.

D is the original LatticeData, e is an arbitrary natural external rank, B : Matrix (Fin D.rank) (Fin e) Int is arbitrary, and C : Matrix (Fin e) (Fin e) Int has the explicit proofs hC : forall i j, C i j = C j i and hCe : forall i, Even (C i i). Both ranks may be zero. The sole positivity assumption in the theorem is hD : (gramReal D).PosDef on the ORIGINAL Gram form. The ambient block E = ambient D e B C hC hCe may be indefinite or degenerate. Its combinatorial energy and literal all-state field are used without an ambient inverse or a conformal-operator premise.

**Definition 1.1 (moduleShift).**

Lean statement: `D5/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy.moduleShift`

*Formalization.* `D5/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy.moduleShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public definition moduleShift D B a, for every a : Fin e -> Int, is the rational vector Matrix.mulVec (longitudinal D B) (fun j => (a j : Rat)). Write P for this original inverse-Gram cross block, so the shift is P*a. The definition itself has no hD, C or ambient-positivity argument. Write S(a,b) = schur D B C a b for the FULL rational Schur form C - B-transpose * G-inverse * B, and sigma(a) = S(a,a)/2. G[a](h) below means rationalGrade D (moduleShift D B a) h, the existing coefficient grade, not a newly postulated grading.

**Theorem 1.2 (actual_compressed_mode_grade).**

Lean statement: `D5/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy.actual_compressed_mode_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy.actual_compressed_mode_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,e,B,C,hC,hCe as above, every hD, every a,b : Fin e -> Int, every hu,hv : Rat, every u,v : Carrier D, every SIGNED m : Int, and proofs hU : u in G[a](hu) and hV : v in G[b](hv), compressed D B C hC hCe a b u m v belongs to G[a+b](hu + hv - (m : Rat) - 1 - S(a,b)). These are all the theorem's hypotheses. The states are arbitrary original carrier states subject only to their displayed homogeneous-grade membership, with arbitrary finite charge sums and oscillator polynomials. The Schur correction is unreduced and includes C. No comparison between different C at a fixed integer mode is asserted.

The proof first computes the actual charge-energy shift. The private gram_longitudinal supplier from Sectors/LatticeCosetCompression proves G*(P*a)=B*a under hD. The consumed shift_dual and charge_shift then give chargeEnergy E (liftCharge a n) = chargeWeight D (P*a) n + sigma(a). The calculation expands both block cross terms and contracts the original inverse-Gram term; it does not assume positivity or invertibility of E. The private schur_swap from Sectors/LatticeCosetChargedJacobi is used only for symmetry in sigma_add, yielding sigma(a+b)=sigma(a)+sigma(b)+S(a,b). charged_borcherds is not invoked.

The actual injection and projection are checked on the FULL monomial basis, then transferred through coefficient spans. The exact suppliers are private injection_single and projection_single from Sectors/LatticeCosetCompression, private coefficientGrade and coefficient_mem from Sectors/LatticeDualCosetGrading, and CompressedOccupationSewing.injection_basis and oldOccupation_level from Sewing/CompressedOccupation. Injection sends G[a](h) into the ambient combinatorial grade h+sigma(a). Projection filters the external charge and sends ambient grade h into G[a](h-sigma(a)); reconstruct_charge handles the retained charge. For its oscillator support, projection_eq_linearSub and projectionMatrix identify polynomialProjection with LongitudinalFockTranspose.transposeSub Qstar, where Qstar j i = star (Q i j). LongitudinalFockTranspose.transpose_monomial_energy supplies equality of oscillator energy at each nonzero coefficient. This uses the CONJUGATE TRANSPOSE substitution and no assumed adjoint identity.

The ambient_mode_grade helper applies Energy/LatticeCoefficientEnergy.actual_mode_grade on basis states and uses span induction in both arguments to pass to rational coefficient grades: Y(E,u)[m]v has grade h+k-m-1. Applying this to the two actual injections, and then applying projection_grade in sector a+b, gives hu+sigma(a)+hv+sigma(b)-m-1-sigma(a+b). sigma_add reduces that expression to the public theorem's full Schur shift. The existing LatticeDualCosetEnergy.moduleL_eigen_iff is an interpretation supplier for rationalGrade as the original-omega eigenspace when its duality premise is supplied by shift_dual; the present proof does not add an eigen-identification wrapper.

Actual consumer: Sectors/LatticeCosetScalarNumerator.product_grade applies this theorem twice to the nested productCoefficient JP, first in sectors b,c and then in a,b+c. Schur additivity gives the output grade hu+hv+hw-m-n-S(a,b)-S(a,c)-S(b,c)-2. That grade is used in numerator_grade and in the restricted-dual scalar support argument. Thus the injection/projection support calculation supplies a consumed mathematical fact, rather than a renamed binding.

The actual original proof source is preserved from import to EOF, with supplied export SHA256 06bff7ca57e6a16b2380849110c31102a078d4ae273a65d66e6695c84d91e910. Imported suppliers retain their attribution; no literature novelty is asserted. The source-bound escape audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/29386. No validated registration is claimed.

Scope and interpretation limits: the original injection, projection, fields and half-diagonal cocycle remain unchanged. This signed grading theorem is a necessary algebraic increment. It does not establish ambient positivity, fixed-integer-mode C-independence, analytic sewing, a fusion category, spacetime dynamics, string theory or AdS/CFT completion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy.actual_compressed_mode_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy.moduleShift`
- Dependency: [D5/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy](LatticeCoefficientEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetChargedJacobi](../Sectors/LatticeCosetChargedJacobi.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetGrading](../Sectors/LatticeDualCosetGrading.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CompressedOccupation](../Sewing/CompressedOccupation.md)
