/- GID: D5/S3/VertexAlgebra/CorrectedInversion/Dual
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CorrectedInversion/Dual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite original-source coordinate inversion and actual functional-dual identity. -/
import D5.S3.VertexAlgebra.CorrectedInversion.Corrected
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient

/-!
# Finite original-source functional-dual inversion

The coordinate transform uses the original inverse-Gram Sugawara mode 1,
monomial source weights and finite factorial powers. Linear extension through
the existing monomial basis and charge direct sum adds coincident shifts.
K_L is the existing left functional; K_R retains the distinct original right
actualForm orientation. Only the transformed input has finite support. No
fixed-dual finite-charge support or restricted-dual representability is claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.CorrectedInversion
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField TwistedGround.ActualChargedAdjoint
open LatticeSugawaraCurrents MvPolynomial

/-- One monomial's finite family, defined with the ORIGINAL Sugawara mode 1.
The finite polynomial coefficient theorem in Corrected supplies its inversion
law. This definition uses no tensor vector, exponent, form or determinant proof. -/
def monomialInversion (D : LatticeData) (a : Charge D) (m : Index D →₀ ℕ) :
    ℤ →₀ Carrier D :=
  let R := m.weight (sourceWeight D)
  ∑ j ∈ Finset.range (R+1), Finsupp.single (shiftIndex D a R j)
    ((paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R * (j.factorial : ℂ)⁻¹) •
      ((sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1 ^ j)
        (Finsupp.single a (monomial m (1 : ℂ)))))

private def sectorInversion (D : LatticeData) (a : Charge D) :
    Oscillator D →ₗ[ℂ] (ℤ →₀ Carrier D) :=
  (basisMonomials (Index D) ℂ).constr ℂ (monomialInversion D a)

@[simp] private theorem sectorInversion_monomial (D : LatticeData) (a : Charge D)
    (m : Index D →₀ ℕ) :
    sectorInversion D a (monomial m (1 : ℂ)) = monomialInversion D a m :=
  (basisMonomials (Index D) ℂ).constr_basis ℂ (monomialInversion D a) m

/-- I(v) is obtained by linear extension through the existing monomial basis
and original finite charge direct sum. Finsupp addition merges every collision. -/
def coordinateInversion (D : LatticeData) : Carrier D →ₗ[ℂ] (ℤ →₀ Carrier D) :=
  Finsupp.lsum ℂ (sectorInversion D)

/-- Existing original left functional; no replacement pairing is chosen. -/
abbrev K_L (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) := correctedDualCoefficient D hu e x y

/- Reuse the original public coefficient evaluator as a linear map. -/

/-- The distinct original right orientation. -/
def K_R (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : Module.Dual ℂ (Carrier D) where
  toFun v := actualForm D hu x ((correctedField D hu v).coeff e y)
  map_add' v w :=
    ((actualForm D hu x).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e y).comp (correctedField D hu))).map_add v w
  map_smul' c v :=
    ((actualForm D hu x).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e y).comp (correctedField D hu))).map_smul c v

private def dualReadout (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : (ℤ →₀ Carrier D) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun d => K_R D hu (d-e) x y)

/- This helper is used by actual native sums and nilpotence as well; it is
   NOT an inverse-equivalence-only helper pending deletion. -/

set_option maxHeartbeats 4000000 in
-- Normalize the finite original-mode and scalar readout sums.
private theorem dualReadout_monomial (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m : Index D →₀ ℕ) (e : ℤ) (x y : ActualTensor D hu) :
    dualReadout D hu e x y (monomialInversion D a m) =
      K_L D hu e x y (Finsupp.single a (monomial m (1 : ℂ))) := by
  classical
  let R := m.weight (sourceWeight D)
  let delta := (SourceMobius.sectorL1 D a).toLinearMap
  let eps := paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R
  have hHG := Matrix.nonsing_inv_mul (LatticeSugawaraCurrents.gramComplex D)
    (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv (LatticeSugawaraCurrents.gramComplex D)
    (SourceMobius.gram_det_unit D hu)
  have he (j : ℕ) : shiftIndex D a R j-e =
      -e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ) := by
    dsimp [shiftIndex]
    ring
  have divided (j : ℕ) :
      actualForm D hu x ((correctedField D hu (Finsupp.single a
        ((j.factorial : ℂ)⁻¹ • ((delta^j) (monomial m (1 : ℂ)))))).coeff
          (-e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ)) y) =
      (j.factorial : ℂ)⁻¹ * K_R D hu (shiftIndex D a R j-e) x y
        (Finsupp.single a ((delta^j) (monomial m (1 : ℂ)))) := by
    rw [← he]
    change K_R D hu (shiftIndex D a R j-e) x y
      (Finsupp.single a ((j.factorial : ℂ)⁻¹ • ((delta^j) (monomial m (1 : ℂ))))) = _
    rw [← Finsupp.smul_single, map_smul, smul_eq_mul]
  calc
    _ = ∑ j ∈ Finset.range (R+1), (eps * (j.factorial : ℂ)⁻¹) *
        K_R D hu (shiftIndex D a R j-e) x y
          (Finsupp.single a ((delta^j) (monomial m (1 : ℂ)))) := by
      simp only [monomialInversion, map_sum, dualReadout, Finsupp.lsum_single,
        map_smul, SourceMobius.sugawara_pow_single D _ hHG hGH, smul_eq_mul,
        R, eps, delta]
    _ = eps * ∑ j ∈ Finset.range (R+1),
        actualForm D hu x ((correctedField D hu (Finsupp.single a
          ((j.factorial : ℂ)⁻¹ • ((delta^j) (monomial m (1 : ℂ)))))).coeff
            (-e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ)) y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [divided]
      ring
    _ = _ := by
      symm
      exact actual_corrected_monomial_inversion D hu a m e x y

set_option maxHeartbeats 4000000 in
-- Reduce the original finite charge direct sum to its monomial basis.
/-- Extension through the EXISTING basis and original finite direct sum.
This proof does not assume an all-source inversion or desired dual law. -/
private theorem actual_dual_inversion_linear (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) :
    K_L D hu e x y = (dualReadout D hu e x y).comp (coordinateInversion D) := by
  apply Finsupp.lhom_ext'
  intro a
  apply (basisMonomials (Index D) ℂ).ext
  intro m
  change K_L D hu e x y (Finsupp.single a (monomial m (1 : ℂ))) =
    dualReadout D hu e x y (coordinateInversion D (Finsupp.single a (monomial m (1 : ℂ))))
  rw [coordinateInversion, Finsupp.lsum_single, sectorInversion_monomial]
  exact (dualReadout_monomial D hu a m e x y).symm

/-- K_L(e)(v) = sum_d K_R(d-e)(I_d(v)), for every original source and signed e.
Expanding K_L/K_R gives the original actualForm/correctedField coefficient
endpoint. Only the transformed INPUT has finite support; this says nothing
about fixed-dual charge support or membership in a graded restricted dual. -/
theorem actual_dual_inversion (D : LatticeData) (hu : IsUnit D.G.det)
    (v : Carrier D) (e : ℤ) (x y : ActualTensor D hu) :
    K_L D hu e x y v = ∑ d ∈ (coordinateInversion D v).support,
      K_R D hu (d-e) x y (coordinateInversion D v d) := by
  rw [actual_dual_inversion_linear D hu e x y]
  rfl

end D5.S3.VertexAlgebra.CorrectedInversion
