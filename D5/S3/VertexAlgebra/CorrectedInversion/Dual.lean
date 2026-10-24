/-
UNCOMPILED. Finite coordinate inversion of each original Carrier source, with
coincident integer shifts added. K_L is the existing left dual coefficient;
K_R retains the distinct right orientation of the same chosen actualForm.
No symmetry, representability, or fixed-dual finite-charge-support premise.
Source reconciliation uses native Corr734f7f and pinned SourceMobius d561416f;
it still depends on the unresolved normal STAGING boundary of NormalReadout.
No compilation or native full-inversion acceptance is asserted.
-/
import D5.S3.VertexAlgebra.CorrectedInversion.Corrected
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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
      ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j)
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

/-- Actual source coefficients and actual mode powers, with an explicit test
for coincident shifts. No injectivity of shifts, charges or monomial lists. -/
theorem coordinateInversion_coeff (D : LatticeData) (v : Carrier D) (d : ℤ) :
    coordinateInversion D v d =
      ∑ a ∈ v.support, ∑ m ∈ (v a).support, (v a).coeff m •
        ∑ j ∈ Finset.range (m.weight (sourceWeight D)+1),
          if shiftIndex D a (m.weight (sourceWeight D)) j = d then
            (paritySign (chargeNorm D a / 2) * (-1 : ℂ)^(m.weight (sourceWeight D)) *
              (j.factorial : ℂ)⁻¹) •
              ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j)
                (Finsupp.single a (monomial m (1 : ℂ))))
          else 0 := by
  classical
  have expand (a : Charge D) : sectorInversion D a (v a) =
      ∑ m ∈ (v a).support, (v a).coeff m • monomialInversion D a m := by
    have hp : v a = ∑ m ∈ (v a).support, (v a).coeff m • monomial m (1 : ℂ) := by
      simpa only [smul_monomial, smul_eq_mul, mul_one] using (v a).as_sum
    conv_lhs => rw [hp]
    simp only [map_sum, map_smul, sectorInversion_monomial]
  simp only [coordinateInversion, Finsupp.lsum_apply, Finsupp.sum,
    Finsupp.finsetSum_apply]
  simp_rw [expand]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, monomialInversion,
    Finsupp.single_apply]

/-- Finite source/monomial/jet support envelope, permitting cancellation. -/
def inversionWindow (D : LatticeData) (v : Carrier D) : Finset ℤ := by
  classical
  exact v.support.biUnion (fun a => (v a).support.biUnion (fun m =>
    (Finset.range (m.weight (sourceWeight D)+1)).image
      (shiftIndex D a (m.weight (sourceWeight D)))))

theorem coordinateInversion_support (D : LatticeData) (v : Carrier D) :
    (coordinateInversion D v).support ⊆ inversionWindow D v := by
  classical
  intro d hd
  by_contra outside
  apply (Finsupp.mem_support_iff.mp hd)
  rw [coordinateInversion_coeff]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro m hm
  have hz : (∑ j ∈ Finset.range (m.weight (sourceWeight D)+1),
      if shiftIndex D a (m.weight (sourceWeight D)) j = d then
        (paritySign (chargeNorm D a / 2) * (-1 : ℂ)^(m.weight (sourceWeight D)) *
          (j.factorial : ℂ)⁻¹) •
          ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j)
            (Finsupp.single a (monomial m (1 : ℂ)))) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have ne : shiftIndex D a (m.weight (sourceWeight D)) j ≠ d := by
      intro eq
      apply outside
      exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_biUnion.mpr
        ⟨m,hm,Finset.mem_image.mpr ⟨j,hj,eq⟩⟩⟩
    simp only [if_neg ne]
  rw [hz, smul_zero]

/-- Existing original left functional; no replacement pairing is chosen. -/
abbrev K_L (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) := correctedDualCoefficient D hu e x y

/- Immutable native coefficient evaluator, reused as a linear map rather than
   assuming that Hahn coefficient extraction reduces to Pi application. -/
local macro "originalFieldCoefficientAt" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.coefficientAt))

/-- The distinct original right orientation. -/
def K_R (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : Module.Dual ℂ (Carrier D) where
  toFun v := actualForm D hu x ((correctedField D hu v).coeff e y)
  map_add' v w :=
    ((actualForm D hu x).comp
      ((originalFieldCoefficientAt D hu e y).comp (correctedField D hu))).map_add v w
  map_smul' c v :=
    ((actualForm D hu x).comp
      ((originalFieldCoefficientAt D hu e y).comp (correctedField D hu))).map_smul c v

private def dualReadout (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : (ℤ →₀ Carrier D) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun d => K_R D hu (d-e) x y)

/- This helper is used by actual native sums and nilpotence as well; it is
   NOT an inverse-equivalence-only helper pending deletion. -/
local macro "existingGramDetUnit" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier 0) ++
    `D5.S3.VertexAlgebra.SourceMobius.gram_det_unit))

private theorem dualReadout_monomial (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m : Index D →₀ ℕ) (e : ℤ) (x y : ActualTensor D hu) :
    dualReadout D hu e x y (monomialInversion D a m) =
      K_L D hu e x y (Finsupp.single a (monomial m (1 : ℂ))) := by
  classical
  let R := m.weight (sourceWeight D)
  let delta := (SourceMobius.sectorL1 D a).toLinearMap
  let eps := paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R
  have hHG := Matrix.nonsing_inv_mul (gramComplex D) (existingGramDetUnit D hu)
  have hGH := Matrix.mul_nonsing_inv (gramComplex D) (existingGramDetUnit D hu)
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
