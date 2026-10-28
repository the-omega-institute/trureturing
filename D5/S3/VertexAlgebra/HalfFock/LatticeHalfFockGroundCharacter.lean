/- GID: D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ground exchange implements the character on every corrected-field coefficient. -/

import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
import D5.S3.VertexAlgebra.Lattice.NormFourPeirceInvolution

/-! Ground exchange, tensor jets and finite normal sums implement the ordinary
charge character on the complete production Delta-corrected twisted field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockCorrectedField LatticeHalfFockFiniteCorrection
open LatticeHalfFockGradedTrace Lattice.NormFourPeirceInvolution
open MvPolynomial

private theorem charged_character (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Charge D) (e : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a) (chargedCoefficient D hu b e x) =
      phase D a b • chargedCoefficient D hu b e
        (actualGroundInsert D hu (groundAction D hu a) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    simp only [chargedCoefficient, actualGroundInsert, LinearMap.smul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, map_smul]
    have h := LinearMap.congr_fun
      (LatticeHalfFockGroundProducts.ground_action_exchange D hu a b) t
    change groundAction D hu a (groundAction D hu b t) =
      phase D a b • groundAction D hu b (groundAction D hu a t) at h
    rw [h, TensorProduct.tmul_smul]
    exact smul_comm _ _ _
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

private theorem ground_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (i : Index D) (j : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a) (jetCurrent D hu i j x) =
      jetCurrent D hu i j (actualGroundInsert D hu (groundAction D hu a) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    simp only [jetCurrent, actualGroundInsert, LatticeHalfFock.tensorCurrent,
      LatticeHalfFock.tensorEnd, LinearMap.smul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem flat_character (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Charge D) (w : List (Index D)) (m : ModeTuple D w)
    (e : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a)
      (flatCoefficient D hu (chargedField D hu b) w m e x) =
      phase D a b • flatCoefficient D hu (chargedField D hu b) w m e
        (actualGroundInsert D hu (groundAction D hu a) x) := by
  induction w generalizing e x with
  | nil =>
    simpa only [flatCoefficient, chargedField, HVertexOperator.coeff_of_coeff]
      using charged_character D hu a b e x
  | cons i w ih =>
    rcases m with ⟨j, m⟩
    by_cases hj : j < 0
    · simp only [flatCoefficient, if_pos hj, Module.End.mul_apply]
      rw [ground_jet, ih, map_smul]
    · simp only [flatCoefficient, if_neg hj, Module.End.mul_apply]
      rw [ih, ground_jet]

private theorem word_character (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Charge D) (w : List (Index D)) (e : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a)
      ((wordField D hu (chargedField D hu b) w).coeff e x) =
      phase D a b • (wordField D hu (chargedField D hu b) w).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x) := by
  rw [wordField_coefficient, wordField_coefficient,
    map_finsum _ (flatTerm_finite D hu (chargedField D hu b) w e x),
    smul_finsum' _ (flatTerm_finite D hu (chargedField D hu b) w e
      (actualGroundInsert D hu (groundAction D hu a) x))]
  apply finsum_congr
  intro m
  exact flat_character D hu a b w m e x

private theorem polynomial_character (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Charge D) (p : Oscillator D) (e : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a)
      ((polynomialField D hu b p).coeff e x) =
      phase D a b • (polynomialField D hu b p).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x) := by
  let left : Oscillator D →ₗ[ℂ] ActualTensor D hu :=
    { toFun p := actualGroundInsert D hu (groundAction D hu a)
        ((polynomialField D hu b p).coeff e x)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let right : Oscillator D →ₗ[ℂ] ActualTensor D hu :=
    { toFun p := phase D a b • (polynomialField D hu b p).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x)
      map_add' := by intros; simp [smul_add]
      map_smul' := by
        intro c p
        simp only [map_smul, RingHom.id_apply, Pi.smul_apply, LinearMap.smul_apply]
        exact smul_comm _ _ _ }
  have maps : left = right := by
    apply (basisMonomials (Index D) ℂ).ext
    intro d
    change actualGroundInsert D hu (groundAction D hu a)
      ((polynomialField D hu b (monomial d 1)).coeff e x) =
      phase D a b • (polynomialField D hu b (monomial d 1)).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x)
    rw [polynomialField_monomial_public]
    exact word_character D hu a b (occurrences D d) e x
  exact LinearMap.congr_fun maps p

private theorem correctedSum_character (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Charge D) (u : ℕ →₀ Oscillator D) (e : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a) ((correctedSum D hu b u).coeff e x) =
      phase D a b • (correctedSum D hu b u).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hu, hv, smul_add]
  | single s p =>
    simp only [correctedSum, Finsupp.lsum_single, LinearMap.comp_apply]
    rw [shiftField_coefficient_public]
    exact polynomial_character D hu a b p (e + 2 * (s : ℤ)) x

private theorem correctedPolynomial_character (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Charge D) (p : Oscillator D) (e : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a)
      ((correctedPolynomial D hu b p).coeff e x) =
      phase D a b • (correctedPolynomial D hu b p).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x) := by
  simp only [correctedPolynomial, LinearMap.comp_apply]
  exact correctedSum_character D hu a b (Corr D b p) e x

/-- Ground exchange implements the existing ordinary charge character on the
entire actual corrected twisted field, for all sources and integer Hahn exponents.
No norm-four, source fixedness, target parity or covariance premise is required. -/
/- proof_shape: correctedField_ground_character: content
   admission_basis: escape-witness
   escape_witness: charged_character derives the actual tensor exchange from
   ground_action_exchange, and ground_jet transports it through both branches
   of arbitrary flat normal words. Pointwise finite word sums, the original
   Corr and shifts, and all finite-charge sources consume this calculation.
   Classical lattice-character mechanism; no literature novelty is claimed. -/
theorem correctedField_ground_character (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (v : Carrier D) (e : ℤ) (x : ActualTensor D hu) :
    actualGroundInsert D hu (groundAction D hu a) ((correctedField D hu v).coeff e x) =
      (correctedField D hu (chi D a v)).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x) := by
  let left : Carrier D →ₗ[ℂ] ActualTensor D hu :=
    { toFun v := actualGroundInsert D hu (groundAction D hu a)
        ((correctedField D hu v).coeff e x)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let right : Carrier D →ₗ[ℂ] ActualTensor D hu :=
    { toFun v := (correctedField D hu (chi D a v)).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have maps : left = right := by
    apply Finsupp.lhom_ext
    intro b p
    change actualGroundInsert D hu (groundAction D hu a)
      ((correctedField D hu (Finsupp.single b p)).coeff e x) =
      (correctedField D hu (chiLinear D a (Finsupp.single b p))).coeff e
        (actualGroundInsert D hu (groundAction D hu a) x)
    rw [chi_single]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
      correctedField, Finsupp.lsum_single]
    exact correctedPolynomial_character D hu a b p e x
  exact LinearMap.congr_fun maps v

end D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockGroundCharacter
