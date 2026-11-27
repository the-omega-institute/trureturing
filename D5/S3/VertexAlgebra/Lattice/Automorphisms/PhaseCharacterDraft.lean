import D5.S3.VertexAlgebra.Lattice.IsometryLift

/-! Charge characters of the actual lattice state-field map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeActualGeneratorLocality LatticeActualProductKernel LatticeActualOrderedProducts
open MvPolynomial
open scoped VertexOperator
noncomputable section

open private ground_current_product current_field compatibleStates all_state_of_ground
  from D5.S3.VertexAlgebra.Lattice.IsometryLift
open private creation_zero from D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
open private neutral_negative_single from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

/-- Preservation of every actual integer mode. -/
def PreservesModes (D : LatticeData) (K : Carrier D ≃ₗ[ℂ] Carrier D) : Prop :=
  ∀ (a : Carrier D) (n : ℤ) (b : Carrier D),
    K (((Y D a)[[n]]) b) = ((Y D (K a))[[n]]) (K b)

private theorem mode_smul (D : LatticeData) (a b : Carrier D) (n : ℤ) (x y : ℂ) :
    ((Y D (x • a))[[n]]) (y • b) = (x * y) • ((Y D a)[[n]]) b := by
  simp only [map_smul, VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply,
    smul_smul, mul_comm x y]

private theorem epsilon_ne (D : LatticeData) (a b : Charge D) : epsilon D a b ≠ 0 := by
  intro h
  have hs : epsilon D a b * epsilon D a b = 1 := by simp [epsilon, paritySign_square]
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

private theorem leading_ground (D : LatticeData) (a b : Charge D) :
    ((Y D (Finsupp.single a 1))[[-bilinear D a b - 1]]) (Finsupp.single b 1) =
      epsilon D a b • Finsupp.single (a + b) (1 : Oscillator D) := by
  rw [stateField_ground, actual_modes, raw_ground]
  rw [show -(-bilinear D a b - 1) - 1 - bilinear D a b = 0 by omega, creation_zero]

/-- A mode-preserving lift of the identity has character phases and acts by the
same phase on every oscillator polynomial in its charge sector. -/
theorem ground_phase_classification (D : LatticeData)
    (K : Carrier D ≃ₗ[ℂ] Carrier D) (hK : PreservesModes D K)
    (eta : Charge D → ℂˣ)
    (hground : ∀ a, K (Finsupp.single a 1) = (eta a : ℂ) • Finsupp.single a 1) :
    eta 0 = 1 ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧
      ∀ a (p : Oscillator D), K (Finsupp.single a p) = (eta a : ℂ) • Finsupp.single a p := by
  classical
  have hmul (a b : Charge D) : eta (a + b) = eta a * eta b := by
    have h := hK (Finsupp.single a 1) (-bilinear D a b - 1) (Finsupp.single b 1)
    rw [leading_ground, map_smul, hground, hground, hground, mode_smul, leading_ground] at h
    rw [smul_comm (epsilon D a b)] at h
    have hg : epsilon D a b • (Finsupp.single (a+b) (1 : Oscillator D) : Carrier D) ≠ 0 :=
      smul_ne_zero (epsilon_ne D a b) (by simp)
    apply Units.ext
    apply smul_left_injective ℂ hg
    simpa only [Units.val_mul, smul_smul] using h
  have hzero : eta 0 = 1 := by
    have h := hmul 0 0
    rw [zero_add] at h
    exact mul_left_cancel (show eta 0 * eta 0 = eta 0 * 1 by simpa only [mul_one] using h.symm)
  have hcurrent (i : Fin D.rank) :
      K (Finsupp.single 0 (X (i, 0) : Oscillator D)) =
        Finsupp.single 0 (X (i, 0) : Oscillator D) := by
    let a := unitCharge D i
    have h := hK (Finsupp.single a 1) (bilinear D a a - 2) (Finsupp.single (-a) 1)
    change K (mu D (Finsupp.single a 1) (bilinear D a a - 2) (Finsupp.single (-a) 1)) =
      ((Y D (K (Finsupp.single a 1)))[[bilinear D a a - 2]]) (K (Finsupp.single (-a) 1)) at h
    rw [hground, hground, mode_smul] at h
    have hcancel : (eta a : ℂ) * (eta (-a) : ℂ) = 1 := by
      rw [← Units.val_mul, ← hmul, add_neg_cancel, hzero, Units.val_one]
    rw [hcancel, one_smul] at h
    change K (mu D (Finsupp.single a 1) (bilinear D a a - 2) (Finsupp.single (-a) 1)) =
      mu D (Finsupp.single a 1) (bilinear D a a - 2) (Finsupp.single (-a) 1) at h
    rw [ground_current_product, map_smul] at h
    have hc := smul_right_injective (Carrier D) (epsilon_ne D a (-a)) h
    simpa [a, chargePolynomial, unitCharge, apply_ite, ite_smul] using hc
  refine ⟨hzero, hmul, ?_⟩
  intro a p
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hc : Finsupp.single a (C c : Oscillator D) = c • Finsupp.single a 1 := by
      rw [show (C c : Oscillator D) = c • 1 by simp [smul_eq_C_mul] ]
      exact map_smul (Finsupp.lsingle a : Oscillator D →ₗ[ℂ] Carrier D) c 1
    rw [hc, map_smul, hground, smul_comm]
  | add p q hp hq =>
    simp only [Finsupp.single_add, map_add, hp, hq, smul_add]
  | mul_X p x hp =>
    have h := hK (Finsupp.single 0 (X (x.1, 0) : Oscillator D))
      (-(x.2 : ℤ) - 1) (Finsupp.single a p)
    rw [hcurrent, hp, current_field, neutral_negative_single, map_smul,
      neutral_negative_single] at h
    simpa only [Prod.mk.eta, mul_comm] using h

private def diagonalLinear (D : LatticeData) (eta : Charge D → ℂˣ) :
    Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun a => (eta a : ℂ) • Finsupp.lsingle a)

private theorem diagonalLinear_single (D : LatticeData) (eta : Charge D → ℂˣ)
    (a : Charge D) (p : Oscillator D) :
    diagonalLinear D eta (Finsupp.single a p) = (eta a : ℂ) • Finsupp.single a p := by
  simp [diagonalLinear]

/-- Chargewise scaling by nonzero units is an actual carrier equivalence. -/
def diagonal (D : LatticeData) (eta : Charge D → ℂˣ) : Carrier D ≃ₗ[ℂ] Carrier D where
  toLinearMap := diagonalLinear D eta
  invFun := diagonalLinear D (fun a => (eta a)⁻¹)
  left_inv := by
    have h : (diagonalLinear D (fun a => (eta a)⁻¹)).comp (diagonalLinear D eta) =
        LinearMap.id := by
      apply Finsupp.lhom_ext
      intro a p
      simp [LinearMap.comp_apply, diagonalLinear_single, smul_smul]
    exact LinearMap.congr_fun h
  right_inv := by
    have h : (diagonalLinear D eta).comp (diagonalLinear D (fun a => (eta a)⁻¹)) =
        LinearMap.id := by
      apply Finsupp.lhom_ext
      intro a p
      simp [LinearMap.comp_apply, diagonalLinear_single, smul_smul]
    exact LinearMap.congr_fun h

theorem diagonal_single (D : LatticeData) (eta : Charge D → ℂˣ)
    (a : Charge D) (p : Oscillator D) :
    diagonal D eta (Finsupp.single a p) = (eta a : ℂ) • Finsupp.single a p :=
  diagonalLinear_single D eta a p

/-- Every unit-valued lattice character acts by an actual mode-preserving
linear equivalence. -/
theorem diagonal_preserves (D : LatticeData) (eta : Charge D → ℂˣ)
    (hmul : ∀ a b, eta (a + b) = eta a * eta b) :
    PreservesModes D (diagonal D eta) := by
  let K := diagonal D eta
  have hground (a : Charge D) :
      Finsupp.single a 1 ∈ compatibleStates D K.toLinearMap := by
    intro n v
    change K (((Y D (Finsupp.single a 1))[[n]]) v) =
      ((Y D (K (Finsupp.single a 1)))[[n]]) (K v)
    rw [diagonal_single, map_smul, stateField_ground, actual_modes]
    rw [map_smul, Pi.smul_apply, LinearMap.smul_apply, actual_modes]
    have h : K.toLinearMap.comp (rawCoeff D a (-n-1)) =
        (eta a : ℂ) • (rawCoeff D a (-n-1)).comp K.toLinearMap := by
      apply Finsupp.lhom_ext
      intro b p
      change K (rawCoeff D a (-n-1) (Finsupp.single b p)) =
        (eta a : ℂ) • rawCoeff D a (-n-1) (K (Finsupp.single b p))
      rw [raw_single_convolution, map_smul, diagonal_single, diagonal_single,
        map_smul, raw_single_convolution, hmul, Units.val_mul]
      simp only [smul_smul]
      congr 1
      ring
    exact LinearMap.congr_fun h v
  exact all_state_of_ground D K.toLinearMap hground

/-- Equality on every charge sector identifies the whole finite-support map. -/
theorem eq_diagonal (D : LatticeData)
    (K : Carrier D ≃ₗ[ℂ] Carrier D) (hK : PreservesModes D K)
    (eta : Charge D → ℂˣ)
    (hground : ∀ a, K (Finsupp.single a 1) = (eta a : ℂ) • Finsupp.single a 1) :
    K = diagonal D eta := by
  have h := (ground_phase_classification D K hK eta hground).2.2
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  change K (Finsupp.single a p) = diagonal D eta (Finsupp.single a p)
  rw [h, diagonal_single]

private theorem preserving_trans (D : LatticeData)
    (U V : Carrier D ≃ₗ[ℂ] Carrier D)
    (hU : PreservesModes D U) (hV : PreservesModes D V) :
    PreservesModes D (U.trans V) := by
  intro a n b
  change V (U (((Y D a)[[n]]) b)) = ((Y D (V (U a)))[[n]]) (V (U b))
  rw [hU, hV]

private theorem preserving_symm (D : LatticeData)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hU : PreservesModes D U) :
    PreservesModes D U.symm := by
  intro a n b
  apply U.injective
  rw [U.apply_symm_apply, hU, U.apply_symm_apply, U.apply_symm_apply]

/-- An arbitrary monomial lift agrees with the canonical lift on the entire
neutral oscillator sector, even when its ground phases are arbitrary units. -/
theorem monomial_neutral (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (hU : PreservesModes D U)
    (theta : Charge D → ℂˣ)
    (hground : ∀ a, U (Finsupp.single a 1) = (theta a : ℂ) • Finsupp.single (g a) 1) :
    ∀ p : Oscillator D, U (Finsupp.single 0 p) = IsometryLift.lift D g (Finsupp.single 0 p) := by
  let L := IsometryLift.lift D g
  let K := U.trans L.symm
  let eta (a : Charge D) := theta a * (IsometryLift.phase D g a)⁻¹
  have hL : PreservesModes D L := (IsometryLift.lift_compatible D g hg).2.2.1
  have hKg (a : Charge D) : K (Finsupp.single a 1) = (eta a : ℂ) • Finsupp.single a 1 := by
    apply L.injective
    change L (L.symm (U (Finsupp.single a 1))) = L ((eta a : ℂ) • Finsupp.single a 1)
    rw [L.apply_symm_apply, hground, map_smul, IsometryLift.lift_single, map_one, smul_smul]
    simp [eta, Units.val_mul]
  have h := ground_phase_classification D K
    (preserving_trans D U L.symm hU (preserving_symm D L hL)) eta hKg
  intro p
  have hp := h.2.2 0 p
  rw [h.1, Units.val_one, one_smul] at hp
  exact L.symm_apply_eq.mp hp

/-- Conjugation by any mode-preserving monomial lift of charge negation
inverts every mode-preserving lift fixing the ground charges. -/
theorem negation_conjugates_inverse (D : LatticeData)
    (R K : Carrier D ≃ₗ[ℂ] Carrier D) (hR : PreservesModes D R) (hK : PreservesModes D K)
    (theta eta : Charge D → ℂˣ)
    (hRg : ∀ a, R (Finsupp.single a 1) = (theta a : ℂ) • Finsupp.single (-a) 1)
    (hKg : ∀ a, K (Finsupp.single a 1) = (eta a : ℂ) • Finsupp.single a 1) :
    (R.symm.trans K).trans R = K.symm := by
  let C := (R.symm.trans K).trans R
  have hCg (a : Charge D) :
      C (Finsupp.single a 1) = (eta (-a) : ℂ) • Finsupp.single a 1 := by
    have hr : R.symm (Finsupp.single a 1) =
        (((theta (-a))⁻¹ : ℂˣ) : ℂ) • Finsupp.single (-a) (1 : Oscillator D) := by
      apply R.injective
      rw [R.apply_symm_apply]
      change _ = R ((((theta (-a))⁻¹ : ℂˣ) : ℂ) • Finsupp.single (-a) 1)
      rw [map_smul, hRg, neg_neg, smul_smul]
      simp
    change R (K (R.symm (Finsupp.single a 1))) = _
    rw [hr, map_smul, hKg, map_smul, map_smul, hRg, neg_neg, smul_smul, smul_smul]
    congr 1
    rw [mul_comm (↑((theta (-a))⁻¹) : ℂ), mul_assoc]
    simp
  have hC := ground_phase_classification D C
    (preserving_trans D _ R (preserving_trans D _ K (preserving_symm D R hR) hK) hR)
      (fun a => eta (-a)) hCg
  have h := ground_phase_classification D K hK eta hKg
  have hi (a : Charge D) : eta (-a) * eta a = 1 := by
    rw [← h.2.1, neg_add_cancel, h.1]
  have he : C.toLinearMap = K.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro a p
    change C (Finsupp.single a p) = K.symm (Finsupp.single a p)
    apply K.injective
    rw [K.apply_symm_apply, hC.2.2, map_smul, h.2.2, smul_smul, ← Units.val_mul, hi]
    simp
  exact LinearEquiv.toLinearMap_injective he

end
end D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft

#print axioms D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft.ground_phase_classification
#print axioms D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft.monomial_neutral
#print axioms D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft.negation_conjugates_inverse

#print axioms D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft.diagonal_preserves
#print axioms D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft.eq_diagonal
