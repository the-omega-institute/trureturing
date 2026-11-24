/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedChargedZhu
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedChargedZhu
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The charged Zhu balance for the actual neutral odd currents. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeEvenGroundZhuCommutant
import D5.S3.VertexAlgebra.Lattice.ActualZhuGroundCurrent
import D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

/-! The singular charged-current source mode and its transverse ground readouts. -/

set_option autoImplicit false

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedMonodromy
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal (chargePolynomial)
open LatticeHalfFockChargedCoefficients
open HalfFock.NormFourLowestGrades (actualGrade_one_eq_span)
open MvPolynomial (X)
open StateFieldResidueReconstruction (integerBinomial)
open private oddCurrent_grade_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private fixedChargedVacuum_zero_current from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
open private ground_current_modes from D5.S3.VertexAlgebra.Lattice.ActualZhuGroundCurrent
open private charged_X_tail half_creation_zero half_creation_one from
  D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det}

private theorem fixedCharged_current_positive (c : Charge D) (i : Fin D.rank)
    (n : ℤ) (hn : 1 ≤ n) :
    oddMode D (fixedChargedVacuum D c) n (oddCurrent D i) = 0 := by
  have hcur : (oddCurrent D i).val = LatticeActualConformalState.currentState D i := by
    change LatticeFiniteNegativeGeneration.neutralMode D i (-1) (vacuum D) = _
    rw [← LatticeSugawaraCurrents.neutralField_ncoeff,
      LatticeActualConformalState.current_state_creation]
  apply Subtype.ext
  change mu D (Finsupp.single c 1 + Finsupp.single (-c) 1) n (oddCurrent D i).val = 0
  rw [hcur]
  simp only [mu, map_add, VertexOperator.ncoeff, Pi.add_apply, LinearMap.add_apply]
  change mu D (Finsupp.single c 1) n _ + mu D (Finsupp.single (-c) 1) n _ = 0
  rw [(ground_current_modes D c i).2.2 n hn, (ground_current_modes D (-c) i).2.2 n hn,
    add_zero]

variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

/-- The fixed charged exponential zero mode on either literal twisted top. -/
def fixedChargedZero (t : Bool) (c : Charge D) : Module.End ℂ (twistedTop D hu t) :=
  fixedTopZero t (fixedChargedVacuum D c) (chargeEnergy D c).toNat
    (by simpa only [Int.toNat_of_nonneg (chargeEnergy_nonneg D hD c)] using
      fixedChargedVacuum_grade D c)

local instance chargedTopAddCommGroup (t : Bool) : AddCommGroup (twistedTop D hu t) :=
  @Submodule.addCommGroup ℂ (Twisted D hu t) _ _ _ (twistedTop D hu t)

/-- The fixed charged action on a neutral current has exactly one singular source mode.
The two ordered top actions therefore differ by the charged odd vacuum coefficient. -/
theorem chargedZhu_current_commutator {s : Bool} (F : LawfulMixedField D hu s)
    (c : Charge D) (i : Fin D.rank) (v : twistedTop D hu s) :
    fixedChargedZero (hu := hu) hD (!s) c (zhuTopEvaluation F v (oddCurrent D i)) -
      zhuTopEvaluation F (fixedChargedZero hD s c v) (oddCurrent D i) =
    (-(bilinear D (unitCharge D i) c : ℂ)) •
      zhuTopEvaluation F v (oddChargedPolynomial D c 1) := by
  let a := fixedChargedVacuum D c
  let b := oddCurrent D i
  let d := (chargeEnergy D c).toNat
  have ha : a.val ∈ grade D (d : ℤ) := by
    simpa only [d, Int.toNat_of_nonneg (chargeEnergy_nonneg D hD c)] using
      fixedChargedVacuum_grade D c
  have hz := zhuTopEvaluation_residue F a b v d 1 ((d : ℤ)-1) 0 ha
    (oddCurrent_grade_one D i) (le_refl _) (by omega)
  rw [add_zero, ite_eq_left rfl, ite_eq_left rfl,
    StateFieldResidueReconstruction.epsilon, zpow_zero, one_smul] at hz
  have hres : oddZhuResidue a b ((d : ℤ)-1) 0 =
      (-(bilinear D (unitCharge D i) c : ℂ)) • oddChargedPolynomial D c 1 := by
    unfold oddZhuResidue
    rw [finsum_eq_single _ 0]
    · simp only [Nat.cast_zero, add_zero, integerBinomial, Ring.choose_zero_right,
        Int.cast_one, one_smul, a, b, fixedChargedVacuum_zero_current]
    · intro j hj
      rw [fixedCharged_current_positive c i (0 + (j : ℤ)) (by omega), smul_zero]
  rw [hres, map_smul] at hz
  exact hz.symm

private theorem fixedChargedZero_coefficient (t : Bool) (c : Charge D)
    (v : twistedTop D hu t) :
    (fixedChargedZero hD t c v).val.val =
      (2 : ℂ) • chargedCoefficient D hu c (-chargeNorm D c) v.val.val := by
  have hi : 2 * (-(((chargeEnergy D c).toNat : ℤ) - 1) - 1) = -chargeNorm D c := by
    rw [Int.toNat_of_nonneg (chargeEnergy_nonneg D hD c)]
    have he := two_chargeEnergy D c
    change 2 * chargeEnergy D c = chargeNorm D c at he
    omega
  have hpar : Even (-chargeNorm D c) := by
    refine ⟨-chargeEnergy D c, ?_⟩
    have he := two_chargeEnergy D c
    change 2 * chargeEnergy D c = chargeNorm D c at he
    omega
  change (correctedField D hu (Finsupp.single c 1 + Finsupp.single (-c) 1)).coeff
    (2 * (-(((chargeEnergy D c).toNat : ℤ) - 1) - 1)) v.val.val = _
  rw [hi]
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, corrected_singleton_coeff_charged,
    chargedField, HVertexOperator.coeff_of_coeff, charged_coefficient_coordinate_monodromy,
    neg_one_zpow_eq_ite, ite_eq_left hpar, one_smul, two_smul]

private theorem charged_zero_first_oscillator (c : Charge D) (j : Fin D.rank)
    (x : ActualGround D hu) :
    chargedCoefficient D hu c (-chargeNorm D c) (X (j, 0) ⊗ₜ[ℂ] x) =
      chargeScalar D c •
        ((X (j, 0) - (2 * (bilinear D c (unitCharge D j) : ℂ)) • chargePolynomial D c) ⊗ₜ[ℂ]
          groundAction D hu c x) := by
  have h : oscillatorCoefficient D c (-chargeNorm D c) (X (j, 0)) =
      X (j, 0) - (2 * (bilinear D c (unitCharge D j) : ℂ)) • chargePolynomial D c := by
    classical
    change (∑ᶠ n : ℕ, oscillatorTerm D c (-chargeNorm D c) (X (j, 0)) n) = _
    rw [finsum_eq_sum_of_support_subset _ (charged_X_tail D c j (-chargeNorm D c))]
    simp [oscillatorTerm, halfTranslatedPolynomial, halfTranslationVariable, omega,
      Polynomial.coeff_C_mul, half_creation_zero, half_creation_one, smul_smul]
    module
  simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul, h]

/-- Read a ground coefficient on the actual odd top by contracting the oscillator factor. -/
def oddTopGroundRead (read : Oscillator D →ₗ[ℂ] ℂ) :
    twistedTop D hu true →ₗ[ℂ] ActualGround D hu :=
  ((TensorProduct.lid ℂ (ActualGround D hu)).toLinearMap.comp
    (TensorProduct.map read LinearMap.id)).comp
      ((HalfFock.LatticeHalfFockParityField.paritySpace D hu (paritySign true)).subtype.comp
        (twistedTop D hu true).subtype)

private theorem oddTopGroundRead_fixedChargedZero (c : Charge D)
    (read : Oscillator D →ₗ[ℂ] ℂ) (hread : read (chargePolynomial D c) = 0)
    (v : twistedTop D hu true) :
    oddTopGroundRead read (fixedChargedZero hD true c v) =
      ((2 : ℂ) * chargeScalar D c) • groundAction D hu c (oddTopGroundRead read v) := by
  let R := (TensorProduct.lid ℂ (ActualGround D hu)).toLinearMap.comp
    (TensorProduct.map read LinearMap.id)
  let A := (2 : ℂ) • chargedCoefficient D hu c (-chargeNorm D c)
  let B := (((2 : ℂ) * chargeScalar D c) • groundAction D hu c).comp R
  have ha : actualGrade D hu 1 ≤ LinearMap.ker (R.comp A - B) := by
    rw [actualGrade_one_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, x⟩, rfl⟩
    change (X (j, 0) ⊗ₜ[ℂ] x : ActualTensor D hu) ∈ LinearMap.ker (R.comp A - B)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change R ((2 : ℂ) • chargedCoefficient D hu c (-chargeNorm D c) (X (j, 0) ⊗ₜ[ℂ] x)) =
      ((2 : ℂ) * chargeScalar D c) • groundAction D hu c (R (X (j, 0) ⊗ₜ[ℂ] x))
    rw [charged_zero_first_oscillator]
    have htmul (p : Oscillator D) (y : ActualGround D hu) :
        R (p ⊗ₜ[ℂ] y) = read p • y := by simp [R]
    simp only [map_smul, htmul, map_sub, hread, smul_zero, sub_zero, smul_smul, mul_assoc]
  have hz := ha v.property
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hz
  change R ((2 : ℂ) • chargedCoefficient D hu c (-chargeNorm D c) v.val.val) =
    ((2 : ℂ) * chargeScalar D c) • groundAction D hu c (R v.val.val) at hz
  rw [← fixedChargedZero_coefficient hD true c v] at hz
  exact hz

private theorem zhuTopEvaluation_smul_input {s : Bool} (F : LawfulMixedField D hu s)
    (v : twistedTop D hu s) (k : ℂ) (b : OddCarrier D) (h : ℤ) (hb : b.val ∈ grade D h) :
    zhuTopEvaluation F (k • v) b = k • zhuTopEvaluation F v b := by
  apply Subtype.ext
  change (zhuTopEvaluation F (k • v) b).val = k • (zhuTopEvaluation F v b).val
  rw [zhuTopEvaluation_homogeneous F _ h b hb, zhuTopEvaluation_homogeneous F _ h b hb]
  exact map_smul _ k v.val

include hD in
/-- An actual even-to-odd current coefficient commutes with the selected ground charge
operator when the source current pairs trivially with the charge and the oscillator
functional kills its creation direction. The normalization is cancelled on both sides. -/
theorem chargedZhu_current_ground_equivariant (F : LawfulMixedField D hu false)
    (c : Charge D) (i : Fin D.rank) (hi : bilinear D (unitCharge D i) c = 0)
    (read : Oscillator D →ₗ[ℂ] ℂ) (hread : read (chargePolynomial D c) = 0)
    (x : ActualGround D hu) :
    let m := fun y => oddTopGroundRead read
      (zhuTopEvaluation F ((evenTopGroundEquiv D hu) y) (oddCurrent D i))
    groundAction D hu c (m x) = m (groundAction D hu c x) := by
  let E := evenTopGroundEquiv D hu
  let k := (2 : ℂ) * chargeScalar D c
  let v := E x
  have hz := chargedZhu_current_commutator hD F c i v
  rw [hi, Int.cast_zero, neg_zero, zero_smul, sub_eq_zero] at hz
  have hr := congrArg (oddTopGroundRead read) hz
  change oddTopGroundRead read
      (fixedChargedZero hD true c (zhuTopEvaluation F v (oddCurrent D i))) =
    oddTopGroundRead read
      (zhuTopEvaluation F (fixedChargedZero hD false c v) (oddCurrent D i)) at hr
  rw [oddTopGroundRead_fixedChargedZero hD c read hread] at hr
  have he := LinearMap.congr_fun (fixedChargedTopZero_conj D hu hD c) x
  change E.symm (fixedChargedZero hD false c v) = k • groundAction D hu c x at he
  have hin := congrArg E he
  rw [LinearEquiv.apply_symm_apply] at hin
  rw [hin, map_smul E, zhuTopEvaluation_smul_input F _ k _ 1 (oddCurrent_grade_one D i),
    map_smul] at hr
  exact smul_right_injective (ActualGround D hu) (fixedChargedScalar_ne_zero D c) hr

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
