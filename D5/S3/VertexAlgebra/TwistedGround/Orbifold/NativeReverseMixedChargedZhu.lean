/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeReverseMixedChargedZhu
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeReverseMixedChargedZhu
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The charged Zhu ground relation for actual odd-to-even current coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedChargedZhu
import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

/-!
The native charged Zhu equation is linear in the source current direction.
For a transverse current and half-oscillator input it gives commutation of
the reverse ground coefficient with the selected ground charge action.
-/

set_option autoImplicit false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeHalfFockGradedTrace LatticeHalfFockParityT
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open LatticeLightConeCoordinates (E g g_symm pairing chargeVector lin standardBasis)
open LatticeSugawaraConformal (chargePolynomial)
open MvPolynomial (X)
open private g_charge lin_single from D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private oddCurrent_grade_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private X_tmul_mem_actualGrade_one from
  D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades
open private fixedChargedZero_coefficient charged_zero_first_oscillator from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedChargedZhu

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

/-- The actual neutral odd source current in a complex lattice direction. -/
def oddCurrentVector (D : LatticeData) : E D →ₗ[ℂ] OddCarrier D :=
  (standardBasis D).constr ℂ (oddCurrent D)

theorem oddCurrentVector_eq_sum (v : E D) :
    oddCurrentVector D v = ∑ i, v i • oddCurrent D i := by
  simp only [oddCurrentVector, standardBasis, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply]

theorem oddCurrentVector_grade_one (v : E D) :
    (oddCurrentVector D v).val ∈ grade D 1 := by
  change (minusSpace D).subtype (oddCurrentVector D v) ∈ grade D 1
  rw [oddCurrentVector_eq_sum, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  exact (grade D 1).smul_mem _ (oddCurrent_grade_one D i)

private theorem lin_tmul_mem_actualGrade_one (w : E D) (t : ActualGround D hu) :
    lin 0 w ⊗ₜ[ℂ] t ∈ actualGrade D hu 1 := by
  classical
  change (∑ i, w i • (X (i, 0) : Oscillator D)) ⊗ₜ[ℂ] t ∈ actualGrade D hu 1
  simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul']
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ (w i) (X_tmul_mem_actualGrade_one D hu i t))

/-- The pure half-oscillator tensor in the literal odd twisted top, linear in both factors. -/
def oddTopHalfOscillator (D : LatticeData) (hu : IsUnit D.G.det) :
    E D →ₗ[ℂ] ActualGround D hu →ₗ[ℂ] twistedTop D hu true := by
  let insert (w : E D) := TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu) (lin 0 w)
  let lift (w : E D) : ActualGround D hu →ₗ[ℂ] twistedTop D hu true :=
    LinearMap.codRestrict _
      (LinearMap.codRestrict (paritySpace D hu (paritySign true)) (insert w) (fun t => by
        change lin 0 w ⊗ₜ[ℂ] t ∈
          LinearMap.ker (actualParity D hu - (-1 : ℂ) • LinearMap.id)
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, sub_eq_zero]
        simpa only [pow_one] using actualParity_on_actualGrade D hu 1
          ⟨_, lin_tmul_mem_actualGrade_one w t⟩))
      (fun t => lin_tmul_mem_actualGrade_one w t)
  refine { toFun := lift, map_add' := ?_, map_smul' := ?_ }
  · intro u v
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    apply Subtype.ext
    change lin 0 (u + v) ⊗ₜ[ℂ] t = lin 0 u ⊗ₜ[ℂ] t + lin 0 v ⊗ₜ[ℂ] t
    rw [map_add, TensorProduct.add_tmul]
  · intro z w
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    apply Subtype.ext
    change lin 0 (z • w) ⊗ₜ[ℂ] t = z • (lin 0 w ⊗ₜ[ℂ] t)
    rw [map_smul, TensorProduct.smul_tmul']

@[simp] theorem oddTopHalfOscillator_val (w : E D) (t : ActualGround D hu) :
    (oddTopHalfOscillator D hu w t).val.val = lin 0 w ⊗ₜ[ℂ] t := rfl

theorem oddTopHalfOscillator_basis_val (j : Fin D.rank) (t : ActualGround D hu) :
    (oddTopHalfOscillator D hu (standardBasis D j) t).val.val = X (j, 0) ⊗ₜ[ℂ] t := by
  rw [oddTopHalfOscillator_val, standardBasis, Pi.basisFun_apply, lin_single]

theorem oddTopHalfOscillator_injective (w : E D) (hw : w ≠ 0) :
    Function.Injective (oddTopHalfOscillator D hu w) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! h
    exact hw (funext h)
  let read : Oscillator D →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ (Finsupp.single (i, 0) 1)
  have hread : read (lin 0 w) = w i := by
    change read (∑ j, w j • (X (j, 0) : Oscillator D)) = w i
    rw [map_sum, Finset.sum_eq_single i]
    · simp [read]
    · intro j _ hji
      simp [read, MvPolynomial.coeff_X,
        Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), hji]
    · simp
  have hcontract (t : ActualGround D hu) :
      oddTopGroundRead read (oddTopHalfOscillator D hu w t) = w i • t := by
    change (TensorProduct.lid ℂ (ActualGround D hu))
      (TensorProduct.map read LinearMap.id (oddTopHalfOscillator D hu w t).val.val) = _
    rw [oddTopHalfOscillator_val]
    simp [hread]
  intro x y hxy
  have h := congrArg (oddTopGroundRead read) hxy
  simp only [hcontract] at h
  exact smul_right_injective (ActualGround D hu) hi h

variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

local instance reverseTopAddCommGroup (b : Bool) : AddCommGroup (twistedTop D hu b) :=
  @Submodule.addCommGroup ℂ (Twisted D hu b) _ _ _ (twistedTop D hu b)

/-- The signed charged Zhu identity for an arbitrary neutral current direction. -/
theorem chargedZhu_currentVector_commutator (F : LawfulMixedField D hu s)
    (c : Charge D) (v : E D) (u : twistedTop D hu s) :
    fixedChargedZero hD (!s) c (zhuTopEvaluation F u (oddCurrentVector D v)) -
      zhuTopEvaluation F (fixedChargedZero hD s c u) (oddCurrentVector D v) =
    (-g D v (chargeVector c)) • zhuTopEvaluation F u (oddChargedPolynomial D c 1) := by
  classical
  rw [oddCurrentVector_eq_sum, g_charge]
  simp only [map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
  calc
    _ = ∑ i, v i • ((-(bilinear D (unitCharge D i) c : ℂ)) •
        zhuTopEvaluation F u (oddChargedPolynomial D c 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [chargedZhu_current_commutator]
    _ = _ := by
      rw [← Finset.sum_neg_distrib, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul, mul_neg]

/-- The actual charged coefficient on a first oscillator tensor has the oscillator
correction `Id - 2 α ⊗ α♭` and the selected ground charge action. -/
theorem chargedCoefficient_halfOscillator (c : Charge D) (w : E D) (t : ActualGround D hu) :
    chargedCoefficient D hu c (-chargeNorm D c) (lin 0 w ⊗ₜ[ℂ] t) =
      chargeScalar D c •
        (lin 0 (w - (2 * g D (chargeVector c) w) • chargeVector c) ⊗ₜ[ℂ]
          groundAction D hu c t) := by
  let correction : E D →ₗ[ℂ] E D :=
    LinearMap.id - ((2 : ℂ) • pairing D (chargeVector c)).smulRight (chargeVector c)
  let tensorAt (x : ActualGround D hu) :=
    (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip x
  have h : (chargedCoefficient D hu c (-chargeNorm D c)).comp ((tensorAt t).comp (lin 0)) =
      chargeScalar D c • (tensorAt (groundAction D hu c t)).comp ((lin 0).comp correction) := by
    apply (standardBasis D).ext
    intro i
    have hpair : g D (chargeVector c) (standardBasis D i) =
        (bilinear D c (unitCharge D i) : ℂ) := by
      rw [g_symm D (chargeVector c), g_charge, bilinear_symmetric D c (unitCharge D i)]
      rw [Finset.sum_eq_single i]
      · simp [standardBasis]
      · intro j _ hji
        simp [standardBasis, hji]
      · simp
    have hlin : lin 0 (standardBasis D i) = (X (i, 0) : Oscillator D) := by
      rw [standardBasis, Pi.basisFun_apply, lin_single]
    change chargedCoefficient D hu c (-chargeNorm D c) (lin 0 (standardBasis D i) ⊗ₜ[ℂ] t) =
      chargeScalar D c •
        (lin 0 (standardBasis D i - (2 * g D (chargeVector c) (standardBasis D i)) •
          chargeVector c) ⊗ₜ[ℂ] groundAction D hu c t)
    rw [hpair, map_sub, map_smul, hlin]
    exact charged_zero_first_oscillator c i t
  exact LinearMap.congr_fun h w

/-- On the odd top the invariant exponential sum doubles the native charged coefficient. -/
theorem fixedChargedZero_oddTopHalfOscillator (c : Charge D) (w : E D)
    (t : ActualGround D hu) :
    fixedChargedZero hD true c (oddTopHalfOscillator D hu w t) =
      ((2 : ℂ) * chargeScalar D c) • oddTopHalfOscillator D hu
        (w - (2 * g D (chargeVector c) w) • chargeVector c) (groundAction D hu c t) := by
  apply Subtype.ext
  apply Subtype.ext
  change (fixedChargedZero hD true c (oddTopHalfOscillator D hu w t)).val.val =
    ((2 : ℂ) * chargeScalar D c) •
      (oddTopHalfOscillator D hu (w - (2 * g D (chargeVector c) w) • chargeVector c)
        (groundAction D hu c t)).val.val
  simp only [fixedChargedZero_coefficient, oddTopHalfOscillator_val,
    chargedCoefficient_halfOscillator, smul_smul]

/-- The weight-one reverse Zhu coefficient is the lawful physical half-mode with label zero. -/
private def reverseCurrentTop (F : LawfulMixedField D hu true) (v : E D) :
    twistedTop D hu true →ₗ[ℂ] twistedTop D hu false :=
  LinearMap.codRestrict _ ((F.coeff 0 (oddCurrentVector D v)).comp
    (twistedTop D hu true).subtype) (fun u => by
      change F.coeff 0 (oddCurrentVector D v) u.val ∈ twistedTop D hu false
      have h := zhuTopEvaluation_homogeneous F u 1 _ (oddCurrentVector_grade_one v)
      change (zhuTopEvaluation F u (oddCurrentVector D v)).val =
        F.coeff 0 (oddCurrentVector D v) u.val at h
      rw [← h]
      exact (zhuTopEvaluation F u (oddCurrentVector D v)).property)

private theorem reverseCurrentTop_apply (F : LawfulMixedField D hu true) (v : E D)
    (u : twistedTop D hu true) :
    reverseCurrentTop F v u = zhuTopEvaluation F u (oddCurrentVector D v) := by
  apply Subtype.ext
  exact (zhuTopEvaluation_homogeneous F u 1 _ (oddCurrentVector_grade_one v)).symm

/-- The selected lawful reverse current coefficient on a pure half-oscillator tensor,
read back on the even ground space. -/
def reverseCurrentGroundMap (F : LawfulMixedField D hu true) (v w : E D) :
    Module.End ℂ (ActualGround D hu) :=
  ((evenTopGroundEquiv D hu).symm.toLinearMap.comp (reverseCurrentTop F v)).comp
    (oddTopHalfOscillator D hu w)

theorem reverseCurrentGroundMap_apply (F : LawfulMixedField D hu true) (v w : E D)
    (t : ActualGround D hu) : reverseCurrentGroundMap F v w t =
      (evenTopGroundEquiv D hu).symm
        (zhuTopEvaluation F (oddTopHalfOscillator D hu w t) (oddCurrentVector D v)) := by
  change (evenTopGroundEquiv D hu).symm
    (reverseCurrentTop F v (oddTopHalfOscillator D hu w t)) = _
  rw [reverseCurrentTop_apply]

include hD in
/-- The reverse ground map commutes with the selected charge action when the source
direction and the input half oscillator are both perpendicular to the charge. -/
theorem chargedZhu_reverseCurrent_ground_equivariant (F : LawfulMixedField D hu true)
    (c : Charge D) (v w : E D) (hv : g D v (chargeVector c) = 0)
    (hw : g D (chargeVector c) w = 0) (t : ActualGround D hu) :
    groundAction D hu c (reverseCurrentGroundMap F v w t) =
      reverseCurrentGroundMap F v w (groundAction D hu c t) := by
  let equiv := evenTopGroundEquiv D hu
  let k := (2 : ℂ) * chargeScalar D c
  let u := oddTopHalfOscillator D hu w t
  have hin : fixedChargedZero hD true c u =
      k • oddTopHalfOscillator D hu w (groundAction D hu c t) := by
    simpa only [u, k, hw, mul_zero, zero_smul, sub_zero] using
      fixedChargedZero_oddTopHalfOscillator hD c w t
  have hout (x : twistedTop D hu false) :
      equiv.symm (fixedChargedZero hD false c x) = k • groundAction D hu c (equiv.symm x) := by
    have h := LinearMap.congr_fun (fixedChargedTopZero_conj D hu hD c) (equiv.symm x)
    change equiv.symm (fixedChargedZero hD false c (equiv (equiv.symm x))) =
      k • groundAction D hu c (equiv.symm x) at h
    rwa [LinearEquiv.apply_symm_apply] at h
  have h := chargedZhu_currentVector_commutator hD F c v u
  rw [hv, neg_zero, zero_smul, sub_eq_zero, ← reverseCurrentTop_apply F v u,
    ← reverseCurrentTop_apply F v (fixedChargedZero hD true c u)] at h
  change fixedChargedZero hD false c (reverseCurrentTop F v u) =
    reverseCurrentTop F v (fixedChargedZero hD true c u) at h
  have hground := congrArg equiv.symm h
  simp only [hout, hin, map_smul] at hground
  exact smul_right_injective (ActualGround D hu) (fixedChargedScalar_ne_zero D c) hground

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
