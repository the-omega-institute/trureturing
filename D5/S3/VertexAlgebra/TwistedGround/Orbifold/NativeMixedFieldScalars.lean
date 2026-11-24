/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedFieldScalars
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedFieldScalars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar closure, native current normalization, and real transverse Leech directions. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeEvenGroundZhuCommutant
import D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Scalar multiplication preserves the actual mixed Borcherds law.
The native creation and return coefficients fix the field normalization,
and real positive definiteness gives a transverse direction for each charge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeHalfFock (current tensorCurrent tensorEnd)
open LatticeHalfFockChargedTensorCoefficients
open LatticeLightConeCoordinates (g chargeVector)
open LatticeRealNullFrame (E_R B_R g_R g_R_apply realCharge complexify
  complexify_charge complexify_gram finrank_E_R)
open MvPolynomial (X)

open private J_current oddCurrent_grade_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

private theorem mixedBorcherds_scale (z : ℂ) (F : LawfulMixedField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : Twisted D hu s) (p q r : ℤ) :
    mixedBorcherds D hu s (z • F.coeff) a b v p q r := by
  have h := F.borcherds a b v p q r
  dsimp only [mixedBorcherds] at h ⊢
  obtain ⟨hl, hf, hs, hsum⟩ := h
  have move (k : ℂ) (w : Twisted D hu (!s)) : k • z • w = z • k • w :=
    smul_comm k z w
  simp only [Pi.smul_apply, LinearMap.smul_apply, map_smul, move]
  refine ⟨hl.subset (Function.support_smul_subset_right (fun _ => z) _),
    hf.subset (Function.support_smul_subset_right (fun _ => z) _),
    hs.subset (Function.support_smul_subset_right (fun _ => z) _), ?_⟩
  simpa only [smul_finsum, smul_sub] using
    congrArg (fun w : Twisted D hu (!s) => z • w) hsum

/-- Scalar multiplication preserves lower truncation, translation and the full mixed Jacobi law. -/
def LawfulMixedField.scale (z : ℂ) (F : LawfulMixedField D hu s) :
    LawfulMixedField D hu s where
  coeff := z • F.coeff
  truncation b v := by
    obtain ⟨N, hN⟩ := F.truncation b v
    refine ⟨N, fun n hn => ?_⟩
    change z • F.coeff n b v = 0
    rw [hN n hn, smul_zero]
  derivative b v n := by
    change z • F.coeff n (oddTranslation D b) v =
      (-((n : ℂ) + 1/2)) • (z • F.coeff (n-1) b v)
    rw [F.derivative]
    exact smul_comm z (-((n : ℂ) + 1/2)) _
  borcherds := mixedBorcherds_scale z F

/-- Scaling a lawful field scales its selected homogeneous Zhu coefficient. -/
theorem zhuTopEvaluation_scale_homogeneous (z : ℂ) (F : LawfulMixedField D hu s)
    (v : twistedTop D hu s) (h : ℤ) (b : OddCarrier D) (hb : b.val ∈ grade D h) :
    zhuTopEvaluation (F.scale z) v b = z • zhuTopEvaluation F v b := by
  apply Subtype.ext
  rw [Submodule.coe_smul, zhuTopEvaluation_homogeneous _ _ h b hb,
    zhuTopEvaluation_homogeneous _ _ h b hb] <;> rfl

theorem zhuTopEvaluation_scale_current (z : ℂ) (F : LawfulMixedField D hu s)
    (v : twistedTop D hu s) (i : Fin D.rank) :
    zhuTopEvaluation (F.scale z) v (oddCurrent D i) =
      z • zhuTopEvaluation F v (oddCurrent D i) :=
  zhuTopEvaluation_scale_homogeneous z F v 1 _ (oddCurrent_grade_one D i)

/-- The native forward Zhu coefficient creates the actual first oscillator tensor. -/
theorem nativeCurrentEven_tensor (i : Fin D.rank) (x : ActualGround D hu) :
    (zhuTopEvaluation (nativeMixedField D hu false)
      (evenTopGroundEquiv D hu x) (oddCurrent D i)).val.val =
        (X (i, 0) : Oscillator D) ⊗ₜ[ℂ] x := by
  have h := zhuTopEvaluation_homogeneous (nativeMixedField D hu false)
    (evenTopGroundEquiv D hu x) 1 _ (oddCurrent_grade_one D i)
  change (zhuTopEvaluation (nativeMixedField D hu false)
    (evenTopGroundEquiv D hu x) (oddCurrent D i)).val =
      J D hu false (-1) (oddCurrent D i) (evenTopGroundEquiv D hu x).val at h
  rw [h, J_current, evenTopGroundEquiv_val]
  have hcreate : current D i (-1) 1 = (X (i, 0) : Oscillator D) := by
    norm_num [current, LinearMap.mulLeft_apply]
  simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply, hcreate]

/-- On a created first oscillator the native reverse Zhu coefficient returns half the Gram pairing. -/
theorem nativeCurrent_gram_return (i j : Fin D.rank) (x : ActualGround D hu) :
    zhuTopEvaluation (nativeMixedField D hu true)
      (zhuTopEvaluation (nativeMixedField D hu false)
        (evenTopGroundEquiv D hu x) (oddCurrent D j))
      (oddCurrent D i) = ((D.G i j : ℂ) / 2) • evenTopGroundEquiv D hu x := by
  apply Subtype.ext
  rw [Submodule.coe_smul, zhuTopEvaluation_homogeneous _ _ 1 _ (oddCurrent_grade_one D i),
    zhuTopEvaluation_homogeneous _ _ 1 _ (oddCurrent_grade_one D j)]
  exact J_ground_return D hu i j (evenTopGroundEquiv D hu x).val x
    (evenTopGroundEquiv_val D hu x)

/-- The specified native field has a nonzero coefficient in each Leech parity direction. -/
theorem leech_nativeMixedField_scale_injective (s : Bool) :
    Function.Injective (fun z : ℂ => (nativeMixedField leechData leechUnit s).scale z) := by
  let i : Fin leechData.rank := ⟨0, by rw [leech_spec.1] <;> decide⟩
  let b := oddCurrent leechData i
  let v := leechGroundVector
  let w := Jplus (-1) b v
  have hn : w ≠ 0 ∧ Jminus 0 b w ≠ 0 :=
    ⟨(leech_normalization i).2.2.1, (leech_normalization i).2.2.2.2⟩
  cases s
  · intro z y hzy
    have h := congrArg (fun F : LawfulMixedField leechData leechUnit false =>
      F.coeff (-1) b v) hzy
    change z • w = y • w at h
    exact smul_left_injective ℂ hn.1 h
  · intro z y hzy
    have h := congrArg (fun F : LawfulMixedField leechData leechUnit true =>
      F.coeff 0 b w) hzy
    change z • Jminus 0 b w = y • Jminus 0 b w at h
    exact smul_left_injective ℂ hn.2 h

/-- For each actual integral charge a real transverse direction has nonzero Gram square. -/
theorem leech_exists_real_transverse (c : Charge leechData) :
    ∃ u : E_R leechData, u ≠ 0 ∧
      g leechData (complexify leechData u) (chargeVector c) = 0 ∧
      g leechData (complexify leechData u) (complexify leechData u) ≠ 0 := by
  let L : E_R leechData →ₗ[ℝ] ℝ := (B_R leechData).flip (realCharge c)
  have hrank : Module.finrank ℝ ℝ < Module.finrank ℝ (E_R leechData) := by
    rw [Module.finrank_self, finrank_E_R, leech_spec.1] <;> decide
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := L) hrank
  obtain ⟨u, hmem, hu⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  have hperp := LinearMap.mem_ker.mp hmem
  change g_R leechData u (realCharge c) = 0 at hperp
  have hpos : 0 < g_R leechData u u := by
    simpa [g_R_apply, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum,
      mul_assoc] using leech_spec.2.2.1.dotProduct_mulVec_pos hu
  refine ⟨u, hu, ?_, ?_⟩
  · rw [← complexify_charge c, complexify_gram, hperp, Complex.ofReal_zero]
  · rw [complexify_gram, ne_eq, Complex.ofReal_eq_zero]
    exact hpos.ne'

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
