/- GID: D5/S3/Quantum/Algebra/PBIdempotentSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBIdempotentSupport
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: Original directed positive two-tables force quantitative ambient idempotent support. -/

import D5.S3.Topology.JBAmbientSupport
import D5.S3.Quantum.Algebra.PBOriginalReadoutRealization

/-! The original total response stays in every actual original idempotent corner. -/

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder

namespace D5.S3.Quantum.Algebra.PBIdempotentSupport
open D5.S3.Topology
open PBOriginalReadoutRealization

variable {X E P : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact original cone bounds and support conclusion for arbitrary original
labels and total response. Neither normalized masses nor any response regularity is used.
The conclusion holds even without density of the original isometric Jordan subalgebra. -/
theorem original_p2_support
    (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (u : X) (A : JBAlgebra.Data X S u)
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E) (C : Set E)
    (i : E →ₗᵢ[ℝ] X) (evaluation : P → E →ₗ[ℝ] ℝ)
    (hj : ∀ a b, i (J a b) = S (i a) (i b))
    (hcone : ∀ a, a ∈ C ↔ ∃ z : X, S z z = i a)
    (hdetect : ∀ a, a ∈ C ↔ ∀ α, 0 ≤ evaluation α a)
    (hP2 : ∀ α a b, (originalTable J D (evaluation α) a b).PosSemidef)
    (p : E) (hp : J p p = p) (a b : E)
    (ha : S (i p) (i a) = i a) (hb : S (i p) (i b) = i b) :
    ((‖a‖ * ‖b‖) • p + D a b ∈ C) ∧
    ((‖a‖ * ‖b‖) • p - D a b ∈ C) ∧
    D a b ∈ originalCorner i.toLinearMap S p := by
  have hip : S (i p) (i p) = i p := by rw [← hj, hp]
  have hpC : p ∈ C := (hcone p).mpr ⟨i p, hip⟩
  have hsq (v : E) : J v v ∈ C := (hcone _).mpr ⟨i v, (hj v v).symm⟩
  have hupper (v : E) (hv : S (i p) (i v) = i v) :
      ‖v‖ ^ 2 • p - J v v ∈ C := by
    apply (hcone _).mpr
    obtain ⟨z, hz⟩ := JBAmbientSupport.corner_square_bound A (i p) (i v) hip hv
    refine ⟨z, ?_⟩
    simpa only [map_sub, map_smul, hj, i.norm_map] using hz
  have hscalar (α : P) : |evaluation α (D a b)| ≤
      (‖a‖ * ‖b‖) * evaluation α p := by
    have hpos (v : E) : 0 ≤ evaluation α (J v v) :=
      (hdetect _).mp (hsq v) α
    have hpa : 0 ≤ evaluation α p := (hdetect p).mp hpC α
    have hau := (hdetect _).mp (hupper a ha) α
    have hbu := (hdetect _).mp (hupper b hb) α
    simp only [map_sub, map_smul, smul_eq_mul] at hau hbu
    have hdet := (positive_table_transfer J D C evaluation hdetect hP2 (evaluation α)
      (fun v hv => (hdetect v).mp hv α) a b).2
    have hprod : evaluation α (J a a) * evaluation α (J b b) ≤
        (‖a‖ ^ 2 * evaluation α p) * (‖b‖ ^ 2 * evaluation α p) :=
      mul_le_mul (by linarith) (by linarith) (hpos b) (by positivity)
    have hr : 0 ≤ (‖a‖ * ‖b‖) * evaluation α p := by positivity
    have hd : evaluation α (D a b) ^ 2 ≤
        ((‖a‖ * ‖b‖) * evaluation α p) ^ 2 := by
      nlinarith [sq_nonneg (evaluation α (J a b))]
    exact (sq_le_sq₀ (abs_nonneg _) hr).mp (by simpa only [sq_abs] using hd)
  have hplus : (‖a‖ * ‖b‖) • p + D a b ∈ C := by
    apply (hdetect _).mpr
    intro α
    have h := (abs_le.mp (hscalar α)).1
    simpa only [map_add, map_smul, smul_eq_mul] using (show
      0 ≤ (‖a‖ * ‖b‖) * evaluation α p + evaluation α (D a b) by linarith)
  have hminus : (‖a‖ * ‖b‖) • p - D a b ∈ C := by
    apply (hdetect _).mpr
    intro α
    have h := (abs_le.mp (hscalar α)).2
    simpa only [map_sub, map_smul, smul_eq_mul] using (show
      0 ≤ (‖a‖ * ‖b‖) * evaluation α p - evaluation α (D a b) by linarith)
  refine ⟨hplus, hminus, ?_⟩
  have hsupport := JBAmbientSupport.support_of_squares A (i p) (i (D a b)) hip
    (‖a‖ * ‖b‖)
    (by simpa only [map_add, map_smul] using (hcone _).mp hplus)
    (by simpa only [map_sub, map_smul] using (hcone _).mp hminus)
  change S (i p) (i (D a b)) - i (D a b) = 0
  exact sub_eq_zero.mpr hsupport

#print axioms original_p2_support

end D5.S3.Quantum.Algebra.PBIdempotentSupport
