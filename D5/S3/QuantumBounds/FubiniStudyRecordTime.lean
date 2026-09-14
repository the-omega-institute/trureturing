/- GID: D5/S3/QuantumBounds/FubiniStudyRecordTime
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/FubiniStudyRecordTime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Fubini-Study triangle inequality gives conditional record time and count bounds. -/

/-
Copyright (c) 2026 QuAIR. Authors: QuAIR Team.
The phase-alignment proof is adapted from QIT.PureVector.projectiveAngle_triangle,
QuAIR/Lean-QIT, revision c1d59b133b56e3d79efb11ee46a728d290f761f5.
Released under Apache 2.0; full license: docs/reports/recordtimebound/Lean-QIT-LICENSE.txt.
Modifications: general complex inner product spaces; Mathlib's unit-phase existence;
conditional recording-time and sequential-count consequences.
-/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped ComplexConjugate

namespace D5.S3.QuantumBounds.FubiniStudyRecordTime

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Fubini–Study angle of unit vectors, insensitive to their scalar phases. -/
noncomputable def fsAngle (a b : E) : ℝ := Real.arccos ‖inner ℂ a b‖

/-- The modulus-inner-product angle obeys the triangle inequality on unit vectors. -/
theorem fs_angle_triangle (a b c : E) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) : fsAngle a c ≤ fsAngle a b + fsAngle b c := by
  obtain ⟨u, hu, hab⟩ := Complex.exists_norm_eq_mul_self (inner ℂ a b)
  obtain ⟨v, hv, hbc⟩ := Complex.exists_norm_eq_mul_self (inner ℂ b c)
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hx : ‖conj u • a‖ = 1 := by simp [norm_smul, hu, ha]
  have hz : ‖v • c‖ = 1 := by simp [norm_smul, hv, hc]
  have hxy : inner ℝ (conj u • a) b = ‖inner ℂ a b‖ := by
    change (inner ℂ (conj u • a) b).re = _
    rw [inner_smul_left]
    simpa using (congrArg Complex.re hab).symm
  have hyz : inner ℝ b (v • c) = ‖inner ℂ b c‖ := by
    change (inner ℂ b (v • c)).re = _
    rw [inner_smul_right]
    exact (congrArg Complex.re hbc).symm
  have hxz : inner ℝ (conj u • a) (v • c) ≤ ‖inner ℂ a c‖ := by
    change (inner ℂ (conj u • a) (v • c)).re ≤ _
    calc
      _ ≤ ‖inner ℂ (conj u • a) (v • c)‖ := Complex.re_le_norm _
      _ = ‖inner ℂ a c‖ := by simp [inner_smul_left, inner_smul_right, hu, hv]
  have ht := InnerProductGeometry.angle_le_angle_add_angle (conj u • a) b (v • c)
  simp only [InnerProductGeometry.angle, hx, hb, hz, mul_one, div_one, hxy, hyz] at ht
  exact (Real.arccos_le_arccos hxz).trans ht

/-- Orthogonal records require this contact time, conditional on the two displacement bounds.
The displacement bounds are physical inputs; no dynamical speed limit is proved here. -/
theorem record_time_lower_bound (a m₀ m₁ : E)
    (ha : ‖a‖ = 1) (h₀ : ‖m₀‖ = 1) (h₁ : ‖m₁‖ = 1)
    (horth : inner ℂ m₀ m₁ = 0) (energy hbar τ : ℝ)
    (henergy : 0 < energy) (hhbar : 0 < hbar)
    (speed₀ : fsAngle a m₀ ≤ energy * τ / hbar)
    (speed₁ : fsAngle a m₁ ≤ energy * τ / hbar) :
    Real.pi * hbar / (4 * energy) ≤ τ := by
  have ht := fs_angle_triangle m₀ a m₁ h₀ ha h₁
  have hsym : fsAngle m₀ a = fsAngle a m₀ := by
    simp only [fsAngle, norm_inner_symm]
  rw [hsym] at ht
  have ho : fsAngle m₀ m₁ = Real.pi / 2 := by simp [fsAngle, horth]
  rw [ho] at ht
  have hsum : Real.pi / 2 ≤ 2 * (energy * τ / hbar) := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 4 * energy)).2
  have h := (le_div_iff₀ hhbar).1 (show Real.pi / 2 ≤ 2 * energy * τ / hbar by
    convert hsum using 1; ring)
  nlinarith

/-- A sequence of orthogonal records obeys this count bound when its total contact time fits T.
Each record has its own common initial vector and two assumed displacement bounds. -/
theorem record_count_upper_bound (N : ℕ) (a m₀ m₁ : Fin N → E)
    (ha : ∀ i, ‖a i‖ = 1) (h₀ : ∀ i, ‖m₀ i‖ = 1) (h₁ : ∀ i, ‖m₁ i‖ = 1)
    (horth : ∀ i, inner ℂ (m₀ i) (m₁ i) = 0)
    (energy hbar T : ℝ) (τ : Fin N → ℝ)
    (henergy : 0 < energy) (hhbar : 0 < hbar)
    (speed₀ : ∀ i, fsAngle (a i) (m₀ i) ≤ energy * τ i / hbar)
    (speed₁ : ∀ i, fsAngle (a i) (m₁ i) ≤ energy * τ i / hbar)
    (budget : ∑ i, τ i ≤ T) :
    (N : ℝ) ≤ 4 * energy * T / (Real.pi * hbar) := by
  have htotal : (N : ℝ) * (Real.pi * hbar / (4 * energy)) ≤ T := by
    calc
      _ = ∑ _i : Fin N, Real.pi * hbar / (4 * energy) := by simp
      _ ≤ ∑ i, τ i := Finset.sum_le_sum fun i _ =>
        record_time_lower_bound (a i) (m₀ i) (m₁ i) (ha i) (h₀ i) (h₁ i)
          (horth i) energy hbar (τ i) henergy hhbar (speed₀ i) (speed₁ i)
      _ ≤ T := budget
  apply (le_div_iff₀ (mul_pos Real.pi_pos hhbar)).2
  have hm := (div_le_iff₀ (by positivity : 0 < 4 * energy)).1
    (show (N : ℝ) * (Real.pi * hbar) / (4 * energy) ≤ T by
      simpa only [mul_div_assoc] using htotal)
  nlinarith

#print axioms fs_angle_triangle
#print axioms record_time_lower_bound
#print axioms record_count_upper_bound

end D5.S3.QuantumBounds.FubiniStudyRecordTime
