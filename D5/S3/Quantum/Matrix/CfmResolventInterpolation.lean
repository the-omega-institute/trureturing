/- GID: D5/S3/Quantum/Matrix/CfmResolventInterpolation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CfmResolventInterpolation
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order, mathlib/module/Mathlib.Analysis.InnerProductSpace.Basic]
   utility: none
   digest: Three spectral nodes control the two mixed resolvent products. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Three-node rational interpolation, including repeated spectral nodes. -/

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.CfmResolventInterpolation

open _root_.Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

private def e₁ (y : Fin 3 → ℝ) : ℝ := y 0 + y 1 + y 2
private def e₂ (y : Fin 3 → ℝ) : ℝ := y 0 * y 1 + y 0 * y 2 + y 1 * y 2
private def e₃ (y : Fin 3 → ℝ) : ℝ := y 0 * y 1 * y 2
private def denominator (y : Fin 3 → ℝ) : ℝ := 1 + e₁ y + e₂ y + e₃ y

private theorem denominator_factor (y : Fin 3 → ℝ) :
    denominator y = (y 0 + 1) * (y 1 + 1) * (y 2 + 1) := by
  simp only [denominator, e₁, e₂, e₃]
  ring

private theorem scalar_interpolation (y : Fin 3 → ℝ) (hy : ∀ i, 2 < y i) :
    ∃ c₁ c₂ c₃ : ℝ, |c₁| ≤ 1 ∧ |c₂| ≤ 2 ∧ |c₃| ≤ 2 ∧
      (∀ i, (y i - 1)⁻¹ * (y i + 1)⁻¹ =
        c₁ * ((y i - 1)⁻¹)^2 +
        c₂ * ((y i - 1)⁻¹ * (y i)⁻¹) + c₃ * ((y i)⁻¹)^2) ∧
      (∀ i, (y i)⁻¹ * (y i + 1)⁻¹ =
        (2*c₁) * ((y i - 1)⁻¹)^2 +
        (2*c₂-1) * ((y i - 1)⁻¹ * (y i)⁻¹) + (2*c₃) * ((y i)⁻¹)^2) := by
  let d := denominator y
  have hy0 := hy 0
  have hy1 := hy 1
  have hy2 := hy 2
  have hym0 : 0 < y 0 - 1 := by linarith
  have hym1 : 0 < y 1 - 1 := by linarith
  have hym2 : 0 < y 2 - 1 := by linarith
  have he1 : 0 < e₁ y := by dsimp [e₁]; linarith
  have he2 : 0 < e₂ y := by
    dsimp [e₂]
    positivity
  have he3 : 0 < e₃ y := by dsimp [e₃]; positivity
  have hd : 0 < d := by dsimp [d, denominator]; linarith
  let c₁ := ((y 0-1)*(y 1-1)*(y 2-1)) / d
  let c₂ := 2*(e₂ y-e₃ y) / d
  let c₃ := 2*e₃ y / d
  have h1 : |c₁| ≤ 1 := by
    rw [abs_of_nonneg (by dsimp [c₁]; positivity), div_le_one hd]
    dsimp [d]
    rw [denominator_factor]
    have h01 : (y 0-1)*(y 1-1) ≤ (y 0+1)*(y 1+1) := by nlinarith
    calc
      (y 0-1)*(y 1-1)*(y 2-1) ≤ (y 0+1)*(y 1+1)*(y 2-1) :=
        mul_le_mul_of_nonneg_right h01 (by linarith)
      _ ≤ (y 0+1)*(y 1+1)*(y 2+1) := by nlinarith
  have h2 : |c₂| ≤ 2 := by
    rw [abs_le]
    constructor <;> dsimp [c₂] <;>
      (first | apply (le_div_iff₀ hd).2 | apply (div_le_iff₀ hd).2) <;>
      dsimp [d, denominator] <;> linarith
  have h3 : |c₃| ≤ 2 := by
    rw [abs_of_nonneg (by dsimp [c₃]; positivity)]
    apply (div_le_iff₀ hd).2
    dsimp [d, denominator]
    linarith
  refine ⟨c₁, c₂, c₃, h1, h2, h3, ?_, ?_⟩
  all_goals
    intro i
    have hm : y i - 1 ≠ 0 := by have := hy i; linarith
    have hp : y i + 1 ≠ 0 := by have := hy i; linarith
    have hz : y i ≠ 0 := by have := hy i; linarith
    dsimp [c₁, c₂, c₃]
    field_simp
    fin_cases i <;> dsimp [d, denominator, e₁, e₂, e₃] <;> ring

private theorem inverse_cfc (C : Matrix (Fin 3) (Fin 3) ℂ) (hC : C.IsHermitian)
    (s : ℝ) (hs : ∀ x ∈ spectrum ℝ C, s - x ≠ 0) :
    (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - C)⁻¹ = cfc (fun x : ℝ => (s-x)⁻¹) C := by
  have hc : cfc (fun x : ℝ => s-x) C = s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - C := by
    rw [cfc_sub _ _ C, cfc_const (p := IsSelfAdjoint) s C hC, cfc_id' (p := IsSelfAdjoint) ℝ C hC]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← hc, Matrix.nonsing_inv_eq_ringInverse, cfc_inv _ C hs]

private theorem norm_three_sq_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : ℝ) (x y z : E) :
    ‖a • x + b • y + c • z‖ ^ 2 ≤
      (a^2+b^2+c^2) * (‖x‖^2+‖y‖^2+‖z‖^2) := by
  have ht : ‖a • x + b • y + c • z‖ ≤ |a| *‖x‖ + |b| *‖y‖ + |c| *‖z‖ := by
    calc
      _ ≤ ‖a • x + b • y‖ + ‖c • z‖ := norm_add_le _ _
      _ ≤ (‖a • x‖ + ‖b • y‖) + ‖c • z‖ := by
        simpa only [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (norm_add_le (a • x) (b • y)) ‖c • z‖
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs]
  have ht' := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
  have hxy := sq_nonneg (|a| *‖y‖ - |b| *‖x‖)
  have hxz := sq_nonneg (|a| *‖z‖ - |c| *‖x‖)
  have hyz := sq_nonneg (|b| *‖z‖ - |c| *‖y‖)
  nlinarith only [ht', hxy, hxz, hyz, sq_abs a, sq_abs b, sq_abs c]

/-- Three spectral nodes give a uniform bound of 54, with no separation assumption
on those nodes. The linear observation may include a square root and a test vector. -/
theorem mixed_resolvent_control (C : Matrix (Fin 3) (Fin 3) ℂ) (hC : C.IsHermitian)
    (hspec : ∀ i, hC.eigenvalues i < 1)
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℝ] E) :
    let R := fun s : ℝ => (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - C)⁻¹
    ‖L (R 2 * R 4)‖^2 + ‖L (R 3 * R 4)‖^2 ≤
      54 * (‖L (R 2 * R 2)‖^2 + ‖L (R 2 * R 3)‖^2 + ‖L (R 3 * R 3)‖^2) := by
  let y : Fin 3 → ℝ := fun i => 3 - hC.eigenvalues i
  obtain ⟨a,b,c,ha,hb,hc,hi,hj⟩ := scalar_interpolation y (by intro i; dsimp [y]; linarith [hspec i])
  let R := fun s : ℝ => (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - C)⁻¹
  have hr (s : ℝ) (hs : 2 ≤ s) : R s = cfc (fun x : ℝ => (s-x)⁻¹) C := by
    apply inverse_cfc C hC s
    intro x hx
    obtain ⟨i,rfl⟩ := hC.spectrum_real_eq_range_eigenvalues ▸ hx
    linarith [hspec i]
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ C) :=
    (Matrix.finite_real_spectrum (A := C)).continuousOn f
  have hfirst : R 2 * R 4 = a • (R 2 * R 2) + b • (R 2 * R 3) + c • (R 3 * R 3) := by
    simp only [hr 2 (by norm_num), hr 3 (by norm_num), hr 4 (by norm_num)]
    simp only [← cfc_mul _ _ C (hcont _) (hcont _),
      ← cfc_const_mul _ _ C (hcont _), ← cfc_add C _ _ (hcont _) (hcont _)]
    apply cfc_congr
    intro x hx
    obtain ⟨i,rfl⟩ := hC.spectrum_real_eq_range_eigenvalues ▸ hx
    have hyi : y i - 1 = 2 - hC.eigenvalues i := by dsimp [y]; ring
    have hyi' : y i + 1 = 4 - hC.eigenvalues i := by dsimp [y]; ring
    simpa only [hyi, hyi', y, pow_two] using hi i
  have hsecond : R 3 * R 4 = (2*a) • (R 2 * R 2) + (2*b-1) • (R 2 * R 3) + (2*c) • (R 3 * R 3) := by
    simp only [hr 2 (by norm_num), hr 3 (by norm_num), hr 4 (by norm_num)]
    simp only [← cfc_mul _ _ C (hcont _) (hcont _),
      ← cfc_const_mul _ _ C (hcont _), ← cfc_add C _ _ (hcont _) (hcont _)]
    apply cfc_congr
    intro x hx
    obtain ⟨i,rfl⟩ := hC.spectrum_real_eq_range_eigenvalues ▸ hx
    have hyi : y i - 1 = 2 - hC.eigenvalues i := by dsimp [y]; ring
    have hyi' : y i + 1 = 4 - hC.eigenvalues i := by dsimp [y]; ring
    simpa only [hyi, hyi', y, pow_two] using hj i
  dsimp only
  change ‖L (R 2 * R 4)‖^2 + ‖L (R 3 * R 4)‖^2 ≤ _
  rw [hfirst, hsecond]
  simp only [map_add, map_smul]
  have h9 : a^2+b^2+c^2 ≤ 9 := by
    have ha' := (sq_le_sq₀ (abs_nonneg a) (by norm_num)).mpr ha
    have hb' := (sq_le_sq₀ (abs_nonneg b) (by norm_num)).mpr hb
    have hc' := (sq_le_sq₀ (abs_nonneg c) (by norm_num)).mpr hc
    simp only [sq_abs] at *
    linarith
  have h45 : (2*a)^2+(2*b-1)^2+(2*c)^2 ≤ 45 := by
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    have hc' := abs_le.mp hc
    nlinarith [sq_nonneg (2*a), sq_nonneg (2*b-1), sq_nonneg (2*c)]
  have hs : 0 ≤ ‖L (R 2 * R 2)‖^2+‖L (R 2 * R 3)‖^2+‖L (R 3 * R 3)‖^2 := by positivity
  have hA := (norm_three_sq_le a b c (L (R 2 * R 2)) (L (R 2 * R 3)) (L (R 3 * R 3))).trans
    (mul_le_mul_of_nonneg_right h9 hs)
  have hB := (norm_three_sq_le (2*a) (2*b-1) (2*c) (L (R 2 * R 2)) (L (R 2 * R 3)) (L (R 3 * R 3))).trans
    (mul_le_mul_of_nonneg_right h45 hs)
  linarith

end D5.S3.Quantum.Matrix.CfmResolventInterpolation
