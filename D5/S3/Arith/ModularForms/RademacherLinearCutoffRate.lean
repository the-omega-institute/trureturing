import D5.S3.Arith.ModularForms.RademacherLinearTailConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# A rate for the rectangular linear Rademacher cutoff

The cotangent comparison controls truncation in the denominator. The Möbius
constant and the positive Fourier powers are then bounded on the omitted moduli.
-/

set_option autoImplicit false

open scoped ArithmeticFunction.Moebius BigOperators UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherLinearTailConvergence

open RademacherLinearCutoff
  (comparisonConstant linearRectangularCutoff_error_le linearPrincipalValueCutoff)
open RademacherPhaseRamanujan
  (vacuumPhaseWeight hasSum_linearPhaseConstant linearConstantCutoff vacuumPhaseWeight_eq_LSeries_term
    sum_vacuumPhase_eq_moebius linearPrincipalValueCutoff_eq_constant_add_qTail
    linearPrincipalValueQTail linearCutoff_eq_linearRectangularCutoff)
open RademacherVacuum (linearCutoff)

private theorem tsum_nat_add_rpow_le {s : ℝ} (hs : s < -1) {N : ℕ} (hN : 1 ≤ N) :
    (∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ s) ≤
      (1 - (s + 1)⁻¹) * (N : ℝ) ^ (s + 1) := by
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0 : ℝ) < N := zero_lt_one.trans_le hN₁
  have hanti : AntitoneOn (fun x : ℝ => x ^ s) (Set.Ici (N : ℝ)) :=
    fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (hN₀.trans_le hx) hxy (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral N hanti
    (integrableOn_Ioi_rpow_of_lt hs hN₀)
    (fun _ ht => Real.rpow_nonneg (hN₀.trans (Set.mem_Ioi.mp ht)).le _)
  rw [integral_Ioi_rpow_of_lt hs hN₀] at htail
  have hsum : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ s) :=
    (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ s) N).mpr
      (Real.summable_nat_rpow.mpr hs)
  rw [hsum.tsum_eq_zero_add]
  simp only [zero_add]
  calc
    _ ≤ (N : ℝ) ^ (s + 1) + -(N : ℝ) ^ (s + 1) / (s + 1) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith))
        (by simpa only [Nat.add_right_comm] using htail)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The Möbius phase constant has an inverse-linear omitted-modulus tail. -/
theorem norm_twelve_sub_linearConstantCutoff_le {N : ℕ} (hN : 1 ≤ N) :
    ‖(12 : ℂ) - linearConstantCutoff N‖ ≤ (4 * Real.pi ^ 2) / (N : ℝ) := by
  let term (c : ℕ) := 2 * (Real.pi : ℂ) ^ 2 * vacuumPhaseWeight c
  have hsplit : (12 : ℂ) - linearConstantCutoff N = ∑' k : ℕ, term (k + N) := by
    have hzero : term 0 = 0 := by
      simp only [term, vacuumPhaseWeight_eq_LSeries_term, LSeries.term_zero, mul_zero]
    have hcut : linearConstantCutoff N = ∑ c ∈ Finset.range N, term c :=
      Finset.sum_erase _ hzero
    rw [hcut, ← hasSum_linearPhaseConstant.tsum_eq,
      ← hasSum_linearPhaseConstant.summable.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hterm (k : ℕ) :
      ‖term (k + N)‖ ≤ 2 * Real.pi ^ 2 * ((k + N : ℕ) : ℝ) ^ (-2 : ℝ) := by
    have hc : 0 < k + N := by omega
    have hmoebius : |(μ (k + N) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k + N)
    simp only [term, vacuumPhaseWeight, sum_vacuumPhase_eq_moebius _ hc, norm_mul,
      Complex.norm_ofNat, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_div, Complex.norm_intCast, Complex.norm_natCast]
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using div_le_div_of_nonneg_right hmoebius (sq_nonneg _))
      (by positivity)
  have hp : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ (-2 : ℝ)) N).mpr
      (Real.summable_nat_rpow.mpr (by norm_num))
  rw [hsplit]
  calc
    _ ≤ 2 * Real.pi ^ 2 * ∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-2 : ℝ) :=
      tsum_of_norm_bounded (hp.hasSum.mul_left _) hterm
    _ ≤ 2 * Real.pi ^ 2 * (2 * (N : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one,
        inv_neg, inv_one, sub_neg_eq_add, one_add_one_eq_two] using
        tsum_nat_add_rpow_le (s := -2) (by norm_num) hN
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The positive Fourier tail of the actual principal value cutoff has rate
`N ^ (-1/8)`, uniformly at or above any fixed positive height. -/
theorem norm_linearPrincipalValueQTailLimit_sub_cutoff_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℍ), δ ≤ τ.im → ∀ N : ℕ, 1 ≤ N →
      ‖linearPrincipalValueQTailLimit τ - linearPrincipalValueQTail N τ‖ ≤
        C * (N : ℝ) ^ (-(1 / 8) : ℝ) := by
  obtain ⟨A, hA, hbound⟩ := norm_linearPrincipalValueQTailLimit_sub_cutoff_le hδ
  refine ⟨9 * A + 1, by positivity, fun τ hτ N hN => ?_⟩
  calc
    _ ≤ A * ∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-(9 / 8) : ℝ) := hbound τ hτ N
    _ ≤ A * (9 * (N : ℝ) ^ (-(1 / 8) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      simpa only [show -(9 / 8 : ℝ) + 1 = -(1 / 8 : ℝ) by norm_num,
        show 1 - (-(1 / 8 : ℝ))⁻¹ = 9 by norm_num] using
        tsum_nat_add_rpow_le (s := -(9 / 8 : ℝ)) (by norm_num) hN
    _ ≤ _ := by
      rw [← mul_assoc, mul_comm A 9]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

private theorem div_nat_le_mul_rpow {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) :
    C / (N : ℝ) ≤ C * (N : ℝ) ^ (-(1 / 8) : ℝ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_eq_mul_inv, ← Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN' (by norm_num)) hC

/-- The shifted rectangular linear cutoff has rate `N ^ (-1/8)` on a bounded
positive-height region whenever the rectangular comparison applies. -/
theorem norm_linearPrincipalValueQTailLimit_sub_linearCutoff_sub_twelve_le
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℍ), δ ≤ τ.im → ‖(τ : ℂ)‖ ≤ B →
      ∀ N : ℕ, 2 * (B + 1) ≤ (N : ℝ) →
        ‖linearPrincipalValueQTailLimit τ - (linearCutoff N τ - 12)‖ ≤
          C * (N : ℝ) ^ (-(1 / 8) : ℝ) := by
  obtain ⟨CQ, hCQ, hq⟩ := norm_linearPrincipalValueQTailLimit_sub_cutoff_le_rpow hδ
  let CR := 2 * Real.pi * comparisonConstant B
  let CC := 4 * Real.pi ^ 2
  have hCR : 0 ≤ CR := by dsimp [CR, comparisonConstant]; positivity
  have hCC : 0 ≤ CC := by dsimp [CC]; positivity
  refine ⟨CQ + CC + CR, by positivity, fun τ hτ hτB N hN => ?_⟩
  have hN₁ : 1 ≤ N := by
    exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hr := linearRectangularCutoff_error_le hτB τ.im_pos hN
  rw [← linearCutoff_eq_linearRectangularCutoff, linearPrincipalValueCutoff_eq_constant_add_qTail,
    ← norm_neg] at hr
  have heq :
      linearPrincipalValueQTailLimit τ - (linearCutoff N τ - 12) =
        ((linearPrincipalValueQTailLimit τ - linearPrincipalValueQTail N τ) +
          (12 - linearConstantCutoff N)) +
          -(linearCutoff N τ - (linearConstantCutoff N + linearPrincipalValueQTail N τ)) := by
    abel
  rw [heq]
  calc
    _ ≤ (‖linearPrincipalValueQTailLimit τ - linearPrincipalValueQTail N τ‖ +
        ‖(12 : ℂ) - linearConstantCutoff N‖) +
        ‖-(linearCutoff N τ - (linearConstantCutoff N + linearPrincipalValueQTail N τ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ CQ * (N : ℝ) ^ (-(1 / 8) : ℝ) + CC * (N : ℝ) ^ (-(1 / 8) : ℝ) +
        CR * (N : ℝ) ^ (-(1 / 8) : ℝ) :=
      add_le_add (add_le_add (hq τ hτ N hN₁)
        ((norm_twelve_sub_linearConstantCutoff_le hN₁).trans (div_nat_le_mul_rpow hCC hN₁)))
        (hr.trans (div_nat_le_mul_rpow hCR hN₁))
    _ = _ := by rw [add_mul, add_mul]

end D5.S3.Arith.ModularForms.RademacherLinearTailConvergence
