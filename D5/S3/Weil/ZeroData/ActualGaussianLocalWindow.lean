/- SOURCE CANDIDATE ONLY. A COMPLETE finite local occurrence set, obtained
   from actual ZeroData and its native mass theorem. No local finiteness,
   height, multiplicity, or cardinality supplier is an input. -/
import D5.S3.Weil.ZeroData.ActualGaussianZeroSum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZeroData.ActualGaussianLocalWindow
open scoped BigOperators
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ActualGaussianMass

private theorem radius_le (rho : ℂ) (hrho : IsNontrivialZero rho) :
    D5.S3.Weil.ZeroSum.spectralRadius rho ≤ |rho.im| + 1 := by
  have hb : |rho.re - 1 / 2| ≤ 1 := abs_le.mpr (by constructor <;> linarith [hrho.2.1, hrho.2.2])
  unfold D5.S3.Weil.ZeroSum.spectralRadius spectralParameter
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have h := Complex.norm_le_abs_re_add_abs_im (rho - (criticalAbscissa : ℂ))
  have hbound : ‖rho - (criticalAbscissa : ℂ)‖ ≤
      |rho.re - 1 / 2| + |rho.im| := by
    simpa [Complex.sub_re, Complex.sub_im, sub_zero, criticalAbscissa] using h
  linarith

/-- Every analytic occurrence, including repeated values, in the closed
two-sided window is included. The larger spectral cutoff is only an
enumeration device and is filtered away from the resulting set. -/
def localWindow (γ : ℝ) : Finset ℕ :=
  (((actualData.symmetricIndices (|γ| + 7)).sigma
      (fun n => (Finset.univ : Finset (Fin (actualData.multiplicity n))))).map
        actualOccurrenceEquiv.symm.toEmbedding).filter
          (fun k => |(actualZero k).im - γ| ≤ 6)

theorem mem_localWindow (γ : ℝ) (k : ℕ) :
    k ∈ localWindow γ ↔ |(actualZero k).im - γ| ≤ 6 := by
  classical
  rw [localWindow, Finset.mem_filter]
  refine ⟨fun h => h.2, fun hk => ⟨?_, hk⟩⟩
  apply Finset.mem_map.mpr
  refine ⟨actualOccurrenceEquiv k, ?_, actualOccurrenceEquiv.symm_apply_apply k⟩
  apply Finset.mem_sigma.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  apply actualData.mem_symmetricIndices.mpr
  change D5.S3.Weil.ZeroSum.spectralRadius (actualZero k) ≤ |γ| + 7
  have hi : |(actualZero k).im| ≤ 6 + |γ| := by
    have htri := abs_add_le ((actualZero k).im - γ) γ
    rw [sub_add_cancel] at htri
    linarith
  have hr := radius_le (actualZero k)
    (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
  have hr' : D5.S3.Weil.ZeroSum.spectralRadius
      (actualData.zero (actualOccurrenceEquiv k).1) ≤
      |(actualZero k).im| + 1 := by
    simpa only [actualZero] using hr
  exact hr'.trans (by linarith)

private theorem occurrence_count_bound (s : Finset ℕ) (T : ℝ) (hT : 0 < T)
    (hs : ∀ k ∈ s, |(actualZero k).im| ≤ T) : (s.card : ℝ) ≤ 2 * T ^ 2 := by
  have hterm (k : ℕ) (hk : k ∈ s) : 1 ≤ T ^ 2 * ((actualZero k).im)⁻¹ ^ 2 := by
    have hh : 10 < |(actualZero k).im| := actual_height_gt_ten _
      (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    have hp : 0 < (actualZero k).im ^ 2 := by
      have habspos : 0 < |(actualZero k).im| := by linarith
      have he := sq_pos_of_pos habspos
      simpa only [sq_abs] using he
    have hsq : (actualZero k).im ^ 2 ≤ T ^ 2 := by
      nlinarith [sq_abs (actualZero k).im, hs k hk,
        mul_nonneg (sub_nonneg.mpr (hs k hk)) (by positivity : 0 ≤ T + |(actualZero k).im|)]
    have hd : 1 ≤ T ^ 2 / (actualZero k).im ^ 2 := (le_div_iff₀ hp).mpr (by simpa)
    simpa only [div_eq_mul_inv, inv_pow] using hd
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hsum
  have hmass := sum_le_hasSum s (fun j _ => sq_nonneg ((actualZero j).im)⁻¹)
    inverse_square_summable.hasSum
  have hb : (∑ k ∈ s, ((actualZero k).im)⁻¹ ^ 2) ≤ 2 :=
    hmass.trans mass_lt_two.le
  exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg T)])

/-- This count includes BOTH ordinate signs and exact analytic repetitions. -/
theorem localWindow_card (γ : ℝ) (hγ : 0 < γ) :
    ((localWindow γ).card : ℝ) ≤ 2 * (γ + 10) ^ 2 := by
  apply occurrence_count_bound _ (γ + 10) (by linarith)
  intro k hk
  have hdist := (mem_localWindow γ k).mp hk
  have ht := abs_add_le ((actualZero k).im - γ) γ
  rw [sub_add_cancel, abs_of_pos hγ] at ht
  linarith

end D5.S3.Weil.ZeroData.ActualGaussianLocalWindow
