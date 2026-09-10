/- GID: D5/S3/Analytic/SeriesInequalities/BaezDuarteNewtonMajorant
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/BaezDuarteNewtonMajorant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Baez-Duarte coefficient decay gives compact summable majorants. -/
import D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
import D5.S3.Weil.ZetaBridge.RieszBaezDuarte
import Mathlib.Analysis.Normed.Group.Bounded

open scoped BigOperators
open Finset
open D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds

namespace D5.S3.Analytic.SeriesInequalities.BaezDuarteNewtonMajorant

private theorem continuous_term (k : ℕ) :
    Continuous (fun s : ℂ => (D5.S3.Weil.RieszBaezDuarte.baezDuarte k : ℂ) *
      normalizedPochhammer k (s / 2)) := by
  cases k with
  | zero =>
    simp only [normalized_pochhammer_zero]
    fun_prop
  | succ k =>
    simp only [normalized_pochhammer_eq_prod]
    fun_prop

theorem baez_duarte_newton_compact_majorant
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ k : ℕ, N ≤ k → |D5.S3.Weil.RieszBaezDuarte.baezDuarte k| ≤
        C * Real.rpow (k : ℝ) (-(3 : ℝ) / 4 + ε))
    (K : Set ℂ) (hK : IsCompact K) (hhalf : K ⊆ {s : ℂ | (1 : ℝ) / 2 < s.re}) :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ k : ℕ, 0 ≤ g k) ∧
      (∀ (k : ℕ) (s : ℂ), s ∈ K →
        ‖(D5.S3.Weil.RieszBaezDuarte.baezDuarte k : ℂ) *
          normalizedPochhammer k (s / 2)‖ ≤ g k) := by
  obtain ⟨a, ha, hamin⟩ := hK.exists_forall_le' Complex.continuous_re.continuousOn
    (a := (1 : ℝ) / 2) hhalf
  let δ : ℝ := (a - 1 / 2) / 4
  have hd : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, N, hN, hc⟩ := hdecay δ hd
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn
    (f := fun s : ℂ => s / 2) (by fun_prop)
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hRs (s : ℂ) (hs : s ∈ K) : ‖s / 2‖ ≤ R :=
    (hR₀ s hs).trans (le_max_left _ _)
  have hprefix (k : ℕ) : ∃ B : ℝ, ∀ s ∈ K,
      ‖(D5.S3.Weil.RieszBaezDuarte.baezDuarte k : ℂ) *
        normalizedPochhammer k (s / 2)‖ ≤ B :=
    hK.exists_bound_of_continuousOn (continuous_term k).continuousOn
  choose B hB using hprefix
  let A := C * Real.exp (R + R ^ 2)
  have hA : 0 ≤ A := mul_nonneg hC.le (Real.exp_pos _).le
  let t : ℕ → ℝ := fun k => A * (k : ℝ) ^ (-1 - δ)
  have ht : Summable t :=
    (Real.summable_nat_rpow.mpr (by linarith : -1 - δ < -1)).mul_left A
  have ht0 (k : ℕ) : 0 ≤ t k := mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let p : ℕ → ℝ := fun k => if k < N then max (B k) 0 else 0
  have hp : Summable p := by
    apply summable_of_ne_finset_zero (s := range N)
    intro k hk
    simp only [mem_range, not_lt] at hk
    simp [p, not_lt.mpr hk]
  refine ⟨fun k => p k + t k, hp.add ht, ?_, ?_⟩
  · intro k
    exact add_nonneg (by dsimp [p]; split_ifs <;> positivity) (ht0 k)
  · intro k s hs
    by_cases hk : k < N
    · calc
        _ ≤ B k := hB k s hs
        _ ≤ max (B k) 0 := le_max_left _ _
        _ ≤ p k + t k := by
          simpa only [p, if_pos hk] using
            (le_add_of_nonneg_right (ht0 k) : max (B k) 0 ≤ max (B k) 0 + t k)
    · have hkN : N ≤ k := Nat.le_of_not_gt hk
      have hk1 : 1 ≤ k := hN.trans hkN
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hkbase : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hexponent : -(3 : ℝ) / 4 + δ + -(s / 2).re ≤ -1 - δ := by
        have hsre := hamin s hs
        simp only [Complex.div_ofNat_re]
        dsimp [δ]
        linarith
      have hbound := normalized_pochhammer_norm_le R hR k hk1 (s / 2) (hRs s hs)
      have hck := hc k hkN
      simp only [Real.rpow_eq_pow] at hck hbound
      have htail : ‖(D5.S3.Weil.RieszBaezDuarte.baezDuarte k : ℂ) *
          normalizedPochhammer k (s / 2)‖ ≤ t k := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ (C * (k : ℝ) ^ (-(3 : ℝ) / 4 + δ)) *
              (Real.exp (R + R ^ 2) * (k : ℝ) ^ (-(s / 2).re)) :=
            mul_le_mul hck hbound (norm_nonneg _) (by positivity)
          _ = A * (k : ℝ) ^ (-(3 : ℝ) / 4 + δ + -(s / 2).re) := by
            rw [Real.rpow_add hkpos (-(3 : ℝ) / 4 + δ) (-(s / 2).re)]
            dsimp [A]
            ring
          _ ≤ t k := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hkbase hexponent) hA
      simpa [p, hk] using htail

end D5.S3.Analytic.SeriesInequalities.BaezDuarteNewtonMajorant
