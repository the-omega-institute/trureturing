/- GID: D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/JainAbsCosine/GapSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn, mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: Exact all-real signs of absolute-cosine Fourier modes and their short gaps. -/

import D5.S3.Analytic.ExponentialSum.DescartesRule
import D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
import D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact signs obtained by saturating the exponential variation bound. -/

noncomputable section
open scoped BigOperators
open Finset
open D5.S3.Analytic.ExponentialSum.DescartesRule
open D5.S3.Quantum.Matrix.JainAbsCosine.Defs
open D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
open D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros

namespace D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns

private lemma half_sum (m : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin m, f (i.val + 1)) = ∑ l ∈ Icc 1 m, f l := by
  apply sum_bij (fun i _ => i.val + 1)
  · intro i _
    simp only [mem_Icc]
    omega
  · intro a _ b _ h
    apply Fin.ext
    omega
  · intro l hl
    have hl' := mem_Icc.mp hl
    refine ⟨⟨l - 1, by omega⟩, mem_univ _, ?_⟩
    dsimp
    omega
  · intro i _
    rfl

private lemma half_list (m : ℕ) (f : ℕ → ℝ) :
    List.ofFn (fun i : Fin m => f (i.val + 1)) = (List.range' 1 m).map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
    congr 1
    omega

private def exponents (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  Real.log (Real.cos ((i.val : ℝ) * angle m))

private lemma exponents_strictAnti (m : ℕ) : StrictAnti (exponents m) := by
  intro a b hab
  have hb : 1 ≤ b.val := by omega
  have hbm : b.val ≤ m := by omega
  by_cases ha : a.val = 0
  · have hc := cosine_base_bounds hb hbm
    simpa [exponents, ha] using Real.log_neg hc.1 hc.2
  · exact (logarithmic_exponent_order (by omega) hab hbm).1

private def zeros (j : ℕ) : Finset ℝ := (range j).image (fun s : ℕ => 2 * (s : ℝ))

private lemma twice_injective : Function.Injective (fun s : ℕ => 2 * (s : ℝ)) := by
  intro a b h
  have : (a : ℝ) = b := by linarith
  exact_mod_cast this

private lemma zeros_card (j : ℕ) : (zeros j).card = j := by
  rw [zeros, card_image_of_injective _ twice_injective, card_range]

private lemma zeros_product (j : ℕ) (r : ℝ) :
    (∏ z ∈ zeros j, (r - z)) = rootProduct j r := by
  rw [zeros, prod_image (fun a _ b _ h => twice_injective h)]
  rfl

private def modeCoefficients (m j : ℕ) (i : Fin (m + 1)) : ℝ :=
  if i.val = 0 then 1 else 2 * Real.cos (2 * (j : ℝ) * (i.val : ℝ) * angle m)

private lemma mode_expansion (m j : ℕ) (r : ℝ) :
    exponentialSum (modeCoefficients m j) (exponents m) r = modeValue m j r := by
  rw [exponentialSum, Fin.sum_univ_succ]
  simp only [modeCoefficients, Fin.val_zero, ite_true, exponents, Nat.cast_zero,
    zero_mul, Real.cos_zero, Real.log_one, Real.exp_zero, mul_one, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
  rw [modeValue, mul_sum]
  congr 1
  rw [← half_sum]
  apply sum_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (cosine_base_bounds (by omega) (by omega)).1]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private lemma mode_variations {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    (List.ofFn (modeCoefficients m j)).signVariations = j := by
  rw [List.ofFn_succ]
  have he : (fun i : Fin m => modeCoefficients m j i.succ) =
      (fun i : Fin m => 2 * Real.cos (2 * (j : ℝ) * ((i.val + 1 : ℕ) : ℝ) * angle m)) := by
    funext i
    simp [modeCoefficients]
  rw [he, half_list m (fun l => 2 * Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m))]
  simpa [modeCoefficients] using mode_coefficients_signVariations hj hjm

/-- Every Fourier mode has exactly the sign of its forced-root product. -/
theorem modeValue_sign {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) (r : ℝ) :
    SignType.sign (modeValue m j r) = SignType.sign (rootProduct j r) := by
  have hz : ∀ t ∈ zeros j, exponentialSum (modeCoefficients m j) (exponents m) t = 0 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
    rw [mode_expansion]
    exact modeValue_even_eq_zero m j s (mem_range.mp hs) hjm
  have hbound := sign_crossing_bound (modeCoefficients m j) (exponents m)
    (exponents_strictAnti m) ⟨0, by simp [modeCoefficients]⟩ (zeros j) hz
  have hcard : (zeros j).card = (List.ofFn (modeCoefficients m j)).signVariations := by
    apply Nat.le_antisymm (le_trans (Nat.le_add_right _ _) hbound)
    rw [zeros_card, mode_variations hj hjm]
  have h := exact_sign (modeCoefficients m j) (exponents m) (exponents_strictAnti m)
    ⟨0, by simp [modeCoefficients], by intro k hk; exact (Fin.not_lt_zero k hk).elim⟩
    (zeros j) hz hcard r
  simpa only [mode_expansion, zeros_product] using h

private def gapCoefficients (m j d : ℕ) (i : Fin m) : ℝ :=
  Real.sin (((2 * j + d : ℕ) : ℝ) * ((i.val + 1 : ℕ) : ℝ) * angle m) *
    Real.sin ((d : ℝ) * ((i.val + 1 : ℕ) : ℝ) * angle m)

private def gapExponents (m : ℕ) (i : Fin m) : ℝ := exponents m i.succ

private lemma gap_expansion (m j d : ℕ) (r : ℝ) :
    modeValue m j r - modeValue m (j + d) r =
      4 * exponentialSum (gapCoefficients m j d) (gapExponents m) r := by
  rw [modeValue_sub, exponentialSum]
  congr 1
  rw [← half_sum]
  apply sum_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (cosine_base_bounds (by omega) (by omega)).1]
  rfl

private lemma gap_variations {m j d : ℕ} (hj : 1 ≤ j) (hd : d = 1 ∨ d = 2)
    (hjdm : j + d ≤ m) : (List.ofFn (gapCoefficients m j d)).signVariations = j := by
  rw [show gapCoefficients m j d = (fun i : Fin m =>
      (fun l : ℕ => Real.sin (((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m) *
        Real.sin ((d : ℝ) * (l : ℝ) * angle m)) (i.val + 1)) from rfl,
    half_list m (fun l => Real.sin (((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m) *
      Real.sin ((d : ℝ) * (l : ℝ) * angle m))]
  exact gap_coefficients_signVariations hj hd hjdm

/-- The gaps of steps one and two have the same sign as their lower mode. -/
theorem modeValue_gap_sign {m j d : ℕ} (hj : 1 ≤ j) (hd : d = 1 ∨ d = 2)
    (hjdm : j + d ≤ m) (r : ℝ) :
    SignType.sign (modeValue m j r - modeValue m (j + d) r) =
      SignType.sign (rootProduct j r) := by
  have hm : 0 < m := by omega
  have hlead : 0 < gapCoefficients m j d ⟨0, hm⟩ := by
    have hb := gap_first_phase_bounds hj hd hjdm
    have h₁ := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
    have h₂ := gap_short_sine_pos hd (show 1 ≤ 1 by omega) (show 1 ≤ m by omega)
    simpa [gapCoefficients] using mul_pos h₁ h₂
  have hs := exact_sign (gapCoefficients m j d) (gapExponents m)
    (fun a b hab => exponents_strictAnti m (Fin.succ_lt_succ_iff.mpr hab))
    ⟨⟨0, hm⟩, hlead, by intro k hk; exact (Nat.not_lt_zero _ hk).elim⟩
    (zeros j) (by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
      have hz := modeValue_gap_even_eq_zero m j d s (mem_range.mp hs) hjdm
      rw [gap_expansion] at hz
      exact (mul_eq_zero.mp hz).resolve_left (by norm_num))
    (by rw [zeros_card, gap_variations hj hd hjdm]) r
  rw [gap_expansion, sign_mul, sign_pos (by norm_num : (0 : ℝ) < 4), one_mul,
    hs, zeros_product]

end D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns
