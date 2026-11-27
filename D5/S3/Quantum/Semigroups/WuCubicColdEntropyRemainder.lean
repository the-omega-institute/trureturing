/- GID: D5/S3/Quantum/Semigroups/WuCubicColdEntropyRemainder
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed cubic entropy remainder through zero support. -/

import D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-! The signed entropy estimate in the cold Wu cubic proof, including rank drop. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open Set
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicColdEntropyRemainder

private def logGap (y : ℝ) : ℝ :=
  y / 3 + 1 / 2 - y⁻¹ + (y⁻¹) ^ 2 / 6 - Real.log y

private theorem hasDerivAt_logGap {y : ℝ} (hy : 0 < y) :
    HasDerivAt logGap ((y - 1) ^ 3 / (3 * y ^ 3)) y := by
  have hinv := hasDerivAt_inv hy.ne'
  unfold logGap
  convert ((((hasDerivAt_id' y).div_const 3).add_const (1 / 2)).sub hinv
    |>.add ((hinv.pow 2).div_const 6)).sub (Real.hasDerivAt_log hy.ne') using 1
  field_simp [hy.ne']
  ring_nf
  rw [mul_inv_cancel₀ hy.ne']
  ring

private theorem logGap_pos {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) : 0 < logGap y := by
  have hone : logGap 1 = 0 := by norm_num [logGap, Real.log_one]
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · have hanti : StrictAntiOn logGap (Icc y 1) :=
      strictAntiOn_of_deriv_neg (convex_Icc _ _)
        (fun z hz => (hasDerivAt_logGap (hy.trans_le hz.1)).continuousAt.continuousWithinAt)
        (by
          rw [interior_Icc]
          intro z hz
          have hzpos := hy.trans hz.1
          rw [(hasDerivAt_logGap hzpos).deriv]
          exact div_neg_of_neg_of_pos ((by decide : Odd 3).pow_neg (sub_neg.mpr hz.2))
            (by positivity))
    rw [← hone]
    exact hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  · have hmono : StrictMonoOn logGap (Icc 1 y) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (fun z hz =>
          (hasDerivAt_logGap (zero_lt_one.trans_le hz.1)).continuousAt.continuousWithinAt)
        (by
          rw [interior_Icc]
          intro z hz
          have hzpos := zero_lt_one.trans hz.1
          rw [(hasDerivAt_logGap hzpos).deriv]
          exact div_pos (pow_pos (sub_pos.mpr hz.1) 3) (by positivity))
    rw [← hone]
    exact hmono ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt

/-- The signed quartic Taylor bound holds through zero support, with equality
exactly at zero and at the positive reference root. -/
theorem cubic_entropy_remainder_le_and_eq_iff {g x : ℝ} (hg : 0 < g) (hx : 0 ≤ x) :
    let F := x ^ 3 * Real.log (x ^ 3 / g ^ 3) - x ^ 3 + g ^ 3
    let P := (9 / 2) * g * (x - g) ^ 2 + (9 / 2) * (x - g) ^ 3 + (x - g) ^ 4 / g
    F ≤ P ∧ (F = P ↔ x = 0 ∨ x = g) := by
  dsimp only
  by_cases hx0 : x = 0
  · subst x
    have hpow : (-g) ^ 4 / g = g ^ 3 := by field_simp [hg.ne']
    have heq :
        (0 : ℝ) ^ 3 * Real.log (0 ^ 3 / g ^ 3) - 0 ^ 3 + g ^ 3 =
          (9 / 2) * g * (0 - g) ^ 2 + (9 / 2) * (0 - g) ^ 3 + (0 - g) ^ 4 / g := by
      simp only [zero_sub, hpow]
      ring
    exact ⟨heq.le, iff_of_true heq (Or.inl rfl)⟩
  by_cases hxg : x = g
  · subst x
    simp [hg.ne']
  let y := x / g
  have hy : 0 < y := div_pos (lt_of_le_of_ne hx (Ne.symm hx0)) hg
  have hgy : g * y = x := by
    dsimp [y]
    field_simp [hg.ne']
  have hy1 : y ≠ 1 := by
    intro h
    exact hxg (by simpa [h] using hgy.symm)
  have hgap :
      (9 / 2) * g * (x - g) ^ 2 + (9 / 2) * (x - g) ^ 3 + (x - g) ^ 4 / g -
        (x ^ 3 * Real.log (x ^ 3 / g ^ 3) - x ^ 3 + g ^ 3) =
      3 * g ^ 3 * y ^ 3 * logGap y := by
    have hlog : Real.log (x ^ 3 / g ^ 3) = 3 * Real.log y := by
      rw [← div_pow, Real.log_pow]
      norm_num [y]
    rw [hlog, ← hgy]
    unfold logGap
    field_simp [hg.ne', hy.ne']
    ring
  have hstrict := sub_pos.mp (hgap.symm ▸
    mul_pos (by positivity : 0 < 3 * g ^ 3 * y ^ 3) (logGap_pos hy hy1))
  exact ⟨hstrict.le, iff_of_false hstrict.ne (not_or_intro hx0 hxg)⟩

/-- Below the reference root, the quartic error is absorbed into the signed
cubic term. -/
theorem cubic_entropy_remainder_le_of_le {g x : ℝ}
    (hg : 0 < g) (hx : 0 ≤ x) (hxg : x ≤ g) :
    x ^ 3 * Real.log (x ^ 3 / g ^ 3) - x ^ 3 + g ^ 3 ≤
      (9 / 2) * g * (x - g) ^ 2 + (7 / 2) * (x - g) ^ 3 := by
  have hquartic : (x - g) ^ 4 / g ≤ -((x - g) ^ 3) := by
    apply (div_le_iff₀ hg).2
    nlinarith only [mul_nonneg hx (pow_nonneg (sub_nonneg.mpr hxg) 3)]
  linarith only [(cubic_entropy_remainder_le_and_eq_iff hg hx).1, hquartic]

#print axioms cubic_entropy_remainder_le_and_eq_iff
#print axioms cubic_entropy_remainder_le_of_le

open WuCubicOccupationTaylor (occupationFrame gibbsLevels cubicMass occupationEnergyFactor
  occupationEdgeSum occupationEntropy occupation_source_deficit_eq occupation_entropy_eq_remainders
  alpha_bounds_of_one_le)
open WuCubicSignedTransfer (sourceDeficitAt)
open WuRepeatedMiddleCubic (alpha)
open private gamma energyKernel from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private levelsAt totalAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

private def entropyWeight (w : ℝ) : ℝ := 9 / 2 + (9 / 2) * w + w ^ 2

private theorem scaled_remainder_le {g w : ℝ} (hg : 0 < g) (hw : -1 ≤ w) :
    3 * (g * (1 + w)) ^ 3 * Real.log (g * (1 + w) / g) -
        ((g * (1 + w)) ^ 3 - g ^ 3) ≤ g ^ 3 * w ^ 2 * entropyWeight w := by
  have h := (cubic_entropy_remainder_le_and_eq_iff hg
    (mul_nonneg hg.le (by linarith : 0 ≤ 1 + w))).1
  rw [← div_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1
  · ring
  · unfold entropyWeight
    field_simp [hg.ne']
    ring

private theorem cold_alpha_bound {r : ℝ} (hr : 4 ≤ r) :
    alpha r * (r⁻¹) ^ 3 ≤ gamma r / 4 := by
  have hr0 : 0 < r := by linarith
  have hlog : 4 / 3 ≤ Real.log r := by
    have h4 : (4 / 3 : ℝ) ≤ Real.log 4 := by
      rw [Real.log_four_eq]
      linarith only [Real.log_two_gt_d9]
    exact h4.trans (Real.log_le_log (by norm_num) hr)
  have hlog0 : 0 < Real.log r := by linarith
  have hpoly : 0 < r ^ 2 + r + 1 := by positivity
  have hden : 0 < r ^ 3 * (r ^ 2 + r + 1) := by positivity
  have hratio : (1 + r ^ 3) * (r ^ 2 - 1) / (r ^ 3 * (r ^ 2 + r + 1)) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
    nlinarith only [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr2), pow_nonneg hr0.le 3]
  have hγ : 0 < gamma r := by unfold gamma; positivity
  calc
    alpha r * (r⁻¹) ^ 3 =
        (gamma r / (3 * Real.log r)) *
          ((1 + r ^ 3) * (r ^ 2 - 1) / (r ^ 3 * (r ^ 2 + r + 1))) := by
      rw [alpha, ite_eq_right (show r ≠ 1 by linarith)]
      unfold gamma
      have hadd : 0 < 1 + r ^ 3 := by positivity
      field_simp [hr0.ne', hlog0.ne', hpoly.ne', hadd.ne']
      ring
    _ ≤ (gamma r / (3 * Real.log r)) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ gamma r / 4 := by
      rw [mul_one]
      exact div_le_div_of_nonneg_left hγ.le (by norm_num) (by linarith)

private theorem cold_edge_bound {γ a t y z : ℝ} (hγ : 0 ≤ γ)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 64) (ha : a * t ≤ γ / 4)
    (hy : y ∈ Icc (-1 : ℝ) (1 / 4)) (hz : z ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    γ * ((7 / 16) * t * y ^ 2 + (27 / 128) * z ^ 2) ≤
      γ * (t * (y - z) ^ 2 * (2 + y + z) + z ^ 2 * (2 + z)) -
        a * t * (t * y ^ 2 * entropyWeight y / 2 + z ^ 2 * entropyWeight z) := by
  have hfy : 0 ≤ entropyWeight y := by
    unfold entropyWeight
    nlinarith only [hy.1, sq_nonneg y]
  have hfz : 0 ≤ entropyWeight z := by
    unfold entropyWeight
    nlinarith only [hz.1, sq_nonneg z]
  have hfzmax : entropyWeight z ≤ 91 / 16 := by
    unfold entropyWeight
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz.2) (show 0 ≤ 19 / 4 + z by linarith [hz.1])]
  have hmix : t * ((3 / 4) * y ^ 2 * (7 / 4 + y) - (15 / 2) * z ^ 2) ≤
      t * (y - z) ^ 2 * (2 + y + z) := by
    have hsq : (3 / 4) * y ^ 2 - 3 * z ^ 2 ≤ (y - z) ^ 2 := by
      nlinarith only [sq_nonneg (y / 2 - 2 * z)]
    have hprod := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 2 + y + z by linarith [hy.1, hz.1])
    have hl := mul_le_mul_of_nonneg_left (show 7 / 4 + y ≤ 2 + y + z by linarith [hz.1])
      (show 0 ≤ (3 / 4) * y ^ 2 by positivity)
    have hu := mul_le_mul_of_nonneg_left (show 2 + y + z ≤ 5 / 2 by linarith [hy.2, hz.2])
      (show 0 ≤ 3 * z ^ 2 by positivity)
    have h := mul_le_mul_of_nonneg_left (show
      (3 / 4) * y ^ 2 * (7 / 4 + y) - (15 / 2) * z ^ 2 ≤ (y - z) ^ 2 * (2 + y + z) by
        nlinarith only [hprod, hl, hu]) ht
    nlinarith only [h]
  have hcoefY : (7 / 16 : ℝ) ≤ (3 / 4) * (7 / 4 + y) - entropyWeight y / 8 := by
    unfold entropyWeight
    nlinarith only [mul_nonneg (show 0 ≤ y + 1 by linarith [hy.1])
      (show 0 ≤ 5 / 8 - y / 4 by linarith [hy.2])]
  have hcoefZ : (27 / 128 : ℝ) ≤ 2 + z - entropyWeight z / 4 - (15 / 2) * t := by
    linarith only [hz.1, hfzmax, htmax]
  have hY := mul_le_mul_of_nonneg_right hcoefY (mul_nonneg ht (sq_nonneg y))
  have hZ := mul_le_mul_of_nonneg_right hcoefZ (sq_nonneg z)
  have hlocal := mul_le_mul_of_nonneg_left (show
      (7 / 16) * t * y ^ 2 + (27 / 128) * z ^ 2 ≤
        t * (y - z) ^ 2 * (2 + y + z) + z ^ 2 * (2 + z) -
          (1 / 4) * (t * y ^ 2 * entropyWeight y / 2 + z ^ 2 * entropyWeight z) by
    nlinarith only [hmix, hY, hZ]) hγ
  have hthermal := mul_le_mul_of_nonneg_right ha (show
      0 ≤ t * y ^ 2 * entropyWeight y / 2 + z ^ 2 * entropyWeight z by positivity)
  nlinarith only [hlocal, hthermal]

/-- The anisotropic cold bound for the actual occupation frame, including a
zero vacuum level. The other two variable levels lie within one quarter of
their Gibbs levels in relative coordinates. -/
theorem occupation_deficit_ge {r y z₁ z₂ : ℝ} (hr : 4 ≤ r)
    (hy : y ∈ Icc (-1 : ℝ) (1 / 4))
    (hz₁ : z₁ ∈ Icc (-1 / 4 : ℝ) (1 / 4)) (hz₂ : z₂ ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    let u := r⁻¹
    (9 / (4 * (1 + r ^ 3))) * ((7 / 8) * u ^ 3 * y ^ 2 +
        (27 / 128) * (z₁ ^ 2 + z₂ ^ 2)) ≤
      sourceDeficitAt r occupationFrame (u ^ 2 * (1 + y)) (u * (1 + z₁)) (u * (1 + z₂)) := by
  let u := r⁻¹
  change gamma r * _ ≤ _
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hu : 0 < u := inv_pos.mpr hr0
  have htmax : u ^ 3 ≤ 1 / 64 := by
    have hu4 : u ≤ 1 / 4 := (inv_le_iff_one_le_mul₀ hr0).2 (by linarith)
    exact (pow_le_pow_left₀ hu.le hu4 3).trans (by norm_num)
  have hγ : 0 ≤ gamma r := by unfold gamma; positivity
  have ha := (alpha_bounds_of_one_le hr1).1
  have hthermal : alpha r * u ^ 3 ≤ gamma r / 4 := cold_alpha_bound hr
  refine le_on_closure (s := Ioc (-1 : ℝ) (1 / 4))
    (f := fun w => gamma r * ((7 / 8) * u ^ 3 * w ^ 2 + (27 / 128) * (z₁ ^ 2 + z₂ ^ 2)))
    (g := fun w => sourceDeficitAt r occupationFrame (u ^ 2 * (1 + w))
      (u * (1 + z₁)) (u * (1 + z₂))) ?_ ?_ ?_ ?_
  · intro w hw
    let x : Fin 4 → ℝ := ![u ^ 2 * (1 + w), u * (1 + z₁), u * (1 + z₂), 1]
    let h : Fin 4 → ℝ := ![u ^ 2 * w, u * z₁, u * z₂, 0]
    have hadd (i : Fin 4) : gibbsLevels r i + (1 : ℝ) * h i = x i := by
      fin_cases i <;> simp [gibbsLevels, h, x, u, inv_pow] <;> ring
    have hx (i : Fin 4) : 0 < x i := by
      have hw0 : 0 < 1 + w := by linarith [hw.1]
      have hz₁0 : 0 < 1 + z₁ := by linarith [hz₁.1]
      have hz₂0 : 0 < 1 + z₂ := by linarith [hz₂.1]
      fin_cases i <;> simp [x] <;> positivity
    have hsource := occupation_source_deficit_eq (d := 1) hr1 h
      (by simp [h]) (fun i => by rw [hadd]; exact hx i)
    simp only [hadd] at hsource
    simp only [one_pow, one_mul] at hsource
    have hrU : r * u = 1 := mul_inv_cancel₀ hr0.ne'
    have hrU2 : r * u ^ 2 = u := by linear_combination u * hrU
    have henergy :
        occupationEnergyFactor r 1 h = gamma r *
          (u ^ 3 * ((w - z₁) ^ 2 * (2 + w + z₁) + (w - z₂) ^ 2 * (2 + w + z₂)) +
            z₁ ^ 2 * (2 + z₁) + z₂ ^ 2 * (2 + z₂)) := by
      simp [occupationEnergyFactor, occupationEdgeSum, h, gibbsLevels, ← mul_assoc, hrU, hrU2]
      left
      ring
    have hmassX : 0 < cubicMass x :=
      Finset.sum_pos (fun i _ => pow_pos (hx i) 3) Finset.univ_nonempty
    have hmassG : 0 < cubicMass (gibbsLevels r) := by
      have hpos (i : Fin 4) : 0 < gibbsLevels r i := by
        fin_cases i <;> simp [gibbsLevels] <;> positivity
      exact Finset.sum_pos (fun i _ => pow_pos (hpos i) 3) Finset.univ_nonempty
    have hmass : 0 ≤ cubicMass x * Real.log (cubicMass x / cubicMass (gibbsLevels r)) -
        (cubicMass x - cubicMass (gibbsLevels r)) := by
      have hkl := mul_nonneg hmassG.le (InformationTheory.klFun_nonneg
        (div_nonneg hmassX.le hmassG.le))
      unfold InformationTheory.klFun at hkl
      rw [mul_sub, mul_add, ← mul_assoc, mul_div_cancel₀ _ hmassG.ne'] at hkl
      linarith only [hkl]
    have hent : occupationEntropy r x ≤
        u ^ 6 * w ^ 2 * entropyWeight w +
          u ^ 3 * (z₁ ^ 2 * entropyWeight z₁ + z₂ ^ 2 * entropyWeight z₂) := by
      let rem (q g : ℝ) := 3 * q ^ 3 * Real.log (q / g) - (q ^ 3 - g ^ 3)
      let massRem := cubicMass x * Real.log (cubicMass x / cubicMass (gibbsLevels r)) -
        (cubicMass x - cubicMass (gibbsLevels r))
      have hform : occupationEntropy r x =
          (∑ i, rem (x i) (gibbsLevels r i)) - massRem :=
        occupation_entropy_eq_remainders hr1 x hx
      have hg0 : gibbsLevels r 0 = u ^ 2 := (inv_pow r 2).symm
      rw [hform, Fin.sum_univ_four, hg0]
      change rem (u ^ 2 * (1 + w)) (u ^ 2) + rem (u * (1 + z₁)) u +
        rem (u * (1 + z₂)) u + rem 1 1 - massRem ≤ _
      have h₃ : rem 1 1 = 0 := by norm_num [rem]
      rw [h₃, add_zero]
      have h₀ := scaled_remainder_le (pow_pos hu 2) hw.1.le
      have h₁ := scaled_remainder_le hu (show -1 ≤ z₁ by linarith [hz₁.1])
      have h₂ := scaled_remainder_le hu (show -1 ≤ z₂ by linarith [hz₂.1])
      dsimp only [rem, massRem]
      nlinarith only [hmass, h₀, h₁, h₂]
    have h₁ := cold_edge_bound hγ (pow_nonneg hu.le 3) htmax hthermal ⟨hw.1.le, hw.2⟩ hz₁
    have h₂ := cold_edge_bound hγ (pow_nonneg hu.le 3) htmax hthermal ⟨hw.1.le, hw.2⟩ hz₂
    change gamma r * _ ≤ sourceDeficitAt r occupationFrame (x 0) (x 1) (x 2)
    rw [hsource, henergy]
    nlinarith only [h₁, h₂, mul_le_mul_of_nonneg_left hent ha]
  · exact (by fun_prop : Continuous
      (fun w : ℝ => gamma r * ((7 / 8) * u ^ 3 * w ^ 2 +
        (27 / 128) * (z₁ ^ 2 + z₂ ^ 2)))).continuousOn
  · apply Continuous.continuousOn
    unfold sourceDeficitAt levelsAt totalAt energyKernel
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    fun_prop
  · rw [closure_Ioc (by norm_num : (-1 : ℝ) ≠ 1 / 4)]
    exact hy

#print axioms occupation_deficit_ge

end D5.S3.Quantum.Semigroups.WuCubicColdEntropyRemainder
