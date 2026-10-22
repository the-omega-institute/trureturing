/- GID: D5/S3/Analytic/GaussZeroBalanced/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The two sharp classifications for the zero-balanced Gauss quotient. -/

import D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
import Mathlib.Tactic

noncomputable section
open Set
open D5.S3.Analytic.GaussZeroBalanced.Defs
open D5.S3.Analytic.GaussZeroBalanced.Series
open D5.S3.Analytic.GaussZeroBalanced.Comparison
open D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
namespace D5.S3.Analytic.GaussZeroBalanced.Result

private theorem comparison_f {a b₁ b₂ : ℝ} (ha : 0 < a) (hb₁ : 0 < b₁)
    (hb : b₁ < b₂) :
    (∀ x ∈ Ioo (0:ℝ) 1, f a b₂ x < f a b₁ x) ↔ b₁*b₂ ≤ a*(a+1) := by
  have hb₂ : 0 < b₂ := hb₁.trans hb
  have hc₁ : a+b₁ ≠ 0 := by positivity
  have hc₂ : a+b₂ ≠ 0 := by positivity
  let w := fun x : ℝ => f a b₁ x - f a b₂ x
  have hw0 : w 0 = 0 := by simp [w, f_zero]
  have hwder (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
      HasDerivAt w (deriv (f a b₁) x - deriv (f a b₂) x) x :=
    (hasDerivAt_f ha hb₁ hx hx1).differentiableAt.hasDerivAt.sub
      (hasDerivAt_f ha hb₂ hx hx1).differentiableAt.hasDerivAt
  constructor
  · intro hgt
    have hmin : IsMinOn w (Icc (0:ℝ) (1/2)) 0 := by
      intro z hz
      rw [hw0]
      rcases eq_or_lt_of_le hz.1 with (rfl | hz0)
      · exact hw0.ge
      · exact (sub_pos.mpr (hgt z ⟨hz0, by linarith [hz.2]⟩)).le
    have ht : (1/2:ℝ)-0 ∈ posTangentConeAt (Icc (0:ℝ) (1/2)) 0 := by
      apply sub_mem_posTangentConeAt_of_segment_subset
      rw [segment_eq_Icc (by norm_num : (0:ℝ) ≤ 1/2)]
    have hd := hwder 0 (by norm_num) (by norm_num)
    rw [deriv_f_zero ha hb₁, deriv_f_zero ha hb₂] at hd
    have hn := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
      hd.hasFDerivAt.hasFDerivWithinAt ht
    have hn' : 0 ≤ (-a*b₁/((a+b₁)*(a+b₁+1)) +
        a*b₂/((a+b₂)*(a+b₂+1))) * (1/2:ℝ) := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm, neg_div,
        sub_eq_add_neg, mul_assoc] using hn
    have heq : -a*b₁/((a+b₁)*(a+b₁+1)) + a*b₂/((a+b₂)*(a+b₂+1)) =
        a*(b₂-b₁)*(a*(a+1)-b₁*b₂) /
          ((a+b₁)*(a+b₂)*(a+b₁+1)*(a+b₂+1)) := by
      have hc₁' : a+b₁+1 ≠ 0 := by positivity
      have hc₂' : a+b₂+1 ≠ 0 := by positivity
      field_simp
      <;> ring
    rw [heq] at hn'
    by_contra hbad
    have hneg : a*(b₂-b₁)*(a*(a+1)-b₁*b₂) /
        ((a+b₁)*(a+b₂)*(a+b₁+1)*(a+b₂+1)) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
        (mul_pos ha (sub_pos.mpr hb)) (sub_neg.mpr (lt_of_not_ge hbad))) (by positivity)
    nlinarith
  · intro hthreshold x hx
    let R : ℝ := (x+1)/2
    let P := fun z : ℝ => (a+b₁) + (a*b₁/(a+b₁))*(z/(1-z))*(f a b₁ z+f a b₂ z)
    have hR0 : 0 < R := by dsimp [R]; linarith [hx.1]
    have hR1 : R < 1 := by dsimp [R]; linarith [hx.2]
    have hxR : x ∈ Ioo (0:ℝ) R := ⟨hx.1, by dsimp [R]; linarith [hx.2]⟩
    have hq : a*b₂/((a+b₂)*(a+b₂+1)) ≤ a^2/((a+b₁)*(a+b₂)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (a+b₂)*(a+b₂+1))
        (by positivity : 0 < (a+b₁)*(a+b₂))).2
      nlinarith only [mul_nonneg (show 0 ≤ a*(a+b₂) by positivity) (sub_nonneg.mpr hthreshold)]
    have hk : a*b₂/(a+b₂) - a*b₁/(a+b₁) =
        (b₂-b₁)*a^2/((a+b₁)*(a+b₂)) := by
      field_simp
      <;> ring
    have hcont : ContinuousOn w (Icc 0 R) := by
      apply ((continuousOn_f ha hb₁).sub (continuousOn_f ha hb₂)).mono
      intro z hz
      exact ⟨hz.1, hz.2.trans_lt hR1⟩
    have hd : ∀ z ∈ Ioo (0:ℝ) R, HasDerivAt w (deriv w z) z := by
      intro z hz
      exact (hwder z hz.1.le (hz.2.trans hR1)).differentiableAt.hasDerivAt
    have hP : ∀ z ∈ Ioo (0:ℝ) R, 0 < P z := by
      intro z hz
      have hf₁ := f_pos ha hb₁ hz.1.le (hz.2.trans hR1)
      have hf₂ := f_pos ha hb₂ hz.1.le (hz.2.trans hR1)
      have ht : 0 < z/(1-z) := div_pos hz.1 (by linarith [hz.2.trans hR1])
      dsimp [P]
      positivity
    have hi : ∀ z ∈ Ioo (0:ℝ) R, 0 < z*deriv w z + P z*w z := by
      intro z hz
      have hz1 := hz.2.trans hR1
      have hf := f_pos ha hb₂ hz.1.le hz1
      have ht : 0 < (z/(1-z))*(f a b₂ z)^2 := by
        have : 0 < z/(1-z) := div_pos hz.1 (by linarith)
        positivity
      have hstrict := (div_lt_iff₀ ht).1 ((certificate ha hb₂ ⟨hz.1, hz1⟩).trans_le hq)
      have h₁ := riccati ha hb₁ hz.1 hz1
      have h₂ := riccati ha hb₂ hz.1 hz1
      have hid : z*deriv w z + P z*w z =
          (b₂-b₁)*(a^2/((a+b₁)*(a+b₂))*(z/(1-z))*(f a b₂ z)^2 - (1-f a b₂ z)) := by
        rw [(hwder z hz.1.le hz1).deriv]
        dsimp [P, w]
        linear_combination h₁ - h₂ + ((z/(1-z))*(f a b₂ z)^2)*hk
      rw [hid]
      apply mul_pos (sub_pos.mpr hb)
      nlinarith only [hstrict]
    have hp := singular_comparison hR0 hw0 hcont hd hP hi x hxR
    exact sub_pos.mp hp

private theorem clause2_local (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (∀ r ∈ Ioo (0:ℝ) 1, ineq17 a r) ↔ 3/7 ≤ a := by
  have hb₁ : 0 < 1-a := by linarith
  have hb₂ : 0 < 3/2-a := by linarith
  have hsame (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
      ineq17 a r ↔ f a (3/2-a) r < f a (1-a) r := by
    have h₁ := quot_eq ha hb₁ hr.1.le hr.2
    have h₂ := quot_eq ha hb₂ hr.1.le hr.2
    have heq₁ : quot a (1-a) r =
        gauss (a+1) (2-a) 2 r / gauss a (1-a) 1 r := by
      unfold quot
      congr 1 <;> congr 1 <;> ring
    have heq₂ : quot a (3/2-a) r =
        gauss (a+1) (5/2-a) (5/2) r / gauss a (3/2-a) (3/2) r := by
      unfold quot
      congr 1 <;> congr 1 <;> ring
    unfold ineq17
    rw [← heq₁, ← heq₂, h₁, h₂]
    exact div_lt_div_iff_of_pos_right (by linarith [hr.2] : 0 < 1-r)
  have heq : (∀ r ∈ Ioo (0:ℝ) 1, ineq17 a r) ↔
      (∀ r ∈ Ioo (0:ℝ) 1, f a (3/2-a) r < f a (1-a) r) := by
    constructor <;> intro h r hr
    · exact (hsame r hr).1 (h r hr)
    · exact (hsame r hr).2 (h r hr)
  rw [heq, comparison_f ha hb₁ (by linarith : 1-a < 3/2-a)]
  constructor <;> intro h <;> nlinarith

/-- The sharp parameter classifications of the zero-balanced Gauss quotient. -/
theorem result : claim := ⟨clause1, clause2_local⟩

end D5.S3.Analytic.GaussZeroBalanced.Result
