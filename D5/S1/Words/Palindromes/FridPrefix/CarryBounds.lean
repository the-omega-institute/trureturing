/- GID: D5/S1/Words/Palindromes/FridPrefix/CarryBounds
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/CarryBounds
   mirror-E: none(waiver:unbounded-carry-completeness)
   anchors: []
   utility: none
   digest: Successful signed Fibonacci carry paths remain in a complete finite integer box. -/

/-
proof_shape: content (complete_carry_box).
escape_witness: simultaneous expanding and contracting strip bounds at every carry prefix.
admission_basis: escape-witness.
Direct frozen dependencies: none; remaining dependencies are pinned Mathlib or this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Words.FridPrefix

open Real
open scoped goldenRatio

/-- The signed residual update when one most-significant Fibonacci digit is consumed. -/
def carryStep (s : ℤ × ℤ) (c : ℤ) : ℤ × ℤ := (s.2+c, s.1+s.2)

/-- A successful carry word of magnitude-two digits is complete in the finite box. -/
theorem complete_carry_box (before after : List ℤ)
    (hc : ∀ c ∈ before ++ after, |(c : ℝ)| ≤ 2)
    (hv : let t := (before ++ after).foldl carryStep (0,0); t.1+2*t.2=1) :
    let s := before.foldl carryStep (0,0);
    -4 ≤ s.1 ∧ s.1 ≤ 4 ∧ -3 ≤ s.2 ∧ s.2 ≤ 3 := by
  let alpha (s : ℤ × ℤ) : ℝ := (s.1 : ℝ)+(s.2 : ℝ)*φ
  let beta (s : ℤ × ℤ) : ℝ := (s.1 : ℝ)+(s.2 : ℝ)*ψ
  have phi_gt_three_halves : (3 / 2 : ℝ) < φ := by
    have hs : (2 : ℝ) < Real.sqrt 5 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    change 3 / 2 < (1 + Real.sqrt 5) / 2
    linarith

  have beta_step (x c : ℝ)
      (hx : |x| < 2 * (φ + 1)) (hc : |c| ≤ 2) :
      |ψ * x + c| < 2 * (φ + 1) := by
    have hp : 0 < φ - 1 := by linarith [Real.one_lt_goldenRatio]
    have habs : |ψ| = φ - 1 := by
      rw [abs_of_neg Real.goldenConj_neg]
      linarith [Real.goldenRatio_add_goldenConj]
    have hmul := mul_lt_mul_of_pos_left hx hp
    have htri := abs_add_le (ψ*x) c
    rw [abs_mul, habs] at htri
    nlinarith [Real.goldenRatio_sq]

  have alpha_back_step (x y c : ℝ)
      (hxy : y = φ * x + c)
      (hy : |y| < 2 * φ) (hc : |c| ≤ 2) :
      |x| < 2 * φ := by
    have htri : |y-c| ≤ |y|+|c| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le y (-c)
    have hrew : y - c = φ * x := by linarith
    rw [hrew, abs_mul, abs_of_pos Real.goldenRatio_pos] at htri
    have hbound : φ * |x| < φ * (2*φ) := by
      nlinarith [Real.goldenRatio_sq]
    exact lt_of_mul_lt_mul_left hbound (le_of_lt Real.goldenRatio_pos)

  have carry_box (a b : ℤ)
      (ha : |(a : ℝ) + (b : ℝ) * φ| < 2*φ)
      (hb : |(a : ℝ) + (b : ℝ) * ψ| < 2*(φ+1)) :
      -4 ≤ a ∧ a ≤ 4 ∧ -3 ≤ b ∧ b ≤ 3 := by
    rw [abs_lt] at ha hb
    have hp := phi_gt_three_halves
    have hpos : 0 < 2*φ-1 := by linarith
    have hconj : ψ = 1-φ := by linarith [Real.goldenRatio_add_goldenConj]
    rw [hconj] at hb
    have hbl : (-4 : ℝ) < (b : ℝ) := by
      by_contra h
      have hle : (b : ℝ) ≤ -4 := le_of_not_gt h
      have hm := mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hpos)
      nlinarith
    have hbu : (b : ℝ) < 4 := by
      by_contra h
      have hle : (4 : ℝ) ≤ (b : ℝ) := le_of_not_gt h
      have hm := mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hpos)
      nlinarith
    have hpa : 0 < φ-1 := by linarith
    have hupper₁ := mul_lt_mul_of_pos_left hb.2 Real.goldenRatio_pos
    have hupper₂ := mul_lt_mul_of_pos_left ha.2 hpa
    have hlower₁ := mul_lt_mul_of_pos_left hb.1 Real.goldenRatio_pos
    have hlower₂ := mul_lt_mul_of_pos_left ha.1 hpa
    have hal : (-5 : ℝ) < (a : ℝ) := by
      by_contra h
      have hle : (a : ℝ) ≤ -5 := le_of_not_gt h
      have hm := mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hpos)
      nlinarith [Real.goldenRatio_sq]
    have hau : (a : ℝ) < 5 := by
      by_contra h
      have hle : (5 : ℝ) ≤ (a : ℝ) := le_of_not_gt h
      have hm := mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hpos)
      nlinarith [Real.goldenRatio_sq]
    have hal' : (-5 : ℤ) < a := by exact_mod_cast hal
    have hau' : a < (5 : ℤ) := by exact_mod_cast hau
    have hbl' : (-4 : ℤ) < b := by exact_mod_cast hbl
    have hbu' : b < (4 : ℤ) := by exact_mod_cast hbu
    omega

  have terminal_alpha (a b : ℤ)
      (hvalue : a + 2*b = 1)
      (hb : |(a : ℝ)+(b : ℝ)*ψ| < 2*(φ+1)) :
      |(a : ℝ)+(b : ℝ)*φ| < 2*φ := by
    have hv : (a : ℝ) + 2*(b : ℝ) = 1 := by exact_mod_cast hvalue
    have hc : ψ = 1-φ := by linarith [Real.goldenRatio_add_goldenConj]
    rw [abs_lt, hc] at hb
    have hp := Real.goldenRatio_pos
    have hpos : 0 < φ+1 := by linarith
    have hbl : (-2 : ℝ) < (b : ℝ) := by
      by_contra h
      have hle : (b : ℝ) ≤ -2 := le_of_not_gt h
      have hm := mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hpos)
      nlinarith
    have hbu : (b : ℝ) < 3 := by
      by_contra h
      have hle : (3 : ℝ) ≤ (b : ℝ) := le_of_not_gt h
      have hm := mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hpos)
      nlinarith
    have hl : (-2 : ℤ) < b := by exact_mod_cast hbl
    have hu : b < (3 : ℤ) := by exact_mod_cast hbu
    have hphi := phi_gt_three_halves
    have hphi2 := Real.goldenRatio_lt_two
    have ha : a = 1-2*b := by omega
    rw [ha]
    interval_cases b
    all_goals norm_num
    all_goals first | (rw [abs_lt]; constructor <;> linarith) | linarith

  have alpha_step (s : (ℤ × ℤ)) (c : ℤ) :
      alpha (carryStep s c) = φ * alpha s + c := by
    simp only [alpha, carryStep, Int.cast_add]
    calc
      _ = φ*(s.1 : ℝ)+(s.2 : ℝ)*(φ+1)+(c : ℝ) := by ring
      _ = _ := by rw [← Real.goldenRatio_sq]; ring

  have beta_step_eq (s : (ℤ × ℤ)) (c : ℤ) :
      beta (carryStep s c) = ψ * beta s + c := by
    simp only [beta, carryStep, Int.cast_add]
    calc
      _ = ψ*(s.1 : ℝ)+(s.2 : ℝ)*(ψ+1)+(c : ℝ) := by ring
      _ = _ := by rw [← Real.goldenConj_sq]; ring

  have beta_fold (s : (ℤ × ℤ)) (cs : List ℤ)
      (hs : |beta s| < 2*(φ+1))
      (hc : ∀ c ∈ cs, |(c : ℝ)| ≤ 2) :
      |beta (cs.foldl carryStep s)| < 2*(φ+1) := by
    induction cs generalizing s with
    | nil => simpa using hs
    | cons c cs ih =>
        simp only [List.foldl_cons]
        apply ih
        · rw [beta_step_eq]
          exact beta_step (beta s) c hs (hc c (by simp))
        · intro d hd
          exact hc d (by simp [hd])

  have alpha_fold_back (s : (ℤ × ℤ)) (cs : List ℤ)
      (hc : ∀ c ∈ cs, |(c : ℝ)| ≤ 2)
      (hf : |alpha (cs.foldl carryStep s)| < 2*φ) :
      |alpha s| < 2*φ := by
    induction cs generalizing s with
    | nil => simpa using hf
    | cons c cs ih =>
        have hb : |alpha (carryStep s c)| < 2*φ :=
          ih (carryStep s c) (fun d hd => hc d (by simp [hd])) (by simpa using hf)
        exact alpha_back_step (alpha s) (alpha (carryStep s c)) c
          (alpha_step s c) hb (hc c (by simp))

  let s := before.foldl carryStep (0,0)
  let t := after.foldl carryStep s
  have hb0 : |beta (0,0)| < 2*(φ+1) := by
    simp only [beta, Int.cast_zero, zero_mul, zero_add, abs_zero]
    linarith [Real.goldenRatio_pos]
  have hbefore : ∀ c ∈ before, |(c : ℝ)| ≤ 2 :=
    fun c h => hc c (List.mem_append_left _ h)
  have hafter : ∀ c ∈ after, |(c : ℝ)| ≤ 2 :=
    fun c h => hc c (List.mem_append_right _ h)
  have hbs : |beta s| < 2*(φ+1) := beta_fold _ before hb0 hbefore
  have hbt : |beta t| < 2*(φ+1) := beta_fold _ after hbs hafter
  have ht : t = (before ++ after).foldl carryStep (0,0) := by
    simp [t,s,List.foldl_append]
  have hv' : t.1+2*t.2=1 := by simpa only [ht] using hv
  have hat : |alpha t| < 2*φ := terminal_alpha t.1 t.2 hv' hbt
  have has : |alpha s| < 2*φ := alpha_fold_back _ after hafter hat
  exact carry_box s.1 s.2 has hbs


end D5.S1.Words.FridPrefix
