/- GID: D5/S3/Fourier/WeightedIntegerRelations
   generality: G
   mirror-B: D5/B/S3/Fourier/WeightedIntegerRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Circle]
   utility: none
   digest: Integer characters give weighted lower bounds for the finite sine phase deficit. -/

import D5.S3.AnalyticClosure.ComplexPowerDifference
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Chord bounds on finite products of unit circles and their quarter-phase specialization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexConjugate

namespace D5.S3.Fourier.WeightedIntegerRelations

private theorem chord_mul (a b x y : Circle) :
    ‖((a * b : Circle) : ℂ) - ((x * y : Circle) : ℂ)‖ ≤
      ‖(a : ℂ) - (x : ℂ)‖ + ‖(b : ℂ) - (y : ℂ)‖ := by
  simp only [Circle.coe_mul]
  calc
    _ = ‖((a : ℂ) - x) * (b : ℂ) + (x : ℂ) * ((b : ℂ) - y)‖ := by
      congr 1
      ring
    _ ≤ _ := by
      simpa only [norm_mul, Circle.norm_coe, one_mul, mul_one] using
        norm_add_le (((a : ℂ) - x) * (b : ℂ)) ((x : ℂ) * ((b : ℂ) - y))

private theorem chord_zpow (a b : Circle) (k : ℤ) :
    ‖((a ^ k : Circle) : ℂ) - ((b ^ k : Circle) : ℂ)‖ ≤
      |(k : ℝ)| * ‖(a : ℂ) - (b : ℂ)‖ := by
  have hpow (n : ℕ) : ‖((a ^ n : Circle) : ℂ) - ((b ^ n : Circle) : ℂ)‖ ≤
      (n : ℝ) * ‖(a : ℂ) - (b : ℂ)‖ := by
    simpa only [Circle.coe_pow, one_pow, mul_one] using
      D5.S3.AnalyticClosure.ComplexPowerDifference.norm_pow_sub_pow_le
        (a : ℂ) (b : ℂ) n 1 zero_le_one a.norm_coe.le b.norm_coe.le
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  cases k with
  | ofNat n =>
    change ‖((a ^ (n : ℤ) : Circle) : ℂ) - ((b ^ (n : ℤ) : Circle) : ℂ)‖ ≤
      (n : ℝ) * ‖(a : ℂ) - (b : ℂ)‖
    simpa only [zpow_natCast] using hpow n
  | negSucc n =>
    simpa only [zpow_negSucc, Circle.coe_inv_eq_conj, ← map_sub, Complex.norm_conj,
      Int.natAbs_negSucc] using hpow (n + 1)

/-- The chordal displacement of a finite integer character is controlled coordinatewise. -/
theorem chord_prod_zpow {J : Type*} (columns : Finset J) (z q : J → Circle) (k : J → ℤ) :
    ‖((∏ j ∈ columns, z j ^ k j : Circle) : ℂ) -
      ((∏ j ∈ columns, q j ^ k j : Circle) : ℂ)‖ ≤
      ∑ j ∈ columns, |(k j : ℝ)| * ‖(z j : ℂ) - (q j : ℂ)‖ := by
  have hprod := columns.apply_prod_le_sum_apply
    (f := fun j => (z j ^ k j, q j ^ k j))
    (fun p : Circle × Circle => ‖(p.1 : ℂ) - (p.2 : ℂ)‖)
    (by simp) (fun a b => chord_mul a.1 b.1 a.2 b.2)
  exact (by simpa only [Prod.fst_prod, Prod.snd_prod] using hprod :
    _ ≤ ∑ j ∈ columns, ‖((z j ^ k j : Circle) : ℂ) - ((q j ^ k j : Circle) : ℂ)‖).trans
    (Finset.sum_le_sum fun j _ => chord_zpow (z j) (q j) (k j))

/-- A simultaneous bound for arbitrary two phase vectors, with overlapping rows. -/
theorem weighted_character_chord {J A : Type*} (columns : Finset J) (rows : Finset A)
    (z q : J → Circle) (w : J → ℝ) (k : A → J → ℤ) (lam : A → ℝ)
    (hw : ∀ j ∈ columns, 0 < w j) (hlam : ∀ a ∈ rows, 0 ≤ lam a) :
    (∑ a ∈ rows, lam a *
      ‖((∏ j ∈ columns, z j ^ k a j : Circle) : ℂ) -
        ((∏ j ∈ columns, q j ^ k a j : Circle) : ℂ)‖) ^ 2 ≤
      (∑ j ∈ columns, (∑ a ∈ rows, lam a * |(k a j : ℝ)|) ^ 2 / w j) *
        ∑ j ∈ columns, w j * ‖(z j : ℂ) - (q j : ℂ)‖ ^ 2 := by
  let load (j : J) := ∑ a ∈ rows, lam a * |(k a j : ℝ)|
  let chord (j : J) := ‖(z j : ℂ) - (q j : ℂ)‖
  let total := ∑ a ∈ rows, lam a *
    ‖((∏ j ∈ columns, z j ^ k a j : Circle) : ℂ) -
      ((∏ j ∈ columns, q j ^ k a j : Circle) : ℂ)‖
  have htotal : 0 ≤ total :=
    Finset.sum_nonneg fun a ha => mul_nonneg (hlam a ha) (norm_nonneg _)
  have hload : total ≤ ∑ j ∈ columns, load j * chord j := calc
    total ≤ ∑ a ∈ rows, lam a * ∑ j ∈ columns, |(k a j : ℝ)| * chord j :=
      Finset.sum_le_sum fun a ha =>
        mul_le_mul_of_nonneg_left (chord_prod_zpow columns z q (k a)) (hlam a ha)
    _ = ∑ j ∈ columns, load j * chord j := by
      simp_rw [load, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
      rw [Finset.sum_comm]
  change total ^ 2 ≤ (∑ j ∈ columns, load j ^ 2 / w j) *
    ∑ j ∈ columns, w j * chord j ^ 2
  refine (pow_le_pow_left₀ htotal hload 2).trans
    (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul columns
      (fun j hj => div_nonneg (sq_nonneg _) (hw j hj).le)
      (fun j hj => mul_nonneg (hw j hj).le (sq_nonneg _)) ?_)
  intro j hj
  rw [mul_pow, ← mul_assoc, div_mul_cancel₀ _ (hw j hj).ne']

def quarter : Circle :=
  ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩

theorem orbit_character {J : Type*} (columns : Finset J)
    (gamma : J → ℝ) (k : J → ℤ) (hrel : ∑ j ∈ columns, (k j : ℝ) * gamma j = 0)
    (v : ℝ) : (∏ j ∈ columns, (Circle.exp (gamma j * v)) ^ k j) = 1 := by
  have h := congrArg Additive.toMul
    (map_sum Circle.expHom (fun j => (k j : ℝ) * (gamma j * v)) columns)
  have hsum : (∑ j ∈ columns, (k j : ℝ) * (gamma j * v)) = 0 := by
    simp_rw [← mul_assoc, ← Finset.sum_mul, hrel, zero_mul]
  rw [hsum, toMul_sum] at h
  change Circle.exp 0 = ∏ j ∈ columns, Circle.exp ((k j : ℝ) * (gamma j * v)) at h
  simpa only [Circle.exp_zero, Circle.exp_intCast_mul] using h.symm

theorem quarter_character {J : Type*} (columns : Finset J) (k : J → ℤ) :
    ((∏ j ∈ columns, quarter ^ k j : Circle) : ℂ) = Complex.I ^ (∑ j ∈ columns, k j) := by
  have h := congrArg Additive.toMul
    (map_sum (zmultiplesHom (Additive Circle) (Additive.ofMul quarter)) k columns)
  rw [toMul_sum] at h
  change quarter ^ (∑ j ∈ columns, k j) = ∏ j ∈ columns, quarter ^ k j at h
  rw [← h, Circle.coe_zpow]
  rfl

theorem quarter_chord_sq (t : ℝ) :
    ‖(Circle.exp t : ℂ) - (quarter : ℂ)‖ ^ 2 = 2 * (1 - Real.sin t) := by
  have hnorm := Circle.normSq_coe (Circle.exp t)
  rw [Complex.normSq_apply] at hnorm
  change ‖(Circle.exp t : ℂ) - Complex.I‖ ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, sub_zero]
  have him : (Circle.exp t : ℂ).im = Real.sin t := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  rw [← him]
  nlinarith only [hnorm]

/-- Nonnegative multipliers combine integer relations into a lower bound for the sine deficit. -/
theorem weighted_phase_deficit {J A : Type*} (columns : Finset J) (rows : Finset A)
    (gamma w : J → ℝ) (k : A → J → ℤ) (lam : A → ℝ)
    (hw : ∀ j ∈ columns, 0 < w j) (hlam : ∀ a ∈ rows, 0 ≤ lam a)
    (hrel : ∀ a ∈ rows, ∑ j ∈ columns, (k a j : ℝ) * gamma j = 0) :
    let W := ∑ j ∈ columns, w j
    let C := ∑ j ∈ columns, (∑ a ∈ rows, lam a * |(k a j : ℝ)|) ^ 2 / w j
    0 < C →
      let N := ∑ a ∈ rows, lam a * ‖(1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j)‖
      N ^ 2 / (2 * W * C) ≤
        1 - sSup (Set.range (fun v : ℝ => ∑ j ∈ columns, w j * Real.sin (gamma j * v))) / W := by
  dsimp only
  let W := ∑ j ∈ columns, w j
  let C := ∑ j ∈ columns, (∑ a ∈ rows, lam a * |(k a j : ℝ)|) ^ 2 / w j
  let N := ∑ a ∈ rows, lam a * ‖(1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j)‖
  let S (v : ℝ) := ∑ j ∈ columns, w j * Real.sin (gamma j * v)
  change 0 < C → N ^ 2 / (2 * W * C) ≤ 1 - sSup (Set.range S) / W
  intro hC
  have hcolumns : columns.Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    simp [C, hempty] at hC
  have hW : 0 < W := Finset.sum_pos hw hcolumns
  have hpoint (v : ℝ) : N ^ 2 ≤ C * (2 * (W - S v)) := by
    have h := weighted_character_chord columns rows (fun j => Circle.exp (gamma j * v))
      (fun _ => quarter) w k lam hw hlam
    have horbit : ∀ a ∈ rows,
        ‖((∏ j ∈ columns, (Circle.exp (gamma j * v)) ^ k a j : Circle) : ℂ) -
          ((∏ j ∈ columns, quarter ^ k a j : Circle) : ℂ)‖ =
          ‖(1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j)‖ := by
      intro a ha
      rw [orbit_character columns gamma (k a) (hrel a ha) v, Circle.coe_one,
        quarter_character columns (k a)]
    have hN : (∑ a ∈ rows, lam a *
        ‖((∏ j ∈ columns, (Circle.exp (gamma j * v)) ^ k a j : Circle) : ℂ) -
          ((∏ j ∈ columns, quarter ^ k a j : Circle) : ℂ)‖) = N :=
      Finset.sum_congr rfl fun a ha => congrArg (lam a * ·) (horbit a ha)
    have henergy : (∑ j ∈ columns, w j *
        ‖(Circle.exp (gamma j * v) : ℂ) - (quarter : ℂ)‖ ^ 2) = 2 * (W - S v) := by
      simp_rw [quarter_chord_sq, mul_left_comm (w _) 2, ← Finset.mul_sum,
        mul_sub, mul_one, Finset.sum_sub_distrib, W, S]
      exact mul_sub ..
    change _ ^ 2 ≤ C * (∑ j ∈ columns, w j *
      ‖(Circle.exp (gamma j * v) : ℂ) - (quarter : ℂ)‖ ^ 2) at h
    rwa [hN, henergy] at h
  have hsup : sSup (Set.range S) ≤ W - N ^ 2 / (2 * C) := by
    apply csSup_le (Set.range_nonempty S)
    rintro _ ⟨v, rfl⟩
    have h := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).2
      (calc
        N ^ 2 ≤ C * (2 * (W - S v)) := hpoint v
        _ = (W - S v) * (2 * C) := by ring)
    linarith only [h]
  have h := (div_le_div_iff_of_pos_right hW).2 hsup
  rw [sub_div, div_self hW.ne', div_div, mul_right_comm 2 C W] at h
  linarith only [h]

/-- On disjoint nonzero rows, the separate squared relation defects add. -/
theorem weighted_phase_deficit_disjoint {J A : Type*} (columns : Finset J) (rows : Finset A)
    (gamma w : J → ℝ) (k : A → J → ℤ)
    (hw : ∀ j ∈ columns, 0 < w j)
    (hrel : ∀ a ∈ rows, ∑ j ∈ columns, (k a j : ℝ) * gamma j = 0)
    (hrow : ∀ a ∈ rows, ∃ j ∈ columns, k a j ≠ 0)
    (hdisj : ∀ a ∈ rows, ∀ b ∈ rows, a ≠ b →
      ∀ j ∈ columns, k a j = 0 ∨ k b j = 0) :
    let W := ∑ j ∈ columns, w j
    0 < W →
      (1 / (2 * W)) * ∑ a ∈ rows,
          ‖(1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j)‖ ^ 2 /
            (∑ j ∈ columns, (k a j : ℝ) ^ 2 / w j) ≤
        1 - sSup (Set.range (fun v : ℝ => ∑ j ∈ columns, w j * Real.sin (gamma j * v))) / W := by
  classical
  let W := ∑ j ∈ columns, w j
  let S (v : ℝ) := ∑ j ∈ columns, w j * Real.sin (gamma j * v)
  let defect (a : A) := ‖(1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j)‖
  let energy (a : A) := ∑ j ∈ columns, (k a j : ℝ) ^ 2 / w j
  let lam (a : A) := defect a / energy a
  let total := ∑ a ∈ rows, defect a ^ 2 / energy a
  change 0 < W → (1 / (2 * W)) * total ≤ 1 - sSup (Set.range S) / W
  intro hW
  have henergy : ∀ a ∈ rows, 0 < energy a := by
    intro a ha
    obtain ⟨j, hj, hk⟩ := hrow a ha
    exact Finset.sum_pos' (fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le)
      ⟨j, hj, div_pos (sq_pos_of_ne_zero (by exact_mod_cast hk)) (hw j hj)⟩
  have hlam : ∀ a ∈ rows, 0 ≤ lam a :=
    fun a ha => div_nonneg (norm_nonneg _) (henergy a ha).le
  have htotal : 0 ≤ total :=
    Finset.sum_nonneg fun a ha => div_nonneg (sq_nonneg _) (henergy a ha).le
  have hN : (∑ a ∈ rows, lam a * defect a) = total := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [lam, div_mul_eq_mul_div, pow_two]
  -- Disjoint supports remove all cross terms from the square of each column load.
  have hcol (j : J) (hj : j ∈ columns) :
      (∑ a ∈ rows, lam a * |(k a j : ℝ)|) ^ 2 =
        ∑ a ∈ rows, (lam a * |(k a j : ℝ)|) ^ 2 := by
    by_cases hex : ∃ a ∈ rows, k a j ≠ 0
    · obtain ⟨a, ha, hka⟩ := hex
      have hzero (b : A) (hb : b ∈ rows) (hne : b ≠ a) :
          lam b * |(k b j : ℝ)| = 0 := by
        have hk := (hdisj a ha b hb hne.symm j hj).resolve_left hka
        simp [hk]
      rw [Finset.sum_eq_single_of_mem a ha hzero,
        Finset.sum_eq_single_of_mem a ha (fun b hb hne => by
          rw [hzero b hb hne, zero_pow (by decide : (2 : ℕ) ≠ 0)])]
    · have hzero (a : A) (ha : a ∈ rows) : lam a * |(k a j : ℝ)| = 0 := by
        have hk : k a j = 0 := by
          by_contra h
          exact hex ⟨a, ha, h⟩
        simp [hk]
      rw [Finset.sum_eq_zero hzero, Finset.sum_eq_zero (fun a ha => by
        rw [hzero a ha, zero_pow (by decide : (2 : ℕ) ≠ 0)]),
        zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hC : (∑ j ∈ columns, (∑ a ∈ rows, lam a * |(k a j : ℝ)|) ^ 2 / w j) = total := by
    calc
      _ = ∑ j ∈ columns, ∑ a ∈ rows, (lam a * |(k a j : ℝ)|) ^ 2 / w j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcol j hj, Finset.sum_div]
      _ = ∑ a ∈ rows, lam a ^ 2 * energy a := by
        rw [Finset.sum_comm]
        simp_rw [mul_pow, sq_abs, mul_div_assoc, ← Finset.mul_sum, energy]
      _ = total := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [lam, div_pow, pow_two (energy a), div_mul_eq_mul_div,
          mul_div_mul_right _ _ (henergy a ha).ne']
  rcases htotal.eq_or_lt' with hzero | hpos
  · rw [hzero, mul_zero, sub_nonneg, div_le_iff₀ hW, one_mul]
    apply csSup_le (Set.range_nonempty S)
    rintro _ ⟨v, rfl⟩
    exact Finset.sum_le_sum fun j hj =>
      mul_le_of_le_one_right (hw j hj).le (Real.sin_le_one _)
  · have h := weighted_phase_deficit columns rows gamma w k lam hw hlam hrel
      (hC.symm ▸ hpos)
    change _ ≤ 1 - sSup (Set.range S) / W at h
    rw [hC, hN] at h
    change total ^ 2 / (2 * W * total) ≤ 1 - sSup (Set.range S) / W at h
    convert h using 1
    field_simp [hW.ne', hpos.ne']

#print axioms chord_prod_zpow
#print axioms weighted_character_chord
#print axioms weighted_phase_deficit
#print axioms weighted_phase_deficit_disjoint

end D5.S3.Fourier.WeightedIntegerRelations
