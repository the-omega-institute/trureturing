/- GID: D5/S3/Combinatorics/Graph/PeriodicBandCochains
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-sharp-four-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Periodic scalar cochains on path powers and their extensions by two tagged vertices. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Sum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

Periodic scalar cochains on path powers and their extensions by two tagged vertices. -/

namespace Omega.PeriodicBandCochains

open scoped BigOperators

noncomputable section

private def residue {w : ℕ} (r : Fin w) (t : ℕ) : ℝ :=
  (if t % w = r.val then 1 else 0) - 1 / (w : ℝ)

private theorem residue_bounds {w : ℕ} (r : Fin w) (t : ℕ) :
    -1 ≤ residue r t ∧ residue r t ≤ 1 := by
  have hw : (1 : ℝ) ≤ w := by exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt r.isLt))
  have h₀ : (0 : ℝ) ≤ 1 / w := by positivity
  have h₁ : (1 : ℝ) / w ≤ 1 := (div_le_one (by linarith)).2 hw
  unfold residue
  split <;> constructor <;> linarith

private theorem sum_residue {w : ℕ} (hw : 0 < w) (t : ℕ) :
    ∑ r : Fin w, residue r t = 0 := by
  have hw' : (w : ℝ) ≠ 0 := by positivity
  let a : Fin w := ⟨t % w, Nat.mod_lt t hw⟩
  have he (r : Fin w) : (t % w = r.val) ↔ a = r := by
    change a.val = r.val ↔ a = r
    exact ⟨Fin.ext, congrArg Fin.val⟩
  simp [residue, he, Finset.sum_sub_distrib, div_eq_mul_inv, hw']

private def bandForward {w : ℕ} (r : Fin w) (u v : ℕ) : ℝ :=
  residue r v + if v - u = w then residue r u else 0

def band {w : ℕ} (r : Fin w) (u v : ℕ) : ℝ :=
  if u < v then bandForward r u v else if v < u then -bandForward r v u else 0

private theorem band_reverse {w : ℕ} (r : Fin w) (u v : ℕ) :
    band r v u = -band r u v := by
  rcases lt_trichotomy u v with h | rfl | h
  · simp [band, h, not_lt_of_ge h.le]
  · simp [band]
  · simp [band, h, not_lt_of_ge h.le]

theorem band_abs_le {w : ℕ} (r : Fin w) (u v : ℕ) :
    |band r u v| ≤ 2 := by
  have h (i j : ℕ) : |bandForward r i j| ≤ 2 := by
    rw [abs_le]
    unfold bandForward
    split <;> constructor <;> linarith [(residue_bounds r i).1, (residue_bounds r i).2,
      (residue_bounds r j).1, (residue_bounds r j).2]
  unfold band
  split
  · exact h _ _
  · split
    · rw [abs_neg]
      exact h _ _
    · norm_num

private theorem band_sorted_defect {w : ℕ} (r : Fin w) {u v z : ℕ}
    (hua : u < v) (hvb : v < z) (hspan : z - u ≤ w) :
    |band r u v + band r v z - band r u z| ≤ 1 := by
  have huv : v - u ≠ w := by omega
  have hvz : z - v ≠ w := by omega
  simp only [band, hua, hvb, hua.trans hvb, ite_true, bandForward, huv, hvz, ite_false]
  by_cases h : z - u = w
  · simp only [h, ite_true]
    rw [show residue r v + 0 + (residue r z + 0) - (residue r z + residue r u) =
      residue r v - residue r u by ring, abs_le]
    unfold residue
    split <;> split <;> constructor <;> linarith
  · simp only [h, ite_false, add_zero, add_sub_cancel_right]
    exact abs_le.mpr (residue_bounds r v)

private theorem band_long {w : ℕ} (r : Fin w) {t : ℕ} (ht : t % w = r.val) :
    band r t (t + w) = 2 - 2 / (w : ℝ) := by
  have h : t < t + w := by omega
  have hmod : (t + w) % w = r.val := by simpa using ht
  simp [band, h, bandForward, residue, ht, hmod]
  ring

private def laneStart {w : ℕ} (r : Fin w) : ℕ := if r.val = 0 then w else r.val

private theorem laneStart_spec {w : ℕ} (r : Fin w) :
    0 < laneStart r ∧ laneStart r ≤ w ∧ laneStart r % w = r.val := by
  unfold laneStart
  split
  · rename_i h
    simp [h, show 0 < w by omega]
  · rename_i h
    exact ⟨Nat.pos_of_ne_zero h, r.isLt.le, Nat.mod_eq_of_lt r.isLt⟩

theorem band_average {w n : ℕ} (hw : 0 < w)
    (H : Fin w → ℕ → ℝ) (hH : ∀ t, ∑ r, H r t = 0) (R δ : ℝ)
    (bound : ∀ (r : Fin w) (u v : ℕ), u < v → v ≤ u + w → v ≤ n * w + w + 1 →
      2 + band r u v + H r u - H r v ≤ R + δ) :
    (n : ℝ) * (4 - 2 / (w : ℝ)) ≤ ((n : ℝ) + 2) * (R + δ) := by
  let finish := n * w + w + 1
  have lane (r : Fin w) :
      (n : ℝ) * (4 - 2 / (w : ℝ)) + H r 0 - H r finish ≤
        ((n : ℝ) + 2) * (R + δ) := by
    let start := laneStart r
    have ⟨hstart, hstartw, hres⟩ := laneStart_spec r
    change 0 < start at hstart
    change start ≤ w at hstartw
    change start % w = r.val at hres
    have hin := bound r 0 start (by omega) (by omega) (by omega)
    have ha := (abs_le.mp (band_abs_le r 0 start)).1
    have hout := bound r (start + n * w) finish (by dsimp [finish]; omega)
      (by dsimp [finish]; omega) (by rfl)
    have hb := (abs_le.mp (band_abs_le r (start + n * w) finish)).1
    have steps (k : ℕ) (hk : k ≤ n) :
        (k : ℝ) * (4 - 2 / (w : ℝ)) + H r start - H r (start + k * w) ≤
          (k : ℝ) * (R + δ) := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hm : k * w ≤ n * w := Nat.mul_le_mul_right _ (by omega)
        have hm' : (k + 1) * w ≤ n * w := Nat.mul_le_mul_right _ hk
        have hd :
            2 + band r (start + k * w) (start + (k + 1) * w) +
              H r (start + k * w) - H r (start + (k + 1) * w) ≤ R + δ :=
          bound r _ _ (by rw [Nat.succ_mul]; omega)
            (by rw [Nat.succ_mul]; omega) (by omega)
        have hmres : (start + k * w) % w = r.val := by simpa using hres
        rw [Nat.succ_mul, ← add_assoc, band_long r hmres] at hd
        rw [Nat.succ_mul, ← add_assoc, Nat.cast_succ]
        nlinarith [ih (by omega)]
    linarith [steps n le_rfl]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin w))) fun r _ => lane r
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hH, add_zero, sub_zero] at hsum
  exact le_of_mul_le_mul_left hsum (by positivity : (0 : ℝ) < w)

private theorem skew_defect_le {A : Type*} [LinearOrder A] (f : A → A → ℝ)
    (hs : ∀ x y, f y x = -f x y) (P : A → A → Prop)
    (symm : ∀ x y, P x y → P y x)
    (sorted : ∀ x y z, x < y → y < z → P x y → P y z → P x z →
      |f x y + f y z - f x z| ≤ 1)
    (x y z : A) (hxy : P x y) (hyz : P y z) (hxz : P x z) :
    |f x y + f y z - f x z| ≤ 1 := by
  have diag (x : A) : f x x = 0 := by linarith [hs x x]
  have swapLeft (a b c : A) :
      |f b a + f a c - f b c| = |f a b + f b c - f a c| := by
    rw [hs a b, show -f a b + f a c - f b c = -(f a b + f b c - f a c) by ring, abs_neg]
  have swapRight (a b c : A) :
      |f a c + f c b - f a b| = |f a b + f b c - f a c| := by
    rw [hs b c, show f a c + -f b c - f a b = -(f a b + f b c - f a c) by ring, abs_neg]
  rcases eq_or_ne x y with rfl | hn₁
  · simp [diag]
  rcases eq_or_ne y z with rfl | hn₂
  · simp [diag]
  rcases eq_or_ne x z with rfl | hn₃
  · simp [diag, hs x y]
  rcases lt_or_gt_of_ne hn₁ with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hn₂ with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hn₃ with h₃ | h₃
  · exact sorted x y z h₁ h₂ hxy hyz hxz
  · exact ((h₁.trans h₂).not_gt h₃).elim
  · rw [← swapRight x y z]
    exact sorted x z y h₃ h₂ hxz (symm _ _ hyz) hxy
  · rw [← swapRight x y z, ← swapLeft x z y]
    exact sorted z x y h₃ h₁ (symm _ _ hxz) hxy (symm _ _ hyz)
  · rw [← swapLeft x y z]
    exact sorted y x z h₁ h₃ (symm _ _ hxy) hxz hyz
  · rw [← swapLeft x y z, ← swapRight y x z]
    exact sorted y z x h₂ h₃ hyz (symm _ _ hxz) (symm _ _ hxy)
  · exact ((h₂.trans h₁).not_gt h₃).elim
  · rw [← swapLeft x y z, ← swapRight y x z, ← swapLeft y z x]
    exact sorted z y x h₂ h₁ (symm _ _ hyz) (symm _ _ hxy) (symm _ _ hxz)

abbrev Tags := ℕ ⊕ Bool

def tagPair (w j i : ℕ) : Tags → Tags → Prop
  | .inl a, .inl b => a ≤ b + w ∧ b ≤ a + w
  | .inl a, .inr false | .inr false, .inl a => j ≤ a ∧ a ≤ i
  | .inl a, .inr true | .inr true, .inl a => a = i
  | .inr _, .inr _ => True

def tagValue {w : ℕ} (r : Fin w) (i : ℕ) : Tags → Tags → ℝ
  | .inl a, .inl b => band r a b
  | .inl a, .inr false => if a = i then 0 else band r a i + 1
  | .inr false, .inl a => -(if a = i then 0 else band r a i + 1)
  | .inr false, .inr true => 1
  | .inr true, .inr false => -1
  | _, _ => 0

private theorem tagPair_symm (w j i : ℕ) (x y : Tags) :
    tagPair w j i x y → tagPair w j i y x := by
  cases x using Sum.rec <;> cases y using Sum.rec
  · exact And.symm
  · rename_i b
    cases b <;> exact id
  · rename_i b a
    cases b <;> exact id
  · rename_i a b
    cases a <;> cases b <;> exact id

theorem tagValue_skew {w : ℕ} (r : Fin w) (i : ℕ) (x y : Tags) :
    tagValue r i y x = -tagValue r i x y := by
  cases x using Sum.rec <;> cases y using Sum.rec
  · apply band_reverse
  · rename_i b
    cases b <;> simp [tagValue]
  · rename_i b a
    cases b <;> simp [tagValue]
  · rename_i a b
    cases a <;> cases b <;> norm_num [tagValue]

theorem tagValue_abs {w : ℕ} (r : Fin w) (i : ℕ) (x y : Tags) :
    |tagValue r i x y| ≤ 3 := by
  cases x using Sum.rec <;> cases y using Sum.rec
  · exact (band_abs_le _ _ _).trans (by norm_num)
  · rename_i a b
    cases b
    · by_cases h : a = i
      · simp [tagValue, h]
      · simp only [tagValue, h, ite_false, abs_le]
        obtain ⟨h₁, h₂⟩ := abs_le.mp (band_abs_le r a i)
        constructor <;> linarith
    · norm_num [tagValue]
  · rw [tagValue_skew r i]
    rw [abs_neg]
    rename_i b a
    cases b
    · by_cases h : a = i
      · simp [tagValue, h]
      · simp only [tagValue, h, ite_false, abs_le]
        obtain ⟨h₁, h₂⟩ := abs_le.mp (band_abs_le r a i)
        constructor <;> linarith
    · norm_num [tagValue]
  · rename_i a b
    cases a <;> cases b <;> norm_num [tagValue]

theorem tagValue_defect {w : ℕ} (r : Fin w) {j i : ℕ}
    (hwidth : i ≤ j + w) (x y z : Tags)
    (hxy : tagPair w j i x y) (hyz : tagPair w j i y z) (hxz : tagPair w j i x z) :
    |tagValue r i x y + tagValue r i y z - tagValue r i x z| ≤ 1 := by
  letI : LinearOrder Tags := LinearOrder.lift' (toLex : Tags → ℕ ⊕ₗ Bool) (fun _ _ h => congrArg ofLex h)
  refine skew_defect_le (tagValue r i) (tagValue_skew r i)
    (tagPair w j i) (tagPair_symm w j i) ?_ x y z hxy hyz hxz
  intro a b c hab hbc hab' hbc' hac'
  cases a using Sum.rec <;> cases b using Sum.rec <;> cases c using Sum.rec
  · rename_i a b c
    have h₁ : a < b := Sum.Lex.inl_lt_inl_iff.mp hab
    have h₂ : b < c := Sum.Lex.inl_lt_inl_iff.mp hbc
    have h₃ : c ≤ a + w := hac'.2
    exact band_sorted_defect r h₁ h₂ (by omega)
  · rename_i a b t
    cases t
    · obtain ⟨hja, hai⟩ := hac'
      obtain ⟨hjb, hbi⟩ := hbc'
      have habn : a < b := Sum.Lex.inl_lt_inl_iff.mp hab
      have hani : a ≠ i := by omega
      by_cases h : b = i
      · subst b
        simp [tagValue, hani]
      · have hbi' : b < i := by omega
        simp only [tagValue, h, hani, ite_false]
        rw [show band r a b + (band r b i + 1) - (band r a i + 1) =
          band r a b + band r b i - band r a i by ring]
        exact band_sorted_defect r habn hbi' (by omega)
    · have ha : a = i := hac'
      have hb : b = i := hbc'
      exact (Sum.Lex.inl_lt_inl_iff.mp hab).ne (ha.trans hb.symm) |>.elim
  · exact (Sum.Lex.not_inr_lt_inl hbc).elim
  · rename_i a s t
    have hst : s < t := Sum.Lex.inr_lt_inr_iff.mp hbc
    cases s <;> cases t
    · exact (lt_irrefl _ hst).elim
    · have ha : a = i := hac'
      subst a
      norm_num [tagValue]
    · exact (by decide : ¬true < false) hst |>.elim
    · exact (lt_irrefl _ hst).elim
  · exact (Sum.Lex.not_inr_lt_inl hab).elim
  · exact (Sum.Lex.not_inr_lt_inl hab).elim
  · exact (Sum.Lex.not_inr_lt_inl hbc).elim
  · rename_i a b c
    have h₁ : a < b := Sum.Lex.inr_lt_inr_iff.mp hab
    have h₂ : b < c := Sum.Lex.inr_lt_inr_iff.mp hbc
    cases a <;> cases b <;> cases c <;>
      first
      | exact (lt_irrefl _ h₁).elim
      | exact (lt_irrefl _ h₂).elim
      | exact ((by decide : ¬true < false) h₁).elim
      | exact ((by decide : ¬true < false) h₂).elim

theorem sum_band {w : ℕ} (hw : 0 < w) (u v : ℕ) :
    ∑ r : Fin w, band r u v = 0 := by
  unfold band
  split
  · unfold bandForward
    split <;> simp [Finset.sum_add_distrib, sum_residue hw]
  · split
    · unfold bandForward
      split <;> simp [Finset.sum_add_distrib, sum_residue hw]
    · simp

end

end Omega.PeriodicBandCochains
