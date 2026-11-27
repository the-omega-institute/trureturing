/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rolling clique separators force Banach gain reconstruction errors approaching four. -/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SimpleGraph.ChordalReconstruction

open scoped BigOperators

noncomputable section

private def residue {w : ℕ} (r : Fin w) (t : ℕ) : ℝ :=
  (if t % w = r.val then 1 else 0) - 1 / (w : ℝ)

private theorem residue_bounds {w : ℕ} (r : Fin w) (t : ℕ) :
    -1 ≤ residue r t ∧ residue r t ≤ 1 := by
  have hw : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w from by omega)
  have h₀ : (0 : ℝ) ≤ 1 / w := by positivity
  have h₁ : (1 : ℝ) / w ≤ 1 := (div_le_one (by linarith)).2 hw
  unfold residue
  split <;> constructor <;> linarith

private theorem sum_residue {w : ℕ} (hw : 0 < w) (t : ℕ) :
    ∑ r : Fin w, residue r t = 0 := by
  have hw' : (w : ℝ) ≠ 0 := by positivity
  let a : Fin w := ⟨t % w, Nat.mod_lt t hw⟩
  have he (r : Fin w) : (t % w = r.val) ↔ a = r := Fin.ext_iff.symm
  simp [residue, he, Finset.sum_sub_distrib, div_eq_mul_inv, hw']

private def bandForward {w : ℕ} (r : Fin w) (u v : ℕ) : ℝ :=
  residue r v + if v - u = w then residue r u else 0

private def band {w : ℕ} (r : Fin w) (u v : ℕ) : ℝ :=
  if u < v then bandForward r u v else if v < u then -bandForward r v u else 0

private theorem band_reverse {w : ℕ} (r : Fin w) (u v : ℕ) :
    band r v u = -band r u v := by
  rcases lt_trichotomy u v with h | rfl | h
  · simp [band, h, not_lt_of_ge h.le]
  · simp [band]
  · simp [band, h, not_lt_of_ge h.le]

private theorem band_abs_le {w : ℕ} (r : Fin w) (u v : ℕ) :
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
  simp only [band, hua, hvb, hua.trans hvb, if_true, bandForward, huv, hvz, if_false]
  by_cases h : z - u = w
  · simp only [h, if_true]
    rw [show residue r v + 0 + (residue r z + 0) - (residue r z + residue r u) =
      residue r v - residue r u by ring, abs_le]
    unfold residue
    split <;> split <;> constructor <;> linarith
  · simp only [h, if_false, add_zero, add_sub_cancel_right]
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

private theorem band_average {w n : ℕ} (hw : 0 < w)
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
            (by rw [Nat.succ_mul]; omega) (by dsimp [finish]; omega)
        have hmres : (start + k * w) % w = r.val := by simpa using hres
        rw [Nat.succ_mul, ← add_assoc, band_long r hmres] at hd
        rw [Nat.succ_mul, ← add_assoc, Nat.cast_succ]
        nlinarith [ih (by omega)]
    linarith [steps n le_rfl]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin w))) fun r _ => lane r
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hH, add_zero, sub_zero] at hsum
  exact le_of_mul_le_mul_left hsum (by positivity : (0 : ℝ) < w)

end

end SimpleGraph.ChordalReconstruction
