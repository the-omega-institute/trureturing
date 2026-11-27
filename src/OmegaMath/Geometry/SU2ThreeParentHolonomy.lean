import OmegaMath.Geometry.SphericalJung
import OmegaMath.Geometry.UnitQuaternionMetric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Omega original.

Spherical cap estimates for chordal reconstruction with at most three parents.
-/

open scoped Quaternion InnerProductSpace

namespace Omega.Geometry.UnitQuaternion

open Real

local notation "U" => unitary ℍ[ℝ]

/-- A common cap for a bounded number of candidates whose diameter satisfies
the spherical Jung cosine criterion. -/
theorem exists_card_bounded_center {ι : Type*} [Fintype ι] (q : ι → U)
    (n : ℕ) (hn : 0 < n) (hcard : Fintype.card ι ≤ n) {d r : ℝ}
    (hd : d ∈ Set.Icc 0 π) (hr : r ∈ Set.Icc 0 π)
    (hdiam : ∀ i j, i ≠ j → roundDist (q i) (q j) ≤ d)
    (hpos : 0 < cos d + (1 - cos d) / n)
    (hcos : cos r ≤ √(cos d + (1 - cos d) / n)) :
    ∃ p : U, ∀ i, roundDist (q i) p ≤ r := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, fun i => (h.false i).elim⟩
  | inr h =>
    let : Nonempty ι := h
    let v (i : ι) : ℍ[ℝ] := q i
    have hnorm (i : ι) : ‖v i‖ = 1 := norm_coe (q i)
    have hpair (i j : ι) (hij : i ≠ j) : cos d ≤ ⟪v i, v j⟫_ℝ :=
      (round_le_iff (q i) (q j) hd.1 hd.2).mp (hdiam i j hij)
    have hz := SphericalJung.zero_not_mem_convexHull_of_card_bound v n hn hcard
      hnorm (cos_le_one d) hpair hpos
    obtain ⟨p, hp, hcenter⟩ :=
      SphericalJung.exists_cap v n hn (.inl hcard) hnorm (cos_le_one d) hpair hz
    refine ⟨ofUnit p hp, fun i => (round_le_iff _ _ hr.1 hr.2).mpr ?_⟩
    rw [coe_ofUnit, real_inner_comm]
    exact hcos.trans (hcenter i)

/-- A diameter at most `2δ` suffices for a cap of radius `δ` on two candidates
when `δ < π/2`. -/
theorem exists_two_parent_center {ι : Type*} [Fintype ι] (q : ι → U)
    (hcard : Fintype.card ι ≤ 2) {δ : ℝ} (hδ : 0 ≤ δ) (hhalf : δ < π / 2)
    (hdiam : ∀ i j, i ≠ j → roundDist (q i) (q j) ≤ 2 * δ) :
    ∃ p : U, ∀ i, roundDist (q i) p ≤ δ := by
  apply exists_card_bounded_center q 2 (by decide) hcard
    (d := 2 * δ) ⟨by linarith, by linarith⟩ ⟨hδ, by linarith [pi_pos]⟩ hdiam
  · norm_num
    rw [cos_two_mul]
    have hc := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hhalf⟩
    nlinarith only [sq_pos_of_pos hc]
  · apply le_sqrt_of_sq_le
    norm_num
    rw [cos_two_mul]
    ring_nf
    rfl

/-- The three-point spherical Jung cap has radius at most `2δ` for
diameter at most `3δ` when `δ ≤ π/5`. -/
theorem exists_three_parent_jung_center {ι : Type*} [Fintype ι] (q : ι → U)
    (hcard : Fintype.card ι ≤ 3) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ π / 5)
    (hdiam : ∀ i j, i ≠ j → roundDist (q i) (q j) ≤ 3 * δ) :
    ∃ p : U, ∀ i, roundDist (q i) p ≤ 2 * δ := by
  have hsmall' : δ < π / 4 := by linarith [pi_pos]
  have hcos : (4 / 5 : ℝ) ≤ cos δ := by
    have h := cos_le_cos_of_nonneg_of_le_pi hδ (by linarith [pi_pos] : π / 5 ≤ π) hsmall
    rw [cos_pi_div_five] at h
    have hs : (11 / 5 : ℝ) ≤ √5 := le_sqrt_of_sq_le (by norm_num)
    linarith
  let c := cos δ
  have hc : c ≤ 1 := cos_le_one _
  have hp : 0 ≤ 6 * c ^ 3 + 2 * c ^ 2 - 4 * c - 1 := by
    have hf : 0 ≤ (c - 4 / 5) * (6 * (c - 4 / 5) ^ 2 + (82 / 5) * (c - 4 / 5) + 268 / 25) := by
      exact mul_nonneg (sub_nonneg.mpr hcos) (by positivity)
    nlinarith only [hf]
  have hsq : cos (2 * δ) ^ 2 ≤ cos (3 * δ) + (1 - cos (3 * δ)) / 3 := by
    rw [cos_two_mul, cos_three_mul]
    have hmul := mul_nonneg (sub_nonneg.mpr hc) hp
    change (2 * c ^ 2 - 1) ^ 2 ≤ 4 * c ^ 3 - 3 * c + (1 - (4 * c ^ 3 - 3 * c)) / 3
    nlinarith only [hmul]
  apply exists_card_bounded_center q 3 (by decide) hcard
    (d := 3 * δ) ⟨by linarith, by linarith [pi_pos]⟩
    ⟨by linarith, by linarith [pi_pos]⟩ hdiam
  · norm_num
    have hc₂ := cos_pos_of_mem_Ioo (x := 2 * δ) ⟨by linarith [pi_pos], by linarith⟩
    exact (sq_pos_of_pos hc₂).trans_le hsq
  · exact le_sqrt_of_sq_le hsq

end Omega.Geometry.UnitQuaternion
