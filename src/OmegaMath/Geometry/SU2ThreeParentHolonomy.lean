import OmegaMath.Geometry.SphericalJung
import OmegaMath.Geometry.SU2HolonomyMatrix
import OmegaMath.Geometry.QuaternionicHermitianSpectrum
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


open Omega.Geometry.HolonomySpectrum

private theorem triple_weight_bound (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) : (7 / 9 : ℝ) ≤ ∑ i, (3 * w i ^ 2 - 2 * w i ^ 3) := by
  simp only [Fin.sum_univ_three] at hs ⊢
  have h₂ : w 2 ≤ 1 := by linarith [hw 0, hw 1]
  have hp : w 0 * w 1 ≤ (1 - w 2) ^ 2 / 4 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (show w 0 + w 1 = 1 - w 2 by linarith)
    nlinarith only [sq_nonneg (w 0 - w 1), h]
  have hq : w 2 * (1 - w 2) ^ 2 ≤ 4 / 27 := by
    nlinarith only [mul_nonneg (sq_nonneg (w 2 - 1 / 3))
      (show 0 ≤ 4 / 3 - w 2 by linarith)]
  have hp' := mul_le_mul_of_nonneg_right hp (hw 2)
  have hid : 3 * w 0 ^ 2 - 2 * w 0 ^ 3 + (3 * w 1 ^ 2 - 2 * w 1 ^ 3) +
      (3 * w 2 ^ 2 - 2 * w 2 ^ 3) = 1 - 6 * w 0 * w 1 * w 2 := by
    have he : w 2 = 1 - w 0 - w 1 := by linarith
    rw [he]
    ring
  linarith only [hp', hq, hid, show w 2 * (1 - w 2) ^ 2 / 4 =
    (1 - w 2) ^ 2 / 4 * w 2 by ring]

/-- Three-parent holonomy fills the interval between the Jung and
closed-hemisphere insertion estimates. -/
theorem exists_three_parent_holonomy_center (q : Fin 3 → U) (g : HolonomyGains (Fin 3))
    {δ : ℝ} (hlo : π / 5 ≤ δ) (hhi : δ < π / 4)
    (hold : ∀ i j, i ≠ j → cos (2 * δ) ≤ (g.gain i j : ℍ[ℝ]).re)
    (hpoint : ∀ i j, i ≠ j → cos δ ≤ (↑((q i)⁻¹ * g.gain i j * q j) : ℍ[ℝ]).re)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      cos δ ≤ (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re) :
    ∃ p : U, ∀ i, roundDist (q i) p ≤ 2 * δ := by
  let t := cos (2 * δ)
  let c := cos δ
  have hδ : 0 ≤ δ := by linarith [pi_pos]
  have ht : 0 < t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  obtain ⟨z, hz, hsupport⟩ := SphericalJung.exists_min_norm_support (fun i => (q i : ℍ[ℝ]))
  suffices hnorm : t ≤ ‖z‖ by
    have hpos : 0 < ‖z‖ := ht.trans_le hnorm
    have hu : ‖‖z‖⁻¹ • z‖ = 1 := by simp [norm_smul, hpos.ne']
    refine ⟨ofUnit (‖z‖⁻¹ • z) hu, fun i => (round_le_iff _ _ (by linarith)
      (by linarith [pi_pos])).mpr ?_⟩
    rw [coe_ofUnit, real_inner_comm, real_inner_smul_left, ← div_eq_inv_mul, le_div_iff₀ hpos]
    exact (mul_le_mul_of_nonneg_right hnorm hpos.le).trans (by simpa [pow_two] using hsupport i)
  by_contra! hsmall
  obtain ⟨w, hw, hw₁, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull hz
  let M := holonomyMatrix g w
  let a := weightedColumn w (fun _ => (1 : U))
  let b := weightedColumn w q
  have han : ‖a‖ = 1 := norm_weightedColumn _ hw hw₁
  have hbn : ‖b‖ = 1 := norm_weightedColumn _ hw hw₁
  have hab : pairing a b = z := by
    rw [show pairing a b = pairing (weightedColumn w fun _ => (1 : U)) (weightedColumn w q) from rfl,
      pairing_weightedColumn _ _ hw]
    simpa using hwz
  obtain ⟨μ, hμ, e, he⟩ := exists_ordered_spectrum (isHermitian_holonomyMatrix g w)
  have hsum := spectrum_moments M e he 1
  have hsq := spectrum_moments M e he 2
  have hcube := spectrum_moments M e he 3
  have htrace := holonomy_trace g hw
  have htrace₂ := holonomy_trace_sq g hw
  have htrace₃ := holonomy_trace_cube_lower g hw hw₁ htri
  have htop := rayleigh_two_unit_le_norm (by simp : 2 ≤ Fintype.card (Fin 3)) M μ hμ e he
    a b han hbn (by rw [hab]; exact hsmall.trans_le (cos_le_one _))
  rw [hab] at htop
  have hlo₁ := rayleigh_weightedColumn_lower g (fun _ => (1 : U)) hw hw₁
    (fun i j hij => by simpa using hold i j hij)
  have hlo₂ := rayleigh_weightedColumn_lower g q hw hw₁ hpoint
  have hW : 1 / 3 ≤ ∑ i, w i ^ 2 := by
    have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
    simp only [hw₁, one_pow, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hh
    linarith only [hh]
  have hlow : 2 / 3 * (1 + c + t) ≤ ⟪a, realAction M a⟫_ℝ + ⟪b, realAction M b⟫_ℝ := by
    have hnon : 0 ≤ 2 - c - t := by linarith [cos_le_one δ, cos_le_one (2 * δ)]
    have h := mul_le_mul_of_nonneg_left hW hnon
    change t + (1 - t) * ∑ i, w i ^ 2 ≤ ⟪a, realAction M a⟫_ℝ at hlo₁
    change c + (1 - c) * ∑ i, w i ^ 2 ≤ ⟪b, realAction M b⟫_ℝ at hlo₂
    linarith only [h, hlo₁, hlo₂]
  have hc₀ : √(2 : ℝ) / 2 ≤ c := by
    rw [← cos_pi_div_four]
    exact cos_le_cos_of_nonneg_of_le_pi hδ (by linarith [pi_pos]) hhi.le
  have hc₁ : c ≤ 5 / 6 := by
    have h := cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos] : 0 ≤ π / 5)
      (by linarith [pi_pos] : δ ≤ π) hlo
    rw [cos_pi_div_five] at h
    have hs : √(5 : ℝ) ≤ 7 / 3 := sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith only [show c ≤ (1 + √5) / 4 from h, hs]
  have htc : t = 2 * c ^ 2 - 1 := cos_two_mul δ
  have hC : 1 - 2 * (1 - c) / 9 ≤ ∑ i, μ i ^ 3 := by
    rw [hcube]
    have hm := mul_le_mul_of_nonneg_left (triple_weight_bound w hw hw₁)
      (sub_nonneg.mpr (cos_le_one δ))
    change c + (1 - c) * (∑ i, (3 * w i ^ 2 - 2 * w i ^ 3)) ≤ _ at htrace₃
    linarith only [hm, htrace₃]
  have hone : ∑ i, μ i = 1 := by
    simpa only [pow_one, M, htrace, hw₁] using hsum
  have htwo : ∑ i, μ i ^ 2 = 1 := by
    simpa only [M, htrace₂, hw₁, one_pow] using hsq
  let m : Fin 3 → ℝ := fun i => μ i
  have hm₁ : (∑ i, m i) = 1 := hone
  have hm₂ : (∑ i, m i ^ 2) = 1 := htwo
  have hm₃ : 1 - 2 * (1 - c) / 9 ≤ ∑ i, m i ^ 3 := hC
  rw [Fin.sum_univ_three] at hm₁ hm₂ hm₃
  have hlim := three_point_moment_obstruction (hμ (by decide : (0 : Fin 3) ≤ 1))
    (hμ (by decide : (1 : Fin 3) ≤ 2)) hm₁ hm₂ hm₃ hc₀ hc₁ (norm_nonneg z)
    (htc ▸ hsmall)
  rw [← htc] at hlim
  exact (not_lt_of_ge (hlow.trans htop)) hlim

end Omega.Geometry.UnitQuaternion
