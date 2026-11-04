/- GID: D5/S0/FiniteGeometry/FiniteIncrementPathBound
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/FiniteIncrementPathBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform boundedness of all admissible finite paths with a fixed finite increment set. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! A finite cap cover and a scalar projection barrier bound arbitrary admissible paths. -/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace D5.S0.FiniteGeometry.FiniteIncrementPathBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finitely many increment directions give one neighborhood preserving every
strictly positive projection at the center. -/
private lemma local_radius (V : Finset E) (u : E) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ s v : E, ‖s - u‖ ≤ δ → v ∈ V →
        ⟪s, v⟫_ℝ ≤ 0 → ⟪u, v⟫_ℝ ≤ 0 := by
  classical
  induction V using Finset.induction_on with
  | empty => exact ⟨1 / 2, by norm_num, le_rfl, by simp⟩
  | @insert v V hv ih =>
    obtain ⟨δ, hδ, hδhalf, hlocal⟩ := ih
    by_cases huv : ⟪u, v⟫_ℝ ≤ 0
    · refine ⟨δ, hδ, hδhalf, ?_⟩
      intro s z hs hz hsz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact huv
      · exact hlocal s z hs hz hsz
    · have hp : 0 < ⟪u, v⟫_ℝ := lt_of_not_ge huv
      let ε := ⟪u, v⟫_ℝ / (2 * (‖v‖ + 1))
      have hε : 0 < ε := by dsimp [ε]; positivity
      refine ⟨min δ ε, lt_min hδ hε, (min_le_left _ _).trans hδhalf, ?_⟩
      intro s z hs hz hsz
      rcases Finset.mem_insert.mp hz with hz | hz
      · subst z
        have hdist : ‖u - s‖ ≤ ε := by
          rw [norm_sub_rev]
          exact hs.trans (min_le_right _ _)
        have hcs := (le_abs_self ⟪u - s, v⟫_ℝ).trans
          (abs_real_inner_le_norm (u - s) v)
        rw [inner_sub_left] at hcs
        have he : ε * (2 * (‖v‖ + 1)) = ⟪u, v⟫_ℝ := by
          dsimp [ε]
          exact div_mul_cancel₀ _ (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hdist (norm_nonneg v)
        nlinarith [norm_nonneg v]
      · exact hlocal s z (hs.trans (min_le_left _ _)) hz hsz


/-- A state near the support hyperplane of a radius-R ball has direction near u. -/
private lemma direction_close {u x : E} {δ R : ℝ}
    (hu : ‖u‖ = 1) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hR : 0 < R) (hxR : ‖x‖ ≤ R)
    (hhigh : (1 - δ ^ 2 / 2) * R ≤ ⟪u, x⟫_ℝ) :
    x ≠ 0 ∧ ‖(‖x‖⁻¹ : ℝ) • x - u‖ ≤ δ := by
  have ha : 0 < 1 - δ ^ 2 / 2 := by nlinarith
  have hux : 0 < ⟪u, x⟫_ℝ := lt_of_lt_of_le (mul_pos ha hR) hhigh
  have hx : x ≠ 0 := by intro hz; simp [hz] at hux
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have hlo : 1 - δ ^ 2 / 2 ≤ ⟪u, (‖x‖⁻¹ : ℝ) • x⟫_ℝ := by
    rw [inner_smul_right, ← div_eq_inv_mul]
    apply (le_div_iff₀ hnx).mpr
    exact (mul_le_mul_of_nonneg_left hxR ha.le).trans hhigh
  have hsq := norm_sub_sq_real ((‖x‖⁻¹ : ℝ) • x) u
  rw [hs, hu, real_inner_comm] at hsq
  refine ⟨hx, ?_⟩
  nlinarith [norm_nonneg ((‖x‖⁻¹ : ℝ) • x - u)]

/-- Above the threshold the projection decreases; below it the overshoot is one step. -/
private lemma projection_barrier (V : Finset E) (u : E) (δ M R : ℝ)
    (hu : ‖u‖ = 1) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hM : 0 ≤ M) (hstep : ∀ v ∈ V, ‖v‖ ≤ M) (hR : 0 < R)
    (hlocal : ∀ s v : E, ‖s - u‖ ≤ δ → v ∈ V →
      ⟪s, v⟫_ℝ ≤ 0 → ⟪u, v⟫_ℝ ≤ 0)
    (N : ℕ) (w : ℕ → E) (hw0 : w 0 = 0)
    (hadm : ∀ k < N, w (k + 1) - w k ∈ V ∧
      ⟪w k, w (k + 1) - w k⟫_ℝ ≤ 0)
    (hmax : ∀ k ≤ N, ‖w k‖ ≤ R) :
    ∀ k ≤ N, ⟪u, w k⟫_ℝ ≤ (1 - δ ^ 2 / 2) * R + M := by
  have ha : 0 < 1 - δ ^ 2 / 2 := by nlinarith
  intro k
  induction k with
  | zero =>
    intro _
    rw [hw0, inner_zero_right]
    exact add_nonneg (mul_nonneg ha.le hR.le) hM
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    have hp := ih (by omega)
    obtain ⟨hv, had⟩ := hadm k hkN
    have hrec : ⟪u, w (k + 1)⟫_ℝ =
        ⟪u, w k⟫_ℝ + ⟪u, w (k + 1) - w k⟫_ℝ := by
      rw [inner_sub_right]
      ring
    by_cases hh : (1 - δ ^ 2 / 2) * R ≤ ⟪u, w k⟫_ℝ
    · obtain ⟨hx, hdir⟩ := direction_close hu hδ hδhalf hR (hmax k (by omega)) hh
      have hnormad : ⟪(‖w k‖⁻¹ : ℝ) • w k, w (k + 1) - w k⟫_ℝ ≤ 0 := by
        rw [real_inner_smul_left]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) had
      have hnonpos := hlocal _ _ hdir hv hnormad
      rw [hrec]
      linarith
    · have hinc := (real_inner_le_norm u (w (k + 1) - w k)).trans
        (mul_le_mul_of_nonneg_left (hstep _ hv) (norm_nonneg u))
      rw [hu, one_mul] at hinc
      rw [hrec]
      linarith

/-- A finite increment set uniformly bounds all finite paths from zero whose
increments have nonpositive pairing with their current state. The constant
precedes both the horizon and the path; the tail after the horizon is unrestricted. -/
theorem exists_uniform_bound [FiniteDimensional ℝ E] (V : Finset E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (w : ℕ → E), w 0 = 0 →
      (∀ k < N, w (k + 1) - w k ∈ V ∧
        ⟪w k, w (k + 1) - w k⟫_ℝ ≤ 0) →
      ∀ k ≤ N, ‖w k‖ ≤ C := by
  classical
  choose δ hδ hδhalf hlocal using (fun u : E => local_radius V u)
  let S := Metric.sphere (0 : E) 1
  let cap : S → Set E := fun u => Metric.ball (u : E) (δ u / 2)
  obtain ⟨T, hcover⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover cap
    (fun _ => Metric.isOpen_ball) (by
      intro s hs
      refine Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩
      exact Metric.mem_ball_self (div_pos (hδ s) (by norm_num)))
  let M : ℝ := 1 + ∑ v ∈ V, ‖v‖
  have hsum : 0 ≤ ∑ v ∈ V, ‖v‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 0 < M := by dsimp [M]; linarith
  have hstep : ∀ v ∈ V, ‖v‖ ≤ M := by
    intro v hv
    have hvsum := Finset.single_le_sum (fun z _ => norm_nonneg z) hv
    dsimp [M]
    linarith
  let B : S → ℝ := fun u => 8 * M / (3 * δ u ^ 2)
  have hB : ∀ u : S, 0 ≤ B u := by
    intro u
    dsimp [B]
    positivity
  refine ⟨1 + ∑ u ∈ T, B u, by positivity, ?_⟩
  intro N w hw0 hadm
  obtain ⟨j, hj, hjmax⟩ := (Finset.range (N + 1)).exists_max_image
    (fun k => ‖w k‖) ⟨0, by simp⟩
  have hjN : j ≤ N := by simpa using hj
  let R := ‖w j‖
  have hmax : ∀ k ≤ N, ‖w k‖ ≤ R := by
    intro k hk
    exact hjmax k (Finset.mem_range.mpr (by omega))
  by_cases hR : R = 0
  · intro k hk
    have hkR := hmax k hk
    rw [hR] at hkR
    have hsumB : 0 ≤ ∑ u ∈ T, B u := Finset.sum_nonneg (fun u _ => hB u)
    linarith
  · have hRpos : 0 < R := lt_of_le_of_ne (norm_nonneg (w j)) (Ne.symm hR)
    have hy : w j ≠ 0 := norm_ne_zero_iff.mp hR
    have hunit : (‖w j‖⁻¹ : ℝ) • w j ∈ S := by
      simpa [S, Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hy
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp (hcover hunit)
    obtain ⟨huT, hcap⟩ := Set.mem_iUnion.mp hu
    have huunit : ‖(u : E)‖ = 1 := by
      simpa [S, Metric.mem_sphere, dist_zero_right] using u.property
    have hdist : ‖(‖w j‖⁻¹ : ℝ) • w j - (u : E)‖ < δ u / 2 := by
      simpa [cap, Metric.mem_ball, dist_eq_norm] using hcap
    have hnorm : ‖(‖w j‖⁻¹ : ℝ) • w j‖ = 1 := norm_smul_inv_norm hy
    have hsq := norm_sub_sq_real ((‖w j‖⁻¹ : ℝ) • w j) (u : E)
    rw [hnorm, huunit, real_inner_comm] at hsq
    have hcapinner : 1 - δ u ^ 2 / 8 <
        ⟪(u : E), (‖w j‖⁻¹ : ℝ) • w j⟫_ℝ := by
      nlinarith [norm_nonneg ((‖w j‖⁻¹ : ℝ) • w j - (u : E)), hδ (u : E)]
    have hpeak : (1 - δ u ^ 2 / 8) * R < ⟪(u : E), w j⟫_ℝ := by
      rw [inner_smul_right, ← div_eq_inv_mul] at hcapinner
      exact (lt_div_iff₀ hRpos).mp hcapinner
    have hbar := projection_barrier V (u : E) (δ u) M R huunit (hδ u) (hδhalf u)
      hM.le hstep hRpos (hlocal u) N w hw0 hadm hmax j hjN
    have hcoeff : 0 < 3 * δ u ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos (hδ u))
    have hRB : R < B u := by
      dsimp [B]
      apply (lt_div_iff₀ hcoeff).mpr
      nlinarith
    have hBsum : B u ≤ ∑ u ∈ T, B u :=
      Finset.single_le_sum (fun z _ => hB z) huT
    intro k hk
    have hkR := hmax k hk
    linarith

end D5.S0.FiniteGeometry.FiniteIncrementPathBound
