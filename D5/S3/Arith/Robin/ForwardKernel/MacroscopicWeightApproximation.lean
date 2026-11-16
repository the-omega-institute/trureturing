/- GID: D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightApproximation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MacroscopicWeightApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform interval cancellation and bounded absolute mass lift to continuous macroscopic weights. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells
import Mathlib.Topology.UniformSpace.HeineCantor

namespace D5.S3.Arith.Robin.ForwardKernel.MacroscopicWeightApproximation

open Set MeasureTheory Filter
open scoped Topology BigOperators
open MovingLengthCells

noncomputable section
set_option autoImplicit false

/-- Uniform cancellation on intervals, with bounded absolute mass, extends to every
continuous weight on the macroscopic interval. -/
theorem continuous_weight_lifting
    {ι : Type} {f : ℝ → ι → ℝ → ℝ} {φ : ℝ → ℝ}
    (hi : ∀ᶠ X : ℝ in atTop, ∀ i, IntervalIntegrable (f X i) volume 1 2)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop, ∀ i,
      (∫ u in (1 : ℝ)..2, |f X i u|) ≤ C)
    (hcancel : ∀ η : ℝ, 0 < η → ∀ᶠ X : ℝ in atTop, ∀ i,
      ∀ A ∈ Icc (1 : ℝ) 2, ∀ B ∈ Icc A 2,
        |∫ u in A..B, f X i u| < η)
    (hφ : ContinuousOn φ (Icc (1 : ℝ) 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ i,
      |∫ u in (1 : ℝ)..2, φ u * f X i u| < ε := by
  obtain ⟨C, hC, hbound⟩ := hbound
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  intro ε hε
  let d := ε / (4 * (C + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ) d hd
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  let n := k + 1
  have hn : 0 < n := Nat.succ_pos k
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hk
  let Q := |K| + 1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let η := ε / (4 * (n : ℝ) * Q)
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [hi, hbound, hcancel η hη] with X hi hb hc
  intro i
  have hcell (j : ℕ) (hj : j < n) :
      Icc (cellPoint n j) (cellPoint n (j + 1)) ⊆ Icc (1 : ℝ) 2 :=
    Icc_subset_Icc (cellPoint_mem hn (by omega)).1
      (cellPoint_mem hn (by omega)).2
  have hicell (j : ℕ) (hj : j < n) :
      IntervalIntegrable (f X i) volume (cellPoint n j) (cellPoint n (j + 1)) := by
    apply (hi i).mono_set
    simpa only [uIcc_of_le (cellPoint_lt hn j).le, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      using hcell j hj
  have hiw (j : ℕ) (hj : j < n) :
      IntervalIntegrable (fun u => φ u * f X i u) volume
        (cellPoint n j) (cellPoint n (j + 1)) :=
    (hicell j hj).continuousOn_mul (by
      rw [uIcc_of_le (cellPoint_lt hn j).le]
      exact hφ.mono (hcell j hj))
  have hblock (j : ℕ) (hj : j ∈ Finset.range n) :
      |∫ u in (cellPoint n j)..(cellPoint n (j + 1)), φ u * f X i u| ≤
        d * (∫ u in (cellPoint n j)..(cellPoint n (j + 1)), |f X i u|) + Q * η := by
    have hjn := Finset.mem_range.mp hj
    have ha := cellPoint_mem hn (by omega : j ≤ n)
    have hbc : cellPoint n (j + 1) ∈ Icc (cellPoint n j) 2 :=
      ⟨(cellPoint_lt hn j).le, (cellPoint_mem hn (by omega)).2⟩
    have herr : |∫ u in (cellPoint n j)..(cellPoint n (j + 1)),
        (φ u - φ (cellPoint n j)) * f X i u| ≤
        d * (∫ u in (cellPoint n j)..(cellPoint n (j + 1)), |f X i u|) := by
      have hm (u : ℝ) (hu : u ∈ Icc (cellPoint n j) (cellPoint n (j + 1))) :
          |φ u - φ (cellPoint n j)| ≤ d := by
        apply le_of_lt
        apply (show dist (φ u) (φ (cellPoint n j)) < d from
          hmod u (hcell j hjn hu) (cellPoint n j) ha ?_)
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)]
        exact (sub_le_sub_right hu.2 _).trans_lt
          ((cellPoint_step hn j).symm ▸ hmesh)
      have hh := intervalIntegral.norm_integral_le_of_norm_le (cellPoint_lt hn j).le
        (Eventually.of_forall (fun u hu => show
          ‖(φ u - φ (cellPoint n j)) * f X i u‖ ≤ d * |f X i u| by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right (hm u ⟨hu.1.le, hu.2⟩) (abs_nonneg _)))
        ((hicell j hjn).abs.const_mul d)
      simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hh
    have heq : (∫ u in (cellPoint n j)..(cellPoint n (j + 1)), φ u * f X i u) =
        (∫ u in (cellPoint n j)..(cellPoint n (j + 1)),
          (φ u - φ (cellPoint n j)) * f X i u) +
        φ (cellPoint n j) * (∫ u in (cellPoint n j)..(cellPoint n (j + 1)), f X i u) := by
      simp_rw [sub_mul]
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        ((hiw j hjn).sub ((hicell j hjn).const_mul _)) ((hicell j hjn).const_mul _)]
      apply intervalIntegral.integral_congr
      intro u _
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    apply add_le_add herr
    rw [abs_mul]
    exact mul_le_mul ((hK _ ha).trans (by dsimp [Q]; linarith [le_abs_self K]))
      (hc i _ ha _ hbc).le (abs_nonneg _) hQ.le
  have hsum (g : ℝ → ℝ)
      (hg : ∀ j < n, IntervalIntegrable g volume (cellPoint n j) (cellPoint n (j + 1))) :
      (∑ j ∈ Finset.range n, ∫ u in (cellPoint n j)..(cellPoint n (j + 1)), g u) =
        ∫ u in (1 : ℝ)..2, g u := by
    convert intervalIntegral.sum_integral_adjacent_intervals hg using 1
    all_goals
      norm_num [cellPoint, hn.ne']
  have htotal : |∫ u in (1 : ℝ)..2, φ u * f X i u| ≤
      d * C + (n : ℝ) * (Q * η) := by
    rw [← hsum _ hiw]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum hblock).trans
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    rw [hsum _ (fun j hj => (hicell j hj).abs)]
    calc
      _ ≤ d * C + Q * ((n : ℝ) * η) :=
        add_le_add (mul_le_mul_of_nonneg_left (hb i) hd.le) le_rfl
      _ = _ := by ring
  have hfirst : d * C ≤ ε / 4 := by
    have : d * C ≤ d * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hd.le
    apply this.trans_eq
    dsimp [d]
    field_simp
  have hsecond : (n : ℝ) * (Q * η) = ε / 4 := by
    dsimp [η]
    field_simp
  exact htotal.trans_lt (by rw [hsecond]; linarith)

end
end D5.S3.Arith.Robin.ForwardKernel.MacroscopicWeightApproximation
