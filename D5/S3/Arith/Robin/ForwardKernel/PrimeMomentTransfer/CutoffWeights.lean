/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cutoff weights have bounded supremum plus total variation. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs
import Mathlib.Analysis.BoundedVariation
import Mathlib.Tactic

/-! Indicator and logarithmic block weights retain both jumps at their closed endpoints. -/

open Set
open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

private theorem p_antitone_extended_factorization (u v U : ℝ) (f : ℝ → ℝ)
    (huv : u ≤ v) (hU : 0 ≤ U) (hf : AntitoneOn f (Icc u v))
    (hb : ∀ x ∈ Icc u v, 0 ≤ f x ∧ f x ≤ U) :
    ∃ p q : ℝ → ℝ, Monotone p ∧ Monotone q ∧
      (∀ x, 0 ≤ p x ∧ p x ≤ U) ∧ (∀ x, 0 ≤ q x ∧ q x ≤ U) ∧
      (Icc u v).indicator f = p - q := by
  let p : ℝ → ℝ := fun x => if x < u then 0 else f u
  let q : ℝ → ℝ := fun x => if x < u then 0 else if x ≤ v then f u - f x else f u
  have hu := hb u ⟨le_rfl, huv⟩
  have hsub (x : ℝ) (hx : x ∈ Icc u v) : 0 ≤ f u - f x ∧ f u - f x ≤ U :=
    ⟨sub_nonneg.mpr (hf ⟨le_rfl, huv⟩ hx hx.1),
      (sub_le_self _ (hb x hx).1).trans hu.2⟩
  refine ⟨p, q, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x < u
    · simp only [p, ite_eq_left hx]
      split_ifs <;> linarith [hu.1]
    · have hy : ¬ y < u := not_lt_of_ge ((le_of_not_gt hx).trans hxy)
      simp [p, hx, hy]
  · intro x y hxy
    by_cases hx : x < u
    · simp only [q, ite_eq_left hx]
      split_ifs with hy hyv
      · exact le_rfl
      · exact (hsub y ⟨le_of_not_gt hy, hyv⟩).1
      · exact hu.1
    · have hux := le_of_not_gt hx
      have hy : ¬ y < u := not_lt_of_ge (hux.trans hxy)
      by_cases hxv : x ≤ v
      · by_cases hyv : y ≤ v
        · simp only [q, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxv, ite_eq_left hyv]
          exact sub_le_sub_left (hf ⟨hux, hxv⟩ ⟨hux.trans hxy, hyv⟩ hxy) _
        · simp only [q, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxv, ite_eq_right hyv]
          exact sub_le_self _ (hb x ⟨hux, hxv⟩).1
      · have hyv : ¬ y ≤ v := fun h => hxv (hxy.trans h)
        simp only [q, ite_eq_right hx, ite_eq_right hy, ite_eq_right hxv, ite_eq_right hyv, le_refl]
  · intro x
    dsimp [p]
    split_ifs
    · exact ⟨le_rfl, hU⟩
    · exact hu
  · intro x
    dsimp [q]
    split_ifs with hx hxv
    · exact ⟨le_rfl, hU⟩
    · exact hsub x ⟨le_of_not_gt hx, hxv⟩
    · exact hu
  · funext x
    by_cases hx : x < u
    · simp [p, q, hx, not_le.mpr hx]
    · by_cases hxv : x ≤ v
      · simp [p, q, hx, hxv, le_of_not_gt hx]
      · simp [p, q, hx, hxv]

private theorem p_variation_triangle (p q : ℝ → ℝ) (U : ℝ) (_hU : 0 ≤ U)
    (hp : Monotone p) (hq : Monotone q)
    (hpb : ∀ x, 0 ≤ p x ∧ p x ≤ U) (hqb : ∀ x, 0 ≤ q x ∧ q x ≤ U) :
    eVariationOn (p - q) univ ≤ ENNReal.ofReal (2 * U) := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, ⟨u, hu, _⟩⟩
  have hinc (i : ℕ) :
      0 ≤ (p (u (i + 1)) - p (u i)) + (q (u (i + 1)) - q (u i)) :=
    add_nonneg (sub_nonneg.mpr (hp (hu (Nat.le_succ i))))
      (sub_nonneg.mpr (hq (hu (Nat.le_succ i))))
  calc
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal
        ((p (u (i + 1)) - p (u i)) + (q (u (i + 1)) - q (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Pi.sub_apply, edist_dist, Real.dist_eq]
      apply ENNReal.ofReal_le_ofReal
      rw [show (p (u (i + 1)) - q (u (i + 1))) - (p (u i) - q (u i)) =
        (p (u (i + 1)) - p (u i)) - (q (u (i + 1)) - q (u i)) by ring]
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg (sub_nonneg.mpr (hp (hu (Nat.le_succ i)))),
          abs_of_nonneg (sub_nonneg.mpr (hq (hu (Nat.le_succ i))))])
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
        ((p (u (i + 1)) - p (u i)) + (q (u (i + 1)) - q (u i)))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => hinc i)).symm
    _ = ENNReal.ofReal ((p (u n) - p (u 0)) + (q (u n) - q (u 0))) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun i => p (u i)),
        Finset.sum_range_sub (fun i => q (u i))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      linarith [(hpb (u n)).2, (hpb (u 0)).1, (hqb (u n)).2, (hqb (u 0)).1])

private theorem p_zero_extension (u v U : ℝ) (f : ℝ → ℝ)
    (huv : u ≤ v) (hU : 0 ≤ U) (hf : AntitoneOn f (Icc u v))
    (hb : ∀ x ∈ Icc u v, 0 ≤ f x ∧ f x ≤ U) :
    eVariationOn ((Icc u v).indicator f) univ ≤ ENNReal.ofReal (2 * U) := by
  obtain ⟨p, q, hp, hq, hpb, hqb, heq⟩ :=
    p_antitone_extended_factorization u v U f huv hU hf hb
  rw [heq]
  exact p_variation_triangle p q U hU hp hq hpb hqb

/-- A closed interval indicator in the dyadic window has supremum plus variation at most three. -/
theorem cutoff_bv (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 2) :
    BVBound ((Icc u v).indicator (fun _ : ℝ => 1)) 3 := by
  have hvar := p_zero_extension u v 1 (fun _ : ℝ => 1) huv zero_le_one
    (fun _ _ _ _ _ => le_rfl) (fun _ _ => ⟨zero_le_one, le_rfl⟩)
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar, ?_, by norm_num,
    1, zero_le_one, ?_, ?_⟩
  · intro t ht
    apply Set.indicator_of_notMem
    exact fun h => ht ⟨hu.trans h.1, h.2.trans hv⟩
  · intro t
    by_cases ht : t ∈ Icc u v <;> simp [ht]
  · have hreal := ENNReal.toReal_le_of_le_ofReal (by norm_num : (0 : ℝ) ≤ 2 * 1) hvar
    linarith

/-- A logarithmic block weight in the dyadic window has supremum plus variation at most 3/log 2. -/
theorem log_block_bv (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 2) :
    BVBound ((Icc u v).indicator (fun t : ℝ => 1 / (t * Real.log 2)))
      (3 / Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos (x : ℝ) (hx : x ∈ Icc u v) : 0 < x * Real.log 2 :=
    mul_pos (lt_of_lt_of_le zero_lt_one (hu.trans hx.1)) hlog
  have hanti : AntitoneOn (fun t : ℝ => 1 / (t * Real.log 2)) (Icc u v) := by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le (hpos x hx)
      (mul_le_mul_of_nonneg_right hxy hlog.le)
  have hb (x : ℝ) (hx : x ∈ Icc u v) :
      0 ≤ 1 / (x * Real.log 2) ∧ 1 / (x * Real.log 2) ≤ 1 / Real.log 2 := by
    refine ⟨(one_div_pos.mpr (hpos x hx)).le, one_div_le_one_div_of_le hlog ?_⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu.trans hx.1) hlog.le
  have hvar := p_zero_extension u v (1 / Real.log 2)
    (fun t : ℝ => 1 / (t * Real.log 2)) huv (by positivity) hanti hb
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar, ?_, by positivity,
    1 / Real.log 2, by positivity, ?_, ?_⟩
  · intro t ht
    apply Set.indicator_of_notMem
    exact fun h => ht ⟨hu.trans h.1, h.2.trans hv⟩
  · intro t
    by_cases ht : t ∈ Icc u v
    · simpa only [Set.indicator_of_mem ht, abs_of_nonneg (hb t ht).1] using (hb t ht).2
    · simp only [Set.indicator_of_notMem ht, abs_zero]
      positivity
  · calc
      _ ≤ 1 / Real.log 2 + 2 * (1 / Real.log 2) :=
        add_le_add le_rfl (ENNReal.toReal_le_of_le_ofReal (by positivity) hvar)
      _ = 3 / Real.log 2 := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
