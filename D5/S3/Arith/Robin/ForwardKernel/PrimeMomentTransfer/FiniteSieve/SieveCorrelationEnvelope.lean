/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Locally bounded uniform small errors have a nonnegative decreasing tail envelope. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.FiniteSieveDefs
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FormalIntervalMomentBounds

open scoped Topology
open Set Filter
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Uniform smallness and bounded-momentScale bounds produce an antitone majorant tending to zero. -/
theorem antitone_error_envelope (k : ℕ) (M : ℝ)
    (F : ℝ → (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (hsmall : UniformIntervalSmall k F M) (hlocal : LocallyBoundedIntervalError F M) :
    ∃ η : ℝ → ℝ, (∀ H, 0 ≤ η H) ∧ AntitoneOn η (Ici 2) ∧
      Tendsto η atTop (nhds 0) ∧ ∀ H : ℝ, 2 ≤ H →
        ∀ a b : Fin k → ℝ, admissible M a b → |F H a b| ≤ η H * momentScale k H := by
  have hpos (H : ℝ) (hH : 2 ≤ H) : 0 < momentScale k H := by
    unfold momentScale
    exact Real.rpow_pos_of_pos (mul_pos (by linarith) (Real.log_pos (by linarith))) _
  let S (H : ℝ) : Set ℝ := {r | r = 0 ∨ ∃ t : ℝ, 2 ≤ t ∧ H ≤ t ∧
    ∃ a b : Fin k → ℝ, admissible M a b ∧ r = |F t a b| / momentScale k t}
  have hzero (H : ℝ) : 0 ∈ S H := Or.inl rfl
  have hne (H : ℝ) : (S H).Nonempty := ⟨0, hzero H⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hsmall 1 (by norm_num))
  obtain ⟨C, hC, hbound⟩ := hlocal (max 2 T) (le_max_left _ _)
  have hbdd (H : ℝ) : BddAbove (S H) := by
    refine ⟨max C 1, ?_⟩
    intro r hr
    rcases hr with rfl | ⟨t, ht, _, a, b, hab, rfl⟩
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
    · by_cases h : T ≤ t
      · exact ((div_le_iff₀ (hpos t ht)).mpr (by simpa using hT t h a b hab)).trans
          (le_max_right _ _)
      · exact ((div_le_iff₀ (hpos t ht)).mpr
          (hbound t ⟨ht, (le_of_not_ge h).trans (le_max_right _ _)⟩ a b hab)).trans
          (le_max_left _ _)
  let η (H : ℝ) := sSup (S H)
  have hη (H : ℝ) : 0 ≤ η H := le_csSup (hbdd H) (hzero H)
  refine ⟨η, hη, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact csSup_le_csSup (hbdd x) (hne y) (by
      intro r hr
      rcases hr with h | ⟨t, ht, hyt, a, b, hab, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, ht, hxy.trans hyt, a, b, hab, he⟩)
  · apply tendsto_order.2
    constructor
    · intro c hc
      exact Filter.Eventually.of_forall (fun H => hc.trans_le (hη H))
    · intro c hc
      obtain ⟨T, hT⟩ := eventually_atTop.mp (hsmall (c/2) (half_pos hc))
      filter_upwards [eventually_ge_atTop T] with H hH
      apply lt_of_le_of_lt (show η H ≤ c/2 from ?_) (by linarith)
      apply csSup_le (hne H)
      intro r hr
      rcases hr with rfl | ⟨t, ht, hHt, a, b, hab, rfl⟩
      · positivity
      · exact (div_le_iff₀ (hpos t ht)).mpr (hT t (hH.trans hHt) a b hab)
  · intro H hH a b hab
    apply (div_le_iff₀ (hpos H hH)).mp
    exact le_csSup (hbdd H) (Or.inr ⟨H, hH, le_rfl, a, b, hab, rfl⟩)

/-- Bounded scales permit only finitely many shift tuples, uniformly over interval endpoints. -/
private theorem correlation_bounded_on_bounded_scales (SS : Finset ℕ → ℝ)
    (k : ℕ) (M T : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, H ∈ Icc 2 T →
      ∀ a b : Fin k → ℝ, admissible M a b → |corr SS H a b| ≤ C := by
  classical
  let S := Fintype.piFinset (fun _ : Fin k => Finset.Iic ⌊M*T⌋₊)
  refine ⟨∑ d ∈ S, |center SS (Finset.univ.image d)|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro H hH a b hab
  unfold corr
  calc
    _ ≤ ∑ d ∈ (Fintype.piFinset (fun i => points H (a i) (b i))).filter
        Function.Injective, |center SS (Finset.univ.image d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        apply Fintype.mem_piFinset.mpr
        intro i
        have hi := interval_points_subset (by linarith [hH.1] : 0 ≤ H) (hab i).2.2
          (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i)
        exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hi).trans
          (Nat.floor_mono (mul_le_mul_of_nonneg_left hH.2 hM)))
      · intro d _ _
        exact abs_nonneg _

/-- On a bounded momentScale interval, correlations are uniformly bounded relative to their momentScale. -/
theorem correlation_locally_bounded (SS : Finset ℕ → ℝ) (k : ℕ)
    (M : ℝ) (hM : 0 ≤ M) : LocallyBoundedIntervalError (k := k) (fun H a b => corr SS H a b) M := by
  intro T hT
  obtain ⟨C,hC,hbound⟩ := correlation_bounded_on_bounded_scales SS k M T hM
  have hc : 0 < momentScale k 2 := by
    unfold momentScale
    exact Real.rpow_pos_of_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) _
  refine ⟨C / momentScale k 2, div_nonneg hC hc.le, ?_⟩
  intro H hH a b hab
  have hs : momentScale k 2 ≤ momentScale k H := by
    apply Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 * Real.log 2)
      (mul_le_mul hH.1 (Real.log_le_log (by norm_num) hH.1)
        (Real.log_nonneg (by norm_num)) (by linarith [hH.1]))
      (by positivity)
  calc
    _ ≤ C := hbound H hH a b hab
    _ = (C / momentScale k 2) * momentScale k 2 := (div_mul_cancel₀ _ hc.ne').symm
    _ ≤ (C / momentScale k 2) * momentScale k H := mul_le_mul_of_nonneg_left hs (by positivity)

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
