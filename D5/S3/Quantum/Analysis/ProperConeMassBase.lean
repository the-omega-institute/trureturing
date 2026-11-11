/- GID: D5/S3/Quantum/Analysis/ProperConeMassBase
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/ProperConeMassBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The entire normalized base of a generating proper cone is compact and spans. -/

import D5.S3.Quantum.Analysis.CompactConvexFixedState

/-! # Entire normalized bases of real proper cones -/

namespace D5.S3.Quantum.ProperConeMassBase

open Set

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [Nontrivial A]

/-- The full normalized cone base, not a selected finite family of states. -/
def base (C : ProperCone ℝ A) (u : Module.Dual ℝ A) : Set A :=
  {x | x ∈ C ∧ u x = 1}

/-- Closedness, generating span, and strict positivity suffice for the entire compact,
nonempty convex spanning base. Strict positivity itself excludes a line in the cone. -/
theorem entire_base_geometry (C : ProperCone ℝ A) (u : Module.Dual ℝ A)
    (hgen : Submodule.span ℝ (C : Set A) = ⊤)
    (hpos : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    (base C u).Nonempty ∧ IsCompact (base C u) ∧ Convex ℝ (base C u) ∧
      Submodule.span ℝ (base C u) = ⊤ := by
  have hnonzero : ∃ x ∈ C, x ≠ 0 := by
    by_contra! hz
    have hbot : Submodule.span ℝ (C : Set A) = ⊥ :=
      Submodule.span_eq_bot.mpr (fun x hx => hz x hx)
    rw [hgen] at hbot
    exact top_ne_bot hbot
  obtain ⟨x, hx, hx0⟩ := hnonzero
  have hux : 0 < u x := hpos x hx hx0
  have hnormalized {y : A} (hy : y ∈ C) (hy0 : y ≠ 0) :
      (u y)⁻¹ • y ∈ base C u := by
    have hu := hpos y hy hy0
    exact ⟨C.smul_mem hy (inv_pos.mpr hu).le,
      by simp [map_smul, smul_eq_mul, hu.ne']⟩
  have hne : (base C u).Nonempty := ⟨_, hnormalized hx hx0⟩
  let S : Set A := {y | y ∈ C ∧ ‖y‖ = 1}
  have hsphere {y : A} (hy : y ∈ C) (hy0 : y ≠ 0) : ‖y‖⁻¹ • y ∈ S := by
    refine ⟨C.smul_mem hy (inv_nonneg.mpr (norm_nonneg y)), ?_⟩
    simp [norm_smul, norm_ne_zero_iff.mpr hy0]
  have hSclosed : IsClosed S :=
    C.isClosed.inter (isClosed_eq continuous_norm continuous_const)
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : A) 1).of_isClosed_subset hSclosed (by
      intro y hy
      simpa [Metric.mem_closedBall, dist_zero_right, hy.2])
  obtain ⟨v, hv, hmin⟩ := hScompact.exists_isMinOn ⟨_, hsphere hx hx0⟩
    u.continuous_of_finiteDimensional.continuousOn
  have hv0 : v ≠ 0 := by intro hz; simpa [hz] using hv.2
  have hvpos : 0 < u v := hpos v hv.1 hv0
  have hbound : Bornology.IsBounded (base C u) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(u v)⁻¹, ?_⟩
    intro y hy
    have hy0 : y ≠ 0 := by intro hz; simpa [hz] using hy.2
    have hnormpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hm := hmin (hsphere hy.1 hy0)
    change u v ≤ u (‖y‖⁻¹ • y) at hm
    have hmy : u v ≤ ‖y‖⁻¹ := by
      simpa only [map_smul, smul_eq_mul, hy.2, mul_one] using hm
    have hmul : u v * ‖y‖ ≤ 1 := (le_div_iff₀ hnormpos).mp (by simpa [one_div] using hmy)
    apply (le_div_iff₀ hvpos).mpr
    simpa [one_div, mul_comm] using hmul
  have hclosed : IsClosed (base C u) := C.isClosed.inter
    (isClosed_eq u.continuous_of_finiteDimensional continuous_const)
  have hconv : Convex ℝ (base C u) := by
    intro a ha b hb c d hc hd hcd
    refine ⟨C.convex ha.1 hb.1 hc hd hcd, ?_⟩
    simp only [map_add, map_smul, ha.2, hb.2, smul_eq_mul, mul_one]
    exact hcd
  refine ⟨hne, Metric.isCompact_of_isClosed_isBounded hclosed hbound, hconv, ?_⟩
  apply top_le_iff.mp
  rw [← hgen]
  apply Submodule.span_le.mpr
  intro y hy
  by_cases hy0 : y = 0
  · simpa [hy0] using (Submodule.span ℝ (base C u)).zero_mem
  · have hmem := (Submodule.span ℝ (base C u)).smul_mem (u y)
      (Submodule.subset_span (hnormalized hy hy0))
    simpa [smul_smul, (hpos y hy hy0).ne'] using hmem

end D5.S3.Quantum.ProperConeMassBase
