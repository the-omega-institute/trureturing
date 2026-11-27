/- GID: D5/S3/Weil/ZetaRvm/InclusiveCountLimit
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaRvm/InclusiveCountLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds off zero ordinates extend to inclusive counts at the same envelope. -/

import D5.S3.Weil.ZetaRvm.Defs

/-! Transfer estimates to inclusive zero ordinates by approaching from above. -/

open Filter Set
open scoped Topology

namespace D5.S3.Weil.ZetaRvm.InclusiveCountLimit

open Zeta23 (IsNontrivialZero Ncount zerosIn zerosIn_finite)
open Zeta23.RvM (GoodHeight)

/-- Immediately above a cutoff, the height is zero-free and the inclusive count is constant. -/
theorem eventually_goodHeight_and_count_eq (T : ℝ) :
    ∀ᶠ t in 𝓝[>] T, GoodHeight t ∧ Ncount 0 t = Ncount 0 T := by
  let heights := Complex.im '' zerosIn T (T + 1)
  have hfinite : heights.Finite := (zerosIn_finite T (T + 1)).image _
  have hT : T ∈ heightsᶜ := by
    rintro ⟨ρ, hρ, him⟩
    exact (ne_of_gt hρ.2.1) him
  have hOpen : IsOpen (Iio (T + 1) ∩ heightsᶜ) := isOpen_Iio.inter hfinite.isClosed.isOpen_compl
  have hMem : T ∈ Iio (T + 1) ∩ heightsᶜ :=
    ⟨show T < T + 1 by linarith, hT⟩
  obtain ⟨U, hTU, hsub⟩ := exists_Ico_subset_of_mem_nhds'
    (hOpen.mem_nhds hMem) (show T < T + 1 by linarith)
  filter_upwards [Ioo_mem_nhdsGT hTU.1] with t ht
  have noZero (ρ : ℂ) (hρ : IsNontrivialZero ρ) (hlo : T < ρ.im)
      (hhi : ρ.im ≤ t) : False := by
    have hh := hsub ⟨hlo.le, hhi.trans_lt ht.2⟩
    exact hh.2 ⟨ρ, ⟨hρ, hlo, hh.1.le⟩, rfl⟩
  constructor
  · intro ρ hρ hEq
    exact noZero ρ hρ (hEq ▸ ht.1) (le_of_eq hEq)
  · unfold Ncount
    have hsets : zerosIn 0 t = zerosIn 0 T := by
      ext ρ
      constructor
      · intro hρ
        refine ⟨hρ.1, hρ.2.1, ?_⟩
        by_contra! hlo
        exact noZero ρ hρ.1 hlo hρ.2.2
      · intro hρ
        exact ⟨hρ.1, hρ.2.1, hρ.2.2.trans ht.1.le⟩
    rw [hsets]

/-- A right-continuous error envelope at zero-free heights bounds the inclusive count everywhere. -/
theorem abs_ncount_sub_le_of_goodHeight {T₀ : ℝ} {M E : ℝ → ℝ}
    (hM : ∀ T ≥ T₀, ContinuousWithinAt M (Ioi T) T)
    (hE : ∀ T ≥ T₀, ContinuousWithinAt E (Ioi T) T)
    (hbound : ∀ T ≥ T₀, GoodHeight T → |(Ncount 0 T : ℝ) - M T| ≤ E T)
    {T : ℝ} (hT : T₀ ≤ T) : |(Ncount 0 T : ℝ) - M T| ≤ E T := by
  have hnear := eventually_goodHeight_and_count_eq T
  have hN : Tendsto (fun t : ℝ => (Ncount 0 t : ℝ)) (𝓝[>] T)
      (𝓝 (Ncount 0 T : ℝ)) := by
    apply tendsto_const_nhds.congr'
    exact hnear.mono fun t ht => by simpa only using congrArg (fun n : ℕ => (n : ℝ)) ht.2.symm
  refine le_of_tendsto_of_tendsto ((hN.sub (hM T hT)).abs) (hE T hT) ?_
  filter_upwards [hnear, self_mem_nhdsWithin (s := Ioi T)] with t ht hright
  exact hbound t (hT.trans (show T < t from hright).le) ht.1

#print axioms abs_ncount_sub_le_of_goodHeight
end D5.S3.Weil.ZetaRvm.InclusiveCountLimit
