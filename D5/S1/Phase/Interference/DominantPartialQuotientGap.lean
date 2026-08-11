/- GID: D5/S1/Phase/Interference/DominantPartialQuotientGap
   generality: G
   mirror-B: D5/B/S1/Phase/Interference/DominantPartialQuotientGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A dominant term leaves a reverse-triangle lower gap for a finite complex sum. -/

import Mathlib.Analysis.Complex.Basic

/- Library-search audit trail (2026-08-11):
   * The pinned mathlib tree and all repository Lean files were searched for
     `dominant_partial`, `gap lemma`, `norm_sub_norm_le`, `norm_sum_le`, and finite-sum variants.
   * No theorem packages a selected `Finset` term and its erased complement in this form.
     `D5.S1.Phase.SeatTowerConsequences.dominant_term_gap_bound` is the nearest repository result,
     but it is an unconditional integer leading-term bound rather than a selected finite complex
     family with a dominance hypothesis and an asserted nonnegative gap.
   * Mathlib already supplies the two substantive inequalities: `norm_sub_norm_le` is the reverse
     triangle inequality and `norm_sum_le` bounds the norm of a finite sum by the sum of norms.
     The proof below is only the named finite-complex-family wrapper, with
     `Finset.sum_erase_add` restoring the full sum.
-/

namespace D5.S1.Phase.Interference.DominantPartialQuotientGap

/-- If one selected term dominates the sum of the norms of all other supported terms, then its
nonnegative dominance gap is a lower bound for the norm of the full finite sum. -/
theorem dominant_partial_quotient_gap
    {ι : Type*} [DecidableEq ι]
    (support : Finset ι) (terms : ι → ℂ) (dominant : ι)
    (hDominantMem : dominant ∈ support)
    (hDominates :
      ∑ i ∈ support.erase dominant, ‖terms i‖ ≤ ‖terms dominant‖) :
    0 ≤ ‖terms dominant‖ - ∑ i ∈ support.erase dominant, ‖terms i‖ ∧
      ‖terms dominant‖ - ∑ i ∈ support.erase dominant, ‖terms i‖ ≤
        ‖∑ i ∈ support, terms i‖ := by
  constructor
  · exact sub_nonneg.mpr hDominates
  · have hRestNorm :
        ‖∑ i ∈ support.erase dominant, terms i‖ ≤
          ∑ i ∈ support.erase dominant, ‖terms i‖ :=
      norm_sum_le (support.erase dominant) terms
    calc
      ‖terms dominant‖ - ∑ i ∈ support.erase dominant, ‖terms i‖ ≤
          ‖terms dominant‖ - ‖∑ i ∈ support.erase dominant, terms i‖ :=
        sub_le_sub_left hRestNorm _
      _ ≤ ‖terms dominant + ∑ i ∈ support.erase dominant, terms i‖ := by
        simpa only [sub_neg_eq_add, norm_neg] using
          norm_sub_norm_le (terms dominant)
            (-(∑ i ∈ support.erase dominant, terms i))
      _ = ‖(∑ i ∈ support.erase dominant, terms i) + terms dominant‖ := by
        rw [add_comm]
      _ = ‖∑ i ∈ support, terms i‖ := by
        rw [Finset.sum_erase_add _ _ hDominantMem]

/-- The two-term family `(2, -1)` is strictly dominated by its first term, has positive gap one,
and attains the gap lower bound. -/
theorem strict_dominance_positive_gap_example :
    let terms : Fin 2 → ℂ := fun i => if i = 0 then 2 else -1
    (∑ i ∈ Finset.univ.erase (0 : Fin 2), ‖terms i‖) < ‖terms 0‖ ∧
      0 < ‖terms 0‖ - ∑ i ∈ Finset.univ.erase (0 : Fin 2), ‖terms i‖ ∧
      ‖terms 0‖ - ∑ i ∈ Finset.univ.erase (0 : Fin 2), ‖terms i‖ ≤
        ‖∑ i, terms i‖ := by
  dsimp only
  have hDominates :
      (∑ i ∈ Finset.univ.erase (0 : Fin 2),
        ‖(if i = 0 then (2 : ℂ) else -1)‖) ≤
        ‖(if (0 : Fin 2) = 0 then (2 : ℂ) else -1)‖ := by
    norm_num [Fin.sum_univ_two]
  have hGap := dominant_partial_quotient_gap
    (Finset.univ : Finset (Fin 2))
    (fun i => if i = 0 then (2 : ℂ) else -1)
    (0 : Fin 2)
    (Finset.mem_univ _)
    hDominates
  refine ⟨?_, ?_, hGap.2⟩ <;> norm_num [Fin.sum_univ_two]

end D5.S1.Phase.Interference.DominantPartialQuotientGap
