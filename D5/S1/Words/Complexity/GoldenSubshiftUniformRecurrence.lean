/- GID: D5/S1/Words/Complexity/GoldenSubshiftUniformRecurrence
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/GoldenSubshiftUniformRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-subshift observers share one finite recurrence window for each factor. -/

import D5.S1.Words.Complexity.GoldenSubshiftMinimality

/- Provenance: Native proof over existing golden-word recurrence and subshift primitives. -/

/-! SEARCH RECEIPT (2026-09-02, current repository and pinned mathlib):
Repository searches for uniform recurrence, the golden recurrence bound, and
membership in the golden word subshift found the explicit bound and recurrence
for the distinguished word in `GoldenUniformRecurrence.lean`, and the canonical
subshift carrier and factor-language theorems in
`GoldenSubshiftMinimality.lean`. No public theorem quantified the bounded-window
conclusion over every member of the golden subshift and every starting index.
Pinned-mathlib searches for syndetic sets, uniform recurrence, return times,
and compact minimal actions found only the general group-action finite-cover
lemma `IsCompact.exists_finite_cover_smul`; it is not the word-level statement
and is not used here. -/

namespace D5.S1.Words.Complexity.GoldenSubshiftUniformRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Words
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.SubshiftHausdorffDimension

/-- Every admissible golden factor occurs wholly within the same bounded window
from every starting position of every observer in the golden subshift. -/
theorem golden_subshift_factor_uniformly_recurrent
    {n : Nat} {w : List Bool} (hw : w ∈ goldenFactorSet n) :
    ∃ R : Nat, ∀ y : Nat → Bool, y ∈ wordSubshift goldenWord →
      ∀ i : Nat, ∃ j : Nat,
        i ≤ j ∧ j + n ≤ i + R ∧ w = List.ofFn (wordFactor y n j) := by
  refine ⟨goldenRecurrenceBound n, ?_⟩
  intro y hy i
  obtain ⟨q, hq⟩ := mem_wordFactorSet.mp (hy (i + goldenRecurrenceBound n))
  obtain ⟨k, hstart, hend, hfactor⟩ :=
    golden_factor_uniformly_recurrent hw (q + i)
  let j := k - q
  have hqk : q ≤ k := by omega
  have hij : i ≤ j := by
    dsimp [j]
    omega
  have hjend : j + n ≤ i + goldenRecurrenceBound n := by
    dsimp [j]
    omega
  refine ⟨j, hij, hjend, ?_⟩
  rw [hfactor, goldenFactor]
  apply List.ofFn_inj.mpr
  funext t
  have ht : j + t.val < i + goldenRecurrenceBound n := by
    have := t.isLt
    omega
  have hyq := congrFun hq ⟨j + t.val, ht⟩
  have hindex : q + (j + t.val) = k + t.val := by
    dsimp [j]
    omega
  change goldenWord (k + t.val) = y (j + t.val)
  simpa only [wordFactor, hindex] using hyq.symm

#print axioms golden_subshift_factor_uniformly_recurrent

end D5.S1.Words.Complexity.GoldenSubshiftUniformRecurrence
