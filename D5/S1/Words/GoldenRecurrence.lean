/- GID: D5/S1/Words/GoldenRecurrence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:qualitative-recurrence-is-formal-only)
   anchors: []
   digest: Every finite golden-word factor recurs at arbitrarily large starting positions. -/

import D5.S1.Words.GoldenFactorComplexity

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord

private theorem goldenFactor_exists_later (n i : Nat) :
    ∃ j, i < j ∧ goldenFactor n i = goldenFactor n j := by
  let Q := i + n
  let j := (fibWord (Q + 1)).length + i
  have hwindow (k : Nat) (hk : k < n) : i + k < (fibWord Q).length := by
    have hdiag := index_lt_diagonal_level Q
    dsimp [Q] at hdiag ⊢
    omega
  have hlater (k : Nat) (hk : k < n) : j + k < (fibWord (Q + 2)).length := by
    rw [fibWord_append_rec, List.length_append]
    simpa [j, Nat.add_assoc] using
      Nat.add_lt_add_left (hwindow k hk) (fibWord (Q + 1)).length
  have hcopy (k : Nat) (hk : k < n) :
      (fibWord (Q + 2))[j + k]'(hlater k hk) =
        (fibWord Q)[i + k]'(hwindow k hk) := by
    have hprefix : (fibWord (Q + 1)).length ≤ j + k := by
      dsimp [j]
      omega
    simp only [fibWord_append_rec]
    rw [List.getElem_append_right hprefix]
    simp [j, Nat.add_assoc]
  refine ⟨j, ?_, ?_⟩
  · have hpositive := index_lt_diagonal_level (Q + 1)
    dsimp [j]
    omega
  · apply List.ext_get (by simp [goldenFactor])
    intro k hkleft hkright
    have hk : k < n := by simpa [goldenFactor] using hkleft
    simpa [goldenFactor] using
      (goldenWord_eq_fibWord_get Q (i + k) (hwindow k hk)).trans
        ((hcopy k hk).symm.trans
          (goldenWord_eq_fibWord_get (Q + 2) (j + k) (hlater k hk)).symm)

/-- Every factor of the golden word occurs beyond every natural threshold. -/
theorem golden_factor_recurrent {n : Nat} {w : List Bool}
    (hw : w ∈ goldenFactorSet n) :
    ∀ B, ∃ j, B < j ∧ w = goldenFactor n j := by
  obtain ⟨i, rfl⟩ := mem_goldenFactorSet.mp hw
  intro B
  induction B with
  | zero =>
      obtain ⟨j, hij, hfactor⟩ := goldenFactor_exists_later n i
      exact ⟨j, Nat.zero_lt_of_lt hij, hfactor⟩
  | succ B ih =>
      obtain ⟨j, hBj, hfactor⟩ := ih
      obtain ⟨k, hjk, hnext⟩ := goldenFactor_exists_later n j
      exact ⟨k, by omega, hfactor.trans hnext⟩

example {n : Nat} {w : List Bool} (hw : w ∈ goldenFactorSet n) :
    ∀ B, ∃ j, B < j ∧ w = goldenFactor n j :=
  golden_factor_recurrent hw

example : (Finset.range 3).image (goldenFactor 2) =
    {[true, false], [false, true], [true, true]} := by
  decide

example : ∀ i ∈ Finset.range 3,
    ∃ j ∈ Finset.Icc (i + 1) 7, goldenFactor 2 j = goldenFactor 2 i := by
  decide

end D5.S1.Words
