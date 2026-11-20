/- GID: D5/S3/ConceptDynamics/Attribution/MonotoneSeedCalibration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/MonotoneSeedCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict increases in the mass of nested events require distinct positive-mass seeds. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Choose

namespace D5.S3.ConceptDynamics.Attribution.MonotoneSeedCalibration

/-- Each strict increase in the mass of a nested event has a distinct positive-mass witness. -/
theorem positive_seed_embedding {S : Type*} [DecidableEq S]
    {m : ℕ} (events : ℕ → Finset S) (weight : S → ℝ)
    (nested : MonotoneOn events (Set.Iic m))
    (increasing : StrictMonoOn (fun k => ∑ s ∈ events k, weight s) (Set.Iic m)) :
    ∃ seed : Fin m ↪ {s : S // 0 < weight s},
      ∀ k, (seed k).val ∈ events (k.val + 1) ∧ (seed k).val ∉ events k.val := by
  classical
  have increment (k : Fin m) :
      ∃ s ∈ events (k.val + 1) \ events k.val, 0 < weight s := by
    have step := nested k.isLt.le (Nat.succ_le_of_lt k.isLt) (Nat.le_succ k.val)
    have mass := increasing k.isLt.le (Nat.succ_le_of_lt k.isLt) (Nat.lt_succ_self k.val)
    have addMass := Finset.sum_sdiff (f := weight) step
    have positive : 0 < ∑ s ∈ events (k.val + 1) \ events k.val, weight s := by
      dsimp only at mass
      simpa only [← addMass, add_sub_cancel_right] using sub_pos.mpr mass
    by_contra h
    apply (not_le_of_gt positive)
    exact Finset.sum_nonpos fun s hs => le_of_not_gt fun hpos => h ⟨s, hs, hpos⟩
  choose seed membership positive using increment
  have in_next (k : Fin m) : seed k ∈ events (k.val + 1) :=
    (Finset.mem_sdiff.mp (membership k)).1
  have not_in_current (k : Fin m) : seed k ∉ events k.val :=
    (Finset.mem_sdiff.mp (membership k)).2
  have distinct {i j : Fin m} (h : i < j) : seed i ≠ seed j := by
    intro same
    have within := nested (Nat.succ_le_of_lt i.isLt) j.isLt.le (Nat.succ_le_of_lt h)
    exact not_in_current j (same ▸ within (in_next i))
  refine ⟨⟨fun k => ⟨seed k, positive k⟩, ?_⟩, fun k => ⟨in_next k, not_in_current k⟩⟩
  intro i j same
  have sameSeed := congrArg Subtype.val same
  rcases lt_trichotomy i j with h | h | h
  · exact (distinct h sameSeed).elim
  · exact h
  · exact (distinct h sameSeed.symm).elim

end D5.S3.ConceptDynamics.Attribution.MonotoneSeedCalibration
