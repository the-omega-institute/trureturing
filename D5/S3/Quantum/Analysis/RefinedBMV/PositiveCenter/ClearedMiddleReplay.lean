/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleReplay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Replay the elementary and four corner checks for a cleared middle-gap rectangle. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleGrid

/-! Replay the cleared middle-gap checks and prove the mixed derivative sign on checked leaves. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid

open private CompactMiddleBox.elementaryChecks from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

/-- The interval model used by the cleared scores on this leaf. -/
def Leaf.model (leaf : Leaf) : CompactMiddleBox :=
  CompactMiddleBox.ofIntervals leaf.box.uLo leaf.box.uHi leaf.box.dLo leaf.box.dHi

/-- The analytic input tests and the signed tests at all four corners. -/
def Leaf.Checked (leaf : Leaf) : Prop :=
  leaf.model.ClearedChecks ∧ ∀ a b : Bool, leaf.model.ClearedEndpointTests leaf.box.dLo a b

theorem Leaf.checked_of_tests (leaf : Leaf) (helem : leaf.model.ClearedChecks)
    (hdegree : leaf.degree ≤ 4)
    (hzero : ∀ a b : Bool, leaf.model.clearedZeroCheck leaf.box.dLo a b = true)
    (hupper : ∀ a b : Bool, leaf.model.clearedUpperCheck leaf.box.dLo a b leaf.degree = true) :
    leaf.Checked :=
  ⟨helem, fun a b ↦ leaf.model.clearedEndpointTests_of_checks leaf.box.dLo a b leaf.degree
    hdegree (hzero a b) (hupper a b)⟩

/-- Check one concrete leaf with separate kernel decisions for the elementary
inequalities, degree cap, and each of the eight score tests. -/
scoped macro "replay_cleared_middle_leaf" : tactic => `(tactic| (
  apply Leaf.checked_of_tests
  · constructor
    all_goals
      simp only [CompactMiddleBox.elementaryChecks, Model.expChecks]
      repeat' apply And.intro
      all_goals decide +kernel
  · decide +kernel
  · intro a b
    cases a <;> cases b <;> decide +kernel
  · intro a b
    cases a <;> cases b <;> decide +kernel))

/-- The strict mixed derivative sign throughout a closed rectangle, uniformly in the rate. -/
def Rectangle.MixedNegative (r : Rectangle) : Prop :=
  ∀ {p : ℕ} {u v : ℝ}, 11 ≤ p → r.Contains u (v - u) →
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0

theorem Leaf.mixedNegative_of_checked {leaf : Leaf} (hv : leaf.box.Valid) (hc : leaf.Checked) :
    leaf.box.MixedNegative := by
  intro p u v hp hmem
  obtain ⟨⟨huMin, huWidth, huMax⟩, ⟨hdMin, hdWidth, _⟩⟩ := hv
  obtain ⟨huLo, huHi, hdLo, hdHi⟩ := hmem
  exact CompactMiddleBox.mixed_neg_of_cleared_interval_checks hp huMin huMax hdMin
    huWidth hdWidth huLo huHi hdLo hdHi hc.1 hc.2

theorem leaves_length : leaves.length = 39 := by decide +kernel

/-- Zero-based index in the grid's evidence order. -/
def leafAt (i : Fin 39) : Leaf :=
  leaves.get (i.cast leaves_length.symm)

theorem leafAt_mem (i : Fin 39) : leafAt i ∈ leaves :=
  List.get_mem leaves (i.cast leaves_length.symm)

/-- A contiguous set of leaves may be replayed as one build target. -/
def batchIndex (start : ℕ) {count : ℕ} (h : start + count ≤ 39) (i : Fin count) : Fin 39 :=
  ⟨start + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt start) h⟩

theorem mixedNegative_of_batch {start count : ℕ} {h : start + count ≤ 39}
    (checked : ∀ j : Fin count, (leafAt (batchIndex start h j)).Checked)
    {i : Fin 39} (hlo : start ≤ i.val) (hhi : i.val < start + count) :
    (leafAt i).box.MixedNegative := by
  let j : Fin count := ⟨i.val - start, by omega⟩
  have heq : batchIndex start h j = i := by
    apply Fin.ext
    change start + (i.val - start) = i.val
    omega
  have hc := checked j
  rw [heq] at hc
  intro p u v hp hmem
  exact Leaf.mixedNegative_of_checked (valid_of_mem_leaves (leafAt_mem i)) hc hp hmem

end RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid
