/- GID: D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder
   generality: G
   mirror-B: D5/B/S3/CompletionDynamics/ObserverJet/FirstBreakOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first nonzero normal jet order is totalized in WithTop Nat, with infinity recording threads whose every finite jet remains unbroken. -/

import Mathlib

/-!
The source minimum is only defined when some finite normal jet is nonzero.
Using `WithTop ℕ` makes the definition total: `⊤` means that no positive finite
order witnesses a break.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.ObserverJet.FirstBreakOrder

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A positive finite order at which the normal jet is nonzero. -/
def IsBreakOrder (breaks : ℕ → Prop) (k : ℕ) : Prop :=
  0 < k ∧ breaks k

/-- First positive break order, with `⊤` when every finite jet is unbroken. -/
def firstBreakOrder (breaks : ℕ → Prop) : WithTop ℕ :=
  by
    classical
    exact if h : ∃ k, IsBreakOrder breaks k then
      (Nat.find h : WithTop ℕ)
    else
      ⊤

/-- Absence of every positive finite break is represented exactly by `⊤`. -/
theorem first_break_order_eq_top_iff (breaks : ℕ → Prop) :
    firstBreakOrder breaks = ⊤ ↔
      ¬ ∃ k, IsBreakOrder breaks k := by
  classical
  unfold firstBreakOrder
  by_cases h : ∃ k, IsBreakOrder breaks k
  · simp [h]
  · simp [h]

/-- Under an existence witness, the totalized order is the ordinary least
natural-number witness. -/
theorem first_break_order_of_exists
    {breaks : ℕ → Prop} (h : ∃ k, IsBreakOrder breaks k) :
    firstBreakOrder breaks = (Nat.find h : WithTop ℕ) := by
  classical
  simp [firstBreakOrder, h]

/-- The selected finite order is a genuine positive break. -/
theorem first_break_order_spec
    {breaks : ℕ → Prop} (h : ∃ k, IsBreakOrder breaks k) :
    IsBreakOrder breaks (Nat.find h) :=
  Nat.find_spec h

/-- No smaller order is an admissible break. -/
theorem no_break_before_first
    {breaks : ℕ → Prop} (h : ∃ k, IsBreakOrder breaks k)
    {j : ℕ} (hj : j < Nat.find h) :
    ¬ IsBreakOrder breaks j :=
  Nat.find_min h hj

/-- A first-order break means that order one is the least positive nonzero jet. -/
theorem first_order_break_characterization
    {breaks : ℕ → Prop}
    (hOne : breaks 1) :
    firstBreakOrder breaks = (1 : WithTop ℕ) := by
  classical
  have hAtOne : IsBreakOrder breaks 1 := ⟨by omega, hOne⟩
  have hExists : ∃ k, IsBreakOrder breaks k := ⟨1, hAtOne⟩
  rw [first_break_order_of_exists hExists]
  congr 1
  have hLe : Nat.find hExists ≤ 1 := Nat.find_min' hExists hAtOne
  have hPos : 0 < Nat.find hExists := (Nat.find_spec hExists).1
  have hFind : Nat.find hExists = 1 := by omega
  exact hFind

/-- If order one vanishes and order two breaks, the first break is quadratic. -/
theorem quadratic_break_characterization
    {breaks : ℕ → Prop}
    (hOne : ¬ breaks 1) (hTwo : breaks 2) :
    firstBreakOrder breaks = (2 : WithTop ℕ) := by
  classical
  have hAtTwo : IsBreakOrder breaks 2 := ⟨by omega, hTwo⟩
  have hExists : ∃ k, IsBreakOrder breaks k := ⟨2, hAtTwo⟩
  rw [first_break_order_of_exists hExists]
  congr 1
  have hLe : Nat.find hExists ≤ 2 := Nat.find_min' hExists hAtTwo
  have hPos : 0 < Nat.find hExists := (Nat.find_spec hExists).1
  have hNotOne : Nat.find hExists ≠ 1 := by
    intro hEq
    exact hOne (hEq ▸ (Nat.find_spec hExists).2)
  have hFind : Nat.find hExists = 2 := by omega
  exact hFind

/-- Probe showing why `WithTop` is required. -/
example : firstBreakOrder (fun _ : ℕ => False) = ⊤ := by
  rw [first_break_order_eq_top_iff]
  simp [IsBreakOrder]

#print axioms first_break_order_eq_top_iff
#print axioms first_break_order_of_exists
#print axioms first_break_order_spec
#print axioms no_break_before_first
#print axioms first_order_break_characterization
#print axioms quadratic_break_characterization

end D5.S3.CompletionDynamics.ObserverJet.FirstBreakOrder
