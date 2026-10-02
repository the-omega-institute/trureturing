import D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
import Reg.Support.DependentFamily

open _root_.D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open _root_.D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau

local notation "F" => Nat.fib
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ mt => heightDeficit mt.1 mt.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ U : ℕ → ℕ, Hyp24_1 U →
    (∀ m t : ℕ, 8 ≤ m → t ≤ F (m - 2) →
      C (F m - t) ≤ F (m - 1) ∧
      (heightDeficit m t = 0 ↔ t ≤ platformWidth m) ∧
      (platformWidth m < t → 1 ≤ heightDeficit m t ∧
        heightDeficit m t ≤ max 1 (t - platformWidth m - 1))) ∧
    (∀ W m : ℕ, max 8 ((3 * W + 10) / 2) ≤ m →
      ∀ t : ℕ, t ≤ W → C (F m - t) = F (m - 1)) ∧
    (∀ j b : ℕ, 9 ≤ j → b ≤ F (j - 1) →
      let N := F (j + 1) - b
      let z := F j - g N
      let w := F (j - 1) - (N - g N)
      g N = F j - z ∧ N - g N = F (j - 1) - w ∧ z + w = b ∧
      z ≤ F (j - 2) ∧ w ≤ F (j - 3) ∧
      (heightDeficit (j + 1) b = 0 ↔
        (b ≤ platformWidth j ∧ z = b ∧ w = 0) ∨
        (b = platformWidth j + 1 ∧ Odd (F j) ∧ z = platformWidth j ∧ w = 1))) ∧
    (∀ j : ℕ, 9 ≤ j →
      let N := F (j + 1) - (platformWidth j + 1)
      Function.minimalPeriod (T N) (g N) = 2 ∧ d N = F j - 1 ∧
      g N = if Odd (F j) then F j - platformWidth j else F j - platformWidth j - 1)

def familyStatement (q : ℕ → ℕ → ℕ) : Prop := ∀ U : ℕ → ℕ, Hyp24_1 U →
    (∀ m t : ℕ, 8 ≤ m → t ≤ F (m - 2) →
      C (F m - t) ≤ F (m - 1) ∧
      (q m t = 0 ↔ t ≤ platformWidth m) ∧
      (platformWidth m < t → 1 ≤ q m t ∧
        q m t ≤ max 1 (t - platformWidth m - 1))) ∧
    (∀ W m : ℕ, max 8 ((3 * W + 10) / 2) ≤ m →
      ∀ t : ℕ, t ≤ W → C (F m - t) = F (m - 1)) ∧
    (∀ j b : ℕ, 9 ≤ j → b ≤ F (j - 1) →
      let N := F (j + 1) - b
      let z := F j - g N
      let w := F (j - 1) - (N - g N)
      g N = F j - z ∧ N - g N = F (j - 1) - w ∧ z + w = b ∧
      z ≤ F (j - 2) ∧ w ≤ F (j - 3) ∧
      (q (j + 1) b = 0 ↔
        (b ≤ platformWidth j ∧ z = b ∧ w = 0) ∨
        (b = platformWidth j + 1 ∧ Odd (F j) ∧ z = platformWidth j ∧ w = 1))) ∧
    (∀ j : ℕ, 9 ≤ j →
      let N := F (j + 1) - (platformWidth j + 1)
      Function.minimalPeriod (T N) (g N) = 2 ∧ d N = F j - 1 ∧
      g N = if Odd (F j) then F j - platformWidth j else F j - platformWidth j - 1)

def arena : Arena where
  signature := signature
  Law R := familyStatement (fun m t => R.readout () () (m, t))

theorem source_bridge : sourceStatement ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := by
  intro U h
  exact full24_3 U h

/-- Constant-one intervention rejects the complete law exactly when its unchanged
source premises have an instance. -/
theorem rejected_iff_source_inhabited :
    ¬ arena.Law rejected ↔ ∃ U : ℕ → ℕ, Hyp24_1 U := by
  classical
  constructor
  · intro hbad
    by_contra hn
    apply hbad
    intro U h
    exact False.elim (hn ⟨U, h⟩)
  · rintro ⟨U, h⟩ hbad
    have hr := (hbad U h).1 8 0 (by omega) (by norm_num)
    have hz := hr.2.1.mpr (show 0 ≤ platformWidth 8 by omega)
    change (1 : ℕ) = 0 at hz
    omega

/-- Whole-family variation of this complete conditional source is equivalent
to inhabitance of its full premise bundle. -/
theorem variation_iff_source_inhabited :
    Variation arena actual ↔ ∃ U : ℕ → ℕ, Hyp24_1 U := by
  classical
  constructor
  · intro hv
    obtain ⟨bad, hbad⟩ := hv.2
    by_contra hn
    apply hbad
    intro U h
    exact False.elim (hn ⟨U, h⟩)
  · intro hs
    exact ⟨actual_positive, rejected, rejected_iff_source_inhabited.mpr hs⟩

/-- An inhabited source permits a genuine intervention with every other role
and every anchor held fixed. -/
theorem sensitivity_of_source_inhabited (hs : ∃ U : ℕ → ℕ, Hyp24_1 U) :
    Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_iff_source_inhabited.mpr hs⟩
    · intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · funext e; exact nomatch e
  · intro e; exact nomatch e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2400000 in
-- Kernel reduction of the actual finite-prefix values needs these elaboration bounds.
/-- The actual deficit observation distinguishes two legal points in the same row. -/
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (8, 0), (8, 3), ?_⟩
  change heightDeficit 8 0 ≠ heightDeficit 8 3
  decide +kernel

#print axioms source_bridge
#print axioms actual_positive
#print axioms rejected_iff_source_inhabited
#print axioms variation_iff_source_inhabited
#print axioms sensitivity_of_source_inhabited
#print axioms actual_dependence

end
end Reg.D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
