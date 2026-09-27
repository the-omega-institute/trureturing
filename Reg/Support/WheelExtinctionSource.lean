import D5.S3.Combinatorics.WheelHivExtinctionRefutation
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.Support.WheelExtinctionSource
open _root_.D5.S3.Combinatorics.WheelHivExtinctionRefutation

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => extinctionSet n (wheelAdj n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n =>
    (if Even n then {3} else {4}) ∪ {R | n - 1 ≤ R}) (fun e => nomatch e)

/-- Both original parity branches, all size guards and the complete negation. -/
abbrev arena : Arena where
  signature := signature
  Law r := ¬ ((∀ n : ℕ, Even n → 12 ≤ n →
    r.readout () () n = {3} ∪ {R | n - 1 ≤ R}) ∧
    (∀ n : ℕ, Odd n → 17 ≤ n → r.readout () () n = {4} ∪ {R | n - 1 ≤ R}))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  constructor
  · intro n hn _
    simp [rejected, realize, hn]
  · intro n hn _
    have notEven : ¬ Even n := by
      rintro ⟨k, hk⟩
      obtain ⟨j, hj⟩ := hn
      omega
    simp [rejected, realize, notEven]

private def initial : Fin 2 → Fin 2 := fun v => if v = 0 then 1 else 0
private def first : Fin 2 → Fin 3 := fun v => if v = 0 then 2 else 1
private def second : Fin 2 → Fin 3 := fun v => if v = 0 then 1 else 2

theorem two_not_extinct : 1 ∉ extinctionSet 2 (wheelAdj 2) := by
  intro h
  obtain ⟨t, ht⟩ := h.2 initial
  have first_step : step (wheelAdj 2) 1 (fun v => (initial v).castSucc) = first := by decide
  have second_step : step (wheelAdj 2) 1 first = second := by decide
  have return_step : step (wheelAdj 2) 1 second = first := by decide
  have orbit : ∀ t : ℕ, (step (wheelAdj 2) 1)^[t] (fun v => (initial v).castSucc) =
      (fun v => (initial v).castSucc) ∨
      (step (wheelAdj 2) 1)^[t] (fun v => (initial v).castSucc) = first ∨
      (step (wheelAdj 2) 1)^[t] (fun v => (initial v).castSucc) = second := by
    intro t
    induction t with
    | zero => exact Or.inl rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h | h
      · rw [h, first_step]
        exact Or.inr (Or.inl rfl)
      · rw [h, second_step]
        exact Or.inr (Or.inr rfl)
      · rw [h, return_step]
        exact Or.inr (Or.inl rfl)
  rcases orbit t with h | h | h <;> rw [h] at ht <;>
    have e := congrFun ht 0 <;> contradiction

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 0, 2, ?_⟩
  intro h
  change extinctionSet 0 (wheelAdj 0) = extinctionSet 2 (wheelAdj 2) at h
  have zero : 1 ∈ extinctionSet 0 (wheelAdj 0) :=
    ⟨by decide, fun _ => ⟨0, funext fun v => Fin.elim0 v⟩⟩
  exact two_not_extinct (h ▸ zero)

/-- The same extinction-set function supplies both parity readings. Interventions
replace that complete function in both clauses and preserve every original guard. -/
def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.WheelHivExtinctionRefutation.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

#print axioms registration
end Reg.Support.WheelExtinctionSource
