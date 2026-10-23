import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.ShankarWords.OddWordConstruction
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.ShankarWords.ActualWordExtremal
open _root_.D5.S3.Combinatorics.ShankarWords.OddWordConstruction

namespace Reg.D5.S3.Combinatorics.ShankarWords.OddWordConstruction

abbrev signature : Signature where
  Params := ℕ
  State := OddIndex
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t i => oddWord t i) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ t : ℕ, 1 ≤ t → Function.Injective (r.readout 0 t) ∧
    ∀ i : OddIndex t, r.readout 1 t i ∈ actualWords (2 * t + 1) ∧
      descents (r.readout 2 t i) = extremalValue (2 * t + 1)

def registration : Registration arena (type_of% (@odd_word_construction)) := by
  let bad (i : Fin 3) : Realization signature :=
    realize signature (fun j t q => if j = i then [] else oddWord t q) (fun e => nomatch e)
  have hb (i : Fin 3) : ¬ arena.Law (bad i) := by
    intro h
    fin_cases i
    · have hi := (h 1 (by decide)).1
      have he := hi (a₁ := Sum.inr false) (a₂ := Sum.inr true) (by rfl)
      cases he
    · have hm := ((h 1 (by decide)).2 (Sum.inr false)).1
      change ([] : List ℕ) ∈ actualWords 3 at hm
      simp only [actualWords, Finset.mem_filter] at hm
      have hh := hm.2.1
      exact (by decide : ¬ (0 : ℕ) = 9) hh
    · have hh := ((h 1 (by decide)).2 (Sum.inr false)).2
      change descents ([] : List ℕ) = extremalValue 3 at hh
      exact (by decide : ¬ descents ([] : List ℕ) = extremalValue 3) hh
  refine { actual := actual
           bridge := Iff.rfl
           variation := ⟨@odd_word_construction, bad 0, hb 0⟩
           sensitivity := ?_
           dependence := ?_ }
  · constructor
    · intro i
      refine ⟨bad i, ?_, rfl, hb i⟩
      intro j hj
      funext t q
      simp [actual, bad, realize, hj]
    · intro i; exact nomatch i
  · intro i
    refine ⟨1, Sum.inr false, Sum.inr true, ?_⟩
    change oddWord 1 (Sum.inr false) ≠ oddWord 1 (Sum.inr true)
    intro h
    have he := (odd_word_construction 1 (by decide)).1 h
    cases he

#print axioms registration

end Reg.D5.S3.Combinatorics.ShankarWords.OddWordConstruction
